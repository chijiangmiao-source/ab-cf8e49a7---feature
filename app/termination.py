"""终止性复核:在已通过包线审计的同一保护脚本上,确认每条可达控制路径
最终到达 halt 或顺序终止,而不仅是存在一个可达终止点。

证据完全复用 /audit 已验证的程序结构与八边形后不动点(无状态服务,
每次请求独立计算,结构错误仍合并反馈且不携带任何旧结论)。

方法
----
1. 可达子图:以后不动点迁移非空的边为可行边,从程序点 0 出发求可达点;
   被不变量判空的边不可执行,不能产生无限执行。
2. 强连通区(SCC):对可达可行子图求 SCC。平凡 SCC(无自循环)不可重复;
   每个非平凡 SCC 是唯一可能无限重复的区域。
3. 逐转移寄存器关系:对每条可行边、每个寄存器,在源点不变量下推导
   两个方向的关系——
     * 下降方向:非增(x' <= x)/ 严格下降(x' < x);
     * 上升方向:非降(x' >= x)/ 严格上升(x' > x),用于有上界保护的计数循环;
   - add r, c:按常数 c 直接判定;
   - set r, c:以源点不变量的下界(下降方向)/上界(上升方向)判定,
     无界则该方向关系未知(不臆造);
   - guard / 无操作:寄存器不变。
4. SCC 闭包判定(避免把局部分支上的下降误作全局进展):
   一个可无限重复的有向闭路 w 可终止,当且仅当存在某个“方向原子”
   (寄存器 r,下降/上升),使 w 上每条边对该原子非增(降)/非降(升),
   至少一条边严格变化,且该严格步源点的不变量给出相应界(下降需下界、
   上升需上界)。非增序列只需在每圈固定位置有界即整体有界,因此不要求
   SCC 每个程序点都有界。
   在扩展图 (程序点, 仍保持单调的原子集 I, 已出现“受界严格步”的原子
   集 O) 上做可达搜索:边迁移为 I' = I & R(e)、O' = O | G(e),其中 R(e)
   为该边的非调关系掩码、G(e) 为严格边中源点有相应界的原子掩码(掩码只
   随步调单调,状态有限)。存在回到起点且 I & O = 0 的非空闭路,即存在
   无法赋任何排序见证的可重复闭路——返回 unknown;否则该 SCC 可终止,
   输出可独立重放的循环证书。

结论形态
--------
* terminating:所有非平凡 SCC 都通过闭包判据(无环可达子图自然通过);
* unknown    :按稳定程序点给出首个无法证明的循环关系,逐项说明每个
               寄存器方向缺失的是“单调关系”“严格一步”还是“不变量界”。
               这只是八边形证明力不足,绝不伪称实际死循环;
* error      :结构错误(与 /audit 同一合并反馈形态,不含分析证据)。
"""
from __future__ import annotations

from collections import deque

from .analyzer import _apply_action, _points_view, analyze_components
from .octagon import INF, terms_text
from .program import EXIT

# 方向原子位:寄存器 r 的下降方向占位 2r,上升方向占位 2r+1
DOWN = 0
UP = 1


def _atom(reg: int, direction: int) -> int:
    return 2 * reg + direction


# ----------------------------------------------------------------------
# 逐转移寄存器关系
# ----------------------------------------------------------------------
def _edge_register_relations(edge, src_state, nregs: int) -> list:
    """返回每条边对各寄存器两个方向的关系判定(含依据,供证书重放)。"""
    kind = edge.action[0]
    rels = []
    if kind == "add":
        r, c = edge.action[1], edge.action[2]
        for j in range(nregs):
            if j == r:
                rels.append({
                    "reg": j, "rule": "add", "delta": c,
                    "down": {"nonincreasing": c <= 0, "strict": c < 0},
                    "up": {"nondecreasing": c >= 0, "strict": c > 0},
                })
            else:
                rels.append(_unchanged(j))
    elif kind == "set":
        r, c = edge.action[1], edge.action[2]
        ub = src_state.bound(((1, r),))
        lb = None
        b = src_state.bound(((-1, r),))
        if b != INF:
            lb = -b
        for j in range(nregs):
            if j == r:
                rels.append({
                    "reg": j, "rule": "set", "value": c,
                    "source_lower_bound": lb,
                    "source_upper_bound": None if ub == INF else ub,
                    # x' = c <= x 对源点所有取值成立,需要 c <= 下界
                    "down": {"nonincreasing": lb is not None and c <= lb,
                             "strict": lb is not None and c < lb},
                    # x' = c >= x 对源点所有取值成立,需要 c >= 上界
                    "up": {"nondecreasing": ub != INF and c >= ub,
                           "strict": ub != INF and c > ub},
                })
            else:
                rels.append(_unchanged(j))
    else:  # guard / none:不赋值,所有寄存器保持不变
        rels = [_unchanged(j) for j in range(nregs)]
    return rels


def _unchanged(reg: int) -> dict:
    return {
        "reg": reg, "rule": "unchanged",
        "down": {"nonincreasing": True, "strict": False},
        "up": {"nondecreasing": True, "strict": False},
    }


def _relation_masks(relations: list) -> tuple:
    """由逐寄存器关系生成 (非调掩码 R, 严格掩码 S),位编码见模块头。"""
    r_mask = s_mask = 0
    for rel in relations:
        r = rel["reg"]
        d, u = rel["down"], rel["up"]
        if d["nonincreasing"]:
            r_mask |= 1 << _atom(r, DOWN)
        if u["nondecreasing"]:
            r_mask |= 1 << _atom(r, UP)
        if d["strict"]:
            s_mask |= 1 << _atom(r, DOWN)
        if u["strict"]:
            s_mask |= 1 << _atom(r, UP)
    return r_mask, s_mask


def _point_bounds(inv, scc_nodes, nregs: int) -> list:
    """逐寄存器收集 SCC 各点的有限下界/上界(供证书独立重放)。"""
    bounds = []
    for r in range(nregs):
        los, his = {}, {}
        for p in scc_nodes:
            state = inv[p]
            ub = state.bound(((1, r),))
            b = state.bound(((-1, r),))
            if ub != INF:
                his[p] = ub
            if b != INF:
                los[p] = -b
        bounds.append({"reg": r, "lower": los, "upper": his})
    return bounds


def _guarded_strict_mask(edge, src_state, s_mask: int, nregs: int) -> int:
    """严格原子中、其严格边源点受不变量界保护的子集 G(e)。

    下降原子需源点给出有限下界,上升原子需源点给出有限上界。
    非增序列只需在每圈的固定位置有界即整体有界,因此不要求 SCC 每点有界。
    """
    g_mask = 0
    for r in range(nregs):
        down = 1 << _atom(r, DOWN)
        up = 1 << _atom(r, UP)
        if s_mask & down:
            b = src_state.bound(((-1, r),))
            if b != INF:
                g_mask |= down
        if s_mask & up:
            if src_state.bound(((1, r),)) != INF:
                g_mask |= up
    return g_mask


# ----------------------------------------------------------------------
# 控制流子图与 SCC(Tarjan,规模 <= 49 个程序点,递归足够)
# ----------------------------------------------------------------------
def _tarjan_scc(nodes, adj) -> list:
    index = {}
    low = {}
    stack = []
    on_stack = set()
    counter = [0]
    result = []

    def strong(v):
        index[v] = counter[0]
        low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        for e in adj.get(v, ()):
            w = e.dst
            if w not in index:
                strong(w)
                low[v] = min(low[v], low[w])
            elif w in on_stack:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                comp.append(w)
                if w == v:
                    break
            result.append(comp)

    for v in nodes:  # nodes 已排序:生成的 SCC 顺序对稳定排序友好
        if v not in index:
            strong(v)
    return result


# ----------------------------------------------------------------------
# SCC 闭包判定:扩展图上搜索无排序见证的可重复闭路
# ----------------------------------------------------------------------
def _search_bad_walk(scc_nodes, internal, edge_triples):
    """搜索回到起点且没有任何“全程单调 + 受界严格步”原子的非空闭路。

    扩展状态 (程序点 u, I, O):
      I = 沿路每条边非调关系 R(e) 的交集(仍保持单调的原子);
      O = 沿路各边受界严格掩码 G(e) 的并集(已出现严格变化且该步源点有界的原子)。
    闭路可终止 ⟺ I & O != 0。起点按程序点升序、边按目的点排序,BFS 取最短
    见证,保证同一程序的复核结论稳定可重放。无坏闭路返回 None。
    """
    node_set = set(scc_nodes)
    for start in scc_nodes:  # 已排序
        init = (start, None, 0)
        seen = {init}
        parent = {init: None}
        queue = deque([init])
        while queue:
            u, keep, ranked = queue.popleft()
            for e in internal.get(u, ()):
                if e.dst not in node_set:
                    continue
                r_mask, _s, g_mask = edge_triples[e]
                new_keep = r_mask if keep is None else (keep & r_mask)
                state2 = (e.dst, new_keep, ranked | g_mask)
                if state2 in seen:
                    continue
                seen.add(state2)
                parent[state2] = ((u, keep, ranked), e)
                if e.dst == start and (state2[1] & state2[2]) == 0:
                    return _recover_walk(parent, state2)
                queue.append(state2)
    return None


def _recover_walk(parent, end_state):
    edges = []
    cur = end_state
    while parent[cur] is not None:
        prev, edge = parent[cur]
        edges.append(edge)
        cur = prev
    edges.reverse()
    walk = [edges[0].src] + [e.dst for e in edges]
    return walk, edges


# ----------------------------------------------------------------------
# 证书与失败证据装配
# ----------------------------------------------------------------------
def _action_text(action: tuple) -> str:
    kind = action[0]
    if kind == "set":
        return f"x{action[1]} := {action[2]}"
    if kind == "add":
        r, c = action[1], action[2]
        sign = "+" if c >= 0 else "-"
        return f"x{r} := x{r} {sign} {abs(c)}"
    if kind == "guard":
        return "guard " + " and ".join(f"{terms_text(t)} <= {k}"
                                       for t, k in action[1])
    return "skip"


def _edge_entry(edge, relations) -> dict:
    may_increase = []
    may_decrease = []
    for rel in relations:
        g = _relation_gap(rel, "down")
        if g is not None:
            may_increase.append(g)
        g = _relation_gap(rel, "up")
        if g is not None:
            may_decrease.append(g)
    return {
        "from": edge.src,
        "to": edge.dst,
        "kind": edge.kind,
        "action": _action_text(edge.action),
        "strict_decrease": [rel["reg"] for rel in relations
                           if rel["down"]["strict"]],
        "strict_increase": [rel["reg"] for rel in relations
                           if rel["up"]["strict"]],
        "not_proven_nonincreasing": may_increase,
        "not_proven_nondecreasing": may_decrease,
        "register_relations": relations,
    }


def _relation_gap(rel: dict, direction: str):
    """说明某方向单调关系为何不成立(用于无法证明时的逐项说明)。"""
    r = rel["reg"]
    if rel["rule"] == "add":
        c = rel["delta"]
        if direction == "down" and c > 0:
            return {"reg": r, "reason": "increases", "delta": c}
        if direction == "up" and c < 0:
            return {"reg": r, "reason": "decreases", "delta": c}
        return None
    if rel["rule"] == "set":
        c = rel["value"]
        if direction == "down":
            lb = rel["source_lower_bound"]
            if lb is None:
                return {"reg": r, "reason": "unbounded_source",
                        "missing": "lower_bound", "value": c}
            if c > lb:
                return {"reg": r, "reason": "may_increase",
                        "value": c, "source_lower_bound": lb}
        else:
            ub = rel["source_upper_bound"]
            if ub is None:
                return {"reg": r, "reason": "unbounded_source",
                        "missing": "upper_bound", "value": c}
            if c < ub:
                return {"reg": r, "reason": "may_decrease",
                        "value": c, "source_upper_bound": ub}
    return None


def _register_evidence(nregs, walk_edges, rel_by_edge, edge_triples):
    """逐寄存器、逐方向说明该闭路缺失的单调关系/严格一步/界保护。

    掩码均沿该具体闭路闭包得到:
      keep    = & R(e):全程保持单调的原子;
      strict  = | S(e):出现过严格一步的原子(不论源点是否有界);
      ranked  = | G(e):出现过严格一步且该步源点有不变量界的原子。
    """
    keep, strict, ranked = None, 0, 0
    for e in walk_edges:
        r_mask, s_mask, g_mask = edge_triples[e]
        keep = r_mask if keep is None else (keep & r_mask)
        strict |= s_mask
        ranked |= g_mask
    evidence = []
    for r in range(nregs):
        for direction, gap_name in (
                (DOWN, "down"),
                (UP, "up")):
            atom = 1 << _atom(r, direction)
            entry = {
                "reg": r,
                "direction": "decrease_to_lower_bound"
                if direction == DOWN else "increase_to_upper_bound",
                "monotone_throughout": bool(keep & atom),
                "has_strict_step": bool(strict & atom),
                "strict_step_source_bounded": bool(ranked & atom),
            }
            if not (keep & atom):
                idx, gap = _first_gap(walk_edges, rel_by_edge, r, gap_name)
                entry["missing"] = "monotone_relation"
                entry["first_breaking_edge"] = {
                    "index": idx,
                    "from": walk_edges[idx].src,
                    "to": walk_edges[idx].dst,
                    "gap": gap,
                }
            elif not (strict & atom):
                entry["missing"] = "strict_step"
                entry["detail"] = (
                    f"整条闭路对 x{r} 仅能证明"
                    f"{'非增' if direction == DOWN else '非降'},"
                    f"没有任何一步严格{'下降' if direction == DOWN else '上升'}")
            elif not (ranked & atom):
                idx = _first_unbounded_strict(walk_edges, edge_triples, r, direction)
                src = walk_edges[idx].src
                entry["missing"] = ("lower_bound" if direction == DOWN
                                    else "upper_bound")
                entry["unbounded_strict_edge"] = {
                    "index": idx,
                    "from": src,
                    "to": walk_edges[idx].dst,
                }
                entry["detail"] = (
                    f"闭路对 x{r} 全程{'非增' if direction == DOWN else '非降'}"
                    f"且含严格步,但严格步源点(程序点 {src})的不变量给不出"
                    f"{'下' if direction == DOWN else '上'}界,"
                    f"严格{'下降' if direction == DOWN else '上升'}无界可坠")
            else:
                entry["missing"] = None
            evidence.append(entry)
    return evidence


def _first_gap(walk_edges, rel_by_edge, reg, direction):
    """闭路中首个破坏该方向单调关系的边及其缺口说明。"""
    for idx, edge in enumerate(walk_edges):
        rel = next(r for r in rel_by_edge[edge] if r["reg"] == reg)
        gap = _relation_gap(rel, direction)
        if gap is not None:
            return idx, gap
    return 0, None


def _first_unbounded_strict(walk_edges, edge_triples, reg, direction):
    """闭路中首个“严格但源点缺界”的边的下标。"""
    atom = 1 << _atom(reg, direction)
    for idx, edge in enumerate(walk_edges):
        _r, s_mask, g_mask = edge_triples[edge]
        if (s_mask & atom) and not (g_mask & atom):
            return idx
    return 0


def _scc_certificate(scc, internal, rel_by_edge, edge_triples,
                     bounds, nregs):
    anchor = min(x for x in scc if isinstance(x, int))
    scc_sorted = sorted(scc, key=lambda p: (isinstance(p, str), p))
    scc_set = set(scc)
    walk_found = _search_bad_walk(scc_sorted, internal, edge_triples)
    transitions = []
    for p in scc_sorted:
        for e in internal.get(p, ()):
            if e.dst in scc_set:
                transitions.append(_edge_entry(e, rel_by_edge[e]))
    cert = {
        "anchor_point": anchor,
        "scc": scc_sorted,
        "repeatable_region": True,
        "bounds": [
            {
                "reg": r,
                "lower_bounds": {str(p): v for p, v in bounds[r]["lower"].items()},
                "upper_bounds": {str(p): v for p, v in bounds[r]["upper"].items()},
            }
            for r in range(nregs)
        ],
        "transitions": transitions,
        "closure": {
            "method": "repeatable_walk_ranking_closure",
            "description": (
                "对 SCC 内每条可重复有向闭路,必须存在同一方向原子"
                "(寄存器 + 下降/上升):闭路中每条边对其保持非增/非降,"
                "且至少一条边严格变化,并且该严格步源点的不变量给出相应界"
                "(下降需下界、上升需上界;非增序列在每圈固定位置有界即整体有界)。"
                "重放方式:用 points.<id>.invariant 中的界核对 bounds 与 "
                "register_relations,再对 transitions 做掩码闭包"
                "(非调关系取交 I=∧R;受界严格步取并 O=∨G),"
                "不应存在回到起点且 I & O = 0 的闭路。"
            ),
        },
    }
    if walk_found is None:
        strict_edges = []
        for p in scc_sorted:
            for e in internal.get(p, ()):
                if e.dst not in scc_set:
                    continue
                rels = rel_by_edge[e]
                sd = [r["reg"] for r in rels if r["down"]["strict"]]
                su = [r["reg"] for r in rels if r["up"]["strict"]]
                if sd or su:
                    strict_edges.append({
                        "edge": [e.src, e.dst],
                        "strict_decrease": sd,
                        "strict_increase": su,
                    })
        cert["status"] = "proven"
        cert["ranking_edges"] = strict_edges
        cert["closure"]["every_repeatable_walk_decreases"] = True
        return cert, None

    walk, walk_edges = walk_found
    evidence = _register_evidence(nregs, walk_edges, rel_by_edge, edge_triples)
    first_edge = {
        "from": walk_edges[0].src,
        "to": walk_edges[0].dst,
        "kind": walk_edges[0].kind,
        "action": _action_text(walk_edges[0].action),
    }
    failure = {
        "anchor_point": anchor,
        "scc": scc_sorted,
        "walk": walk,
        "walk_edges": [
            {"index": i, "from": e.src, "to": e.dst, "kind": e.kind,
             "action": _action_text(e.action)}
            for i, e in enumerate(walk_edges)
        ],
        "first_cycle_relation": first_edge,
        "register_evidence": evidence,
        "kind": "no_ranking_witness",
        "note": (
            "在已验证的八边形不变量上,该可重复闭路对每个寄存器方向"
            "都不能同时满足“全程单调 + 至少一步严格变化 + 严格步源点有界”;"
            "这是静态证明力不足,并非已构造出实际死循环,禁止据此判定脚本"
            "必然无限执行。"
        ),
    }
    cert["status"] = "unproven"
    cert["closure"]["every_repeatable_walk_decreases"] = False
    return cert, failure


# ----------------------------------------------------------------------
# 顶层入口
# ----------------------------------------------------------------------
def review_termination(payload) -> dict:
    """终止性复核入口:terminating / unknown / error。"""
    kind, data = analyze_components(payload)
    if kind == "error":
        return data
    prog, engine, audit = data
    inv = engine.inv
    nregs = prog.nregs

    # 1. 可行可达子图(从点 0 出发,只取迁移结果非空的边)
    out_edges = {}
    for e in prog.edges:
        out_edges.setdefault(e.src, []).append(e)
    for edges in out_edges.values():
        edges.sort(key=lambda e: (e.dst, e.kind))

    feasible = set()
    reachable = set()
    queue = deque([0])
    reachable.add(0)
    while queue:
        p = queue.popleft()
        for e in out_edges.get(p, ()):
            y = _apply_action(inv[p], e.action) if inv[p] is not None else None
            if y is None:
                continue
            feasible.add(e)
            if e.dst not in reachable:
                reachable.add(e.dst)
                queue.append(e.dst)

    radj = {}
    for e in feasible:
        radj.setdefault(e.src, []).append(e)
    for edges in radj.values():
        edges.sort(key=lambda e: (e.dst, e.kind))
    nodes = sorted(reachable, key=lambda p: (isinstance(p, str), p))

    # 2. SCC
    components = _tarjan_scc(nodes, radj)
    nontrivial = []
    for comp in components:
        comp_set = set(comp)
        if len(comp) > 1 or any(e.dst == comp[0]
                                for e in radj.get(comp[0], ())
                                if e.dst in comp_set):
            nontrivial.append(sorted(comp, key=lambda p: (isinstance(p, str), p)))
    nontrivial.sort(key=lambda c: min(x for x in c if isinstance(x, int)))

    # 3. 逐边关系(只需可行边;证书聚焦 SCC 内部边)
    #    每条边给出 (R 非调掩码, S 严格掩码, G 受界严格掩码)
    rel_by_edge = {}
    edge_triples = {}
    for e in feasible:
        rels = _edge_register_relations(e, inv[e.src], nregs)
        rel_by_edge[e] = rels
        r_mask, s_mask = _relation_masks(rels)
        g_mask = _guarded_strict_mask(e, inv[e.src], s_mask, nregs)
        edge_triples[e] = (r_mask, s_mask, g_mask)

    # 4. 逐 SCC 闭包判定
    certificates = []
    first_failure = None
    for scc in nontrivial:
        bounds = _point_bounds(inv, scc, nregs)
        cert, failure = _scc_certificate(
            scc, radj, rel_by_edge, edge_triples, bounds, nregs)
        certificates.append(cert)
        if failure is not None and first_failure is None:
            first_failure = failure

    assertions = [{"point": a["point"], "status": a["status"]}
                  for a in audit["assertions"]]
    unproven_points = [a["point"] for a in assertions
                       if a["status"] == "unproven"]
    response = {
        "verdict": "terminating" if first_failure is None else "unknown",
        "program": {"num_registers": nregs, "num_instructions": prog.n_instr},
        "envelope": {
            "verdict": "pass" if not unproven_points else "fail",
            "assertions": assertions,
            "first_unproven": (min(unproven_points) if unproven_points else None),
            "note": "终止性复核预设包线审计已通过;envelope.verdict 为同一脚本"
                    "独立复算的包线结论,/audit 的响应格式不受影响。",
        },
        "reachable_graph": {
            "nodes": [str(p) for p in nodes],
            "exit_reachable": EXIT in reachable,
            "feasible_edges": [
                {"from": e.src, "to": e.dst, "kind": e.kind,
                 "action": _action_text(e.action)}
                for e in sorted(feasible, key=lambda e: (
                    isinstance(e.src, str), e.src,
                    isinstance(e.dst, str), e.dst, e.kind))
            ],
        },
        "points": _points_view(engine),
        "loop_certificates": certificates,
        "fixpoint": {
            "widening_points": sorted(prog.widening_points),
            "post_fixpoint_verified": True,
        },
    }
    if first_failure is not None:
        response["first_unproven_cycle"] = first_failure
    return response
