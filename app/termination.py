"""终止性复核:在包线审计通过的同一份保护脚本上,确认每个可达循环都有
全局进展——沿 SCC 闭包后的任意可无限重复路径,存在受不变量下界保护的
寄存器严格自降。

方法(复用 prepare_analysis 已验证的程序结构与八边形不变量):
  1. 用已校验的归纳不变量对每条边做可行性(活性)判定,去掉不可达/不可行
     转移,避免把不可行方向上的关系计入循环闭包;
  2. 在活跃转移图上求强连通区(SCC,Tarjan);非平凡 SCC 即循环;
  3. 为每条活跃转移逐寄存器推导单调关系
     x'_r <op> x_r,op ∈ lt/le/eq/ge/gt/unk:
       - set c          → 以源点不变量判定 c 与 x_r 的界,给出 lt/le/eq/ge/gt/unk;
       - add c          → c<0 严格降 / c==0 相等 / c>0 严格升;
       - guard / none   → eq(恒等);
     这是基于不变量的可靠推导,缺信息时给 unk,绝不臆造下降;
  4. 在每个 SCC 内按关系复合半格做 Kleene 闭包,得到"沿 SCC 内任意路径
     从程序点 p 回到 p(或到达 q)"的路径关系——分支交替时局部下降会被
     与另一条无下降路径的 join 稀释为非严格,从而不会被误作全局进展;
  5. 仅当每个非平凡 SCC 都能选出一个寄存器 r:
       (a) SCC 内每个程序点上 x_r 都有不变量给出的有限界
           (严格下降配下界,或严格上升配有限上界——后者即 -x_r 严格自降);
       (b) 该寄存器在每个程序点的闭环关系都是严格的(lt 或 gt);
     才判可终止。否则按稳定程序点(最小 SCC 头)给出首个无法证明的循环关系,
     说明缺失的是严格变化还是有限界——这是证明失败,不伪称实际死循环。

通过的 SCC 输出可独立重放的循环证书:SCC 程序点、退出边、逐转移关系、
闭环关系、排名寄存器/方向与其逐点界;调用方可凭 /audit 同款逐点不变量
独立核对每一项。
"""
from __future__ import annotations

from .octagon import INF
from .analyzer import _apply_action

# 单调关系半格(按信息量排序):unk 为顶。
RELATIONS = ("lt", "le", "eq", "ge", "gt", "unk")
REL_TEXT = {"lt": "<", "le": "<=", "eq": "==", "ge": ">=", "gt": ">", "unk": "?"}

# 顺序复合表:R1 ∘ R2(先走 R1 再走 R2,均为 x' op x 形态)。
# 依据传递性与整数严格性(a<b<=c ⇒ a<c,整数下 a<b ⇒ a<=b-1)。
_COMPOSE = {
    ("lt", "lt"): "lt", ("lt", "le"): "lt", ("lt", "eq"): "lt",
    ("le", "lt"): "lt", ("le", "le"): "le", ("le", "eq"): "le",
    ("eq", "lt"): "lt", ("eq", "le"): "le", ("eq", "eq"): "eq",
    ("eq", "ge"): "ge", ("eq", "gt"): "gt",
    ("ge", "eq"): "ge", ("ge", "ge"): "ge", ("ge", "gt"): "gt",
    ("gt", "eq"): "gt", ("gt", "ge"): "gt", ("gt", "gt"): "gt",
    ("lt", "ge"): "unk", ("ge", "lt"): "unk",
    ("lt", "gt"): "unk", ("gt", "lt"): "unk",
    ("le", "ge"): "unk", ("ge", "le"): "unk",
    ("le", "gt"): "unk", ("gt", "le"): "unk",
}


def compose(r1: str, r2: str) -> str:
    if r1 == "unk" or r2 == "unk":
        return "unk"
    return _COMPOSE.get((r1, r2), "unk")


def join_rel(r1: str, r2: str) -> str:
    """路径分支的关系合并:两条路径都成立时,仅保留共同结论(格上确界)。

    谓词格:lt ≤ le ≤ unk,eq ≤ le,eq ≤ ge,gt ≤ ge(按蕴含排序)。
    在"差集"表示下关系复合对该 join 分配(Minkowski 和对并集分配),
    故 Kleene 闭包迭代对所有路径关系是精确的。
    """
    if r1 == r2:
        return r1
    pair = frozenset((r1, r2))
    if pair == frozenset(("lt", "eq")) or pair == frozenset(("lt", "le")) \
            or pair == frozenset(("eq", "le")):
        return "le"
    if pair == frozenset(("gt", "eq")) or pair == frozenset(("gt", "ge")) \
            or pair == frozenset(("eq", "ge")):
        return "ge"
    return "unk"


# ----------------------------------------------------------------------
# 活跃转移(可行性)与逐转移寄存器关系
# ----------------------------------------------------------------------
def _relation_for_action(action: tuple, src_state, r: int) -> str:
    """推导边迁移后 x'_r 与源点 x_r 的单调关系。"""
    kind = action[0]
    if kind == "add":
        if action[1] != r:
            return "eq"
        c = action[2]
        if c < 0:
            return "lt"
        if c > 0:
            return "gt"
        return "eq"
    if kind == "set":
        if action[1] != r:
            return "eq"
        c = action[2]
        hi = src_state.bound(((1, r),))    # x_r <= hi
        lb = src_state.bound(((-1, r),))  # -x_r <= lb ⇒ x_r >= -lb
        lo = None if lb == INF else -lb
        hi_v = None if hi == INF else hi
        # 对范围内*所有*具体值都成立的最强关系
        if lo is not None and c < lo:
            return "lt"  # c 严格小于最小值
        if hi_v is not None and c > hi_v:
            return "gt"  # c 严格大于最大值
        if lo is not None and hi_v is not None and lo == hi_v == c:
            return "eq"  # 范围退化为单点且等于 c
        if lo is not None and c == lo:
            return "le"  # 恒有 c <= x,取到最小值时相等
        if hi_v is not None and c == hi_v:
            return "ge"  # 恒有 c >= x,取到最大值时相等
        return "unk"
    # guard / none:寄存器值不变
    return "eq"


def _edge_relations(edge, src_state, nregs: int) -> dict:
    return {r: _relation_for_action(edge.action, src_state, r) for r in range(nregs)}


# ----------------------------------------------------------------------
# Tarjan SCC(迭代实现,避免深递归)
# ----------------------------------------------------------------------
def _tarjan_scc(nodes, out_edges):
    index = {}
    low = {}
    on_stack = set()
    stack = []
    sccs = []
    counter = 0

    for root in nodes:
        if root in index:
            continue
        work = [(root, iter(out_edges.get(root, ())))]
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        on_stack.add(root)
        while work:
            u, it = work[-1]
            advanced = False
            for v in it:
                if v not in index:
                    index[v] = low[v] = counter
                    counter += 1
                    stack.append(v)
                    on_stack.add(v)
                    work.append((v, iter(out_edges.get(v, ()))))
                    advanced = True
                    break
                if v in on_stack:
                    if index[v] < low[u]:
                        low[u] = index[v]
            if advanced:
                continue
            work.pop()
            if work:
                parent = work[-1][0]
                if low[u] < low[parent]:
                    low[parent] = low[u]
            if low[u] == index[u]:
                comp = []
                while True:
                    w = stack.pop()
                    on_stack.discard(w)
                    comp.append(w)
                    if w == u:
                        break
                sccs.append(comp)
    return sccs


# ----------------------------------------------------------------------
# SCC 内关系闭包
# ----------------------------------------------------------------------
def _closure_scc(members, internal_edges, nregs: int, edge_rels) -> dict:
    """自反传递闭包 A*:star[r][(p,q)] 是 SCC 内从 p 到 q 的**任意路径**
    (含长度 0 的空路径,对角初值为 eq)对寄存器 r 的关系上界;按边扩展并
    join 直到不动点。关系复合对分支 join 分配(差集表示的 Minkowski 和),
    迭代结果即精确的路径关系并:一条路径局部下降、另一条只非增 ⇒ join 为 le,
    分支交替不会把局部进展误作全局进展。
    """
    members = list(members)
    star = {r: {(p, p): "eq" for p in members} for r in range(nregs)}
    changed = True
    # 程序上限 48 条指令、4 个寄存器,有限格上迭代必然很快收敛
    while changed:
        changed = False
        for edge in internal_edges:
            u, v = edge.src, edge.dst
            for r in range(nregs):
                cur = star[r]
                step = edge_rels[id(edge)][r]
                for p in members:
                    pu = cur.get((p, u))
                    if pu is None:
                        continue
                    candidate = compose(pu, step)
                    old = cur.get((p, v))
                    new = candidate if old is None else join_rel(old, candidate)
                    if old != new:
                        cur[(p, v)] = new
                        changed = True
    return star


def _cycle_relations(members, internal_edges, star, edge_rels, nregs: int) -> dict:
    """长度 >=1 的闭环关系:cycle[r][p] = join 所有以 p 为终点的内部边
    u→p 上(从 p 到 u 的任意路径,含空路径)复合该边的关系。

    不能直接读 A* 的对角——那里混入了空路径 eq,会把严格环关系弱化成 <=。
    cycle[r][p] 即"绕一圈回到 p 的所有方式"的合并:严格(lt/gt)当且仅当
    每条可无限重复的回程路径对该寄存器都严格变化。
    """
    cycle = {r: {p: None for p in members} for r in range(nregs)}
    for edge in internal_edges:
        u, v = edge.src, edge.dst
        for r in range(nregs):
            pu = star[r].get((v, u))
            if pu is None:
                continue
            rel = compose(pu, edge_rels[id(edge)][r])
            old = cycle[r][v]
            cycle[r][v] = rel if old is None else join_rel(old, rel)
    return cycle


def _register_bounds(members, inv, nregs: int) -> dict:
    """每个寄存器在 SCC *所有* 程序点上共同成立的不变量有限下界/上界;
    任一点无界则该方向为 None。

    每点:下界 = -bound(-x_r),上界 = bound(x_r)。
    全部点共同的下界取 min(最弱者仍处处成立)、共同上界取 max。
    严格下降配下界、严格上升配上界(后者即 -x 严格下降)。
    """
    bounds = {}
    for r in range(nregs):
        los, his = [], []
        lo_ok = hi_ok = True
        for p in members:
            ub = inv[p].bound(((1, r),))
            lb = inv[p].bound(((-1, r),))
            if ub == INF:
                hi_ok = False
            else:
                his.append(ub)
            if lb == INF:
                lo_ok = False
            else:
                los.append(-lb)
        bounds[r] = {
            "lower": min(los) if lo_ok else None,
            "upper": max(his) if hi_ok else None,
        }
    return bounds


def _edge_view(edge, rels) -> dict:
    return {
        "from": edge.src,
        "to": edge.dst,
        "kind": edge.kind,
        "register_relations": {str(r): REL_TEXT[rels[r]] for r in sorted(rels)},
    }


def analyze_termination(payload) -> dict:
    """终止性复核入口。结构错误合并反馈(复用 /audit 同款校验,不携带旧结论);
    包线未通过则拒绝复核;否则返回 terminating / cannot_prove。
    """
    from .analyzer import prepare_analysis

    prep = prepare_analysis(payload)
    if prep["outcome"] == "error":
        return prep["response"]
    prog = prep["prog"]
    engine = prep["engine"]
    inv = engine.inv
    nregs = prog.nregs

    if prep["unproven"]:
        point = min(u[0] for u in prep["unproven"])
        return {
            "verdict": "error",
            "reason": "envelope_audit_not_passed",
            "detail": "终止性复核仅对包线审计通过的脚本开放;请先取得 /audit 的 pass 结论。",
            "first_unproven_point": point,
        }

    # 1. 活跃转移:源点可达且迁移后(含 guard 收窄)非空
    live_edges = []
    edge_rels = {}
    for edge in prog.edges:
        src_state = inv[edge.src]
        if src_state is None:
            continue
        if _apply_action(src_state, edge.action) is None:
            continue
        live_edges.append(edge)
        rels = _edge_relations(edge, src_state, nregs)
        edge_rels[id(edge)] = rels

    reachable = [p for p in prog.points if inv[p] is not None]
    out_live = {}
    for e in live_edges:
        out_live.setdefault(e.src, []).append(e.dst)

    # 2. 强连通区
    sccs = _tarjan_scc(reachable, out_live)
    loop_sccs = []
    for comp in sccs:
        members = set(comp)
        internal = [e for e in live_edges if e.src in members and e.dst in members]
        # 多节点 SCC 非平凡;单节点 SCC 仅当存在活跃自环边时才算循环
        # (internal 同时覆盖这两种情形)
        if internal:
            loop_sccs.append(sorted(comp))

    def scc_head(members):
        # 稳定标识:SCC 内编号最小的程序点(EXIT 是字符串,排序时靠后)
        return min(members, key=lambda p: (isinstance(p, str), p))

    loop_sccs.sort(key=lambda m: (isinstance(scc_head(m), str), scc_head(m)))

    certificates = []
    failures = []
    for members in loop_sccs:
        mset = set(members)
        ordered_points = sorted(members, key=lambda p: (isinstance(p, str), p))
        internal_edges = [e for e in live_edges if e.src in mset and e.dst in mset]
        exit_edges = [e for e in live_edges if e.src in mset and e.dst not in mset]

        # 3-4. 逐转移关系 + SCC 闭包(A*),并提取长度 >=1 的闭环关系
        star = _closure_scc(members, internal_edges, nregs, edge_rels)
        cycle = _cycle_relations(members, internal_edges, star, edge_rels, nregs)
        bounds = _register_bounds(members, inv, nregs)

        # 5. 排名寄存器(两个对称方向):
        #    下降 x' < x 需不变量有限下界;上升 x' > x 需不变量有限上界
        #    (后者即 -x 严格自降)。要求该寄存器在每个程序点的*闭环关系*都严格。
        rank = None
        rank_dir = None
        for r in range(nregs):
            strict_lt = all(cycle[r][p] == "lt" for p in members)
            strict_gt = all(cycle[r][p] == "gt" for p in members)
            if strict_lt and bounds[r]["lower"] is not None:
                rank, rank_dir = r, "decreasing"
                break
            if strict_gt and bounds[r]["upper"] is not None:
                rank, rank_dir = r, "increasing"
                break

        head = scc_head(members)
        internal_view = [_edge_view(e, edge_rels[id(e)])
                         for e in sorted(internal_edges,
                                         key=lambda e: (e.src, str(e.dst), e.kind))]
        self_rels = {str(p): {str(r): REL_TEXT[cycle[r][p]] for r in range(nregs)}
                     for p in ordered_points}

        if rank is not None:
            if rank_dir == "decreasing":
                bound_key = "ranking_lower_bounds"
                point_bounds = {}
                for p in ordered_points:
                    lb = inv[p].bound(((-1, rank),))
                    point_bounds[str(p)] = None if lb == INF else -lb
                guard = bounds[rank]["lower"]
                sign_word = "下界"
                relation_word = "减小"
                guard_word = "至少"
                strict_sign = "<"
            else:
                bound_key = "ranking_upper_bounds"
                point_bounds = {}
                for p in ordered_points:
                    ub = inv[p].bound(((1, rank),))
                    point_bounds[str(p)] = None if ub == INF else ub
                guard = bounds[rank]["upper"]
                sign_word = "上界"
                relation_word = "增大"
                guard_word = "至多"
                strict_sign = ">"
            certificates.append({
                "loop_head": head,
                "points": ordered_points,
                "exit_edges": [{"from": e.src, "to": e.dst, "kind": e.kind}
                               for e in sorted(exit_edges,
                                               key=lambda e: (e.src, str(e.dst), e.kind))],
                "internal_edges": internal_view,
                "closed_cycle_relations": self_rels,
                "ranking_register": rank,
                "ranking_direction": rank_dir,
                bound_key: point_bounds,
                "argument": (
                    f"寄存器 x{rank} 沿 SCC 内任意路径回到同一程序点都严格{relation_word}"
                    f"(闭环关系均为 '{strict_sign}'),且在每个循环程序点上都有不变量给出的"
                    f"有限{sign_word}({guard_word} {guard}),故该循环不可能无限重复。"
                ),
            })
        else:
            # 诊断:在 head(稳定程序点)上逐个寄存器说明缺什么
            candidates = []
            for r in range(nregs):
                self_rel = cycle[r][head]
                lo, hi = bounds[r]["lower"], bounds[r]["upper"]
                missing = []
                rel_text = REL_TEXT.get(self_rel, "?") if self_rel is not None else "?"
                if self_rel not in ("lt", "gt"):
                    if self_rel is None or self_rel == "unk":
                        missing.append({
                            "kind": "strict_decrease",
                            "detail": f"沿 SCC 内某些路径无法证明 x{r} 的单调性"
                                      f"(head={head} 处闭环关系未知):分支交替时,"
                                      f"一条路径的局部下降被另一路径抵消",
                        })
                    else:
                        missing.append({
                            "kind": "strict_decrease",
                            "detail": f"head={head} 处闭环关系为 "
                                      f"x{r} {rel_text} x{r},并非沿每条可无限重复"
                                      f"路径都严格变化(局部进展经分支 join 后不构成全局进展)",
                        })
                else:
                    strict_kind = self_rel
                    guarded = lo is not None if strict_kind == "lt" else hi is not None
                    if not guarded:
                        missing.append({
                            "kind": "lower_bound" if strict_kind == "lt" else "upper_bound",
                            "detail": (f"x{r} 虽在 head={head} 处闭环关系严格"
                                       f"({'下降' if strict_kind == 'lt' else '上升'}),"
                                       f"但不变量未在全部循环程序点上给出有限"
                                       f"{'下界' if strict_kind == 'lt' else '上界'},"
                                       f"严格变化可能无限持续"),
                        })
                candidates.append({
                    "register": r,
                    "closed_self_relation_at_head": rel_text,
                    "lower_bound_in_scc": lo,
                    "upper_bound_in_scc": hi,
                    "missing": missing,
                })
            # 稳定排序选"首个无法证明的循环关系":缺失项最少者优先,其次寄存器号
            best = min(candidates, key=lambda c: (len(c["missing"]), c["register"]))
            failures.append({
                "loop_head": head,
                "points": ordered_points,
                "internal_edges": internal_view,
                "closed_cycle_relations": self_rels,
                "register_candidates": candidates,
                "first_missing": best["missing"],
                "kind": "termination_proof_failure",
                "note": "无法在八边形不变量上证明该循环终止:这是证明失败(信息不足),"
                        "并非断言存在实际死循环;不得据此伪造具体无限执行。",
            })

    result = {
        "verdict": "terminating" if not failures else "cannot_prove",
        "envelope_audit": "pass",
        "envelope_assertions": len(prep["assertions"]),
        "program": {"num_registers": prog.nregs, "num_instructions": prog.n_instr},
        "method": {
            "live_transfer_feasibility": "仅对源点可达且经八边形迁移(含 guard)后非空的"
                                         "转移推导关系",
            "scc": "Tarjan 强连通区;非平凡 SCC 即循环",
            "relation_closure": "逐转移寄存器单调关系(lt/le/eq/ge/gt/unk)在 SCC 内按"
                                "复合半格闭包,分支路径 join 后局部下降不可伪装为全局进展",
            "ranking": "每个循环需存在寄存器:闭包自关系处处严格(下降配不变量有限下界,"
                       "或上升配有限上界,后者等价于 -x 下降)",
        },
        "loops": {
            "total": len(loop_sccs),
            "proven": len(certificates),
            "unproven": len(failures),
        },
        "certificates": certificates,
    }
    if failures:
        result["first_unproven_loop"] = failures[0]
        result["unproven_loops"] = failures
    return result
