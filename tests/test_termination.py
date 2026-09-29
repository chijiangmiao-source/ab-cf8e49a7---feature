"""终止性复核单元测试:单调计数循环、分支交替仍终止、无界自增闭环、
乒乓式局部下降(非全局进展)、无环程序与结构错误合并反馈。"""
import unittest

from app.termination import review_termination


def monotone_up_program():
    """x0、x1 同步自增至 5:上升方向严格步 + 上界保护,包线亦通过。"""
    return {
        "num_registers": 2,
        "initial": [{"lo": 0, "hi": 0}, {"lo": 0, "hi": 0}],
        "instructions": [
            {"id": 0, "op": "set", "reg": 0, "value": 0},
            {"id": 1, "op": "set", "reg": 1, "value": 0},
            {"id": 2, "op": "branch",
             "cond": {"coefs": {"0": 1}, "op": "<", "value": 5}, "target": 6},
            {"id": 3, "op": "assert",
             "cond": {"coefs": {"0": 1, "1": -1}, "op": "==", "value": 0}},
            {"id": 4, "op": "assert",
             "cond": {"coefs": {"0": 1}, "op": "<=", "value": 5}},
            {"id": 5, "op": "halt"},
            {"id": 6, "op": "add", "reg": 0, "value": 1},
            {"id": 7, "op": "add", "reg": 1, "value": 1},
            {"id": 8, "op": "goto", "target": 2},
        ],
    }


def monotone_down_program():
    """x0 从 3 递减到 0:下降方向严格步 + 下界保护。"""
    return {
        "num_registers": 1,
        "initial": [{"lo": 3, "hi": 3}],
        "instructions": [
            {"id": 0, "op": "branch",
             "cond": {"coefs": {"0": 1}, "op": ">", "value": 0}, "target": 3},
            {"id": 1, "op": "assert",
             "cond": {"coefs": {"0": 1}, "op": ">=", "value": 0}},
            {"id": 2, "op": "halt"},
            {"id": 3, "op": "add", "reg": 0, "value": -1},
            {"id": 4, "op": "goto", "target": 0},
        ],
    }


def alternating_program():
    """两支回边:x0>0 时 x0--/x1++;否则 x1>0 时 x1--。
    纯走任一支或任意交替都终止;不存在单一寄存器在每条回边上都下降。"""
    return {
        "num_registers": 2,
        "initial": [{"lo": 3, "hi": 3}, {"lo": 0, "hi": 0}],
        "instructions": [
            {"id": 0, "op": "branch",
             "cond": {"coefs": {"0": 1}, "op": ">", "value": 0}, "target": 3},
            {"id": 1, "op": "branch",
             "cond": {"coefs": {"1": 1}, "op": ">", "value": 0}, "target": 6},
            {"id": 2, "op": "halt"},
            {"id": 3, "op": "add", "reg": 0, "value": -1},
            {"id": 4, "op": "add", "reg": 1, "value": 1},
            {"id": 5, "op": "goto", "target": 0},
            {"id": 6, "op": "add", "reg": 1, "value": -1},
            {"id": 7, "op": "goto", "target": 0},
        ],
    }


def unbounded_increment_program():
    """x0 每圈 +1,退出条件 x0<0 在不变量下不可行:计数无界,无法证明终止。"""
    return {
        "num_registers": 1,
        "initial": [{"lo": 0, "hi": 0}],
        "instructions": [
            {"id": 0, "op": "add", "reg": 0, "value": 1},
            {"id": 1, "op": "branch",
             "cond": {"coefs": {"0": 1}, "op": "<", "value": 0}, "target": 3},
            {"id": 2, "op": "goto", "target": 0},
            {"id": 3, "op": "halt"},
        ],
    }


def pingpong_program():
    """τ1: x0--/x1++;τ2: x0++/x1--。每支都有寄存器下降,
    但合起来走一圈净零,任何闭路都找不到全程严格下降的寄存器。"""
    return {
        "num_registers": 2,
        "initial": [{"lo": 1, "hi": 1}, {"lo": 0, "hi": 0}],
        "instructions": [
            {"id": 0, "op": "branch",
             "cond": {"coefs": {"0": 1}, "op": ">", "value": 0}, "target": 4},
            {"id": 1, "op": "branch",
             "cond": {"coefs": {"1": 1}, "op": ">", "value": 0}, "target": 7},
            {"id": 2, "op": "halt"},
            {"id": 3, "op": "halt"},
            {"id": 4, "op": "add", "reg": 0, "value": -1},
            {"id": 5, "op": "add", "reg": 1, "value": 1},
            {"id": 6, "op": "goto", "target": 0},
            {"id": 7, "op": "add", "reg": 0, "value": 1},
            {"id": 8, "op": "add", "reg": 1, "value": -1},
            {"id": 9, "op": "goto", "target": 0},
        ],
    }


class TestTerminating(unittest.TestCase):
    def test_monotone_up_counter(self):
        res = review_termination(monotone_up_program())
        self.assertEqual(res["verdict"], "terminating")
        self.assertEqual(res["envelope"]["verdict"], "pass")
        self.assertTrue(res["reachable_graph"]["exit_reachable"])
        self.assertTrue(res["fixpoint"]["post_fixpoint_verified"])
        certs = res["loop_certificates"]
        self.assertEqual(len(certs), 1)
        cert = certs[0]
        self.assertEqual(cert["status"], "proven")
        self.assertEqual(cert["anchor_point"], 2)
        self.assertEqual(cert["scc"], [2, 6, 7, 8])
        self.assertTrue(cert["closure"]["every_repeatable_walk_decreases"])
        # 严格步:x0 与 x1 的自增
        strict_regs = {(r, d) for e in cert["ranking_edges"]
                       for r in e["strict_increase"] for d in ("up",)}
        self.assertIn((0, "up"), strict_regs)
        self.assertIn((1, "up"), strict_regs)
        # 界保护:SCC 锚点处 x0 上界为 5
        self.assertEqual(cert["bounds"][0]["upper_bounds"]["2"], 5)
        # 证书只含 SCC 内部转移(退出边不计入循环闭包)
        pairs = {(t["from"], t["to"]) for t in cert["transitions"]}
        self.assertEqual(pairs, {(2, 6), (6, 7), (7, 8), (8, 2)})

    def test_certificate_is_independently_replayable(self):
        """按证书中的 register_relations 与 bounds 独立重放掩码闭包。

        重放规则(与 closure.description 一致):
          I = 所有内部转移上非调关系的交集;O = 严格步(其源点在 bounds
          中有相应界)的并集;闭路成立 ⟺ I & O != 0。
        """
        res = review_termination(monotone_up_program())
        cert = res["loop_certificates"][0]
        nregs = 2
        atoms = [(r, d) for r in range(nregs) for d in ("down", "up")]
        keep = (1 << (2 * nregs)) - 1
        ranked = 0
        for t in cert["transitions"]:
            for rel in t["register_relations"]:
                base = 2 * rel["reg"]
                d, u = rel["down"], rel["up"]
                if not d["nonincreasing"]:
                    keep &= ~(1 << base)
                if not u["nondecreasing"]:
                    keep &= ~(1 << (base + 1))
                lb = cert["bounds"][rel["reg"]]["lower_bounds"]
                ub = cert["bounds"][rel["reg"]]["upper_bounds"]
                if d["strict"] and str(t["from"]) in lb:
                    ranked |= 1 << base
                if u["strict"] and str(t["from"]) in ub:
                    ranked |= 1 << (base + 1)
        self.assertNotEqual(keep & ranked, 0, "独立重放闭包应找到排序原子")
        # x0、x1 的上升方向均为见证原子
        for r in range(nregs):
            self.assertTrue(keep & ranked & (1 << (2 * r + 1)))
        # 原子名表与位编码一致(供外部工具重放)
        self.assertEqual(atoms[1], (0, "up"))

    def test_monotone_down_counter(self):
        res = review_termination(monotone_down_program())
        self.assertEqual(res["verdict"], "terminating")
        cert = res["loop_certificates"][0]
        self.assertEqual(cert["status"], "proven")
        decreases = {r for e in cert["ranking_edges"]
                     for r in e["strict_decrease"]}
        self.assertIn(0, decreases)
        # 下界保护:锚点 0 处 -x0 <= 0
        self.assertEqual(cert["bounds"][0]["lower_bounds"]["0"], 0)

    def test_alternating_branches_still_terminate(self):
        res = review_termination(alternating_program())
        self.assertEqual(res["verdict"], "terminating")
        self.assertEqual(res["envelope"]["verdict"], "pass")
        cert = res["loop_certificates"][0]
        self.assertEqual(cert["status"], "proven")
        # 两支各贡献不同寄存器的严格下降:x0(第一支)与 x1(第二支)
        dec = {r for e in cert["ranking_edges"] for r in e["strict_decrease"]}
        self.assertEqual(dec, {0, 1})

    def test_acyclic_program_has_no_certificates(self):
        res = review_termination({
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "add", "reg": 0, "value": 1},
                {"id": 1, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": "==", "value": 1}},
                {"id": 2, "op": "halt"},
            ],
        })
        self.assertEqual(res["verdict"], "terminating")
        self.assertEqual(res["loop_certificates"], [])
        self.assertTrue(res["reachable_graph"]["exit_reachable"])

    def test_set_reset_loop_terminates(self):
        res = review_termination({
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "set", "reg": 0, "value": 3},
                {"id": 1, "op": "branch",
                 "cond": {"coefs": {"0": 1}, "op": ">", "value": 0}, "target": 4},
                {"id": 2, "op": "halt"},
                {"id": 3, "op": "halt"},
                {"id": 4, "op": "set", "reg": 0, "value": 0},
                {"id": 5, "op": "goto", "target": 1},
            ],
        })
        self.assertEqual(res["verdict"], "terminating")
        cert = res["loop_certificates"][0]
        # set x0 := 0 的源点下界为 0,严格下降成立且有下界
        reset = [t for t in cert["transitions"]
                 if any(r["rule"] == "set" and r["down"]["strict"]
                        for r in t["register_relations"])]
        self.assertTrue(reset)


class TestUnknown(unittest.TestCase):
    def test_unbounded_increment_closed_loop(self):
        res = review_termination(unbounded_increment_program())
        self.assertEqual(res["verdict"], "unknown")
        fail = res["first_unproven_cycle"]
        self.assertEqual(fail["kind"], "no_ranking_witness")
        self.assertEqual(fail["anchor_point"], 0)
        # 闭包后的可重复闭路,首尾同为锚点
        self.assertEqual(fail["walk"][0], fail["walk"][-1])
        # 首个无法证明的循环关系(稳定程序点)
        self.assertEqual(fail["first_cycle_relation"]["from"], 0)
        # 退出边在不变量下不可行:exit 不可达
        self.assertFalse(res["reachable_graph"]["exit_reachable"])
        ev = {(e["reg"], e["direction"]): e for e in fail["register_evidence"]}
        up = ev[(0, "increase_to_upper_bound")]
        self.assertTrue(up["monotone_throughout"])
        self.assertTrue(up["has_strict_step"])
        self.assertFalse(up["strict_step_source_bounded"])
        self.assertEqual(up["missing"], "upper_bound")
        down = ev[(0, "decrease_to_lower_bound")]
        self.assertFalse(down["monotone_throughout"])
        self.assertEqual(down["missing"], "monotone_relation")
        self.assertEqual(down["first_breaking_edge"]["gap"]["reason"], "increases")
        # 绝不伪造实际死循环
        self.assertIn("并非已构造出实际死循环", fail["note"])
        # 对应 SCC 证书标记为 unproven
        self.assertEqual(res["loop_certificates"][0]["status"], "unproven")
        self.assertFalse(
            res["loop_certificates"][0]["closure"]["every_repeatable_walk_decreases"])

    def test_pingpong_local_decrease_is_not_global_progress(self):
        res = review_termination(pingpong_program())
        self.assertEqual(res["verdict"], "unknown")
        fail = res["first_unproven_cycle"]
        # 坏闭路必须同时经过两支(只走一支的简单环都能证明终止)
        visited = {(e["from"], e["to"]) for e in fail["walk_edges"]}
        self.assertIn((4, 5), visited)
        self.assertIn((7, 8), visited)
        for e in fail["register_evidence"]:
            self.assertEqual(e["missing"], "monotone_relation")

    def test_unknown_is_not_error_and_carries_replay_evidence(self):
        res = review_termination(unbounded_increment_program())
        self.assertIn("points", res)
        self.assertIn("reachable_graph", res)
        self.assertIn("loop_certificates", res)

    def test_verdict_is_deterministic(self):
        import json
        payload = pingpong_program()
        outs = {json.dumps(review_termination(payload), sort_keys=True,
                           ensure_ascii=False) for _ in range(5)}
        self.assertEqual(len(outs), 1)


class TestStructuralErrors(unittest.TestCase):
    def test_structural_error_merged_without_evidence(self):
        res = review_termination({
            "num_registers": 2,
            "initial": [{"lo": 0, "hi": 0}, {"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "set", "reg": 5, "value": 1},
                {"id": 1, "op": "goto", "target": 9},
                {"id": 2, "op": "assert",
                 "cond": {"coefs": {"0": 2}, "op": "<=", "value": 1}},
                {"id": 3, "op": "goto", "target": 2},
            ],
        })
        self.assertEqual(res["verdict"], "error")
        self.assertEqual(res["reason"], "structural_errors")
        kinds = {e["kind"] for e in res["errors"]}
        self.assertIn("register_out_of_bounds", kinds)
        self.assertIn("dangling_jump", kinds)
        self.assertIn("unparseable_constraint", kinds)
        self.assertIn("no_reachable_halt", kinds)
        self.assertNotIn("points", res)
        self.assertNotIn("loop_certificates", res)
        self.assertNotIn("first_unproven_cycle", res)


if __name__ == "__main__":
    unittest.main()
