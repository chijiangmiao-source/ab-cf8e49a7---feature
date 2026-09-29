"""终止性复核单元测试:单调计数、分支交替、伪进展、无界自增、
SCC 闭包关系代数、结构错误与审计门禁。
"""
import unittest

from app.analyzer import analyze
from app.termination import analyze_termination, compose, join_rel


def monotone_decrement_program():
    """单调递减计数循环:x0∈[0,5],循环体 add -1,由不变量下界 0 保护。"""
    return {
        "num_registers": 1,
        "initial": [{"lo": 0, "hi": 5}],
        "instructions": [
            {"id": 0, "op": "branch",
             "cond": {"coefs": {"0": 1}, "op": "<=", "value": 0}, "target": 3},
            {"id": 1, "op": "add", "reg": 0, "value": -1},
            {"id": 2, "op": "goto", "target": 0},
            {"id": 3, "op": "halt"},
        ],
    }


def alternating_branches_program():
    """两条循环回程路径分别 add -1 / add -2,x0 在每条路径上都严格下降。"""
    return {
        "num_registers": 2,
        "initial": [{"lo": 0, "hi": 5}, {"lo": 0, "hi": 0}],
        "instructions": [
            {"id": 0, "op": "branch",
             "cond": {"coefs": {"0": 1}, "op": "<=", "value": 0}, "target": 6},
            {"id": 1, "op": "branch",
             "cond": {"coefs": {"1": 1}, "op": "==", "value": 0}, "target": 4},
            {"id": 2, "op": "add", "reg": 0, "value": -1},
            {"id": 3, "op": "goto", "target": 5},
            {"id": 4, "op": "add", "reg": 0, "value": -2},
            {"id": 5, "op": "goto", "target": 0},
            {"id": 6, "op": "halt"},
        ],
    }


def fake_progress_program():
    """一条回程 add -1,另一条 add +1:局部下降被交替抵消,不得判终止。"""
    return {
        "num_registers": 2,
        "initial": [{"lo": 0, "hi": 5}, {"lo": 0, "hi": 0}],
        "instructions": [
            {"id": 0, "op": "branch",
             "cond": {"coefs": {"0": 1}, "op": "<=", "value": 0}, "target": 6},
            {"id": 1, "op": "branch",
             "cond": {"coefs": {"1": 1}, "op": "==", "value": 0}, "target": 4},
            {"id": 2, "op": "add", "reg": 0, "value": -1},
            {"id": 3, "op": "goto", "target": 5},
            {"id": 4, "op": "add", "reg": 0, "value": 1},
            {"id": 5, "op": "goto", "target": 0},
            {"id": 6, "op": "halt"},
        ],
    }


def unbounded_increment_program():
    """无界自增闭环:x0 每轮 +1,循环不变量不给出有限上界。"""
    return {
        "num_registers": 2,
        "initial": [{"lo": 0, "hi": 0}, {"lo": 0, "hi": 0}],
        "instructions": [
            {"id": 0, "op": "branch",
             "cond": {"coefs": {"1": 1}, "op": "==", "value": 1}, "target": 4},
            {"id": 1, "op": "add", "reg": 0, "value": 1},
            {"id": 2, "op": "set", "reg": 1, "value": 0},
            {"id": 3, "op": "goto", "target": 0},
            {"id": 4, "op": "halt"},
        ],
    }


class TestRelationAlgebra(unittest.TestCase):
    def test_compose_table(self):
        self.assertEqual(compose("lt", "lt"), "lt")
        self.assertEqual(compose("eq", "lt"), "lt")
        self.assertEqual(compose("le", "lt"), "lt")
        self.assertEqual(compose("lt", "le"), "lt")
        self.assertEqual(compose("gt", "ge"), "gt")
        self.assertEqual(compose("unk", "lt"), "unk")
        # 一升一降无法判定
        self.assertEqual(compose("lt", "gt"), "unk")

    def test_join_keeps_only_common_consequence(self):
        self.assertEqual(join_rel("lt", "eq"), "le")
        self.assertEqual(join_rel("eq", "gt"), "ge")
        self.assertEqual(join_rel("lt", "le"), "le")
        self.assertEqual(join_rel("lt", "gt"), "unk")
        self.assertEqual(join_rel("le", "eq"), "le")
        self.assertEqual(join_rel("ge", "eq"), "ge")
        self.assertEqual(join_rel("gt", "ge"), "ge")


class TestTerminating(unittest.TestCase):
    def test_monotone_decrement_loop(self):
        res = analyze_termination(monotone_decrement_program())
        self.assertEqual(res["verdict"], "terminating")
        self.assertEqual(res["envelope_audit"], "pass")
        self.assertEqual(res["loops"], {"total": 1, "proven": 1, "unproven": 0})
        cert = res["certificates"][0]
        self.assertEqual(cert["loop_head"], 0)
        self.assertEqual(cert["points"], [0, 1, 2])
        self.assertEqual(cert["ranking_register"], 0)
        self.assertEqual(cert["ranking_direction"], "decreasing")
        # 下界由不变量保护,每一点都给出
        self.assertEqual(cert["ranking_lower_bounds"], {"0": 0, "1": 1, "2": 0})
        # 每个程序点的闭环关系对 x0 都严格下降
        for p, rels in cert["closed_cycle_relations"].items():
            self.assertEqual(rels["0"], "<", msg=f"point {p}")
        # 退出边列出(分支真向 halt)
        self.assertEqual(cert["exit_edges"], [{"from": 0, "to": 3, "kind": "branch_true"}])

    def test_certificate_is_self_replayable(self):
        res = analyze_termination(monotone_decrement_program())
        cert = res["certificates"][0]
        edges = {(e["from"], e["to"]): e["register_relations"]
                 for e in cert["internal_edges"]}
        # 逐转移关系:只有循环体 add -1 是严格下降,其余恒等
        self.assertEqual(edges[(1, 2)], {"0": "<"})
        self.assertEqual(edges[(0, 1)], {"0": "=="})
        self.assertEqual(edges[(2, 0)], {"0": "=="})

    def test_alternating_branches_both_decrease(self):
        res = analyze_termination(alternating_branches_program())
        self.assertEqual(res["verdict"], "terminating")
        cert = res["certificates"][0]
        self.assertEqual(cert["ranking_register"], 0)
        # 闭包后任意回程路径都严格降(尽管单条边多数恒等)
        for rels in cert["closed_cycle_relations"].values():
            self.assertEqual(rels["0"], "<")

    def test_bounded_increment_terminates_via_upper_bound(self):
        # 冒烟 PASS_CASE 的计数循环:x0 每轮 +1,循环不变量给出上界 5
        program = {
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
        res = analyze_termination(program)
        self.assertEqual(res["verdict"], "terminating")
        cert = res["certificates"][0]
        self.assertEqual(cert["ranking_direction"], "increasing")
        self.assertEqual(cert["ranking_upper_bounds"]["2"], 5)

    def test_straight_line_has_no_loops(self):
        res = analyze_termination({
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": ">=", "value": 0}},
                {"id": 1, "op": "halt"},
            ],
        })
        self.assertEqual(res["verdict"], "terminating")
        self.assertEqual(res["loops"]["total"], 0)
        self.assertEqual(res["certificates"], [])


class TestCannotProve(unittest.TestCase):
    def test_fake_progress_is_not_global_progress(self):
        res = analyze_termination(fake_progress_program())
        self.assertEqual(res["verdict"], "cannot_prove")
        loop = res["first_unproven_loop"]
        self.assertEqual(loop["loop_head"], 0)
        self.assertEqual(loop["kind"], "termination_proof_failure")
        # 不得伪造实际死循环
        self.assertIn("并非断言存在实际死循环", loop["note"])
        # x0 在 head 的闭环关系未知(一升一降交替)
        cand = {c["register"]: c for c in loop["register_candidates"]}
        self.assertEqual(cand[0]["closed_self_relation_at_head"], "?")
        kinds = {m["kind"] for m in cand[0]["missing"]}
        self.assertIn("strict_decrease", kinds)

    def test_unbounded_increment_missing_upper_bound(self):
        res = analyze_termination(unbounded_increment_program())
        self.assertEqual(res["verdict"], "cannot_prove")
        cand = {c["register"]: c
                for c in res["first_unproven_loop"]["register_candidates"]}
        # x0 严格自增但无有限上界
        self.assertIsNone(cand[0]["upper_bound_in_scc"])
        kinds = {m["kind"] for m in cand[0]["missing"]}
        self.assertIn("upper_bound", kinds)

    def test_diagnosis_reports_at_stable_head(self):
        res = analyze_termination(fake_progress_program())
        # 稳定程序点:编号最小的循环头
        self.assertEqual(res["first_unproven_loop"]["loop_head"], 0)

    def test_decrement_without_lower_bound(self):
        # x0 每轮 -1 但循环不变量无有限下界(初值下端无界);
        # 退出条件挂在抽象上可达的 x1 上,结构校验通过但排名缺下界
        res = analyze_termination({
            "num_registers": 2,
            "initial": [{"lo": None, "hi": 0}, {"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "branch",
                 "cond": {"coefs": {"1": 1}, "op": "==", "value": 1}, "target": 4},
                {"id": 1, "op": "add", "reg": 0, "value": -1},
                {"id": 2, "op": "set", "reg": 1, "value": 0},
                {"id": 3, "op": "goto", "target": 0},
                {"id": 4, "op": "halt"},
            ],
        })
        self.assertEqual(res["verdict"], "cannot_prove")
        cand = {c["register"]: c
                for c in res["first_unproven_loop"]["register_candidates"]}
        self.assertIsNone(cand[0]["lower_bound_in_scc"])
        kinds = {m["kind"] for m in cand[0]["missing"]}
        self.assertIn("lower_bound", kinds)


class TestGatingAndErrors(unittest.TestCase):
    def test_recheck_requires_passed_audit(self):
        res = analyze_termination({
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": "<=", "value": -1}},
                {"id": 1, "op": "halt"},
            ],
        })
        self.assertEqual(res["verdict"], "error")
        self.assertEqual(res["reason"], "envelope_audit_not_passed")
        self.assertEqual(res["first_unproven_point"], 0)
        self.assertNotIn("certificates", res)

    def test_structural_errors_merged_without_stale_conclusions(self):
        res = analyze_termination({
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [{"id": 0, "op": "goto", "target": 0}],
        })
        self.assertEqual(res["verdict"], "error")
        self.assertEqual(res["reason"], "structural_errors")
        self.assertEqual([e["kind"] for e in res["errors"]], ["no_reachable_halt"])
        for key in ("points", "assertions", "certificates", "loops"):
            self.assertNotIn(key, res)

    def test_audit_endpoint_unchanged(self):
        # 原 /audit 结论形态回归
        res = analyze(monotone_decrement_program())
        self.assertEqual(res["verdict"], "pass")
        self.assertNotIn("certificates", res)


if __name__ == "__main__":
    unittest.main()
