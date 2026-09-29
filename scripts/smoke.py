#!/usr/bin/env python3
"""verify 容器的 HTTP 冒烟:健康路径、审计接口三类结论、镜像构建(版本)核对。

通过环境变量配置:
    APP_URL          被测服务地址(默认 http://127.0.0.1:8080)
    EXPECTED_VERSION 期望的构建版本(默认 1.0.0),与 /health 返回比对

全部检查通过以状态码 0 退出,否则状态码 1。
"""
import json
import os
import sys
import time
import urllib.error
import urllib.request

APP_URL = os.environ.get("APP_URL", "http://127.0.0.1:8080").rstrip("/")
EXPECTED_VERSION = os.environ.get("EXPECTED_VERSION", "1.0.0")
WAIT_SECONDS = float(os.environ.get("SMOKE_WAIT_SECONDS", "30"))

# 含循环与寄存器间关系的脚本: widening + 下降复算后应放行
PASS_CASE = {
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

# 不可证断言:应返回 fail,首个未证位置为程序点 2
FAIL_CASE = {
    "num_registers": 1,
    "initial": [{"lo": 0, "hi": 0}],
    "instructions": [
        {"id": 0, "op": "set", "reg": 0, "value": 0},
        {"id": 1, "op": "add", "reg": 0, "value": 5},
        {"id": 2, "op": "assert",
         "cond": {"coefs": {"0": 1}, "op": "<=", "value": 3}},
        {"id": 3, "op": "halt"},
    ],
}

# 四类结构错误:寄存器越界 + 跳转悬空 + 不可解析约束 + 无可达终止,应合并反馈
ERROR_CASE = {
    "num_registers": 2,
    "initial": [{"lo": 0, "hi": 0}, {"lo": 0, "hi": 0}],
    "instructions": [
        {"id": 0, "op": "set", "reg": 5, "value": 1},
        {"id": 1, "op": "goto", "target": 9},
        {"id": 2, "op": "assert",
         "cond": {"coefs": {"0": 2}, "op": "<=", "value": 1}},
        {"id": 3, "op": "goto", "target": 2},
    ],
}

# 终止性复核 1:单调递减计数循环(x0 从 3 递减到 0),应 terminating
TERM_DOWN_CASE = {
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

# 终止性复核 2:分支交替仍终止
#   x0>0 走第一支(x0--, x1++);否则 x1>0 走第二支(x1--)。
#   不存在单一寄存器在每条回边上都下降,需 SCC 闭路闭包才能证明。
TERM_ALTERNATING_CASE = {
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

# 终止性复核 3:无界自增闭环(x0 每圈 +1,退出条件 x0<0 不变量下不可行)
TERM_UNBOUNDED_CASE = {
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

_failures = []


def check(name, ok, detail=""):
    mark = "PASS" if ok else "FAIL"
    print(f"[{mark}] {name}" + (f" -- {detail}" if detail and not ok else ""))
    if not ok:
        _failures.append(name)


def request(method, path, payload=None):
    data = json.dumps(payload).encode("utf-8") if payload is not None else None
    req = urllib.request.Request(APP_URL + path, data=data, method=method,
                                 headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=5) as resp:
            return resp.status, json.loads(resp.read())
    except urllib.error.HTTPError as e:
        return e.code, json.loads(e.read())


def wait_ready():
    deadline = time.time() + WAIT_SECONDS
    while time.time() < deadline:
        try:
            code, body = request("GET", "/health")
            if code == 200 and body.get("status") == "ok":
                return body
        except (OSError, ValueError):
            pass
        time.sleep(0.5)
    return None


def main():
    health = wait_ready()
    check("health endpoint reachable", health is not None)
    if health is None:
        return 1

    # 镜像构建核对:运行中的镜像须报告期望的构建版本
    check("image build version matches",
          health.get("version") == EXPECTED_VERSION,
          f"expected {EXPECTED_VERSION}, got {health.get('version')!r}")

    code, body = request("POST", "/audit", PASS_CASE)
    check("pass case verdict", code == 200 and body.get("verdict") == "pass",
          f"code={code} body={body}")
    check("pass case post-fixpoint verified",
          body.get("fixpoint", {}).get("post_fixpoint_verified") is True)
    check("pass case per-point invariants present",
          "2" in body.get("points", {}) and
          any(c["text"] == "x0 - x1 <= 0" for c in body["points"]["3"]["invariant"]))

    code, body = request("POST", "/audit", FAIL_CASE)
    first = body.get("first_unproven", {})
    check("fail case verdict", code == 200 and body.get("verdict") == "fail",
          f"code={code} body={body}")
    check("fail case first unproven point", first.get("point") == 2)
    check("fail case is abstract alarm, not counterexample",
          first.get("kind") == "abstract_alarm")
    check("fail case uncovered envelope bound",
          bool(first.get("uncovered")) and first["uncovered"][0].get("bound") == 5)

    code, body = request("POST", "/audit", ERROR_CASE)
    kinds = {e.get("kind") for e in body.get("errors", [])}
    check("error case verdict", code == 200 and body.get("verdict") == "error",
          f"code={code} body={body}")
    check("error case merges all four structural kinds",
          {"register_out_of_bounds", "dangling_jump",
           "unparseable_constraint", "no_reachable_halt"} <= kinds,
          f"kinds={kinds}")
    check("error case returns no stale evidence",
          "points" not in body and "assertions" not in body)

    # 无状态性:结构错误之后再次审计,结论不受既往请求影响
    code, body = request("POST", "/audit", PASS_CASE)
    check("no stale state after error case",
          code == 200 and body.get("verdict") == "pass")

    # ------------------------------------------------------------------
    # 终止性复核 POST /terminate
    # ------------------------------------------------------------------
    code, body = request("POST", "/terminate", TERM_DOWN_CASE)
    certs = body.get("loop_certificates", [])
    check("terminate monotone counter verdict",
          code == 200 and body.get("verdict") == "terminating",
          f"code={code} body={body}")
    check("terminate monotone counter reuses envelope pass",
          body.get("envelope", {}).get("verdict") == "pass")
    check("terminate monotone counter certificate proven",
          len(certs) == 1 and certs[0].get("status") == "proven"
          and certs[0]["closure"].get("every_repeatable_walk_decreases") is True)
    dec_regs = {r for e in certs[0].get("ranking_edges", [])
                for r in e.get("strict_decrease", [])} if certs else set()
    check("terminate monotone counter strict self-decrease bounded",
          0 in dec_regs and "0" in certs[0]["bounds"][0]["lower_bounds"]
          if certs else False)

    code, body = request("POST", "/terminate", TERM_ALTERNATING_CASE)
    certs = body.get("loop_certificates", [])
    check("terminate alternating branches verdict",
          code == 200 and body.get("verdict") == "terminating",
          f"code={code} body={body}")
    dec_regs = {r for e in certs[0].get("ranking_edges", [])
                for r in e.get("strict_decrease", [])} if certs else set()
    check("alternating closure combines both branches (x0 and x1)",
          len(certs) == 1 and certs[0].get("status") == "proven"
          and dec_regs == {0, 1}, f"dec_regs={dec_regs}")

    code, body = request("POST", "/terminate", TERM_UNBOUNDED_CASE)
    fail = body.get("first_unproven_cycle", {})
    ev = {(e.get("reg"), e.get("direction")): e
          for e in fail.get("register_evidence", [])}
    check("terminate unbounded increment verdict unknown",
          code == 200 and body.get("verdict") == "unknown",
          f"code={code} body={body}")
    check("unbounded case names first unproven cycle relation at stable point",
          fail.get("kind") == "no_ranking_witness"
          and fail.get("first_cycle_relation", {}).get("from") == 0)
    check("unbounded case explains missing upper bound, not a fake infinite loop",
          ev.get((0, "increase_to_upper_bound"), {}).get("missing") == "upper_bound"
          and "并非已构造出实际死循环" in fail.get("note", ""))
    check("unbounded case infeasible exit excluded from reachable graph",
          body.get("reachable_graph", {}).get("exit_reachable") is False)

    code, body = request("POST", "/terminate", ERROR_CASE)
    kinds = {e.get("kind") for e in body.get("errors", [])}
    check("terminate structural errors merged without stale evidence",
          code == 200 and body.get("verdict") == "error"
          and {"register_out_of_bounds", "dangling_jump",
               "unparseable_constraint", "no_reachable_halt"} <= kinds
          and "points" not in body and "loop_certificates" not in body,
          f"kinds={kinds}")

    # 终止性复核无状态性:复核未知之后,/audit 回归结论仍不受影响
    code, body = request("POST", "/audit", PASS_CASE)
    check("audit regression after termination review",
          code == 200 and body.get("verdict") == "pass"
          and body.get("fixpoint", {}).get("post_fixpoint_verified") is True)
    code, body = request("POST", "/audit", FAIL_CASE)
    check("audit fail-case regression after termination review",
          code == 200 and body.get("verdict") == "fail"
          and body.get("first_unproven", {}).get("point") == 2)

    if _failures:
        print(f"smoke FAILED: {len(_failures)} check(s): {', '.join(_failures)}")
        return 1
    print("smoke OK: all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
