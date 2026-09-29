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

# 终止性复核 1:单调计数循环(每轮 -1,不变量下界 0)→ terminating
RECHECK_DECREASING = {
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

# 终止性复核 2:分支交替仍终止——两条回程分别 -1 / -2,闭包后任意回程都严格降
RECHECK_ALTERNATING = {
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

# 终止性复核 2b(对照):一升一降交替,局部下降被抵消 → cannot_prove,不伪称死循环
RECHECK_FAKE_PROGRESS = {
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

# 终止性复核 3:无界自增闭环(x0 每轮 +1,循环不变量无有限上界)→ cannot_prove
RECHECK_UNBOUNDED_UP = {
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
    # 终止性复核 POST /recheck:四类验收场景
    # ------------------------------------------------------------------
    code, body = request("POST", "/recheck", RECHECK_DECREASING)
    check("recheck monotone counting loop terminates",
          code == 200 and body.get("verdict") == "terminating",
          f"code={code} body={body}")
    check("recheck certificate replayable (rank/direction/bounds)",
          bool(body.get("certificates")) and
          body["certificates"][0].get("ranking_register") == 0 and
          body["certificates"][0].get("ranking_direction") == "decreasing" and
          body["certificates"][0].get("ranking_lower_bounds") ==
          {"0": 0, "1": 1, "2": 0})
    check("recheck certificate lists closed cycle relations",
          all(rels.get("0") == "<"
              for rels in body["certificates"][0]["closed_cycle_relations"].values())
          if body.get("certificates") else False)

    code, body = request("POST", "/recheck", RECHECK_ALTERNATING)
    check("recheck alternating branches still terminate",
          code == 200 and body.get("verdict") == "terminating",
          f"code={code} body={body}")
    check("recheck closure joins per-path relations",
          bool(body.get("certificates")) and
          all(rels.get("0") == "<"
              for rels in body["certificates"][0]["closed_cycle_relations"].values()))

    code, body = request("POST", "/recheck", RECHECK_FAKE_PROGRESS)
    check("recheck fake alternating progress cannot be proven",
          code == 200 and body.get("verdict") == "cannot_prove",
          f"code={code} body={body}")
    check("recheck does not fabricate infinite loop",
          body.get("first_unproven_loop", {}).get("kind") ==
          "termination_proof_failure" and
          "并非断言存在实际死循环" in
          body.get("first_unproven_loop", {}).get("note", ""))
    check("recheck failure names missing decrease at stable head",
          body.get("first_unproven_loop", {}).get("loop_head") == 0 and
          any(m.get("kind") == "strict_decrease"
              for c in body.get("first_unproven_loop", {})
              .get("register_candidates", [])
              for m in c.get("missing", [])))

    code, body = request("POST", "/recheck", RECHECK_UNBOUNDED_UP)
    check("recheck unbounded self-increment loop cannot be proven",
          code == 200 and body.get("verdict") == "cannot_prove",
          f"code={code} body={body}")
    check("recheck names missing upper bound",
          any(m.get("kind") == "upper_bound"
              for c in body.get("first_unproven_loop", {})
              .get("register_candidates", [])
              for m in c.get("missing", [])))

    # 审计门禁:包线未过的脚本不接受复核
    code, body = request("POST", "/recheck", FAIL_CASE)
    check("recheck gated on passed envelope audit",
          code == 200 and body.get("verdict") == "error" and
          body.get("reason") == "envelope_audit_not_passed" and
          body.get("first_unproven_point") == 2)

    # 结构错误:合并反馈,不携带循环证书等旧结论
    code, body = request("POST", "/recheck", ERROR_CASE)
    check("recheck structural errors merged without certificates",
          code == 200 and body.get("verdict") == "error" and
          "certificates" not in body and "loops" not in body)

    # 复核不改变 /audit 的无状态结论(原审计回归)
    code, body = request("POST", "/audit", PASS_CASE)
    check("audit regression after rechecks",
          code == 200 and body.get("verdict") == "pass" and
          "certificates" not in body)

    if _failures:
        print(f"smoke FAILED: {len(_failures)} check(s): {', '.join(_failures)}")
        return 1
    print("smoke OK: all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
