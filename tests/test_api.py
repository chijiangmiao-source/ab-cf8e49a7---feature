"""HTTP 接口单元测试:健康路径、审计接口、错误码。"""
import json
import threading
import unittest
import urllib.error
import urllib.request
from http.server import ThreadingHTTPServer

from app.server import Handler


class ApiTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        cls.port = cls.server.server_address[1]
        cls.thread = threading.Thread(target=cls.server.serve_forever, daemon=True)
        cls.thread.start()

    @classmethod
    def tearDownClass(cls):
        cls.server.shutdown()
        cls.server.server_close()
        cls.thread.join(timeout=5)

    def _get(self, path):
        try:
            with urllib.request.urlopen(
                    f"http://127.0.0.1:{self.port}{path}", timeout=5) as resp:
                return resp.status, json.loads(resp.read())
        except urllib.error.HTTPError as e:
            return e.code, json.loads(e.read())

    def _post(self, path, payload=None, raw=None):
        data = raw if raw is not None else json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(
            f"http://127.0.0.1:{self.port}{path}", data=data,
            headers={"Content-Type": "application/json"})
        try:
            with urllib.request.urlopen(req, timeout=5) as resp:
                return resp.status, json.loads(resp.read())
        except urllib.error.HTTPError as e:
            return e.code, json.loads(e.read())

    def test_health(self):
        code, body = self._get("/health")
        self.assertEqual(code, 200)
        self.assertEqual(body["status"], "ok")
        self.assertIn("version", body)

    def test_audit_pass(self):
        code, body = self._post("/audit", {
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 2}],
            "instructions": [
                {"id": 0, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": "<=", "value": 2}},
                {"id": 1, "op": "halt"},
            ],
        })
        self.assertEqual(code, 200)
        self.assertEqual(body["verdict"], "pass")

    def test_audit_fail(self):
        code, body = self._post("/audit", {
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "add", "reg": 0, "value": 4},
                {"id": 1, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": "<", "value": 4}},
                {"id": 2, "op": "halt"},
            ],
        })
        self.assertEqual(code, 200)
        self.assertEqual(body["verdict"], "fail")
        self.assertEqual(body["first_unproven"]["point"], 1)
        self.assertEqual(body["first_unproven"]["kind"], "abstract_alarm")

    def test_audit_structural_error(self):
        code, body = self._post("/audit", {
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [{"id": 0, "op": "goto", "target": 0}],
        })
        self.assertEqual(code, 200)
        self.assertEqual(body["verdict"], "error")
        self.assertNotIn("points", body)

    # ------------------------------------------------------------------
    # 终止性复核 POST /terminate
    # ------------------------------------------------------------------
    def _down_counter(self):
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

    def test_terminate_monotone_counter(self):
        code, body = self._post("/terminate", self._down_counter())
        self.assertEqual(code, 200)
        self.assertEqual(body["verdict"], "terminating")
        self.assertEqual(body["envelope"]["verdict"], "pass")
        self.assertTrue(body["reachable_graph"]["exit_reachable"])
        cert = body["loop_certificates"][0]
        self.assertEqual(cert["status"], "proven")
        self.assertTrue(cert["closure"]["every_repeatable_walk_decreases"])

    def test_terminate_unknown_unbounded_loop(self):
        code, body = self._post("/terminate", {
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "add", "reg": 0, "value": 1},
                {"id": 1, "op": "branch",
                 "cond": {"coefs": {"0": 1}, "op": "<", "value": 0}, "target": 3},
                {"id": 2, "op": "goto", "target": 0},
                {"id": 3, "op": "halt"},
            ],
        })
        self.assertEqual(code, 200)
        self.assertEqual(body["verdict"], "unknown")
        self.assertEqual(body["first_unproven_cycle"]["kind"],
                         "no_ranking_witness")
        self.assertIn("并非已构造出实际死循环",
                      body["first_unproven_cycle"]["note"])

    def test_terminate_structural_error_has_no_stale_evidence(self):
        code, body = self._post("/terminate", {
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [{"id": 0, "op": "goto", "target": 0}],
        })
        self.assertEqual(code, 200)
        self.assertEqual(body["verdict"], "error")
        self.assertEqual([e["kind"] for e in body["errors"]],
                         ["no_reachable_halt"])
        self.assertNotIn("points", body)
        self.assertNotIn("loop_certificates", body)

    def test_terminate_bad_json_and_not_found(self):
        code, _ = self._post("/terminate", raw=b"{not json")
        self.assertEqual(code, 400)
        code, _ = self._post("/other", {})
        self.assertEqual(code, 404)

    def test_audit_format_unchanged_by_terminate(self):
        """新增 /terminate 后,/audit 的结论与字段形态保持原样。"""
        code, body = self._post("/audit", self._down_counter())
        self.assertEqual(code, 200)
        self.assertEqual(body["verdict"], "pass")
        self.assertNotIn("loop_certificates", body)
        self.assertNotIn("envelope", body)
        self.assertIn("fixpoint", body)

    def test_bad_json(self):
        code, body = self._post("/audit", raw=b"{not json")
        self.assertEqual(code, 400)

    def test_not_found(self):
        code, _ = self._get("/nope")
        self.assertEqual(code, 404)
        code, _ = self._post("/health", {})
        self.assertEqual(code, 404)


if __name__ == "__main__":
    unittest.main()
