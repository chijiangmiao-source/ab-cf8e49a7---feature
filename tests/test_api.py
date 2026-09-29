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

    def test_recheck_terminating(self):
        code, body = self._post("/recheck", {
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 5}],
            "instructions": [
                {"id": 0, "op": "branch",
                 "cond": {"coefs": {"0": 1}, "op": "<=", "value": 0}, "target": 3},
                {"id": 1, "op": "add", "reg": 0, "value": -1},
                {"id": 2, "op": "goto", "target": 0},
                {"id": 3, "op": "halt"},
            ],
        })
        self.assertEqual(code, 200)
        self.assertEqual(body["verdict"], "terminating")
        self.assertEqual(body["loops"]["proven"], 1)
        cert = body["certificates"][0]
        self.assertEqual(cert["ranking_register"], 0)
        self.assertEqual(cert["ranking_lower_bounds"], {"0": 0, "1": 1, "2": 0})

    def test_recheck_cannot_prove_unbounded_loop(self):
        code, body = self._post("/recheck", {
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
        })
        self.assertEqual(code, 200)
        self.assertEqual(body["verdict"], "cannot_prove")
        self.assertEqual(body["first_unproven_loop"]["kind"],
                         "termination_proof_failure")

    def test_recheck_requires_passed_audit(self):
        code, body = self._post("/recheck", {
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": "<=", "value": -1}},
                {"id": 1, "op": "halt"},
            ],
        })
        self.assertEqual(code, 200)
        self.assertEqual(body["verdict"], "error")
        self.assertEqual(body["reason"], "envelope_audit_not_passed")

    def test_recheck_structural_error_no_evidence(self):
        code, body = self._post("/recheck", {
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [{"id": 0, "op": "goto", "target": 0}],
        })
        self.assertEqual(code, 200)
        self.assertEqual(body["verdict"], "error")
        self.assertNotIn("certificates", body)

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
