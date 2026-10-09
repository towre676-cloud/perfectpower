from http.client import HTTPConnection
from pathlib import Path
import json
import socket
import tempfile
import threading
import time
import unittest
from perfectpower.http_service import QueryHTTPServer
from perfectpower.bounded_dispatch import BoundedDispatcher,QueryDeadline
from perfectpower.industrial_execution import execute


class ReleaseHardeningTests(unittest.TestCase):
    def test_stalled_body_does_not_block_health(self):
        with tempfile.TemporaryDirectory() as directory:
            server=QueryHTTPServer(Path(directory)/'db.sqlite',request_timeout=.15)
            thread=threading.Thread(target=server.serve_forever,kwargs={'poll_interval':.01},daemon=True)
            thread.start();stalled=socket.create_connection(server.server_address)
            try:
                stalled.sendall((f'POST /query HTTP/1.0\r\nHost: 127.0.0.1:{server.server_port}\r\n'
                    'Content-Type: application/json\r\nContent-Length: 100\r\n\r\n{').encode())
                client=HTTPConnection(*server.server_address,timeout=2)
                client.request('GET','/health');response=client.getresponse()
                self.assertEqual(response.status,200);self.assertTrue(json.loads(response.read())['ok']);client.close()
                stalled.settimeout(2);stalled.recv(1024)
            finally:stalled.close();server.shutdown();thread.join();server.server_close()

    def test_query_deadline_stops_worker_and_next_request_recovers(self):
        with tempfile.TemporaryDirectory() as directory:
            dispatcher=BoundedDispatcher(Path(directory)/'db.sqlite',timeout=3)
            try:
                self.assertEqual(json.loads(dispatcher.call({'op':'list'})),[])
                dispatcher.timeout=.001
                with self.assertRaises(QueryDeadline):
                    dispatcher.call({'op':'checked_box','args':dict(coefficients=[0,1],exponent=16,
                        x_bounds=[-127,127],y_bounds=[-128,128],work_limit=65536)})
                dispatcher.timeout=3
                self.assertEqual(json.loads(dispatcher.call({'op':'list'})),[])
            finally:dispatcher.close()

    def test_transport_matches_original_incremental_trace(self):
        script='(set-logic QF_NIA)(declare-const x Int)(assert (= x 1))(check-sat)(push 1)(assert (= x 2))(check-sat)(pop 1)(check-sat)'
        answers=[]
        for mode in ['baseline','transport']:
            result=execute(script,mode=mode)
            self.assertEqual(result['errors'],[])
            answers.append([r['answer'] for r in result['queries']])
            self.assertFalse(result['arithmetic_speedup_claimed'])
        self.assertEqual(answers,[['sat','unsat','sat']]*2)
        with self.assertRaises(ValueError):execute(script,mode='portfolio')


if __name__=='__main__':unittest.main()
