#!/usr/bin/env python3
"""Public fixed-stage failure labels; exception/payload text never rendered."""
import hashlib,json,ssl,subprocess
from pathlib import Path
import fixture_server as fixture
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def main():
 secret='FORBIDDEN_FIXTURE_SECRET'
 cases=[(AssertionError(secret),'assertion'),(ValueError(secret),'format'),(KeyError(secret),'format'),
  (TypeError(secret),'format'),(ssl.SSLError(secret),'tls'),(OSError(secret),'io'),
  (subprocess.CalledProcessError(1,secret,output=secret,stderr=secret),'oracle_process'),(RuntimeError(secret),'internal')]
 for error,category in cases:
  fixture.stage('tls_handshake');text=fixture.failure_diagnostic(error)
  assert text=='protocol fixture failed stage=tls_handshake category='+category and secret not in text
 saved=fixture.run_oracle
 try:
  for answer,expected in [(dict(status=400,credentials=''), 'upgrade_status'),(dict(status=101,credentials=''), 'upgrade_credentials'),(None,'upgrade_oracle')]:
   peer=fixture.Peer.__new__(fixture.Peer);peer.buffer=bytearray(b'GET / HTTP/1.1\r\n\r\n');peer.oracle=Path('/not-executed')
   peer.fixture={'upgrade_username':secret,'upgrade_password':secret}
   def oracle(*args):
    if answer is None:raise subprocess.CalledProcessError(1,secret,output=secret,stderr=secret)
    return answer
   fixture.run_oracle=oracle
   try:peer.upgrade();raise RuntimeError('expected rejection')
   except (AssertionError,subprocess.CalledProcessError) as error:
    text=fixture.failure_diagnostic(error);assert 'stage='+expected+' category=' in text and secret not in text
 finally:fixture.run_oracle=saved
 report={'fixed_exception_categories_checked':8,'upgrade_failure_stages_checked':3,'exception_or_payload_text_logged':False,
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),HERE/'fixture_server.py']}}
 (HERE/'diagnostic-report.json').write_text(json.dumps(report,indent=2)+'\n');print('11 fixed-category/stage diagnostics passed without exception/payload text')
if __name__=='__main__':main()
