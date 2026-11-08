#!/usr/bin/env python3
"""Split successful public recipient evidence into client/receiver-only fixtures."""
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
def prepare(f):
 assert f['public_disposable_fixture_only'] and len(f['conversations'])==2
 header=['#pragma once','// PUBLIC DISPOSABLE FIXTURES ONLY. Never authenticated bootstrap.','#include <vector>','#include <string>','#include <stdexcept>','namespace signal_mpc {','struct PublicTextFixture {',
 ' static std::vector<unsigned char> decode(const std::string& text){std::vector<unsigned char> out;for(size_t i=0;i<text.size();i+=2)out.push_back(std::stoul(text.substr(i,2),nullptr,16));return out;}',
 ' static std::vector<unsigned char> initial(size_t slot){switch(slot){']
 for slot,c in enumerate(f['conversations']):header.append(' case '+str(slot)+':return decode("'+c['initial']+'");')
 header+=[' default:throw std::runtime_error("public text fixture slot");}}',' static std::vector<unsigned char> text_input(size_t slot,size_t round){if(slot>=2||round>=2)throw std::runtime_error("public text fixture index");switch(2*slot+round){']
 for slot,c in enumerate(f['conversations']):
  for round,(text,time)in enumerate(zip(c['expected_text'],c['timestamps'])):
   body=text.encode();assert len(body)<=48
   raw=b'\xff'+len(body).to_bytes(2,'big')+body+bytes(48-len(body))+time.to_bytes(8,'big')
   header.append(' case '+str(2*slot+round)+':return decode("'+raw.hex()+'");')
 header+=[' default:throw std::runtime_error("public text fixture input");}}','};','}']
 (HERE/'PublicTextFixture.h').write_text('\n'.join(header)+'\n')
 # No sender initialization/private identity/final message keys enter server.
 server={k:v for k,v in f.items()if k!='conversations'}
 server['conversations']=[{k:v for k,v in c.items()if k!='initial'}for c in f['conversations']]
 (HERE/'server-fixtures.json').write_text(json.dumps(server,indent=2)+'\n')
if __name__=='__main__':prepare(json.loads((HERE/'text-fixtures.json').read_text()))
