#!/usr/bin/env python3
"""Isolated exact-source queue prerequisite, not a usable failure runtime."""
from pathlib import Path
import hashlib, json, difflib
root=Path(__file__).resolve().parents[2]
source=root/'.deps/tls-backend-diagnostic-runtime-v4/MP-SPDZ/Tools/WaitQueue.h'
out=root/'.deps/tls-caught-failure-queue/Tools/WaitQueue.h'
a=source.read_text(); b=a
assert b.count('if (running and queue.size() == 0)')==2
b=b.replace('if (running and queue.size() == 0)', 'while (running and queue.size() == 0)')
b=b.replace('        queue.push_back(value);\n        signal();', '        if (running)\n        {\n            queue.push_back(value);\n            signal();\n        }')
b=b.replace('        unlock();\n        return running;', '        const bool result = running;\n        unlock();\n        return result;')
b=b.replace('        running = false;\n        signal();','        running = false;\n        pthread_cond_broadcast(&cond);')
assert b!=a
out.parent.mkdir(parents=True,exist_ok=True)
if out.exists(): assert out.read_text()==b, 'candidate source changed'
out.write_text(b)
work=Path(__file__).parent
(work/'waitqueue-cancellation.patch').write_text(''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='a/Tools/WaitQueue.h',tofile='b/Tools/WaitQueue.h')))
(work/'queue-candidate.json').write_text(json.dumps(dict(candidate_only=True,runtime_integrated=False,source=str(source.relative_to(root)),source_sha256=hashlib.sha256(a.encode()).hexdigest(),candidate_sha256=hashlib.sha256(b.encode()).hexdigest()),indent=2)+'\n')
