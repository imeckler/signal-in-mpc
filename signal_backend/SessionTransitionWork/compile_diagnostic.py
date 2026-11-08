#!/usr/bin/env python3
"""Public-source compiler diagnostics only; never run around private workers.

Wrappers call each original pinned compiler method exactly once with unchanged
arguments/results. They report public phase names/time/process high-water RSS;
faulthandler reports public compiler source stack frames every60seconds.
"""
import faulthandler,functools,json,resource,runpy,sys,time
from pathlib import Path
sys.path.insert(0,str(Path.cwd()))
from Compiler.program import Program,Tape
start=time.monotonic()
def note(phase,event):
 r=resource.getrusage(resource.RUSAGE_SELF)
 print('COMPILE_PHASE '+json.dumps(dict(phase=phase,event=event,elapsed_seconds=time.monotonic()-start,user_cpu_seconds=r.ru_utime,system_cpu_seconds=r.ru_stime,max_rss=r.ru_maxrss,max_rss_unit='bytes'if sys.platform=='darwin'else'KiB')),flush=True)
def wrap(cls,name):
 original=getattr(cls,name)
 @functools.wraps(original)
 def observed(*args,**kwargs):
  note(cls.__name__+'.'+name,'begin')
  try:return original(*args,**kwargs)
  finally:note(cls.__name__+'.'+name,'end')
 setattr(cls,name,observed)
for cls,name in [(Program,'finalize'),(Program,'finalize_tape'),(Tape,'optimize'),(Tape,'write_bytes')]:wrap(cls,name)
faulthandler.enable();faulthandler.dump_traceback_later(60,repeat=True)
sys.argv[0]='compile.py';note('compile','begin')
try:runpy.run_path('compile.py',run_name='__main__')
finally:faulthandler.cancel_dump_traceback_later();note('compile','end')
