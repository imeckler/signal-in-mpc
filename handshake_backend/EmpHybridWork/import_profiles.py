"""Import existing Lean circuit artifacts and their fixtures as runner profiles.

The earlier work exported many circuits (`.deps/*-artifacts/NAME.json`) with
fixture lanes (`NAME-fixtures.json`, input/output hex) whose expected outputs
were established by that work's own references. This script lowers a selected
artifact with the project's standard bit order, re-checks every chosen lane
against the lowered gates in the clear, pins the result and writes a profile
for `check_lean_runs.py`. No circuit is defined here.
"""
import hashlib,json,pathlib,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;OUT=ROOT/'.deps/emp-hybrid-word-v1';OUT.mkdir(exist_ok=True)
sys.path.insert(0,str(HERE))
from hybrid_lowering import lower,flat_text,byte_bits,evaluate_bytes
SELECTED={
    'signal-spqr-send-256':('signal-steady-send-artifacts/signal-spqr-send-256-3-3-3-3-0-none-present','Steady-state send with SPQR, 256-byte plaintext'),
    'signal-new-ratchet-receive':('signal-new-ratchet-receive-artifacts/signal-new-ratchet-receive-2-2-96','Receive that starts a new DH ratchet chain'),
}
names=sys.argv[1:] or list(SELECTED);report={}
subprocess.run(['lake','build','word_mask_emitter'],cwd=ROOT,check=True,capture_output=True)
for name in names:
    stem,description=SELECTED[name];artifact=ROOT/'.deps'/(stem+'.json');fixture_file=ROOT/'.deps'/(stem+'-fixtures.json')
    image=json.loads(artifact.read_text());n,gates,outputs=lower(image,msb_first=True);fixtures=[]
    for index,lane in enumerate(json.loads(fixture_file.read_text())[:2]):
        data,want=bytes.fromhex(lane['input']),bytes.fromhex(lane['output'])
        if 8*len(data)!=n or 8*len(want)!=len(outputs):raise ValueError(name+' fixture shape')
        if evaluate_bytes(gates,outputs,byte_bits(data,True),True)!=want:raise AssertionError((name,index))
        fixtures.append(dict(label=lane.get('label') or 'lane-%d'%index,input=lane['input'],output=lane['output']))
    text=flat_text(n,gates,outputs);(OUT/(name+'.flat')).write_text(text);digest=hashlib.sha256(text.encode()).hexdigest()
    equal=subprocess.run(['lake','exe','word_mask_emitter','equal',str(len(outputs))],cwd=ROOT,check=True,capture_output=True).stdout.decode()
    (OUT/(name+'-equal.flat')).write_text(equal)
    (OUT/(name+'.json')).write_text(json.dumps(dict(circuit=name+'.flat',circuit_sha256=digest,equal=name+'-equal.flat',equal_sha256=hashlib.sha256(equal.encode()).hexdigest(),input_bits=n,output_bits=len(outputs),bit_order='msb',fixtures=fixtures),indent=2)+'\n')
    report[name]=dict(description=description,artifact=str(artifact.relative_to(ROOT)),artifact_sha256=hashlib.sha256(artifact.read_bytes()).hexdigest(),fixtures_sha256=hashlib.sha256(fixture_file.read_bytes()).hexdigest(),flat_sha256=digest,and_gates=sum(g[0]=='A' for g in gates),input_bits=n,output_bits=len(outputs),lanes=len(fixtures))
    print(json.dumps({name:dict(and_gates=report[name]['and_gates'],input_bits=n,output_bits=len(outputs))}),flush=True)
target=HERE/'imported-profiles-report.json';prior=json.loads(target.read_text()) if target.exists() else dict(profiles={})
prior['profiles'].update(report);prior['passed']=True;prior['scope']='Existing exported Lean circuits lowered with the standard bit order and re-checked against their existing fixture lanes in the clear. Expected outputs are those of the earlier fixture work, not recomputed here.'
target.write_text(json.dumps(prior,indent=2)+'\n')
