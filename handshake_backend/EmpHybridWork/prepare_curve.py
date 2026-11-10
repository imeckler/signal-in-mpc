"""Pin and serialize the existing pinned exported field DAG, no new curve math."""
import hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;OUT=ROOT/'.deps/emp-hybrid-curve-v1';OUT.mkdir(exist_ok=True)
source=ROOT/'.deps/relay-service-artifacts/x25519-field.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if sha(source)!='a5a2d584d694adb5c0fae84192f393fbb7d207353f1a5e2e7584e9860168ee59':raise ValueError('field DAG pin')
p=json.loads(source.read_text());assert p['input_count']==257 and p['modulus']==str(2**255-19) and p['outputs']==[9436] and len(p['nodes'])==9437
rows=['EMP_HYBRID_FIELD_DAG_V1',f"257 {len(p['nodes'])} 9436",str(2**255-19)];depth=[];counts={}
for i,n in enumerate(p['nodes']):
    op=n['op'];counts[op]=counts.get(op,0)+1
    if op=='const':assert n['value'] in ['0','1','2','121665'];rows.append('C '+n['value']);depth.append(0)
    elif op=='input':assert 0<=n['index']<257;rows.append('I '+str(n['index']));depth.append(0)
    elif op in ['add','sub','mul']:
        a,b=n['left'],n['right'];assert 0<=a<i and 0<=b<i;rows.append({'add':'A','sub':'S','mul':'M'}[op]+f' {a} {b}');depth.append(max(depth[a],depth[b])+(op=='mul'))
    else:raise ValueError('field op')
flat=OUT/'x25519.flat';flat.write_text('\n'.join(rows)+'\n')
(OUT/'field_curve_pin.h').write_text('#pragma once\nnamespace emp_hybrid { inline constexpr const char* FIELD_FLAT_SHA="'+sha(flat)+'"; }\n')
report=dict(passed=True,source_sha256=sha(source),flat_sha256=sha(flat),flat_bytes=flat.stat().st_size,nodes=len(depth),counts=counts,multiplicative_depth=max(depth),scope='Same pinned FieldDag reserialization, not a new X25519 implementation/proof.')
(HERE/'curve-program-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
