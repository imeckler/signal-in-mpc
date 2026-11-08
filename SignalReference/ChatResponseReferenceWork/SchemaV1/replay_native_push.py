#!/usr/bin/env python3
"""Original pinned native push vs exact-body literal replay, private fields kept."""
from pathlib import Path
import json,hashlib,re,shutil
H=Path(__file__).resolve().parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();vendor=ROOT/'.deps/libsignal-vendor/prost-0.14.4';native=H/'Native';copy=native/'ProstReplay';checks=json.loads((vendor/'.cargo-checksum.json').read_text())['files']
for name,digest in checks.items():assert sha(vendor/name)==digest,name
if copy.exists():shutil.rmtree(copy)
shutil.copytree(vendor,copy)
# Only native-test target metadata is omitted; runtime dependencies/features unchanged.
cargo=(copy/'Cargo.toml').read_text();cargo=re.sub(r'(?ms)^\[\[bench\]\].*?(?=^\[|\Z)','',cargo);cargo=re.sub(r'(?ms)^\[dev-dependencies\.[^\]]+\].*?(?=^\[|\Z)','',cargo);(copy/'Cargo.toml').write_text(cargo)
source=(vendor/'src/error.rs').read_text();start=source.index("    pub fn push(&mut self, message: &'static str, field: &'static str) {");end=source.index('\n    }',start)+6;method=source[start:end];body=method[method.index('{')+1:method.rindex('}')];assert body.strip()=='self.inner.stack.push((message, field));'
receipt=json.loads((H/'Artifacts/specialized.push.json').read_text());pairs=list(dict.fromkeys(tuple(c['literals']) for c in receipt['changes']));methods=''
for i,(message,field) in enumerate(pairs):
 literal=lambda text:json.dumps(text,ensure_ascii=False)
 content=re.sub(r'\bmessage\b',lambda _:literal(message),body);content=re.sub(r'\bfield\b',lambda _:literal(field),content)
 methods+=f'\n    #[doc(hidden)]\n    pub fn reference_push_literal_{i}(&mut self) {{{content}}}\n'
(copy/'src/error.rs').write_text(source[:end]+methods+source[end:])
(native/'src').mkdir(parents=True,exist_ok=True);(native/'.cargo').mkdir(exist_ok=True)
(native/'.cargo/config.toml').write_text((H/'Rust/.cargo/config.toml').read_text())
(native/'Cargo.toml').write_text('[package]\nname="native-push-literal-check"\nversion="0.1.0"\nedition="2024"\n[dependencies]\nprost={path="ProstReplay"}\n[workspace]\n')
s='''fn main() {
    let frames: &[(&'static str,&'static str)] = &[
'''+''.join('        ('+json.dumps(m)+','+json.dumps(f)+'),\n' for m,f in pairs)+'''];
    let helpers: &[fn(&mut prost::DecodeError)] = &[
'''+''.join(f'        prost::DecodeError::reference_push_literal_{i},\n' for i in range(len(pairs)))+'''];
    let mut checked=0;
    for seed in 0..128 {
        let mut original=prost::DecodeError::new(format!("seed{seed}"));
        for _ in 0..seed%5 { original.push("Existing", "prefix"); }
        for (i,(message,field)) in frames.iter().enumerate() {
            let mut expected=original.clone();let mut actual=original.clone();
            expected.push(message,field);helpers[i](&mut actual);
            assert_eq!(format!("{expected:?}"),format!("{actual:?}"));checked+=1;
        }
    }
    for seed in 0..16 {
        for (i,(m1,f1)) in frames.iter().enumerate() {
            for (j,(m2,f2)) in frames.iter().enumerate() {
                let mut expected=prost::DecodeError::new(format!("seed{seed}"));
                let mut actual=expected.clone();
                expected.push(m1,f1);expected.push(m2,f2);
                helpers[i](&mut actual);helpers[j](&mut actual);
                assert_eq!(format!("{expected:?}"),format!("{actual:?}"));checked+=1;
            }
        }
    }
    println!("Compared {checked} exact native error/stack/order outcomes");
}
'''
(native/'src/main.rs').write_text(s)
(H/'native-push-replay.json').write_text(json.dumps({'scope':'Private scoped copy of pinned prost; original method unchanged; additional literal helpers replay exact actual body. Native diagnostic mutation/order regression only; static-reference Aeneas bridge remains open.','pinned_error_sha256':checks['src/error.rs'],'original_method_sha256':hashlib.sha256(method.encode()).hexdigest(),'specialization_receipt_sha256':sha(H/'Artifacts/specialized.push.json'),'replayed_error_sha256':sha(copy/'src/error.rs'),'script_sha256':sha(Path(__file__)),'pairs':pairs,'compared':128*len(pairs)+16*len(pairs)**2,'generated_main_sha256':sha(native/'src/main.rs')},indent=2)+'\n');print('native literal helpers:',len(pairs))
