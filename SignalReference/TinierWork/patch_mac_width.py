#!/usr/bin/env python3
"""Explicit local Tinier MAC-width candidate; preserve short-field cut semantics."""
import difflib,hashlib,json,shutil
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];BACKEND=ROOT/'.deps/signal-tinier128/MP-SPDZ';SOURCE=ROOT/'.deps/MP-SPDZ/OT/OTMultiplier.hpp';TARGET=BACKEND/'OT/OTMultiplier.hpp'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    original=SOURCE.read_text();assert TARGET.read_text()==original,'Candidate already edited; refuse ambiguous reapplication'
    old='''int128(
                            auth_ot_ext.receiverOutputMatrix[i]
                                    ^ auth_ot_ext.senderOutputMatrices[0][i]).get_lower()'''
    new='''T::mac_type::cut(int128(
                            auth_ot_ext.receiverOutputMatrix[i]
                                    ^ auth_ot_ext.senderOutputMatrices[0][i]))'''
    assert original.count(old)==1;patched=original.replace(old,new)
    for role in ['receiverOutputMatrix','senderOutputMatrices[0]']:
        old=f'int128(auth_ot_ext.{role}[j]).get_lower()';new=f'U::mac_type::cut(int128(auth_ot_ext.{role}[j]))'
        assert patched.count(old)==1;patched=patched.replace(old,new)
    backup=HERE/'before-width-fix';backup.mkdir(exist_ok=True)
    for name in ['build-report.json','preparation.json','dependency-build.json']:
        shutil.copy2(HERE/name,backup/name)
    shutil.copy2(ROOT/'scripts/check_lean_signal_tinier128.py',backup/'check_lean_signal_tinier128.py')
    shutil.copy2(BACKEND/'tinier-party.x',BACKEND/'tinier-party-before-width-fix.x')
    shutil.copy2(Path('/tmp/signal-tinier-build.log'),backup/'build.log')
    TARGET.write_text(patched)
    diff=HERE/'tinier-mac-width.diff';diff.write_text(''.join(difflib.unified_diff(original.splitlines(True),patched.splitlines(True),fromfile='pinned/OT/OTMultiplier.hpp',tofile='candidate/OT/OTMultiplier.hpp')))
    report={'candidate_only':True,'original_sha256':digest(SOURCE),'patched_sha256':digest(TARGET),'diff_sha256':digest(diff),'patched_sites':3,'purpose':'Use existing field-specific cut on the full128-bit OT block. gf2n_long::cut preserves128bits; gf2n_short::cut retains previous low64bit behavior. No OT checks, MAC checks, sacrifice, or security parameter changes.','original_failure':'all five parties aborted on first INPUTBVEC with MacCheck Failure; no Signal throughput measured','script_sha256':digest(Path(__file__))}
    (HERE/'mac-width-patch.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
