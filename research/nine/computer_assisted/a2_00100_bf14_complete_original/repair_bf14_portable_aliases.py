"""Repair verified path aliases in a new packet; proof/checker bytes unchanged."""
from pathlib import Path
from hashlib import sha256
import argparse,json,shutil

def digest(path):
    h=sha256()
    with Path(path).open('rb')as stream:
        for block in iter(lambda:stream.read(1048576),b''):h.update(block)
    return h.hexdigest()

def main():
    ap=argparse.ArgumentParser()
    for name in('source','output','prior','historical_prefix','failure_log'):ap.add_argument(name,type=Path)
    a=ap.parse_args();source=a.source.resolve();out=a.output.resolve();prior=a.prior.resolve()
    assert not out.exists()
    before=json.loads((source/'INPUT_MANIFEST.json').read_text())
    for name,h in before['files'].items():assert digest(source/name)==h,name
    raw=(source/'BINDINGS.json').read_bytes();bindings=json.loads(raw)
    historical=a.historical_prefix.absolute();canonical=historical.resolve()
    assert historical!=canonical and historical.is_dir()
    additions={}
    for name,entry in list(bindings.items()):
        path=Path(name)
        if not path.is_relative_to(canonical):continue
        alias=str(historical/path.relative_to(canonical))
        assert Path(alias).resolve()==path and digest(alias)==entry['sha256']
        assert entry['root']in('packet','prior')
        base=source if entry['root']=='packet'else prior
        target=(base/entry['path']).resolve()
        assert target.is_relative_to(base)and digest(target)==entry['sha256']
        if alias in bindings:assert bindings[alias]==entry
        else:bindings[alias]=entry;additions[alias]=dict(canonical=name,binding=entry)
    assert additions
    parent=str(historical/'whole_B_roots/negative-f14f5bc4eafdf50d.json')
    assert bindings[parent]['sha256']=='63bf1a0fd1511857846e821eff14d452d68c5236205ccbb20a745005f3ffe00d'
    shutil.copytree(source,out)
    (out/'PRE_ALIAS_INPUT_MANIFEST.json').write_bytes((source/'INPUT_MANIFEST.json').read_bytes())
    (out/'PRE_ALIAS_BINDINGS.json').write_bytes(raw)
    (out/'BINDINGS.json').write_text(json.dumps(bindings,indent=2)+'\n')
    for name,h in before['files'].items():
        if name!='BINDINGS.json':assert digest(out/name)==h,name
    shutil.copyfile(__file__,out/'acceptance_tools/repair_bf14_portable_aliases.py')
    shutil.copyfile(a.failure_log,out/'original_audits/PORTABLE_V1_TRANSPORT_FAILURE.log')
    proof=dict(schema='bf14_verified_historical_prefix_alias_repair_v1',
        source_input_manifest_sha256=digest(source/'INPUT_MANIFEST.json'),
        original_bindings_sha256=sha256(raw).hexdigest(),
        repaired_bindings_sha256=digest(out/'BINDINGS.json'),
        historical_prefix=str(historical),canonical_prefix=str(canonical),
        added_aliases=additions,added_alias_count=len(additions),
        every_alias_matches_already_frozen_input=True,
        all_literal_proof_and_checker_bytes_unchanged=True,
        all_original_inputs_except_bindings_unchanged=True,
        original_package_preserved=True,
        initial_portable_failure_was_before_tree_arithmetic=True,
        fresh_portable_replay_required=True,original_credit=0,mask_credit=0)
    (out/'TRANSPORT_ALIAS_REPAIR.json').write_text(json.dumps(proof,indent=2)+'\n')
    manifest=dict(before)
    manifest['files']={str(p.relative_to(out)):digest(p)for p in sorted(out.rglob('*'))
        if p.is_file()and p!=out/'INPUT_MANIFEST.json'}
    (out/'INPUT_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(dict(status='VERIFIED_ALIAS_REPAIR_FRESH_REPLAY_REQUIRED',
        added_aliases=len(additions),final_inputs=len(manifest['files']),
        input_manifest_sha256=digest(out/'INPUT_MANIFEST.json')),indent=2))

if __name__=='__main__':main()
