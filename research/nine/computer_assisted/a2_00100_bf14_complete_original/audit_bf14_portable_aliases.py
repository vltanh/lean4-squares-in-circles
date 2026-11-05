"""Independently check that portable v2 changes only explicit path aliases."""
from pathlib import Path
from hashlib import sha256
import argparse,json

def digest(path):
    h=sha256()
    with Path(path).open('rb')as stream:
        for block in iter(lambda:stream.read(1048576),b''):h.update(block)
    return h.hexdigest()

def main():
    ap=argparse.ArgumentParser()
    for name in('packet','prior','output'):ap.add_argument(name,type=Path)
    a=ap.parse_args();packet=a.packet.resolve();prior=a.prior.resolve()
    proof=json.loads((packet/'TRANSPORT_ALIAS_REPAIR.json').read_text())
    old_manifest=json.loads((packet/'PRE_ALIAS_INPUT_MANIFEST.json').read_text())
    old=json.loads((packet/'PRE_ALIAS_BINDINGS.json').read_text())
    new=json.loads((packet/'BINDINGS.json').read_text())
    assert digest(packet/'PRE_ALIAS_INPUT_MANIFEST.json')==proof['source_input_manifest_sha256']
    assert digest(packet/'PRE_ALIAS_BINDINGS.json')==proof['original_bindings_sha256']
    assert digest(packet/'BINDINGS.json')==proof['repaired_bindings_sha256']
    for name,h in old_manifest['files'].items():
        if name!='BINDINGS.json':assert digest(packet/name)==h,name
    for name,entry in old.items():assert new[name]==entry,name
    added=set(new)-set(old)
    assert added==set(proof['added_aliases'])and len(added)==proof['added_alias_count']==754
    for name in sorted(added):
        item=proof['added_aliases'][name]
        assert new[name]==item['binding']==old[item['canonical']]
        entry=new[name];assert entry['root']in('packet','prior')
        root=packet if entry['root']=='packet'else prior
        target=(root/entry['path']).resolve()
        assert target.is_relative_to(root)and digest(target)==entry['sha256']
    report=dict(status='PASS_LITERAL_PORTABLE_ALIAS_EXTENSION_ONLY',
        old_bindings=len(old),new_bindings=len(new),added_aliases=len(added),
        every_old_binding_unchanged=True,every_new_alias_matches_old_binding=True,
        all_original_inputs_except_bindings_byte_identical=True,
        all_literal_proof_and_checker_bytes_unchanged=True,
        reads_of_historical_workspace_needed=False,
        source_sha256={str(Path(__file__).resolve()):digest(__file__),
            str(packet/'TRANSPORT_ALIAS_REPAIR.json'):digest(packet/'TRANSPORT_ALIAS_REPAIR.json'),
            str(packet/'PRE_ALIAS_INPUT_MANIFEST.json'):digest(packet/'PRE_ALIAS_INPUT_MANIFEST.json'),
            str(packet/'PRE_ALIAS_BINDINGS.json'):digest(packet/'PRE_ALIAS_BINDINGS.json'),
            str(packet/'BINDINGS.json'):digest(packet/'BINDINGS.json')},
        arithmetic_repeated=False,whole_original_credit=0,new_masks=0)
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items()if k!='source_sha256'},indent=2))

if __name__=='__main__':main()
