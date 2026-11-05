#!/usr/bin/env python3
"""Assemble exact predecessor/final trees into new folders; no source modification."""
from pathlib import Path
import argparse,json,os
import verify_packet as V

def run(package,base,output):
    package,base,output=map(lambda p:Path(p).resolve(),(package,base,output))
    assert not output.exists()and not output.is_relative_to(package)and not output.is_relative_to(base)
    table,pins=V.check(package,base)
    output.mkdir(parents=True,exist_ok=False)
    for kind,key in [('predecessor','predecessor_sha256'),('continued','continued_sha256')]:
        folder=output/kind;folder.mkdir()
        for item in table['nodes']:
            if item[key]==item['published_sha256']:
                source=V.local(base,item['published_member'])
            else:
                source=V.local(package,item['included_member'])
            assert V.sha(source)==item[key]
            p=folder/item['file']
            with p.open('xb')as stream:stream.write(source.read_bytes());stream.flush();os.fsync(stream.fileno())
            assert V.sha(p)==item[key]
        source=package/('predecessor/manifest.json'if kind=='predecessor'else'tree/manifest.json')
        with (folder/'manifest.json').open('xb')as stream:stream.write(source.read_bytes());stream.flush();os.fsync(stream.fileno())
    for p,h in pins.items():assert V.sha(p)==h
    assert V.sha(output/'predecessor/manifest.json')==table['predecessor_manifest_sha256']
    assert V.sha(output/'continued/manifest.json')==table['continued_manifest_sha256']
    receipt=dict(status='PASS_EXACT_C887_PREDECESSOR_AND17TERMINAL_TREE_ASSEMBLY',
        predecessor_nodes=91,continued_nodes=91,unchanged_input_hashes=True,outputs_copied_not_shared=True,
        continued_manifest_sha256=table['continued_manifest_sha256'],arithmetic_replayed=False,
        historical_proof_dependencies_required=True,new_original_cells=0,new_masks=0)
    (output/'ASSEMBLY_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--package',type=Path,required=True);p.add_argument('--published-base',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();run(a.package,a.published_base,a.output)
