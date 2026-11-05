#!/usr/bin/env python3
"""Restore exact accepted family bytes into this new post-reset preparation."""
if not __debug__:
    raise RuntimeError('Source restoration requires assertions.')
import argparse
from hashlib import sha1,sha256
import json
from pathlib import Path
import subprocess

HERE=Path(__file__).resolve().parent
COMMIT='5b227091489931a8f7c84e4d0849419792508c0a'
PREFIX='research/nine/computer_assisted/four_product_corner_rows_v1/'
def digest(raw):return sha256(raw).hexdigest()
def main():
    parser=argparse.ArgumentParser();parser.add_argument('--repo',type=Path,required=True);args=parser.parse_args()
    rows=subprocess.check_output(['git','-C',str(args.repo.resolve()),'ls-tree','-r','-z',COMMIT,'--',PREFIX]).split(b'\0')
    inventory={}
    for row in rows:
        if not row:continue
        meta,path=row.split(b'\t');mode,kind,oid=meta.decode().split();name=path.decode()
        assert mode=='100644' and kind=='blob' and name.startswith(PREFIX)
        relative=name[len(PREFIX):];assert relative and '..' not in Path(relative).parts
        raw=subprocess.check_output(['git','-C',str(args.repo.resolve()),'cat-file','blob',oid])
        assert sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==oid
        target=HERE/'accepted'/relative;target.parent.mkdir(parents=True,exist_ok=True)
        if target.exists():assert target.read_bytes()==raw
        else:
            with target.open('xb') as stream:stream.write(raw)
        inventory['accepted/'+relative]=dict(bytes=len(raw),sha256=digest(raw),git_blob_sha1=oid,git_path=name)
    assert len(inventory)==15
    assert inventory['accepted/physical_unit_four_corner_rows.py']['sha256']=='87b1807d71442d558fd6eeaaed9b065d953cc6ca58908079e72b745cb2e227ac'
    assert inventory['accepted/independent_physical_unit_four_corner_rows.py']['sha256']=='bfb6dc614269eaaa2c9f087cc7295c2598648d9349d76006b1e4aa08e66380a6'
    value=dict(schema='new_strict011_four_product_accepted_family_copy_v2',commit=COMMIT,
        exact_accepted_bytes=True,old_missing_new_layer_receipt_reused=False,files=inventory)
    target=HERE/'ACCEPTED_FAMILY.json'
    raw=(json.dumps(value,indent=2,sort_keys=True)+'\n').encode()
    if target.exists():assert target.read_bytes()==raw
    else:
        with target.open('xb') as stream:stream.write(raw)
    print(json.dumps(dict(status='PASS_EXACT_ACCEPTED_FAMILY_COPY',members=len(inventory),manifest_sha256=digest(raw))))
if __name__=='__main__':main()
