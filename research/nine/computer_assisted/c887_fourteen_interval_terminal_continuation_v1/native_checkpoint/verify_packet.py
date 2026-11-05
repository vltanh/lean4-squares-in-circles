#!/usr/bin/env python3
"""Byte/assembly verification only; this does not replay proof arithmetic."""
from pathlib import Path
import argparse,hashlib,json

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def local(root,name):
    rel=Path(name);assert not rel.is_absolute()and rel.parts and all(x not in ('..','.')for x in rel.parts)
    p=root/rel;assert p.resolve().is_relative_to(root)and p.is_file()and not p.is_symlink()
    return p

def check(package,base):
    if not __debug__:raise RuntimeError('Assertions required')
    package=Path(package).resolve();base=Path(base).resolve()
    m=read(package/'INPUT_MANIFEST.json');assert m['schema']=='C887_complete91_seventeen_terminal_delta_v1'
    assert not any(p.is_symlink()for p in package.rglob('*'))
    assert {str(p.relative_to(package))for p in package.rglob('*')if p.is_file()}==set(m['files'])|{'INPUT_MANIFEST.json'}
    pins={str(package/'INPUT_MANIFEST.json'):sha(package/'INPUT_MANIFEST.json')}
    for name,item in m['files'].items():
        p=local(package,name);assert p.stat().st_size==item['bytes']and sha(p)==item['sha256'];pins[str(p)]=item['sha256']
    assembly=read(package/'TREE_ASSEMBLY.json')
    assert sha(base/'INPUT_MANIFEST.json')==assembly['published_base_input_manifest_sha256']=='06115f494173bc344821932525d7a8522df8ea2ed80b400f735f3b68d4a1b58b'
    assert sha(base/'BINDINGS.json')==assembly['published_base_binding_sha256']=='e7706717cc9136d2327b2a76a65f5824dad385743757f860863a50d5373b6c10'
    base_files=read(base/'INPUT_MANIFEST.json')['files']
    original=read(package/'metadata/SOURCE_MANIFEST.json');prior=read(package/'predecessor/manifest.json');final=read(package/'tree/manifest.json')
    assert sha(package/'metadata/SOURCE_MANIFEST.json')=='a091ad6716ef688cf001857a70f5058acfbb9601a87818de1edb4db4fa9bbe49'
    assert sha(package/'predecessor/manifest.json')==assembly['predecessor_manifest_sha256']=='276bae5827e64c8e9cabd1c5907d5047b26cde6cabc68fee9440a44f067f7e09'
    assert sha(package/'tree/manifest.json')==assembly['continued_manifest_sha256']=='295a4b73434471634c2eb636ac4ffa676cc8a4c26c1ba20e1a3b1f404e40c3e6'
    assert len(original['nodes'])==len(prior['nodes'])==len(final['nodes'])==len(assembly['nodes'])==91
    new14={1,3,5,11,12,17,19,22,71,73,75,84,85,87};old3={29,30,64};included=0
    for i,(a,b,c,item)in enumerate(zip(original['nodes'],prior['nodes'],final['nodes'],assembly['nodes'])):
        assert a['index']==b['index']==c['index']==item['index']==i
        assert a['file']==b['file']==c['file']==item['file']==f'node_{i:05d}.json'
        p=local(base,item['published_member']);assert base_files[item['published_member']]==a['sha256']==item['published_sha256']==sha(p)
        pins[str(p)]=a['sha256']
        assert item['predecessor_sha256']==b['sha256']and item['continued_sha256']==c['sha256']
        if i in old3|new14:
            q=local(package,item['included_member']);assert sha(q)==c['sha256'];included+=1
            if i in old3:assert b['sha256']==c['sha256']
            else:assert b['sha256']==a['sha256']
        else:
            assert 'included_member'not in item and a['sha256']==b['sha256']==c['sha256']
    assert included==17
    r=read(package/'reports/FOURTEEN_TERMINAL_EXACT_REPLAY.json')
    assert sha(package/'reports/FOURTEEN_TERMINAL_EXACT_REPLAY.json')=='8ea1ae86b99d401b805951a15ba3f229f9cce4db7a81e126f70c13d1e6002ac7'
    assert r['new_manifest_sha256']==assembly['continued_manifest_sha256']
    assert (r['all_nodes'],r['leaf_domains'],r['excluded_leaf_domains'],r['open_leaf_domains'])==(91,73,17,56)
    assert r['fresh_terminal_leaf_indices']==sorted(new14)and r['retained_prior_excluded_leaf_indices']==sorted(old3)
    assert r['new_hull_or_endpoint_family_used']is False
    assert r['historical_weighted_arithmetic_reused_not_repeated']is True
    assert sha(package/'reports/THREE_TERMINAL_EXACT_REPLAY.json')=='ab1f2aac0ad99539365df036ce3c884b6af2f7ebecc5c890fdd8b35df5f3a51a'
    for p,h in pins.items():assert sha(p)==h
    return assembly,pins

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--package',type=Path,required=True);p.add_argument('--published-base',type=Path,required=True)
    a=p.parse_args();table,pins=check(a.package,a.published_base)
    print(json.dumps(dict(status='PASS_C88717_DELTA_BYTES_AND_BASE_ALIASES',nodes=91,included_nodes=17,reused_base_final_nodes=74,
        all_original_base_nodes_checked=91,arithmetic_replayed=False,new_original_cells=0,new_masks=0)),flush=True)
