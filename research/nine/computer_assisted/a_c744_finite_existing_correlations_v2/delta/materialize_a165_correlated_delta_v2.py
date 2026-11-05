#!/usr/bin/env python3
"""Byte-only assembly or verification of six exact A165 payload replacements."""
if not __debug__:raise RuntimeError('Assertions required.')
from pathlib import Path
import argparse,hashlib,json,os
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def local(root,name):
    p=Path(name);assert not p.is_absolute()and p.parts and '..'not in p.parts
    q=root/p;assert q.resolve().is_relative_to(root)and q.is_file()and not q.is_symlink();return q
def run(delta,prior,output=None):
    delta,prior=Path(delta).resolve(),Path(prior).resolve()
    inv=read(delta/'INPUT_MANIFEST.json');invhash=sha(delta/'INPUT_MANIFEST.json')
    assert inv['schema']=='A165_existing_correlated_rows_native_delta_v2'
    assert not any(p.is_symlink()for p in delta.rglob('*'))
    assert {str(p.relative_to(delta))for p in delta.rglob('*')if p.is_file()}==set(inv['files'])|{'INPUT_MANIFEST.json'}
    pins={str(delta/'INPUT_MANIFEST.json'):invhash}
    for name,e in inv['files'].items():
        p=local(delta,name);assert p.stat().st_size==e['bytes']and sha(p)==e['sha256'];pins[str(p)]=e['sha256']
    old=read(prior/'manifest.json');m=read(delta/'tree/manifest.json');a=read(delta/'TREE_ASSEMBLY.json')
    assert sha(prior/'manifest.json')==a['source_manifest_sha256']=='4469ce8ceda7692f49faa58ece25872c0448fbd8fc86447acb6facf0cd4e2283'
    assert sha(delta/'tree/manifest.json')==a['continued_manifest_sha256']=='5c06610c0f8e4e317707b4f352277a2530d39e7f3cb63dfc5b03089571ccd98c'
    assert len(old['nodes'])==len(m['nodes'])==len(a['nodes'])==165
    pins[str(prior/'manifest.json')]=a['source_manifest_sha256'];sources=[];changed=[]
    for n,(before,after,entry)in enumerate(zip(old['nodes'],m['nodes'],a['nodes'])):
        assert before['index']==after['index']==entry['index']==n
        assert before['file']==after['file']==entry['file']==f'node_{n:05d}.json'
        source=local(prior,before['file']);assert sha(source)==before['sha256'];pins[str(source)]=before['sha256']
        assert {k:v for k,v in before.items()if k not in('status','sha256')}=={k:v for k,v in after.items()if k not in('status','sha256')}
        if entry['source']=='PREVIOUS_ACCEPTED_A165_TREE':assert after==before and after['sha256']==entry['sha256']
        else:
            assert entry['source']=='THIS_DELTA'and n in(151,152,154,156,157,163)
            previous=read(source);source=local(delta,entry['member']);current=read(source)
            assert current['initial']==previous['initial']and current['rounds'][:len(previous['rounds'])]==previous['rounds']
            assert sha(source)==after['sha256']==entry['sha256'];changed.append(n)
        sources.append((source,after))
    assert changed==[151,152,154,156,157,163]
    report=read(delta/'reports/A165_CORRELATED_EXISTING_CONTINUATION_EXACT_REPLAY_V2.json')
    assert sha(delta/'reports/A165_CORRELATED_EXISTING_CONTINUATION_EXACT_REPLAY_V2.json')=='eee73dfe46135c506568026e92bb32e16cbbd5751bb26b87768504fe3175061d'
    assert report['continued_manifest_sha256']==a['continued_manifest_sha256']
    assert(report['nodes'],report['excluded_leaves'],report['open_leaves'],report['fresh_rounds'],report['fresh_deductions'],report['fresh_printed_rows_checked'])==(165,118,14,12,10,19)
    assert report['old165_consumer_arithmetic_reused_not_repeated']is True
    if output is not None:
        output=Path(output).resolve();assert not output.exists()and not output.is_relative_to(delta)and not output.is_relative_to(prior)
        output.mkdir(parents=True,exist_ok=False)
        for source,node in sources:
            with(output/node['file']).open('xb')as f:f.write(source.read_bytes());f.flush();os.fsync(f.fileno())
            assert sha(output/node['file'])==node['sha256']
        with(output/'manifest.json').open('xb')as f:f.write((delta/'tree/manifest.json').read_bytes());f.flush();os.fsync(f.fileno())
        assert sha(output/'manifest.json')==a['continued_manifest_sha256']
    for path,h in pins.items():assert sha(path)==h
    return dict(status='PASS_A165_CORRELATED_DELTA_BYTE_ASSEMBLY'if output is not None else'PASS_A165_CORRELATED_DELTA_BYTE_AND_PREFIX_VERIFICATION',
        input_manifest_sha256=invhash,files=len(inv['files'])+1,nodes=165,reused_payloads=159,changed_payloads=6,
        excluded_leaves=118,open_leaves=14,source_hashes_unchanged=True,arithmetic_replayed=False,cold_proof_claimed=False,
        new_original_cells=0,new_masks=0)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--delta',required=True,type=Path);p.add_argument('--prior-tree',required=True,type=Path)
    p.add_argument('--output',type=Path);p.add_argument('--report',required=True,type=Path);a=p.parse_args();assert not a.report.exists()
    r=run(a.delta,a.prior_tree,a.output)
    with a.report.open('x')as f:json.dump(r,f,indent=2);f.write('\n')
    print(json.dumps(r),flush=True)
