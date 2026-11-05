"""Non-author exact review of the immutable B462 57-node partial cover."""
from pathlib import Path
from collections import Counter
import hashlib,json,sys,tarfile,time
import review_b16_checkpoints as R

HERE=Path(__file__).resolve().parent
TARGET=HERE.parent/'b462_continue'
PACKET=TARGET/'early57_native_packet'

def main():
    start=time.monotonic()
    manifest=R.read(PACKET/'MANIFEST.json')
    identities={str(p):R.sha(p) for p in PACKET.iterdir() if p.is_file()}
    for name,digest in manifest['files'].items():
        assert Path(name).name==name and R.sha(PACKET/name)==digest
    inputs=R.read(PACKET/'INPUTS.json')['files']
    blobs={x['sha256']:x['bytes'] for x in inputs}
    assert len(inputs)==manifest['input_paths']==317
    assert len(blobs)==manifest['unique_blobs']==308
    seen=set()
    with tarfile.open(PACKET/'inputs.tar.xz','r|xz') as a:
        for m in a:
            assert m.isfile() and m.name.startswith('sources/')
            h=m.name.removeprefix('sources/')
            assert h in blobs and h not in seen
            raw=a.extractfile(m).read()
            assert len(raw)==m.size==blobs[h]
            assert hashlib.sha256(raw).hexdigest()==h
            seen.add(h)
    assert seen==set(blobs)
    for x in inputs:
        p=Path(x['path']); assert p.stat().st_size==x['bytes'] and R.sha(p)==x['sha256']
        identities[str(p)]=x['sha256']
    m,nodes,structure=R.tree(TARGET/'snapshot_early')
    base=R.read(TARGET/'BASE_REPLAY.json')
    early=R.read(TARGET/'EARLY_REPLAY.json')
    assert early==R.read(PACKET/'FRESH_EXACT_REPLAY.json')
    assert base==R.read(PACKET/'BASE_REPLAY.json')
    assert early['certificate_sha256']==R.sha(TARGET/'snapshot_early/manifest.json')
    base_folder=Path(m['continuation']['source'])
    basem=R.read(base_folder/'manifest.json')
    assert R.sha(base_folder/'manifest.json')==base['certificate_sha256']
    basen=R.read(base_folder/basem['nodes'][0]['file'])
    assert m['parent']==basem['parent']
    assert nodes[0]['initial']==basen['initial']
    assert nodes[0]['record']['rounds'][:2]==basen['record']['rounds']
    assert len(basen['record']['rounds'])==2
    assert nodes[0]['children']==[1,2,3,4]
    assert nodes[1]['choice']==[0,-1] and nodes[1]['status']=='CANDIDATE_CLOSED'
    assert all(nodes[i]['status']=='OPEN' for i in [2,3,4])
    assert structure==dict(nodes=57,unions={'proxy':12,'angle':4},excluded=31,open=10)
    cap=R.WORK/'recovery_20261105/extracted_b340/unpacked/b340_complete_original_package/accepted_repo/research/nine/computer_assisted/full_angle_common_side_row_v1'
    adapter=R.EXACT.Adapter(R.WORK/'b16a_I32_complete_H_checkpoint',cap)
    parent=adapter.retain(m['parent']['path'],m['parent']['sha256'])
    parent_audit,parent_state=adapter.replay(parent)
    assert parent_audit['status']=='PASS_REGISTERED_WHOLE_ORIGINAL_INITIAL_STATE'
    assert R.EXACT.CORE.state_view(parent_state)==nodes[0]['initial']
    assert R.EXACT.BASE.BASE.WHOLE.verify(parent,adapter) is True
    audits=[]; kinds=Counter()
    for n in nodes:
        t=n['record'].get('terminal')
        if t:kinds[t['kind']]+=1
        reserve=R.literal_sum(t) if t and t['kind']=='positive_exact_reserve' else None
        audit,after=R.EXACT.CORE.check_record(n['record'],R.parse_state(n['initial'],adapter),adapter)
        assert (after is None)==(n['record']['status']=='CANDIDATE_CLOSED')
        audits.append(dict(node=n['index'],literal_reserve=reserve,audit=audit))
    adapter.recheck()
    for path,digest in early['source_sha256'].items():
        assert R.sha(path)==digest
        identities[path]=digest
    assert not any(name in sys.modules for name in ('numpy','scipy','highspy'))
    for path,digest in identities.items():assert R.sha(path)==digest
    result=dict(status='PASS_SCOPED_NONAUTHOR_REVIEW',original_id=parent_audit['id'],
        structure=structure,entire_original_parent_retained=True,whole_original_proved=False,
        original_cells_closed=0,masks_closed=0,completed_root_branches=[1],
        original_two_round_prefix_retained=True,parent_audit=parent_audit,
        terminal_kinds=dict(kinds),fresh_record_audits=audits,
        printed_rows_checked=sum(a['audit']['printed_rows_checked'] for a in audits),
        adapter_source_pins_rechecked=len(adapter.files),indexed_source_paths=len(inputs),
        unique_archive_blobs=len(blobs),source_identities=identities,
        review_source_sha256=R.sha(__file__),helper_source_sha256=R.sha(R.__file__),
        whole_proof_audit_claimed=False,standalone_cold_replay_claimed=False,
        seconds=time.monotonic()-start)
    (HERE/'B462_EARLY57_NONAUTHOR_REVIEW.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','structure','terminal_kinds','printed_rows_checked','seconds']}))

if __name__=='__main__':
    assert __debug__
    main()
