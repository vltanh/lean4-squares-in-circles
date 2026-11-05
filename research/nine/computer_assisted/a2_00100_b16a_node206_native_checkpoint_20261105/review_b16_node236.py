"""Non-author conditional node236 attachment, cover, arithmetic and byte review."""
from pathlib import Path
from copy import deepcopy
from fractions import Fraction as F
import json,sys,time
import review_b16_checkpoints as R

HERE=Path(__file__).resolve().parent
GEOM=HERE.parent/'b16_geometry'
PACKET=HERE.parent/'b16_continue/node236_native_package'

def child(raw,split,choice):
    s=deepcopy(raw);kind=split['kind']
    if kind=='angle':
        i=split['owner'];q=F(split['cut']);lo,hi=map(F,s['angles'][i])
        assert type(i)is int and 0<=i<9 and choice in (0,1) and lo<q<hi
        s['angles'][i]=[str(lo),str(q)] if choice==0 else [str(q),str(hi)]
        s['path'].append(['angle_cut',[i,str(q)],choice])
    else:
        pair=split['pair'];assert len(pair)==2 and all(type(i)is int for i in pair)
        assert 0<=pair[0]<pair[1]<9
        if kind=='sat':
            assert len(choice)==3 and choice[0] in pair and choice[1] in (0,1) and choice[2] in (-1,1)
        else:
            assert kind=='proxy' and len(choice)==2 and choice[0] in (0,1) and choice[1] in (-1,1)
        s['path'].append([kind,pair,choice])
    return s

def main():
    started=time.monotonic()
    transport=R.check_transport(PACKET)
    identities={str(p):R.sha(p) for p in PACKET.iterdir() if p.is_file()}
    m=R.read(GEOM/'complete_node236_tree/manifest.json')
    prefix=R.read(GEOM/'node236_ancestry_prefix.json')
    report=R.read(PACKET/'EXACT_REPLAY.json')
    assert R.sha(GEOM/'complete_node236_tree/manifest.json')=='28ff378d53a57bf25fea1b43faf2a2fd07307b33927cb45cd2fdcbe53861233a'
    assert R.sha(PACKET/'EXACT_REPLAY.json')=='a3fec7f6661e4c5f536986528eaac4652fba0dc6991de918ada4365f023ad4e5'
    assert m==R.read(PACKET/'TREE_MANIFEST.json') and prefix==R.read(PACKET/'ANCESTRY_PREFIX.json')
    assert m['parent']['sha256']==R.sha(GEOM/'node236_ancestry_prefix.json')
    assert m['completed'] and m['original_cells_closed']==m['masks_closed']==0
    assert report['complete'] and not report['whole_original_proved'] and not report['entire_registered_original_domain_retained']
    assert prefix['conditional_branch_only'] and prefix['original_cells_closed']==prefix['masks_closed']==0
    frozen=R.read(prefix['source_manifest_path'])
    assert R.sha(prefix['source_manifest_path'])==prefix['source_manifest_sha256']
    original=R.read(PACKET/'SOURCE_NODE236.json')
    assert R.sha(PACKET/'SOURCE_NODE236.json')==frozen['nodes'][236]['sha256']
    assert (original['index'],original['parent'])==(236,206)
    assert original['record']==prefix['steps'][-1]['record']
    assert original['record']['final']==prefix['final']
    oldfolder=R.WORK/'b16_hi_cover_v2_20261105'
    oldm=R.read(oldfolder/'manifest.json')
    assert R.sha(oldfolder/'manifest.json')=='0a6cba31b7b94b40267fe0a2fa0b295acaa3b345602ddcd79eee17700f5f13b7'
    assert R.sha(HERE/'B16_CHECKPOINTS_NONAUTHOR_REVIEW.json')=='0cf2119730030a434e6b10ba720ff1da48eb21bb1024b04a63b03f191827e79a'
    for e in oldm['nodes']:assert R.sha(oldfolder/e['file'])==e['sha256']
    assert prefix['parent']==oldm['parent']==frozen['parent']
    old=[R.read(oldfolder/e['file']) for e in oldm['nodes']]
    assert prefix['steps'][0]['record']['initial']==old[0]['initial']
    assert len(prefix['steps'])==18
    previous=None;reused=[];changed=[]
    for k,step in enumerate(prefix['steps']):
        i=step['original_tree_index'];record=step['record']
        assert record['status']=='OPEN'
        if k==0:assert step['restriction'] is None
        else:
            sel=step['restriction']
            assert child(previous,sel['split'],sel['choice'])==record['initial']
        if i<203:
            assert record['initial']==old[i]['initial']
            assert record['rounds'][:len(old[i]['record']['rounds'])]==old[i]['record']['rounds']
        if i<203 and record==old[i]['record']:reused.append(i)
        else:changed.append((i,record))
        previous=record['final']
    assert reused==[0,4,7,9,11,14,15,16,17,18,65,67,69,71,73]
    assert [i for i,_ in changed]==[188,206,236]
    assert previous==prefix['final']
    nodes=[]
    for e in m['nodes']:
        f=GEOM/'complete_node236_tree'/e['file'];assert R.sha(f)==e['sha256']
        n=R.read(f);assert n['index']==len(nodes)==e['index']
        assert n['record']['initial']==n['initial']
        assert (n['status'],n['depth'])==(e['status'],e['depth'])
        nodes.append(n)
    assert nodes[0]['initial']==prefix['final']
    seen=set();unions=[];leaves=[]
    def visit(i,parent=None,depth=0,choice=None):
        assert i not in seen;seen.add(i);n=nodes[i]
        assert (n['parent'],n['depth'],n['choice'])==(parent,depth,choice)
        if not n['children']:
            assert n['status']=='CANDIDATE_CLOSED';leaves.append(i);return
        assert n['complete_closed_children'] and n['status']=='CANDIDATE_COVER_CLOSED'
        assert n['split']['kind']=='angle' and len(n['children'])==len(set(n['children']))==2
        unions.append(dict(node=i,owner=n['split']['owner'],cut=n['split']['cut']))
        for side,j in enumerate(n['children']):
            assert child(n['record']['final'],n['split'],side)==nodes[j]['initial']
            visit(j,i,depth+1,side)
    visit(0)
    assert seen==set(range(11)) and len(unions)==5 and len(leaves)==6
    cap=R.WORK/'recovery_20261105/extracted_b340/unpacked/b340_complete_original_package/accepted_repo/research/nine/computer_assisted/full_angle_common_side_row_v1'
    adapter=R.EXACT.Adapter(R.WORK/'b16a_I32_complete_H_checkpoint',cap)
    audits=[]
    for group,records in [('new_ancestry',changed),('complete_component',[(n['index'],n['record']) for n in nodes])]:
        for i,record in records:
            t=record.get('terminal');reserve=R.literal_sum(t) if t else None
            audit,after=R.EXACT.CORE.check_record(record,R.parse_state(record['initial'],adapter),adapter)
            assert (after is None)==(record['status']=='CANDIDATE_CLOSED')
            audits.append(dict(group=group,node=i,literal_reserve=reserve,audit=audit))
    adapter.recheck()
    for path,digest in report['source_sha256'].items():
        assert R.sha(path)==digest;identities[path]=digest
    for x in R.read(PACKET/'INPUTS.json')['files']:identities[x['path']]=x['sha256']
    assert not any(name in sys.modules for name in ('numpy','scipy','highspy'))
    for path,digest in identities.items():assert R.sha(path)==digest
    result=dict(status='PASS_COMPLETE_CONDITIONAL_COMPONENT_NONAUTHOR_REVIEW',
        original_id=report['initial_original_id'],conditional_node=236,transport=transport,
        nodes=11,complete_angle_unions=unions,excluded_leaves=leaves,open_leaves=0,
        ancestry_steps=18,reused_unchanged_certified_records=reused,new_ancestry_records=[188,206,236],
        all_new_literal_reserves_recomputed=True,record_audits=audits,
        component_printed_rows=sum(x['audit']['printed_rows_checked'] for x in audits if x['group']=='complete_component'),
        new_ancestry_printed_rows=sum(x['audit']['printed_rows_checked'] for x in audits if x['group']=='new_ancestry'),
        frozen_source_sibling242_status=frozen['nodes'][242]['status'],
        whole_node206_closed=False,whole_original_proved=False,original_cells_closed=0,masks_closed=0,
        source_identities=identities,adapter_source_pins_rechecked=len(adapter.files),
        accepted_merged_parent_and_15_old_record_replays_reused=True,
        standalone_cold_replay_claimed=False,whole_proof_audit_claimed=False,
        reviewer_source_sha256=R.sha(__file__),helper_source_sha256=R.sha(R.__file__),seconds=time.monotonic()-started)
    (HERE/'B16_NODE236_NONAUTHOR_REVIEW.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','nodes','excluded_leaves','open_leaves','component_printed_rows','new_ancestry_printed_rows','seconds']}))

if __name__=='__main__':
    assert __debug__
    main()
