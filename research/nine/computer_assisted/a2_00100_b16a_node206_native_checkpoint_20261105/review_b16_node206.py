"""Independent incremental review of the complete conditional B16 node206."""
from pathlib import Path
from itertools import product
import json,sys,time
import review_b16_checkpoints as R
from review_b16_node236 import child
HERE=Path(__file__).resolve().parent
RUN=HERE.parent/'b16_continue'
PACKET=RUN/'node206_native_package'

def main():
    start=time.monotonic();transport=R.check_transport(PACKET)
    olddir=HERE.parent/'b16_geometry/complete_node236_tree'
    assert R.sha(olddir/'manifest.json')=='28ff378d53a57bf25fea1b43faf2a2fd07307b33927cb45cd2fdcbe53861233a'
    assert R.sha(HERE/'B16_NODE236_NONAUTHOR_REVIEW.json')=='1bbd9598e953e501c31dac2d0c5be8e4591c30b6c6bf245651425b59587f7478'
    old=[]
    for e in R.read(olddir/'manifest.json')['nodes']:
        assert R.sha(olddir/e['file'])==e['sha256'];old.append(R.read(olddir/e['file']))
    oldpre=R.read(HERE.parent/'b16_geometry/node236_ancestry_prefix.json')
    pre=R.read(PACKET/'ANCESTRY_PREFIX.json')
    assert pre['parent']==oldpre['parent'] and pre['steps']==oldpre['steps'][:-1]
    assert pre['final']==pre['steps'][-1]['record']['final']
    assert len(pre['steps'])==17 and pre['steps'][-1]['original_tree_index']==206
    assert pre['conditional_branch_only'] and pre['original_cells_closed']==pre['masks_closed']==0
    folder=RUN/'complete_node206_tree';m=R.read(folder/'manifest.json')
    assert m==R.read(PACKET/'TREE_MANIFEST.json')
    assert R.sha(folder/'manifest.json')=='a4d9a4043ab87e8c9fd09957600bb72b8ba1e1a7cdda2fbf374d7b96a2a2636d'
    assert m['parent']['sha256']==R.sha(PACKET/'ANCESTRY_PREFIX.json')
    nodes=[]
    for e in m['nodes']:
        assert R.sha(folder/e['file'])==e['sha256'];n=R.read(folder/e['file'])
        assert n['index']==len(nodes)==e['index'] and n['record']['initial']==n['initial']
        assert (n['depth'],n['status'])==(e['depth'],e['status']);nodes.append(n)
    assert nodes[0]['initial']==pre['final']
    seen=set();unions=[];leaves=[]
    def visit(i,parent=None,depth=0,choice=None):
        assert i not in seen;seen.add(i);n=nodes[i]
        assert(n['parent'],n['depth'],n['choice'])==(parent,depth,choice)
        if not n['children']:
            assert n['status']=='CANDIDATE_CLOSED';leaves.append(i);return
        assert n['complete_closed_children'] and n['status']=='CANDIDATE_COVER_CLOSED'
        split=n['split'];kind=split['kind']
        if kind=='sat':
            assert i==0 and split['pair']==[0,7]
            choices=list(map(list,product([0,7],[0,1],[-1,1])))
        else:assert kind=='angle';choices=[0,1]
        assert len(n['children'])==len(set(n['children']))==len(choices)
        unions.append(kind)
        for j,ch in zip(n['children'],choices):
            assert child(n['record']['final'],split,ch)==nodes[j]['initial']
            visit(j,i,depth+1,ch)
    visit(0)
    assert seen==set(range(33)) and len(leaves)==20 and unions.count('sat')==1 and unions.count('angle')==12
    reused=[(n['index'],o['index']) for n in nodes for o in old if n['record']==o['record']]
    assert len(reused)==11 and {i for _,i in reused}==set(range(11))
    reused_indices={i for i,_ in reused}
    cap=R.WORK/'recovery_20261105/extracted_b340/unpacked/b340_complete_original_package/accepted_repo/research/nine/computer_assisted/full_angle_common_side_row_v1'
    adapter=R.EXACT.Adapter(R.WORK/'b16a_I32_complete_H_checkpoint',cap)
    reserves={};audits=[]
    for n in nodes:
        t=n['record'].get('terminal')
        if t:reserves[n['index']]=R.literal_sum(t)
        if n['index'] in reused_indices:continue
        audit,after=R.EXACT.CORE.check_record(n['record'],R.parse_state(n['initial'],adapter),adapter)
        assert (after is None)==(n['record']['status']=='CANDIDATE_CLOSED')
        audits.append(dict(node=n['index'],audit=audit))
    adapter.recheck();report=R.read(PACKET/'EXACT_REPLAY.json')
    assert report['complete'] and not report['whole_original_proved'] and not report['entire_registered_original_domain_retained']
    identities={str(p):R.sha(p) for p in PACKET.iterdir() if p.is_file()}
    for p,h in report['source_sha256'].items():assert R.sha(p)==h;identities[p]=h
    for e in R.read(PACKET/'INPUTS.json')['files']:identities[e['path']]=e['sha256']
    assert not any(x in sys.modules for x in ('numpy','scipy','highspy'))
    result=dict(status='PASS_COMPLETE_CONDITIONAL_COMPONENT_NONAUTHOR_REVIEW',conditional_node=206,
        nodes=33,complete_sat_unions=1,complete_angle_unions=12,excluded_leaves=20,open_leaves=0,
        reused236_record_mapping=reused,all20_literal_reserves=reserves,new_record_audits=audits,
        new_records_replayed=len(audits),new_printed_rows=sum(a['audit']['printed_rows_checked'] for a in audits),
        ancestry_reused_from_reviewed236=True,whole188_closed=False,whole_original_closed=False,
        original_cells_closed=0,masks_closed=0,transport=transport,source_identities=identities,
        adapter_source_pins_rechecked=len(adapter.files),standalone_cold_replay_claimed=False,
        source_sha256=R.sha(__file__),helper236_sha256=R.sha(HERE/'review_b16_node236.py'),
        seconds=time.monotonic()-start)
    (HERE/'B16_NODE206_NONAUTHOR_REVIEW.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','nodes','excluded_leaves','open_leaves','new_records_replayed','new_printed_rows','seconds']}))

if __name__=='__main__':assert __debug__;main()
