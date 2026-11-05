"""Fresh original-prefix and conditional closed-difference cover replay.

The prefix identifies a proved conditional state. This entry never awards
original-cell credit; all omitted siblings remain obligations in the full tree.
"""
from pathlib import Path
from hashlib import sha256
from copy import deepcopy
import argparse, json, sys, time

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / 'b_family' / 'source'
sys.path.insert(0, str(SOURCE))
import verify_b_relative_support_chord_tree as V
import independent_b_difference_tree_replay as TREE
import independent_physical_proxy_cover as PROXY
import verify_b_mixed_tree as MIX
CORE = V.CORE

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('prefix',type=Path)
    ap.add_argument('trial',type=Path)
    ap.add_argument('output',type=Path)
    a=ap.parse_args()
    start=time.monotonic()
    prefix=a.prefix.resolve(); trial=a.trial.resolve()
    m=json.loads((prefix/'manifest.json').read_text())
    chain=[];index=260
    while index is not None:
        e=m['nodes'][index];p=prefix/e['file']
        assert sha256(p.read_bytes()).hexdigest()==e['sha256']
        n=json.loads(p.read_text());chain.append((p,n));index=n['parent']
    chain.reverse()
    adapter=V.Adapter(HERE.parent/'b_family/b16a_I32_complete_H_checkpoint')
    parent=m['parent'];_,state=adapter.replay(adapter.retain(parent['path'],parent['sha256']))
    audits=[]
    for k,(p,n) in enumerate(chain):
        adapter.retain(p)
        assert n['initial']==CORE.state_view(state)
        audit,after=CORE.check_record(n['record'],state,adapter)
        assert after is not None
        audits.append(dict(index=n['index'],audit=audit))
        if k+1==len(chain):
            state=after
            break
        child=chain[k+1][1];choice=child['choice'];split=n['split']
        assert child['index'] in n['children']
        if split['kind']=='proxy':state=PROXY.proxy_child(after,split['pair'],choice,adapter)
        elif split['kind']=='sat':state=CORE.sat_child(after,split['pair'],choice,adapter)
        else:
            assert split['kind']=='angle'
            state=MIX.angle_child(after,split['owner'],split['cut'],choice,adapter)
    for group in ('sources','accepted_geometric_sources'):
        for p,h in m[group].items():adapter.retain(p,h)
    tm=json.loads((trial/'manifest.json').read_text());anchor=tm['parent']
    anchor_path=adapter.retain(anchor['path'],anchor['sha256'])
    anchor_node=json.loads(anchor_path.read_text())
    assert anchor_node['index']==260
    assert anchor_node['record']['final']==CORE.state_view(state)
    prior_replay=adapter.replay
    def verified_anchor(path):
        if Path(path).resolve()==anchor_path.resolve():
            return dict(status='FRESH_VERIFIED_CONDITIONAL_ORIGINAL_PREFIX',prefix_audits=audits),deepcopy(state)
        return prior_replay(path)
    adapter.replay=verified_anchor
    report=TREE.verify_tree(trial/'manifest.json',adapter)
    for p in (Path(__file__),Path(TREE.__file__),Path(V.__file__)):
        adapter.retain(p)
    adapter.recheck()
    assert report['whole_original_proved'] is False
    assert not any(name in sys.modules for name in ('numpy','scipy','highspy','b_center_difference_split','physical_relative_support_chords'))
    report.update(status='PASS_COMPLETE_CONDITIONAL_DIFFERENCE_TREE' if report['complete'] else 'PASS_PARTIAL_CONDITIONAL_DIFFERENCE_TREE',
                  verified_global_prefix_node=260,whole_original_proved=False,new_original_ledger_credit=0,
                  source_sha256=adapter.files,prefix_nodes=len(chain),prefix_audits=audits,
                  numeric_producer_imported=False,relative_support_chord_rows_checked=adapter.relative_support_chord_rows,seconds=time.monotonic()-start)
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('status','nodes','complete_unions','open_leaves','local_deductions','prefix_nodes','seconds')}),flush=True)

if __name__=='__main__':main()
