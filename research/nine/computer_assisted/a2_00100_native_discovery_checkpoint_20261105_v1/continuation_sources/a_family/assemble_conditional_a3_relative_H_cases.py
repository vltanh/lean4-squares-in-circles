#!/usr/bin/env python3
"""Fresh exact assembly of the three complete H cases within A-c744/A3.

This is not an original-cell closure: old I-components 0,1,2,4 must also be
assembled by the caller. Every case is rechecked, rather than trusted from a
previous report. The exact transport loader must wrap this program.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,subprocess,sys
import independent_a_c744_component3_post_a1_bound_rows as POST
import independent_actual_ab_any_extra_guard_064 as GUARD

HERE=Path(__file__).resolve().parent
TARGET='positive-c744bc031d40ee64'
ORIGINAL=[['angle',3,1],['angle_cut',[0,'0'],0],['inward_row_escape',[7,8],[4]]]

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def replay(trees,output):
    output=Path(output).resolve();output.parent.mkdir(parents=True,exist_ok=True)
    assert set(trees)=={0,3,4}
    reports={};manifests={};initial=[]
    for h in(0,3,4):
        tree=Path(trees[h]).resolve();m=json.loads((tree/'manifest.json').read_text())
        assert m['stronger_scope']['H_component']==h
        assert m['stronger_scope']['H_ordered_extra_assumption']==(h in(3,4))
        report=output.with_name(output.stem+f'_H{h}.json')
        log=report.with_suffix('.log')
        with log.open('w')as stream:
            subprocess.run([sys.executable,'-B','-S',str(HERE/'verify_conditional_a3_relative_tree.py'),str(tree),str(report)],check=True,stdout=stream,stderr=subprocess.STDOUT)
        r=json.loads(report.read_text())
        assert r['status']=='PASS_COMPLETE_SCOPED_A3_CONDITIONAL_TREE'
        assert r['open_leaves']==0 and r['H_component']==h
        assert r['H_complete_case_union_required']==[0,3,4]
        assert r['original_id']==TARGET and r['original_path']==ORIGINAL and r['component']==3
        assert r['all_nine_originals_retained'] is True and r['closed_shared_faces_retained'] is True
        assert r['numerical_producer_imported'] is False
        assert r['new_original_cells']==r['new_masks']==0
        manifests[h]=m
        first=m['nodes'][0]
        assert first['parent']is None and first['restriction']is None and first['depth']==0
        assert sha(tree/first['file'])==first['sha256']
        initial.append(json.loads((tree/first['file']).read_text())['initial'])
        reports[str(h)]={'path':str(report),'sha256':sha(report),'report':r}
    assert initial[0]==initial[1]==initial[2]
    for key in('id','original_path','component','scope','parent','conditional_parent','closed_domain','component3_post_a1_bound_state'):
        assert manifests[0][key]==manifests[3][key]==manifests[4][key]
    binding=POST.verify_binding()
    for h in(0,3,4):
        s=reports[str(h)]['report']['fresh_component3_post_a1_bound_source']
        assert s['status']=='PASS_FRESH_UNSPLIT_A_C744_COMPONENT3_POST_A1_BOUND_STATE'
        assert s['binding_sha256']==POST.BINDING_SHA
    # This source is valid on every point in the unsplit A3 domain. It is
    # freshly rederived by each case checker before that case is accepted.
    state=binding['state'];g=GUARD.evaluate(state,8)
    assert g['premises_proved'] is True
    assert all(F(v[0])>=0 for v in g['B_extra_D_order_intervals'])
    assert F(g['B_extra_D_order_intervals'][1][0])>0
    heights=list(map(F,g['four_signed_height_upper_bounds']))
    assert max(heights[k]for k in(0,1,3))<F(16,25)
    raw=state['differences']
    diff={tuple(e['pair']):GUARD.intervals(e['intervals'])for e in raw}if isinstance(raw,list)else{tuple(k):GUARD.intervals(v)for k,v in raw.items()}
    assert diff[7,8][0][0]>=0
    # Algebraic coverage: xH<=xB enters H0. Otherwise B<=H<=I<D.
    # The universal actual-AB terminal excludes all four signed H heights
    # <=16/25. The first two are already <16/25 by the certified source;
    # therefore H-high>=16/25 or H-low>=16/25, giving H3 or H4. Closed
    # equality faces are retained in both order and height branches.
    result=dict(status='PASS_COMPLETE_A_C744_COMPONENT3_CONDITIONAL_H_COVER',
        original_id=TARGET,original_path=ORIGINAL,mask='001/00',squared_radius='1105/256',
        component=3,scope=manifests[0]['scope'],conditional_parent=manifests[0]['conditional_parent'],
        closed_domain=manifests[0]['closed_domain'],H_complete_components=[0,3,4],
        component_reports=reports,certified_post_A1_binding_sha256=POST.BINDING_SHA,
        source_actual_AB_premises=g,source_H_to_I_x_interval=list(map(str,diff[7,8][0])),
        H_components_1_2_excluded_by_source_signed_BD_upper_bounds=list(map(str,heights[:2])),
        all_nine_originals_retained=True,closed_shared_faces_retained=True,
        whole_original_closure_not_claimed=True,other_I_components_required=[0,1,2,4],
        new_original_cells=0,new_masks=0,checker_sha256=sha(__file__))
    output.write_text(json.dumps(result,indent=2)+'\n')
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('H0',type=Path);p.add_argument('H3',type=Path);p.add_argument('H4',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
    replay({0:a.H0,3:a.H3,4:a.H4},a.output)
