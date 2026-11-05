#!/usr/bin/env python3
"""Fresh unchanged-core arithmetic at a certified A165 leaf final state."""
if not __debug__:raise RuntimeError('Assertions required.')
from pathlib import Path
from copy import deepcopy
from fractions import Fraction as F
import argparse,json,sys
import attachment as A
def run(folder,output):
    folder=Path(folder).resolve();output=Path(output).resolve();assert not output.exists()
    with A.environment()as e:
        d=A.read(folder/'ATTACHMENT.json');r=A.read(folder/'SUFFIX_RECORD.json');combined=A.read(folder/'CONTINUED_NODE_00154.json')
        assert d['schema']=='A165_existing_height_literal_first_use_v1'and d['leaf']==154
        assert d['source_manifest_sha256']==A.MANIFEST_SHA and d['source_full_report_sha256']==A.REPORT_SHA
        assert d['source_node_sha256']==e['node']['sha256']and d['source_final']==e['prior']['final']
        assert A.sha(folder/'SUFFIX_RECORD.json')==d['suffix_sha256']
        assert A.sha(folder/'CONTINUED_NODE_00154.json')==d['continued_node_sha256']
        assert combined['initial']==e['prior']['initial']and combined['rounds'][:-1]==e['prior']['rounds']
        assert combined['rounds'][-1:]==r['rounds']and combined['final']==r['final']
        assert {k:v for k,v in combined.items()if k not in('rounds','final')}=={k:v for k,v in e['prior'].items()if k not in('rounds','final')}
        audit,state=A.CORE.check_record(r,e['initial'],e['adapter']);assert state is not None
        assert audit['rounds']==audit['deductions']==1 and audit['printed_rows_checked']==3
        assert e['checker'].i64_original_height_occurrences==1
        assert e['checker'].i64_original_endpoint_occurrences==0
        rr=r['rounds'][0];proposal=rr['proposals'][0]
        assert proposal['key']==17 and proposal['sign']==-1
        assert proposal['residual_coefficients']==[]and proposal['residual_correction']=='0'
        assert F(state['positions'][17][0])-F(e['initial']['positions'][17][0])>=F(1,2000)
        damages=[]
        for label,mutate in (
            ('negative_weight',lambda x:x['rounds'][0]['proposals'][0]['weights'][0].__setitem__(1,-1)),
            ('changed_height_rhs',lambda x:next(z for z in x['rounds'][0]['printed_rows']if z['name']==A.ROWS.HEIGHT_NAME).__setitem__('rhs','-17/25')),
            ('changed_final',lambda x:x['final']['positions'][17].__setitem__(0,'0')),
            ('initial_rebased',lambda x:x['initial']['positions'][17].__setitem__(0,'0')),
            ('residual_erased',lambda x:x['rounds'][0]['proposals'][0].__setitem__('residual_correction','1/1000'))):
            bad=deepcopy(r);mutate(bad)
            try:A.CORE.check_record(bad,e['initial'],e['adapter'])
            except(AssertionError,ValueError,KeyError):damages.append(label)
            else:raise AssertionError(('accepted damaged record',label))
        assert len(damages)==5
        assert not any(k in sys.modules for k in('isolate_height_round','original_i64_bound_rows','numpy','scipy','highspy'))
        report=dict(status='PASS_FIRST_I64_HEIGHT_LITERAL_ORDINARY_ROUND',leaf=154,source_node_sha256=e['node']['sha256'],
            source_full_consumer_report_sha256=A.REPORT_SHA,source_manifest_sha256=A.MANIFEST_SHA,
            suffix_sha256=A.sha(folder/'SUFFIX_RECORD.json'),exact_audit=audit,
            positive_weighted_I64_height_occurrences=1,weight_denominator=1<<40,zero_residual=True,
            before_y_I_lower=str(e['initial']['positions'][17][0]),after_y_I_lower=str(state['positions'][17][0]),
            improvement=str(state['positions'][17][0]-e['initial']['positions'][17][0]),damaged_records_rejected=damages,
            source_reuse=e['source_reuse'],all_initial_and_old_prefix_bytes_preserved=True,
            full_cover_replacement_performed=False,full_cover_replay_repeated=False,
            numerical_solves=0,new_rows_family=0,new_original_cells=0,new_masks=0)
        A.write(output,report);print(json.dumps({k:report[k]for k in('status','leaf','after_y_I_lower','improvement','positive_weighted_I64_height_occurrences')}),flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('folder',type=Path);p.add_argument('output',type=Path);a=p.parse_args();run(a.folder,a.output)
