#!/usr/bin/env python3
"""First exact-only candidate: retain leaf154 prefix and append one height use."""
if not __debug__:raise RuntimeError('Assertions required.')
from pathlib import Path
from copy import deepcopy
import argparse,json
import attachment as A
import isolate_height_round as P
def run(output):
    output=Path(output).resolve();assert not output.exists()
    with A.environment()as e:
        rr,after=P.construct(e['initial'],e['adapter']);assert len(rr['proposals'])==1
        assert rr['proposals'][0]['key']==17 and rr['proposals'][0]['sign']==-1
        assert sum(x['name']==A.ROWS.HEIGHT_NAME for x in rr['printed_rows'])==1
        suffix=dict(status='OPEN',initial=A.CORE.state_view(e['initial']),rounds=[rr],final=A.CORE.state_view(after))
        combined=deepcopy(e['prior']);combined['rounds'].append(rr);combined['final']=suffix['final']
        assert combined['initial']==e['prior']['initial']and combined['rounds'][:-1]==e['prior']['rounds']
        output.mkdir(parents=True,exist_ok=False)
        A.write(output/'SUFFIX_RECORD.json',suffix);A.write(output/'CONTINUED_NODE_00154.json',combined)
        A.write(output/'ATTACHMENT.json',dict(schema='A165_existing_height_literal_first_use_v1',leaf=A.LEAF,
            source_manifest_sha256=A.MANIFEST_SHA,source_full_report_sha256=A.REPORT_SHA,
            source_node_sha256=e['node']['sha256'],source_final=e['prior']['final'],
            suffix_sha256=A.sha(output/'SUFFIX_RECORD.json'),continued_node_sha256=A.sha(output/'CONTINUED_NODE_00154.json'),
            whole_original_height_binding_sha256=A.ROWS.BINDING_SHA,original_initial_unchanged=True,old_round_prefix_retained=True,
            new_path_predicates=0,new_splits=0,numerical_solves=0,independent_replay_pending=True))
        print(json.dumps(dict(status='CANDIDATE_EXACT_HEIGHT_ROW_ISOLATION',leaf=154,
            suffix_sha256=A.sha(output/'SUFFIX_RECORD.json'),new_y_I_lower=suffix['final']['positions'][17][0])),flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('output',type=Path);a=p.parse_args();run(a.output)
