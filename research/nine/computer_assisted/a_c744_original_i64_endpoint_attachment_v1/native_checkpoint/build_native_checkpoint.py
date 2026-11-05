#!/usr/bin/env python3
"""Make a small immutable native source/evidence packet; never rerun arithmetic."""
from pathlib import Path
from collections import Counter
import json,hashlib,shutil

ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
OUT=WORK/'a_c744_original_i64_endpoint_native_v1'
PRIOR=WORK/'i64_fresh_gate_native_checkpoint_v1'
REPO=ROOT/'repo'
FAMILY=WORK/'a_c744_original_i64_bounds_v2'
DIRECT=WORK/'a_c744_original_i64_direct_use_v3'
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path):return json.loads(Path(path).read_text())
def write(path,value):
    assert not path.exists();path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,indent=2)+'\n')

def main():
    assert not OUT.exists();OUT.mkdir()
    copied={}
    def copy(source,member):
        source=Path(source).resolve();target=OUT/member
        assert source.is_file()and not source.is_symlink()and not target.exists()
        raw=source.read_bytes();h=hashlib.sha256(raw).hexdigest()
        target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
        assert sha(source)==sha(target)==h
        copied[str(source)]=dict(member=member,sha256=h,bytes=len(raw))
    family=read(FAMILY/'SOURCE_BINDINGS.json')
    assert sha(FAMILY/'SOURCE_BINDINGS.json')=='93d79d81b6f9f4b2499220b75aca0e6c2c400829261ff783a6ff068fa4301e78'
    for name,h in family['files'].items():
        assert sha(FAMILY/name)==h;copy(FAMILY/name,'family/'+name)
    copy(FAMILY/'SOURCE_BINDINGS.json','family/SOURCE_BINDINGS.json')
    for path in sorted(DIRECT.iterdir()):
        if path.is_file():copy(path,'direct_v3/'+path.name)
    for name in('A_C744_ORIGINAL_I64_BOUND_CONTROLS_V2.json','A_C744_ORIGINAL_I64_FIRST_DIRECT_USE_V3.json',
        'A_C744_ORIGINAL_I64_FIRST_DIRECT_USE_V3_RECORD.json','A_C744_ORIGINAL_I64_FIRST_DIRECT_USE_V3.log',
        'A_C744_ORIGINAL_I64_FIRST_DIRECT_USE_V2.log','A_C744_ORIGINAL_I64_FIRST_DIRECT_USE_V2_EXECUTION.json'):
        copy(WORK/name,'evidence/'+name)
    for path in (ROOT/'d_work/A_ORIGINAL_I64_FIRST_DIRECT_ROOT_FRESH_REPLAY.json',
        ROOT/'d_work/replay_a_original_i64_first_record_v1.py',
        ROOT/'b_work/recovery_20261105_reset2/A_I64_ORIGINAL_ENDPOINT_V2_SOURCE_REVIEW.json',
        ROOT/'b_work/recovery_20261105_reset2/A_I64_ORIGINAL_ENDPOINT_V2_SOURCE_REVIEW.md'):
        copy(path,'reviews/'+path.name)
    copy(__file__,'build_native_checkpoint.py')
    prior_copies=read(PRIOR/'COPY_PROVENANCE.json')['sources']
    prior_dependencies=read(PRIOR/'DEPENDENCIES.json')
    assert sha(PRIOR/'INPUT_MANIFEST.json')=='db309823e7a1f27c85ee2c17cd66aea7d459244e804d5d4b0e45018c74d2a46b'
    published=REPO/'research/nine/computer_assisted/a_c744_i64_fresh_native_gate_v1'
    assert sha(published/'INPUT_MANIFEST.json')==sha(PRIOR/'INPUT_MANIFEST.json')
    report=read(WORK/'A_C744_ORIGINAL_I64_FIRST_DIRECT_USE_V3.json');binding=read(FAMILY/'PREMISE_BINDING.json')
    inputs={}
    def add(path,h):
        if path in inputs:assert inputs[path]==h
        inputs[path]=h
    for field in('source_sha256','independent_loaded_dependency_sha256'):
        for path,h in report[field].items():add(path,h)
    for path,h in binding['independent_helper_sha256'].items():add(path,h)
    for value in binding.values():
        if isinstance(value,dict)and set(value)=={'path','sha256'}:add(value['path'],value['sha256'])
    paths={}
    for path,h in sorted(inputs.items()):
        assert sha(path)==h,path
        if path in copied:
            assert copied[path]['sha256']==h
            paths[path]=dict(kind='INCLUDED_EXACT_ALIAS',member=copied[path]['member'],sha256=h)
        elif path in prior_copies:
            old=prior_copies[path];assert old['sha256']==h and sha(PRIOR/old['member'])==h
            paths[path]=dict(kind='PUBLISHED_FRESH813_PACKET_MEMBER',member=old['member'],sha256=h)
        elif path in prior_dependencies['paths']:
            old=prior_dependencies['paths'][path];assert old['sha256']==h
            paths[path]=dict(kind='PUBLISHED_FRESH813_TRANSITIVE_INPUT',sha256=h,prior_exact_mapping=old)
        elif Path(path).is_relative_to(REPO):
            paths[path]=dict(kind='PUBLISHED_REPOSITORY_FILE',file=str(Path(path).relative_to(REPO)),sha256=h)
        else:
            assert Path(path).stat().st_size<2_000_000,path
            member='additional_exact_sources/'+h
            if not(OUT/member).exists():copy(path,member)
            paths[path]=dict(kind='INCLUDED_EXACT_ALIAS',member=member,sha256=h)
    dependencies=dict(schema='original_I64_endpoint_native_dependency_map_v1',
        fresh813_publication=dict(commit='7e00375c5a72cbd462e5dd7b788f7f01ddbac25d',
            package='research/nine/computer_assisted/a_c744_i64_fresh_native_gate_v1',
            input_manifest_sha256=sha(published/'INPUT_MANIFEST.json'),archive_sha256='fd9ebbd7781207796ef51ea969cec103a82374f96c9d142948564967fbb17adf',
            dependency_map_sha256=sha(published/'DEPENDENCIES.json'),
            publication_manifest_sha256=sha(published/'PUBLICATION_MANIFEST.json')),
        complete_A1_publication=prior_dependencies['complete_A1_publication'],
        I64_recovery_publication=prior_dependencies['I64_recovery_publication'],
        paths=paths,categories=dict(Counter(x['kind']for x in paths.values())),
        missing_unpreserved_dependencies=[],full_cold_replay_claimed=False,
        historical_A1_and_fresh813_arithmetic_repeated=False)
    write(OUT/'DEPENDENCIES.json',dependencies)
    write(OUT/'OBSERVED_EXECUTION.json',dict(schema='observed_native_exact_endpoint_execution_v1',
        successful_agent_session=10772,observed_exit_code=0,
        successful_report_sha256='3fc7996b0a2571cfd2d232d5b3811f4d27b39ced63c1b4c9330d551c1ad5f481',
        successful_record_sha256='c183d3ee7c8dcaf80c4e5a3ff6fc0d6a37c820545a3e722cb32a4361bb8ff21d',
        bound_control_session=54815,bound_control_observed_exit=0,
        failed_preparation_session=5032,failed_preparation_observed_exit=1,
        failed_preparation_reached_weighted_round=False,
        failed_preparation_reason='The v2 entrypoint incorrectly expected no inherited choices; the exact original inward_row_escape choice is retained by the v3 entrypoint.',
        family_sources_unchanged_by_v3=True,numerical_solves=0,new_original_cells=0,new_masks=0))
    readme='''# Original-wide I64 endpoint family and exact first use

This checkpoint accepts 414 necessary endpoint rows and one separate height
row on the entire unchanged A-c744 original in mask001/00. It does not exclude
that original or complete a mask. All nine originals, 36 corners, 36 pairs,
five marked cones and closed faces remain in scope.

The complete physical implication is in family/WHOLE_ORIGINAL_ENDPOINT_ATTACHMENT.md.
The old complete components0/1/2/4 and the accepted actual-AB16/25 theorem with
the strict-CD equality blocker imply the new I-high16/25 inequality everywhere
on this original. The separately published fresh7-round813-deduction source is
therefore necessary for the whole original. Its certified final box supplies
the414 endpoint expansions. No selected SAT predicate or auxiliary bound is
transported. The source I-slope interval remains[-1,1], so this packet makes no
unconditional7/10 promotion.

The agent's actual first use appends one ordinary exact round to the unchanged
whole-original parent:268 positive unit-weight deductions, zero residual, the
usual grid and frame propagation, with OPEN final state. The original path
and its inherited inward_row_escape choice are retained. The independent root
gate separately replayed the same268 deductions and matched the final state.
Both gates reuse previously accepted source proofs by full identity; they do
not repeat the757-node A1 proof or the published fresh813 arithmetic.

The original v2 entrypoint's failed preparation and its log are preserved.
It stopped before any weighted round because it expected an empty choice list.
The separate v3 entrypoint fixes only that expectation and the local import
path. The9 frozen mathematical family files were not changed.

This is native exact evidence with explicit published dependencies, not a
self-contained cold proof. DEPENDENCIES.json pins the prior published A1/base,
I64 recovery and fresh813 packets and every new exact source alias. Native
absolute paths are provenance metadata; extracting this checkpoint alone does
not recreate them. No A165 continuation or lost235-node consumer result is
claimed by this packet.

The packet header/member checker performs only byte, binding and count checks:
`python -B -S check_checkpoint.py --output /tmp/i64_endpoint_header_audit.json`.
Reproducing the native weighted gate requires restoring the exact dependency
aliases, then invoking direct_v3/first_direct_use_v3.py from its recorded native
layout. Full cold replay of older dependencies remains a separate protocol.
'''
    (OUT/'README.md').write_text(readme)
    checker='''#!/usr/bin/env python3
"""File/header checks only; no weighted proof is replayed by this tool."""
if not __debug__:raise RuntimeError('Checkpoint checks require assertions.')
from pathlib import Path
import argparse,hashlib,json
HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 assert not a.output.exists()and not a.output.resolve().is_relative_to(HERE)
 m=read(HERE/'INPUT_MANIFEST.json');actual={str(p.relative_to(HERE))for p in HERE.rglob('*')if p.is_file()}
 assert not any(p.is_symlink()for p in HERE.rglob('*'))
 assert actual==set(m['files'])|{'INPUT_MANIFEST.json'}
 for rel,item in m['files'].items():
  q=HERE/rel;assert q.resolve().is_relative_to(HERE)and q.stat().st_size==item['bytes']and sha(q)==item['sha256']
 f=read(HERE/'family/SOURCE_BINDINGS.json')
 assert sha(HERE/'family/SOURCE_BINDINGS.json')=='93d79d81b6f9f4b2499220b75aca0e6c2c400829261ff783a6ff068fa4301e78'
 for rel,h in f['files'].items():assert sha(HERE/'family'/rel)==h
 b=read(HERE/'family/PREMISE_BINDING.json');assert b['endpoint_rows']==414 and b['whole_original_height_rows']==1 and b['valid_on_whole_original']is True
 r=read(HERE/'evidence/A_C744_ORIGINAL_I64_FIRST_DIRECT_USE_V3.json')
 assert sha(HERE/'evidence/A_C744_ORIGINAL_I64_FIRST_DIRECT_USE_V3.json')=='3fc7996b0a2571cfd2d232d5b3811f4d27b39ced63c1b4c9330d551c1ad5f481'
 assert r['status']=='PASS_FIRST_EXACT_ORIGINAL_WIDE_I64_DIRECT_BOUND_USE'and r['scope']=='WHOLE_UNCHANGED_ORIGINAL_PARENT'
 assert r['ordinary_exact_audit']['deductions']==r['ordinary_exact_audit']['printed_rows_checked']==r['weighted_endpoint_occurrences']==268
 assert sha(HERE/'evidence/A_C744_ORIGINAL_I64_FIRST_DIRECT_USE_V3_RECORD.json')==r['record']['sha256']
 root=read(HERE/'reviews/A_ORIGINAL_I64_FIRST_DIRECT_ROOT_FRESH_REPLAY.json')
 assert root['exact_audit']==r['ordinary_exact_audit']and root['record_sha256']==r['record']['sha256']and root['final_state_matches']is True
 controls=read(HERE/'evidence/A_C744_ORIGINAL_I64_BOUND_CONTROLS_V2.json');assert controls['damaged_literals_or_callers_rejected']==432 and controls['endpoint_rows']==414
 for x in(r,root,controls):assert x['new_original_cells']==x['new_masks']==0
 deps=read(HERE/'DEPENDENCIES.json');assert deps['missing_unpreserved_dependencies']==[]and deps['full_cold_replay_claimed']is False
 for path,item in deps['paths'].items():
  if item['kind']=='INCLUDED_EXACT_ALIAS':assert sha(HERE/item['member'])==item['sha256']
 result=dict(status='PASS_ORIGINAL_I64_ENDPOINT_PACKET_BYTES_AND_HEADERS',files=len(actual),
   input_manifest_sha256=sha(HERE/'INPUT_MANIFEST.json'),endpoint_rows=414,separate_height_rows=1,
   saved_direct_deductions=268,weighted_arithmetic_replayed=False,historical_source_arithmetic_repeated=False,
   cold_proof_claimed=False,new_original_cells=0,new_masks=0)
 a.output.write_text(json.dumps(result,indent=2)+'\\n');print(json.dumps(result),flush=True)
if __name__=='__main__':main()
'''
    (OUT/'check_checkpoint.py').write_text(checker)
    write(OUT/'COPY_PROVENANCE.json',dict(schema='original_I64_native_exact_copies_v1',sources=copied))
    files={str(p.relative_to(OUT)):dict(sha256=sha(p),bytes=p.stat().st_size)for p in sorted(OUT.rglob('*'))if p.is_file()}
    write(OUT/'INPUT_MANIFEST.json',dict(schema='original_I64_endpoint_native_packet_v1',files=files,
        new_original_cells=0,new_masks=0,whole_original_still_open=True))
    print(json.dumps(dict(folder=str(OUT),input_manifest_sha256=sha(OUT/'INPUT_MANIFEST.json'),files=len(files)+1,
        bytes=sum(x['bytes']for x in files.values())+(OUT/'INPUT_MANIFEST.json').stat().st_size,
        dependency_categories=dependencies['categories']),indent=2),flush=True)

if __name__=='__main__':main()
