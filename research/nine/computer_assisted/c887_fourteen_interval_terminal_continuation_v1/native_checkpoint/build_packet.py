#!/usr/bin/env python3
"""Compact exact C88717-terminal delta against the published original91-node packet."""
from pathlib import Path
import hashlib,json

ROOT=Path('/workspace/scratch/f9f48fcfb253')
OUT=ROOT/'b_work/c887_fourteen_terminal_publication_v1'
BASE=Path('/tmp/recovered_c_height_packet_064e4aa')
PRIOR=Path('/tmp/c887_complete91_three_terminal_tree_v1_20261105')
TREE=Path('/tmp/c887_complete91_fourteen_interval_tree_v1_20261105')
CODE=ROOT/'b_work/c887_fourteen_interval_terminal_v1'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def dump(p,v):assert not p.exists();p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')

def main():
    assert not OUT.exists();OUT.mkdir();copies={}
    def copy(source,member):
        source=Path(source).resolve();target=OUT/member;assert source.is_file()and not source.is_symlink()and not target.exists()
        data=source.read_bytes();digest=hashlib.sha256(data).hexdigest();target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
        assert sha(source)==sha(target)==digest;copies[str(source)]=dict(member=member,sha256=digest,bytes=len(data))
    assert sha(CODE/'SOURCE_BINDING.json')=='3883125c8fc8bb01fde711577b858f365b6b24c10b0a0665625fe4d5ada7fa15'
    assert sha(TREE/'manifest.json')=='295a4b73434471634c2eb636ac4ffa676cc8a4c26c1ba20e1a3b1f404e40c3e6'
    oldroot=BASE/'payload/ac_work/tree/c887_first_weighted_shared_height_path'
    old=read(oldroot/'manifest.json');prior=read(PRIOR/'manifest.json');final=read(TREE/'manifest.json')
    assert len(old['nodes'])==len(prior['nodes'])==len(final['nodes'])==91
    for p in sorted(CODE.iterdir()):
        if p.is_file():copy(p,'sources/'+p.name)
    earlier=ROOT/'b_work/c887_three_terminal_continuation_v1'
    for p in sorted(earlier.iterdir()):
        if p.is_file():copy(p,'prior_sources/'+p.name)
    copy(oldroot/'manifest.json','metadata/SOURCE_MANIFEST.json')
    copy(PRIOR/'manifest.json','predecessor/manifest.json');copy(TREE/'manifest.json','tree/manifest.json')
    copy(TREE/'CONSTRUCTION_RECEIPT.json','reports/CONSTRUCTION_RECEIPT.json')
    copy('/tmp/c887_complete91_fourteen_interval_exact_v1_20261105/EXACT_REPLAY.json','reports/FOURTEEN_TERMINAL_EXACT_REPLAY.json')
    copy('/tmp/c887_complete91_three_terminal_exact_v1_20261105/EXACT_REPLAY.json','reports/THREE_TERMINAL_EXACT_REPLAY.json')
    copy(BASE/'payload/ac_work/tree/C887_FIRST_WEIGHTED_SHARED_HEIGHT_BOUNDS_REPLAY.json','reports/HISTORICAL_COMPLETE91_REPLAY.json')
    copy('/tmp/c887_complete91_fourteen_interval_construction_v1_20261105.log','reports/CONSTRUCTION.log')
    copy('/tmp/c887_complete91_fourteen_interval_exact_v1_20261105.log','reports/FOURTEEN_TERMINAL_EXACT_REPLAY.log')
    for stem in ['C887_FOURTEEN_INTERVAL_TERMINALS_INDEPENDENT_REVIEW','C887_THREE_TERMINAL_CONTINUATION_INDEPENDENT_REVIEW']:
        for suffix in ['.json','.md']:
            copy(ROOT/'ac_work/recovery_20261105_reset2'/f'{stem}{suffix}','reviews/'+stem+suffix)
    copy(ROOT/'d_work/C887_FOURTEEN_INTERVAL_TERMINALS_ROOT_SOURCE_REVIEW.json','reviews/ROOT_SOURCE_REVIEW.json')
    copy(ROOT/'b_work/c887_fourteen_packet_tools_v1/verify_packet.py','verify_packet.py')
    copy(ROOT/'b_work/c887_fourteen_packet_tools_v1/materialize_trees.py','materialize_trees.py')
    copy(__file__,'build_packet.py')
    nodes=[];included=[]
    for a,b,c in zip(old['nodes'],prior['nodes'],final['nodes']):
        assert a['index']==b['index']==c['index']and a['file']==b['file']==c['file']
        base_member='payload/ac_work/tree/c887_first_weighted_shared_height_path/'+a['file']
        assert sha(BASE/base_member)==a['sha256']and sha(PRIOR/b['file'])==b['sha256']and sha(TREE/c['file'])==c['sha256']
        row=dict(index=a['index'],file=a['file'],published_member=base_member,published_sha256=a['sha256'],
            predecessor_sha256=b['sha256'],continued_sha256=c['sha256'])
        if a['sha256']!=c['sha256']:
            member='nodes/'+c['file'];copy(TREE/c['file'],member);row['included_member']=member;included.append(a['index'])
        nodes.append(row)
    assert included==[1,3,5,11,12,17,19,22,29,30,64,71,73,75,84,85,87]
    dump(OUT/'TREE_ASSEMBLY.json',dict(schema='C887_original91_to17terminal_exact_delta_assembly_v1',
        published_base_input_manifest_sha256=sha(BASE/'INPUT_MANIFEST.json'),published_base_binding_sha256=sha(BASE/'BINDINGS.json'),
        predecessor_manifest_sha256=sha(PRIOR/'manifest.json'),continued_manifest_sha256=sha(TREE/'manifest.json'),
        included_changed_payloads=17,reused_final_published_payloads=74,nodes=nodes,new_original_cells=0,new_masks=0))
    dump(OUT/'OBSERVED_EXECUTION.json',dict(status='PASS_CONSTRUCTION_AND_NEW14_TERMINAL_GATE_OBSERVED_EXIT',
        constructor_session=88208,constructor_observed_exit_code=0,constructor_completion_tool_chunk='b990a9',
        checker_session=9160,checker_observed_exit_code=0,checker_completion_tool_chunk='aef913',
        exact_report_sha256='8ea1ae86b99d401b805951a15ba3f229f9cce4db7a81e126f70c13d1e6002ac7',
        copied_source_count=6,all_old_sources_unchanged=True,weighted_historical_arithmetic_replayed=False,
        new_hull_or_endpoint_family_used=False,numerical_solver_called=False))
    dump(OUT/'PUBLISHED_DEPENDENCIES.json',dict(schema='C88717_terminal_native_delta_dependencies_v1',
        original_complete_packet=dict(publication='research/nine/computer_assisted/c_original_height_consequences_v1',
            commit='8e842e98a4f31fa9e0a2d8ece42bc2661a2783c2',
            input_manifest_sha256=sha(BASE/'INPUT_MANIFEST.json'),binding_sha256=sha(BASE/'BINDINGS.json'),
            archive_sha256='d17d9582e5ebfdde535be70dea47853d5a8d2fa4b0bddc0a287b35255caa745b'),
        historical_complete91_report_sha256=sha(OUT/'reports/HISTORICAL_COMPLETE91_REPLAY.json'),
        accepted_prior_three_terminal_report_sha256=sha(OUT/'reports/THREE_TERMINAL_EXACT_REPLAY.json'),
        prior_three_terminal_sources_included=True,all17changed_nodes_included=True,
        historical_proof_reuse_explicit=True,full_source_arithmetic_not_repeated=True,
        fresh_whole_hull_dependency_absent=True,standalone_cold_proof_claimed=False,new_original_cells=0,new_masks=0))
    (OUT/'README.md').write_text('''# C887: 14 further existing interval exclusions in the complete91-node cover

The retained complete C887 cover now has17 excluded leaves and56 OPEN leaves.
Fourteen existing zero-round physical states are newly excluded by the unchanged
exact center-interval terminal. The earlier three D/G terminals are retained.
All nine originals,36 corners,36 pairs,five cones,strict weakCD and closed faces
remain unchanged. The original cell and mask remain OPEN; no credit is added.

The independent gate freshly checked all14 terminals and56 malformed controls,
and reconstructed every parent/child state across all18 complete4/8/2 covers.
It explicitly reuses the accepted original91-node weighted proof and prior
three-terminal proof by exact identity. Their arithmetic was not repeated.
The newly accepted whole-original hull and any new endpoint family are absent.

The17 changed node payloads are included. The other74 final payloads are exact
aliases to the published original91 packet. Both the prior-three and final
seventeen-terminal manifests are included; materialize_trees.py assembles both
complete trees into fresh output folders using the published base packet.
The14-terminal source gate then runs from an exact copied sources directory
under/tmp with that same frozen published packet and newly assembled trees.
The original portable guard and decoder sources remain unchanged.

verify_packet.py checks bytes, report headers and base aliases only. It does
not repeat row arithmetic. This is an explicit native continuation with
historical proof reuse, not a standalone cold proof. The construction receipt's
pending flag is preserved historical output; the included fresh report and
observed exit receipt record the later completed gate.
''')
    dump(OUT/'COPY_PROVENANCE.json',dict(sources=copies))
    files={str(p.relative_to(OUT)):dict(bytes=p.stat().st_size,sha256=sha(p))for p in sorted(OUT.rglob('*'))if p.is_file()}
    dump(OUT/'INPUT_MANIFEST.json',dict(schema='C887_complete91_seventeen_terminal_delta_v1',files=files,new_original_cells=0,new_masks=0))
    print(json.dumps(dict(status='READY_COMPACT_C88717_TERMINAL_DELTA',folder=str(OUT),files=len(files)+1,
        bytes=sum(v['bytes']for v in files.values())+(OUT/'INPUT_MANIFEST.json').stat().st_size,
        input_manifest_sha256=sha(OUT/'INPUT_MANIFEST.json'),included_nodes=17,reused_final_nodes=74)),flush=True)

if __name__=='__main__':main()
