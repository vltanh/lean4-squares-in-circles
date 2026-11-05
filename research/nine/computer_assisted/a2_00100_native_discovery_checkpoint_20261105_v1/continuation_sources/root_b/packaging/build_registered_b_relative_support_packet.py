#!/usr/bin/env python3
"""Curate one B original tree and its exact, unchanged proof dependencies."""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,shutil
TOOLS=Path(__file__).resolve().parent
HERE=PRIOR=REPO=None
PACKAGES=('coupled_three_energy_v1','physical_gram_square_rows_v1',
          'adaptive_original_corner_disk_v1','unit_frame_corner_rows_v1','row_label_substitutions_v1')

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,v):p.write_text(json.dumps(v,indent=2)+'\n')

def main():
    global HERE,PRIOR,REPO
    ap=argparse.ArgumentParser();ap.add_argument('tree',type=Path);ap.add_argument('report',type=Path);ap.add_argument('output',type=Path)
    ap.add_argument('--open-prototype',action='store_true')
    ap.add_argument('--source-root',type=Path,required=True);ap.add_argument('--prior',type=Path,required=True);ap.add_argument('--repo',type=Path,required=True)
    a=ap.parse_args();HERE=a.source_root.resolve();PRIOR=a.prior.resolve();REPO=a.repo.resolve()
    tree=a.tree.resolve();report=json.loads(a.report.read_text());m=json.loads(tree.read_text())
    assert report['certificate_sha256']==sha(tree)
    assert report['entire_registered_original_domain_retained']is True
    assert report['initial_original_id'].startswith('negative-')
    if not a.open_prototype:
        assert report['status']=='PASS_COMPLETE_ORIGINAL_PHYSICAL_TREE'
        assert report['complete']is True and report['whole_original_proved']is True and report['open_leaves']==0
    out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
    bindings={}
    cap_manifest=json.loads((HERE/'cap_proof/PREMISE_BINDINGS.json').read_text())
    cap_inherited=cap_manifest['inherited_dependencies']
    def bind(raw,h):
        p=Path(raw).resolve();assert sha(p)==h,('input changed',str(p))
        if p.is_relative_to(PRIOR):
            entry=dict(root='prior',path=str(p.relative_to(PRIOR)),sha256=h)
        else:
            if any(h==v and str(p).endswith('/'+k) for k,v in cap_inherited.items()):
                names=[k for k,v in cap_inherited.items()if h==v and str(p).endswith('/'+k)];assert len(names)==1
                target=out/'accepted_repo/research/nine'/names[0]
            elif p.is_relative_to(HERE/'cap_proof'):target=out/'accepted_repo/research/nine/computer_assisted/full_angle_common_side_row_v1'/p.relative_to(HERE/'cap_proof')
            elif p.is_relative_to(TOOLS):target=out/'code'/p.relative_to(TOOLS)
            elif p.is_relative_to(HERE):
                rel=p.relative_to(HERE)
                if len(rel.parts)==1 and p.suffix=='.py':target=out/'code'/rel
                elif rel.parts[0]in('sharp_terminal','row_guards','accepted_unit_four_corner','universal_center_disk','incircle_distance_chords','rotating_center_cones','general_center_cones','relative_support_chords','cap_proof'):target=out/'code'/rel
                else:target=out/'records'/rel
            elif p.is_relative_to(REPO):target=out/'accepted_repo'/p.relative_to(REPO)
            else:target=out/'inputs'/f'{h}_{p.name}'
            target.parent.mkdir(parents=True,exist_ok=True)
            if target.exists():assert sha(target)==h
            else:shutil.copy2(p,target)
            entry=dict(root='packet',path=str(target.relative_to(out)),sha256=h)
        key=str(p);assert key not in bindings or bindings[key]==entry;bindings[key]=entry
        return entry
    original_manifest=json.loads((PRIOR/'SHA256_MANIFEST.json').read_text())
    published=REPO/'research/nine/computer_assisted/a2_00100_b340_complete_original/PUBLISHED_PRIOR.json'
    publication=json.loads(published.read_text())
    assert sha(PRIOR/'SHA256_MANIFEST.json')==publication['frozen_manifest_sha256']
    for name,h in original_manifest['files'].items():bind(PRIOR/name,h)
    bind(PRIOR/'SHA256_MANIFEST.json',sha(PRIOR/'SHA256_MANIFEST.json'))
    for p,h in report['source_sha256'].items():bind(p,h)
    frozen_hash='ea000e84c04675fe22424e5c20d3df9d735d659065349800aef2699170bff604'
    frozen_paths=[Path(p)for p,h in report['source_sha256'].items()if h==frozen_hash]
    assert len(frozen_paths)==1
    frozen_register=frozen_paths[0];current_register=REPO/'research/nine/gates/A2_00100_FIXED_FRONTIER.json'
    old=json.loads(frozen_register.read_text());current=json.loads(current_register.read_text())
    fields=('id','sign','baseline_frontier_index','path')
    assert len(old['cells'])==len(current['cells'])==231
    assert [[c[k]for k in fields]for c in old['cells']]==[[c[k]for k in fields]for c in current['cells']]
    current_cell=[c for c in current['cells']if c['id']==report['initial_original_id']]
    assert len(current_cell)==1 and current_cell[0]['path']==report['initial_path']and current_cell[0]['status']=='OPEN'
    current_definition_attachment=dict(frozen_definition=bind(frozen_register,frozen_hash),
        current_register=bind(current_register,sha(current_register)),compared_fields=list(fields),
        all_231_original_definitions_unchanged=True,selected_original_status_before_acceptance='OPEN')
    for entry in m['nodes']:bind(tree.parent/entry['file'],entry['sha256'])
    tree_entry=bind(tree,sha(tree))
    for name in('verify_b_relative_support_chord_tree.py','verify_b_center_difference_tree.py','verify_b_four_corner_trees.py','independent_b_difference_tree_replay.py','REGISTERED_B_COMPLETE_TREE_HAND_PROOF.md','CENTER_DIFFERENCE_COVER_HAND_PROOF.md'):
        bind(HERE/name,sha(HERE/name))
    for name in ('build_registered_b_relative_support_packet.py','replay_registered_b_relative_support_packet.py'):
        bind(TOOLS/name,sha(TOOLS/name))
    for pkg in PACKAGES:
        root=REPO/'research/nine/computer_assisted'/pkg
        assert root.is_dir(),pkg
        for p in sorted(root.rglob('*')):
            if p.is_file()and '__pycache__'not in p.parts:bind(p,sha(p))
    (out/'original_audits').mkdir()
    shutil.copy2(a.report,out/'original_audits/EXACT_TREE_REPLAY.json')
    shutil.copy2(published,out/'PUBLISHED_PRIOR.json')
    dump(out/'BINDINGS.json',bindings)
    info=dict(schema='registered_B_original_complete_physical_tree_packet_v1',exact_entry='verify_b_relative_support_chord_tree',original_id=report['initial_original_id'],
        original_path=report['initial_path'],tree=tree_entry,open_prototype=a.open_prototype,
        current_definition_attachment=current_definition_attachment,
        prior_directory=PRIOR.name,prior_archive_sha256=publication['archive_sha256'],
        prior_manifest_sha256=publication['frozen_manifest_sha256'],prior_inputs=len(original_manifest['files']),
        exact_tree_report_sha256=sha(a.report),all_nine_original_frames_retained=True,
        all_36_original_corner_and_pair_predicates_retained=True,all_five_center_cones_retained=True,
        actual_AB_BC_EF_FG_and_strict_CD_retained=True,all_shared_closed_faces_retained=True,
        complete=report['complete'],counts={k:report[k]for k in('nodes','complete_unions','terminal_leaves','excluded_leaves','open_leaves','local_rounds','local_deductions','local_printed_rows','universal_center_disk_rows_checked','incircle_chord_rows_checked','rotating_center_cone_rows_checked','general_center_cone_rows_checked','relative_support_chord_rows_checked')},
        new_original_ledger_credit=0,new_mask_ledger_credit=0,whole_acceptance_requires_fresh_portable_replay=True)
    dump(out/'ORIGINAL_PROOF.json',info)
    audits={r['index']:r for r in report['node_audits']}
    lines=['# Original '+info['original_id']+' terminal table','',
        'All rows refer to unchanged original labels A=0 through I=8. Exact coefficients and rational multipliers remain in the bound node records.',
        'The proof must independently replay every complete four-way inset, eight-way physical separator, and two-way closed angle or center-coordinate-difference cover.',
        '', '| Leaf | Depth | Parent | Last choice | Rounds | Deductions | Conclusion |', '|---:|---:|---:|---|---:|---:|---|']
    for leaf in report['leaf_table']:
        audit=audits[leaf['index']];r=audit['audit']
        if not leaf['excluded']:conclusion='OPEN — no exclusion'
        elif r['reserve']is None:conclusion=leaf['terminal_kind']
        else:
            q=F(r['reserve']);assert q>0;b=F(1)
            while b>q:b/=2
            conclusion='positive exact reserve ≥ '+str(b)
        lines.append(f'| {leaf["index"]} | {leaf["depth"]} | {audit["parent"]} | {audit["choice"]} | {r["rounds"]} | {r["deductions"]} | {conclusion} |')
    (out/'COMPLETE_TERMINAL_TABLE.md').write_text('\n'.join(lines)+'\n')
    dump(out/'INPUT_MANIFEST.json',dict(schema='frozen_registered_B_original_packet_inputs_v1',
        files={str(p.relative_to(out)):sha(p)for p in sorted(out.rglob('*'))if p.is_file()},
        old_workspace_reads_forbidden_during_portable_replay=True))
    print(json.dumps(dict(status='FROZEN_OPEN_PROTOTYPE'if a.open_prototype else'FROZEN_COMPLETE_ORIGINAL_PACKET',
        packet=str(out),bindings=len(bindings),original_id=info['original_id'],complete=info['complete'])),flush=True)

if __name__=='__main__':main()
