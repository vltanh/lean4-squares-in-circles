#!/usr/bin/env python3
"""Preserve small frozen sources/native gates without assembling a cold proof."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import os
import shutil
import subprocess

WORK = Path('/workspace/scratch/f9f48fcfb253')
HERE = Path(__file__).resolve().parent
OUT = HERE / 'native_progress_checkpoints_v1'
REPO = WORK / 'repo'
DIRECT = WORK / 'ac_work/tree'
CB = WORK / 'd_work/cb882_shared_height_bounds'
VERIFY = HERE / 'verify_native_checkpoint_inventory.py'
PUBROOT = 'research/nine/computer_assisted/'
PUBLICATIONS = {
    'A_open_base': dict(commit='05635c849df1d62160b15e5373e85b9c4b95600d',
        path=PUBROOT+'a2_00100_a_c744_portable_open_checkpoint/ARCHIVE_MANIFEST.json',
        manifest_sha256='343731ca252568a3032fe584cf5d389b4be7ae443869d700b842ecc7179a55f6',
        inventory=HERE/'portable_A_prototype/packet/INPUT_MANIFEST.json',
        inventory_sha256='6b730ae5e0dabed264d7e71ba6de72bc15f744d7bba619ed8f6c27a86b9097cf'),
    'C_height_delta': dict(commit='8e842e98a4f31fa9e0a2d8ece42bc2661a2783c2',
        path=PUBROOT+'c_original_height_consequences_v1/ARCHIVE_MANIFEST.json',
        manifest_sha256='8f9be5d565759fb3e04039983721eeb5f22ec7959e4c086090194bc6cfbf8e1c',
        inventory=HERE/'compact_C_publication/delta_v7/INPUT_MANIFEST.json',
        inventory_sha256='06115f494173bc344821932525d7a8522df8ea2ed80b400f735f3b68d4a1b58b'),
    'complete_A1_delta': dict(commit='925e1112814a0758889cafa5c975c27414b86570',
        path=PUBROOT+'a2_00100_a_c744_complete_a1_portable_checkpoint_v2/ARCHIVE_MANIFEST.json',
        manifest_sha256='e07a65074d8ed90eb0afa5a1b3bfd99a488652475fd02ae181f5bee692a3cfe5',
        inventory=HERE/'compact_A1_publication/delta_v2/INPUT_MANIFEST.json',
        inventory_sha256='d8ca6d465aa3831e26d6d0149b8ce734a1043c51694f81a9ce9b9a4e3baaf965'),
}


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def dump(path, value):
    with Path(path).open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def native_member(path):
    return 'native/' + Path(path).relative_to(WORK).as_posix()


def add_sources_from_binding(selected, binding):
    selected.add(binding)
    files = json.loads(binding.read_text())['files']
    for name, digest in files.items():
        path = Path(name) if Path(name).is_absolute() else binding.parent/name
        expected = digest['sha256'] if isinstance(digest, dict) else digest
        assert sha(path) == expected
        # Large source dependency trees remain explicit external prerequisites.
        if path.suffix in ('.py', '.md') or path.stat().st_size <= 100_000:
            selected.add(path)


def references(value, answer, origin):
    if isinstance(value, dict):
        for key, item in value.items():
            if isinstance(key, str) and key.startswith('/') and isinstance(item, str) and len(item) == 64:
                try:
                    int(item, 16)
                except ValueError:
                    pass
                else:
                    answer.setdefault((key, item), set()).add(origin)
            references(item, answer, origin)
        if isinstance(value.get('path'), str) and value['path'].startswith('/'):
            digest = value.get('sha256')
            if isinstance(digest, str) and len(digest) == 64:
                answer.setdefault((value['path'], digest), set()).add(origin)
    elif isinstance(value, list):
        for item in value:
            references(item, answer, origin)


def gate(report, fixture, name, fields, component=None):
    m = json.loads((fixture/'manifest.json').read_text())
    n = m['nodes'][0]
    result = dict(name=name, report_member=native_member(report),
        manifest_member=native_member(fixture/'manifest.json'),
        record_member=native_member(fixture/n['file']),
        native_manifest_path=str(fixture/'manifest.json'), native_record_path=str(fixture/n['file']),
        original_id=m['id'], original_path=m['original_path'], expected_report_fields=fields)
    if component is not None:
        result.update(component=component, closed_domain=m['closed_domain'])
    return result


def write_package(name, selected, publication_keys, header, readme):
    target = OUT/name
    target.mkdir(parents=True)
    selected = set(selected) | {Path(__file__).resolve(), VERIFY}
    provenance = {}
    refs = {}
    for source in sorted(selected):
        source = source.resolve(strict=True)
        assert source.is_relative_to(WORK) and not source.is_symlink()
        before = sha(source)
        size = source.stat().st_size
        assert size <= 8*1024*1024, ('Not a small frozen record', str(source), size)
        member = native_member(source)
        destination = target/member
        destination.parent.mkdir(parents=True, exist_ok=True)
        if size >= 256*1024 and source.suffix == '.json':
            os.link(source, destination)
            storage = 'hardlink_to_frozen_record'
        else:
            shutil.copy2(source, destination)
            storage = 'byte_copy'
        assert sha(destination) == sha(source) == before
        provenance[str(source)] = dict(member=member, sha256=before, bytes=size, storage=storage)
        if source.suffix == '.json':
            references(json.loads(source.read_text()), refs, member)
    published_index = {}
    publications = []
    for key in publication_keys:
        p = PUBLICATIONS[key]
        raw = subprocess.check_output(['git', '-C', str(REPO), 'show', p['commit']+':'+p['path']])
        assert hashlib.sha256(raw).hexdigest() == p['manifest_sha256']
        assert sha(p['inventory']) == p['inventory_sha256']
        member = 'published_references/'+key+'_ARCHIVE_MANIFEST.json'
        destination = target/member
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(raw)
        inv = json.loads(p['inventory'].read_text())['files']
        for digest in inv.values():
            digest = digest['sha256'] if isinstance(digest, dict) else digest
            published_index.setdefault(digest, []).append(key)
        meta = json.loads(raw)
        publications.append(dict(name=key, commit=p['commit'], repository_path=p['path'],
            manifest_member=member, manifest_sha256=p['manifest_sha256'],
            archive_sha256=meta.get('archive_sha256', meta.get('sha256')),
            assembled_input_manifest_sha256=p['inventory_sha256'],
            archive_and_full_inventory_contents_bundled=False,
            publication_url='https://github.com/vltanh/lean4-squares-in-circles/tree/'+p['commit']+'/'+str(Path(p['path']).parent)))
    rows = []
    for (path, digest), origins in sorted(refs.items()):
        included = provenance.get(path)
        row = dict(native_path=path, sha256=digest, referenced_by=sorted(origins))
        if included and included['sha256'] == digest:
            row.update(availability='included_exact_bytes', member=included['member'])
        elif digest in published_index:
            row.update(availability='published_content_by_hash_not_bundled',
                       published_content_indexes=sorted(set(published_index[digest])))
        else:
            row.update(availability='native_reference_not_bundled')
        rows.append(row)
    dependency = dict(schema='explicit_native_and_published_prerequisite_inventory_v1',
        published_packages=publications, references=rows,
        availability_counts=dict(Counter(row['availability'] for row in rows)),
        hash_availability_is_not_a_relocation_or_cold_replay=True,
        unresolved_references_are_explicitly_not_bundled=True,
        omitted_native_prerequisites_rehashed_during_build=False)
    dump(target/'DEPENDENCIES.json', dependency)
    dump(target/'SOURCE_PROVENANCE.json', provenance)
    header.update(native_exact_evidence_only=True, self_contained_cold_proof=False,
        new_original_cells=0, new_masks=0, full_proof_replayed_during_checkpoint_build=False,
        live_numerical_frontiers_included=False,
        source_and_record_bytes_unchanged=True, dependency_inventory='DEPENDENCIES.json')
    dump(target/'CHECKPOINT.json', header)
    (target/'README.md').write_text(readme)
    files = {p.relative_to(target).as_posix(): dict(sha256=sha(p), bytes=p.stat().st_size)
             for p in sorted(target.rglob('*')) if p.is_file()}
    dump(target/'INPUT_MANIFEST.json', dict(schema='native_progress_checkpoint_file_inventory_v1',
        files=files, exact_record_bytes_preserved=True, native_evidence_only=True,
        cold_proof_bundle=False, new_original_cells=0, new_masks=0))
    for source, item in provenance.items():
        assert sha(source) == sha(target/item['member']) == item['sha256']
    return dict(folder=str(target), files=len(files), bytes=sum(x['bytes'] for x in files.values()),
        input_manifest_sha256=sha(target/'INPUT_MANIFEST.json'), dependency_counts=dependency['availability_counts'])


def main():
    assert not OUT.exists()
    OUT.mkdir()
    direct_names = [
        'direct_shared_bound_round.py', 'direct_shared_bound_precheck.py',
        'search_with_direct_shared_bound_round.py', 'check_direct_shared_bound_round_controls.py',
        'check_direct_shared_search_composition.py', 'DIRECT_SHARED_BOUND_ROUND_SOURCE_FREEZE.json',
        'DIRECT_SHARED_BOUND_ROUND_EXACT_CONTROLS.json', 'DIRECT_SHARED_BOUND_PRECHECK_CONTROLS.json',
        'DIRECT_SHARED_SEARCH_COMPOSITION_CONTROLS.json', 'DIRECT_SHARED_BOUND_ROUND_HAND_PROOF.md',
        'physical_sat_diagonal_engine.py', 'independent_physical_sat_diagonal_replay.py',
        'prepare_cb882_direct_shared_bound_round.py', 'prepare_c887_direct_shared_bound_round.py',
        'CB882_DIRECT_SHARED_BOUND_FIRST_EXACT_REPLAY.json',
        'CB882_DIRECT_SHARED_BOUND_FIRST_LAZY_EXACT_REPLAY.json',
        'CB882_DIRECT_SHARED_LAZY_READER_ACTUAL_ATTACHMENT.json',
        'C887_DIRECT_SHARED_BOUND_FIRST_LAZY_EXACT_REPLAY.json',
        'C887_DIRECT_SHARED_LAZY_READER_ACTUAL_ATTACHMENT.json',
        'C887_WHOLE_HEIGHT_BOUND_STATE_BINDING.json', 'C_HEIGHT_EXCLUSION_CONSEQUENCES_BINDING.json',
        'c887_whole_height_bound_rows.py', 'independent_c887_whole_height_bound_rows.py',
    ]
    selected = {DIRECT/name for name in direct_names}
    for name in ('C_AND_CB_LAZY_EXACT_REPLAY_INDEPENDENT_REVIEW', 'C887_DIRECT_SHARED_SEARCH_V3_INDEPENDENT_REVIEW'):
        binding = WORK/'b_work'/(name+'.json')
        add_sources_from_binding(selected, binding)
        selected.add(WORK/'b_work'/(name+'.md'))
    for name in ('cb882_shared_height_bounds_runtime.py', 'cb882_whole_height_bound_rows.py',
                 'independent_cb882_whole_height_bound_rows.py', 'CB882_WHOLE_HEIGHT_BOUND_STATE_BINDING.json',
                 'CB882_WHOLE_HEIGHT_BOUND_STATE_HAND_PROOF.md', 'CB882_WHOLE_HEIGHT_BOUND_EXACT_CONTROLS.json',
                 'SOURCE_FREEZE.json'):
        selected.add(CB/name)
    fixtures = [DIRECT/'cb882_component1_direct_shared_bound_round', DIRECT/'c887_original_direct_shared_bound_round_fixture']
    for folder in fixtures:
        selected.update(folder/name for name in ('manifest.json', 'node_00000.json', 'PREVIOUS_COMPLETE_MANIFEST.json'))
    gates = [gate(DIRECT/'CB882_DIRECT_SHARED_BOUND_FIRST_LAZY_EXACT_REPLAY.json', fixtures[0],
        'Cb882 component1 direct bound round under lazy replay',
        dict(status='PASS_PARTIAL_CB882_HEIGHT_COMPONENT_TREE', nodes=1, rounds=1, deductions=158,
             printed_rows_checked=158, open_leaves=1, complete=False,
             whole_original_height_bound_state_row_occurrences_checked=158,
             node_payloads_replayed_lazily=True, numerical_producer_imported=False), component=1),
        gate(DIRECT/'C887_DIRECT_SHARED_BOUND_FIRST_LAZY_EXACT_REPLAY.json', fixtures[1],
        'C887 unsplit original direct bound round under lazy replay',
        dict(status='PASS_PARTIAL_WHOLE_ORIGINAL_C887_COVER', nodes=1, rounds=4, deductions=390,
             printed_rows_checked=532, excluded_leaf_domains=0,
             whole_original_height_bound_state_row_occurrences_checked=181,
             node_payloads_replayed_lazily=True, numerical_producer_imported=False))]
    h = dict(kind='direct_shared_bounds_and_C_lazy_readers', actual_native_gates=gates,
        cb_eager_report=native_member(DIRECT/'CB882_DIRECT_SHARED_BOUND_FIRST_EXACT_REPLAY.json'),
        cb_comparison_attachment=native_member(DIRECT/'CB882_DIRECT_SHARED_LAZY_READER_ACTUAL_ATTACHMENT.json'),
        original_statuses={'negative-b882d8ade0cf9ea0':'OPEN', 'negative-887236b78100baf3':'OPEN'},
        historical_pending_flags_retained_without_editing_sources=True,
        current_gate_supersedes_historical_C_lazy_pending_flag=True)
    direct_readme = '''# Direct shared bounds and bounded-memory C readers: native checkpoint\n\n**Native exact evidence and source preservation only. This is not a self-contained cold proof. It closes no original cell or mask.**\n\nThe generic helper copies already certified original-variable inequalities into the existing exact bound-round schema. It requires an explicit source-prefix allow-list, the ordinary objective identity, multiplier2^40, zero residual, the ordinary rational rounding grid and the existing frame/interval propagation. Source applicability must already hold for the untouched caller. The precheck is a discovery shortcut and proves no inequality. The composition wrapper preserves completed rounds and checkpoints before a fresh numerical phase.\n\nThe saved Cb882 component1 fixture has one OPEN domain:158 direct deductions and158 weighted source rows, all replayed through the lazy reader. Its listed mathematical/coverage fields exactly match the earlier eager replay. The saved C887 fixture is one unsplit OPEN original domain: three existing rounds plus181 direct deductions, giving four rounds,390 deductions and532 checked rows. Its181 shared-bound occurrences, whole-root source, complete DG8 union and archived height exclusion were freshly replayed. Numerical solvers were not used to create either direct round.\n\nBoth lazy readers change payload storage only. Their complete closed4/8/2 covers, sibling visits, child-state construction, visited-set equality and final source rehashes remain in the independently reviewed logic. The earlier review's pending-C-use flag is historical; the included actual C887 receipt records its later PASS. Frozen review/control bytes have not been edited.\n\n`INPUT_MANIFEST.json` pins every bundled byte. `SOURCE_PROVENANCE.json` identifies original files; larger immutable JSON records are hardlinked locally and must remain read-only. `DEPENDENCIES.json` pins referenced prerequisites, published commits/archive digests and any unbundled native files. Published byte-hash matches are availability evidence, not an automatic path relocation. The earlier archives, full original ancestry and all omitted prerequisites are not duplicated here. Original absolute paths inside code/records remain unchanged.\n\nRun the bundled `native/ac_work/verify_native_checkpoint_inventory.py CHECKPOINT --output OUTSIDE_JSON` only for a byte/header audit. It does not repeat weighted arithmetic, download archives, or establish closure. A future independent proof replay requires the full frozen dependencies and reviewed transport. No Lean, Lake, CI or optimizer is run during checkpoint creation.\n'''
    summaries = [write_package('direct_shared_bounds_and_C_lazy_readers_native_v1', selected,
        ['A_open_base', 'C_height_delta'], h, direct_readme)]
    a3_binding = DIRECT/'A_C744_COMPONENT3_POST_A1_BOUND_SOURCE_FREEZE.json'
    selected = {a3_binding}
    add_sources_from_binding(selected, a3_binding)
    selected.update({DIRECT/'A_C744_COMPONENT3_SHARED_BOUND_STATE_BINDING.json',
                     DIRECT/'A_C744_COMPONENT1_CLOSED_CONSEQUENCE_BINDING.json'})
    for name in ('A_C744_POST_A1_BOUNDS_ROOT_DESIGN_REVIEW.json', 'A_C744_POST_A1_BOUNDS_ROOT_DESIGN_REVIEW.md',
                 'A_C744_COMPONENT3_FIRST_POST_A1_BOUND_EXACT_REPLAY.json',
                 'resume_a_component3_post_a1_bounds_round_tree_v11.py'):
        selected.add(WORK/'d_work'/name)
    fixture = WORK/'d_work/A_c744_component3_post_a1_bound_whole_probe'
    selected.update(fixture/name for name in ('manifest.json', 'node_00000.json', 'PREVIOUS_COMPLETE_MANIFEST.json'))
    gates = [gate(WORK/'d_work/A_C744_COMPONENT3_FIRST_POST_A1_BOUND_EXACT_REPLAY.json', fixture,
        'A c744 component3 first weighted POST-A1 interval row use',
        dict(status='PASS_PARTIAL_TWO_LINK_COMPLEMENT_TREE', nodes=1, rounds=5, deductions=546,
             printed_rows_checked=1245, open_leaves=1, component3_post_a1_bound_rows_checked=39,
             component3_post_a1_bounds_valid_on_whole_original=False,
             node_payloads_replayed_lazily=True, numerical_producer_imported=False), component=3)]
    h = dict(kind='A_c744_component3_post_A1_conditional_bound_rows', component=3,
        valid_on_whole_original=False, actual_native_gates=gates,
        original_status='OPEN', component_status='OPEN', rows_in_conditional_family=414,
        source_freeze_pending_flag_is_historical=True, first_weighted_use_now_passed=True,
        complete_A1_source_is_separately_published=True)
    a3_readme = '''# A c744 component3 POST-A1 bounds: native checkpoint\n\n**This is conditional necessary-bound progress, not a complete original or a self-contained cold proof. New original and mask credit are both zero.**\n\nThe414-row family is valid only on the identical component3 closed domain of original positive-c744bc031d40ee64. It is not valid on the whole original or on components0,1,2,4. It transports original-variable interval consequences of a freshly replayed unsplit component3 source after the independently completed component1 exclusion. No source-child SAT choice, auxiliary interval or conditional predicate is imported into another domain. Caller/component/path/closed-row checks precede use.\n\nThe frozen literal controls and root design review are included. The actual native first-use record remains OPEN: one unsplit domain, five rounds,546 exact deductions and1245 checked premises, including39 weighted POST-A1 rows. Its full source dependencies, including complete A1 arithmetic, were replayed by the saved native gate. The source-freeze flag saying first use was pending is historical; its bytes remain unchanged and the later native PASS is included separately.\n\nThe complete component1 proof and original base are already published at the exact commits and archive hashes in `DEPENDENCIES.json`; their large payloads are not copied here. All referenced unbundled native prerequisites are listed explicitly. The record, native report, source code and bindings retain their exact bytes and original path strings. Larger frozen JSON files are hardlinked locally and must remain read-only.\n\n`INPUT_MANIFEST.json` and the bundled `native/ac_work/verify_native_checkpoint_inventory.py` provide a read-only byte/header audit only. They do not replay weighted arithmetic or establish portability. A fresh cold proof still requires full dependency reconstruction and the separately reviewed transport. No live A3 or C frontier is included or modified, no register status is refreshed, and no Lean, Lake, CI, optimizer or full proof rerun is part of this checkpoint.\n'''
    summaries.append(write_package('A_c744_component3_POST_A1_bounds_native_v1', selected,
        ['A_open_base', 'complete_A1_delta'], h, a3_readme))
    dump(OUT/'PREPARED_CHECKPOINTS.json', dict(status='PREPARED_NATIVE_ONLY_SOURCE_EVIDENCE_CHECKPOINTS',
        checkpoints=summaries, builder_sha256=sha(__file__), inventory_checker_sha256=sha(VERIFY),
        archive_created=False, full_proof_replayed=False, repository_or_index_edited=False,
        new_original_cells=0, new_masks=0))
    print(json.dumps(summaries, indent=2))


if __name__ == '__main__':
    main()
