#!/usr/bin/env python3
"""Archive a cold-replayed complete D821 proof without a raw tar intermediate.

The mathematical input manifest remains byte-identical.  The two fresh audit
files and this release manifest are outer release evidence, added only after
the independent portable replay has finished successfully.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import tarfile
import time

TARGET = 'positive-821c9a2debeed0aa'
ORIGINAL_PATH = [
    ['angle', 3, 1],
    ['angle_cut', [0, '0'], 1],
    ['alternate_four_escape', [1, 7], [3]],
]


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def literal_file(root, name):
    relative = Path(name)
    assert not relative.is_absolute() and '..' not in relative.parts
    path = root / relative
    assert not path.is_symlink()
    assert path.resolve().is_relative_to(root)
    assert path.is_file()
    return path


def check_complete(report):
    assert report['schema'] == 'D821_complete_grafted_original_exact_proof_v1'
    assert report['status'] == 'PASS_COMPLETE_ORIGINAL_CELL'
    assert report['original_id'] == TARGET
    assert report['original_path'] == ORIGINAL_PATH
    assert report['mask'] == '001/00'
    assert report['whole_original_proved'] is True
    assert report['complete_closed_complement_domains'] == 5
    assert report['all_nine_original_frames'] is True
    assert report['original_corners'] == report['original_physical_pairs'] == 36
    assert report['original_center_cones_preserved'] == 5
    assert report['original_actual_links'] == ['AB', 'BC', 'EF', 'FG']
    assert report['original_strict_weak_bits'] == ['CD']
    assert report['closed_Q_face_excluded_by_strict_CD_equality_blocker'] is True
    assert report['proposed_original_cell_credit'] == 1
    assert report['whole_mask_credit'] == 0
    assert report['fixed_ledger_not_modified'] is True
    assert report['numerical_producer_imported'] is False
    assert report['numerical_fields_used'] is False
    assert [item['component'] for item in report['component_audits']] == list(range(5))
    assert all(item['complete'] is True for item in report['component_audits'])
    assert all(item['complete_after_grafting'] is True for item in report['grafted_cover_nodes'])
    scalar = report['accepted_two_link_theorem']
    assert scalar['fresh_scalar_domains'] == 28
    assert scalar['fresh_scalar_leaves'] == 103
    assert scalar['fresh_scalar_coefficients'] == 12875


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('packet', type=Path)
    parser.add_argument('portable_replay', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    assert __debug__, 'Release gates require assertions.'
    started = time.monotonic()
    packet = args.packet.resolve()
    replay_folder = args.portable_replay.resolve()
    output = args.output.resolve()
    assert packet.is_dir() and replay_folder.is_dir()
    assert not replay_folder.is_relative_to(packet)
    assert not output.is_relative_to(packet)
    assert not output.exists()

    input_manifest = packet / 'INPUT_MANIFEST.json'
    input_hash = sha(input_manifest)
    inventory = json.loads(input_manifest.read_text())
    assert inventory['schema'] == 'D821_portable_frozen_inputs_v1'
    assert inventory['external_workspace_reads_forbidden'] is True
    assert inventory['numerical_imports_forbidden'] is True
    assert inventory['unchanged_strict_complete_original_assembler_required'] is True
    for name, digest in inventory['files'].items():
        assert sha(literal_file(packet, name)) == digest, ('changed frozen input', name)

    info = json.loads((packet / 'ORIGINAL_PROOF.json').read_text())
    assert info['schema'] == 'D821_portable_unchanged_proof_inputs_v1'
    assert info['mode'] == 'COMPLETE_ORIGINAL'
    assert info['original_id'] == TARGET and info['mask'] == '001/00'
    assert info['original_frames'] == 9
    assert info['original_corners'] == info['original_pairs'] == 36
    assert info['original_cones'] == 5
    assert info['original_actual_links'] == ['AB', 'BC', 'EF', 'FG']
    assert info['original_strict_weak_links'] == ['CD']
    assert info['mathematical_sources_unchanged'] is True
    assert info['aliases_are_filename_transport_only'] is True
    assert info['new_masks'] == 0
    bindings = json.loads((packet / 'BINDINGS.json').read_text())['files']

    def original_file(logical, digest):
        entry = bindings[logical]
        assert entry['sha256'] == digest == inventory['files'][entry['path']]
        path = literal_file(packet, entry['path'])
        assert sha(path) == digest
        return path

    plan_path = original_file(info['complete_plan'], info['complete_plan_sha256'])
    plan = json.loads(plan_path.read_text())
    assert plan['schema'] == 'D821_grafted_five_complement_complete_original_plan_v1'
    assert plan['original_id'] == TARGET
    native_path = original_file(info['original_report'], info['original_report_sha256'])
    native = json.loads(native_path.read_text())
    check_complete(native)
    assert native['plan_sha256'] == info['complete_plan_sha256']

    table_ref = info['terminal_table']
    table_path = original_file(table_ref['path'], table_ref['sha256'])
    table = json.loads(table_path.read_text())
    assert table['schema'] == 'D821_complete_literal_terminal_table_v1'
    assert table['status'] == 'RENDERED_FROM_PASS_COMPLETE_ORIGINAL_CELL'
    assert table['exact_report'] == dict(path=info['original_report'], sha256=info['original_report_sha256'])
    assert table['new_original_cell_credit_from_renderer'] == table['new_masks'] == 0
    assert table['tree_count'] == len(native['grafted_cover_nodes'])
    assert table['node_count'] == len(table['nodes'])
    native_audits = {item['manifest_sha256']: item for item in native['exact_tree_reports'].values()}
    covered_digests = {item['manifest']['sha256'] for item in native['grafted_cover_nodes']}
    assert len(covered_digests) == table['tree_count']
    assert table['node_count'] == sum(len(native_audits[digest]['node_audits']) for digest in covered_digests)
    assert sha(packet / 'COMPLETE_TERMINAL_TABLE.json') == table_ref['sha256']
    assert sha(packet / 'COMPLETE_TERMINAL_TABLE.md') == info['terminal_table_markdown']['sha256']

    receipt_path = replay_folder / 'PORTABLE_RECEIPT.json'
    report_path = replay_folder / 'COMPLETE_ORIGINAL_REPLAY.json'
    receipt = json.loads(receipt_path.read_text())
    assert receipt['status'] == 'PASS_FRESH_PORTABLE_COMPLETE_ORIGINAL_D821'
    assert receipt['original_id'] == TARGET
    assert receipt['packet_manifest_sha256'] == input_hash
    assert receipt['exact_report_sha256'] == sha(report_path)
    assert receipt['new_original_cells'] == 1 and receipt['new_masks'] == 0
    assert receipt['whole_original_coverage_not_claimed'] is False
    for name in ('exact_mathematical_sources_unchanged', 'external_workspace_reads_forbidden',
                 'numerical_imports_forbidden', 'all_inputs_rehashed_at_completion'):
        assert receipt[name] is True
    assert receipt['lean_lake_ci_run'] is False
    fresh = json.loads(report_path.read_text())
    check_complete(fresh)
    assert fresh['plan_sha256'] == native['plan_sha256']
    assert len(fresh['grafted_cover_nodes']) == len(native['grafted_cover_nodes'])
    assert {item['manifest']['sha256'] for item in fresh['grafted_cover_nodes']} == covered_digests
    fresh_audits = {item['manifest_sha256']: item for item in fresh['exact_tree_reports'].values()}
    assert set(fresh_audits) == set(native_audits)
    assert sum(len(fresh_audits[digest]['node_audits']) for digest in covered_digests) == table['node_count']

    # These are new outer audit files, never replacements for frozen inputs.
    audit_folder = packet / 'release_audits'
    audit_folder.mkdir(exist_ok=False)
    for name in ('PORTABLE_RECEIPT.json', 'COMPLETE_ORIGINAL_REPLAY.json'):
        source = replay_folder / name
        destination = audit_folder / ('FRESH_' + name)
        destination.write_bytes(source.read_bytes())
        assert sha(source) == sha(destination)
    for path in packet.rglob('*'):
        assert not path.is_symlink(), ('symlink cannot be released', str(path))
    sources = {str(path.relative_to(packet)): sha(path)
               for path in sorted(packet.rglob('*')) if path.is_file()}
    assert 'RELEASE_MANIFEST.json' not in sources
    release = dict(schema='D821_complete_original_release_v1', original_id=TARGET,
                   original_path=ORIGINAL_PATH, mask='001/00', files=sources,
                   input_manifest_sha256=input_hash,
                   portable_receipt_sha256=sha(audit_folder / 'FRESH_PORTABLE_RECEIPT.json'),
                   native_exact_report_sha256=info['original_report_sha256'],
                   fresh_exact_report_sha256=sha(report_path),
                   complete_original=True, complete_closed_complement_domains=5,
                   tree_count=table['tree_count'], node_count=table['node_count'],
                   original_frames=9, original_corners=36, original_pairs=36, original_cones=5,
                   new_original_cell_credit=1, new_mask_credit=0,
                   fixed_ledger_not_modified=True, mathematical_inputs_unchanged=True,
                   outer_archiver_sha256=sha(__file__))
    dump(packet / 'RELEASE_MANIFEST.json', release)
    expected = dict(sources)
    expected['RELEASE_MANIFEST.json'] = sha(packet / 'RELEASE_MANIFEST.json')

    output.mkdir(parents=True, exist_ok=False)
    temporary = output / (packet.name + '.tar.xz.tmp')
    final = output / (packet.name + '.tar.xz')
    with temporary.open('xb') as stream:
        producer = subprocess.Popen([
            'tar', '--sort=name', '--mtime=@0', '--owner=0', '--group=0', '--numeric-owner',
            '--format=gnu', '-cf', '-', '-C', str(packet.parent), packet.name,
        ], stdout=subprocess.PIPE)
        compressor = None
        try:
            compressor = subprocess.Popen(['xz', '-T1', '-1', '-c'], stdin=producer.stdout, stdout=stream)
            producer.stdout.close()
            compressed_status = compressor.wait()
            archive_status = producer.wait()
            assert compressed_status == archive_status == 0, (
                'streaming archive failure', archive_status, compressed_status)
        finally:
            for child in (compressor, producer):
                if child is not None and child.poll() is None:
                    child.terminate()
                    child.wait()
        stream.flush()
        os.fsync(stream.fileno())
    subprocess.run(['xz', '-t', str(temporary)], check=True)
    found = {}
    with tarfile.open(temporary, 'r|xz') as archive:
        for member in archive:
            if member.isdir():
                continue
            assert member.isfile(), ('unexpected archive member type', member.name)
            relative = Path(member.name).relative_to(packet.name)
            name = str(relative)
            assert '..' not in relative.parts and name in expected and name not in found
            stream = archive.extractfile(member)
            digest = hashlib.sha256()
            for block in iter(lambda: stream.read(1024 * 1024), b''):
                digest.update(block)
            assert digest.hexdigest() == expected[name], ('archive member mismatch', name)
            found[name] = digest.hexdigest()
    assert set(found) == set(expected)
    assert sha(input_manifest) == input_hash
    for name, digest in inventory['files'].items():
        assert sha(literal_file(packet, name)) == digest, ('frozen input changed during archive', name)
    os.replace(temporary, final)

    parts = []
    with final.open('rb') as stream:
        index = 1
        while True:
            block = stream.read(8 * 1024 * 1024)
            if not block:
                break
            part = output / (final.name + f'.part{index:03d}')
            with part.open('xb') as target:
                target.write(block)
                target.flush()
                os.fsync(target.fileno())
            parts.append(dict(file=part.name, bytes=len(block), sha256=hashlib.sha256(block).hexdigest()))
            index += 1
    ready = dict(schema='D821_complete_original_archive_parts_v1', original_id=TARGET,
                 original_path=ORIGINAL_PATH, mask='001/00', archive=final.name,
                 archive_bytes=final.stat().st_size, archive_sha256=sha(final), parts=parts,
                 release_manifest_sha256=expected['RELEASE_MANIFEST.json'],
                 packet_input_manifest_sha256=input_hash, all_archive_members_verified=len(found),
                 xz_integrity_pass=True, all_member_hashes_match=True,
                 fresh_portable_replay_pass=True, complete_original=True,
                 complete_closed_complement_domains=5, tree_count=table['tree_count'],
                 node_count=table['node_count'], new_original_cell_credit=1, new_mask_credit=0,
                 fixed_ledger_not_modified=True, streaming_compression=True,
                 raw_tar_intermediate_created=False, outer_archiver_sha256=sha(__file__),
                 seconds=time.monotonic() - started)
    dump(output / 'ARCHIVE_READY.json', ready)
    print(json.dumps(ready, indent=2), flush=True)


if __name__ == '__main__':
    main()
