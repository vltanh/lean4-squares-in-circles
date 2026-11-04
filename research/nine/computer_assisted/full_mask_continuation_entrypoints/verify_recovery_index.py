"""Verify recovered immutable source bytes and the two full boundary packets."""
from pathlib import Path
import argparse
import hashlib
import json


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--directory', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    home = args.directory.resolve()
    index_path = home/'SOURCE_BINDINGS.json'
    index_bytes = index_path.read_bytes()
    index = json.loads(index_bytes)
    assert index['schema'] == 'n9_other_mask_entrypoint_recovery_index_v1'
    assert index['immutable_head'] == '8ac1db9d311ab0319105cd35ce46d2b002216330'
    assert index['new_mask_closures'] == index['new_original_cell_closures'] == 0
    assert index['full_mask_solver_called'] is False
    assert index['strict_radius_target_unchanged'] is True
    checked = {}
    for name, source in index['recovered_files'].items():
        assert Path(name).name == name
        data = (home/name).read_bytes()
        assert len(data) == source['bytes'] and sha(data) == source['sha256']
        blob = b'blob '+str(len(data)).encode()+b'\0'+data
        assert hashlib.sha1(blob).hexdigest() == source['git_blob_sha1']
        checked[name] = sha(data)
    for name, digest in index['local_outputs_sha256'].items():
        assert Path(name).name == name
        assert sha((home/name).read_bytes()) == digest
        checked[name] = digest
    packets = [
        ('four_full_nine_mask_closed_q_boundary_manifest.json',
         'four_full_nine_mask_closed_q_boundary_witnesses/four_mask_closed_q_boundary'),
        ('mask_11100_full_nine_closed_q_boundary_manifest.json',
         'mask_11100_full_nine_closed_q_boundary/mask_11100_closed_q_boundary'),
    ]
    member_count = 0
    for name, folder in packets:
        manifest = json.loads((home/name).read_text())
        archive = home/manifest['archive']
        assert sha(archive.read_bytes()) == manifest['archive_sha256']
        for relative, digest in manifest['archive_members'].items():
            target = home/folder/relative
            assert target.resolve().is_relative_to(home/folder)
            assert sha(target.read_bytes()) == digest
            member_count += 1
    assert index_path.read_bytes() == index_bytes
    result = dict(
        status='PASS_IMMUTABLE_RECOVERY_INDEX',
        source_files=len(index['recovered_files']),
        extracted_boundary_members=member_count,
        local_outputs=len(index['local_outputs_sha256']),
        index_sha256=sha(index_bytes),
        checker_sha256=sha(Path(__file__).read_bytes()),
        new_mask_closures=0,
        new_original_cell_closures=0,
        scope='Source recovery integrity; exact finite predicates have separate fresh replay reports.',
    )
    if args.output:
        assert not args.output.exists()
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
