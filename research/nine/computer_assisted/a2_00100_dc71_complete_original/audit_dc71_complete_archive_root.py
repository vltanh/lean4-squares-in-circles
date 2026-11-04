from pathlib import Path, PurePosixPath
from hashlib import sha256
from datetime import datetime, timezone
import gzip, json, lzma, tarfile, time

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'a_family/other_masks/dc71_original_assembly'
DOC = BASE / 'complete_original_documents_v2'

def digest(path):
    h = sha256()
    with Path(path).open('rb') as stream:
        while block := stream.read(1 << 20):
            h.update(block)
    return h.hexdigest()

def main():
    started = time.monotonic()
    receipt_path = DOC / 'PORTABLE_ARCHIVE_BUILD_RECEIPT.json'
    assert digest(receipt_path) == 'c27a667fb57dfc7b28704807daa7351e4d213f8fe865eae286f283dde3c6d8af'
    receipt = json.loads(receipt_path.read_text())
    outer_path = DOC / 'OUTER_ARCHIVE_MANIFEST.json'
    assert digest(outer_path) == 'dfceed3e71c4a30b3caa4a89c10fe7e6bdf3804fb32a917b229ac9cbbaaedf28'
    outer = json.loads(outer_path.read_text())
    expected = dict(outer['files'])
    expected['OUTER_ARCHIVE_MANIFEST.json'] = digest(outer_path)
    assert len(expected) == 1497
    assert outer['complete_fixed_I'] == 16 and outer['open_I'] == [] and outer['open_H'] == 0
    assert outer['original_id'] == 'positive-c71dc2feef1abb0b'
    assert outer['original_path'] == [['angle', 3, 1], ['angle_cut', [0, '0'], 1], ['alternate_four_escape', [1, 7], [2]]]
    assert outer['frozen_assembly_inputs'] == 1459
    archive = Path(receipt['archive'])
    assert archive == BASE / 'dc71_complete_original.tar.xz'
    assert archive.stat().st_size == 281913000
    assert digest(archive) == '37745648b17e0e3e68abdba52505d1a9373d44fc857d23a96a9f9e7e3f9597cd'
    prefix = 'dc71_complete_original/'
    checked, regular, links, total = {}, 0, 0, 0
    with lzma.open(archive, 'rb') as stream:
        with tarfile.open(fileobj=stream, mode='r|') as tar:
            for item in tar:
                path = PurePosixPath(item.name)
                assert not path.is_absolute() and '..' not in path.parts
                assert item.name.startswith(prefix)
                name = item.name[len(prefix):]
                assert name in expected and name not in checked
                assert item.uid == item.gid == item.mtime == 0
                assert item.uname == item.gname == '' and item.mode == 0o644
                if item.isfile():
                    h, count = sha256(), 0
                    payload = tar.extractfile(item)
                    while block := payload.read(1 << 20):
                        h.update(block); count += len(block)
                    assert count == item.size
                    value = h.hexdigest()
                    regular += 1; total += count
                else:
                    assert item.islnk() and item.linkname.startswith(prefix)
                    target = item.linkname[len(prefix):]
                    assert target in checked and '..' not in PurePosixPath(target).parts
                    value = checked[target]
                    links += 1
                assert value == expected[name], name
                checked[name] = value
        # Consume the remaining XZ stream, forcing its checksum and footer check.
        while stream.read(1 << 20):
            pass
    assert checked == expected
    assert (regular, links, total) == (875, 622, 2328466253)
    assert expected['ASSEMBLY_MANIFEST.json'] == '3b67d3be76f0292d95cd8011ae4a62c59ac89e0f24396042d0465de818f7af49'
    assert expected['HAND_PROOF.md'] == 'ce76084e4dc457e9ba58852616fac12ee98f53a6016300b50c99c817878f4855'
    assert expected['COVER_TABLE.json'] == '6b14dfed5dafca9522d9cba4b61c4271da3d45e61df3115a7b031ea2392e11da'
    assert expected['independent_complete_reviews/DC71_COMPLETE_ORIGINAL_ROOT_HAND_TABLE_REVIEW_V3.json'] == 'eb277774cb1c17b9cc67c29b61bed9a40d2f9358abd3764803350a0d418d6ad1'
    assert expected['independent_complete_reviews/DC71_COMPLETE_ORIGINAL_HAND_TABLE_SOURCE_REVIEW_V2.json'] == '5a703eb3227ee27b9330607854817aa1008a28d2edc3e4d5dd677ef49fef9eb2'
    for name, value in outer['outer_physical_theorem_dependencies'].items():
        assert expected[name] == value
    gz = DOC / 'COMPLETE_REPLAY.json.gz'
    assert digest(gz) == 'b877e50773605859962e40f3db664181f94f1b5b251e3d985278a2f48e5c91f9'
    h, count = sha256(), 0
    with gzip.open(gz, 'rb') as stream:
        while block := stream.read(1 << 20):
            h.update(block); count += len(block)
    assert count == 35179712 and h.hexdigest() == '3b52ef8d60de895ea9db0277a5d9f840acc7f265cc85990ba6cb3d44be474548'
    output = dict(schema='Dc71_complete_original_root_archive_audit_v1', status='PASS_ALL_MEMBERS_HARDLINKS_XZ_FOOTER_AND_GZIP_BYTE_IDENTITY',
        checked_at=datetime.now(timezone.utc).isoformat(), archive=str(archive), archive_bytes=archive.stat().st_size,
        archive_sha256=digest(archive), archive_build_receipt_sha256=digest(receipt_path),
        outer_manifest_sha256=digest(outer_path), members=1497, regular_payloads=regular, prior_internal_hardlinks=links,
        unique_payload_bytes=total, complete_expected_member_set=True, all_member_hashes_match=True,
        all_five_physical_theorem_dependencies_bound=True, both_final_independent_reviews_bound=True,
        compressed_report_bytes_identical=True, repeated_weighted_replay_claimed=False,
        complete_original_parent=True, new_original_cells=1, new_masks=0, seconds=time.monotonic()-started)
    out = ROOT / 'DC71_COMPLETE_ORIGINAL_ROOT_ARCHIVE_AUDIT.json'
    assert not out.exists()
    out.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps(output), flush=True)
    print('REPORT_SHA256', digest(out), flush=True)

if __name__ == '__main__':
    main()
