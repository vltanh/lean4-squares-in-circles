#!/usr/bin/env python3
"""Losslessly package an already completed exact arithmetic replay.

No new arithmetic replay is claimed. The ordinary independent checker
can also replay the delivered gzip directly.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json

HERE = Path(__file__).resolve().parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('raw_certificate', type=Path)
    parser.add_argument('raw_replay_report', type=Path)
    args = parser.parse_args()
    raw = args.raw_certificate.read_bytes()
    original_report = args.raw_replay_report.read_bytes()
    report = json.loads(original_report)
    assert report['complete'] is True
    assert report['proof_status'] == 'independent_exact_replay_passed'
    assert digest(raw) == report['certificate_sha256'] == report['decompressed_json_sha256']
    assert len(raw) == report['decompressed_json_bytes']
    assert digest((HERE / 'verify_bad_upper_extra_floor_exact.cpp').read_bytes()) == report['checker_cpp_sha256']
    assert digest((HERE / 'verify_bad_upper_extra_floor_exact.py').read_bytes()) == report['checker_wrapper_sha256']
    packed = gzip.compress(raw, compresslevel=9, mtime=0)
    assert gzip.decompress(packed) == raw
    packed_path = HERE / 'bad_upper_extra_floor_cover.json.gz'
    packed_path.write_bytes(packed)
    original_path = HERE / 'bad_upper_extra_floor_raw_json_independent_exact_replay.json'
    original_path.write_bytes(original_report)
    identity = dict(
        result='PASS', scope='Lossless byte identity; complete arithmetic replay recorded separately',
        raw_json_file=args.raw_certificate.name, raw_json_sha256=digest(raw), raw_json_bytes=len(raw),
        gzip_file=packed_path.name, gzip_sha256=digest(packed), gzip_bytes=len(packed),
        decompressed_json_sha256=digest(gzip.decompress(packed)), decompressed_json_bytes=len(raw),
        gzip_mtime=0)
    identity_path = HERE / 'bad_upper_extra_floor_gzip_identity.json'
    identity_path.write_text(json.dumps(identity, indent=2) + '\n')
    report.update(certificate_file=packed_path.name, certificate_encoding='gzip', certificate_sha256=digest(packed))
    report['lossless_packaging'] = dict(
        status='Delivered gzip expands byte-for-byte to the completely replayed JSON',
        arithmetic_replayed_again=False,
        original_arithmetic_replay_report=original_path.name,
        original_arithmetic_replay_report_sha256=digest(original_report),
        replayed_json_sha256=digest(raw),
        identity_report=identity_path.name,
        identity_report_sha256=digest(identity_path.read_bytes()),
        binding_source_sha256=digest(Path(__file__).read_bytes()))
    report_path = HERE / 'bad_upper_extra_floor_cover_independent_exact_replay.json'
    report_path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(identity))


if __name__ == '__main__':
    main()
