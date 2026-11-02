#!/usr/bin/env python3
"""Losslessly package and bind the completed raw ordering replay.

The gzip is written to a temporary file, verified by full decompression,
and atomically renamed. No mathematical inequality is replayed here.
The delivered gzip remains directly replayable by the normal checker.
"""
from pathlib import Path
import gzip
import hashlib
import json

HERE = Path(__file__).resolve().parent
RAW = HERE / 'upper_extra_order_cover.json'
PACKED = HERE / 'upper_extra_order_cover.json.gz'
TEMP = HERE / 'upper_extra_order_cover.json.gz.exact_replay_tmp'
REPORT = HERE / 'upper_extra_order_cover_independent_exact_replay.json'
IDENTITY = HERE / 'upper_extra_order_gzip_identity.json'


def hash_stream(stream):
    digest, size = hashlib.sha256(), 0
    while True:
        block = stream.read(1 << 20)
        if not block:
            return digest.hexdigest(), size
        digest.update(block)
        size += len(block)


def main():
    original = REPORT.read_bytes()
    record = json.loads(original)
    assert record['complete'] is True and record['proof_status'] == 'independent_exact_replay_passed'
    assert record['certificate_file'] == RAW.name
    assert not PACKED.exists(), 'Do not overwrite another completed packager.'
    raw_digest, raw_size = hashlib.sha256(), 0
    with RAW.open('rb') as src, TEMP.open('wb') as dst:
        with gzip.GzipFile(fileobj=dst, filename='', mode='wb', compresslevel=9, mtime=0) as packed:
            while True:
                block = src.read(1 << 20)
                if not block:
                    break
                raw_digest.update(block)
                raw_size += len(block)
                packed.write(block)
    raw_hash = raw_digest.hexdigest()
    assert raw_hash == record['certificate_sha256'] == record['decompressed_json_sha256']
    assert raw_size == record['decompressed_json_bytes']
    with TEMP.open('rb') as stream:
        compressed_hash, compressed_size = hash_stream(stream)
    with gzip.open(TEMP, 'rb') as stream:
        restored_hash, restored_size = hash_stream(stream)
    assert restored_hash == raw_hash and restored_size == raw_size
    with TEMP.open('rb') as stream:
        header = stream.read(10)
    assert header[:2] == b'\x1f\x8b' and int.from_bytes(header[4:8], 'little') == 0
    TEMP.replace(PACKED)
    identity = {
        'result': 'PASS', 'raw_json_file': RAW.name, 'gzip_file': PACKED.name,
        'raw_json_sha256': raw_hash, 'raw_json_bytes': raw_size,
        'gzip_sha256': compressed_hash, 'gzip_bytes': compressed_size,
        'decompressed_json_sha256': restored_hash, 'decompressed_json_bytes': restored_size,
        'gzip_mtime': 0, 'scope': 'byte identity only; completed arithmetic report is preserved separately',
        'packaging_source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    IDENTITY.write_text(json.dumps(identity, indent=2) + '\n')
    saved = HERE / 'upper_extra_order_raw_json_independent_exact_replay.json'
    saved.write_bytes(original)
    controls = HERE / 'upper_extra_order_rejection_controls.json'
    if controls.exists():
        (HERE / 'upper_extra_order_raw_json_rejection_controls.json').write_bytes(controls.read_bytes())
    record.update(certificate_file=PACKED.name, certificate_encoding='gzip',
                  certificate_sha256=compressed_hash)
    record['lossless_packaging'] = {
        'status': 'gzip decompression is byte-for-byte identical to the completed raw arithmetic replay',
        'arithmetic_replayed_again': False,
        'original_arithmetic_replay_report': saved.name,
        'original_arithmetic_replay_report_sha256': hashlib.sha256(original).hexdigest(),
        'replayed_json_sha256': raw_hash,
        'identity_report': IDENTITY.name,
        'identity_report_sha256': hashlib.sha256(IDENTITY.read_bytes()).hexdigest(),
        'packaging_source_sha256': identity['packaging_source_sha256'],
    }
    REPORT.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(identity, indent=2), flush=True)


if __name__ == '__main__':
    main()
