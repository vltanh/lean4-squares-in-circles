#!/usr/bin/env python3
"""Bind a completed raw arithmetic replay to its identical gzip artifact.

This performs no new arithmetic replay. It preserves the raw replay and
proves that the delivered gzip expands to exactly the already replayed
JSON bytes. The compressed artifact is independently replayable by the
normal verifier wrapper without this utility.
"""
from pathlib import Path
import gzip,hashlib,json

HERE=Path(__file__).resolve().parent
REPORT=HERE/'two_shoulder_mainheight_cover_independent_exact_replay.json'
PACKED=HERE/'two_shoulder_mainheight_cover.json.gz'
IDENTITY=HERE/'two_shoulder_mainheight_gzip_identity.json'


def main():
    original=REPORT.read_bytes();record=json.loads(original)
    assert record['complete']is True and record['proof_status']=='independent_exact_replay_passed'
    assert record['certificate_file']=='two_shoulder_mainheight_cover.json'
    identity=json.loads(IDENTITY.read_text());assert identity['result']=='PASS'
    packed=PACKED.read_bytes();unpacked=gzip.decompress(packed)
    packed_hash=hashlib.sha256(packed).hexdigest();json_hash=hashlib.sha256(unpacked).hexdigest()
    assert packed_hash==identity['gzip_sha256']
    assert json_hash==identity['raw_json_sha256']==identity['decompressed_json_sha256']
    assert json_hash==record['certificate_sha256']==record['decompressed_json_sha256']
    assert len(unpacked)==record['decompressed_json_bytes']==identity['decompressed_json_bytes']
    saved=HERE/'two_shoulder_mainheight_raw_json_independent_exact_replay.json'
    saved.write_bytes(original)
    record.update(certificate_file=PACKED.name,certificate_encoding='gzip',certificate_sha256=packed_hash)
    record['lossless_packaging']={
        'status':'gzip decompression is byte-for-byte identical to the completed raw arithmetic replay',
        'arithmetic_replayed_again':False,
        'original_arithmetic_replay_report':saved.name,
        'original_arithmetic_replay_report_sha256':hashlib.sha256(original).hexdigest(),
        'replayed_json_sha256':json_hash,
        'identity_report':IDENTITY.name,
        'identity_report_sha256':hashlib.sha256(IDENTITY.read_bytes()).hexdigest(),
        'binding_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    REPORT.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'result':'PASS','gzip_sha256':packed_hash,'replayed_json_sha256':json_hash,
                      'raw_replay_preserved':saved.name,'delivered_replay_report':REPORT.name}),flush=True)


if __name__=='__main__':main()
