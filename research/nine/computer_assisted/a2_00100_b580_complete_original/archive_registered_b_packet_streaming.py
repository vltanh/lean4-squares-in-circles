#!/usr/bin/env python3
"""Stream a freshly replayed complete B packet into xz and verify every member."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,tarfile,time

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,v):p.write_text(json.dumps(v,indent=2)+'\n')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('packet',type=Path);ap.add_argument('portable_replay',type=Path);ap.add_argument('output',type=Path)
    a=ap.parse_args();packet=a.packet.resolve();started=time.monotonic()
    info=json.loads((packet/'ORIGINAL_PROOF.json').read_text());assert info['complete']is True and info['open_prototype']is False
    receipt=json.loads((a.portable_replay/'PORTABLE_RECEIPT.json').read_text())
    assert receipt['status']=='PASS_FRESH_PORTABLE_COMPLETE_REGISTERED_B_ORIGINAL'and receipt['complete']is True
    assert receipt['original_id']==info['original_id']
    assert receipt['packet_manifest_sha256']==sha(packet/'INPUT_MANIFEST.json')
    assert receipt['report_sha256']==sha(a.portable_replay/'COMPLETE_ORIGINAL_REPLAY.json')
    for name in('PORTABLE_RECEIPT.json','COMPLETE_ORIGINAL_REPLAY.json'):
        target=packet/'original_audits'/('FRESH_'+name);assert not target.exists()
        target.write_bytes((a.portable_replay/name).read_bytes())
    sources={str(p.relative_to(packet)):sha(p)for p in sorted(packet.rglob('*'))if p.is_file()}
    assert 'RELEASE_MANIFEST.json'not in sources
    dump(packet/'RELEASE_MANIFEST.json',dict(schema='complete_registered_B_original_release_v1',
        original_id=info['original_id'],files=sources,portable_receipt_sha256=sha(packet/'original_audits/FRESH_PORTABLE_RECEIPT.json'),
        prior_archive_sha256=info['prior_archive_sha256'],complete_original=True,new_mask_credit=0))
    expected=dict(sources);expected['RELEASE_MANIFEST.json']=sha(packet/'RELEASE_MANIFEST.json')
    a.output.mkdir(parents=True,exist_ok=False);temp=a.output/(packet.name+'.tar.xz.tmp');final=a.output/(packet.name+'.tar.xz')
    with temp.open('xb')as stream:
        producer=subprocess.Popen(['tar','--sort=name','--mtime=@0','--owner=0','--group=0','--numeric-owner','--format=gnu',
            '-cf','-','-C',str(packet.parent),packet.name],stdout=subprocess.PIPE)
        compressor=None
        try:
            compressor=subprocess.Popen(['xz','-T1','-6','-c'],stdin=producer.stdout,stdout=stream)
            producer.stdout.close()
            compressed_status=compressor.wait();archive_status=producer.wait()
            assert compressed_status==0 and archive_status==0,('streaming archive failure',archive_status,compressed_status)
        finally:
            for child in (compressor,producer):
                if child is not None and child.poll()is None:child.terminate();child.wait()
        stream.flush();os.fsync(stream.fileno())
    subprocess.run(['xz','-t',str(temp)],check=True)
    found={}
    with tarfile.open(temp,'r|xz')as archive:
        for member in archive:
            if member.isdir():continue
            assert member.isfile(),('unexpected member type',member.name)
            rel=Path(member.name).relative_to(packet.name);name=str(rel)
            assert '..'not in rel.parts and name in expected and name not in found
            stream=archive.extractfile(member);h=hashlib.sha256()
            for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
            assert h.hexdigest()==expected[name];found[name]=h.hexdigest()
    assert set(found)==set(expected);os.replace(temp,final)
    parts=[]
    with final.open('rb')as stream:
        k=1
        while True:
            block=stream.read(8*1024*1024)
            if not block:break
            p=a.output/(final.name+f'.part{k:03d}')
            with p.open('xb')as out:out.write(block);out.flush();os.fsync(out.fileno())
            parts.append(dict(file=p.name,bytes=len(block),sha256=hashlib.sha256(block).hexdigest()));k+=1
    report=dict(schema='complete_registered_B_original_archive_parts_v1',original_id=info['original_id'],
        archive=final.name,archive_bytes=final.stat().st_size,archive_sha256=sha(final),parts=parts,
        release_manifest_sha256=expected['RELEASE_MANIFEST.json'],all_archive_members_verified=len(found),
        xz_integrity_pass=True,all_member_hashes_match=True,prior_archive_sha256=info['prior_archive_sha256'],
        fresh_portable_replay_pass=True,streaming_compression=True,raw_tar_intermediate_created=False,
        outer_archiver_sha256=sha(__file__),seconds=time.monotonic()-started)
    dump(a.output/'ARCHIVE_READY.json',report);print(json.dumps(report,indent=2),flush=True)

if __name__=='__main__':main()
