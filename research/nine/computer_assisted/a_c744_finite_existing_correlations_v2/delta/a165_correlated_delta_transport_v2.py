#!/usr/bin/env python3
"""Deterministic regular-file A165 delta transport, with verified fresh extraction."""
if not __debug__:
    raise RuntimeError('I64 transport verification requires assertions.')
from pathlib import Path,PurePosixPath
import argparse,hashlib,io,json,lzma,os,tarfile

SCHEMA='A165_correlated_delta_regular_file_archive_v2'

def sha_bytes(data):return hashlib.sha256(data).hexdigest()
def sha(path):return sha_bytes(Path(path).read_bytes())
def canonical_name(name):
    assert isinstance(name,str)and name and '\\'not in name and '\x00'not in name
    p=PurePosixPath(name)
    assert not p.is_absolute()and all(x not in ('','.','..')for x in name.split('/'))
    assert str(p)==name
    return p

def validate_inventory(inv):
    assert inv['schema']==SCHEMA and inv['file_only']is True
    assert isinstance(inv['files'],dict)and inv['files']
    for name,entry in inv['files'].items():
        canonical_name(name)
        assert set(entry)=={'bytes','sha256'}
        assert type(entry['bytes'])is int and entry['bytes']>=0
        assert isinstance(entry['sha256'],str)and len(entry['sha256'])==64
        assert all(c in '0123456789abcdef'for c in entry['sha256'])
    assert inv['members']==len(inv['files'])
    assert inv['uncompressed_file_bytes']==sum(x['bytes']for x in inv['files'].values())

def validated_members(archive,inv):
    validate_inventory(inv)
    assert sha(archive)==inv['archive_sha256']
    assert Path(archive).stat().st_size==inv['archive_bytes']
    result={}
    with tarfile.open(archive,'r:xz')as stream:
        for member in stream:
            name=member.name;canonical_name(name)
            assert name in inv['files']and name not in result
            assert member.isfile()and not member.issym()and not member.islnk()
            assert member.mode==0o644 and member.uid==member.gid==0
            assert member.uname==member.gname==''and member.mtime==0
            assert not member.pax_headers and not member.linkname
            entry=inv['files'][name];assert member.size==entry['bytes']
            source=stream.extractfile(member);assert source is not None
            data=source.read(entry['bytes']+1)
            assert len(data)==entry['bytes']and sha_bytes(data)==entry['sha256']
            result[name]=data
    assert set(result)==set(inv['files'])
    # Reading the entire compressed stream checks the XZ trailer as well.
    with lzma.open(archive,'rb')as source:
        while source.read(1<<20):pass
    return result

def build(source,archive,inventory):
    source,archive,inventory=Path(source).resolve(),Path(archive).resolve(),Path(inventory).resolve()
    assert source.is_dir()and not archive.exists()and not inventory.exists()
    assert not archive.is_relative_to(source)and not inventory.is_relative_to(source)
    files={}
    for p in sorted(source.rglob('*')):
        assert not p.is_symlink()
        if p.is_dir():continue
        assert p.is_file()
        name=str(p.relative_to(source));canonical_name(name)
        data=p.read_bytes();files[name]=dict(bytes=len(data),sha256=sha_bytes(data))
    assert len(files)==44
    assert files['INPUT_MANIFEST.json']['sha256']=='f3778cf2b2a583cdce4bacb8691add8a7d14b1d5a6c1256d6b7d0965fb8b1781'
    with archive.open('xb')as raw:
        with lzma.LZMAFile(raw,'w',format=lzma.FORMAT_XZ,check=lzma.CHECK_CRC64,preset=1)as compressed:
            with tarfile.open(fileobj=compressed,mode='w|',format=tarfile.USTAR_FORMAT)as stream:
                for name,entry in files.items():
                    data=(source/name).read_bytes();assert len(data)==entry['bytes']and sha_bytes(data)==entry['sha256']
                    member=tarfile.TarInfo(name);member.size=len(data);member.mode=0o644
                    member.uid=member.gid=0;member.uname=member.gname='';member.mtime=0
                    stream.addfile(member,io.BytesIO(data))
        raw.flush();os.fsync(raw.fileno())
    inv=dict(schema=SCHEMA,file_only=True,compression='XZ CRC64 preset1',tar_format='USTAR',
        deterministic_order='lexicographically sorted relative regular-file paths',
        metadata=dict(mode='0644',uid=0,gid=0,uname='',gname='',mtime=0),
        archive_sha256=sha(archive),archive_bytes=archive.stat().st_size,members=len(files),
        uncompressed_file_bytes=sum(x['bytes']for x in files.values()),files=files)
    validated_members(archive,inv)
    for name,entry in files.items():assert sha(source/name)==entry['sha256']
    inventory.write_text(json.dumps(inv,indent=2)+'\n')
    return inv

def extract(archive,inventory,output):
    archive,inventory=Path(archive).resolve(),Path(inventory).resolve()
    target=Path(os.path.abspath(output))
    assert target==target.resolve()and target.parent.is_dir()
    assert not target.exists()and not target.is_symlink()
    assert not archive.is_relative_to(target)and not inventory.is_relative_to(target)
    inv=json.loads(inventory.read_text());inventory_hash=sha(inventory)
    data=validated_members(archive,inv)
    target.mkdir(exist_ok=False)
    for name,content in data.items():
        p=target/name;p.parent.mkdir(parents=True,exist_ok=True)
        assert p.resolve().is_relative_to(target)
        fd=os.open(p,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o644)
        os.fchmod(fd,0o644)
        with os.fdopen(fd,'wb')as stream:
            stream.write(content);stream.flush();os.fsync(stream.fileno())
        assert sha(p)==inv['files'][name]['sha256']
    observed={str(p.relative_to(target))for p in target.rglob('*')if p.is_file()}
    assert observed==set(inv['files'])
    assert sha(inventory)==inventory_hash and sha(archive)==inv['archive_sha256']
    return dict(status='PASS_EXACT_FRESH_A165_DELTA_EXTRACTION',members=len(data),
        bytes=sum(len(x)for x in data.values()),archive_sha256=inv['archive_sha256'],
        inventory_sha256=inventory_hash,input_manifest_sha256=sha(target/'INPUT_MANIFEST.json'),
        proof_arithmetic_replayed=False,new_original_cells=0,new_masks=0)

if __name__=='__main__':
    p=argparse.ArgumentParser();sub=p.add_subparsers(dest='mode',required=True)
    b=sub.add_parser('build');b.add_argument('source',type=Path);b.add_argument('archive',type=Path);b.add_argument('inventory',type=Path)
    e=sub.add_parser('extract');e.add_argument('archive',type=Path);e.add_argument('inventory',type=Path);e.add_argument('output',type=Path)
    v=sub.add_parser('verify');v.add_argument('archive',type=Path);v.add_argument('inventory',type=Path)
    args=p.parse_args()
    if args.mode=='build':
        x=build(args.source,args.archive,args.inventory)
        print(json.dumps({k:x[k]for k in('archive_sha256','archive_bytes','members','uncompressed_file_bytes')}),flush=True)
    elif args.mode=='extract':print(json.dumps(extract(args.archive,args.inventory,args.output)),flush=True)
    else:
        x=json.loads(args.inventory.read_text());validated_members(args.archive,x)
        print(json.dumps(dict(status='PASS_COMPLETE_REGULAR_FILE_ARCHIVE',members=x['members'],archive_sha256=x['archive_sha256'])),flush=True)
