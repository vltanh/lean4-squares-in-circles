#!/usr/bin/env python3
from pathlib import Path
from copy import deepcopy
import hashlib,importlib.util,io,json,lzma,subprocess,sys,tarfile,tempfile
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('T',HERE/'i64_transport_v1.py');T=importlib.util.module_from_spec(spec);spec.loader.exec_module(T)

if not __debug__:raise RuntimeError('Controls require assertions.')

def main():
    root=Path(tempfile.mkdtemp(prefix='i64_transport_controls_'))
    archive=HERE/'i64_source_checkpoint_v3.tar.xz';inventory=HERE/'I64_ARCHIVE_INVENTORY.json';inv=json.loads(inventory.read_text())
    first=T.extract(archive,inventory,root/'actual_extracted')
    second_archive=root/'repeat.tar.xz';second_inv=root/'repeat_inventory.json'
    T.build(HERE/'i64_source_checkpoint_v3',second_archive,second_inv)
    assert T.sha(second_archive)==T.sha(archive)and T.sha(second_inv)==T.sha(inventory)
    original_bytes={str(p.relative_to(HERE/'i64_source_checkpoint_v3')):T.sha(p)for p in(HERE/'i64_source_checkpoint_v3').rglob('*')if p.is_file()}
    accepted=[]
    def reject(name,call):
        try:call()
        except (AssertionError,ValueError,KeyError,tarfile.TarError,lzma.LZMAError,EOFError,OSError):accepted.append(name);return
        raise AssertionError('malformed case accepted: '+name)
    def fixture(tag,entries):
        p=root/(tag+'.tar.xz')
        with lzma.open(p,'wb',preset=1)as compressed:
            with tarfile.open(fileobj=compressed,mode='w|',format=tarfile.USTAR_FORMAT)as tar:
                for name,kind,data,mtime in entries:
                    info=tarfile.TarInfo(name);info.type=kind;info.uid=info.gid=0;info.uname=info.gname='';info.mode=0o644;info.mtime=mtime
                    if kind in(tarfile.SYMTYPE,tarfile.LNKTYPE):info.linkname='/tmp/never_write_i64_control_target'
                    info.size=len(data)if kind==tarfile.REGTYPE else 0
                    tar.addfile(info,io.BytesIO(data)if kind==tarfile.REGTYPE else None)
        expected=dict(schema=T.SCHEMA,file_only=True,files={'proof.json':dict(bytes=4,sha256=T.sha_bytes(b'abc\n'))},members=1,uncompressed_file_bytes=4,archive_sha256=T.sha(p),archive_bytes=p.stat().st_size)
        return p,expected
    cases={
      'parent_escape':[('../proof.json',tarfile.REGTYPE,b'abc\n',0)],
      'absolute_name':[('/proof.json',tarfile.REGTYPE,b'abc\n',0)],
      'empty_component':[('proof//data.json',tarfile.REGTYPE,b'abc\n',0)],
      'duplicate_member':[('proof.json',tarfile.REGTYPE,b'abc\n',0)]*2,
      'symlink_member':[('proof.json',tarfile.SYMTYPE,b'',0)],
      'hardlink_member':[('proof.json',tarfile.LNKTYPE,b'',0)],
      'directory_member':[('proof.json',tarfile.DIRTYPE,b'',0)],
      'extra_member':[('proof.json',tarfile.REGTYPE,b'abc\n',0),('extra.json',tarfile.REGTYPE,b'abc\n',0)],
      'missing_member':[],
      'content_damage':[('proof.json',tarfile.REGTYPE,b'bad\n',0)],
      'size_damage':[('proof.json',tarfile.REGTYPE,b'abc\nX',0)],
      'noncanonical_timestamp':[('proof.json',tarfile.REGTYPE,b'abc\n',1)]}
    for name,entries in cases.items():
        p,x=fixture(name,entries);reject(name,lambda p=p,x=x:T.validated_members(p,x))
    reject('existing_output',lambda:T.extract(archive,inventory,root/'actual_extracted'))
    link=root/'output_link';link.symlink_to(root/'actual_extracted',target_is_directory=True)
    reject('symlink_output',lambda:T.extract(archive,inventory,link))
    process=subprocess.run([sys.executable,'-B','-S','-O',str(HERE/'i64_transport_v1.py'),'verify',str(archive),str(inventory)],capture_output=True,text=True)
    assert process.returncode!=0 and 'requires assertions'in process.stderr
    accepted.append('optimized_python_rejected_before_dispatch')
    for name,h in original_bytes.items():assert T.sha(HERE/'i64_source_checkpoint_v3'/name)==h
    report=dict(status='PASS_I64_REGULAR_FILE_TRANSPORT_CONTROLS',actual_archive_sha256=T.sha(archive),actual_extraction=first,
      deterministic_rebuild_same_archive_and_inventory=True,damaged_cases_rejected=accepted,damaged_case_count=len(accepted),
      source_files_before_after=len(original_bytes),source_bytes_unchanged=True,proof_arithmetic_replayed=False,new_original_cells=0,new_masks=0,
      helper_sha256=T.sha(HERE/'i64_transport_v1.py'),control_source_sha256=T.sha(__file__),temporary_folder=str(root))
    p=HERE/'I64_TRANSPORT_CONTROLS.json';assert not p.exists();p.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(status=report['status'],report_sha256=T.sha(p),helper_sha256=report['helper_sha256'],damages=len(accepted),archive_sha256=T.sha(archive))),flush=True)

if __name__=='__main__':main()
