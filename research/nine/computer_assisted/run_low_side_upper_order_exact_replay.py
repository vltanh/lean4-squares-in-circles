#!/usr/bin/env python3
"""Bind a complete JSON proof to the standalone exact integer replay.

No producer imports. The C++ checker rebuilds all physical expressions and
all rational midpoint roots. This wrapper checks the graph, validates the
closed metadata, and serializes only the selected integer tree events.
"""
from fractions import Fraction as F
from pathlib import Path
from contextlib import contextmanager
import gzip,hashlib,itertools,json,shutil,subprocess,sys,tempfile,time

ROOT=((F(0),F(1)),(F(0),F(1)),(F(0),F(1)),(F(0),F(1129,3000)),
      (F(7,10),F(13,12)),(F(1,2),F(57,100)))

def integer(x):return type(x)is int

def no_duplicates(pairs):
    answer={}
    for key,value in pairs:
        assert key not in answer,('duplicate JSON field',key)
        answer[key]=value
    return answer

@contextmanager
def build_checker():
    """Compile the exact delivered bytes, then bind and execute that build.

    An existing .bin file is never read. The immutable temporary snapshot
    prevents a changed source or stale executable from acquiring a new hash.
    """
    source=Path(__file__).with_name('verify_low_side_upper_order_exact.cpp')
    source_bytes=source.read_bytes()
    compiler=shutil.which('g++')
    assert compiler is not None,'g++ is required for the standalone exact replay'
    version=subprocess.run([compiler,'--version'],capture_output=True,check=True).stdout.decode().splitlines()[0]
    flags=['-std=c++17','-O2','-Wall','-Wextra','-pedantic']
    with tempfile.TemporaryDirectory(prefix='low-side-exact-') as directory:
        snapshot=Path(directory)/source.name
        executable=Path(directory)/'checker'
        snapshot.write_bytes(source_bytes)
        built=subprocess.run([compiler,*flags,str(snapshot),'-o',str(executable)],capture_output=True,check=False)
        assert built.returncode==0,('checker source did not compile',built.stdout.decode(),built.stderr.decode())
        assert snapshot.read_bytes()==source_bytes
        metadata={
            'checker_source_file':source.name,
            'checker_source_sha256':hashlib.sha256(source_bytes).hexdigest(),
            'checker_executable_sha256':hashlib.sha256(executable.read_bytes()).hexdigest(),
            'compiled_from_exact_source_snapshot':True,
            'checker_compiler':version,
            'checker_compile_flags':flags,
            'checker_compile_diagnostics':built.stderr.decode(),
        }
        yield executable,metadata

def events_for(data):
    if data.get('schema')=='low_side_upper_order_compact_v1':
        assert data['status']=='COMPLETE_PENDING_INDEPENDENT_REPLAY'
        assert integer(data['remaining'])and data['remaining']==0
        assert integer(data['leaves'])and data['leaves']>=8
        assert integer(data['nodes'])and data['nodes']==2*data['leaves']-8
        assert integer(data['maximum_depth'])and 0<=data['maximum_depth']<=70
        raw=data['events'];assert type(raw)is list and len(raw)==data['nodes']
        assert type(data['counts'])is list and len(data['counts'])==13
        assert type(data['leaves_per_root'])is list and len(data['leaves_per_root'])==8
        assert all(integer(n)and n>=0 for n in data['counts']+data['leaves_per_root'])
        pending=[(rid,0)for rid in range(7,-1,-1)]
        counts=[0]*13;perroot=[0]*8;depthmax=0;events=bytearray()
        for tag in raw:
            assert integer(tag)and pending
            rid,depth=pending.pop();depthmax=max(depthmax,depth)
            assert depth<=70
            if tag>=0:
                assert tag<6
                pending.extend(((rid,depth+1),(rid,depth+1)))
            else:
                code=-tag-1;assert 0<=code<13
                counts[code]+=1;perroot[rid]+=1
            events.append(tag%256)
        assert not pending and counts==data['counts']and perroot==data['leaves_per_root']
        assert sum(counts)==data['leaves']and depthmax==data['maximum_depth']
        return events,perroot
    assert data['schema']=='low_side_upper_order_lower_central_v1'
    assert data['status']=='COMPLETE_PENDING_INDEPENDENT_REPLAY'
    assert data['root']==[[str(a),str(b)]for a,b in ROOT]
    assert integer(data['remaining'])and data['remaining']==0 and data['pending']==[]
    assert integer(data['leaves'])and data['leaves']>=8
    assert integer(data['maximum_depth'])and 0<=data['maximum_depth']<=75
    assert type(data['counts'])is list and len(data['counts'])==13
    assert all(integer(x)and x>=0 for x in data['counts'])and sum(data['counts'])==data['leaves']
    roots,nodes=data['roots'],data['nodes']
    assert type(roots)is list and len(roots)==8 and type(nodes)is list
    assert len(nodes)==2*data['leaves']-8
    assert all(type(r)is dict and set(r)=={'index','chart'}for r in roots)
    assert all(integer(r['index'])and type(r['chart'])is list and all(integer(c)for c in r['chart'])for r in roots)
    assert [tuple(r['chart'])for r in roots]==list(itertools.product((-1,1),repeat=3))
    events=bytearray();seen=set();depthmax=0;counts=[0]*13;perroot=[]
    for root in roots:
        before=sum(counts);todo=[(root['index'],0)]
        while todo:
            index,depth=todo.pop()
            assert integer(index)and 0<=index<len(nodes)and index not in seen and depth<=75
            seen.add(index);depthmax=max(depthmax,depth);node=nodes[index]
            assert type(node)is dict
            if 'rule'in node:
                assert set(node)=={'rule','upper'}and type(node['upper'])is str
                rule=node['rule'];assert integer(rule)and 0<=rule<13
                events.append((-rule-1)%256);counts[rule]+=1
            else:
                assert set(node)=={'axis','children'}
                axis,child=node['axis'],node['children']
                assert integer(axis)and 0<=axis<6 and type(child)is list and len(child)==2
                events.append(axis);todo.extend(((child[1],depth+1),(child[0],depth+1)))
        perroot.append(sum(counts)-before)
    assert len(seen)==len(nodes)and counts==data['counts']and depthmax==data['maximum_depth']
    return events,perroot

def verify(path):
    path=Path(path);stored=path.read_bytes()
    raw=gzip.decompress(stored)if path.suffix=='.gz'else stored
    data=json.loads(raw,object_pairs_hook=no_duplicates)
    events,perroot=events_for(data)
    payload=(str(len(events))+' '+str(data['leaves'])+'\n').encode()+events
    with build_checker()as(binary,build_metadata):
        run=subprocess.run([str(binary)],input=payload,capture_output=True,check=False)
    assert run.returncode==0,('exact checker rejected',run.stdout.decode(),run.stderr.decode())
    result=json.loads(run.stdout)
    assert result['result']=='PASS'and result['complete']is True
    assert result['nodes']==len(events)and result['strict_leaves']==data['leaves']
    assert result['counts']==data['counts']and result['leaves_per_root']==perroot
    assert result['maximum_depth']==data['maximum_depth']and result['roots']==8
    assert result['scale_bits']==48 and int(result['minimum_positive_reserve_numerator'])>0
    result.update(certificate_file=path.name,stored_sha256=hashlib.sha256(stored).hexdigest(),
                  certificate_json_sha256=hashlib.sha256(raw).hexdigest(),event_stream_sha256=hashlib.sha256(payload).hexdigest(),
                  wrapper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  producer_imports=False,scope='low opposite side at/above P with a lower central; no whole mask claim')
    result.update(build_metadata)
    return result

def main():
    path=Path(sys.argv[1])if len(sys.argv)>1 else Path(__file__).with_name('low_side_upper_order_compact_cover.json')
    started=time.monotonic();result=verify(path);result['total_seconds']=time.monotonic()-started
    path.with_name('low_side_upper_order_cover_independent_exact_replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
