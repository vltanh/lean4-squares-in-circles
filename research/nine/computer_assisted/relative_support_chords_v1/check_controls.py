"""Cold exact parity and adversarial literal/guard tests; no producer import."""
from pathlib import Path
from fractions import Fraction as F
import json,hashlib,sys,time
import independent_relative_support_chords as V
HERE=Path(__file__).resolve().parent;start=time.monotonic();fixture=HERE/'CONTROL_FIXTURE.json';data=json.loads(fixture.read_text());scalar=tuple(tuple(map(F,v))for v in data['scalar']);n=0;good=[]
for domain in data['domains']:
    ds={tuple(domain['pair']):tuple(tuple(map(F,v))for v in domain['box'])}
    for co,rhs,name in domain['rows']:
        row=tuple((int(k),F(v))for k,v in co),F(rhs),name
        assert V.verify_literal(row,scalar,ds);n+=1
        if len(good)<1 and '_0_1_' in name:good.append((row,ds))
# Select a nonzero-intercept row with a positive longitudinal guard.
domain=next(d for d in data['domains']if F(d['box'][0][0])>0 and F(d['box'][1][0])<0)
ds={tuple(domain['pair']):tuple(tuple(map(F,v))for v in domain['box'])};raw=domain['rows'][0]
row=(tuple((k,F(v))for k,v in raw[0]),F(raw[1]),raw[2]);assert V.verify_literal(row,scalar,ds)
parts=row[2][len(V.PREFIX):].split('_');cases=[]
def renamed(index,value):
    f=parts[:];f[index]=value;return(row[0],row[1],V.PREFIX+'_'.join(f))
def must_reject(label,literal=row,ss=scalar,dd=ds):
    try:V.verify_literal(literal,ss,dd)
    except(AssertionError,ValueError,KeyError,IndexError,ZeroDivisionError):cases.append(label);return
    raise AssertionError('accepted damaged control '+label)
must_reject('right-hand-side', (row[0],row[1]+F(1,1000),row[2]))
co=list(row[0]);co[0]=(co[0][0],co[0][1]+F(1,1000));must_reject('coefficient',(tuple(co),row[1],row[2]))
must_reject('reverse-coefficient-order',(tuple(reversed(row[0])),row[1],row[2]))
must_reject('unknown-family',renamed(0,'other'))
must_reject('reversed-original-pair',renamed(1,parts[2]))
must_reject('noncanonical-integer',renamed(1,'0'+parts[1]))
must_reject('bad-axis',renamed(3,'2'))
must_reject('longitudinal-sign',renamed(4,'-1'))
must_reject('bad-epsilon',renamed(5,'0'))
must_reject('ratio-left-guard',renamed(6,'0'))
must_reject('ratio-right-guard',renamed(7,'-1'))
must_reject('endpoint-height-square',renamed(8,'2'))
must_reject('negative-endpoint-height',renamed(9,'-1'))
must_reject('bad-plane-bit',renamed(10,'0002'))
box=list(next(iter(ds.values())));box[0]=(F(-1),F(2));must_reject('caller-longitudinal-interval',dd={next(iter(ds)):tuple(box)})
box=list(next(iter(ds.values())));box[1]=(F(-2),F(2));must_reject('caller-transverse-interval',dd={next(iter(ds)):tuple(box)})
badscalar=list(scalar);badscalar[0]=(F(2),F(1));must_reject('reversed-scalar-interval',ss=tuple(badscalar))
# A legitimate endpoint under-chord with negative intercept must not be used
# to replace h by its lower bound. Force ratio [1/4,1/2], heights [0,1/2].
f=parts[:];f[6:10]=['1/4','1/2','0','1/2'];box=list(next(iter(ds.values())));box[1]=(F(121,400),F(1,2));must_reject('negative-intercept',(row[0],row[1],V.PREFIX+'_'.join(f)),dd={next(iter(ds)):tuple(box)})
# Degenerate t=0 is the only supported collapsed ratio interval.
zero=next(d for d in data['domains'] if all(F(x)==0 for x in d['box'][1]) and F(d['box'][0][0])>0);zr=zero['rows'][0];zrow=(tuple((k,F(v))for k,v in zr[0]),F(zr[1]),zr[2]);zd={tuple(zero['pair']):tuple(tuple(map(F,v))for v in zero['box'])};assert V.verify_literal(zrow,scalar,zd)
f=zrow[2][len(V.PREFIX):].split('_');f[8:10]=['0','0'];must_reject('degenerate-height',(zrow[0],zrow[1],V.PREFIX+'_'.join(f)),dd=zd)
assert not any(k in sys.modules for k in ('physical_relative_support_chords','owner_free_relative_support_snapshot','numpy','scipy','highspy'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for p,h in data['producer_sources'].items():
    name=Path(p).name
    assert name in ('physical_relative_support_chords.py','owner_free_relative_support_snapshot.py')
    assert sha(HERE/name)==h
out=dict(status='PASS_INDEPENDENT_RELATIVE_SUPPORT_CHORD_CONTROLS',domains=len(data['domains']),literals=n,rejected_controls=cases,decoder=dict(path=str(Path(V.__file__).resolve()),sha256=sha(V.__file__)),fixture=dict(path=str(fixture),sha256=sha(fixture)),checker=dict(path=str(Path(__file__).resolve()),sha256=sha(__file__)),producer_imported=False,numerical_library_imported=False,actual_weighted_certificate_checked=False,new_original_cells=0,new_masks=0,seconds=time.monotonic()-start)
(HERE/'CONTROL_REPORT.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'],n,len(cases),out['seconds'])
