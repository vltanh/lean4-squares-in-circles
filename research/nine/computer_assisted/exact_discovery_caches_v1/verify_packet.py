"""Literal/guard parity and exact scalar-rounding behavior on complete fixtures."""
from pathlib import Path
from fractions import Fraction as F
from types import SimpleNamespace
import importlib.util,json,gzip,hashlib,time,math
import numpy as np
import fast_coupled_energy_cache as CACHE
import fast_sparse_dual_terms as SPARSE
ROOT=Path(__file__).resolve().parent
assert __debug__
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def reference(name):
    spec=importlib.util.spec_from_file_location(name,ROOT/'reference_coupled_energy.py')
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod
before=reference('uncached_energy');after=reference('cached_energy');CACHE.install(after)
energy=[]
for case in json.loads((ROOT/'PAIR_INTERVAL_INPUTS.json').read_text())['cases']:
    ds={tuple(r['pair']):tuple(tuple(map(F,x))for x in r['intervals'])for r in case['differences']}
    dg={p:((x[0]+y[0],x[1]+y[1]),(x[0]-y[1],x[1]-y[0]))for p,(x,y)in ds.items()}
    t=time.monotonic();a=before.rows(ds,dg);old=time.monotonic()-t
    t=time.monotonic();b=after.rows(ds,dg);new=time.monotonic()-t;assert a==b
    t=time.monotonic();c=after.rows(ds,dg);repeat=time.monotonic()-t;assert c==a
    assert b[0]is not c[0]and b[1]is not c[1]
    b[0].clear();b[1][0]['planes'].clear();assert after.rows(ds,dg)==a
    energy.append(dict(case=case['id'],rows=len(a[0]),guards=len(a[1]),all_rows_and_guards_equal=True,mutable_outputs_isolated=True,reference_seconds=old,optimized_seconds=new,repeated_seconds=repeat))
SCALE=1<<40
def old_terms(dual):return [[i,int(round(-float(v)*SCALE))]for i,v in enumerate(dual)if int(round(-float(v)*SCALE))>0]
module=SimpleNamespace(terms=old_terms,SCALE=SCALE);SPARSE.install(module)
fixture=json.loads(gzip.decompress((ROOT/'DUAL_INPUTS.json.gz').read_bytes()))
old_seconds=new_seconds=0.;weights=0
for row in fixture['vectors']:
    dual=np.zeros(row['length'],dtype='float64')
    for i,w in row['weights']:dual[i]=-w/SCALE
    t=time.monotonic();a=old_terms(dual);old_seconds+=time.monotonic()-t
    t=time.monotonic();b=module.terms(dual);new_seconds+=time.monotonic()-t
    assert a==b;weights+=len(a)
thresholds=[]
for n in(0,1,2,3,1000,1<<20):
    x=(n+0.5)/SCALE
    for v in(x,math.nextafter(x,math.inf),math.nextafter(x,-math.inf)):thresholds.extend((v,-v))
thresholds.extend((0.,-0.,math.nextafter(0.,1.),math.nextafter(0.,-1.),1e50,-1e50))
for v in thresholds:
    dual=np.array([0.,v,0.,-v],dtype='float64');assert module.terms(dual)==old_terms(dual)
for v in(math.nan,math.inf,-math.inf,1e308,-1e308):
    errors=[]
    for fn in(old_terms,module.terms):
        try:fn(np.array([v],dtype='float64'))
        except(ValueError,OverflowError)as e:errors.append(type(e).__name__)
    assert len(errors)==2 and errors[0]==errors[1]
report=dict(status='PASS_COMPLETE_DISCOVERY_CACHE_PARITY',energy=energy,energy_rows=sum(a['rows']for a in energy),energy_guards=sum(a['guards']for a in energy),dual_vectors=len(fixture['vectors']),nonzero_weights=weights,rounding_boundary_controls=len(thresholds),error_behaviors_preserved=5,dual_reference_seconds=old_seconds,dual_optimized_seconds=new_seconds,fixture_contains_reconstructed_rounded_duals_only=True,source_sha256={p.name:digest(p)for p in sorted(ROOT.iterdir())if p.is_file()and p.name!='VERIFY_REPORT.json'},new_original_cells=0,new_masks=0)
(ROOT/'VERIFY_REPORT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items()if k not in('energy','source_sha256')}),flush=True)
