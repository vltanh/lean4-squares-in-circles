"""Literal seven-square substitution in the frozen opposite-endpoint guard."""
from pathlib import Path
from fractions import Fraction as F
import importlib.util,hashlib

SOURCE=Path(__file__).resolve().parent.parent/'c887/c887_whole_eight_checkpoint_package/opposite_tilt_theorem/opposite_tilt_four_row_guard.py'
SOURCE_SHA='3d1a74e8108f9eb02e431e2e25f9f24aa7bffd55aac8f3a956d2f54a11886c0d'
assert hashlib.sha256(SOURCE.read_bytes()).hexdigest()==SOURCE_SHA
spec=importlib.util.spec_from_file_location('ac_source_opposite_abid_guard',SOURCE)
G=importlib.util.module_from_spec(spec);spec.loader.exec_module(G)

def evaluate(state):
    # Map the theorem's dummy H to physical B. This changes no original path,
    # mask, corner, pair, or bound: the temporary view is used by the guard only.
    p,a,s,ds=G.unpack(state);permutation=(0,7,2,3,4,5,6,1,8)
    positions=tuple(p[2*permutation[i]+axis]for i in range(9)for axis in(0,1))
    angles=tuple(a[permutation[i]]for i in range(9))
    scalar=tuple(s[offset+permutation[i]]for offset in(0,9,18,27)for i in range(9))
    differences={}
    for i in range(9):
        for j in range(i+1,9):
            u,v=permutation[i],permutation[j];pair=tuple(sorted((u,v)))
            if pair not in ds:continue
            differences[i,j]=ds[pair]if u<v else tuple((-hi,-lo)for lo,hi in ds[pair])
    result=G.evaluate(dict(positions=positions,angles=angles,scalar=scalar,differences=differences))
    result['status']='PASS_OPPOSITE_TILT_ABID_TERMINAL'if result['status']=='PASS_OPPOSITE_TILT_AHID_TERMINAL'else'GUARD_NOT_IMPLIED'
    result['physical_row']=[0,1,8,3]
    result['literal_source_substitution']={'H':'B'}
    return result
