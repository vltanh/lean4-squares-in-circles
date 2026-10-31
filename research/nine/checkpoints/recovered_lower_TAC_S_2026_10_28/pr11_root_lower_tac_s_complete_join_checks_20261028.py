from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
import re,json
base=Path('/workspace/scratch/8168d2185cf7/repo/research/nine')
digest=lambda p:sha256(p.read_bytes()).hexdigest()
name='HOUSE_LOWER_TAC_S_COMPLETE_EXCLUSION.md'
assert digest(base/name)=='de3565cda8f47022376c115c26f50061fc67e10e320c9f389dcce1c99d8a568b'
pins=re.findall(r'^\|\s*([A-Za-z0-9_/]+\.(?:md|py))\s*\|\s*([0-9a-f]{64})\s*\|',(base/name).read_text(),re.M)
assert len(pins)==19
for n,h in pins:assert digest(base/n)==h,n
edges=['AT','DT','AD','AB','BC','CD','BL']
degrees={v:sum(v in e for e in edges) for v in 'ABCDTL'}
assert degrees=={'A':3,'B':3,'C':2,'D':3,'T':2,'L':1}
assert all(''.join(sorted(a+b)) in {''.join(sorted(e)) for e in edges} for a,b in zip('BATDC','ATDCB'))
reserves={
 'd_lower_radius_square':F(15,4)-F(29,15)**2,
 'd_upper_radius_square':F(121,60)**2-F(1041,256),
 'visibility_sqrt_two_majorant':F(99,70)**2-2,
 'upper_A_height_floor':F(1,25000),
 'upper_C_visibility_floor':F(1,1000000),
 'actual_required_extras_minus_capacity':F(3)-2,
}
assert all(v>0 for v in reserves.values())
records={
 '/tmp/pr11_root_lower_tac_s_tilted_checks.json':'9911a7635a4f0c1e1656930dcd32778cfda3e08d1f326970444062f5764ac858',
 '/tmp/pr11_root_lower_tac_s_upper_a_checks.json':'62fe61bb75f4a567fa411c1d4fe9bbf23725a2f6e6a7a1677c205a5be62954db',
 '/tmp/pr11_root_replay_aligned_low_s_lower_return_height_separation_certificate.json':'ce034bcdca30eb79e8ea0e1647885f71614af2da138ebf58d5856978e41d9470',
 '/tmp/aligned_low_s_upper_c_visibility_certificate.json':'a960dd73c0ed3084e4dfe4cf34a3f749e2a2ca2fef962e247c46cc3ffc405691',
}
for p,h in records.items():assert digest(Path(p))==h,p
out={'source':{'file':name,'sha256':digest(base/name)},'literal_source_review_code_pins':[{'file':n,'sha256':h} for n,h in pins],
 'actual_positive_edges':edges,'actual_degrees':degrees,'actual_positive_loads':['A','C','T','L'],
 'full_disjoint_partition':['R<=2','R>2 tilted B','R>2 aligned B,d>=1','R>2 aligned B,d<1,A upper','R>2 aligned B,d<1,C upper'],
 'critical_endpoints':{'R=2':'same-nine radius exclusion','d=1':'aligned high or tilted row','upper/lower degree labels':'both actual placements retained'},
 'strict_exact_reserves':{k:str(v) for k,v in reserves.items()},'retained_complete_root_records':[{'path':p,'sha256':h} for p,h in records.items()],
 'scope':'Exact support for whole original-family root join audit; every complete direct proof/review read, two independent peers for root contributions; no metadata change.'}
p=Path('/tmp/pr11_root_lower_tac_s_complete_join_checks_20261028.json');p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'literal_pins':len(pins),'whole_partition_rows':5,'strict_reserves':len(reserves),'record':str(p),'sha256':digest(p)},indent=2))
