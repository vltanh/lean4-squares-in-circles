"""Bind the completed hand pair proofs to their exact finite cyclic assembly.

This is a source-integrity and fixed-case/arithmetic audit. The continuous
inequalities are the bound hand manuscripts, not consequences of file hashes.
The script works in the research workspace and in a flat research/eight bundle.
"""
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256
from itertools import product
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent if (HERE.parent/'m5_agent').is_dir() else HERE
def resolve(p):
    direct=ROOT/p
    if direct.is_file():return direct
    flat=HERE/Path(p).name
    assert flat.is_file(),p
    return flat
def digest(p):return sha256(resolve(p).read_bytes()).hexdigest()
def load(p):return json.loads(resolve(p).read_text())

P='proof_integration/'
M='m5_agent/hand_conversion/'
G='global_attack/hand_conversion/'
coverage_path=M+'wrong_0011011_pair_coverage_audit.json'
cover=load(coverage_path)
assert cover['status']=='PASS_FINITE_COVERAGE'
assert (cover['directed_pair_cases'],cover['canonical_pair_cases'])==(76,39)
assert cover['canonical_kind_counts']=={'CC':10,'mixed':19,'OO':10}
data=load(P+'wrong_0011011_labels.json')
assert data['word']==[0,0,1,1,0,1,1]
assert F(data['Q'])==F(9789,2500) and F(data['gamma'])==F(17953,20000)
assert data['denominator']==100000

# Reconstruct the necessary sign list independently from five free signs.
signs=[]
for s1,s3,s4,s5,s6 in product('+-',repeat=5):
    s=('+',s1,'-',s3,s4,s5,s6)
    if (s4,s5)!=('-','+'):signs.append(s)
assert len(signs)==24
edge_signs={(i,s[i]+s[(i+1)%7]) for s in signs for i in range(7)}
assert len(edge_signs)==19
cases={(i,ss,kinds) for i,ss in edge_signs for kinds in ['CC','CO','OC','OO']}
assert len(cases)==76
opp={'+':'-','-':'+'}
def reflection(case):
    i,ss,k=case
    return ((1-i)%7,opp[ss[1]]+opp[ss[0]],k[::-1])
assert all(reflection(reflection(c))==c and reflection(c) in cases for c in cases)
orbits={frozenset((c,reflection(c))) for c in cases}
assert len(orbits)==39
assert {next(iter(o)) for o in orbits if len(o)==1}=={(4,'+-','CC'),(4,'+-','OO')}
listed={frozenset(tuple(c) for c in row['orbit']) for row in cover['canonical_cover']}
assert listed==orbits
assert all(row['retained_axes_covered']==[1,2,3,4] for row in cover['canonical_cover'])

# Current manuscript bytes must be precisely those of the finite cover.
manuscripts=cover['manuscript_hashes']
for path,h in manuscripts.items():assert digest(path)==h,('finite cover source changed',path)

# Completed independent review records, including the restored archival pieces.
review_paths=[
 P+'WRONG_0011011_ALL_CORE_CORE_INDEPENDENT_AUDIT.md',
 P+'wrong_0011011_all_core_independent_audit.json',
 P+'WRONG_0011011_EARLIER_MIXED_INDEPENDENT_AUDIT.md',
 P+'wrong_0011011_earlier_mixed_independent_audit.json',
 P+'WRONG_0011011_FINAL_MIXED_EDGE3_INDEPENDENT_AUDIT.md',
 P+'wrong_0011011_edge3_final_mixed_independent_audit.json',
 M+'WRONG_0011011_EDGE2_NEGATIVE_CORE_TO_OUTER_INDEPENDENT_AUDIT.md',
 M+'WRONG_0011011_NEGATIVE_OUTER_QUARTER_INDEPENDENT_AUDIT.md',
 M+'negative_outer_quarter_author_replay_audit.json',
 M+'WRONG_0011011_OPPOSITE_MIXED_ZERO_INDEPENDENT_AUDIT.md',
 M+'wrong_0011011_opposite_mixed_zero_independent_polynomial_audit.json',
 M+'WRONG_0011011_ASYMMETRIC_OPPOSITE_OUTER_ZERO_INDEPENDENT_AUDIT.md',
 M+'wrong_0011011_asymmetric_opposite_outer_zero_independent_audit.json',
 M+'WRONG_0011011_SYMMETRIC_OUTER_INDEPENDENT_AUDIT.md',
 M+'wrong_0011011_symmetric_outer_independent_audit.json',
 G+'WRONG_0011011_SAME_SIGN_MIXED_ZERO_INDEPENDENT_AUDIT.md',
 G+'wrong_0011011_same_sign_mixed_zero_independent_audit.json',
 G+'WRONG_0011011_SAME_OUTER_ZERO_INDEPENDENT_AUDIT.md',
 G+'WRONG_0011011_POSITIVE_NEGATIVE_OUTER_QUARTER_INDEPENDENT_AUDIT.md',
 G+'wrong_0011011_two_outer_components_independent_arithmetic.json',
 G+'WRONG_0011011_POSITIVE_CORE_OUTER_EDGE3_INDEPENDENT_AUDIT.md',
 G+'wrong_0011011_positive_core_outer_edge3_independent_audit.json',
 G+'WRONG_0011011_NEGATIVE_OUTER_EDGE3_INDEPENDENT_AUDIT.md',
 G+'wrong_0011011_negative_outer_edge3_independent_audit.json',
 G+'WRONG_0011011_OPPOSITE_OUTER_EDGE2_INDEPENDENT_AUDIT.md',
 G+'wrong_0011011_opposite_outer_edge2_independent_audit.json',
 G+'WRONG_0011011_OPPOSITE_OUTER_EDGE3_INDEPENDENT_AUDIT.md',
 G+'wrong_0011011_opposite_outer_edge3_independent_audit.json',
 G+'WRONG_0011011_POSITIVE_OUTER_EDGE3_INDEPENDENT_AUDIT.md',
 G+'wrong_0011011_positive_outer_edge3_independent_audit.json',
]
reviews={p:resolve(p).read_text() for p in review_paths}
for p,text in reviews.items():
    if p.endswith('.json'):
        j=json.loads(text)
        if p==M+'negative_outer_quarter_author_replay_audit.json':
            assert j['returncode']==0 and j['byte_identical'] is True and j['stderr']==''
        else:
            assert str(j['status']).startswith('PASS'),(p,j['status'])
    else:assert 'PASS' in text[:600],p

# Every principal and every explicit imported manuscript has a current
# SHA-256 in at least one completed independent review record.
review_links={}
for path,h in manuscripts.items():
    if not path.endswith('.md'):continue
    matched=[p for p,t in reviews.items() if h in t]
    assert matched,('no independent binding for current manuscript',path,h)
    review_links[path]={'sha256':h,'independent_records':matched}

gamma=F(data['gamma'])
def T(x,n):
    x=F(x);return sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(n)),F(0))
pi_upper=16*T('1/5',5)-4*T('1/239',2)
assert pi_upper<F(355,113)
assert 7*gamma-F(710,113)==F(823,2260000)>0
assert F(41,50)>F(355,452)
assert sum(data['word'])==4

theorem_path=P+'WRONG_0011011_WHOLE_WORD_HAND_PROOF.md'
other_bindings={
 theorem_path:digest(theorem_path),
 coverage_path:digest(coverage_path),
 M+'WRONG_0011011_PAIR_COVERAGE_INDEPENDENT_AUDIT.md':digest(M+'WRONG_0011011_PAIR_COVERAGE_INDEPENDENT_AUDIT.md'),
 M+'audit_wrong_0011011_pair_coverage.py':digest(M+'audit_wrong_0011011_pair_coverage.py'),
 P+'wrong_0011011_labels.json':digest(P+'wrong_0011011_labels.json'),
}
out={
 'status':'PASS_FIXED_CASE_AND_SOURCE_BINDING',
 'hand_word_status':'CLOSED',
 'scope':'The complete 0011011 hand word theorem at Q=9789/2500, under the stated analytic exterior boundary/gap/frame premises. No candidate-word or unrestricted equality conclusion.',
 'Q':data['Q'],'word':data['word'],'gamma':data['gamma'],
 'full_sign_assignments':24,'directed_pair_cases':76,'canonical_pair_cases':39,
 'canonical_kind_counts':{'CC':10,'mixed':19,'OO':10},
 'directed_axis_cases':304,'axis_reflection_orbits':152,
 'cyclic_lower_bound':str(7*gamma),'twice_pi_upper':'710/113',
 'strict_rational_surplus':'823/2260000',
 'independent_machin_pi_upper':str(pi_upper),
 'exact_machin_reserve':str(F(355,113)-pi_upper),
 'principal_and_import_manuscript_count':len(review_links),
 'independently_bound_manuscripts':review_links,
 'independent_review_artifacts':{p:digest(p) for p in review_paths},
 'assembly_bindings':other_bindings,
 'finite_case_map':cover['canonical_cover'],
 'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
}
HERE.joinpath('wrong_0011011_hand_word_closure_manifest.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in [
 'status','hand_word_status','directed_pair_cases','canonical_pair_cases',
 'principal_and_import_manuscript_count','strict_rational_surplus']},indent=2))
