#!/usr/bin/env python3
"""Bind the completed mathematical appendices; this is not a proof solver.

Run in the flat research/eight directory after every component is present.
The checkout-layout fallback only locates the same named source files in
this collaborative workspace. No network, search, fitting or proof repair
is performed. Existing component sources and manifests remain unchanged.
"""
from pathlib import Path
from collections import defaultdict
from fractions import Fraction as F
import hashlib
import json
import re
import sys

BASE = Path(__file__).resolve().parent
WORK = BASE.parent
OUT = BASE / 'UNRESTRICTED_EIGHT_SQUARE_HAND_MANIFEST.json'
ROOTS = [BASE, WORK/'proof_reference', WORK/'m5_agent/hand_conversion',
         WORK/'global_attack/hand_conversion',
         WORK/'global_attack/hand_conversion/final_assembly_review',
         WORK/'n8/research/eight', WORK/'candidate_hand',
         WORK/'candidate_hand/m5_coarse_mismatch_audit',
         WORK/'candidate_hand/root_coarse_mismatch',
         WORK/'candidate_hand/root_middle_mismatch',
         WORK/'candidate_hand/global_budget/narrow01_hand',
         WORK/'candidate_hand/global_budget/final015_hand']
ROOTS += [WORK/'candidate_hand'/p for p in
          ['root_Glow','global_Ghigh','root_Thigh','global_Tlow',
           'root_Hlow','m5_Dhigh']]

GROUPS = {
 'main_assembly': [
  'UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md',
  'verify_unrestricted_eight_hand_interfaces.py',
  'unrestricted_eight_hand_interface_arithmetic.json',
  'UNRESTRICTED_EIGHT_HAND_DEPENDENCY_INDEPENDENT_AUDIT.md',
  'unrestricted_eight_hand_dependency_independent_audit.json',
  'UNRESTRICTED_EIGHT_ROOT_CORE_EQUALITY_INDEPENDENT_AUDIT.md',
  'unrestricted_eight_root_core_equality_independent_binding.json',
  'assemble_unrestricted_eight_hand_proof.py'],
 'exact_family_and_attainment': [
  'ANALYTIC_RATIONAL_CONSTRUCTION.md','FIVE_CORNER_REDUCTION.md',
  'HUMAN_FIVE_CORNER.md','HUMAN_FAMILY_ENCLOSURE.md',
  'HUMAN_FAMILY_CLOSURE.md','HUMAN_SHARP_CEILING_BRACKET.md',
  'HUMAN_BROAD_TERMINAL_ARITHMETIC.md'],
 'central_square_and_positive_core': [
  'HUMAN_GLOBAL_GEOMETRY_CLOSURE.md',
  'HUMAN_CENTRAL_CORE_FROM_TRANSVERSE_SEGMENT.md',
  'CENTRAL_BAND_COMMON_POINT_LEMMAS.md'],
 'radial_boundary_and_lifts': [
  'CYCLIC_RADIAL_BOUNDARY_REDUCTION.md',
  'LIFTED_STATE_POTENTIAL_TELESCOPING.md',
  'COMMON_POINT_AND_THREE_QUARTER_ANGLE.md',
  'HUMAN_CIRCULAR_CAP_AND_AXIS_ELIMINATION.md'],
 'complete_four_type_frame_theorem': [
  'CORE_CORE_WHOLE_PAIR_HAND_PROOF.md','CORE_LOW_WHOLE_PAIR_HAND_PROOF.md',
  'CORE_MID_WHOLE_PAIR_HAND_PROOF.md','CORE_HIGH_WHOLE_PAIR_HAND_PROOF.md',
  'LOW_LOW_WHOLE_PAIR_HAND_PROOF.md','LOW_MID_WHOLE_PAIR_HAND_PROOF.md',
  'LOW_HIGH_WHOLE_PAIR_HAND_PROOF.md','MID_MID_WHOLE_PAIR_HAND_PROOF.md',
  'MID_HIGH_WHOLE_PAIR_HAND_PROOF.md','HIGH_HIGH_WHOLE_PAIR_HAND_PROOF.md',
  'FOUR_TYPE_HAND_COVERAGE_INVENTORY.md','HAND_EXTERIOR_FRAME_CONCENTRATION.md',
  'LOW_FRAME_ENTRIES_INDEPENDENT_AUDIT.md',
  'CORE_MID_WHOLE_PAIR_INDEPENDENT_AUDIT.md','CORE_HIGH_INDEPENDENT_AUDIT.md',
  'LOW_MID_WHOLE_PAIR_INDEPENDENT_AUDIT.md',
  'LOW_HIGH_WHOLE_PAIR_INDEPENDENT_AUDIT.md',
  'MID_MID_WHOLE_PAIR_INDEPENDENT_AUDIT.md',
  'MID_HIGH_WHOLE_PAIR_INDEPENDENT_AUDIT.md',
  'RESTORED_HIGH_HIGH_INDEPENDENT_AUDIT.md'],
 'all_six_wrong_quarter_words': [
  'SEVEN_QUARTER_WORDS.md',
  'QUARTER_ZERO_ALL_BOUNDARY_STATES_HAND_PROOF.md',
  'QUARTER_ONE_ALL_BOUNDARY_STATES_HAND_PROOF.md',
  'QUARTER_TWO_ALL_BOUNDARY_STATES_HAND_PROOF.md',
  'COMMON_QUARTER_TABLE_AND_FOUR_WORD_EXCLUSIONS.md',
  'SHORT_WRONG_WORD_COMPLETE_HAND_EXCLUSION.md',
  'short_whole_word_hand_assembly_audit.json',
  'WRONG_0011011_WHOLE_WORD_HAND_PROOF.md',
  'wrong_0011011_hand_word_closure_manifest.json'],
 'continuous_scalar_support_kernel': [
  'AFFINE_MARKER_SUPPORT_REDUCTION.md','AFFINE_ARC_ONE_ANGLE_HAND_KERNEL.md',
  'CONDITIONAL_AFFINE_ARC_KERNEL_INDEPENDENT_AUDIT.md'],
 'six_candidate_tangent_cuts': [
  'CANDIDATE_WORD_HAND_CAPTURE_INTERFACES.md',
  'G_LOWER_AFFINE_HAND_MANIFEST.json','G_UPPER_AFFINE_HAND_MANIFEST.json',
  'T_LOWER_AFFINE_HAND_MANIFEST.json','T_UPPER_AFFINE_HAND_MANIFEST.json',
  'H_LOWER_AFFINE_HAND_MANIFEST.json','D_UPPER_AFFINE_HAND_MANIFEST.json'],
 'complete_mismatch_chain': [
  'CANDIDATE_COARSE_MISMATCH_HAND_MANIFEST.json',
  'COARSE_MISMATCH_PRINTED_RESERVE_MANIFEST.json',
  'MISMATCH_026_TO_01_AFFINE_HAND_MANIFEST.json',
  'MISMATCH_01_TO_015_AFFINE_HAND_MANIFEST.json',
  'MISMATCH_015_TO_001_AFFINE_HAND_MANIFEST.json',
  'HAND_CANDIDATE_MISMATCH_BOOTSTRAP.md'],
 'owners_tilt_and_arbitrary_center_terminal': [
  'CANDIDATE_CAPTURE_AT_ONE_THOUSANDTH_HAND_MANIFEST.json',
  'HAND_EXACT_CENTER_SQUARE_COMPLETION.md',
  'HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md'],
 'original_radius_and_complete_equality': [
  'FIXED_CEILING_TRANSFER_HAND_MANIFEST.json',
  'EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md',
  'COMPLETE_EQUALITY_PARAMETER_DOMAIN.md',
  'COMPLETE_EQUALITY_PARAMETER_DOMAIN_INDEPENDENT_AUDIT.md'],
}

# The current inventory in BASE is authoritative when an archival copy
# with the same filename exists in proof_reference. All other direct
# sources use this same explicit, reproducible search order.
def locate(name):
    assert '/' not in name and '\\' not in name, name
    for root in ROOTS:
        p=root/name
        if p.is_file(): return p
    raise FileNotFoundError('Required hand appendix is absent: '+name)

def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1<<20),b''):h.update(block)
    return h.hexdigest()

def meta(p): return {'sha256':digest(p),'bytes':p.stat().st_size}

def load(name): return json.loads(locate(name).read_text())

def accepted_status(status):
    if not isinstance(status,str): return False
    return ((status in ('PASS','COMPLETE') or
             status.startswith(('PASS_','COMPLETE_'))) and
            not any(word in status for word in ('INCOMPLETE','FAIL','PENDING')))

main=locate('UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md')
text=main.read_text()
assert '**The unrestricted sharp-radius theorem and the complete equality' in text
assert '**Theorem.**' in text
for phrase in ['pending lemma: M1','conditional only on M1',
               'Pending lemma M1','Required statement M1',
               'Assume M1.','Pending complete table and independent review']:
    assert phrase not in text, phrase

# Completion is checked against the independently frozen stage bindings,
# not inferred from a positive cyclic constant or from this main text.
expected={
 'MISMATCH_026_TO_01_AFFINE_HAND_MANIFEST.json':
  (131255,123168,401,354398,2903573,F(18173,2712000000)),
 'MISMATCH_015_TO_001_AFFINE_HAND_MANIFEST.json':
  (144709,129368,456,399773,3183184,F(522599,240000000000)),
}
for name,(rows,chains,arcs,polys,coeffs,reserve) in expected.items():
    d=load(name)
    status=d.get('status','')
    assert accepted_status(status), (name,status)
    assert d['rows']==rows and d['angle_chains']==chains and d['arcs']==arcs
    assert d['polynomials']==polys and d['coefficients']==coeffs
    assert F(d['strict_contraction_reserve'])==reserve

mainhash=digest(main)
review_files=['unrestricted_eight_hand_dependency_independent_audit.json',
              'unrestricted_eight_root_core_equality_independent_binding.json']
for name in review_files:
    d=load(name)
    status=d.get('status','')
    assert accepted_status(status), (name,status)
    # Both independent authors bind this exact main file explicitly.
    assert d['sha256']['UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md']==mainhash, \
        (name,'main SHA mismatch')

files={}; groups=defaultdict(list)
for group,names in GROUPS.items():
    for name in names:
        p=locate(name); record=meta(p)
        assert name not in files or files[name]==record
        files[name]=record;groups[group].append(name)
links=sorted(set(re.findall(r'\]\(([^()]+\.(?:md|py))\)',text)))
for name in links:
    files[name]=meta(locate(name))

child_names=sorted(name for name in files
                   if name.endswith('MANIFEST.json') or
                   name.endswith('_closure_manifest.json') or
                   name=='short_whole_word_hand_assembly_audit.json')
children={}
for name in child_names:
    d=load(name)
    status=d.get('status',d.get('hand_word_status',''))
    assert accepted_status(status), (name,status)
    children[name]={'status':status,'sha256':files[name]['sha256']}

report={
 'status':'PASS_UNRESTRICTED_HAND_PROOF_AND_COMPLETE_EQUALITY_CLASSIFICATION',
 'scope':'Eight closed unit squares with pairwise disjoint open interiors in an arbitrary circle; all orientations and positions; sharp radius and the exact necessary/sufficient equality family up to isometry and relabeling.',
 'mathematical_form':'Continuous hand arguments with supplied fixed rational scalar and univariate Bernstein tables. The tables are part of the proof. This manifest binds those sources and their completed independent reviews; it is not itself a geometric proof or a replacement for any table.',
 'pending_mathematical_gates':[],
 'exact_constant':{'definition':'Unique admissible stationary zero in UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md (1.1)-(1.3).',
   'coarse_lower_q':'7831/2000','capture_ceiling_q':'1957767069/500000000',
   'frame_ceiling_q':'9789/2500',
   'sharp_bracket_center_q':'97888353437936883163/25000000000000000000',
   'sharp_bracket_lower_offset':'-1/5000000000000000',
   'sharp_bracket_upper_offset':'1/10000000000000000'},
 'equality':{'classification':'Exactly the five-variable explicit domain in main Section12, equivalently COMPLETE_EQUALITY_PARAMETER_DOMAIN.md; both necessity and sufficiency.',
   'unique_data':['admissible stationary root','normalized five exterior anchors','two exterior orientation groups'],
   'free_parameters':['central x','central y','central tan(theta/2)',
                      'T vertical coordinate z','G f-coordinate eta'],
   'contains_full_dimension_noncongruent_box':5},
 'mismatch_chain':['13/50','1/10','3/200','1/1000'],
 'mismatch_stage_reserves':{
   '13/50_to_1/10':'18173/2712000000',
   '1/10_to_3/200':'2287/6400000000',
   '3/200_to_1/1000':'522599/240000000000'},
 'fixed_interface_checks':{'strict_rational_comparisons':44,
   'four_type_order':['C','L','M','H'],'seven_walks':16384,
   'seven_walk_floor':'3881/625','admissible_quarter_words':70,
   'dihedral_quarter_classes':7},
 'excluded_proof_premises':[
   'earlier central-core adaptive subdivision certificate',
   'earlier piecewise-linear four-type interval certificate',
   'radial-necklace / three-core / short-two-core interval exclusions',
   'earlier 123-box role-potential capture',
   'discovery samples, optimizer minima, failed rows or adaptive state trees',
   'Lean formalization or CI success'],
 'historical_status_policy':'Frozen component notes may retain historical pending/computer-assisted wording. Only the explicit completed hand implications in the main dependency graph are used, and their former external capture premises are now discharged by the named hand stages. Frozen source hashes remain unchanged.',
 'groups':dict(groups),'child_manifests':children,
 'direct_main_links':links,'files':dict(sorted(files.items()))
}
assert F(report['exact_constant']['sharp_bracket_center_q'])==F('3.91553413751747532652')
OUT.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'status':report['status'],'files':len(files),
                  'child_manifests':len(children),'main_sha256':mainhash,
                  'manifest_sha256':digest(OUT)},sort_keys=True))
