#!/usr/bin/env python3
"""Write direct candidate-stage exports from the complete table theorems."""
from pathlib import Path
root=Path(__file__).resolve().parents[2]
prefix='SquaresInCircles.Eight.Generated.Affine.'
aliases={'coarse':'CandidateCoarseMismatch','middle':'Mismatch026To01Affine',
         'intermediate':'Mismatch01To015Affine','final':'Mismatch015To001Affine',
         'g_lower':'GLowerAffine','g_upper':'GUpperAffine','t_lower':'TLowerAffine',
         't_upper':'TUpperAffine','h_lower':'HLowerAffine','d_upper':'DUpperAffine'}
lines=['module','','public import SquaresInCircles.Eight.Generated.AffineCovers',
       'public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Enhanced',
       'public import SquaresInCircles.Eight.Candidate.Mismatch','',
       '/-! Complete F7/F8 affine-table instances in their dependency order.',
       'All Lean source and generated decision proof scripts remain uncompiled. -/','',
       '@[expose] public section','noncomputable section',
       'namespace SquaresInCircles.Eight.Candidate.Tables',
       'open Arithmetic','open scoped BigOperators','']
def hypdefs(hyps):
    out=['  have he : C.tangent 6≤0 := hE']
    if 'G' in hyps:out += ['  have hgl : -4/5<C.tangent 1 := hG.1','  have hgu : C.tangent 1< -1/20 := hG.2']
    if 'T' in hyps:out += ['  have htl : 1/20<C.tangent 4 := hT.1','  have htu : C.tangent 4<4/5 := hT.2']
    if 'HD' in hyps:out += ['  have hhl : 1/2<C.tangent 0 := hHD.1','  have hdu : C.tangent 5< -1/2 := hHD.2']
    if 'Signs' in hyps:out += [
        '  have hhs : 0<C.tangent 0 := hSigns.1',
        '  have hgs : C.tangent 1<0 := hSigns.2.1',
        '  have has : 0<C.tangent 2 := hSigns.2.2.1',
        '  have hbs : C.tangent 3<0 := hSigns.2.2.2.1',
        '  have hts : 0<C.tangent 4 := hSigns.2.2.2.2.1',
        '  have hds : C.tangent 5<0 := hSigns.2.2.2.2.2']
    return out
def cutproof(ns):return [
    f'  have hcuts : ∀ i, ({ns}.meta.cuts i).Mem (C.tangent i) := by',
    '    intro i','    have hb := C.tangent_mem i',
    f'    fin_cases i <;> norm_num [{ns}.meta,QInterval.Mem] <;> constructor <;> linarith']
def diffproof(ns,restricted=False):
    out=[f'  have hdiff : ∀ i, ({ns}.meta.differenceRange i).Mem (delta F.theta i) := by','    intro i']
    if not restricted:return out+['    have hb := abs_le.mp (F.delta_small i).le',f'    fin_cases i <;> simpa [{ns}.meta,QInterval.Mem] using hb']
    return out+[
        '    by_cases hi : i∈charged',
        '    · have hb := abs_le.mp ((delta_le_mismatch F.theta hi).trans hS)',
        f'      fin_cases i <;> norm_num [charged] at hi <;> simpa [{ns}.meta,QInterval.Mem] using hb',
        '    · have hb := abs_le.mp (F.delta_small i).le',
        f'      fin_cases i <;> norm_num [charged] at hi <;> simpa [{ns}.meta,QInterval.Mem] using hb']
def axisproof(ns,owners=False):
    out=[f'  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →',
        f'      ForwardAxis.ofIndex j∈{ns}.meta.allowedAxes i := by','    intro i j hj']
    if not owners:return out+[f'    fin_cases i <;> fin_cases j <;> simp [{ns}.meta,ForwardAxis.ofIndex]']
    return out+[
        '    by_cases hi : i∈zeroEdges',
        '    · have ho := hZero i hi j hj',
        f'      fin_cases i <;> fin_cases j <;> norm_num [zeroEdges,zeroOwners,{ns}.meta,ForwardAxis.ofIndex] at hi ho ⊢',
        '    · by_cases hq : i∈otherQuarterEdges',
        '      · have ho := hQuarter i hq j hj',
        f'        fin_cases i <;> fin_cases j <;> norm_num [otherQuarterEdges,quarterOwners,{ns}.meta,ForwardAxis.ofIndex] at hq ho ⊢',
        f'      · fin_cases i <;> fin_cases j <;> norm_num [zeroEdges,otherQuarterEdges,{ns}.meta,ForwardAxis.ofIndex] at hi hq ⊢']
def getbound(ns,beta,gamma=None):
    out=[f'  have hb : ∀ i, ({ns}.meta.charge i:ℝ)=charge ({beta}) i := by',
        f'    intro i; fin_cases i <;> norm_num [{ns}.meta,charge,charged,coarseBeta]',
        f'  have P := {ns}.charged_bound C F ({beta}) hb hcuts hdiff haxes']
    if gamma:out += [f'  simpa [{ns}.meta,{gamma},coarseBeta] using P','']
    return out
failure=[('g_lower',[], 'C.tangent G≤ -4/5'),('g_upper',[],'-1/20≤C.tangent G'),
         ('t_lower',['G'],'C.tangent T≤1/20'),('t_upper',['G'],'4/5≤C.tangent T'),
         ('h_lower',['G','T'],'C.tangent H≤1/2'),('d_upper',['G','T'],'-1/2≤C.tangent D')]
for name,hyps,fail in failure:
    ns=prefix+aliases[name]
    lines += [f'theorem {name}_excluded {{C : BoundaryCycle Q1}} (F : Frame C)',
        '    (hE : EHalf C)'+''.join(f' (h{x} : {x}Cut C)' for x in hyps),
        f'    (hFail : {fail}) : False := by']
    lines += hypdefs(hyps)+['  change '+fail.replace(' G',' 1').replace(' T',' 4').replace(' H',' 0').replace(' D',' 5')+' at hFail']
    lines += cutproof(ns)+diffproof(ns)+axisproof(ns)+getbound(ns,'0')
    lines += ['  have hbudget := P.cyclic',f'  norm_num [{ns}.meta,Fin.sum_univ_succ] at hbudget',
        '  have hpi := two_pi_lt_710_over_113','  linarith','']
lines += [
    'theorem g_cut {C : BoundaryCycle Q1} (F : Frame C) (hE : EHalf C) : GCut C := by',
    '  constructor','  · by_contra! hFail; exact g_lower_excluded F hE hFail',
    '  · by_contra! hFail; exact g_upper_excluded F hE hFail','',
    'theorem t_cut {C : BoundaryCycle Q1} (F : Frame C) (hE : EHalf C) (hG : GCut C) : TCut C := by',
    '  constructor','  · by_contra! hFail; exact t_lower_excluded F hE hG hFail',
    '  · by_contra! hFail; exact t_upper_excluded F hE hG hFail','',
    'theorem hd_cut {C : BoundaryCycle Q1} (F : Frame C)',
    '    (hE : EHalf C) (hG : GCut C) (hT : TCut C) : HDCut C := by',
    '  constructor','  · by_contra! hFail; exact h_lower_excluded F hE hG hT hFail',
    '  · by_contra! hFail; exact d_upper_excluded F hE hG hT hFail','']
stages=[('coarse',['G','T'],'coarseBeta','coarseGamma',None),
        ('middle',['G','T','HD'],'1/400','middleGamma','13/50'),
        ('intermediate',['G','T','Signs'],'1/200','intermediateGamma','1/10'),
        ('final',['G','T','HD','Signs'],'1/20','finalGamma','3/200')]
for name,hyps,beta,gamma,S in stages:
    ns=prefix+aliases[name]
    lines += [f'noncomputable def {name}_bound {{C : BoundaryCycle Q1}} (F : Frame C)',
        '    (hE : EHalf C)'+''.join(f' (h{x} : '+('Signs C)' if x=='Signs' else 'HDCut C)' if x=='HD' else f'{x}Cut C)') for x in hyps)]
    if name=='final':lines += ['    (hZero : ZeroOwners C) (hQuarter : QuarterOwners C)']
    if S:lines += [f'    (hS : mismatch F.theta≤{S})']
    lines += [f'    : ChargedBound C F ({beta}) {gamma} := by']
    lines += hypdefs(hyps)+cutproof(ns)+diffproof(ns,bool(S))+axisproof(ns,name=='final')+getbound(ns,beta,gamma)
ns=prefix+'CandidateCoarseMismatch.Enhanced'
original=prefix+'CandidateCoarseMismatch'
lines += ['noncomputable def enhanced_bound {C : BoundaryCycle Q1} (F : Frame C)',
    '    (hE : EHalf C) (hG : GCut C) (hT : TCut C) :',
    '    ChargedBound C F coarseBeta enhancedGamma := by']
lines += hypdefs(['G','T'])+cutproof(original)+diffproof(original)+axisproof(original)
lines += [f'  exact {ns}.charged_bound C F hcuts hdiff haxes','',
    'end SquaresInCircles.Eight.Candidate.Tables','']
(root/'SquaresInCircles/Eight/Generated/AffineBudgets.lean').write_text('\n'.join(lines))
