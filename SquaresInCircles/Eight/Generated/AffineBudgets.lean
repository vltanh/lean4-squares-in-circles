module

public import SquaresInCircles.Eight.Generated.AffineCovers
public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Enhanced
public import SquaresInCircles.Eight.Candidate.Mismatch

/-! Complete F7/F8 affine-table instances in their dependency order.
All Lean source and generated decision proof scripts remain uncompiled. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Candidate.Tables
open Arithmetic
open scoped BigOperators

theorem g_lower_excluded {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C)
    (hFail : C.tangent G≤ -4/5) : False := by
  have he : C.tangent 6≤0 := hE
  change C.tangent 1≤ -4/5 at hFail
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.GLowerAffine.meta.cuts i).Mem (C.tangent i) := by
    intro i
    have hb := C.tangent_mem i
    fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.GLowerAffine.meta,QInterval.Mem] <;> constructor <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.GLowerAffine.meta.differenceRange i).Mem (delta F.theta i) := by
    intro i
    have hb := abs_le.mp (F.delta_small i).le
    fin_cases i <;> simpa [SquaresInCircles.Eight.Generated.Affine.GLowerAffine.meta,QInterval.Mem] using hb
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.GLowerAffine.meta.allowedAxes i := by
    intro i j hj
    fin_cases i <;> fin_cases j <;> simp [SquaresInCircles.Eight.Generated.Affine.GLowerAffine.meta,ForwardAxis.ofIndex]
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.GLowerAffine.meta.charge i:ℝ)=charge (0) i := by
    intro i; fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.GLowerAffine.meta,charge,charged,coarseBeta]
  have P := SquaresInCircles.Eight.Generated.Affine.GLowerAffine.charged_bound C F (0) hb hcuts hdiff haxes
  have hbudget := P.cyclic
  norm_num [SquaresInCircles.Eight.Generated.Affine.GLowerAffine.meta,Fin.sum_univ_succ] at hbudget
  have hpi := two_pi_lt_710_over_113
  linarith

theorem g_upper_excluded {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C)
    (hFail : -1/20≤C.tangent G) : False := by
  have he : C.tangent 6≤0 := hE
  change -1/20≤C.tangent 1 at hFail
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.GUpperAffine.meta.cuts i).Mem (C.tangent i) := by
    intro i
    have hb := C.tangent_mem i
    fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.GUpperAffine.meta,QInterval.Mem] <;> constructor <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.GUpperAffine.meta.differenceRange i).Mem (delta F.theta i) := by
    intro i
    have hb := abs_le.mp (F.delta_small i).le
    fin_cases i <;> simpa [SquaresInCircles.Eight.Generated.Affine.GUpperAffine.meta,QInterval.Mem] using hb
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.GUpperAffine.meta.allowedAxes i := by
    intro i j hj
    fin_cases i <;> fin_cases j <;> simp [SquaresInCircles.Eight.Generated.Affine.GUpperAffine.meta,ForwardAxis.ofIndex]
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.GUpperAffine.meta.charge i:ℝ)=charge (0) i := by
    intro i; fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.GUpperAffine.meta,charge,charged,coarseBeta]
  have P := SquaresInCircles.Eight.Generated.Affine.GUpperAffine.charged_bound C F (0) hb hcuts hdiff haxes
  have hbudget := P.cyclic
  norm_num [SquaresInCircles.Eight.Generated.Affine.GUpperAffine.meta,Fin.sum_univ_succ] at hbudget
  have hpi := two_pi_lt_710_over_113
  linarith

theorem t_lower_excluded {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C)
    (hFail : C.tangent T≤1/20) : False := by
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  change C.tangent 4≤1/20 at hFail
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.TLowerAffine.meta.cuts i).Mem (C.tangent i) := by
    intro i
    have hb := C.tangent_mem i
    fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.TLowerAffine.meta,QInterval.Mem] <;> constructor <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.TLowerAffine.meta.differenceRange i).Mem (delta F.theta i) := by
    intro i
    have hb := abs_le.mp (F.delta_small i).le
    fin_cases i <;> simpa [SquaresInCircles.Eight.Generated.Affine.TLowerAffine.meta,QInterval.Mem] using hb
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.TLowerAffine.meta.allowedAxes i := by
    intro i j hj
    fin_cases i <;> fin_cases j <;> simp [SquaresInCircles.Eight.Generated.Affine.TLowerAffine.meta,ForwardAxis.ofIndex]
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.TLowerAffine.meta.charge i:ℝ)=charge (0) i := by
    intro i; fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.TLowerAffine.meta,charge,charged,coarseBeta]
  have P := SquaresInCircles.Eight.Generated.Affine.TLowerAffine.charged_bound C F (0) hb hcuts hdiff haxes
  have hbudget := P.cyclic
  norm_num [SquaresInCircles.Eight.Generated.Affine.TLowerAffine.meta,Fin.sum_univ_succ] at hbudget
  have hpi := two_pi_lt_710_over_113
  linarith

theorem t_upper_excluded {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C)
    (hFail : 4/5≤C.tangent T) : False := by
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  change 4/5≤C.tangent 4 at hFail
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.TUpperAffine.meta.cuts i).Mem (C.tangent i) := by
    intro i
    have hb := C.tangent_mem i
    fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.TUpperAffine.meta,QInterval.Mem] <;> constructor <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.TUpperAffine.meta.differenceRange i).Mem (delta F.theta i) := by
    intro i
    have hb := abs_le.mp (F.delta_small i).le
    fin_cases i <;> simpa [SquaresInCircles.Eight.Generated.Affine.TUpperAffine.meta,QInterval.Mem] using hb
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.TUpperAffine.meta.allowedAxes i := by
    intro i j hj
    fin_cases i <;> fin_cases j <;> simp [SquaresInCircles.Eight.Generated.Affine.TUpperAffine.meta,ForwardAxis.ofIndex]
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.TUpperAffine.meta.charge i:ℝ)=charge (0) i := by
    intro i; fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.TUpperAffine.meta,charge,charged,coarseBeta]
  have P := SquaresInCircles.Eight.Generated.Affine.TUpperAffine.charged_bound C F (0) hb hcuts hdiff haxes
  have hbudget := P.cyclic
  norm_num [SquaresInCircles.Eight.Generated.Affine.TUpperAffine.meta,Fin.sum_univ_succ] at hbudget
  have hpi := two_pi_lt_710_over_113
  linarith

theorem h_lower_excluded {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C) (hT : TCut C)
    (hFail : C.tangent H≤1/2) : False := by
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  have htl : 1/20<C.tangent 4 := hT.1
  have htu : C.tangent 4<4/5 := hT.2
  change C.tangent 0≤1/2 at hFail
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.HLowerAffine.meta.cuts i).Mem (C.tangent i) := by
    intro i
    have hb := C.tangent_mem i
    fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.HLowerAffine.meta,QInterval.Mem] <;> constructor <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.HLowerAffine.meta.differenceRange i).Mem (delta F.theta i) := by
    intro i
    have hb := abs_le.mp (F.delta_small i).le
    fin_cases i <;> simpa [SquaresInCircles.Eight.Generated.Affine.HLowerAffine.meta,QInterval.Mem] using hb
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.HLowerAffine.meta.allowedAxes i := by
    intro i j hj
    fin_cases i <;> fin_cases j <;> simp [SquaresInCircles.Eight.Generated.Affine.HLowerAffine.meta,ForwardAxis.ofIndex]
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.HLowerAffine.meta.charge i:ℝ)=charge (0) i := by
    intro i; fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.HLowerAffine.meta,charge,charged,coarseBeta]
  have P := SquaresInCircles.Eight.Generated.Affine.HLowerAffine.charged_bound C F (0) hb hcuts hdiff haxes
  have hbudget := P.cyclic
  norm_num [SquaresInCircles.Eight.Generated.Affine.HLowerAffine.meta,Fin.sum_univ_succ] at hbudget
  have hpi := two_pi_lt_710_over_113
  linarith

theorem d_upper_excluded {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C) (hT : TCut C)
    (hFail : -1/2≤C.tangent D) : False := by
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  have htl : 1/20<C.tangent 4 := hT.1
  have htu : C.tangent 4<4/5 := hT.2
  change -1/2≤C.tangent 5 at hFail
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.DUpperAffine.meta.cuts i).Mem (C.tangent i) := by
    intro i
    have hb := C.tangent_mem i
    fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.DUpperAffine.meta,QInterval.Mem] <;> constructor <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.DUpperAffine.meta.differenceRange i).Mem (delta F.theta i) := by
    intro i
    have hb := abs_le.mp (F.delta_small i).le
    fin_cases i <;> simpa [SquaresInCircles.Eight.Generated.Affine.DUpperAffine.meta,QInterval.Mem] using hb
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.DUpperAffine.meta.allowedAxes i := by
    intro i j hj
    fin_cases i <;> fin_cases j <;> simp [SquaresInCircles.Eight.Generated.Affine.DUpperAffine.meta,ForwardAxis.ofIndex]
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.DUpperAffine.meta.charge i:ℝ)=charge (0) i := by
    intro i; fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.DUpperAffine.meta,charge,charged,coarseBeta]
  have P := SquaresInCircles.Eight.Generated.Affine.DUpperAffine.charged_bound C F (0) hb hcuts hdiff haxes
  have hbudget := P.cyclic
  norm_num [SquaresInCircles.Eight.Generated.Affine.DUpperAffine.meta,Fin.sum_univ_succ] at hbudget
  have hpi := two_pi_lt_710_over_113
  linarith

theorem g_cut {C : BoundaryCycle Q1} (F : Frame C) (hE : EHalf C) : GCut C := by
  constructor
  · by_contra! hFail; exact g_lower_excluded F hE hFail
  · by_contra! hFail; exact g_upper_excluded F hE hFail

theorem t_cut {C : BoundaryCycle Q1} (F : Frame C) (hE : EHalf C) (hG : GCut C) : TCut C := by
  constructor
  · by_contra! hFail; exact t_lower_excluded F hE hG hFail
  · by_contra! hFail; exact t_upper_excluded F hE hG hFail

theorem hd_cut {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C) (hT : TCut C) : HDCut C := by
  constructor
  · by_contra! hFail; exact h_lower_excluded F hE hG hT hFail
  · by_contra! hFail; exact d_upper_excluded F hE hG hT hFail

noncomputable def coarse_bound {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C) (hT : TCut C)
    : ChargedBound C F (coarseBeta) coarseGamma := by
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  have htl : 1/20<C.tangent 4 := hT.1
  have htu : C.tangent 4<4/5 := hT.2
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta.cuts i).Mem (C.tangent i) := by
    intro i
    have hb := C.tangent_mem i
    fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta,QInterval.Mem] <;> constructor <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta.differenceRange i).Mem (delta F.theta i) := by
    intro i
    have hb := abs_le.mp (F.delta_small i).le
    fin_cases i <;> simpa [SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta,QInterval.Mem] using hb
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta.allowedAxes i := by
    intro i j hj
    fin_cases i <;> fin_cases j <;> simp [SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta,ForwardAxis.ofIndex]
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta.charge i:ℝ)=charge (coarseBeta) i := by
    intro i; fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta,charge,charged,coarseBeta]
  have P := SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.charged_bound C F (coarseBeta) hb hcuts hdiff haxes
  simpa [SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta,coarseGamma,coarseBeta] using P

noncomputable def middle_bound {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C) (hT : TCut C) (hHD : HDCut C)
    (hS : mismatch F.theta≤13/50)
    : ChargedBound C F (1/400) middleGamma := by
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  have htl : 1/20<C.tangent 4 := hT.1
  have htu : C.tangent 4<4/5 := hT.2
  have hhl : 1/2<C.tangent 0 := hHD.1
  have hdu : C.tangent 5< -1/2 := hHD.2
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.meta.cuts i).Mem (C.tangent i) := by
    intro i
    have hb := C.tangent_mem i
    fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.meta,QInterval.Mem] <;> constructor <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.meta.differenceRange i).Mem (delta F.theta i) := by
    intro i
    by_cases hi : i∈charged
    · have hb := abs_le.mp ((delta_le_mismatch F.theta hi).trans hS)
      fin_cases i <;> norm_num [charged] at hi <;> simpa [SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.meta,QInterval.Mem] using hb
    · have hb := abs_le.mp (F.delta_small i).le
      fin_cases i <;> norm_num [charged] at hi <;> simpa [SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.meta,QInterval.Mem] using hb
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.meta.allowedAxes i := by
    intro i j hj
    fin_cases i <;> fin_cases j <;> simp [SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.meta,ForwardAxis.ofIndex]
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.meta.charge i:ℝ)=charge (1/400) i := by
    intro i; fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.meta,charge,charged,coarseBeta]
  have P := SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.charged_bound C F (1/400) hb hcuts hdiff haxes
  simpa [SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.meta,middleGamma,coarseBeta] using P

noncomputable def intermediate_bound {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C) (hT : TCut C) (hSigns : Signs C)
    (hS : mismatch F.theta≤1/10)
    : ChargedBound C F (1/200) intermediateGamma := by
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  have htl : 1/20<C.tangent 4 := hT.1
  have htu : C.tangent 4<4/5 := hT.2
  have hhs : 0<C.tangent 0 := hSigns.1
  have hgs : C.tangent 1<0 := hSigns.2.1
  have has : 0<C.tangent 2 := hSigns.2.2.1
  have hbs : C.tangent 3<0 := hSigns.2.2.2.1
  have hts : 0<C.tangent 4 := hSigns.2.2.2.2.1
  have hds : C.tangent 5<0 := hSigns.2.2.2.2.2
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.meta.cuts i).Mem (C.tangent i) := by
    intro i
    have hb := C.tangent_mem i
    fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.meta,QInterval.Mem] <;> constructor <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.meta.differenceRange i).Mem (delta F.theta i) := by
    intro i
    by_cases hi : i∈charged
    · have hb := abs_le.mp ((delta_le_mismatch F.theta hi).trans hS)
      fin_cases i <;> norm_num [charged] at hi <;> simpa [SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.meta,QInterval.Mem] using hb
    · have hb := abs_le.mp (F.delta_small i).le
      fin_cases i <;> norm_num [charged] at hi <;> simpa [SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.meta,QInterval.Mem] using hb
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.meta.allowedAxes i := by
    intro i j hj
    fin_cases i <;> fin_cases j <;> simp [SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.meta,ForwardAxis.ofIndex]
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.meta.charge i:ℝ)=charge (1/200) i := by
    intro i; fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.meta,charge,charged,coarseBeta]
  have P := SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.charged_bound C F (1/200) hb hcuts hdiff haxes
  simpa [SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.meta,intermediateGamma,coarseBeta] using P

noncomputable def final_bound {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C) (hT : TCut C) (hHD : HDCut C) (hSigns : Signs C)
    (hZero : ZeroOwners C) (hQuarter : QuarterOwners C)
    (hS : mismatch F.theta≤3/200)
    : ChargedBound C F (1/20) finalGamma := by
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  have htl : 1/20<C.tangent 4 := hT.1
  have htu : C.tangent 4<4/5 := hT.2
  have hhl : 1/2<C.tangent 0 := hHD.1
  have hdu : C.tangent 5< -1/2 := hHD.2
  have hhs : 0<C.tangent 0 := hSigns.1
  have hgs : C.tangent 1<0 := hSigns.2.1
  have has : 0<C.tangent 2 := hSigns.2.2.1
  have hbs : C.tangent 3<0 := hSigns.2.2.2.1
  have hts : 0<C.tangent 4 := hSigns.2.2.2.2.1
  have hds : C.tangent 5<0 := hSigns.2.2.2.2.2
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.meta.cuts i).Mem (C.tangent i) := by
    intro i
    have hb := C.tangent_mem i
    fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.meta,QInterval.Mem] <;> constructor <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.meta.differenceRange i).Mem (delta F.theta i) := by
    intro i
    by_cases hi : i∈charged
    · have hb := abs_le.mp ((delta_le_mismatch F.theta hi).trans hS)
      fin_cases i <;> norm_num [charged] at hi <;> simpa [SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.meta,QInterval.Mem] using hb
    · have hb := abs_le.mp (F.delta_small i).le
      fin_cases i <;> norm_num [charged] at hi <;> simpa [SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.meta,QInterval.Mem] using hb
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.meta.allowedAxes i := by
    intro i j hj
    by_cases hi : i∈zeroEdges
    · have ho := hZero i hi j hj
      fin_cases i <;> fin_cases j <;> norm_num [zeroEdges,zeroOwners,SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.meta,ForwardAxis.ofIndex] at hi ho ⊢
    · by_cases hq : i∈otherQuarterEdges
      · have ho := hQuarter i hq j hj
        fin_cases i <;> fin_cases j <;> norm_num [otherQuarterEdges,quarterOwners,SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.meta,ForwardAxis.ofIndex] at hq ho ⊢
      · fin_cases i <;> fin_cases j <;> norm_num [zeroEdges,otherQuarterEdges,SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.meta,ForwardAxis.ofIndex] at hi hq ⊢
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.meta.charge i:ℝ)=charge (1/20) i := by
    intro i; fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.meta,charge,charged,coarseBeta]
  have P := SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.charged_bound C F (1/20) hb hcuts hdiff haxes
  simpa [SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.meta,finalGamma,coarseBeta] using P

noncomputable def enhanced_bound {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C) (hT : TCut C) :
    ChargedBound C F coarseBeta enhancedGamma := by
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  have htl : 1/20<C.tangent 4 := hT.1
  have htu : C.tangent 4<4/5 := hT.2
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta.cuts i).Mem (C.tangent i) := by
    intro i
    have hb := C.tangent_mem i
    fin_cases i <;> norm_num [SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta,QInterval.Mem] <;> constructor <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta.differenceRange i).Mem (delta F.theta i) := by
    intro i
    have hb := abs_le.mp (F.delta_small i).le
    fin_cases i <;> simpa [SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta,QInterval.Mem] using hb
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta.allowedAxes i := by
    intro i j hj
    fin_cases i <;> fin_cases j <;> simp [SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta,ForwardAxis.ofIndex]
  exact SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Enhanced.charged_bound C F hcuts hdiff haxes

end SquaresInCircles.Eight.Candidate.Tables
