module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAETD2CommonEndpoints
public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAETD2Stress
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2SameBlock

/-!
# The three negative forms and the common positive charge

Uncompiled transcription of Sections 4--5 of the joint-negative TD2
proof. The B comparison keeps its actual ordered pair, including the
switch at m = lambdaB. The secant sine estimate uses the full remaining
negative budget, so it also covers both negative primaries at once.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.BlockBounds
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope OrdinaryNegativeSlope Source
open Certificate (Row)

def canonicalQ (r s : ℝ) : Fin 3→ℝ := ![1,sec r,sec s]
def charge (f : Row) (z : ℝ) : ℝ := (109/200)*Explicit.cap f z

theorem zero_slope_upper {k q : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hq : 1≤q) : Vd R k q 0<(119/100)*q := by
  have hq0 : 0<q := by linarith
  have hr0 : 0≤k/q := div_nonneg (by linarith [hk.1]) hq0.le
  have hr : k/q≤751/1000 := (div_le_iff₀ hq0).2 (by nlinarith [hk.2])
  have hm := NegativeAPositiveTD.Curvature.shapeD0q_monotone
    (show k/q∈Icc (0:ℝ) 1 from ⟨hr0,by linarith⟩)
    (show (751/1000:ℝ)∈Icc (0:ℝ) 1 by norm_num) hr
  have hshape : (5/4:ℝ)<shape (751/1000) := by
    have hh := shape_sq (751/1000:ℝ)
    nlinarith [shape_pos (751/1000:ℝ)]
  have hb : NegativeAPositiveTD.Curvature.shapeD0q (751/1000)<119/100 := by
    dsimp [NegativeAPositiveTD.Curvature.shapeD0q]
    apply (div_lt_iff₀ (shape_pos _)).2
    nlinarith [Secondary.radius_bounds.2]
  have hmul := mul_lt_mul_of_pos_left (hm.trans_lt hb) hq0
  rw [Vd_normalized hq0]
  simpa [NegativeAPositiveTD.Curvature.shapeD0q,VaryingBFunctions.root,
    OrdinaryCurvatureBounds.shape,mul_comm] using hmul

theorem B_negative_lower {k m q d : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hq : q∈Icc (1:ℝ) (539/500))
    (hm : k≤m) (hmhi : m≤69/50) (hd : d∈Icc 0 frameCap) :
    V R k q d≤V R (min q m) (max q m) d := by
  have hk0 : 0<k := by linarith [hk.1]
  have hq0 : 0<q := by linarith [hq.1]
  have hkq : k≤q := by linarith [hk.2,hq.1]
  have hqk : q≤2*k := by linarith [hk.1,hq.2]
  rcases le_total m q with hmq|hqm
  · rw [min_eq_right hmq,max_eq_left hmq]
    exact V_monotone_smaller (Real.sqrt_nonneg qCap) hq0 hd
      ⟨by linarith,hkq⟩ ⟨by linarith,hmq⟩ hm
  · rw [min_eq_left hqm,max_eq_right hqm]
    have hchord := V_chord_lower hq0 hqm (show m≤2*q by linarith [hq.1]) hd
    have htangent := V_tangent_zero hk0 hkq hqk hd
    have hupper := mul_le_mul_of_nonneg_right (zero_slope_upper hk hq.1).le hd.1
    have hqd : 0≤q*d := mul_nonneg hq0.le hd.1
    nlinarith

theorem negative_index (f : Row) (atG atH : Bool) {r s z d : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hd : d∈Icc 0 frameCap) (i : Fin 4) :
    ∃j : Fin 3,V R (Explicit.k f z) (canonicalQ r s j) d≤
      V R (pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i)
        (qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i) d := by
  rcases Explicit.ranges f hz with ⟨hk,hkc,hc,hkm,hm,hcap,hstrict⟩
  have hl := lambda_bounds atG atH hr hs hH
  fin_cases i
  · cases atH
    · exact ⟨0,by simp [pWeights,qWeights,canonicalQ,lambdaH]⟩
    · exact ⟨2,by simp [pWeights,qWeights,canonicalQ,lambdaH]⟩
  · cases atG
    · exact ⟨0,by simp [pWeights,qWeights,canonicalQ,lambdaG]⟩
    · exact ⟨1,by simp [pWeights,qWeights,canonicalQ,lambdaG]⟩
  · have hh := B_negative_lower hk hl.2.1 hkm (hm.trans hcap) hd
    cases atG
    · exact ⟨1,by simpa [pWeights,qWeights,canonicalQ,lambdaB] using hh⟩
    · exact ⟨0,by simpa [pWeights,qWeights,canonicalQ,lambdaB] using hh⟩
  · exact ⟨0,by simp [pWeights,qWeights,canonicalQ]⟩

theorem cap_lower (f : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    (539/500:ℝ)≤Explicit.cap f z := by
  cases f
  · have hh := Explicit.low_m_ranges hz
    change (539/500:ℝ)≤Explicit.m .low z
    linarith [hh.1]
  · norm_num [Explicit.cap]
  · norm_num [Explicit.cap]

theorem charge_bounds (f : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    0≤charge f z ∧ charge f z≤7521/10000 ∧
      (f≠.low → charge f z=58751/100000) := by
  have hlo := cap_lower f hz
  have hhi := (Explicit.ranges f hz).2.2.2.2.2.1
  refine ⟨by dsimp [charge]; positivity,by dsimp [charge]; linarith,?_⟩
  intro hf
  cases f <;> norm_num [charge,Explicit.cap] at *

theorem q_le_cap (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (i : Fin 4) :
    qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i≤Explicit.cap f z := by
  have hcap := cap_lower f hz
  have hm := (Explicit.ranges f hz).2.2.2.2.1
  have hl := lambda_bounds atG atH hr hs hH
  fin_cases i
  · exact hl.2.2.1.2.trans hcap
  · exact hl.1.2.trans hcap
  · exact max_le (hl.2.1.2.trans hcap) hm
  · change (1:ℝ)≤Explicit.cap f z
    linarith

theorem positive_lower (f : Row) (atG atH : Bool) {r s z d : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hd : d∈Icc 0 frameCap) (i : Fin 4) :
    -charge f z*d≤PositiveTD.Hybrid.positive R (diagonal-1/2)
      (pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s) 3 i d := by
  have hc := q_le_cap f atG atH hz hr hs hH i
  have hp := pair_domain f atG atH hz hr hs hH i
  by_cases hi : i=3
  · subst i
    have hcap := cap_lower f hz
    have hcoef : diagonal-1/2≤charge f z := by
      dsimp [charge]
      linarith [Secondary.diagonal_bounds.2]
    simpa [PositiveTD.Hybrid.positive] using
      mul_le_mul_of_nonneg_right (neg_le_neg hcoef) hd.1
  · have hu := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap)
      radius_sq.le hp.1 hp.2.1 (show _≤2*_ by linarith [hp.2.2,hp.1]) hd
    have hm := mul_le_mul_of_nonneg_right hc hd.1
    simp only [PositiveTD.Hybrid.positive,if_neg hi]
    dsimp [charge]
    nlinarith

theorem secant_sine_remaining {x S : ℝ} (hx : x∈Icc 0 frameCap)
    (hS : S∈Icc 0 frameCap) (hxS : x≤S) :
    sec x*Real.sin (frameCap-S)<129/200 := by
  have hc : 0<Real.cos x := by linarith [(transport_trig hx).1]
  have hsec : 0≤sec x := div_nonneg (by norm_num) hc.le
  have hsine : Real.sin (frameCap-S)≤Real.sin (frameCap-x) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_gt_three,hS.2]
    · dsimp [frameCap] at *
      nlinarith [Real.pi_gt_three,hx.1]
    · linarith
  have hmul := mul_le_mul_of_nonneg_left hsine hsec
  have hid : sec x*Real.sin (frameCap-x)=
      Real.sin frameCap-Real.cos frameCap*Real.tan x := by
    rw [Real.sin_sub]
    dsimp [sec,SecantNormCurvature.secant]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
    ring
  rw [hid] at hmul
  have htan : 0≤Real.tan x := SecantCoordinate.tan_nonnegative hx
  have ht := transport_trig (show frameCap∈Icc 0 frameCap by
    exact ⟨by norm_num [frameCap],le_rfl⟩)
  have hprod := mul_nonneg (show 0≤Real.cos frameCap by linarith [ht.1]) htan
  linarith [ht.2.2.2.1]

theorem same_block_sine (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hS : r+s≤frameCap) (i : Fin 4) :
    qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i*Real.sin (frameCap-(r+s))≤
      pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i := by
  rcases Explicit.ranges f hz with ⟨hk,hkc,hc,hkm,hm,hcap,hstrict⟩
  have htotal : r+s∈Icc 0 frameCap := ⟨add_nonneg hr.1 hs.1,hS⟩
  have hr' : r∈Icc 0 frameCap := ⟨hr.1,by linarith [hs.1]⟩
  have hzero := secant_sine_remaining (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    htotal htotal.1
  simp only [sec,SecantNormCurvature.secant,Real.cos_zero,div_one,one_mul] at hzero
  have hA := secant_sine_remaining hr' htotal (by linarith [hs.1])
  have hE := secant_sine_remaining hs htotal (by linarith [hr.1])
  have hG : lambdaG atG r*Real.sin (frameCap-(r+s))≤Explicit.k f z := by
    cases atG <;> simp only [lambdaG,if_true,if_false] <;> linarith [hk.1]
  have hH : lambdaH atH s*Real.sin (frameCap-(r+s))≤Explicit.k f z := by
    cases atH <;> simp only [lambdaH,if_true,if_false] <;> linarith [hk.1]
  have hB : lambdaB atG r*Real.sin (frameCap-(r+s))≤Explicit.k f z := by
    cases atG <;> simp only [lambdaB,if_true,if_false] <;> linarith [hk.1]
  fin_cases i
  · exact hH
  · exact hG
  · change max (lambdaB atG r) (Explicit.m f z)*Real.sin (frameCap-(r+s))≤
      min (lambdaB atG r) (Explicit.m f z)
    rcases le_total (Explicit.m f z) (lambdaB atG r) with hh|hh
    · rw [max_eq_left hh,min_eq_right hh]
      exact hB.trans hkm
    · rw [max_eq_right hh,min_eq_left hh]
      have hλ : 1≤lambdaB atG r := by
        cases atG
        · exact (secant_short hr).1
        · simp [lambdaB]
      have hsin := (transport_trig (show frameCap-(r+s)∈Icc 0 frameCap from
        ⟨by linarith,by linarith [htotal.1]⟩)).2.2.1
      have hupper := mul_le_mul_of_nonneg_right (hm.trans hcap) hsin
      nlinarith
  · change (1:ℝ)*Real.sin (frameCap-(r+s))≤Explicit.k f z
    linarith [hk.1]

theorem unit_negative_growth {k x y : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hx : x∈Icc 0 frameCap) (hy : y∈Icc 0 frameCap) (hxy : x≤y) :
    (16/25)*(y-x)≤V R k 1 y-V R k 1 x := by
  have hk0 : 0<k := by linarith [hk.1]
  apply derivative_reserve
    (fun t ht => (V_hasDerivAt (R:=R) hk0 (by norm_num) ht).continuousAt.continuousWithinAt)
    (fun t ht => V_hasDerivAt (R:=R) hk0 (by norm_num) (Ioo_subset_Icc_self ht))
    (fun t ht => ?_) hx hy hxy
  have hh := NegativeAPositiveTD.NegativeSlope.lower_bound .ABfull hk0
    (show k≤1 by linarith [hk.2]) (show (1:ℝ)≤2*k by linarith [hk.1])
    (show (NegativeAPositiveTD.NegativeSlope.lowerRatio .ABfull:ℝ)*1≤k by
      simpa [NegativeAPositiveTD.NegativeSlope.lowerRatio] using hk.1)
    (show t∈Icc 0 (NegativeAPositiveTD.NegativeSlope.lowerAngle .ABfull:ℝ) by
      simpa [NegativeAPositiveTD.NegativeSlope.lowerAngle,frameCap] using Ioo_subset_Icc_self ht)
  simpa [NegativeAPositiveTD.NegativeSlope.lowerValue] using hh.le

theorem same_negative (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤z) (i : Fin 4) :
    V R (pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i) (z-(r+s))≤
    PositiveTD.Hybrid.block R (diagonal-1/2)
      (pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s) 3 i
      (frameCap-z) (frameCap-(r+s)) := by
  have hz' := Explicit.frame_domain f hz
  have hp := pair_domain f atG atH hz hr hs hH i
  have htotal := add_nonneg hr.1 hs.1
  by_cases hi : i=3
  · subst i
    have hh := unit_negative_growth (Explicit.ranges f hz).1
      (show z-(r+s)∈Icc 0 frameCap from ⟨by linarith,by linarith [hz'.2]⟩)
      (show frameCap-(r+s)∈Icc 0 frameCap from ⟨by linarith [hz'.2],by linarith⟩)
      (by linarith [hz'.2])
    have hcharge := mul_le_mul_of_nonneg_right
      (show diagonal-1/2≤16/25 by linarith [Secondary.diagonal_bounds.2])
      (show 0≤frameCap-z by linarith [hz'.2])
    simp [PositiveTD.Hybrid.block,pWeights,qWeights]
    linarith
  · have hh := NegativeAPositiveTD.SameBlock.negative_surplus hp.1.le
      (show frameCap-z∈Icc 0 (frameCap-(r+s)) from ⟨by linarith [hz'.2],by linarith⟩)
      (show frameCap-(r+s)∈Icc 0 frameCap from ⟨by linarith [hz'.2],by linarith⟩)
      (same_block_sine f atG atH hz hr hs (hS.trans hz'.2) i)
    simpa [PositiveTD.Hybrid.block,hi,show frameCap-(r+s)-(frameCap-z)=z-(r+s) by ring] using hh

theorem same_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s∈Icc z frameCap) (i : Fin 4) :
    PositiveTD.Hybrid.positive R (diagonal-1/2)
      (pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s) 3 i (r+s-z)≤
    PositiveTD.Hybrid.block R (diagonal-1/2)
      (pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s) 3 i
      (frameCap-z) (frameCap-(r+s)) := by
  have hz' := Explicit.frame_domain f hz
  have hp := pair_domain f atG atH hz hr hs hH i
  have htotal := add_nonneg hr.1 hs.1
  by_cases hi : i=3
  · subst i
    have hh := unit_negative_growth (Explicit.ranges f hz).1
      (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
      (show frameCap-(r+s)∈Icc 0 frameCap from ⟨by linarith [hS.2],by linarith⟩)
      (by linarith [hS.2])
    have hcharge := mul_le_mul_of_nonneg_right
      (show diagonal-1/2≤16/25 by linarith [Secondary.diagonal_bounds.2])
      (show 0≤frameCap-(r+s) by linarith [hS.2])
    simp only [V_zero,sub_zero] at hh
    simp [PositiveTD.Hybrid.positive,PositiveTD.Hybrid.block,pWeights,qWeights]
    linarith
  · have hh := NegativeAPositiveTD.SameBlock.positive_surplus hp.1.le hp.2.2
      (show frameCap-z∈Icc 0 frameCap from ⟨by linarith [hz'.2],by linarith [hz'.1]⟩)
      (show frameCap-(r+s)∈Icc 0 (frameCap-z) from ⟨by linarith [hS.2],by linarith [hS.1]⟩)
    simpa [PositiveTD.Hybrid.positive,PositiveTD.Hybrid.block,hi,
      show frameCap-z-(frameCap-(r+s))=r+s-z by ring] using hh

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.BlockBounds
