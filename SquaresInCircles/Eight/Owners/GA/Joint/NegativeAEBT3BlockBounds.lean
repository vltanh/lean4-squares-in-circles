module

public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAEBT3Penalty
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAEBT3SourceData
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2BlockBounds

/-!
# Eight squares: canonical negative forms and the actual BT3 positive charge

The charge retains the combined primary magnitude S. The B pair
keeps the actual ordering of its two coefficients; the single ordinary
D case has pair (c,1). Same-block reduction is used only for ordinary
blocks, leaving the distinguished D term separated.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.BlockBounds
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope Source
open Certificate (Row)

abbrev canonicalQ := JointNegativeAETD2.BlockBounds.canonicalQ

theorem B_negative_lower {k m q d : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hq : q∈Icc (1:ℝ) (539/500))
    (hm : k≤ m) (hmhi : m≤7/5) (hd : d∈Icc 0 frameCap) :
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
    have hupper := mul_le_mul_of_nonneg_right
      (JointNegativeAETD2.BlockBounds.zero_slope_upper hk hq.1).le hd.1
    have hqd := mul_nonneg hq0.le hd.1
    nlinarith

theorem negative_index (f : Row) (atG atH : Bool) {r s z d : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hd : d∈Icc 0 frameCap) (i : Fin 5) :
    ∃j : Fin 3,V R (Explicit.k f z) (canonicalQ r s j) d≤
      V R (pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i)
        (qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i) d := by
  have hc := Explicit.ranges f hz
  have hl := JointNegativeAETD2.Source.lambda_bounds atG atH hr hs hH
  fin_cases i
  · cases atH
    · exact ⟨0,by simp [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,
        lambdaH,JointNegativeAETD2.Source.lambdaH]⟩
    · exact ⟨2,by simp [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,
        lambdaH,JointNegativeAETD2.Source.lambdaH]⟩
  · cases atG
    · exact ⟨0,by simp [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,
        lambdaG,JointNegativeAETD2.Source.lambdaG]⟩
    · exact ⟨1,by simp [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,
        lambdaG,JointNegativeAETD2.Source.lambdaG]⟩
  · have hh := B_negative_lower hc.k_domain hl.2.1 hc.k_le_m (hc.m_le_c.trans hc.c_domain.2) hd
    cases atG
    · exact ⟨1,by simpa [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,
        lambdaB,JointNegativeAETD2.Source.lambdaB] using hh⟩
    · exact ⟨0,by simpa [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,
        lambdaB,JointNegativeAETD2.Source.lambdaB] using hh⟩
  · refine ⟨0,?_⟩
    by_cases ho : ordinaryD atH (Explicit.c f z)
    · simp only [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,
        Fin.reduceFinMk,Fin.isValue,Matrix.cons_val,ho,↓reduceIte]
      exact V_monotone_smaller (Real.sqrt_nonneg qCap) (q:=1) (by norm_num) hd
        ⟨by linarith [hc.k_domain.1],by linarith [hc.k_domain.2]⟩
        ⟨by linarith [hc.c_domain.1],ho.2.le⟩ (hc.k_le_m.trans hc.m_le_c)
    · simp [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,ho]
  · exact ⟨0,by simp [pWeights,qWeights,canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ]⟩

theorem cost_max_coefficient {c S : ℝ} (hS : S∈Icc 0 frameCap) :
    (109/200)*max (sec S) c≤Penalty.cost c S := by
  have hs := (JointNegativeAETD2.CommonGain.full_secant_domain hS).1
  by_cases hc : c<1
  · rw [max_eq_left (by linarith),Penalty.cost,ite_eq_left hc]
  · simp only [Penalty.cost,hc,↓reduceIte]
    rcases le_total (sec S) c with h|h
    · rw [max_eq_right h]
      exact le_max_of_le_right (le_max_left _ _)
    · rw [max_eq_left h]
      exact le_max_of_le_right (le_max_right _ _)

theorem incident_secants (atG atH : Bool) {r s : ℝ}
    (hr : 0≤r) (hs : 0≤ s) (hS : r+s≤frameCap) :
    lambdaG atG r≤ sec (r+s) ∧ lambdaB atG r≤ sec (r+s) ∧
      lambdaH atH s≤ sec (r+s) ∧ lambdaD atH s≤ sec (r+s) := by
  have htotal : r+s∈Icc 0 frameCap := ⟨add_nonneg hr hs,hS⟩
  have h1 := (JointNegativeAETD2.CommonGain.full_secant_domain htotal).1
  have hA := Penalty.secant_monotone ⟨hr,by linarith⟩ htotal (by linarith)
  have hE := Penalty.secant_monotone ⟨hs,by linarith⟩ htotal (by linarith)
  cases atG <;> cases atH <;>
    simp only [lambdaG,lambdaB,lambdaH,lambdaD,JointNegativeAETD2.Source.lambdaG,
      JointNegativeAETD2.Source.lambdaB,JointNegativeAETD2.Source.lambdaH,
      JointNegativeAETD2.Source.lambdaD,ite_true] <;>
    exact ⟨by assumption,by assumption,by assumption,by assumption⟩

theorem q_charge_le (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : 0≤r) (hs : 0≤ s) (hS : r+s≤frameCap) (i : Fin 5) :
    (109/200)*qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i≤
      Penalty.cost (Explicit.c f z) (r+s) := by
  have hc := Explicit.ranges f hz
  have hl := incident_secants atG atH hr hs hS
  have h1 := (JointNegativeAETD2.CommonGain.full_secant_domain ⟨add_nonneg hr hs,hS⟩).1
  have hq : qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i≤
      max (sec (r+s)) (Explicit.c f z) := by
    fin_cases i
    · exact hl.2.2.1.trans (le_max_left _ _)
    · exact hl.1.trans (le_max_left _ _)
    · exact max_le (hl.2.1.trans (le_max_left _ _)) (hc.m_le_c.trans (le_max_right _ _))
    · exact h1.trans (le_max_left _ _)
    · exact h1.trans (le_max_left _ _)
  exact (mul_le_mul_of_nonneg_left hq (by norm_num)).trans
    (cost_max_coefficient ⟨add_nonneg hr hs,hS⟩)

theorem positive_lower (f : Row) (atG atH : Bool) {r s z d : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤frameCap) (hd : d∈Icc 0 frameCap) (i : Fin 5) :
    -Penalty.cost (Explicit.c f z) (r+s)*d≤
      PositiveTD.Hybrid.positive R (Penalty.cost (Explicit.c f z) (r+s))
        (pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s)
        (qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s)
        (distinguished atH (Explicit.c f z)) i d := by
  by_cases hi : i=distinguished atH (Explicit.c f z)
  · simp [PositiveTD.Hybrid.positive,hi]
  · have hp := pair_domain f atG atH hz hr hs hH i
    have hu := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap)
      radius_sq.le hp.1 hp.2.1 (show _≤2*_ by linarith [hp.2.2,hp.1]) hd
    have hq := mul_le_mul_of_nonneg_right (q_charge_le f atG atH hz hr.1 hs.1 hS i) hd.1
    simp only [PositiveTD.Hybrid.positive,ite_eq_right hi]
    linarith

theorem same_block_sine (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hS : r+s≤frameCap) (i : Fin 5) :
    qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i*
        Real.sin (frameCap-(r+s))≤
      pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i := by
  have hc := Explicit.ranges f hz
  have htotal : r+s∈Icc 0 frameCap := ⟨add_nonneg hr.1 hs.1,hS⟩
  have hr' : r∈Icc 0 frameCap := ⟨hr.1,by linarith [hs.1]⟩
  have hzero := JointNegativeAETD2.BlockBounds.secant_sine_remaining
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) htotal htotal.1
  simp only [JointNegativeAETD2.Source.sec,SecantNormCurvature.secant,
    Real.cos_zero,div_one,one_mul] at hzero
  have hA := JointNegativeAETD2.BlockBounds.secant_sine_remaining hr' htotal (by linarith [hs.1])
  have hE := JointNegativeAETD2.BlockBounds.secant_sine_remaining hs htotal (by linarith [hr.1])
  have hG : lambdaG atG r*Real.sin (frameCap-(r+s))≤Explicit.k f z := by
    cases atG <;> simp only [lambdaG,JointNegativeAETD2.Source.lambdaG,Bool.false_eq_true,↓reduceIte] <;>
      linarith [hc.k_domain.1]
  have hH : lambdaH atH s*Real.sin (frameCap-(r+s))≤Explicit.k f z := by
    cases atH <;> simp only [lambdaH,JointNegativeAETD2.Source.lambdaH,Bool.false_eq_true,↓reduceIte] <;>
      linarith [hc.k_domain.1]
  have hB : lambdaB atG r*Real.sin (frameCap-(r+s))≤Explicit.k f z := by
    cases atG <;> simp only [lambdaB,JointNegativeAETD2.Source.lambdaB,Bool.false_eq_true,↓reduceIte] <;>
      linarith [hc.k_domain.1]
  fin_cases i
  · exact hH
  · exact hG
  · change max (lambdaB atG r) (Explicit.m f z)*Real.sin (frameCap-(r+s))≤
      min (lambdaB atG r) (Explicit.m f z)
    rcases le_total (Explicit.m f z) (lambdaB atG r) with hh|hh
    · rw [max_eq_left hh,min_eq_right hh]
      exact hB.trans hc.k_le_m
    · rw [max_eq_right hh,min_eq_left hh]
      have hlam : 1≤lambdaB atG r := by
        cases atG
        · exact (JointNegativeAETD2.Source.secant_short hr).1
        · simp [lambdaB,JointNegativeAETD2.Source.lambdaB]
      have hsin := (transport_trig (show frameCap-(r+s)∈Icc 0 frameCap from
        ⟨by linarith,by linarith [htotal.1]⟩)).2.2.1
      have hupper := mul_le_mul_of_nonneg_right (hc.m_le_c.trans hc.c_domain.2) hsin
      nlinarith
  · by_cases ho : ordinaryD atH (Explicit.c f z)
    · simp only [pWeights,qWeights,Fin.reduceFinMk,Matrix.cons_val,ho,↓reduceIte,one_mul]
      linarith [hc.c_domain.1]
    · simp only [pWeights,qWeights,Fin.reduceFinMk,Matrix.cons_val,ho,↓reduceIte,one_mul]
      linarith [hc.k_domain.1]
  · change (1:ℝ)*Real.sin (frameCap-(r+s))≤Explicit.k f z
    linarith [hc.k_domain.1]

theorem same_negative (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤z) (i : Fin 5)
    (hi : i≠distinguished atH (Explicit.c f z)) :
    V R (pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i) (z-(r+s))≤
    PositiveTD.Hybrid.block R (Penalty.cost (Explicit.c f z) (r+s))
      (pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s)
      (distinguished atH (Explicit.c f z)) i (frameCap-z) (frameCap-(r+s)) := by
  have hz' := Explicit.frame_domain f hz
  have hp := pair_domain f atG atH hz hr hs hH i
  have htotal := add_nonneg hr.1 hs.1
  have hh := NegativeAPositiveTD.SameBlock.negative_surplus hp.1.le
    (show frameCap-z∈Icc 0 (frameCap-(r+s)) from ⟨by linarith [hz'.2],by linarith⟩)
    (show frameCap-(r+s)∈Icc 0 frameCap from ⟨by linarith [hz'.2],by linarith⟩)
    (same_block_sine f atG atH hz hr hs (hS.trans hz'.2) i)
  simpa [PositiveTD.Hybrid.block,hi,show frameCap-(r+s)-(frameCap-z)=z-(r+s) by ring] using hh

theorem same_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s∈Icc z frameCap) (i : Fin 5)
    (hi : i≠distinguished atH (Explicit.c f z)) :
    PositiveTD.Hybrid.positive R (Penalty.cost (Explicit.c f z) (r+s))
      (pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s)
      (distinguished atH (Explicit.c f z)) i (r+s-z)≤
    PositiveTD.Hybrid.block R (Penalty.cost (Explicit.c f z) (r+s))
      (pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s)
      (qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s)
      (distinguished atH (Explicit.c f z)) i (frameCap-z) (frameCap-(r+s)) := by
  have hz' := Explicit.frame_domain f hz
  have hp := pair_domain f atG atH hz hr hs hH i
  have hh := NegativeAPositiveTD.SameBlock.positive_surplus hp.1.le hp.2.2
    (show frameCap-z∈Icc 0 frameCap from ⟨by linarith [hz'.2],by linarith [hz'.1]⟩)
    (show frameCap-(r+s)∈Icc 0 (frameCap-z) from ⟨by linarith [hS.2],by linarith [hS.1]⟩)
  simpa [PositiveTD.Hybrid.positive,PositiveTD.Hybrid.block,hi,
    show frameCap-z-(frameCap-(r+s))=r+s-z by ring] using hh

end SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.BlockBounds
