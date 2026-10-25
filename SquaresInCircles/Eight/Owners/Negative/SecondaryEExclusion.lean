module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Frames.Ordinary.ShortSecantGrowth
public import SquaresInCircles.Eight.Owners.Flat.TStress
public import SquaresInCircles.Eight.Owners.Negative.TEntry
public import SquaresInCircles.Eight.Owners.Positive.SecondaryEExclusion
public import SquaresInCircles.Eight.Owners.Positive.SmallScalar
public import SquaresInCircles.Eight.Owners.WholeIntervalBernstein
public import SquaresInCircles.Eight.Owners.RemovedPrimaryConcentration

/-!
# Eight squares: actual secondary-E exclusion in the negative-T regimes

The original T boundary gives either an already
available secondary physical owner, or the proved short flat-core branch.
The latter uses the exact original T work, original seven-angle budgets,
and the strict secant gain. Negative BT uses the actual TD alignment
provided by the preceding T-pair preprocessing.
-/

section
/-!
## Concrete ordinary coefficients for the two negative-T stresses

The only enlarged coefficient is the actual
`c_N(d) / cos s`. The TD case has `s ≤ .3`; the BT case has `s ≤ .09`.
Every correlated, high-angle, and low-angle bound below is proved for
these coefficients and retains the original value of `s`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.NegativeOrdinaryParameters
open PositiveAngularEnvelope PositivePrimaryBaselines PositiveStressCoefficients
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope OrdinaryNegativeSlope
open PositiveOrdinaryParameters PositiveOrdinaryEnvelope VaryingBComparison
open ActualOrdinaryBlocks

structure Bounds (d s b t : ℝ) : Prop where
  angle : d∈Icc 0 frameCap
  short : s∈Icc 0 (3/10)
  B_lower : k≤b
  D_lower : k≤t
  B_upper : b*Real.cos s≤2069/2000
  D_upper : t*Real.cos s≤2069/2000
  correlated : (ratio d-31/10000)*b≤lN d
  shortened : s≤d → ratio (d-s)*b≤lN d
  high : 3/10≤d → (2/3)*b≤lN d
  low : d≤3/10 → b*Real.cos s≤1 ∧ t*Real.cos s≤1

theorem short_cos {s : ℝ} (hs : s∈Icc 0 (3/10)) :
    191/200≤Real.cos s ∧ 0<Real.cos s ∧ Real.cos s≤1 := by
  have h := Real.one_sub_sq_div_two_le_cos (x := s)
  have hs2 := pow_le_pow_left₀ hs.1 hs.2 2
  have hc : 191/200≤Real.cos s := by norm_num at hs2; linarith
  exact ⟨hc,by linarith,Real.cos_le_one s⟩

theorem short_BT_ratios {d s : ℝ} (hd : d∈Icc 0 frameCap)
    (hs : s∈Icc 0 (9/100)) :
    ratio d-31/10000≤ratio d*Real.cos s ∧
    (s≤d → ratio (d-s)≤ratio d*Real.cos s) ∧
    (29/50 : ℝ)≤ratio d*Real.cos s := by
  have hd1 := hd.1
  have hd2 : d≤7/10 := hd.2
  have hrlo : 117/200≤ratio d := by dsimp [ratio]; linarith
  have hrhi : ratio d≤1527/2000 := by dsimp [ratio]; linarith
  have hcos := Real.one_sub_sq_div_two_le_cos (x := s)
  have hc1 := Real.cos_le_one s
  have hs0 : 0 ≤ s := hs.1
  have hs9 : s≤9/100 := hs.2
  have hs2 : s^2≤(9/100)*s := by nlinarith
  have hm := mul_le_mul hrhi (show 1-Real.cos s ≤ s^2/2 by linarith) (by linarith)
    (by norm_num : (0:ℝ)≤1527/2000)
  refine ⟨by linarith,?_,by linarith⟩
  intro _
  have he : ratio (d-s)=ratio d-(51/200)*s := by dsimp [ratio]; ring
  rw [he]
  linarith

theorem short_BT_high {d s : ℝ} (hd : d∈Icc 0 frameCap)
    (hs : s∈Icc 0 (9/100)) (hlarge : 3/10≤d) :
    (2/3)*cN d≤lN d*Real.cos s := by
  have hb := coefficient_bounds hd
  have hd2 : d≤7/10 := hd.2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := s)
  have hs2 := pow_le_pow_left₀ hs.1 hs.2 2
  have hcos' : 19919/20000≤Real.cos s := by norm_num at hs2; linarith
  have hmul := mul_le_mul_of_nonneg_left hcos' (by linarith [hb.2.2.1] : 0≤lN d)
  have hdd := mul_nonneg (sub_nonneg.2 hlarge) (sub_nonneg.2 hd2)
  dsimp [lN,cN] at hmul ⊢
  linarith

theorem familyTD {d s : ℝ} (hd : d∈Icc 0 frameCap)
    (hs : s∈Icc 0 (3/10)) : Bounds d s (cN d) (cN d/Real.cos s) := by
  have hb := PositiveOrdinaryParameters.familyN hd
  have hc := short_cos hs
  have hc0 : 0≤cN d := by linarith [hb.B_lower,show k=(863/1000 : ℝ) from rfl]
  have hcsec : cN d≤cN d/Real.cos s :=
    (le_div_iff₀ hc.2.1).2 (mul_le_of_le_one_right hc0 hc.2.2)
  have he : (cN d/Real.cos s)*Real.cos s=cN d := div_mul_cancel₀ _ hc.2.1.ne'
  have hcorr : (ratio d-31/10000)*cN d≤lN d := by
    nlinarith [hb.correlated]
  refine ⟨hd,hs,hb.B_lower,hb.D_lower.trans hcsec,
    (mul_le_of_le_one_right hc0 hc.2.2).trans hb.B_upper,
    by rw [he]; exact hb.D_upper,hcorr,?_,hb.high,?_⟩
  · intro hsd
    have hr : ratio (d-s)≤ratio d := by dsimp [ratio]; linarith [hs.1]
    exact (mul_le_mul_of_nonneg_right hr hc0).trans hb.correlated
  · intro hsmall
    exact ⟨(mul_le_of_le_one_right hc0 hc.2.2).trans (hb.low hsmall).1,
      by rw [he]; exact (hb.low hsmall).2.1⟩

theorem familyBT {d s : ℝ} (hd : d∈Icc 0 frameCap)
    (hs : s∈Icc 0 (9/100)) : Bounds d s (cN d/Real.cos s) (cN d) := by
  have hb := PositiveOrdinaryParameters.familyN hd
  have hs' : s∈Icc 0 (3/10) := ⟨hs.1,by linarith [hs.2]⟩
  have hc := short_cos hs'
  have hc0 : 0≤cN d := by linarith [hb.B_lower,show k=(863/1000 : ℝ) from rfl]
  have hsec : cN d≤cN d/Real.cos s :=
    (le_div_iff₀ hc.2.1).2 (mul_le_of_le_one_right hc0 hc.2.2)
  have he : (cN d/Real.cos s)*Real.cos s=cN d := div_mul_cancel₀ _ hc.2.1.ne'
  have hr := short_BT_ratios hd hs
  have hcorr : (ratio d-31/10000)*(cN d/Real.cos s)≤lN d := by
    refine le_of_mul_le_mul_right ?_ hc.2.1
    have hm := mul_le_mul_of_nonneg_right hr.1 hc0
    have hb' := mul_le_mul_of_nonneg_right hb.correlated hc.2.1.le
    have he' : ((ratio d-31/10000)*(cN d/Real.cos s))*Real.cos s=
        (ratio d-31/10000)*cN d := by rw [mul_assoc,he]
    rw [he']
    linarith
  refine ⟨hd,hs',hb.B_lower.trans hsec,hb.D_lower,
    by rw [he]; exact hb.B_upper,
    (mul_le_of_le_one_right hc0 hc.2.2).trans hb.D_upper,hcorr,?_,?_,?_⟩
  · intro hsd
    refine le_of_mul_le_mul_right ?_ hc.2.1
    have hm := mul_le_mul_of_nonneg_right (hr.2.1 hsd) hc0
    have hb' := mul_le_mul_of_nonneg_right hb.correlated hc.2.1.le
    rw [mul_assoc,he]
    linarith
  · intro hlarge
    have hx := short_BT_high hd hs hlarge
    refine le_of_mul_le_mul_right ?_ hc.2.1
    rw [mul_assoc,he]
    exact hx
  · intro hsmall
    exact ⟨by rw [he]; exact (hb.low hsmall).1,
      (mul_le_of_le_one_right hc0 hc.2.2).trans (hb.low hsmall).2.1⟩

theorem coefficient_ranges {d s b t : ℝ} (h : Bounds d s b t) :
    b≤109/100 ∧ t≤109/100 ∧
    b≤(2069/2000)/Real.cos s ∧ t≤(2069/2000)/Real.cos s := by
  have hc := short_cos h.short
  have hb0 : 0≤b := by linarith [h.B_lower,show k=(863/1000 : ℝ) from rfl]
  have ht0 : 0≤t := by linarith [h.D_lower,show k=(863/1000 : ℝ) from rfl]
  have hbm := mul_le_mul_of_nonneg_left hc.1 hb0
  have htm := mul_le_mul_of_nonneg_left hc.1 ht0
  exact ⟨by linarith [h.B_upper],by linarith [h.D_upper],
    (le_div_iff₀ hc.2.1).2 h.B_upper,(le_div_iff₀ hc.2.1).2 h.D_upper⟩

theorem block_coefficients {d s b t : ℝ} (h : Bounds d s b t)
    (C : SignedCycle) (ab bt td : Fin 4) (i : Fin 4) :
    (blocks C ab bt td (SecondaryEStress.tiltedWeight k (19/50) d) k (lN d) b t i).p=
      ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i ∧
    (blocks C ab bt td (SecondaryEStress.tiltedWeight k (19/50) d) k (lN d) b t i).q=qs b t i := by
  have hb := PositiveOrdinaryParameters.familyN h.angle
  have hlb : lN d≤b := hb.ell_upper.le.trans h.B_lower
  fin_cases i <;>
    simp [blocks,Block.p,Block.q,ps,qs,min_eq_left hb.H_upper,max_eq_right hb.H_upper,
      min_eq_left hb.ell_upper.le,max_eq_right hb.ell_upper.le,min_eq_left hlb,max_eq_right hlb]

theorem domains {d s b t : ℝ} (h : Bounds d s b t) (i : Fin 4) :
    0<ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i ∧
    ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i≤qs b t i ∧
    qs b t i≤2*ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i ∧
    (ratio d-31/10000)*qs b t i≤ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i ∧
    k≤qs b t i ∧ qs b t i≤(2069/2000)/Real.cos s ∧
    1263/2500≤ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i := by
  have hb := PositiveOrdinaryParameters.familyN h.angle
  have hd1 := h.angle.1
  have hd2 : d≤7/10 := h.angle.2
  have hrlo : 5819/10000≤ratio d-31/10000 := by dsimp [ratio]; linarith
  have hrhi : ratio d-31/10000≤1901/2500 := by dsimp [ratio]; linarith
  have hc := short_cos h.short
  have hqone : 1≤(2069/2000)/Real.cos s := (le_div_iff₀ hc.2.1).2 (by linarith [hc.2.2])
  have hu := coefficient_ranges h
  have hk : k=(863/1000 : ℝ) := rfl
  have hDlo : k ≤ min 1 t := le_min (by norm_num [k]) h.D_lower
  have hDup : max 1 t≤109/100 := max_le (by norm_num) hu.2.1
  have hDq : max 1 t≤(2069/2000)/Real.cos s := max_le hqone hu.2.2.2
  have hB0 : 0≤b := by linarith [h.B_lower]
  have hD0 : 0 ≤ max 1 t := (by norm_num : (0:ℝ)≤1).trans (le_max_left 1 t)
  have hmm : min 1 t ≤ max 1 t := min_le_max
  have hDc := mul_le_mul hrhi hDup hD0 (by norm_num : (0:ℝ)≤1901/2500)
  have hBc := mul_le_mul_of_nonneg_right hrlo hB0
  have hAc : (ratio d-31/10000)*k≤lN d := by
    have hm := mul_le_mul_of_nonneg_right (show ratio d-31/10000≤ratio d by linarith)
      (show 0≤k by norm_num [k])
    have hh := (mul_le_mul_of_nonneg_left hb.B_lower
      (show 0≤ratio d by dsimp [ratio]; linarith)).trans hb.correlated
    exact hm.trans hh
  have hell : (1263/2500 : ℝ)≤lN d := by
    have hd2' : d^2≤(7/10)*d := by nlinarith
    dsimp [lN]
    nlinarith
  have hl0 := hb.ell_lower
  have hl1 := hb.ell_upper
  have hH0 := hb.H_lower
  have hH1 := hb.H_upper
  fin_cases i <;> simp only [ps,qs,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  · exact ⟨by linarith,hH1,by linarith,by linarith,by linarith,hqone,by linarith⟩
  · exact ⟨by linarith,hl1.le,by linarith,hAc,le_rfl,by linarith,hell⟩
  · exact ⟨by linarith,hl1.le.trans h.B_lower,by linarith [h.correlated],
      h.correlated,h.B_lower,hu.2.2.1,hell⟩
  · exact ⟨by linarith,hmm,by linarith,by linarith,by linarith,hDq,by linarith⟩

theorem high_domains {d s b t : ℝ} (h : Bounds d s b t) (hd : 3/10≤d)
    (i : Fin 4) : (2/3)*qs b t i≤ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i := by
  have hb := PositiveOrdinaryParameters.familyN h.angle
  have hDlo : k ≤ min 1 t := le_min (by norm_num [k]) h.D_lower
  have hDhi : max 1 t≤109/100 := max_le (by norm_num) (coefficient_ranges h).2.1
  have hA := (mul_le_mul_of_nonneg_left h.B_lower (by norm_num : (0:ℝ)≤2/3)).trans (h.high hd)
  have hk : k=(863/1000 : ℝ) := rfl
  have hH0 := hb.H_lower
  fin_cases i <;> simp only [ps,qs,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  · linarith
  · exact hA
  · exact h.high hd
  · linarith

theorem low_domains {d s b t : ℝ} (h : Bounds d s b t) (hd : d≤3/10)
    (i : Fin 4) : lP d≤ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i ∧
      qs b t i≤1/Real.cos s := by
  have hb := PositiveOrdinaryParameters.familyN h.angle
  have hl := hb.low hd
  have hc := short_cos h.short
  have hq1 : 1≤1/Real.cos s := (le_div_iff₀ hc.2.1).2 (by simpa using hc.2.2)
  have hB : b≤1/Real.cos s := (le_div_iff₀ hc.2.1).2 (h.low hd).1
  have hD : t≤1/Real.cos s := (le_div_iff₀ hc.2.1).2 (h.low hd).2
  have hDlo : k≤ min 1 t := le_min (by norm_num [k]) h.D_lower
  have hlk : lP d≤k := hl.2.2.1.trans hb.ell_upper.le
  fin_cases i
  · simpa [ps,qs] using And.intro (hlk.trans hb.H_lower) hq1
  · simpa [ps,qs] using And.intro hl.2.2.1 ((show k≤1 by norm_num [k]).trans hq1)
  · simpa [ps,qs] using And.intro hl.2.2.1 hB
  · simpa [ps,qs] using And.intro (hlk.trans hDlo) (max_le hq1 hD)

theorem single_negative_lower {d s b t w : ℝ} (h : Bounds d s b t)
    (hsd : s≤d) (hw : w∈Icc 0 (d-s)) (i : Fin 4) :
    V (Real.sqrt qCap) (lN d) k w≤
      V (Real.sqrt qCap) (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i) (qs b t i) w := by
  have hb := PositiveOrdinaryParameters.familyN h.angle
  have hz : d-s∈Icc 0 frameCap := ⟨by linarith,by linarith [h.angle.2,h.short.1]⟩
  have hw' : w∈Icc 0 frameCap := ⟨hw.1,hw.2.trans hz.2⟩
  have hlhalf : k/2≤lN d := by norm_num [k]; linarith [hb.ell_lower]
  have hchain := near_equal_chain (by norm_num [k] : (43/50 : ℝ)≤k)
    hb.H_lower hb.H_upper hlhalf hb.ell_upper.le hw'
  have hH := hchain.1.trans (hchain.2.1.trans hchain.2.2)
  have hB := V_larger_coefficient (by linarith [hb.ell_lower]) hb.ell_upper.le
    h.B_lower (h.shortened hsd) hz hw
  have hD : V (Real.sqrt qCap) (lN d) k w≤V (Real.sqrt qCap) (min 1 t) (max 1 t) w := by
    by_cases ht : t≤1
    · have hc := near_equal_chain (by norm_num [k] : (43/50 : ℝ)≤k)
        h.D_lower ht hlhalf hb.ell_upper.le hw'
      simpa [min_eq_right ht,max_eq_left ht] using hc.1.trans (hc.2.1.trans hc.2.2)
    · have ht1 : 1≤t := (lt_of_not_ge ht).le
      have hc := near_equal_chain (by norm_num [k] : (43/50 : ℝ)≤k)
        (by norm_num [k] : k≤1) le_rfl hlhalf hb.ell_upper.le hw'
      have hu := (coefficient_ranges h).2.1
      have hlarge := V_larger_coefficient (l := 1) (k := 1) (q := t)
        (by norm_num) le_rfl ht1 (by norm_num [ratio,frameCap]; nlinarith)
        (show frameCap∈Icc 0 frameCap by constructor; norm_num [frameCap]; rfl) hw'
      simpa [min_eq_left ht1,max_eq_right ht1] using
        (hc.1.trans (hc.2.1.trans hc.2.2)).trans hlarge
  fin_cases i
  · simpa [ps,qs] using hH
  · simp [ps,qs]
  · simpa [ps,qs] using hB
  · simpa [ps,qs] using hD

end SquaresInCircles.Eight.NegativeOrdinaryParameters
end
end
end

section
/-!
## Complete ordinary envelope with one negative primary removed

This proves the full four-block inequality for
the actual negative-T coefficients. Both signs are allowed in every
ordinary block. The two removed primary angles remain independent, and
the result includes the junction where their imbalance changes sign.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.NegativeOrdinaryEnvelope
open PositiveAngularEnvelope PositivePrimaryBaselines PositiveStressCoefficients
open OrdinaryAngleConcavity OrdinaryAngleConcentration OrdinaryPositiveEnvelope
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope PositiveOrdinaryEnvelope
open NegativeOrdinaryParameters OrdinaryShortSecantGrowth RemovedPrimaryConcentration

theorem affine_concave (a b l u : ℝ) :
    ConcaveOn ℝ (Icc l u) (fun x => a*x+b) := by
  refine ⟨convex_Icc l u,?_⟩
  intro x hx y hy α β hα hβ hsum
  simp only [smul_eq_mul]
  have hc : (α+β)*b=b := by rw [hsum,one_mul]
  nlinarith only [hc]

theorem gain_junction {d s : ℝ} (hd : d∈Icc 0 frameCap) (hs : s∈Icc 0 d) :
    min (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d)≤
      lambdaN d*s+V (Real.sqrt qCap) (lN d) k (d-s) := by
  have hb := PositiveOrdinaryParameters.familyN hd
  have hV := V_concave (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
    (by linarith [hb.ell_lower] : 0<lN d) hb.ell_upper.le
    (by norm_num [k]; linarith [hb.ell_lower] : k≤2*lN d)
  have hc := concave_affine_argument hV (a := -1) (b := d) (l := 0) (u := d)
    (fun x hx => ⟨by linarith [hx.2],by linarith [hd.2,hx.1]⟩)
  have hl := affine_concave (lambdaN d) 0 0 d
  have hconc : ConcaveOn ℝ (Icc 0 d)
      (fun x => lambdaN d*x+V (Real.sqrt qCap) (lN d) k (d-x)) := by
    convert hl.add hc using 1
    funext x
    congr 1 <;> ring
  have hh := hconc.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 d from ⟨le_rfl,hd.1⟩)
    (show d∈Icc 0 d from ⟨hd.1,le_rfl⟩) hs
  simpa only [sub_zero,sub_self,mul_zero,zero_add,V_zero,add_zero] using hh

theorem low_U_lower {d s b t z : ℝ} (h : Bounds d s b t) (hd : d≤3/10)
    (i : Fin 4) (hz : z∈Icc 0 frameCap) :
    -(571/1000)*z≤U (Real.sqrt qCap)
      (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i) (qs b t i) z := by
  have hi := domains h i
  have hlo := (low_domains h hd i).2
  have hc := short_cos h.short
  have hq0 : 0≤qs b t i := (hi.1.trans_le hi.2.1).le
  have hqcos := (le_div_iff₀ hc.2.1).1 hlo
  have hqmul := mul_le_mul_of_nonneg_left hc.1 hq0
  have hcoef : (109/200)*qs b t i≤571/1000 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hcoef hz.1
  have hU := U_lower (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hi.1 hi.2.1 hi.2.2.1 hz
  nlinarith

theorem low_V_lower {d s b t z : ℝ} (h : Bounds d s b t) (hd : d≤3/10)
    (i : Fin 4) (hz : z∈Icc 0 frameCap) :
    (87/70)*lP d*z≤V (Real.sqrt qCap)
      (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i) (qs b t i) z := by
  have hi := domains h i
  have hv := V_chord_lower hi.1 hi.2.1 hi.2.2.1 hz
  have hm := mul_le_mul_of_nonneg_right (low_domains h hd i).1 hz.1
  nlinarith

theorem low_constants {d : ℝ} (hd : d∈Icc 0 (3/10)) :
    571/1000≤(87/70)*lP d ∧ (87/70)*lP d≤lambdaN d ∧
    571/1000≤lambdaN d ∧
    0<(87/100)*lP d-(26/25)*d-(571/1000)*(frameCap-d) := by
  have hd2 : d^2≤(3/10)*d := by nlinarith [hd.1,hd.2]
  have hd2' := pow_le_pow_left₀ hd.1 hd.2 2
  dsimp [lP,lambdaN,frameCap]
  constructor
  · nlinarith
  constructor
  · nlinarith [sq_nonneg d]
  constructor
  · linarith [hd.1]
  · nlinarith [hd.1,hd.2]

theorem low_separated {d s b t : ℝ} (h : Bounds d s b t) (hd : d≤3/10)
    (i j : Fin 4) :
    V (Real.sqrt qCap) (lN d) k d≤lambdaN d*s+
      U (Real.sqrt qCap) (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i) (qs b t i) (frameCap-d)+
      V (Real.sqrt qCap) (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t j) (qs b t j) (frameCap-s) := by
  have hU := low_U_lower h hd i
    (show frameCap-d∈Icc 0 frameCap from ⟨by linarith [h.angle.2],by linarith [h.angle.1]⟩)
  have hV := low_V_lower h hd j
    (show frameCap-s∈Icc 0 frameCap from ⟨by dsimp [frameCap]; linarith [h.short.2],
      by linarith [h.short.1]⟩)
  have hc := low_constants ⟨h.angle.1,hd⟩
  have hg := mul_le_mul_of_nonneg_right hc.2.1 h.short.1
  have htarget := target_low_upper (PositiveOrdinaryParameters.familyN h.angle) hd
  dsimp [frameCap] at *
  nlinarith

theorem high_separated {d s b t : ℝ} (h : Bounds d s b t)
    (hd : 3/10≤d) (hsd : s≤d) (i j : Fin 4) :
    V (Real.sqrt qCap) (lN d) k (d-s)≤
      U (Real.sqrt qCap) (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i) (qs b t i) (frameCap-d)+
      V (Real.sqrt qCap) (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t j) (qs b t j) (frameCap-s) := by
  have hi := domains h i
  have hj := domains h j
  have ha : frameCap-d∈Icc 0 frameCap := ⟨by linarith [h.angle.2],by linarith [h.angle.1]⟩
  have hw : d-s∈Icc 0 (frameCap-s) := ⟨by linarith,by linarith [h.angle.2]⟩
  have hu : frameCap-s∈Icc 0 (frameCap-s) :=
    ⟨by dsimp [frameCap]; linarith [h.short.2],le_rfl⟩
  have hU := U_lower (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hi.1 hi.2.1 hi.2.2.1 ha
  have hV := shortened_growth hj.1 hj.2.1 (high_domains h hd j) h.short.1 hw hu
    (by linarith [h.angle.2])
  have hsingle := single_negative_lower h hsd ⟨hw.1,le_rfl⟩ j
  have hqi := mul_le_mul_of_nonneg_left hi.2.2.2.2.2.1 (by norm_num : (0:ℝ)≤109/200)
  have hqj := mul_le_mul_of_nonneg_left hj.2.2.2.2.1
    (show 0≤2/3+s/4 by linarith [h.short.1])
  have hcoef : (109/200)*qs b t i≤(2/3+s/4)*qs b t j := by
    have hc := secant_compensation h.short
    rw [mul_div_assoc] at hc
    linarith only [hqi,hqj,hc]
  have hm := mul_le_mul_of_nonneg_right hcoef ha.1
  linarith

theorem mixed_sum_lower {d s b t : ℝ} (h : Bounds d s b t)
    (P N : Fin 4 → ℝ) (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑ i,P i)≤frameCap-d)
    (hbalance : (∑ i,N i)=d-s+∑ i,P i) :
    min (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d)≤
      lambdaN d*s+∑ i,mixedBlock (Real.sqrt qCap)
        (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i) (qs b t i) (P i) (N i) := by
  classical
  let p := ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t
  let q := qs b t
  let L := min (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d)
  have hR := Real.sqrt_nonneg qCap
  have hQ := (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
  have hp (i : Fin 4) : 0<p i := (domains h i).1
  have hpq (i : Fin 4) : p i≤q i := (domains h i).2.1
  have hqp (i : Fin 4) : q i≤2*p i := (domains h i).2.2.1
  by_cases hsd : s≤d
  · obtain ⟨i,j,hconc⟩ := negative_concentration (Real.sqrt qCap) p q P N
      hR hQ hp hpq hqp hP hN h.angle ⟨h.short.1,hsd⟩ hbudget hbalance
    have hjunction := gain_junction h.angle ⟨h.short.1,hsd⟩
    have hpure : L≤lambdaN d*s+V (Real.sqrt qCap) (p j) (q j) (d-s) := by
      have hh := single_negative_lower h hsd ⟨by linarith,le_rfl⟩ j
      dsimp [L]
      linarith
    have hsat : L≤lambdaN d*s+
        (if i=j then mixedBlock (Real.sqrt qCap) (p i) (q i) (frameCap-d) (frameCap-s)
         else U (Real.sqrt qCap) (p i) (q i) (frameCap-d)+
           V (Real.sqrt qCap) (p j) (q j) (frameCap-s)) := by
      by_cases hij : i=j
      · rw [ite_eq_left hij]
        have hi := domains h i
        have hs := RelaxedSameBlock.negative_surplus (R := Real.sqrt qCap)
          ((hp i).trans_le (hpq i)).le hi.2.2.2.1 h.angle ⟨h.short.1,hsd⟩
        have hsingle := single_negative_lower h hsd ⟨by linarith,le_rfl⟩ i
        dsimp [L,p,q] at *
        linarith
      · rw [ite_eq_right hij]
        by_cases hd : d≤3/10
        · have hh := low_separated h hd i j
          have hmin := min_le_left (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d)
          dsimp [L,p,q] at *
          linarith
        · have hh := high_separated h (lt_of_not_ge hd).le hsd i j
          dsimp [L,p,q] at *
          linarith
    have hmin : L-lambdaN d*s≤ min (V (Real.sqrt qCap) (p j) (q j) (d-s))
        (if i=j then mixedBlock (Real.sqrt qCap) (p i) (q i) (frameCap-d) (frameCap-s)
         else U (Real.sqrt qCap) (p i) (q i) (frameCap-d)+
           V (Real.sqrt qCap) (p j) (q j) (frameCap-s)) :=
      le_min (by linarith) (by linarith)
    have hh := hmin.trans hconc
    change L≤lambdaN d*s+_
    linarith
  · have hds : d≤ s := (lt_of_not_ge hsd).le
    have hd : d≤3/10 := hds.trans h.short.2
    have hPt : (∑ i,P i)≤frameCap := by linarith [h.angle.1]
    have hNt : (∑ i,N i)≤frameCap := by rw [hbalance]; linarith [h.short.1]
    have hP0 := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hP i)
    have hN0 := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hN i)
    obtain ⟨i,j,hconc⟩ := both_signs_concentrate (Real.sqrt qCap) p q P N
      hR hQ hp hpq hqp hP hN hPt hNt
    have hconstants := low_constants ⟨h.angle.1,hd⟩
    have hlambda : (571/1000)*(s-d)≤lambdaN d*(s-d) :=
      mul_le_mul_of_nonneg_right hconstants.2.2.1 (by linarith)
    have hlower : -(571/1000)*(s-d)≤
        (if i=j then mixedBlock (Real.sqrt qCap) (p i) (q i) (∑ k,P k) (∑ k,N k)
         else U (Real.sqrt qCap) (p i) (q i) (∑ k,P k)+
           V (Real.sqrt qCap) (p j) (q j) (∑ k,N k)) := by
      by_cases hij : i=j
      · rw [ite_eq_left hij]
        have hi := domains h i
        have hq0 := ((hp i).trans_le (hpq i)).le
        have hratio : (29/50)*q i≤p i := by
          have hr : 29/50≤ratio d-31/10000 := by dsimp [ratio]; linarith [h.angle.1]
          exact (mul_le_mul_of_nonneg_right hr hq0).trans hi.2.2.2.1
        have hs := RelaxedSameBlock.positive_surplus (R := Real.sqrt qCap) hq0 hratio
          ⟨hP0,hPt⟩ (show (∑ k,N k)∈Icc 0 (∑ k,P k) from ⟨hN0,by linarith⟩)
        have he : (∑ k,P k)-(∑ k,N k)=s-d := by linarith
        rw [he] at hs
        have hU := low_U_lower h hd i
          (show s-d∈Icc 0 frameCap from ⟨by linarith,by linarith [h.short.2,h.angle.1,
            show frameCap=(7/10 : ℝ) from rfl]⟩)
        exact hU.trans hs
      · rw [ite_eq_right hij]
        have hU := low_U_lower h hd i ⟨hP0,hPt⟩
        have hV := low_V_lower h hd j ⟨hN0,hNt⟩
        have hm := mul_le_mul_of_nonneg_right hconstants.1 hN0
        dsimp [p,q] at *
        nlinarith
    have hactual := hlower.trans hconc
    have hmin := min_le_right (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d)
    dsimp [p,q] at *
    nlinarith

end SquaresInCircles.Eight.NegativeOrdinaryEnvelope
end
end
end

section
/-!
## The seven-angle budgets for negative T

The positive and negative parts removed from the four blocks are computed from the seven edge
errors of the cycle; both variation caps and the signed balance follow for the blocks
(`budgets`). They apply to the stress increments, with the owner of AB of the cycle
(`increment_lower`, `TD_increment_lower`, `BT_increment_lower`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.NegativeOrdinaryBlocks
open Candidate PositiveAngularEnvelope PositivePrimaryBaselines PositiveStressCoefficients
open OrdinaryAngleConcavity ActualOrdinaryBlocks PositiveOrdinaryEnvelope
open NegativeOrdinaryParameters FlatTStress

theorem budgets {C : SignedCycle} {ab bt td : Fin 4} {n k l b t d s : ℝ}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hvar : positiveVariation C.theta≤frameCap)
    (hpos : positivePart (delta C.theta G)+
      (if bt=3 then positivePart (delta C.theta B) else 0)+
      (if td=2 then positivePart (delta C.theta T) else 0)=d)
    (hneg : negativePart (delta C.theta G)+
      (if bt=3 then negativePart (delta C.theta B) else 0)+
      (if td=2 then negativePart (delta C.theta T) else 0)=s) :
    (∑ i,(blocks C ab bt td n k l b t i).P)≤frameCap-d ∧
    (∑ i,(blocks C ab bt td n k l b t i).N)≤frameCap-s ∧
    (∑ i,(blocks C ab bt td n k l b t i).N)=
      d-s+∑ i,(blocks C ab bt td n k l b t i).P := by
  have hp := sum_parts C hab hbt htd n k l b t positivePart positivePart_zero
  have hn := sum_parts C hab hbt htd n k l b t negativePart negativePart_zero
  have hp' : (∑ i,(blocks C ab bt td n k l b t i).P)=positiveVariation C.theta-d := by
    change (∑ i,(positivePart (blocks C ab bt td n k l b t i).u+
      positivePart (blocks C ab bt td n k l b t i).v))=_
    rw [hp]
    dsimp [positiveVariation]
    linarith
  have hn' : (∑ i,(blocks C ab bt td n k l b t i).N)=negativeVariation C.theta-s := by
    change (∑ i,(negativePart (blocks C ab bt td n k l b t i).u+
      negativePart (blocks C ab bt td n k l b t i).v))=_
    rw [hn]
    dsimp [negativeVariation]
    linarith
  have heq := variations_equal C.theta
  exact ⟨by linarith,by linarith,by linarith⟩

theorem increment_lower {C : SignedCycle} {ab bt td : Fin 4} {d s b t : ℝ}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hvar : positiveVariation C.theta≤frameCap)
    (hpos : positivePart (delta C.theta G)+
      (if bt=3 then positivePart (delta C.theta B) else 0)+
      (if td=2 then positivePart (delta C.theta T) else 0)=d)
    (hneg : negativePart (delta C.theta G)+
      (if bt=3 then negativePart (delta C.theta B) else 0)+
      (if td=2 then negativePart (delta C.theta T) else 0)=s)
    (h : Bounds d s b t) :
    min (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d)≤lambdaN d*s+
      ∑ i,(blocks C ab bt td (SecondaryEStress.tiltedWeight k (19/50) d) k (lN d) b t i).increment
        (Real.sqrt qCap) := by
  have hb := budgets (n := SecondaryEStress.tiltedWeight k (19/50) d) (k := k) (l := lN d)
    (b := b) (t := t) hab hbt htd hvar hpos hneg
  set Bs := blocks C ab bt td (SecondaryEStress.tiltedWeight k (19/50) d) k (lN d) b t with hBs
  have hP : ∀ i,0≤(Bs i).P := fun i => (Bs i).P_nonneg
  have hN : ∀ i,0≤(Bs i).N := fun i => (Bs i).N_nonneg
  have hsumP : (∑ i,(Bs i).P)≤frameCap := by linarith [hb.1,h.angle.1]
  have hsumN : (∑ i,(Bs i).N)≤frameCap := by linarith [hb.2.1,h.short.1]
  have hPi (i : Fin 4) : (Bs i).P≤frameCap :=
    (Finset.single_le_sum (fun j _ => hP j) (Finset.mem_univ i)).trans hsumP
  have hNi (i : Fin 4) : (Bs i).N≤frameCap :=
    (Finset.single_le_sum (fun j _ => hN j) (Finset.mem_univ i)).trans hsumN
  have hsum := NegativeOrdinaryEnvelope.mixed_sum_lower h (fun i => (Bs i).P)
    (fun i => (Bs i).N) hP hN hb.1 hb.2.2
  apply hsum.trans
  refine add_le_add le_rfl ?_
  apply Finset.sum_le_sum
  intro i _
  have hc : (Bs i).p=ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i ∧
      (Bs i).q=qs b t i := NegativeOrdinaryParameters.block_coefficients h C ab bt td i
  have hminor := (Bs i).minorant (Real.sqrt qCap)
    (by rw [hc.1]; exact (NegativeOrdinaryParameters.domains h i).1.le) (hPi i) (hNi i)
  simpa only [hc.1,hc.2] using hminor

theorem TD_increment_lower {C : SignedCycle} {ab : Fin 4} {s : ℝ}
    (hab : ab=0 ∨ ab=2) (hvar : positiveVariation C.theta≤frameCap)
    (hd : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 (3/10))
    (hT : delta C.theta T= -s) :
    min (V (Real.sqrt qCap) (lN (delta C.theta G)) k (delta C.theta G))
      (lambdaN (delta C.theta G)*delta C.theta G)≤lambdaN (delta C.theta G)*s+
        negativeTDIncrement C ab (Real.sqrt qCap) k (lN (delta C.theta G))
          (cN (delta C.theta G)) (19/50) s := by
  have hPG : positivePart (delta C.theta G)=delta C.theta G := max_eq_left hd.1
  have hNG : negativePart (delta C.theta G)=0 :=
    max_eq_right (by linarith [hd.1] : -delta C.theta G≤0)
  have hPT : positivePart (delta C.theta T)=0 := by
    rw [hT]
    exact max_eq_right (by linarith [hs.1] : -s≤0)
  have hNT : negativePart (delta C.theta T)=s := by
    rw [hT]
    simpa [negativePart] using max_eq_left hs.1
  have h := increment_lower hab (Or.inl rfl) (Or.inr rfl) hvar
    (by simp [hPG,hPT]) (by simp [hNG,hNT]) (familyTD hd hs)
  simpa only [negativeTDIncrement] using h

theorem BT_increment_lower {C : SignedCycle} {ab : Fin 4} {s : ℝ}
    (hab : ab=0 ∨ ab=2) (hvar : positiveVariation C.theta≤frameCap)
    (hd : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 (9/100))
    (hB : delta C.theta B= -s) :
    min (V (Real.sqrt qCap) (lN (delta C.theta G)) k (delta C.theta G))
      (lambdaN (delta C.theta G)*delta C.theta G)≤lambdaN (delta C.theta G)*s+
        negativeBTIncrement C ab (Real.sqrt qCap) k (lN (delta C.theta G))
          (cN (delta C.theta G)) (19/50) s := by
  have hPG : positivePart (delta C.theta G)=delta C.theta G := max_eq_left hd.1
  have hNG : negativePart (delta C.theta G)=0 :=
    max_eq_right (by linarith [hd.1] : -delta C.theta G≤0)
  have hPB : positivePart (delta C.theta B)=0 := by
    rw [hB]
    exact max_eq_right (by linarith [hs.1] : -s≤0)
  have hNB : negativePart (delta C.theta B)=s := by
    rw [hB]
    simpa [negativePart] using max_eq_left hs.1
  have h := increment_lower hab (Or.inr rfl) (Or.inl rfl) hvar
    (by simp [hPG,hPB]) (by simp [hNG,hNB]) (familyBT hd hs)
  simpa only [negativeBTIncrement] using h

end SquaresInCircles.Eight.NegativeOrdinaryBlocks
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.NegativeSecondaryEExclusion
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity
open SecondaryEStress PositivePrimaryBaselines PositiveStressCoefficients
open PositiveSecondaryEExclusion FlatTStress NegativeOrdinaryBlocks

theorem scalar_min_positive {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0<secondaryBaseline (Real.sqrt qCap) k (lN d) (cN d) (19/50) d+
      min (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d) := by
  have hs := PositiveScalarTransfer.seven_scalar_bounds hd
  have hV := hs.2.2.2.1
  have hL := hs.2.2.2.2.1
  rw [scalar_V_eq] at hV
  change 0<secondaryBaseline (Real.sqrt qCap) k (lN d) (cN d) (19/50) d+
    V (Real.sqrt qCap) (lN d) k d at hV
  change 0<secondaryBaseline (Real.sqrt qCap) k (lN d) (cN d) (19/50) d+
    lambdaN d*d at hL
  rcases le_total (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d) with h | h
  · rw [min_eq_left h]; exact hV
  · rw [min_eq_right h]; exact hL

theorem flat_negative_TD_false {C : SignedCycle} {q s : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hs : s∈Ioc 0 (3/10))
    (hT : delta C.theta T= -s) (hflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (owners ab 2 2 i)) : False := by
  let d : ℝ := delta C.theta G
  have hd : d∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hC.spread (next G) G)⟩
  have hs' : s∈Icc 0 frameCap := ⟨hs.1.le,by dsimp [frameCap]; linarith [hs.2]⟩
  have hb := coefficient_bounds hd
  have hc : 0<cN d := by linarith [hb.2.2.2.2.1,show k=(863/1000 : ℝ) from rfl]
  have hnec := negative_TD_necessary (k := k) (l := lN d) (c := cN d) (η := 19/50)
    hq hC hnormal hab (by norm_num [k])
    (by linarith [hb.2.2.1]) hc (by norm_num : (0:ℝ)≤19/50) hG hs' hT hflat hf
  have hinc := TD_increment_lower hab hvar hd (Ioc_subset_Icc_self hs) hT
  have hgain := PositiveSecantGain.negative_TD_gain (q := qCap)
    (by norm_num [qCap]) le_rfl hd (show s∈Ioc 0 frameCap from ⟨hs.1,hs'.2⟩)
  have hstrict := scalar_min_positive hd
  dsimp [d] at *
  linarith

theorem flat_negative_BT_false {C : SignedCycle} {q s : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hs : s∈Ioc 0 (9/100))
    (hB : delta C.theta B= -s) (hflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (owners ab 3 0 i)) : False := by
  let d : ℝ := delta C.theta G
  have hd : d∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hC.spread (next G) G)⟩
  have hs' : s∈Icc 0 frameCap := ⟨hs.1.le,by dsimp [frameCap]; linarith [hs.2]⟩
  have hb := coefficient_bounds hd
  have hc : 0<cN d := by linarith [hb.2.2.2.2.1,show k=(863/1000 : ℝ) from rfl]
  have hnec := negative_BT_necessary (k := k) (l := lN d) (c := cN d) (η := 19/50)
    hq hC hnormal hab (by norm_num [k])
    (by linarith [hb.2.2.1]) hc (by norm_num : (0:ℝ)≤19/50) hG hs' hB hflat hf
  have hinc := BT_increment_lower hab hvar hd (Ioc_subset_Icc_self hs) hB
  have hgain := ShortSecantGain.negative_BT_gain (q := qCap)
    (by norm_num [qCap]) le_rfl hd hs
  have hstrict := scalar_min_positive hd
  dsimp [d] at *
  linarith

theorem BT_contact (C : SignedCycle) (j : Fin 4) :
    C.Feasible B j ↔ quarterFeasible (C.point B) (C.point T) (delta C.theta B) j := by
  simp [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,next,B,T,
    quarterFeasible,sub_nonneg]

theorem TD_contact (C : SignedCycle) (j : Fin 4) :
    C.Feasible T j ↔ zeroFeasible (C.point T) (C.point D) (delta C.theta T) j := by
  simp [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,next,T,D,
    zeroFeasible,sub_nonneg]

theorem reselect_TD {C : SignedCycle} {ab td : Fin 4}
    (hf : ∀ i,C.Feasible i (owners ab 2 td i)) (hT : C.Feasible T 0) :
    ∀ i,C.Feasible i (owners ab 2 0 i) := by
  intro i
  by_cases hi : i=T
  · subst hi
    exact hT
  · have he : ∀ ab td : Fin 4,∀ j : Vertex,j≠T → owners ab 2 0 j=owners ab 2 td j := by
      decide
    rw [he ab td i hi]
    exact hf i

theorem reselect_BT {C : SignedCycle} {ab bt : Fin 4}
    (hf : ∀ i,C.Feasible i (owners ab bt 0 i)) (hB : C.Feasible B 2) :
    ∀ i,C.Feasible i (owners ab 2 0 i) := by
  intro i
  by_cases hi : i=B
  · subst hi
    exact hB
  · have he : ∀ ab bt : Fin 4,∀ j : Vertex,j≠B → owners ab 2 0 j=owners ab bt 0 j := by
      decide
    rw [he ab bt i hi]
    exact hf i

theorem negative_TD_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hTb : (C.point T).Boundary q)
    (hT : delta C.theta T<0)
    (hf : ∀ i,C.Feasible i (owners ab 2 2 i)) : False := by
  let s : ℝ := -delta C.theta T
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next T) T)⟩
  have hTs : delta C.theta T= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (delta C.theta B) 2 :=
    (BT_contact C 2).1 (by simpa [owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) (-s) 2 := by
    rw [← hTs]
    exact (TD_contact C 2).1 (by simpa [owners,T] using hf T)
  have he := NegativeTEntry.negative_TD_entry (hC.sorted B) (hC.sorted T) (hC.sorted D)
    (hC.contained B) hTb (hC.contained D) (hC.core T) (hC.core D)
    hq hnormal.D_nonpos hs hBT hTD
  rcases he with hsecondary | ⟨hcore,hflat,hy,hyu,hshort⟩
  · have hsecondary' : C.Feasible T 0 := (TD_contact C 0).2 (by simpa [hTs] using hsecondary)
    exact secondary_T_false hq hC hnormal hvar hab hG (reselect_TD hf hsecondary')
  · exact flat_negative_TD_false hq hC hnormal hvar hab hG ⟨hs.1,hshort.le⟩ hTs hflat hf

theorem negative_BT_aligned_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hTb : (C.point T).Boundary q)
    (hB : delta C.theta B<0) (halign : delta C.theta T=0)
    (hf : ∀ i,C.Feasible i (owners ab 3 0 i)) : False := by
  by_cases hsecondary : C.Feasible B 2
  · exact secondary_T_false hq hC hnormal hvar hab hG (reselect_BT hf hsecondary)
  let s : ℝ := -delta C.theta B
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next B) B)⟩
  have hBs : delta C.theta B= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (-s) 3 := by
    rw [← hBs]
    exact (BT_contact C 3).1 (by simpa [owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) 0 0 := by
    rw [← halign]
    exact (TD_contact C 0).1 (by simpa [owners,T] using hf T)
  have hnot : ¬quarterFeasible (C.point B) (C.point T) (-s) 2 := by
    intro hh
    exact hsecondary ((BT_contact C 2).2 (by simpa [hBs] using hh))
  obtain ⟨hcore,hflat,hy,hyu,hshort⟩ := NegativeTEntry.negative_BT_aligned_entry
    (hC.sorted B) (hC.sorted T) (hC.sorted D) (hC.contained B) hTb (hC.contained D)
    (hC.core D) hq hnormal.B_nonpos hnormal.D_nonpos hs hBT hTD hnot
  exact flat_negative_BT_false hq hC hnormal hvar hab hG ⟨hs.1,hshort.le⟩ hBs hflat hf

/-- The full original secondary-E owner union after T-pair preprocessing.
The only frame alignment used is the actual negative-BT endpoint clause. -/
theorem preprocessed_secondary_E_false {C : SignedCycle} {q : ℝ} {ab bt td : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hTb : (C.point T).Boundary q)
    (hT : (bt=2 ∧ td=0) ∨ (bt=2 ∧ td=2) ∨
      (bt=3 ∧ td=0 ∧ (delta C.theta B<0 → delta C.theta T=0)))
    (hf : ∀ i,C.Feasible i (owners ab bt td i)) : False := by
  rcases hT with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl,halign⟩
  · exact secondary_T_false hq hC hnormal hvar hab hG hf
  · by_cases ht : 0≤delta C.theta T
    · exact positive_TD_false hq hC hnormal hvar hab hG ht hf
    · exact negative_TD_false hq hC hnormal hvar hab hG hTb (lt_of_not_ge ht) hf
  · by_cases hb : 0≤delta C.theta B
    · exact positive_BT_false hq hC hnormal hvar hab hG hb hf
    · have hb' : delta C.theta B<0 := lt_of_not_ge hb
      exact negative_BT_aligned_false hq hC hnormal hvar hab hG hTb hb' (halign hb') hf

end SquaresInCircles.Eight.NegativeSecondaryEExclusion
end
end
end
