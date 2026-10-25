module

public import SquaresInCircles.Eight.TableFree.PositiveOrdinaryEnvelope
public import SquaresInCircles.Eight.TableFree.RelaxedSameBlock
public import SquaresInCircles.Eight.TableFree.OrdinaryShortSecantGrowth

/-!
# Concrete ordinary coefficients for the two negative-T stresses

Uncompiled source draft. The only enlarged coefficient is the actual
`c_N(d) / cos s`. The TD case has `s ≤ .3`; the BT case has `s ≤ .09`.
Every correlated, high-angle, and low-angle bound below is proved for
these coefficients and retains the original value of `s`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.NegativeOrdinaryParameters
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

end SquaresInCircles.Eight.TableFree.NegativeOrdinaryParameters
