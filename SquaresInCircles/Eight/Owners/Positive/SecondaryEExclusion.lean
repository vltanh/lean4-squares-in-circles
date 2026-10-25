module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Boundary.ActualOrdinaryBlocks
public import SquaresInCircles.Eight.Frames.Ordinary.AngleConcentration
public import SquaresInCircles.Eight.Frames.Ordinary.NegativeSlope
public import SquaresInCircles.Eight.Frames.Ordinary.PositiveEnvelope
public import SquaresInCircles.Eight.Owners.Endpoint.Principles
public import SquaresInCircles.Eight.Owners.Positive.SplitComparison
public import SquaresInCircles.Eight.Owners.Positive.ScalarTransfer
public import SquaresInCircles.Eight.Owners.Positive.SplitCalculus
public import SquaresInCircles.Eight.Owners.Positive.StressCoefficients

/-!
# Eight squares: positive GA with both separators at E secondary

The weak separating-axis contacts, the seven-angle budgets, the ordinary envelope on the whole
angle range, the split of the positive primary and the strict scalar inequalities combine to
exclude the three nonnegative-T regimes (`secondary_T_false`, `positive_TD_false`,
`positive_BT_false`), for both owners of AB. E has no sign or radial assumption, the selected
contacts are used as they are, and the radius is only bounded above by `qCap`.
-/

section
/-!
## Coefficient domains for the three nonnegative-T regimes

Inequalities for the stress coefficients (`Bounds`): the dependence on the split is kept, and the
conditions for low and high `d` follow from the coefficient polynomials (`low_P`, `high_P`,
`low_N`, `high_N`, `familyP_td`, `familyP_bt`, `familyN`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveOrdinaryParameters
open PositiveStressCoefficients SecondaryEStress PositivePrimaryBaselines

structure Bounds (d l n b t : ℝ) : Prop where
  angle : d∈Icc 0 frameCap
  ell_lower : 1/2<l
  ell_upper : l<k
  H_lower : k≤n
  H_upper : n≤1
  B_lower : k≤b
  B_upper : b≤2069/2000
  D_lower : k≤t
  D_upper : t≤2069/2000
  correlated : ratio d*b≤l
  high : 3/10≤d → (2/3)*b≤l
  low : d≤3/10 → b≤1 ∧ t≤1 ∧ lP d≤l ∧ l≤1631/2500

theorem tilted_le_one {η x : ℝ} (hη : η∈Icc 0 (19/50))
    (hx : x∈Icc 0 frameCap) : tiltedWeight k η x≤1 := by
  have hnon : 0≤tiltedWeight k η x :=
    tiltedWeight_nonneg (by norm_num [k]) hη.1 hx
  have hη2 := pow_le_pow_left₀ hη.1 hη.2 2
  have he : (Real.cos x+η*Real.sin x)^2+(η*Real.cos x-Real.sin x)^2=1+η^2 := by
    linear_combination (1+η^2)*(Real.sin_sq_add_cos_sq x)
  have hsquare := sq_nonneg (η*Real.cos x-Real.sin x)
  have hbound := mul_le_mul_of_nonneg_left
    (show (Real.cos x+η*Real.sin x)^2≤1+η^2 by linarith) (sq_nonneg k)
  dsimp [tiltedWeight,k] at *
  nlinarith

theorem P_weight_range {d x : ℝ} (hd : d∈Icc 0 frameCap) (hx : x∈Icc 0 d) :
    k≤tiltedWeight k (etaP d) x ∧ tiltedWeight k (etaP d) x≤1 := by
  have hb := coefficient_bounds hd
  have hη : etaP d∈Icc 0 (19/50) := by
    exact ⟨by linarith [hb.2.2.2.2.2.2.1],by linarith [hb.2.2.2.2.2.2.2.1]⟩
  exact ⟨(tiltedWeight_bounds hd hx).1,tilted_le_one hη ⟨hx.1,hx.2.trans hd.2⟩⟩

theorem N_weight_range {d : ℝ} (hd : d∈Icc 0 frameCap) :
    k≤tiltedWeight k (19/50) d ∧ tiltedWeight k (19/50) d≤1 := by
  have hb := coefficient_bounds hd
  have hη : etaP d≤19/50 := by linarith [hb.2.2.2.2.2.2.2.1]
  have hsin := (transport_trig hd).2.2.1
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hη hsin) (show 0≤k by norm_num [k])
  have hbase := (P_weight_range hd ⟨hd.1,le_rfl⟩).1
  refine ⟨?_,tilted_le_one ⟨by norm_num,le_rfl⟩ hd⟩
  dsimp [tiltedWeight] at *
  nlinarith

theorem high_P {d : ℝ} (hd : d∈Icc 0 frameCap) (hlarge : 3/10≤d) :
    (2/3)*k*(1+d/4)≤lP d := by
  have h2 : d≤7/10 := hd.2
  have hd2 : d^2≤(7/10 : ℝ)*d := by nlinarith [hd.1]
  dsimp [lP,k]
  nlinarith

theorem high_N {d : ℝ} (hd : d∈Icc 0 frameCap) (hlarge : 3/10≤d) :
    (2/3)*cN d≤lN d := by
  have h2 : d≤7/10 := hd.2
  have hd2 : d^2≤(7/10 : ℝ)*d := by nlinarith [hd.1]
  dsimp [lN,cN]
  nlinarith

theorem low_P {d : ℝ} (_hd : d∈Icc 0 frameCap) (hsmall : d≤3/10) :
    lP d≤1631/2500 := by dsimp [lP]; nlinarith [sq_nonneg d]

theorem low_N {d : ℝ} (hd : d∈Icc 0 frameCap) (hsmall : d≤3/10) :
    cN d≤1 ∧ lP d≤lN d ∧ lN d≤1631/2500 := by
  have hd2 : d^2≤(3/10 : ℝ)*d := by nlinarith [hd.1,hsmall]
  have hupper := mul_nonneg (show 0≤3/10-d by linarith)
    (show 0≤11/20-(1/5 : ℝ)*(d+3/10) by linarith)
  dsimp [cN,lP,lN]
  constructor
  · nlinarith [sq_nonneg d]
  constructor <;> nlinarith

theorem P_base_ratio {d : ℝ} (hd : d∈Icc 0 frameCap) : ratio d*k≤lP d := by
  have h := (correlated_ratios hd).1
  have hr : 0≤ratio d := by dsimp [ratio]; linarith [hd.1]
  have hnon := mul_nonneg (mul_nonneg hr (show 0≤k by norm_num [k])) hd.1
  nlinarith

theorem familyP_td {d x z : ℝ} (hd : d∈Icc 0 frameCap)
    (hx : x∈Icc 0 d) (hz : z∈Icc 0 d) :
    Bounds d (lP d) (tiltedWeight k (etaP d) x) (tiltedWeight k (etaP d) z) k := by
  have hb := coefficient_bounds hd
  have hn := P_weight_range hd hx
  have hm := P_weight_range hd hz
  refine ⟨hd,hb.1,hb.2.1,hn.1,hn.2,hm.1,by linarith [hm.2],
    le_rfl,by norm_num [k],(varying_B_ratio hd hz).1.le,?_,?_⟩
  · intro hlarge
    have hweight := mul_le_mul_of_nonneg_left (tiltedWeight_bounds hd hz).2
      (by norm_num : (0:ℝ)≤2/3)
    nlinarith [high_P hd hlarge]
  · intro hsmall
    exact ⟨hm.2,by norm_num [k],le_rfl,low_P hd hsmall⟩

theorem familyP_bt {d x z : ℝ} (hd : d∈Icc 0 frameCap)
    (hx : x∈Icc 0 d) (hz : z∈Icc 0 d) :
    Bounds d (lP d) (tiltedWeight k (etaP d) x) k (tiltedWeight k (etaP d) z) := by
  have hb := coefficient_bounds hd
  have hn := P_weight_range hd hx
  have hm := P_weight_range hd hz
  refine ⟨hd,hb.1,hb.2.1,hn.1,hn.2,le_rfl,by norm_num [k],
    hm.1,by linarith [hm.2],P_base_ratio hd,?_,?_⟩
  · intro hlarge
    have hnon := mul_nonneg (show 0≤(2/3 : ℝ)*k by norm_num [k]) hd.1
    nlinarith [high_P hd hlarge]
  · intro hsmall
    exact ⟨by norm_num [k],hm.2,le_rfl,low_P hd hsmall⟩

theorem familyN {d : ℝ} (hd : d∈Icc 0 frameCap) :
    Bounds d (lN d) (tiltedWeight k (19/50) d) (cN d) (cN d) := by
  have hb := coefficient_bounds hd
  have hn := N_weight_range hd
  refine ⟨hd,hb.2.2.1,hb.2.2.2.1,hn.1,hn.2,hb.2.2.2.2.1,
    hb.2.2.2.2.2.1,hb.2.2.2.2.1,hb.2.2.2.2.2.1,
    (varying_B_ratio hd ⟨le_rfl,hd.1⟩).2.le,high_N hd,?_⟩
  intro hsmall
  have h := low_N hd hsmall
  exact ⟨h.1,h.1,h.2.1,h.2.2⟩

end SquaresInCircles.Eight.PositiveOrdinaryParameters
end
end
end

section
/-!
## The complete ordinary angular lower bound with no negative primary removed

Both signs are concentrated only in an analytic
minorant of the original sum. Correlated same-block saturation and the
two exact coefficient regimes cover every resulting endpoint. This file
then applies the result to the four blocks of the original seven angles.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.PositiveOrdinaryEnvelope
open Candidate PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryAngleConcentration CorrelatedSameBlock
open OrdinaryPositiveEnvelope OrdinaryNegativeEnvelope OrdinaryNegativeSlope
open VaryingBComparison PositiveStressCoefficients PositiveOrdinaryParameters
open ActualOrdinaryBlocks

def ps (n l t : ℝ) : Fin 4 → ℝ := ![n,l,l,min 1 t]
def qs (b t : ℝ) : Fin 4 → ℝ := ![1,k,b,max 1 t]

theorem block_coefficients {d l n b t : ℝ} (h : Bounds d l n b t)
    (C : SignedCycle) (ab bt td : Fin 4) (i : Fin 4) :
    (blocks C ab bt td n k l b t i).p=ps n l t i ∧
    (blocks C ab bt td n k l b t i).q=qs b t i := by
  have hlb : l≤b := h.ell_upper.le.trans h.B_lower
  fin_cases i <;>
    simp [blocks,Block.p,Block.q,ps,qs,min_eq_left h.H_upper,max_eq_right h.H_upper,
      min_eq_left h.ell_upper.le,max_eq_right h.ell_upper.le,min_eq_left hlb,max_eq_right hlb]

theorem domains {d l n b t : ℝ} (h : Bounds d l n b t) (i : Fin 4) :
    0<ps n l t i ∧ ps n l t i≤qs b t i ∧ qs b t i≤2*ps n l t i ∧
    ratio d*qs b t i≤ps n l t i ∧ k≤qs b t i ∧ qs b t i≤2069/2000 := by
  have hk : k=(863/1000 : ℝ) := rfl
  have hd7 : d≤7/10 := h.angle.2
  have hr0 : 117/200≤ratio d := by dsimp [ratio]; linarith [h.angle.1]
  have hr1 : ratio d≤1527/2000 := by dsimp [ratio]; linarith
  have hDlo : k≤ min 1 t := le_min (by norm_num [k]) h.D_lower
  have hDlo' : (863/1000 : ℝ)≤ min 1 t := hDlo
  have hDhi : max 1 t≤2069/2000 := max_le (by norm_num) h.D_upper
  have hDq0 : 0≤ max 1 t := (by norm_num : (0:ℝ)≤1).trans (le_max_left 1 t)
  have hDcorr : ratio d*max 1 t≤ min 1 t := by
    have hp := mul_le_mul hr1 hDhi hDq0 (by norm_num : (0:ℝ)≤1527/2000)
    linarith
  have hAcorr : ratio d*k≤l :=
    (mul_le_mul_of_nonneg_left h.B_lower (by linarith)).trans h.correlated
  have hB0 : 0≤b := by linarith [h.B_lower]
  have hBtwice : b≤2*l := by
    have hp := mul_le_mul_of_nonneg_right hr0 hB0
    linarith [h.correlated]
  have hAtwice : k≤2*l := by linarith [h.ell_lower]
  have hDtwice : max 1 t≤2*min 1 t := by linarith
  fin_cases i
  · show 0<n ∧ n≤1 ∧ 1≤2*n ∧ ratio d*1≤n ∧ k≤1 ∧ (1:ℝ)≤2069/2000
    have hH := h.H_lower
    exact ⟨by linarith,h.H_upper,by linarith,by linarith,by linarith,by norm_num⟩
  · show 0<l ∧ l≤k ∧ k≤2*l ∧ ratio d*k≤l ∧ k≤k ∧ k≤2069/2000
    exact ⟨by linarith [h.ell_lower],h.ell_upper.le,hAtwice,hAcorr,le_rfl,by linarith⟩
  · show 0<l ∧ l≤b ∧ b≤2*l ∧ ratio d*b≤l ∧ k≤b ∧ b≤2069/2000
    exact ⟨by linarith [h.ell_lower],h.ell_upper.le.trans h.B_lower,hBtwice,h.correlated,
      h.B_lower,h.B_upper⟩
  · show 0< min 1 t ∧ min 1 t≤ max 1 t ∧ max 1 t≤2*min 1 t ∧ ratio d*max 1 t≤ min 1 t ∧
      k≤ max 1 t ∧ max 1 t≤2069/2000
    exact ⟨by linarith,min_le_max,hDtwice,hDcorr,hDlo.trans min_le_max,hDhi⟩

theorem high_domains {d l n b t : ℝ} (h : Bounds d l n b t) (hd : 3/10≤d)
    (i : Fin 4) : (2/3)*qs b t i≤ps n l t i := by
  have hH : (2/3 : ℝ)≤n := by linarith [h.H_lower,show k=(863/1000 : ℝ) from rfl]
  have hA : (2/3)*k≤l :=
    (mul_le_mul_of_nonneg_left h.B_lower (by norm_num)).trans (h.high hd)
  have hDlo : (863/1000 : ℝ)≤ min 1 t := le_min (by norm_num) h.D_lower
  have hDhi : max 1 t≤2069/2000 := max_le (by norm_num) h.D_upper
  have hD : (2/3)*max 1 t≤ min 1 t := by linarith
  fin_cases i
  · show (2/3)*1≤n
    linarith
  · show (2/3)*k≤l
    exact hA
  · show (2/3)*b≤l
    exact h.high hd
  · show (2/3)*max 1 t≤ min 1 t
    exact hD

theorem low_domains {d l n b t : ℝ} (h : Bounds d l n b t) (hd : d≤3/10)
    (i : Fin 4) : lP d≤ps n l t i ∧ qs b t i≤1 := by
  have hl := h.low hd
  have hlk : lP d≤k := hl.2.2.1.trans h.ell_upper.le
  have hDlo : k≤ min 1 t := le_min (by norm_num [k]) h.D_lower
  fin_cases i
  · show lP d≤n ∧ (1:ℝ)≤1
    exact ⟨hlk.trans h.H_lower,le_refl _⟩
  · show lP d≤l ∧ k≤1
    exact ⟨hl.2.2.1,by norm_num [k]⟩
  · show lP d≤l ∧ b≤1
    exact ⟨hl.2.2.1,hl.1⟩
  · show lP d≤ min 1 t ∧ max 1 t≤1
    exact ⟨hlk.trans hDlo,max_le (le_refl _) hl.2.1⟩

theorem single_negative_lower {d l n b t w : ℝ} (h : Bounds d l n b t)
    (hw : w∈Icc 0 d) (i : Fin 4) :
    V (Real.sqrt qCap) l k w≤V (Real.sqrt qCap) (ps n l t i) (qs b t i) w := by
  have hw' : w∈Icc 0 frameCap := ⟨hw.1,hw.2.trans h.angle.2⟩
  have hlhalf : k/2≤l := by norm_num [k]; linarith [h.ell_lower]
  have hchainH := near_equal_chain (by norm_num [k] : (43/50 : ℝ)≤k)
    h.H_lower h.H_upper hlhalf h.ell_upper.le hw'
  have hH := hchainH.1.trans (hchainH.2.1.trans hchainH.2.2)
  have hB := V_larger_coefficient (by linarith [h.ell_lower]) h.ell_upper.le
    h.B_lower h.correlated h.angle hw
  have hD : V (Real.sqrt qCap) l k w≤
      V (Real.sqrt qCap) (min 1 t) (max 1 t) w := by
    by_cases ht : t≤1
    · have hc := near_equal_chain (by norm_num [k] : (43/50 : ℝ)≤k)
        h.D_lower ht hlhalf h.ell_upper.le hw'
      simpa [min_eq_right ht,max_eq_left ht] using hc.1.trans (hc.2.1.trans hc.2.2)
    · have ht1 : 1≤t := (lt_of_not_ge ht).le
      have hc := near_equal_chain (by norm_num [k] : (43/50 : ℝ)≤k)
        (by norm_num [k] : k≤1) le_rfl hlhalf h.ell_upper.le hw'
      have hlarge := V_larger_coefficient (l := 1) (k := 1) (q := t)
        (by norm_num) le_rfl ht1
        (by dsimp [ratio,frameCap]; nlinarith [h.D_upper])
        (show frameCap∈Icc 0 frameCap by constructor; norm_num [frameCap]; rfl) hw'
      simpa [min_eq_left ht1,max_eq_right ht1] using
        (hc.1.trans (hc.2.1.trans hc.2.2)).trans hlarge
  fin_cases i
  · simpa [ps,qs] using hH
  · simp [ps,qs]
  · simpa [ps,qs] using hB
  · simpa [ps,qs] using hD

theorem target_zero_slope {l : ℝ} (hl : 1/2<l) (hlu : l≤1631/2500) :
    Vd (Real.sqrt qCap) l k 0<26/25 := by
  have hl0 : 0<l := by linarith
  have hk0 : 0<k := by norm_num [k]
  have hN := pairNorm_pos (p := l) (q := k) (t := 0) hl0 hk0 (by norm_num [frameCap])
  have hN2 := pairNorm_sq (p := l) (q := k) (t := 0) hl0 hk0 (by norm_num [frameCap])
  simp only [pairEnergy,pairProduct,Real.sin_zero,mul_zero,add_zero] at hN2
  have hl2 := pow_le_pow_left₀ hl0.le hlu 2
  have hQ := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hnum : (Real.sqrt qCap*l*k)^2=qCap*l^2*k^2 := by rw [mul_pow,mul_pow,hQ]
  have hstrict : qCap*l^2*k^2<(26/25 : ℝ)^2*(l^2+k^2) := by
    rw [show qCap=(9789/2500 : ℝ) from rfl,show k=(863/1000 : ℝ) from rfl]
    linarith
  have hcross : Real.sqrt qCap*l*k<(26/25)*pairNorm l k 0 := by
    apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
    rw [hnum,mul_pow,hN2]
    exact hstrict
  have hdiv := (div_lt_iff₀ hN).2 hcross
  have he : Vd (Real.sqrt qCap) l k 0=Real.sqrt qCap*l*k/pairNorm l k 0 := by
    simp only [Vd,mixedNDerivative,normD1,pairProduct,sub_zero,Real.sin_zero,Real.cos_zero]
    ring
  rw [he]
  exact hdiv

theorem target_low_upper {d l n b t : ℝ} (h : Bounds d l n b t) (hd : d≤3/10) :
    V (Real.sqrt qCap) l k d≤(26/25)*d := by
  have hp : 0<l := by linarith [h.ell_lower]
  have hqp : k≤2*l := by norm_num [k]; linarith [h.ell_lower]
  exact (V_tangent_zero hp h.ell_upper.le hqp h.angle).trans
    (mul_le_mul_of_nonneg_right (target_zero_slope h.ell_lower (h.low hd).2.2.2).le h.angle.1)

theorem low_reserve {d : ℝ} (hd : d∈Icc 0 (3/10)) :
    0<(87/100)*lP d-(26/25)*d-(109/200)*(frameCap-d) := by
  have hd2 := pow_le_pow_left₀ hd.1 hd.2 2
  dsimp [lP,frameCap]
  nlinarith

theorem separated_saturated_lower {d l n b t : ℝ} (h : Bounds d l n b t)
    (i j : Fin 4) :
    V (Real.sqrt qCap) l k d≤
      U (Real.sqrt qCap) (ps n l t i) (qs b t i) (frameCap-d)+
        V (Real.sqrt qCap) (ps n l t j) (qs b t j) frameCap := by
  have hi := domains h i
  have hj := domains h j
  have ha : frameCap-d∈Icc 0 frameCap :=
    ⟨by linarith [h.angle.2],by linarith [h.angle.1]⟩
  have hU := U_lower (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hi.1 hi.2.1 hi.2.2.1 ha
  by_cases hd : d≤3/10
  · have hloi := low_domains h hd i
    have hloj := low_domains h hd j
    have hV := V_endpoint_lower sqrt_cap_lower hj.1 hj.2.1 hj.2.2.1
    have hqmul := mul_le_mul_of_nonneg_right hloi.2 ha.1
    have hpl := mul_le_mul_of_nonneg_left hloj.1 (by norm_num : (0:ℝ)≤87/100)
    have htarget := target_low_upper h hd
    have hreserve := low_reserve ⟨h.angle.1,hd⟩
    generalize frameCap=F at *
    linarith
  · have hlarge : 3/10≤d := (lt_of_not_ge hd).le
    have hV := V_growth hj.1 hj.2.1 (high_domains h hlarge j) h.angle
      (show frameCap∈Icc 0 frameCap by constructor <;> norm_num [frameCap]) h.angle.2
    have hsingle := single_negative_lower h ⟨h.angle.1,le_rfl⟩ j
    have hqi := mul_le_mul_of_nonneg_right hi.2.2.2.2.2 ha.1
    have hqj := mul_le_mul_of_nonneg_right hj.2.2.2.2.1 ha.1
    have hreserve : 0≤((2/3)*k-(109/200)*(2069/2000))*
        (frameCap-d) := mul_nonneg (by norm_num [k]) ha.1
    generalize frameCap=F at *
    linarith

theorem mixed_sum_lower {d l n b t : ℝ} (h : Bounds d l n b t)
    (P N : Fin 4 → ℝ) (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑ i,P i)≤frameCap-d) (hbalance : (∑ i,N i)=d+∑ i,P i) :
    V (Real.sqrt qCap) l k d≤
      ∑ i,mixedBlock (Real.sqrt qCap) (ps n l t i) (qs b t i) (P i) (N i) := by
  obtain ⟨i,j,hconc⟩ := ordinary_concentration (Real.sqrt qCap) (ps n l t) (qs b t) P N
    (Real.sqrt_nonneg qCap) (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
    (fun i => (domains h i).1) (fun i => (domains h i).2.1)
    (fun i => (domains h i).2.2.1) hP hN h.angle hbudget hbalance
  apply le_trans _ hconc
  apply le_min
  · exact single_negative_lower h ⟨h.angle.1,le_rfl⟩ j
  · by_cases hij : i=j
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hij)]
      have hi := domains h i
      have hsame := negative_surplus (R := Real.sqrt qCap)
        (hi.1.trans_le hi.2.1).le hi.2.2.2.1 h.angle
        (show (0:ℝ)∈Icc 0 d from ⟨le_rfl,h.angle.1⟩)
      have he : mixedBlock (Real.sqrt qCap) (ps n l t i) (qs b t i) (frameCap-d) frameCap=
          M (Real.sqrt qCap) (ps n l t i) (qs b t i) d := by
        dsimp [mixedBlock,M]
        rw [show frameCap-d-frameCap= -d by ring]
      simp only [sub_zero,he] at hsame
      exact (single_negative_lower h ⟨h.angle.1,le_rfl⟩ i).trans hsame
    · simpa only [ite_eq_right_of_eq_false _ _ (eq_false hij)] using separated_saturated_lower h i j

/-- The completed lower bound is applied to the actual four block sums,
with the exact original seven-angle budget. -/
theorem increment_lower {C : SignedCycle} {ab bt td : Fin 4} {l n b t : ℝ}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hBT : bt=3 → 0≤delta C.theta B)
    (hTD : td=2 → 0≤delta C.theta T)
    (h : Bounds (removed C bt td) l n b t) :
    V (Real.sqrt qCap) l k (removed C bt td)≤
      ∑ i,(blocks C ab bt td n k l b t i).increment (Real.sqrt qCap) := by
  let Bs := blocks C ab bt td n k l b t
  have hb := block_budgets hab hbt htd n k l b t hvar hG hBT hTD
  have hP : ∀ i,0≤(Bs i).P := fun i => (Bs i).P_nonneg
  have hN : ∀ i,0≤(Bs i).N := fun i => (Bs i).N_nonneg
  have hsumP : (∑ i,(Bs i).P)≤frameCap := by linarith [hb.1.1,hb.2.1]
  have hsumN : (∑ i,(Bs i).N)≤frameCap := by linarith [hb.2.1,hb.2.2]
  have hPi (i : Fin 4) : (Bs i).P≤frameCap :=
    (Finset.single_le_sum (fun j _ => hP j) (Finset.mem_univ i)).trans hsumP
  have hNi (i : Fin 4) : (Bs i).N≤frameCap :=
    (Finset.single_le_sum (fun j _ => hN j) (Finset.mem_univ i)).trans hsumN
  have hsum := mixed_sum_lower h (fun i => (Bs i).P) (fun i => (Bs i).N)
    hP hN hb.2.1 hb.2.2
  refine hsum.trans (Finset.sum_le_sum fun i _ => ?_)
  have hc := block_coefficients h C ab bt td i
  have hminor := (blocks C ab bt td n k l b t i).minorant (Real.sqrt qCap)
    (by rw [hc.1]; exact (domains h i).1.le) (hPi i) (hNi i)
  rw [hc.1,hc.2] at hminor
  exact hminor

end SquaresInCircles.Eight.PositiveOrdinaryEnvelope
end
end
end

section
/-!
## The positive split lies above its smaller scalar endpoint

The curvature estimate of the split is quantitative and holds on the whole interval
(`splitSecond_le`), so the split exceeds the baseline `familyPBaseline` by `(k/40) x (d - x)`
(`familyP_split_lower`); the scalar endpoints need not be geometrically feasible. Both baselines
of T dominate `familyPBaseline` (`tdBaseline_ge_familyP`, `btBaseline_ge_familyP`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveSplitConcavity
open PositiveAngularEnvelope PositivePrimaryBaselines PositiveSplitComparison
open PositiveStressCoefficients PositiveSplitCalculus

private theorem weight_lt {η t : ℝ}
    (hη : η∈Icc (1/4) (7303/20000)) (ht : t∈Icc 0 frameCap) :
    0≤k*PositiveSplitCalculus.f η t ∧ k*PositiveSplitCalculus.f η t<23/25 := by
  obtain ⟨hc,_,hs,_,_⟩ := transport_trig ht
  have hf : 0≤PositiveSplitCalculus.f η t := by unfold PositiveSplitCalculus.f; nlinarith [hη.1]
  have hm : 0≤k*PositiveSplitCalculus.f η t := mul_nonneg (by norm_num [k]) hf
  have hη2 := pow_le_pow_left₀ (show 0≤η by linarith [hη.1]) hη.2 2
  have he := f_energy η t
  have hm2 : (k*PositiveSplitCalculus.f η t)^2<(23/25 : ℝ)^2 := by
    dsimp [k]
    nlinarith [sq_nonneg (df η t)]
  exact ⟨hm,by nlinarith⟩

private theorem ratio_bound {r η t a : ℝ} (hr : 0<r)
    (ha : 0<a) (_hm : 0≤k*PositiveSplitCalculus.f η t)
    (hstrict : qCap*(k*PositiveSplitCalculus.f η t)^2<a^2*(r^2+(k*PositiveSplitCalculus.f η t)^2)) :
    Real.sqrt qCap*(k*PositiveSplitCalculus.f η t)/norm r k η t<a := by
  have hN := norm_pos hr k η t
  have hsq := norm_sq hr k η t
  have hR : (Real.sqrt qCap)^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hleft : (Real.sqrt qCap*(k*PositiveSplitCalculus.f η t))^2=
      qCap*(k*PositiveSplitCalculus.f η t)^2 := by
    rw [mul_pow,hR]
  apply (div_lt_iff₀ hN).2
  dsimp [radicand] at hsq
  apply lt_of_pow_lt_pow_left₀ 2 (mul_pos ha hN).le
  rw [hleft,show (a*norm r k η t)^2=a^2*(norm r k η t)^2 by ring,hsq]
  exact hstrict

private theorem ratio_one_lt {η t : ℝ}
    (hη : η∈Icc (1/4) (7303/20000)) (ht : t∈Icc 0 frameCap) :
    Real.sqrt qCap*(k*PositiveSplitCalculus.f η t)/norm 1 k η t<29/20 := by
  obtain ⟨hm,hm1⟩ := weight_lt hη ht
  have hm2 := pow_le_pow_left₀ hm hm1.le 2
  apply ratio_bound (by norm_num) (by norm_num) hm
  norm_num [qCap] at *
  nlinarith

private theorem ratio_l_lt {d η t : ℝ} (hd : d∈Icc 0 frameCap)
    (hη : η∈Icc (1/4) (7303/20000)) (ht : t∈Icc 0 frameCap) :
    Real.sqrt qCap*(k*PositiveSplitCalculus.f η t)/norm (lP d) k η t<7/4 := by
  obtain ⟨hm,hm1⟩ := weight_lt hη ht
  have hl := (coefficient_bounds hd).1
  have hl2 : (1/2 : ℝ)^2≤(lP d)^2 := pow_le_pow_left₀ (by norm_num) hl.le 2
  have hm2 := pow_le_pow_left₀ hm hm1.le 2
  apply ratio_bound (by linarith) (by norm_num) hm
  norm_num [qCap] at *
  nlinarith

/-- The two sine coefficient bounds are positive square comparisons of
concave quadratics; both endpoint checks are contained in the same proof. -/
private theorem sine_coefficients {η : ℝ}
    (hη : η∈Icc (1/4) (7303/20000)) :
    Real.sqrt qCap*Real.sqrt (1+η^2)-1-(11/20 : ℝ)*η<907/1000 ∧
    Real.sqrt qCap*Real.sqrt (1+η^2)-1-(1/4 : ℝ)*η<1017/1000 := by
  have hη0 : 0≤η := by linarith [hη.1]
  have hfactor := mul_nonneg (sub_nonneg.mpr hη.1) (sub_nonneg.mpr hη.2)
  have hroot : (Real.sqrt qCap*Real.sqrt (1+η^2))^2=qCap*(1+η^2) := by
    rw [mul_pow,Real.sq_sqrt (by norm_num [qCap]),Real.sq_sqrt (by positivity)]
  have hnonneg := mul_nonneg (Real.sqrt_nonneg qCap) (Real.sqrt_nonneg (1+η^2))
  constructor
  · have hsq : qCap*(1+η^2)<((1907/1000 : ℝ)+(11/20 : ℝ)*η)^2 := by
      norm_num [qCap] at *
      nlinarith
    have := lt_of_pow_lt_pow_left₀ 2 (by positivity) (hroot ▸ hsq)
    linarith
  · have hsq : qCap*(1+η^2)<((2017/1000 : ℝ)+(1/4 : ℝ)*η)^2 := by
      norm_num [qCap] at *
      nlinarith
    have := lt_of_pow_lt_pow_left₀ 2 (by positivity) (hroot ▸ hsq)
    linarith

theorem g_one_second_le {d t : ℝ} (hd : d∈Icc 0 frameCap)
    (ht : t∈Icc 0 frameCap) :
    gSecond (Real.sqrt qCap) 1 k (etaP d) t≤
      k*(-(11/20 : ℝ)*Real.cos t+(907/1000 : ℝ)*Real.sin t) := by
  have hb := coefficient_bounds hd
  have hη : etaP d∈Icc (1/4) (7303/20000) := ⟨hb.2.2.2.2.2.2.1,hb.2.2.2.2.2.2.2.1⟩
  have hc := transport_cos_pos (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hs := (transport_trig ht).2.2.1
  refine (gSecond_le (a := 29/20) (c := 907/1000) (Real.sqrt_nonneg qCap)
    (by norm_num : (0:ℝ)<1) (by norm_num [k] : (0:ℝ)≤k) (by linarith [hη.1]) hc.le hs
    (ratio_one_lt hη ht).le (by linarith [(sine_coefficients hη).1])).trans_eq ?_
  ring

theorem g_l_second_le {d t : ℝ} (hd : d∈Icc 0 frameCap)
    (ht : t∈Icc 0 frameCap) :
    gSecond (Real.sqrt qCap) (lP d) k (etaP d) t≤
      k*(-(1/4 : ℝ)*Real.cos t+(1017/1000 : ℝ)*Real.sin t) := by
  have hb := coefficient_bounds hd
  have hη : etaP d∈Icc (1/4) (7303/20000) := ⟨hb.2.2.2.2.2.2.1,hb.2.2.2.2.2.2.2.1⟩
  have hc := transport_cos_pos (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hs := (transport_trig ht).2.2.1
  refine (gSecond_le (a := 7/4) (c := 1017/1000) (Real.sqrt_nonneg qCap)
    (by linarith [hb.1] : (0:ℝ)<lP d) (by norm_num [k] : (0:ℝ)≤k) (by linarith [hη.1]) hc.le hs
    (ratio_l_lt hd hη ht).le (by linarith [(sine_coefficients hη).2])).trans_eq ?_
  ring

def splitA (d : ℝ) : ℝ := -(11/20 : ℝ)-(1/4 : ℝ)*Real.cos d+
  (1017/1000 : ℝ)*Real.sin d
def splitB (d : ℝ) : ℝ := (907/1000 : ℝ)-(1/4 : ℝ)*Real.sin d-
  (1017/1000 : ℝ)*Real.cos d

theorem split_coefficients {d : ℝ} (hd : d∈Icc 0 frameCap) :
    splitA d< -(17/200 : ℝ) ∧ splitB d< -(3/100 : ℝ) := by
  obtain ⟨hc,_,hs0,hs,hslt⟩ := transport_trig hd
  constructor
  · unfold splitA
    linarith
  · let F : ℝ → ℝ := fun x => (1/4 : ℝ)*Real.sin x+(1017/1000 : ℝ)*Real.cos x
    have hconc : ConcaveOn ℝ (Icc 0 frameCap) F := by
      apply concave_of_deriv2
        (f' := fun x => (1/4 : ℝ)*Real.cos x-(1017/1000 : ℝ)*Real.sin x)
        (f'' := fun x => -(1/4 : ℝ)*Real.sin x-(1017/1000 : ℝ)*Real.cos x)
      · intro x _
        exact (((Real.hasDerivAt_sin x).const_mul (1/4 : ℝ)).fun_add
          ((Real.hasDerivAt_cos x).const_mul (1017/1000 : ℝ))).congr_deriv (by ring)
      · intro x _
        exact (((Real.hasDerivAt_cos x).const_mul (1/4 : ℝ)).fun_sub
          ((Real.hasDerivAt_sin x).const_mul (1017/1000 : ℝ))).congr_deriv (by ring)
      · intro x hx
        obtain ⟨hcx,_,hsx,_,_⟩ := transport_trig hx
        linarith
    have hleft : (937/1000 : ℝ)<F 0 := by norm_num [F]
    have hright : (937/1000 : ℝ)<F frameCap := by
      have hc7 := cos_lower_six (by norm_num : (0:ℝ)≤7/10)
      have hs7 := sin_lower_seven (by norm_num : (0:ℝ)≤7/10)
      dsimp [F,frameCap]
      norm_num at hc7 hs7
      linarith
    have h := concave_gt_of_endpoints hconc hd hleft hright
    dsimp [F,splitB] at *
    linarith

def split (d x : ℝ) : ℝ :=
  tdBaseline (Real.sqrt qCap) k (lP d) (etaP d) x (d-x)
def splitDeriv (d x : ℝ) : ℝ :=
  gDeriv (Real.sqrt qCap) 1 k (etaP d) x-
    gDeriv (Real.sqrt qCap) (lP d) k (etaP d) (d-x)
def splitSecond (d x : ℝ) : ℝ :=
  gSecond (Real.sqrt qCap) 1 k (etaP d) x+
    gSecond (Real.sqrt qCap) (lP d) k (etaP d) (d-x)

theorem split_eq (d x : ℝ) :
    split d x=3+2*lP d-Real.sqrt qCap*(pairNorm k (lP d) 0+pairNorm 1 k 0)+
      g (Real.sqrt qCap) 1 k (etaP d) x+
      g (Real.sqrt qCap) (lP d) k (etaP d) (d-x) := by
  simp only [split,tdBaseline,zeroNorms,g,PositiveSplitCalculus.norm,
    PositiveSplitCalculus.radicand,PositiveSplitCalculus.f,SecondaryEStress.tiltedWeight,
    pairNorm_zero]
  ring

theorem split_hasDerivAt {d : ℝ} (hd : d∈Icc 0 frameCap) (x : ℝ) :
    HasDerivAt (split d) (splitDeriv d x) x := by
  have hl : 0<lP d := by linarith [(coefficient_bounds hd).1]
  have h1 := g_hasDerivAt (by norm_num : (0:ℝ)<1) (Real.sqrt qCap) k (etaP d) x
  have h2 := (g_hasDerivAt hl (Real.sqrt qCap) k (etaP d) (d-x)).comp x
    ((hasDerivAt_const x d).sub (hasDerivAt_id x))
  have h := ((hasDerivAt_const x
    (3+2*lP d-Real.sqrt qCap*(pairNorm k (lP d) 0+pairNorm 1 k 0))).add h1).add h2
  convert h using 1
  · funext t
    exact split_eq d t
  · dsimp [splitDeriv]
    ring

theorem splitDeriv_hasDerivAt {d : ℝ} (hd : d∈Icc 0 frameCap) (x : ℝ) :
    HasDerivAt (splitDeriv d) (splitSecond d x) x := by
  have hl : 0<lP d := by linarith [(coefficient_bounds hd).1]
  have h1 := gDeriv_hasDerivAt (by norm_num : (0:ℝ)<1) (Real.sqrt qCap) k (etaP d) x
  have h2 := (gDeriv_hasDerivAt hl (Real.sqrt qCap) k (etaP d) (d-x)).comp x
    ((hasDerivAt_const x d).sub (hasDerivAt_id x))
  convert h1.fun_sub h2 using 1
  · funext t
    simp only [splitDeriv,Function.comp_apply]
  · simp only [splitSecond]
    ring

theorem splitSecond_le {d x : ℝ} (hd : d∈Icc 0 frameCap) (hx : x∈Icc 0 d) :
    splitSecond d x≤-k/20 := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans hd.2⟩
  have hz : d-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [hx.1,hd.2]⟩
  have h1 := g_one_second_le hd hx'
  have h2 := g_l_second_le hd hz
  have hc := (transport_trig hx').1
  have hs := (transport_trig hx').2.2.1
  have hab := split_coefficients hd
  have ha := mul_le_mul_of_nonneg_right hab.1.le (show 0≤Real.cos x by linarith)
  have hb := mul_le_mul_of_nonneg_right hab.2.le hs
  have hid : -(11/20 : ℝ)*Real.cos x+(907/1000 : ℝ)*Real.sin x-
      (1/4 : ℝ)*Real.cos (d-x)+(1017/1000 : ℝ)*Real.sin (d-x)=
      splitA d*Real.cos x+splitB d*Real.sin x := by
    simp [splitA,splitB,Real.cos_sub,Real.sin_sub]
    ring
  have hsum : splitSecond d x≤k*(splitA d*Real.cos x+splitB d*Real.sin x) := by
    unfold splitSecond
    rw [← hid]
    nlinarith [h1,h2]
  norm_num [k] at *
  nlinarith

/-- The split exceeds its smaller endpoint `familyPBaseline d` by the reserve `(k/40) x (d - x)`. -/
theorem familyP_split_lower {d x : ℝ} (hd : d∈Icc 0 frameCap)
    (hx : x∈Icc 0 d) :
    familyPBaseline d+k/40*x*(d-x)≤ split d x := by
  have hg : ConcaveOn ℝ (Icc 0 d) (fun x => split d x+(k/20)/2*x^2) := by
    apply concave_of_deriv2
      (f' := fun x => splitDeriv d x+k/20*x)
      (f'' := fun x => splitSecond d x+k/20)
    · intro x _
      have hp : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
        simpa using hasDerivAt_pow 2 x
      exact ((split_hasDerivAt hd x).fun_add (hp.const_mul ((k/20)/2))).congr_deriv (by ring)
    · intro x _
      exact ((splitDeriv_hasDerivAt hd x).fun_add
        ((hasDerivAt_id' x).const_mul (k/20))).congr_deriv (by ring)
    · intro x hx
      linarith [splitSecond_le hd hx]
  have h := concave_endpoint_reserve (show 0≤k/20 by norm_num [k]) hx hg
  have hzero : split d 0=familyPBaseline d := by simp [split,familyPBaseline]
  have hend : split d 0≤split d d := by
    simpa [split,familyPBaseline] using familyP_endpoint_le hd
  rw [min_eq_left hend,hzero] at h
  convert h using 1
  ring

theorem tdBaseline_ge_familyP {d x z : ℝ} (hd : d∈Icc 0 frameCap)
    (hx : 0≤x) (hz : 0≤z) (hsum : x+z=d) :
    familyPBaseline d≤tdBaseline (Real.sqrt qCap) k (lP d) (etaP d) x z := by
  have hx' : x∈Icc 0 d := ⟨hx,by linarith⟩
  have h := familyP_split_lower hd hx'
  have hz' : z=d-x := by linarith
  have hp : 0≤k/40*x*(d-x) :=
    mul_nonneg (mul_nonneg (by norm_num [k]) hx) (sub_nonneg.mpr hx'.2)
  rw [hz']
  exact le_trans (by linarith) h

theorem btBaseline_ge_familyP {d x z : ℝ} (hd : d∈Icc 0 frameCap)
    (hx : 0≤x) (hz : 0≤z) (hsum : x+z=d) :
    familyPBaseline d≤btBaseline (Real.sqrt qCap) k (lP d) (etaP d) x z :=
  (tdBaseline_ge_familyP hd hx hz hsum).trans
    (familyP_bt_ge_td hd ⟨hz,by linarith⟩)

end SquaresInCircles.Eight.PositiveSplitConcavity
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveSecondaryEExclusion
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity
open SecondaryEStress PositivePrimaryBaselines PositiveStressCoefficients
open PositiveOrdinaryParameters PositiveOrdinaryEnvelope ActualOrdinaryBlocks

theorem scalar_V_eq (l d : ℝ) :
    PositiveScalarTransfer.V l d=V (Real.sqrt qCap) l k d := by
  simp [PositiveScalarTransfer.V,PositiveScalarData.K,k,V,pairNorm,Real.sin_neg]
  ring_nf

/-- With BT2 and TD0 secondary, both angles of T stay in the ordinary budget, whatever their
signs. -/
theorem secondary_T_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G)
    (hf : ∀ i,C.Feasible i (owners ab 2 0 i)) : False := by
  let d : ℝ := delta C.theta G
  have hbud := block_budgets hab (Or.inl rfl) (Or.inl rfl) 0 0 0 0 0
    hvar hG (by intro h; norm_num at h) (by intro h; norm_num at h)
  have hd : d∈Icc 0 frameCap := by simpa [removed,d] using hbud.1
  have hp := familyN hd
  have hinc := increment_lower hab (Or.inl rfl) (Or.inl rfl) hvar hG
    (by intro h; norm_num at h) (by intro h; norm_num at h)
    (by simpa [removed,d] using hp)
  have hinc' : V (Real.sqrt qCap) (lN d) k d≤
      secondaryIncrement C ab (Real.sqrt qCap) k (lN d) (cN d) (19/50) := by
    rw [secondary_increment_eq C hab]
    simpa [removed,d] using hinc
  have hcoeff := coefficient_bounds hd
  have hnec := secondary_necessary (k := k) (l := lN d) (c := cN d) (η := 19/50)
    hq hC hnormal hab
    (by norm_num [k]) (by linarith [hcoeff.2.2.1])
    (by norm_num [k] at hcoeff; linarith [hcoeff.2.2.2.2.1])
    (by norm_num : (0:ℝ)≤19/50) hG hf
  have hstrict := (PositiveScalarTransfer.seven_scalar_bounds hd).2.2.2.1
  rw [scalar_V_eq] at hstrict
  have hbase : PositiveScalarTransfer.BN d=
      secondaryBaseline (Real.sqrt qCap) k (lN d) (cN d) (19/50) d := by
    rfl
  rw [hbase] at hstrict
  dsimp [d] at hinc' hstrict
  linarith

/-- A positive TD2 uses its nonnegative angle as the second primary angle; the BT2 angle stays in
the B block. -/
theorem positive_TD_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hT : 0≤delta C.theta T)
    (hf : ∀ i,C.Feasible i (owners ab 2 2 i)) : False := by
  let x : ℝ := delta C.theta G
  let z : ℝ := delta C.theta T
  let d : ℝ := x+z
  have hbud := block_budgets hab (Or.inl rfl) (Or.inr rfl) 0 0 0 0 0
    hvar hG (by intro h; norm_num at h) (by intro _; exact hT)
  have hd : d∈Icc 0 frameCap := by simpa [removed,d,x,z] using hbud.1
  have hx : x∈Icc 0 d := ⟨hG,by dsimp [d,x,z]; linarith⟩
  have hz : z∈Icc 0 d := ⟨hT,by dsimp [d,x,z]; linarith⟩
  have hp := familyP_td hd hx hz
  have hinc := increment_lower hab (Or.inl rfl) (Or.inr rfl) hvar hG
    (by intro h; norm_num at h) (by intro _; exact hT)
    (by simpa [removed,d,x,z] using hp)
  have hinc' : V (Real.sqrt qCap) (lP d) k d≤
      tdIncrement C ab (Real.sqrt qCap) k (lP d) (etaP d) := by
    rw [td_increment_eq C hab]
    simpa [removed,d,x,z] using hinc
  have hcoeff := coefficient_bounds hd
  have hnec := td_necessary (k := k) (l := lP d) (η := etaP d)
    hq hC hnormal hab (by norm_num [k])
    (by linarith [hcoeff.1]) (by linarith [hcoeff.2.2.2.2.2.2.1]) hG hT hf
  have hbase := PositiveSplitConcavity.tdBaseline_ge_familyP hd hG hT
    (show delta C.theta G+delta C.theta T=d by rfl)
  have hstrict := (PositiveScalarTransfer.seven_scalar_bounds hd).1
  rw [scalar_V_eq] at hstrict
  linarith

/-- A positive BT3 is the other primary of T; its TD0 angle stays in the D block, for both AB0 and
AB2. -/
theorem positive_BT_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hB : 0≤delta C.theta B)
    (hf : ∀ i,C.Feasible i (owners ab 3 0 i)) : False := by
  let x : ℝ := delta C.theta G
  let z : ℝ := delta C.theta B
  let d : ℝ := x+z
  have hbud := block_budgets hab (Or.inr rfl) (Or.inl rfl) 0 0 0 0 0
    hvar hG (by intro _; exact hB) (by intro h; norm_num at h)
  have hd : d∈Icc 0 frameCap := by simpa [removed,d,x,z] using hbud.1
  have hx : x∈Icc 0 d := ⟨hG,by dsimp [d,x,z]; linarith⟩
  have hz : z∈Icc 0 d := ⟨hB,by dsimp [d,x,z]; linarith⟩
  have hp := familyP_bt hd hx hz
  have hinc := increment_lower hab (Or.inr rfl) (Or.inl rfl) hvar hG
    (by intro _; exact hB) (by intro h; norm_num at h)
    (by simpa [removed,d,x,z] using hp)
  have hinc' : V (Real.sqrt qCap) (lP d) k d≤
      btIncrement C ab (Real.sqrt qCap) k (lP d) (etaP d) := by
    rw [bt_increment_eq C hab]
    simpa [removed,d,x,z] using hinc
  have hcoeff := coefficient_bounds hd
  have hnec := bt_necessary (k := k) (l := lP d) (η := etaP d)
    hq hC hnormal hab (by norm_num [k])
    (by linarith [hcoeff.1]) (by linarith [hcoeff.2.2.2.2.2.2.1]) hG hB hf
  have hbase := PositiveSplitConcavity.btBaseline_ge_familyP hd hG hB
    (show delta C.theta G+delta C.theta B=d by rfl)
  have hstrict := (PositiveScalarTransfer.seven_scalar_bounds hd).1
  rw [scalar_V_eq] at hstrict
  linarith

end SquaresInCircles.Eight.PositiveSecondaryEExclusion
end
end
end
