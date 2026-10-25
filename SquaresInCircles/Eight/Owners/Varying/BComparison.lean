module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Frames.Ordinary.AngleConcavity
public import SquaresInCircles.Eight.Owners.Varying.BEndpoint

/-!
# Eight squares: the full correlated comparison for the varying B coefficient

The actual endpoint inequality is proved in `VaryingBEndpoint`, the
whole-angle concavity and ratio monotonicity in `VaryingBFunctions`.
Consequently the final comparison has only the original coefficient and
angle hypotheses. It carries no polynomial-positivity or endpoint premise.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.VaryingBComparison
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity PositiveStressCoefficients VaryingBFunctions

theorem D_correlated_nonneg {d t : ℝ} (hd : d∈Icc 0 frameCap)
    (ht : t∈Icc 0 d) : 0≤D (Real.sqrt qCap) (ratio d) t := by
  have hR0 : 0≤Real.sqrt qCap := Real.sqrt_nonneg qCap
  have hR2 : Real.sqrt qCap≤2 := by
    have h := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
    dsimp [qCap] at h
    nlinarith
  by_cases hz : d=0
  · have ht0 : t=0 := by rw [hz] at ht; linarith [ht.1,ht.2]
    simp [ht0]
  have hdp : 0<d := lt_of_le_of_ne hd.1 (Ne.symm hz)
  have hend := VaryingBEndpoint.D_endpoint_pos ⟨hdp,hd.2⟩
  have hconc := D_concave hR0 hR2 hd
  have h := hconc.min_le_of_mem_Icc ⟨le_rfl,hd.1⟩ ⟨hd.1,le_rfl⟩ ht
  simpa only [D_zero,min_eq_left hend.le] using h

theorem D_nonneg {r d t : ℝ} (hd : d∈Icc 0 frameCap)
    (ht : t∈Icc 0 d) (hr : ratio d≤r) (hr1 : r≤1) :
    0≤D (Real.sqrt qCap) r t := by
  have hr0 : 1/2≤ratio d := by dsimp [ratio]; linarith [hd.1]
  have hrd1 : ratio d≤1 := hr.trans hr1
  exact (D_correlated_nonneg hd ht).trans
    (D_monotone_ratio (Real.sqrt_nonneg qCap) ⟨ht.1,ht.2.trans hd.2⟩
      ⟨hr0,hrd1⟩ ⟨hr0.trans hr,hr1⟩ hr)

theorem negativeNorm_hasDerivAt_q {l q t : ℝ}
    (hl : 0<l) (hq : 0<q) (ht : t∈Icc 0 frameCap) :
    HasDerivAt (fun x => pairNorm l x (-t))
      ((q-l*Real.sin t)/pairNorm l q (-t)) q := by
  have harg : |-t|≤frameCap := by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2
  have hraw := (((hasDerivAt_const q (l^2)).add ((hasDerivAt_id q).pow 2)).add
    (((hasDerivAt_id q).const_mul (2*l)).mul_const (Real.sin (-t)))).sqrt
      (pair_radicand_pos hl hq harg).ne'
  convert hraw using 1
  · rfl
  · dsimp [pairNorm]
    rw [Real.sin_neg]
    ring

theorem negativeNorm_normalized {l q t : ℝ} (hq : 0<q) :
    pairNorm l q (-t)=q*root (l/q) (Real.sin t) := by
  unfold pairNorm root
  rw [Real.sin_neg]
  have he : l^2+q^2+2*l*q*(-Real.sin t)=
      q^2*(1+(l/q)^2-2*(l/q)*Real.sin t) := by
    field_simp
    ring
  rw [he,Real.sqrt_mul (sq_nonneg q),Real.sqrt_sq hq.le]

theorem V_hasDerivAt_q {R l q t : ℝ} (hl : 0<l) (hq : 0<q)
    (ht : t∈Icc 0 frameCap) :
    HasDerivAt (fun x => V R l x t) (D R (l/q) t) q := by
  have hN := negativeNorm_hasDerivAt_q hl hq ht
  have hZ := negativeNorm_hasDerivAt_q hl hq
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  simp only [neg_zero,Real.sin_zero,mul_zero,sub_zero] at hZ
  have hraw := ((hasDerivAt_id q).mul_const (Real.cos t-1)).sub
    ((hN.sub hZ).const_mul R)
  have hnorm := negativeNorm_normalized (l := l) (t := t) hq
  have hzero : pairNorm l q 0=q*shape (l/q) := by
    have h := negativeNorm_normalized (l := l) (t := 0) hq
    rw [neg_zero,Real.sin_zero,root_zero] at h
    exact h
  have hS := (shape_pos (l/q)).ne'
  have hNn := (root_pos (l/q) (sin_mem ht)).ne'
  convert hraw using 1
  · rfl
  · dsimp [D,gain]
    rw [hnorm,hzero]
    field_simp
    ring

/-- Increasing the larger coefficient preserves the required comparison
when its actual endpoint ratio has the correlated lower bound. -/
theorem V_larger_coefficient {l k q d t : ℝ}
    (hl : 0<l) (hlk : l≤k) (hkq : k≤q)
    (hratio : ratio d*q≤l) (hd : d∈Icc 0 frameCap) (ht : t∈Icc 0 d) :
    V (Real.sqrt qCap) l k t≤V (Real.sqrt qCap) l q t := by
  have hk : 0<k := hl.trans_le hlk
  have hr0 : 0≤ratio d := by dsimp [ratio]; linarith [hd.1]
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hd.2⟩
  have hcoeff (x : ℝ) (hx : x∈Icc k q) :
      0<x ∧ ratio d≤l/x ∧ l/x≤1 := by
    have hx0 : 0<x := hk.trans_le hx.1
    refine ⟨hx0,?_,?_⟩
    · exact (le_div_iff₀ hx0).2
        ((mul_le_mul_of_nonneg_left hx.2 hr0).trans hratio)
    · exact (div_le_one hx0).2 (hlk.trans hx.1)
  have hm : MonotoneOn (fun x => V (Real.sqrt qCap) l x t) (Icc k q) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      exact (V_hasDerivAt_q hl (hcoeff x hx).1 ht').continuousAt.continuousWithinAt
    · intro x hx
      exact V_hasDerivAt_q hl (hcoeff x (Ioo_subset_Icc_self hx)).1 ht'
    · intro x hx
      have hc := hcoeff x (Ioo_subset_Icc_self hx)
      exact D_nonneg hd ht hc.2.1 hc.2.2
  exact hm ⟨le_rfl,hkq⟩ ⟨hkq,le_rfl⟩ hkq

end SquaresInCircles.Eight.VaryingBComparison
