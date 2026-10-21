module

public import SquaresInCircles.Eight.TableFree.NegativePrimaryEntry

/-!
# The aligned negative contact has a strict anchor-circle gain

Uncompiled source. The intrinsic A-circle inequality couples the flat-core
height and angle. A single affine bound on that whole domain proves the
strict H-circle rate, without differentiating an implicitly defined upper
curve or subdividing the angle interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace AlignedNegative
open PrimaryCap

def intrinsic (D x : ℝ) : ℝ :=
  1+D^2+K^2+2*D*Real.cos x+2*K*Real.sin x

def tangentRate (D x : ℝ) : ℝ := K-D*Real.tan x

theorem intrinsic_hasDerivAt (D x : ℝ) :
    HasDerivAt (intrinsic D) (2*K*Real.cos x-2*D*Real.sin x) x := by
  convert (((hasDerivAt_const x (1+D^2+K^2)).add
    ((Real.hasDerivAt_cos x).const_mul (2*D))).add
    ((Real.hasDerivAt_sin x).const_mul (2*K))) using 1 <;>
    simp [intrinsic] <;> ring

theorem intrinsic_strictMono {D : ℝ} (hD : 0≤D ∧ D≤82/125) :
    StrictMonoOn (intrinsic D) (Icc 0 (7/10 : ℝ)) := by
  apply strict_increase_of_reserve
    (df := fun x => 2*K*Real.cos x-2*D*Real.sin x) (k := 3/4)
  · exact (by fun_prop : Continuous (intrinsic D)).continuousOn
  · intro x hx
    exact intrinsic_hasDerivAt D x
  · norm_num
  · intro x hx
    obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse (Ioo_subset_Icc_self hx)
    have hm := mul_le_mul hD.2 hs.le hs0 (by norm_num : (0:ℝ)≤82/125)
    unfold K
    nlinarith

/-- The actual exceptional contact lies on one short continuous domain. -/
theorem intrinsic_cuts {D x : ℝ}
    (hD : 3/5<D ∧ D≤183/200) (hx : x∈Icc 0 (7/10 : ℝ))
    (hR : intrinsic D x<qCap) :
    D<82/125 ∧ x<9/100 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hx
  have hsum : 1≤Real.sin x+Real.cos x := by
    have hh := one_le_abs_cos_add_abs_sin x
    rw [abs_of_pos (by linarith : 0<Real.cos x),abs_of_nonneg hs0] at hh
    linarith
  have hsupport : D≤D*Real.cos x+K*Real.sin x := by
    have hp := mul_nonneg (by linarith [hD.1] : 0≤D) (sub_nonneg.mpr hsum)
    have hm := mul_nonneg (show 0≤K-D by unfold K; linarith [hD.2]) hs0
    nlinarith
  have hbase : K^2+(D+1)^2<qCap := by
    dsimp [intrinsic] at hR
    nlinarith
  have hDu : D<82/125 := by
    by_contra! hbad
    dsimp [K,qCap] at hbase
    nlinarith
  refine ⟨hDu,?_⟩
  by_contra! hxlarge
  have hm := (intrinsic_strictMono ⟨by linarith [hD.1],hDu.le⟩).monotoneOn
    (show (9/100 : ℝ)∈Icc 0 (7/10) by constructor <;> norm_num) hx hxlarge
  have hc9 := Real.one_sub_sq_div_two_le_cos (x := (9/100 : ℝ))
  have hs9 := Real.sin_ge_sub_cube (show (0:ℝ)≤9/100 by norm_num)
  have hcmul := mul_le_mul_of_nonneg_right hD.1.le
    (show 0≤Real.cos (9/100 : ℝ) by linarith)
  have hDsq : (3/5 : ℝ)^2≤D^2 :=
    pow_le_pow_left₀ (by norm_num) hD.1.le 2
  dsimp [intrinsic,K,qCap] at hR hm
  nlinarith

/-- One exact affine estimate retains the height/angle coupling that a
rectangular bound would lose. Its positive reserve is 781/2250000. -/
theorem intrinsic_affine_cut {D x : ℝ}
    (hD : 3/5<D ∧ D≤183/200) (hx : x∈Icc 0 (7/10 : ℝ))
    (hR : intrinsic D x<qCap) : D+(63/100)*x<82/125 := by
  obtain ⟨hDu,hxu⟩ := intrinsic_cuts hD hx hR
  have hD0 : 0≤D := by linarith [hD.1]
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hs := Real.sin_ge_sub_cube hx.1
  have hxc : x^2≤(9/100 : ℝ)^2 :=
    pow_le_pow_left₀ hx.1 hxu.le 2
  have hDx : D*x≤(2/3 : ℝ)*(9/100) :=
    mul_le_mul (by linarith : D≤2/3) hxu.le hx.1 (by norm_num)
  have hcoef : 0≤2*K-21/10-D*x-(K/3)*x^2 := by
    unfold K
    nlinarith
  have hprod := mul_nonneg hx.1 hcoef
  have hcos := mul_le_mul_of_nonneg_left hc (show 0≤2*D by positivity)
  have hsin := mul_le_mul_of_nonneg_left hs (show 0≤2*K by norm_num [K])
  have hlower : (D+1)^2+K^2+(21/10)*x≤intrinsic D x := by
    unfold intrinsic
    nlinarith
  by_contra! hbad
  have hb0 : 0≤1+82/125-(63/100)*x := by linarith [hx.1,hxu]
  have hbsq := pow_le_pow_left₀ hb0
    (show 1+82/125-(63/100)*x≤D+1 by linarith) 2
  dsimp [K,qCap] at hlower hR
  nlinarith [sq_nonneg x]

theorem short_tangent_linear {x : ℝ} (hx : x∈Icc 0 (9/100 : ℝ)) :
    0≤Real.tan x ∧ Real.tan x≤(101/100)*x := by
  have hc := transport_cos_pos (show |x|≤(7/10 : ℝ) by
    rw [abs_of_nonneg hx.1]; linarith [hx.2])
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_gt_three])
  have hsin : Real.sin x≤x :=
    (le_abs_self _).trans (Real.abs_sin_le_abs.trans_eq (abs_of_nonneg hx.1))
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hx.1 hx.2 2
  have hcl : (100/101 : ℝ)≤Real.cos x := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hcl hx.1
  rw [Real.tan_eq_sin_div_cos]
  refine ⟨div_nonneg hs hc.le,?_⟩
  rw [div_le_iff₀ hc]
  nlinarith

/-- The exact scalar reserve needed for the anchor gain. This proves the
whole intrinsic domain at once, including its x=0 endpoint. -/
theorem circle_rate_reserve {D x : ℝ}
    (hD : 3/5<D ∧ D≤183/200) (hx : x∈Icc 0 (7/10 : ℝ))
    (hR : intrinsic D x<qCap) :
    1<tangentRate D x ∧ tangentRate D x≤K ∧
      qCap<(2-D)^2*(1+tangentRate D x^2) := by
  obtain ⟨hDu,hxu⟩ := intrinsic_cuts hD hx hR
  have hline := intrinsic_affine_cut hD hx hR
  obtain ⟨ht0,htu⟩ := short_tangent_linear ⟨hx.1,hxu.le⟩
  have hD0 : 0≤D := by linarith [hD.1]
  have htan : D*Real.tan x≤(101/150 : ℝ)*x := by
    have hm := mul_le_mul (show D≤2/3 by linarith) htu ht0 (by norm_num)
    nlinarith
  let r := tangentRate D x
  let Y := 2-D
  have hrlo : K-(101/150)*x≤r := by dsimp [r,tangentRate]; linarith
  have hr : 1<r := by dsimp [K] at hrlo; linarith [hxu]
  have hru : r≤K := by
    have hm := mul_nonneg hD0 ht0
    dsimp [r,tangentRate]
    linarith
  have hY0 : 0≤Y := by dsimp [Y]; linarith
  have hYu : Y<7/5 := by dsimp [Y]; linarith [hD.1]
  have hYline : 168/125+(63/100)*x<Y := by dsimp [Y]; linarith
  have hYsq := pow_lt_pow_left₀
    (show 0≤168/125+(63/100)*x by positivity) hYline (by decide : (2:ℕ)≠0)
  have hY2 : (168/125 : ℝ)^2+2*(168/125)*(63/100)*x<Y^2 := by
    nlinarith [sq_nonneg x]
  have hrbase : 0≤K-(101/150)*x := by unfold K; linarith [hxu]
  have hrsq := pow_le_pow_left₀ hrbase hrlo 2
  have hr2 : K^2-2*K*(101/150)*x≤r^2 := by nlinarith [sq_nonneg x]
  have hmult := mul_le_mul_of_nonneg_left hr2 (sq_nonneg Y)
  have hYbound : Y^2≤(7/5 : ℝ)^2 := pow_le_pow_left₀ hY0 hYu.le 2
  have hcost := mul_le_mul_of_nonneg_left hYbound
    (show 0≤2*K*(101/150)*x by unfold K; positivity)
  have hgrowth := mul_lt_mul_of_pos_left hY2 (show 0<1+K^2 by positivity)
  refine ⟨hr,hru,?_⟩
  change qCap<Y^2*(1+r^2)
  dsimp [K,qCap] at hmult hcost hgrowth ⊢
  nlinarith

/-- On its own retained circle, H's primary gains faster than one when the
aligned negative angle decreases. The radius is the actual H circle value. -/
theorem circle_primary_gain {qH D x : ℝ}
    (hD : 3/5<D ∧ D≤183/200) (hx : x∈Icc 0 (7/10 : ℝ))
    (hR : intrinsic D x<qCap) (hqH : qH≤qCap)
    (hrad : 0<qH-(2-D)^2) :
    1<(2-D)*tangentRate D x/Real.sqrt (qH-(2-D)^2) := by
  obtain ⟨hr,hru,hreserve⟩ := circle_rate_reserve hD hx hR
  have hY : 0<2-D := by linarith [hD.2]
  have hs := Real.sqrt_pos.mpr hrad
  have hs2 := Real.sq_sqrt hrad.le
  rw [lt_div_iff₀ hs]
  have hp := mul_pos hY (show 0<tangentRate D x by linarith)
  nlinarith

end AlignedNegative
end SquaresInCircles.Eight.TableFree
