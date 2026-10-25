module

public import SquaresInCircles.Eight.TableFree.GlobalBTSoftCapScalar

/-!
# The original positive-AB2 soft prefix

Two proved affine charges give the exact maximum penalty.  Its
argument is supplied by the actual BT1 inequality and the true
original B radial chart.  No upper bound is imposed on 1+y_B.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.SoftCap

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

def g (x : ℝ) : ℝ := kappa*x+(2-kappa)*max (x-c0) 0

theorem g_eq_max (x : ℝ) : g x=max (kappa*x) (2*x-(2-kappa)*c0) := by
  by_cases hx : x≤c0
  · have hm : 2*x-(2-kappa)*c0≤kappa*x := by
      dsimp [kappa]
      linarith
    rw [g,max_eq_right (by linarith : x-c0≤0),max_eq_left hm]
    ring
  · have hm : kappa*x≤2*x-(2-kappa)*c0 := by
      dsimp [kappa]
      linarith
    rw [g,max_eq_left (by linarith : 0≤x-c0),max_eq_right hm]
    ring

theorem g_first (x : ℝ) : kappa*x≤g x := by rw [g_eq_max]; exact le_max_left _ _
theorem g_second (x : ℝ) : 2*x-(2-kappa)*c0≤g x := by rw [g_eq_max]; exact le_max_right _ _

theorem g_monotone : Monotone g := by
  intro x y hxy
  rw [g_eq_max,g_eq_max]
  apply max_le_max
  · exact mul_le_mul_of_nonneg_left hxy (by norm_num [kappa])
  · linarith

theorem AB2_charge (a b : State) {v : ℝ}
    (ha : 0≤transverse a) (hv : v∈Icc 0 frameCap)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v 2) : g (1+transverse b)≤v+kappa*a.b := by
  have hp : GlobalOuterAnchor.width v≤projection false a b v (leftOwner true) := hAB
  have hfirst := (positive_zero_delete a b true (lambda := kappa)
    (by norm_num [kappa]) le_rfl hv).trans
      (zeroDual_le_error a b true (by norm_num [kappa]) hp)
  rw [transverse_of_nonneg a ha] at hfirst
  have hscalar := charge a hv
  have hAB' := hAB
  dsimp [projection] at hAB'
  rw [transverse_of_nonneg a ha] at hAB'
  rw [g_eq_max]
  apply max_le
  · nlinarith only [hfirst]
  · nlinarith only [hscalar,hAB']

theorem AB2_B_small (a b t : State) {v z : ℝ}
    (ha : 0≤transverse a) (hv : v∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v 2)
    (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1) : b.b<1/2 := by
  by_cases hy : transverse b≤0
  · exact OneNegative.negative_B_small b t hz hy hBT
  · have hby := transverse_of_nonneg b (le_of_not_ge hy)
    have hay := transverse_of_nonneg a ha
    have hw : (1:ℝ)≤GlobalOuterAnchor.width v := by
      have hh := sine_cosine_monotone
        (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hv hv.1
      simp only [Real.sin_zero,Real.cos_zero,zero_add] at hh
      rw [width_positive hv]
      linarith
    have hs := FrameCoreArc.projection_lt (by norm_num : (0:ℝ)<283/200)
      (GlobalQuarterSign.state_norm_sq a) v
    dsimp [projection] at hAB
    rw [hay,hby] at hAB
    linarith

/-- The actual prefix supplies the complete penalty, with no
necessary high-primary cap asserted in this branch. -/
theorem AB2_prefix (a b t : State) {v z : ℝ}
    (ha : 0≤transverse a) (hv : v∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v 2)
    (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1) :
    g (HighPrimary.«prefix» z-t.a/Real.cos z)≤v+kappa*a.b := by
  have hb := AB2_B_small a b t ha hv hz hAB hBT
  have hcap := OneNegative.BT1_secondary_cap b t hz (OneNegative.small_B_primary b hb) hBT
  exact (g_monotone (show HighPrimary.«prefix» z-t.a/Real.cos z≤1+transverse b by linarith)).trans
    (AB2_charge a b ha hv hAB)

end SquaresInCircles.Eight.TableFree.GlobalBT.SoftCap
