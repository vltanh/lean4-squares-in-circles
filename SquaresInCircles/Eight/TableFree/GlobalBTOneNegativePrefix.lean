module

public import SquaresInCircles.Eight.TableFree.GlobalBTHighPrimaryPath

/-!
# Both original AB owners at nonpositive error

The previously proved signed AB dual comparison supplies a necessary
cap as well as its retained charge reserve.  Negative B follows from
the actual contact, and original BT1 forces B into the small-side
range of its exact radial chart.  No new state is introduced.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.OneNegative

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem negative_B_small (b t : State) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hy : transverse b≤0) (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1) : b.b<1/2 := by
  have hby : transverse b= -b.b := transverse_nonpos_eq b hy
  have hsum := sine_cosine_monotone
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz hz.1
  simp only [Real.sin_zero,Real.cos_zero,zero_add] at hsum
  have tr := transport_trig hz
  rw [width_negative hz] at hBT
  dsimp [projection] at hBT
  rw [hby] at hBT
  simp only [Real.sin_neg,Real.cos_neg] at hBT
  by_contra! hn
  have hA := mul_le_mul_of_nonneg_right (hn.trans b.canonical) tr.2.2.1
  have hB := mul_le_mul_of_nonneg_right hn (show 0≤Real.cos z by linarith [tr.1])
  have hT := (ZeroPrimary.coordinates t).2.1
  nlinarith only [hBT,hA,hB,hT,hsum]

theorem small_B_primary (b : State) (hb : b.b<1/2) : (7/12:ℝ)≤b.a := by
  by_cases hcore : b.branch.type=0
  · have hh := (CommonQuarter.core_small_side (FrameCoreArc.state_core_chart b hcore) hb).1
    linarith
  · have houter := state_outer_chart b hcore
    have hA := (A_bounds houter.2).1
    rw [← houter.1] at hA
    linarith [c0_bounds.1]

theorem BT1_secondary_cap (b t : State) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hB : (7/12:ℝ)≤b.a) (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1) :
    HighPrimary.«prefix» z≤1+transverse b+t.a/Real.cos z := by
  have tr := transport_trig hz
  have hcos : 0<Real.cos z := by linarith [tr.1]
  have hprod := mul_le_mul_of_nonneg_right hB tr.2.2.1
  rw [width_negative hz] at hBT
  dsimp [projection] at hBT
  simp only [Real.sin_neg,Real.cos_neg] at hBT
  have hleft : HighPrimary.«prefix» z*Real.cos z=
      (3/2)*Real.cos z+1/2+(13/12)*Real.sin z := by
    dsimp [HighPrimary.«prefix»,HighPrimary.K]
    field_simp
  have hright : (1+transverse b+t.a/Real.cos z)*Real.cos z=
      (1+transverse b)*Real.cos z+t.a := by
    field_simp
  apply le_of_mul_le_mul_right _ hcos
  rw [hleft,hright]
  nlinarith only [hBT,hprod]

/-- Both prefix conclusions are necessary inequalities on the same
original A/B/T states.  The negative-AB reserve is retained. -/
theorem nonpositive_prefix (a b t : State) (ab : Bool) {w z : ℝ}
    (ha : 0≤transverse a) (hw : w∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hAB : GlobalOuterAnchor.width (-w)≤projection false a b (-w) (leftOwner ab))
    (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1) :
    HighPrimary.«prefix» z≤a.b+t.a/Real.cos z ∧
      -z+kappa*(HighPrimary.«prefix» z-t.a/Real.cos z)+(9/2000)*w≤
        -w-z+kappa*a.b := by
  have hcos : 0<Real.cos w := by linarith [(transport_trig hw).1]
  have hl : 0≤kappa/Real.cos w := div_nonneg (by norm_num [kappa]) hcos.le
  have hab := (negative_zero_delete a b ab hw).trans (zeroDual_le_error a b ab hl hAB)
  rw [transverse_of_nonneg a ha] at hab
  have hbase : 1+transverse b≤a.b := by
    have hh := hab
    norm_num [kappa] at hh
    linarith [hw.1]
  have hby : transverse b<0 := by
    linarith [(ZeroPrimary.coordinates a).2.2.2.2]
  have hbsmall := negative_B_small b t hz hby.le hBT
  have hcap := BT1_secondary_cap b t hz (small_B_primary b hbsmall) hBT
  have hprod := mul_le_mul_of_nonneg_left
    (show HighPrimary.«prefix» z-t.a/Real.cos z≤1+transverse b by linarith)
    (show 0≤kappa by norm_num [kappa])
  refine ⟨by linarith,?_⟩
  nlinarith only [hab,hprod]

end SquaresInCircles.Eight.TableFree.GlobalBT.OneNegative
