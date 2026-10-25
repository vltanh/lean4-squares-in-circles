module

public import SquaresInCircles.Eight.TableFree.GlobalBTOneNegativeAB0Domain

/-!
# The complete effective-error cap for original AB0 and negative BT1

When 0 <= v <= z, the effective error is r=z-v.  The two actual
projections cancel the original signed B coordinate exactly.  Their
remaining trigonometric line increases on the entire segment from
zero to v and begins at the high-primary prefix value.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.OneNegative

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

def capLine (r v : ℝ) : ℝ :=
  (1+Real.cos v+Real.sin v)/2+
  (1+Real.cos (v+r)+Real.sin (v+r))/(2*Real.cos r)+
  (Real.sin r/Real.cos r)*((7/12)*Real.cos v-(1/2)*Real.sin v)
def capLineD (r v : ℝ) : ℝ :=
  (Real.cos (v+r)-Real.sin (v+r)-(1/12)*Real.sin r*Real.sin v)/Real.cos r

theorem capLine_deriv {r : ℝ} (hr : r∈Icc 0 frameCap) (v : ℝ) :
    HasDerivAt (capLine r) (capLineD r v) v := by
  have hcos : Real.cos r≠0 := ne_of_gt (by linarith [(transport_trig hr).1])
  have hfirst := (((Real.hasDerivAt_cos v).add (Real.hasDerivAt_sin v)).const_add 1).div_const 2
  have hcosSum := (Real.hasDerivAt_cos (v+r)).comp v ((hasDerivAt_id v).add_const r)
  have hsinSum := (Real.hasDerivAt_sin (v+r)).comp v ((hasDerivAt_id v).add_const r)
  have hsecond := ((hcosSum.add hsinSum).const_add 1).div_const (2*Real.cos r)
  have hthird := (((Real.hasDerivAt_cos v).const_mul (7/12)).sub
    ((Real.hasDerivAt_sin v).const_mul (1/2))).const_mul (Real.sin r/Real.cos r)
  convert (hfirst.add hsecond).add hthird using 1
  · funext x
    dsimp [capLine]
    ring
  · dsimp [capLineD]
    rw [Real.cos_add,Real.sin_add]
    field_simp [hcos]
    ring

theorem capLineD_positive {r v : ℝ} (hr : r∈Icc 0 frameCap)
    (hv : v∈Icc 0 frameCap) (hsum : v+r≤frameCap) : 0<capLineD r v := by
  have hsumdom : v+r∈Icc 0 frameCap := ⟨add_nonneg hv.1 hr.1,hsum⟩
  have tr := transport_trig hsumdom
  have hprod := mul_le_mul (Real.sin_le_one r) (Real.sin_le_one v)
    (transport_trig hv).2.2.1 (by norm_num : (0:ℝ)≤1)
  have hnum : 0<Real.cos (v+r)-Real.sin (v+r)-(1/12)*Real.sin r*Real.sin v := by
    nlinarith only [tr.1,tr.2.2.2.1,hprod]
  exact div_pos hnum (by linarith [(transport_trig hr).1])

theorem capLine_zero {r : ℝ} (hr : r∈Icc 0 frameCap) :
    capLine r 0=HighPrimary.«prefix» r := by
  have hcos : Real.cos r≠0 := ne_of_gt (by linarith [(transport_trig hr).1])
  simp only [capLine,Real.cos_zero,Real.sin_zero,zero_add,mul_one,mul_zero,sub_zero]
  dsimp [HighPrimary.«prefix»,HighPrimary.K]
  field_simp [hcos]
  ring

theorem capLine_lower {r v : ℝ} (hr : r∈Icc 0 frameCap) (hv : 0≤v)
    (hsum : v+r≤frameCap) : HighPrimary.«prefix» r≤capLine r v := by
  have hm : MonotoneOn (capLine r) (Icc 0 v) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x _ => (capLine_deriv hr x).continuousAt.continuousWithinAt
    · exact fun x _ => capLine_deriv hr x
    · intro x hx
      exact (capLineD_positive hr
        ⟨hx.1.le,by linarith [hx.2,hr.1,hsum]⟩ (by linarith [hx.2,hsum])).le
  have hh := hm ⟨le_rfl,hv⟩ ⟨hv,le_rfl⟩ hv
  rwa [capLine_zero hr] at hh

theorem AB0_effective_cap (a b t : State) {v z : ℝ}
    (ha : 0≤transverse a) (hv : v∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hvz : v≤z) (hAB : GlobalOuterAnchor.width v≤projection false a b v 0)
    (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1) :
    HighPrimary.«prefix» (z-v)≤a.b+t.a/Real.cos (z-v) ∧
      -(z-v)+kappa*(HighPrimary.«prefix» (z-v)-t.a/Real.cos (z-v))≤v-z+kappa*a.b := by
  let r := z-v
  have hr : r∈Icc 0 frameCap := ⟨by dsimp [r]; linarith,by dsimp [r]; linarith [hz.2,hv.1]⟩
  have hsum : v+r=z := by dsimp [r]; ring
  have hcos : 0<Real.cos r := by linarith [(transport_trig hr).1]
  have hBsmall := AB0_intermediate_B_small a b t ha hv hz hvz hAB hBT
  have hBprimary := small_B_primary b hBsmall
  have hBy : -(1/2:ℝ)≤transverse b := by linarith [(transverse_bounds b).1]
  have hp1 := mul_le_mul_of_nonneg_right hBprimary
    (show 0≤Real.cos v by linarith [(transport_trig hv).1])
  have hp2 := mul_le_mul_of_nonneg_right hBy (transport_trig hv).2.2.1
  have hforce := mul_le_mul_of_nonneg_left
    (show (7/12)*Real.cos v-(1/2)*Real.sin v≤b.a*Real.cos v+transverse b*Real.sin v by
      linarith only [hp1,hp2]) (transport_trig hr).2.2.1
  have hAB' := hAB
  have hBT' := hBT
  rw [width_positive hv] at hAB'
  rw [width_negative hz] at hBT'
  dsimp [projection] at hAB' hBT'
  rw [transverse_of_nonneg a ha] at hAB'
  simp only [Real.sin_neg,Real.cos_neg] at hBT'
  have hABscaled := mul_le_mul_of_nonneg_right hAB' hcos.le
  have hsin : Real.sin z=Real.sin v*Real.cos r+Real.cos v*Real.sin r := by
    rw [← hsum,Real.sin_add]
  have hcosz : Real.cos z=Real.cos v*Real.cos r-Real.sin v*Real.sin r := by
    rw [← hsum,Real.cos_add]
  have hline : capLine r v≤a.b+t.a/Real.cos r := by
    have hleft : capLine r v*Real.cos r=
        ((1+Real.cos v+Real.sin v)/2)*Real.cos r+
        (1+Real.cos z+Real.sin z)/2+
        Real.sin r*((7/12)*Real.cos v-(1/2)*Real.sin v) := by
      dsimp [capLine]
      rw [hsum]
      field_simp [hcos.ne']
    have hright : (a.b+t.a/Real.cos r)*Real.cos r=a.b*Real.cos r+t.a := by
      field_simp [hcos.ne']
    apply le_of_mul_le_mul_right _ hcos
    rw [hleft,hright]
    rw [hsin,hcosz] at hBT'
    rw [hsin,hcosz]
    nlinarith only [hABscaled,hBT',hforce]
  have hcap := (capLine_lower hr hv.1 (by rw [hsum]; exact hz.2)).trans hline
  refine ⟨hcap,?_⟩
  have hp := mul_le_mul_of_nonneg_left hcap (show 0≤kappa by norm_num [kappa])
  change -(z-v)+kappa*(HighPrimary.«prefix» r-t.a/Real.cos r)≤v-z+kappa*a.b
  nlinarith only [hp]

end SquaresInCircles.Eight.TableFree.GlobalBT.OneNegative
