module

public import SquaresInCircles.Eight.TableFree.GlobalBTSoftCapPrefix

/-!
# The slope-two charge increases at every fixed original T point

Its derivative is independent of the TD force parameters.  A single
quadratic bound is positive over the entire original error interval,
including errors for which the high-primary cap is empty.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.SoftCap

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

def low (c eta a b z : ℝ) : ℝ :=
  -z+2*HighPrimary.«prefix» z-(2-kappa)*c0-
    (2/Real.cos z-c*Real.sin eta)*a-c*Real.cos eta*b
def lowD (a z : ℝ) : ℝ :=
  (2*HighPrimary.K-1-(2*a-1)*Real.sin z+(Real.sin z)^2)/(Real.cos z)^2
def value (c eta z a b : ℝ) : ℝ :=
  -z+g (HighPrimary.«prefix» z-a/Real.cos z)+c*Real.sin eta*a-c*Real.cos eta*b

theorem prefix_deriv {z : ℝ} (hz : z∈Icc 0 frameCap) :
    HasDerivAt HighPrimary.«prefix»
      (((1/2)*Real.sin z+HighPrimary.K)/(Real.cos z)^2) z := by
  have hc : Real.cos z≠0 := ne_of_gt (by linarith [(transport_trig hz).1])
  have hfirst := (hasDerivAt_const z (1/2)).div (Real.hasDerivAt_cos z) hc
  have hsecond := ((Real.hasDerivAt_sin z).const_mul HighPrimary.K).div
    (Real.hasDerivAt_cos z) hc
  convert (hfirst.add hsecond).const_add (3/2) using 1
  · funext x
    dsimp [HighPrimary.«prefix»]
    ring
  · field_simp [hc]
    dsimp [HighPrimary.K]
    nlinarith only [Real.sin_sq_add_cos_sq z]

theorem low_deriv (c eta a b : ℝ) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    HasDerivAt (low c eta a b) (lowD a z) z := by
  have hc : Real.cos z≠0 := ne_of_gt (by linarith [(transport_trig hz).1])
  have hsec := (hasDerivAt_const z (2:ℝ)).div (Real.hasDerivAt_cos z) hc
  have hlin := (((hasDerivAt_id z).neg).add ((prefix_deriv hz).const_mul 2)).sub_const
    ((2-kappa)*c0)
  have hd := (hlin.sub ((hsec.sub_const (c*Real.sin eta)).mul_const a)).sub_const
    (c*Real.cos eta*b)
  convert hd using 1
  · rfl
  · dsimp [lowD]
    field_simp [hc]
    nlinarith only [Real.sin_sq_add_cos_sq z]

theorem lowD_positive {a z : ℝ} (ha : a≤283/200) (hz : z∈Icc 0 frameCap) :
    0<lowD a z := by
  have tr := transport_trig hz
  have hs : Real.sin z≤13/20 := by linarith [tr.2.2.2.1]
  have hp := mul_le_mul_of_nonneg_right
    (show 2*a-1≤183/100 by linarith) tr.2.2.1
  have hq := mul_nonneg (show 0≤13/20-Real.sin z by linarith)
    (show 0≤59/50-Real.sin z by linarith)
  have hnum : 0<2*HighPrimary.K-1-(2*a-1)*Real.sin z+(Real.sin z)^2 := by
    dsimp [HighPrimary.K]
    nlinarith only [hp,hq]
  exact div_pos hnum (sq_pos_of_pos (by linarith [tr.1]))

theorem low_monotone (c eta b : ℝ) {a : ℝ} (ha : a≤283/200) :
    MonotoneOn (low c eta a b) (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun z hz => (low_deriv c eta a b hz).continuousAt.continuousWithinAt
  · exact fun z hz => low_deriv c eta a b (Ioo_subset_Icc_self hz)
  · exact fun z hz => (lowD_positive ha (Ioo_subset_Icc_self hz)).le

theorem first_le_value (c eta z a b : ℝ) : HighPrimary.charge c eta z a b≤value c eta z a b := by
  have hh := g_first (HighPrimary.«prefix» z-a/Real.cos z)
  dsimp [HighPrimary.charge,HighPrimary.force,value]
  have hid : kappa/Real.cos z*a=kappa*(a/Real.cos z) := by ring
  linarith only [hh,hid]

theorem low_le_value (c eta z a b : ℝ) : low c eta a b z≤value c eta z a b := by
  have hh := g_second (HighPrimary.«prefix» z-a/Real.cos z)
  dsimp [low,value]
  have hid : 2/Real.cos z*a=2*(a/Real.cos z) := by ring
  linarith only [hh,hid]

theorem cap_equation {z a : ℝ} (hz : z∈Icc 0 frameCap) :
    (HighPrimary.«prefix» z-a/Real.cos z-c0)*Real.cos z=HighPrimary.X z-(a+1/2) := by
  have hc : Real.cos z≠0 := ne_of_gt (by linarith [(transport_trig hz).1])
  dsimp [HighPrimary.«prefix»,HighPrimary.X,HighPrimary.L]
  field_simp [hc]
  ring

theorem low_eq_first_at_cap {c eta z a b : ℝ} (hz : z∈Icc 0 frameCap)
    (hcap : HighPrimary.X z=a+1/2) : low c eta a b z=HighPrimary.charge c eta z a b := by
  have hcos : 0<Real.cos z := by linarith [(transport_trig hz).1]
  have hh := cap_equation (a := a) hz
  rw [hcap,sub_self] at hh
  have harg : HighPrimary.«prefix» z-a/Real.cos z=c0 := by nlinarith only [hh,hcos]
  have hid : low c eta a b z-HighPrimary.charge c eta z a b=
      (2-kappa)*(HighPrimary.«prefix» z-a/Real.cos z-c0) := by
    dsimp [low,HighPrimary.charge,HighPrimary.force]
    ring
  rw [harg,sub_self,mul_zero] at hid
  linarith only [hid]

theorem low_zero_lower (t : State) (c eta : ℝ)
    (hsmall : t.a+1/2≤HighPrimary.X 0) : HighPrimary.aligned c eta≤low c eta t.a t.b 0 := by
  have hsupport := state_support t (kappa-c*Real.sin eta) (c*Real.cos eta)
  have ha : t.a≤2-c0 := by
    have hh := hsmall
    simp only [HighPrimary.X,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,
      add_zero,HighPrimary.L] at hh
    linarith
  have hp := mul_nonneg (show 0≤2-kappa by norm_num [kappa])
    (show 0≤2-c0-t.a by linarith)
  dsimp [HighPrimary.aligned,HighPrimary.full,low,HighPrimary.«prefix»]
  simp only [Real.cos_zero,Real.sin_zero,mul_zero,zero_div,div_one,add_zero,neg_zero,zero_add]
  change (kappa-c*Real.sin eta)*t.a+(c*Real.cos eta)*t.b≤
    R*Real.sqrt ((kappa-c*Real.sin eta)^2+(c*Real.cos eta)^2)-
      (kappa-c*Real.sin eta+c*Real.cos eta)/2 at hsupport
  nlinarith only [hsupport,hp]

end SquaresInCircles.Eight.TableFree.GlobalBT.SoftCap
