module

public import SquaresInCircles.Eight.TableFree.GlobalBTHighPrimaryCap

/-!
# Whole-cap radical curvature and the increasing boundary charge

An exact polynomial expansion bounds the sole curvature numerator.
The resulting positive second derivative holds over every feasible
cap interval.  At one eighth the first derivative has a uniform
positive reserve for every TD multiplier and every TD angle.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.HighPrimary

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

def Zd (z : ℝ) : ℝ := -X z*Xd z/Z z
def Zdd (z : ℝ) : ℝ :=
  -(Q0*(Xd z)^2-X z*(X z-1)*(Q0-(X z)^2))/(Z z)^3
def boundary (c eta z : ℝ) : ℝ :=
  kappa*c0-z+c*Real.sin eta*(X z-1/2)-c*Real.cos eta*(Z z-1/2)
def boundaryD (c eta z : ℝ) : ℝ :=
  -1+c*Real.sin eta*Xd z-c*Real.cos eta*Zd z
def boundaryDD (c eta z : ℝ) : ℝ :=
  c*Real.sin eta*(1-X z)-c*Real.cos eta*Zdd z

theorem Z_deriv {z : ℝ} (hz : OnCap z) : HasDerivAt Z (Zd z) z := by
  have hh := ((hasDerivAt_const z Q0).sub ((X_deriv z).pow 2)).sqrt
    (show Q0-(X z)^2≠0 by linarith [cap_radicand hz])
  convert hh using 1
  · rfl
  · dsimp [Zd,Z]
    ring

theorem Zd_deriv {z : ℝ} (hz : OnCap z) : HasDerivAt Zd (Zdd z) z := by
  have hn := (Z_pos hz).ne'
  have hh := (((X_deriv z).neg).mul (Xd_deriv z)).div (Z_deriv hz) hn
  have hQ : Q0=(Z z)^2+(X z)^2 := by linarith [Z_sq hz]
  convert hh using 1
  · rfl
  · dsimp [Zd,Zdd]
    rw [hQ]
    field_simp [hn]
    ring

theorem curvature_polynomial {x : ℝ} (hx : (8/5:ℝ)≤x) :
    x*(x-1)*(Q0-x^2)≤(24/25)*(Q0-64/25) := by
  have hid : (24/25)*(Q0-64/25)-x*(x-1)*(Q0-x^2)=
      (x-8/5)*((1121/12500)+(16611/2500)*(x-8/5)+
        (27/5)*(x-8/5)^2+(x-8/5)^3) := by norm_num [Q0] <;> ring
  have hh : 0≤(x-8/5)*((1121/12500)+(16611/2500)*(x-8/5)+
      (27/5)*(x-8/5)^2+(x-8/5)^3) := by
    have hp : 0≤x-8/5 := by linarith
    positivity
  linarith only [hid,hh]

theorem curvature_numerator {z : ℝ} (hz : OnCap z) :
    (4/5)*(Z z)^3<Q0*(Xd z)^2-X z*(X z-1)*(Q0-(X z)^2) := by
  have hF := curvature_polynomial (X_lower hz.1).le
  have hXd := pow_le_pow_left₀ (show (0:ℝ)≤41/50 by norm_num)
    (cap_Xd_lower hz).le 2
  have hZ := pow_le_pow_left₀ (Z_pos hz).le (Z_bounds hz).2.le 3
  norm_num [Q0] at hF ⊢
  nlinarith only [hF,hXd,hZ]

theorem Zdd_upper {z : ℝ} (hz : OnCap z) : Zdd z< -(4/5) := by
  have hp := pow_pos (Z_pos hz) 3
  have hh := (lt_div_iff₀ hp).2 (curvature_numerator hz)
  dsimp [Zdd]
  linarith

theorem boundary_deriv (c eta : ℝ) {z : ℝ} (hz : OnCap z) :
    HasDerivAt (boundary c eta) (boundaryD c eta z) z := by
  convert ((((hasDerivAt_id z).neg).const_add (kappa*c0)).add
    (((X_deriv z).sub_const (1/2)).const_mul (c*Real.sin eta))).sub
      (((Z_deriv hz).sub_const (1/2)).const_mul (c*Real.cos eta)) using 1 <;>
    dsimp [boundary,boundaryD] <;> ring

theorem boundaryD_deriv (c eta : ℝ) {z : ℝ} (hz : OnCap z) :
    HasDerivAt (boundaryD c eta) (boundaryDD c eta z) z := by
  convert (((Xd_deriv z).const_mul (c*Real.sin eta)).const_add (-1)).sub
    ((Zd_deriv hz).const_mul (c*Real.cos eta)) using 1 <;>
    dsimp [boundaryD,boundaryDD] <;> ring

theorem boundaryDD_positive {c eta z : ℝ} (hc : 0<c)
    (heta : eta∈Icc 0 frameCap) (hz : OnCap z) : 0<boundaryDD c eta z := by
  have tr := transport_trig heta
  have hs : 0≤Real.sin eta := tr.2.2.1
  have hcos : (3/4:ℝ)<Real.cos eta := by linarith [tr.1]
  have hsin : Real.sin eta≤13/20 := by linarith [tr.2.2.2.1]
  have hX : 0≤X z-1 := by linarith [X_lower hz.1]
  have hprod := mul_le_mul (show X z-1≤183/200 by linarith [cap_X_upper hz])
    hsin hs (by norm_num : (0:ℝ)≤183/200)
  have hZ := Zdd_upper hz
  have hneg := mul_pos (show 0< -Zdd z-4/5 by linarith)
    (show 0<Real.cos eta by linarith)
  have hinner : 0<Real.sin eta*(1-X z)-Real.cos eta*Zdd z := by
    nlinarith only [hprod,hneg,hcos]
  have hp := mul_pos hc hinner
  dsimp [boundaryDD]
  nlinarith only [hp]

/-- A fixed rational lower support line for every admitted TD angle. -/
theorem weighted_angle {eta : ℝ} (heta : eta∈Icc 0 frameCap) :
    (7/4:ℝ)≤Real.sin eta+(7/4)*Real.cos eta := by
  have tr := transport_trig heta
  have hc : (3/4:ℝ)≤Real.cos eta := by linarith [tr.1]
  have hs : Real.sin eta≤13/20 := by linarith [tr.2.2.2.1]
  have h1 := mul_nonneg (sub_nonneg.mpr (Real.cos_le_one eta))
    (show 0≤Real.cos eta-3/4 by linarith)
  have h2 := mul_nonneg tr.2.2.1 (show 0≤13/20-Real.sin eta by linarith)
  nlinarith only [h1,h2,Real.sin_sq_add_cos_sq eta,tr.2.2.1]

theorem boundaryD_eighth_positive {c eta : ℝ} (hc : (3/5:ℝ)≤c)
    (heta : eta∈Icc 0 frameCap) (hz : OnCap (1/8)) : 0<boundaryD c eta (1/8) := by
  have hZ := Z_pos hz
  have hbounds := cap_large_bounds hz le_rfl
  have hratio : (7/4:ℝ)≤X (1/8)/Z (1/8) := by
    apply (le_div_iff₀ hZ).2
    linarith [hbounds.1,hbounds.2]
  have hcos : 0≤Real.cos eta := by linarith [(transport_trig heta).1]
  have hprod := mul_le_mul_of_nonneg_left hratio hcos
  have hangle : (7/4:ℝ)≤Real.sin eta+Real.cos eta*(X (1/8)/Z (1/8)) := by
    linarith [weighted_angle heta]
  have hcpos : 0≤c := by linarith
  have hXd := Xd_eighth_lower
  have hcx : (297/500:ℝ)≤c*Xd (1/8) := by
    have hh := mul_le_mul hc (show (99/100:ℝ)≤Xd (1/8) from hXd.le)
      (by norm_num : (0:ℝ)≤99/100) hcpos
    norm_num at hh
    exact hh
  have hp := mul_le_mul hcx hangle (by norm_num : (0:ℝ)≤7/4)
    (mul_nonneg hcpos (by linarith : 0≤Xd (1/8)))
  have hid : boundaryD c eta (1/8)=
      -1+c*Xd (1/8)*(Real.sin eta+Real.cos eta*(X (1/8)/Z (1/8))) := by
    dsimp [boundaryD,Zd]
    ring
  rw [hid]
  nlinarith only [hp]

theorem boundaryD_monotone {c eta z : ℝ} (hc : 0<c)
    (heta : eta∈Icc 0 frameCap) (hz : OnCap z) :
    MonotoneOn (boundaryD c eta) (Icc (1/8) z) := by
  have hdom (w : ℝ) (hw : w∈Icc (1/8) z) : OnCap w :=
    cap_down hz ⟨by linarith [hw.1],hw.2⟩
  apply monoOn_of_hasDeriv_nonneg
  · exact fun w hw => (boundaryD_deriv c eta (hdom w hw)).continuousAt.continuousWithinAt
  · exact fun w hw => boundaryD_deriv c eta (hdom w (Ioo_subset_Icc_self hw))
  · exact fun w hw => (boundaryDD_positive hc heta (hdom w (Ioo_subset_Icc_self hw))).le

theorem boundary_monotone {c eta z : ℝ} (hc : (3/5:ℝ)≤c)
    (heta : eta∈Icc 0 frameCap) (hz : OnCap z) (hlarge : (1/8:ℝ)≤z) :
    MonotoneOn (boundary c eta) (Icc (1/8) z) := by
  have hcpos : 0<c := by linarith
  have hdom (w : ℝ) (hw : w∈Icc (1/8) z) : OnCap w :=
    cap_down hz ⟨by linarith [hw.1],hw.2⟩
  have hstart := boundaryD_eighth_positive hc heta (hdom (1/8) ⟨le_rfl,hlarge⟩)
  have hdmono := boundaryD_monotone hcpos heta hz
  apply monoOn_of_hasDeriv_nonneg
  · exact fun w hw => (boundary_deriv c eta (hdom w hw)).continuousAt.continuousWithinAt
  · exact fun w hw => boundary_deriv c eta (hdom w (Ioo_subset_Icc_self hw))
  · intro w hw
    have hh := hdmono ⟨le_rfl,hlarge⟩ (Ioo_subset_Icc_self hw) hw.1.le
    linarith

end SquaresInCircles.Eight.TableFree.GlobalBT.HighPrimary
