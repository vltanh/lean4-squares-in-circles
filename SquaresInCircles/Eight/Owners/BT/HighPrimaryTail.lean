module

public import SquaresInCircles.Common.DiskSupport
public import SquaresInCircles.Eight.Owners.BT.CoreDE3Support
public import SquaresInCircles.Eight.Owners.BT.OneNegativeAB0Cap
public import SquaresInCircles.Eight.Owners.BT.CoreDE3Polynomial

/-!
# Eight squares: both complete TD--DE scalar tails after high-primary transport

The necessary cap and prefix charge are separate hypotheses.  The
transport acts only on the unchanged T circle; D, E, their errors,
the TD owner and the exact DE marker chart remain original.
-/

section
/-!
## Whole-cap radical curvature and the increasing boundary charge

An exact polynomial expansion bounds the sole curvature numerator.
The resulting positive second derivative holds over every feasible
cap interval.  At one eighth the first derivative has a uniform
positive reserve for every TD multiplier and every TD angle.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.HighPrimary

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
        (27/5)*(x-8/5)^2+(x-8/5)^3) := by norm_num [Q0]; ring
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
  rw [neg_div]
  linarith

theorem boundary_deriv (c eta : ℝ) {z : ℝ} (hz : OnCap z) :
    HasDerivAt (boundary c eta) (boundaryD c eta z) z := by
  have h1 : HasDerivAt (fun y => kappa*c0-y) (-1) z := (hasDerivAt_id' z).const_sub (kappa*c0)
  have h2 : HasDerivAt (fun y => c*Real.sin eta*(X y-1/2)) (c*Real.sin eta*Xd z) z :=
    ((X_deriv z).sub_const (1/2)).const_mul (c*Real.sin eta)
  have h3 : HasDerivAt (fun y => c*Real.cos eta*(Z y-1/2)) (c*Real.cos eta*Zd z) z :=
    ((Z_deriv hz).sub_const (1/2)).const_mul (c*Real.cos eta)
  have h := (h1.fun_add h2).fun_sub h3
  unfold boundary boundaryD
  exact h.congr_deriv (by ring)

theorem boundaryD_deriv (c eta : ℝ) {z : ℝ} (hz : OnCap z) :
    HasDerivAt (boundaryD c eta) (boundaryDD c eta z) z := by
  have h1 : HasDerivAt (fun y => c*Real.sin eta*Xd y) (c*Real.sin eta*(1-X z)) z :=
    (Xd_deriv z).const_mul (c*Real.sin eta)
  have h2 : HasDerivAt (fun y => c*Real.cos eta*Zd y) (c*Real.cos eta*Zdd z) z :=
    (Zd_deriv hz).const_mul (c*Real.cos eta)
  have h := ((hasDerivAt_const z (-1:ℝ)).fun_add h1).fun_sub h2
  unfold boundaryD boundaryDD
  exact h.congr_deriv (by ring)

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

end SquaresInCircles.Eight.GlobalBT.HighPrimary
end
end
end

section
/-!
## Explicit support on both parts of the high-primary cap

Up to one eighth, a positive polynomial pays the extra secant force
using the original universal primary bound.  Beyond one eighth,
uniform rational bounds put the support maximum on the primary
boundary.  Every comparison is on the same corner disk.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.HighPrimary

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

def full (f g : ℝ) : ℝ := R*Real.sqrt (f^2+g^2)-(f+g)/2
def force (c eta z : ℝ) : ℝ := kappa/Real.cos z-c*Real.sin eta
def charge (c eta z a b : ℝ) : ℝ :=
  -z+kappa*«prefix» z-force c eta z*a-c*Real.cos eta*b
def aligned (c eta : ℝ) : ℝ :=
  2*kappa-full (kappa-c*Real.sin eta) (c*Real.cos eta)

theorem full_support {a b : ℝ}
    (hc : (a+1/2)^2+(b+1/2)^2≤Q0) (f g : ℝ) : f*a+g*b≤full f g := by
  have hrad : normSq (a+1/2,b+1/2)≤R^2 := by rw [R_sq]; exact hc
  have hh := dot_le_radius (v := (f,g)) (p := (a+1/2,b+1/2)) R_pos.le hrad
  dsimp [dot,vectorLength,normSq,full] at *
  linarith

theorem small_gain {z : ℝ} (hz : z∈Icc 0 (1/8:ℝ)) :
    z*Real.cos z≤kappa*(K*Real.sin z-(183/200)*(1-Real.cos z)) := by
  have hs := Real.sin_ge_sub_cube hz.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := z)
  have hzc := mul_le_mul_of_nonneg_left (Real.cos_le_one z) hz.1
  have hsq : z^2≤z/8 := by nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
  have hcube1 := mul_le_mul_of_nonneg_left hsq hz.1
  have hcube2 := mul_le_mul_of_nonneg_left hsq (show (0:ℝ)≤1/8 by norm_num)
  dsimp [K,kappa]
  nlinarith only [hs,hc,hzc,hsq,hcube1,hcube2,hz.1]

/-- The small-error comparison works on every point of the disk;
it does not assume the high-primary restriction. -/
theorem small_lower {a b z : ℝ} (hc : (a+1/2)^2+(b+1/2)^2≤Q0)
    (ha : a≤283/200) (hz : z∈Icc 0 (1/8:ℝ)) (c eta : ℝ) :
    aligned c eta≤charge c eta z a b := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hcos : 0<Real.cos z := by linarith [(transport_trig hz').1]
  have hsec : 0≤1/Real.cos z-1 := by
    apply sub_nonneg.mpr
    exact (le_div_iff₀ hcos).2 (by simpa using Real.cos_le_one z)
  have hsupport := full_support hc (kappa-c*Real.sin eta) (c*Real.cos eta)
  have hgain := div_nonneg (show 0≤
    kappa*(K*Real.sin z-(183/200)*(1-Real.cos z))-z*Real.cos z by
      linarith [small_gain hz]) hcos.le
  have hreserve := mul_nonneg
    (mul_nonneg (show 0≤kappa by norm_num [kappa]) hsec)
    (show 0≤283/200-a by linarith)
  have hid : charge c eta z a b-aligned c eta=
      (kappa*(K*Real.sin z-(183/200)*(1-Real.cos z))-z*Real.cos z)/Real.cos z+
      (full (kappa-c*Real.sin eta) (c*Real.cos eta)-
        ((kappa-c*Real.sin eta)*a+c*Real.cos eta*b))+
      kappa*(1/Real.cos z-1)*(283/200-a) := by
    dsimp [charge,aligned,force,«prefix»]
    field_simp [hcos.ne']
    ring
  linarith only [hid,hsupport,hgain,hreserve]

theorem force_direction {c eta z : ℝ} (hc : (3/5:ℝ)≤c)
    (heta : eta∈Icc 0 frameCap) (hz : OnCap z) :
    force c eta z≤(kappa/Real.cos z)*Real.cos eta := by
  have hcos : 0<Real.cos z := by linarith [(cap_trig hz).1]
  have hcpos : 0≤c := by linarith
  have hfirst : kappa/Real.cos z≤(7/4)*c := by
    apply (div_le_iff₀ hcos).2
    have hp := mul_le_mul hc (cap_trig hz).1 (by norm_num : (0:ℝ)≤17/18) hcpos
    dsimp [kappa]
    nlinarith only [hp]
  have hnonneg : 0≤1-Real.cos eta := sub_nonneg.mpr (Real.cos_le_one eta)
  have h1 := mul_le_mul_of_nonneg_right hfirst hnonneg
  have h2 := mul_le_mul_of_nonneg_left (weighted_angle heta) hcpos
  dsimp [force]
  nlinarith only [h1,h2]

theorem large_support_direction {c eta z : ℝ} (hc : (3/5:ℝ)≤c)
    (heta : eta∈Icc 0 frameCap) (hz : OnCap z) (hlarge : (1/8:ℝ)≤z) :
    force c eta z*Z z≤c*Real.cos eta*X z := by
  have hxz := cap_large_bounds hz hlarge
  have hcos := (cap_trig hz).1
  have hzcos : 0<Real.cos z := by linarith
  have hcpos : 0≤c := by linarith
  have hxpos : 0≤X z := by linarith [hxz.1]
  have hcx := mul_le_mul hc hcos (by norm_num : (0:ℝ)≤17/18) hcpos
  have htriple := mul_le_mul hcx hxz.1.le
    (by norm_num : (0:ℝ)≤173/100)
    (mul_nonneg hcpos hzcos.le)
  have hprimary : kappa*Z z≤c*Real.cos z*X z := by
    dsimp [kappa]
    nlinarith only [htriple,hxz.2]
  have hdiv : (kappa/Real.cos z)*Z z≤c*X z := by
    apply le_of_mul_le_mul_right _ hzcos
    have hid : ((kappa/Real.cos z)*Z z)*Real.cos z=kappa*Z z := by
      field_simp
    rw [hid]
    nlinarith only [hprimary]
  have hetaCos : 0≤Real.cos eta := by linarith [(transport_trig heta).1]
  have hforce := mul_le_mul_of_nonneg_right (force_direction hc heta hz) (Z_pos hz).le
  have hforce2 := mul_le_mul_of_nonneg_left hdiv hetaCos
  nlinarith only [hforce,hforce2]

/-- Exact restricted support, with no assumed maximizing point. -/
theorem restricted_support {a b c eta z : ℝ}
    (hcirc : (a+1/2)^2+(b+1/2)^2≤Q0) (hprimary : X z≤a+1/2)
    (hc : (3/5:ℝ)≤c) (heta : eta∈Icc 0 frameCap)
    (hz : OnCap z) (hlarge : (1/8:ℝ)≤z) :
    force c eta z*a+c*Real.cos eta*b≤
      force c eta z*(X z-1/2)+c*Real.cos eta*(Z z-1/2) := by
  have hZ := Z_pos hz
  have hcircle := Z_sq hz
  have htan : X z*(a+1/2-X z)+Z z*(b+1/2-Z z)≤0 := by
    nlinarith only [hcirc,hcircle,sq_nonneg (a+1/2-X z),sq_nonneg (b+1/2-Z z)]
  have hcpos : 0≤c := by linarith
  have hcos : 0≤Real.cos eta := by linarith [(transport_trig heta).1]
  have hB := mul_nonneg hcpos hcos
  have h1 := mul_nonpos_of_nonneg_of_nonpos hB htan
  have h2 := mul_nonpos_of_nonpos_of_nonneg
    (show force c eta z*Z z-c*Real.cos eta*X z≤0 by
      linarith [large_support_direction hc heta hz hlarge])
    (show 0≤a+1/2-X z by linarith)
  have hzprod : Z z*(force c eta z*a+c*Real.cos eta*b-
      (force c eta z*(X z-1/2)+c*Real.cos eta*(Z z-1/2)))≤0 := by
    nlinarith only [h1,h2]
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hzprod hZ)

theorem boundary_identity {c eta z : ℝ} (hz : z∈Icc 0 frameCap) :
    charge c eta z (X z-1/2) (Z z-1/2)=boundary c eta z := by
  have hcos : Real.cos z≠0 := ne_of_gt (by linarith [(transport_trig hz).1])
  dsimp [charge,force,«prefix»,boundary,X,L]
  field_simp [hcos]
  ring

end SquaresInCircles.Eight.GlobalBT.HighPrimary
end
end
end

section
/-!
## Complete negative-BT1 transport on the restricted original T disk

The explicit split covers the whole necessary-cap domain.  The
comparison retains arbitrary fixed TD force angle and every
multiplier at least three fifths.  No numerical minimizer, residual
derivative hypothesis or asserted feasible aligned state is used.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.HighPrimary

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem circle_transport {a b c eta z : ℝ}
    (hcirc : (a+1/2)^2+(b+1/2)^2≤Q0) (ha : a≤283/200)
    (hprimary : X z≤a+1/2) (hc : (3/5:ℝ)≤c)
    (heta : eta∈Icc 0 frameCap) (hz : OnCap z) :
    aligned c eta≤charge c eta z a b := by
  by_cases hsmall : z≤1/8
  · exact small_lower hcirc ha ⟨hz.1.1,hsmall⟩ c eta
  · have hlarge : (1/8:ℝ)≤z := by linarith
    have hstart : OnCap (1/8) := cap_down hz ⟨by norm_num,hlarge⟩
    have hstartCircle : (X (1/8)-1/2+1/2)^2+(Z (1/8)-1/2+1/2)^2≤Q0 := by
      nlinarith only [Z_sq hstart]
    have hstartPrimary : X (1/8)-1/2≤283/200 := by
      linarith [cap_X_upper hstart]
    have hbase := small_lower hstartCircle hstartPrimary
      (show (1/8:ℝ)∈Icc 0 (1/8:ℝ) by norm_num) c eta
    rw [boundary_identity hstart.1] at hbase
    have hmono := boundary_monotone hc heta hz hlarge
      ⟨le_rfl,hlarge⟩ ⟨hlarge,le_rfl⟩ hlarge
    have hsupport := restricted_support hcirc hprimary hc heta hz hlarge
    have hlast : boundary c eta z≤charge c eta z a b := by
      rw [← boundary_identity hz.1]
      dsimp [charge]
      linarith only [hsupport]
    exact hbase.trans (hmono.trans hlast)

/-- The actual necessary prefix supplies every domain hypothesis of
the full transport theorem. -/
theorem state_transport (a t : State) {c eta z : ℝ}
    (hc : (3/5:ℝ)≤c) (heta : eta∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hpref : «prefix» z≤a.b+t.a/Real.cos z) :
    aligned c eta≤charge c eta z t.a t.b := by
  obtain ⟨hprimary,hcap⟩ := cap_of_prefix a t hz hpref
  exact circle_transport (state_circle t) (ZeroPrimary.coordinates t).2.1.le
    hprimary hc heta hcap

end SquaresInCircles.Eight.GlobalBT.HighPrimary
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.HighPrimary

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem aligned_formula (c eta : ℝ) :
    aligned c eta=2*kappa-R*tailNorm kappa c eta+
      (kappa-c*Real.sin eta+c*Real.cos eta)/2 := by
  have hn : Real.sqrt ((kappa-c*Real.sin eta)^2+(c*Real.cos eta)^2)=
      tailNorm kappa c eta := by
    simpa only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero,zero_add]
      using mixed_force_norm kappa c 0 eta
  dsimp [aligned,full]
  rw [hn]
  ring

theorem transported_prefix (a t : State) {c eta z P : ℝ}
    (hc : (3/5:ℝ)≤c) (heta : eta∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hpref : «prefix» z≤a.b+t.a/Real.cos z)
    (hcharge : -z+kappa*(«prefix» z-t.a/Real.cos z)≤P) :
    2*kappa-R*tailNorm kappa c eta+(kappa-c*Real.sin eta+c*Real.cos eta)/2≤
      P+c*Real.sin eta*t.a-c*Real.cos eta*t.b := by
  have ht := state_transport a t hc heta hz hpref
  rw [aligned_formula] at ht
  dsimp [charge,force] at ht
  have hid : kappa/Real.cos z*t.a=kappa*(t.a/Real.cos z) := by ring
  linarith only [ht,hcharge,hid]

theorem ordinary_support (a t d e : State) (second : Bool)
    {c eWeight margin z s u P : ℝ}
    (ht : 0≤transverse t) (hd : transverse d≤0) (he : transverse e≤0)
    (hc : (3/5:ℝ)≤c) (hz : z∈Icc 0 frameCap)
    (hs : s∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap)
    (hpref : «prefix» z≤a.b+t.a/Real.cos z)
    (hcharge : -z+kappa*(«prefix» z-t.a/Real.cos z)≤P)
    (hmarker : margin+eWeight*e.b≤ZeroPrimary.unsigned e) :
    de2Tail second eWeight margin c 0 s u≤
      Real.pi+P+zeroDual second t d (-s) c+
        quarterDual d e 2 (-u) eWeight+ZeroPrimary.unsigned e := by
  have hty := transverse_of_nonneg t ht
  have hdy : transverse d= -d.b := transverse_nonpos_eq d hd
  have hey : transverse e= -e.b := transverse_nonpos_eq e he
  cases second with
  | false =>
      have hT := transported_prefix a t hc
        (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz hpref hcharge
      have hD := mixed_state_support d eWeight c u s
      rw [add_comm u s] at hD
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero] at hT
      dsimp [de2Tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg,Real.cos_zero,
        mul_one,zero_add]
      nlinarith only [hT,hD,hmarker]
  | true =>
      have hT := transported_prefix a t hc hs hz hpref hcharge
      have hD := mixed_state_support d eWeight c u 0
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero] at hD
      dsimp [de2Tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg,Real.cos_zero,
        mul_one,zero_add]
      nlinarith only [hT,hD,hmarker]

theorem core_support (a t d e : State) (second : Bool) {c z s u P : ℝ}
    (ht : 0≤transverse t) (hd : transverse d≤0) (he : transverse e≤0)
    (hcore : e.branch.type=0) (hc : (3/5:ℝ)≤c)
    (hz : z∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap)
    (hpref : «prefix» z≤a.b+t.a/Real.cos z)
    (hcharge : -z+kappa*(«prefix» z-t.a/Real.cos z)≤P) :
    CoreDE3.tail second (CoreDE3.endpointWeight u) c 0 s u≤
      Real.pi+P+zeroDual second t d (-s) c+
        quarterDual d e 3 (-u) (CoreDE3.endpointWeight u)+ZeroPrimary.unsigned e := by
  have hty := transverse_of_nonneg t ht
  have hdy : transverse d= -d.b := transverse_nonpos_eq d hd
  have hey : transverse e= -e.b := transverse_nonpos_eq e he
  have hmarker := CoreDE3.core_endpoint_marker e hcore hu
  cases second with
  | false =>
      have hT := transported_prefix a t hc
        (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz hpref hcharge
      have hD := mixed_state_support d (CoreDE3.endpointWeight u) c 0 s
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,zero_add] at hT hD
      dsimp [CoreDE3.tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg,Real.cos_zero,
        mul_one,zero_add]
      nlinarith only [hT,hD,hmarker]
  | true =>
      have hT := transported_prefix a t hc hs hz hpref hcharge
      have hD := mixed_state_support d (CoreDE3.endpointWeight u) c 0 0
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero] at hD
      dsimp [CoreDE3.tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg,Real.cos_zero,
        mul_one,zero_add]
      nlinarith only [hT,hD,hmarker]

end SquaresInCircles.Eight.GlobalBT.HighPrimary
end
end
end
