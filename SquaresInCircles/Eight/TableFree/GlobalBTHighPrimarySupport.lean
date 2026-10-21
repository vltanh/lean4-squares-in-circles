module

public import SquaresInCircles.Eight.TableFree.GlobalBTHighPrimaryCurvature

/-!
# Explicit support on both parts of the high-primary cap

Up to one eighth, a positive polynomial pays the extra secant force
using the original universal primary bound.  Beyond one eighth,
uniform rational bounds put the support maximum on the primary
boundary.  Every comparison is on the same corner disk.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.HighPrimary

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

def full (f g : ℝ) : ℝ := R*Real.sqrt (f^2+g^2)-(f+g)/2
def force (c eta z : ℝ) : ℝ := kappa/Real.cos z-c*Real.sin eta
def charge (c eta z a b : ℝ) : ℝ :=
  -z+kappa*prefix z-force c eta z*a-c*Real.cos eta*b
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
  have hs := sin_lower_three hz.1
  have hc := cos_lower_two hz.1
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
    dsimp [charge,aligned,force,prefix]
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
    apply (mul_le_mul_right hzcos).mp
    have hid : ((kappa/Real.cos z)*Z z)*Real.cos z=kappa*Z z := by
      field_simp [hzcos.ne']
      ring
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
  exact sub_nonpos.mp ((mul_nonpos_iff_of_pos_left hZ).mp hzprod)

theorem boundary_identity {c eta z : ℝ} (hz : z∈Icc 0 frameCap) :
    charge c eta z (X z-1/2) (Z z-1/2)=boundary c eta z := by
  have hcos : Real.cos z≠0 := ne_of_gt (by linarith [(transport_trig hz).1])
  dsimp [charge,force,prefix,boundary,X,L]
  field_simp [hcos]
  ring

end SquaresInCircles.Eight.TableFree.GlobalBT.HighPrimary
