module

public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3PrefixPolynomial

/-!
# Exact tangent majorants for the saturated norm ratios

A factored square difference proves the concave-ratio tangent bound
directly.  Replacing only its positive root denominators by the
explicit smaller rational roots gives the two polynomial tangents.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3

open Polynomial FrameCircleArc

theorem circle_ratio_tangent {b c t N N0 : ℝ}
    (hc : 0≤c) (ht : 0≤t) (hN : 0<N) (hN0 : 0<N0)
    (hs : N^2=b^2+c^2) (hs0 : N0^2=b^2+t^2) :
    c/N≤t/N0+(b^2/N0^3)*(c-t) := by
  have hfactor : ((b^2*c+t^3)*N)^2-(c*N0^3)^2=
      b^2*(c-t)^2*(b^2*c*(c+2*t)+t^3*(2*c+t)) := by
    calc
      ((b^2*c+t^3)*N)^2-(c*N0^3)^2=
          (b^2*c+t^3)^2*N^2-c^2*(N0^2)^3 := by ring
      _ = b^2*(c-t)^2*(b^2*c*(c+2*t)+t^3*(2*c+t)) := by rw [hs,hs0]; ring
  have hfactor_nonneg : 0≤b^2*(c-t)^2*(b^2*c*(c+2*t)+t^3*(2*c+t)) := by positivity
  have hright : 0≤(b^2*c+t^3)*N := by positivity
  have hcross : c*N0^3≤(b^2*c+t^3)*N := by
    nlinarith only [hfactor,hfactor_nonneg,hright]
  have hquot : c/N≤(b^2*c+t^3)/N0^3 :=
    (div_le_div_iff₀ hN (pow_pos hN0 3)).2 hcross
  have hid : (b^2*c+t^3)/N0^3=t/N0+(b^2/N0^3)*(c-t) := by
    field_simp [hN0.ne']
    linear_combination -t*hs0
  rw [hid] at hquot
  exact hquot

theorem saturated_tangent_upper (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) :
    weight p/tailNorm (SaturatedPolynomial.other last:ℝ) (weight p) 0≤
      aeval p (SaturatedPolynomial.tangent last) := by
  let b : ℝ := (SaturatedPolynomial.other last:ℝ)
  let rho : ℝ := (SaturatedPolynomial.rho last:ℝ)
  let N0 := tailNorm b (3/5) 0
  let N := tailNorm b (weight p) 0
  have hb : 0<b := by cases last <;> norm_num [b,SaturatedPolynomial.other]
  have hc := weight_pos hp
  have hzero : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hN : 0<N := tailNorm_pos hb hc hzero
  have hN0 : 0<N0 := tailNorm_pos hb (by norm_num) hzero
  have hsq : N^2=b^2+(weight p)^2 := by
    simpa [N] using tailNorm_sq hb hc hzero
  have hsq0 : N0^2=b^2+(3/5)^2 := by
    simpa [N0] using tailNorm_sq hb (by norm_num : (0:ℝ)<3/5) hzero
  have hreserve := SaturatedPolynomial.rho_reserve last
  have hrho : 0<rho := hreserve.1
  have hroot : rho≤N0 := by
    have hh : rho^2<b^2+(3/5)^2 := by
      rw [show ((3:ℝ)/5)^2=9/25 by norm_num]
      exact hreserve.2
    nlinarith only [hh,hsq0,hN0,hrho]
  have hfirst := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤3/5) hrho hroot
  have hsecond := div_le_div_of_nonneg_left (sq_nonneg b) (pow_pos hrho 3)
    (pow_le_pow_left₀ hrho.le hroot 3)
  have hproduct := mul_le_mul_of_nonneg_right hsecond
    (show 0≤weight p-3/5 by linarith [(weight_bounds hp).1])
  have htangent := circle_ratio_tangent hc.le (by norm_num : (0:ℝ)≤3/5)
    hN hN0 hsq hsq0
  have hpoly : aeval p (SaturatedPolynomial.tangent last)=
      (3/5)/rho+(b^2/rho^3)*(weight p-3/5) := by
    simp only [SaturatedPolynomial.tangent,map_add,map_mul,aeval_C,aeval_X,eq_ratCast]
    push_cast
    dsimp [rho,b,weight,slope]
    ring
  rw [hpoly]
  change weight p/N≤_
  linarith only [hfirst,hproduct,htangent]

end SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3
