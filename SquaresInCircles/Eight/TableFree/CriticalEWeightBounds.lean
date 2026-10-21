module

public import SquaresInCircles.Eight.TableFree.CriticalERatioBounds
public import SquaresInCircles.Eight.TableFree.CriticalECoefficients

/-!
# Actual coefficient bounds on every critical minimizing fibre

Uncompiled source. All ordinary-envelope coefficients are now the
literal functions of the original common-radius circle chain. Positive
denominator substitution proves the numerical bounds, and position
stationarity gives the correlated l/c and c/k comparisons. The public
entry theorem selects minimizingPosition itself and discharges the
affine-strip and stationary-position premises.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalEWeightBounds
open CriticalEPolynomials CriticalERadicals CriticalESubstitution CriticalEPosition
open CriticalEFamily ExactFamily.FiveCornerGeometry

theorem weight_formulas {q t u : ℝ} (h : SmoothDomain q u) :
    k q t u=(Real.cos t*lowerLeft q u+Real.sin t*lowerHeight q u)*topLeft q u/
      (lowerLeft q u*topHeight q u) ∧
    ell q t u=(Real.cos t*lowerLeft q u+Real.sin t*lowerHeight q u)*topLeft q u*(2-u)/
      (lowerLeft q u*topHeight q u*topRight q u) := by
  dsimp [k,ell,lam,eta]
  constructor <;> field_simp [h.w_pos.ne',h.Y_pos.ne',h.U_pos.ne'] <;> ring

theorem original_bounds {q t u : ℝ}
    (hq : q∈Icc (qLower:ℝ) (qUpper:ℝ)) (ht : t∈Icc (1/10:ℝ) (4/25))
    (hu : u∈Icc (ev t uMinus) (ev t uPlus))
    (hposition : positionHalf q (Real.cos t) (Real.sin t) u=0) :
    CriticalECoefficients.Bounds t (k q t u) (ell q t u) (c q t u) (eta q u) := by
  have hr := actual_radicals .mixed hq ht hu
  have hd := hr.smoothDomain ht (by linarith [hu.1,(endpoints ht .mixed).1])
    (by norm_num [qUpper] at hq; linarith [hq.2])
  obtain ⟨hc,hs,_⟩ := tiltInterval_bounds (angle_mem ht)
  have hpos := positive_weights hd hc hs.le
  have hforms := weight_formulas hd
  let B := boxes ht hu hr
  let L := (B.cosine.mul B.w).add (B.sine.mul B.v)
  let KN := L.mul B.V
  let KD := B.w.mul B.Y
  let EN := KN.mul B.other
  let ED := KD.mul B.U
  let PN := (B.sine.mul B.r).add (B.cosine.mul B.height)
  have hp (i : Fin 6) : 0<ev t (coordinateLower .mixed i) := by
    linarith [(polynomial_coordinates .mixed i ht).1]
  have hrlo : 0<B.r.lo := by simpa [B,boxes,PositiveInterval.of_bounds] using hp 0
  have hUlo : 0<B.U.lo := by simpa [B,boxes,PositiveInterval.of_bounds] using hp 1
  have hYlo : 0<B.Y.lo := by simpa [B,boxes,PositiveInterval.of_bounds] using hp 3
  have hwlo : 0<B.w.lo := by simpa [B,boxes,PositiveInterval.of_bounds] using hp 5
  have hKDp : 0<KD.lo := mul_pos hwlo hYlo
  have hEDp : 0<ED.lo := mul_pos hKDp hUlo
  have hsecond : 0<B.second.lo := by
    simpa [B,boxes,PositiveInterval.of_bounds] using
      (show 0<ev t (secondLo .mixed) by linarith [(auxiliary_bounds .mixed ht).2.2.2])
  have hpoly (i : Coefficient) : 0<ev t (cleared i) := coefficient_positive i (local_parameter ht)
  have helo : (27/100:ℝ)<eta q u := by
    apply PositiveInterval.lower_ratio B.v B.w hwlo (by norm_num)
    have hh := hpoly .etaLower
    simpa [cleared,B,boxes,PositiveInterval.of_bounds,sub_pos] using hh
  have hehi : eta q u<31/100 := by
    apply PositiveInterval.upper_ratio B.v B.w hwlo (by norm_num)
    have hh := hpoly .etaUpper
    simpa [cleared,B,boxes,PositiveInterval.of_bounds,sub_pos] using hh
  have hklo : (37/40:ℝ)<k q t u := by
    rw [hforms.1]
    apply PositiveInterval.lower_ratio KN KD hKDp (by norm_num)
    have hh := hpoly .kLower
    simpa [cleared,KN,KD,L,B,boxes,PositiveInterval.of_bounds,
      PositiveInterval.mul,PositiveInterval.add,sub_pos] using hh
  have hkhi : k q t u<197/200 := by
    rw [hforms.1]
    apply PositiveInterval.upper_ratio KN KD hKDp (by norm_num)
    have hh := hpoly .kUpper
    simpa [cleared,KN,KD,L,B,boxes,PositiveInterval.of_bounds,
      PositiveInterval.mul,PositiveInterval.add,sub_pos] using hh
  have hello : 0<ell q t u := hpos.2.2.2.1
  have hellhi : ell q t u<67/100 := by
    rw [hforms.2]
    apply PositiveInterval.upper_ratio EN ED hEDp (by norm_num)
    have hh := hpoly .ellUpper
    simpa [cleared,EN,ED,KN,KD,L,B,boxes,PositiveInterval.of_bounds,
      PositiveInterval.mul,PositiveInterval.add,sub_pos] using hh
  have helk : ell q t u<(27/40)*k q t u := by
    have hh : (2-u)/topRight q u<(27/40:ℝ) := by
      apply PositiveInterval.upper_ratio B.other B.U hUlo (by norm_num)
      have hh := hpoly .ellK
      simpa [cleared,B,boxes,PositiveInterval.of_bounds,sub_pos] using hh
    have hm := mul_lt_mul_of_pos_left hh hpos.2.2.1
    simpa [ell,mul_div_assoc,mul_comm] using hm
  have hclo : (37/40:ℝ)<c q t u := by
    apply PositiveInterval.lower_ratio B.first B.second hsecond (by norm_num)
    have hh := hpoly .cLower
    simpa [cleared,B,boxes,PositiveInterval.of_bounds,sub_pos] using hh
  have hchi : c q t u<1 := by
    apply PositiveInterval.upper_ratio B.first B.second hsecond (by norm_num)
    have hh := hpoly .cUpper
    simpa [cleared,B,boxes,PositiveInterval.of_bounds,sub_pos] using hh
  have hPa : (Real.sin t*lowerRight q u+Real.cos t*u)/lowerRight q u=
      Real.sin t+Real.cos t*u/lowerRight q u := by
    field_simp [hd.r_pos.ne']
    ring
  have hpaLo : (63/100:ℝ)<Real.sin t+Real.cos t*u/lowerRight q u := by
    rw [← hPa]
    apply PositiveInterval.lower_ratio PN B.r hrlo (by norm_num)
    have hh := hpoly .ellCLower
    simpa [cleared,PN,B,boxes,PositiveInterval.of_bounds,
      PositiveInterval.mul,PositiveInterval.add,sub_pos] using hh
  have hpaHi : Real.sin t+Real.cos t*u/lowerRight q u<(17/25:ℝ) := by
    rw [← hPa]
    apply PositiveInterval.upper_ratio PN B.r hrlo (by norm_num)
    have hh := hpoly .ellCUpper
    simpa [cleared,PN,B,boxes,PositiveInterval.of_bounds,
      PositiveInterval.mul,PositiveInterval.add,sub_pos] using hh
  have hel := CriticalEFamily.stationary_ratio hd hc hs.le hposition
  have helcLo : (63/100)*c q t u<ell q t u := by
    rw [hel]
    nlinarith [mul_lt_mul_of_pos_left hpaLo hpos.2.2.2.2]
  have helcHi : ell q t u<(17/25)*c q t u := by
    rw [hel]
    nlinarith [mul_lt_mul_of_pos_left hpaHi hpos.2.2.2.2]
  have hck := CriticalERatioBounds.original_ratio_upper hq ht hu hposition
  have hck' : c q t u<(51/50)*k q t u := (div_lt_iff₀ hpos.2.2.1).1 hck
  have hdiff : c q t u-k q t u<1/50 := by nlinarith [hkhi]
  exact ⟨ht.1,ht.2,hklo,hkhi,hclo,hchi,hello,hellhi,helk,helcLo,helcHi,hdiff,helo,hehi⟩

/-- All coefficient conditions are conclusions about the actual
geometric position minimum, for each tilt in the critical interval. -/
theorem minimizing_bounds {q t : ℝ}
    (hq : q∈Icc (qLower:ℝ) (qUpper:ℝ)) (ht : t∈Icc (1/10:ℝ) (4/25)) :
    CriticalECoefficients.Bounds t (k q t (minimizingPosition q t))
      (ell q t (minimizingPosition q t)) (c q t (minimizingPosition q t))
      (eta q (minimizingPosition q t)) := by
  have hs := minimizingPosition_strip hq ht
  have hql : (79/40:ℝ)^2≤q := by norm_num [qLower] at hq; nlinarith [hq.1]
  have hqu : q≤9789/2500 := by norm_num [qUpper] at hq; linarith [hq.2]
  have hz := minimizingPosition_root hql hqu (angle_mem ht)
  apply original_bounds hq ht
    (by simpa only [ev_minus,ev_plus] using And.intro hs.1.le hs.2.le)
  dsimp [jointPosition] at hz
  linarith

end SquaresInCircles.Eight.TableFree.CriticalEWeightBounds
