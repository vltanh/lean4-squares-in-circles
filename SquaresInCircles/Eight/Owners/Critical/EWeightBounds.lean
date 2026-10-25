module

public import SquaresInCircles.Eight.Owners.Critical.ERatioBounds
public import SquaresInCircles.Eight.Owners.Critical.ECoefficients

/-!
# Eight squares: actual coefficient bounds on every critical minimizing fibre

All ordinary-envelope coefficients are now the
literal functions of the original common-radius circle chain. Positive
denominator substitution proves the numerical bounds, and position
stationarity gives the correlated l/c and c/k comparisons. The public
entry theorem selects minimizingPosition itself and discharges the
affine-strip and stationary-position premises.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalEWeightBounds
open CriticalEPolynomials CriticalERadicals CriticalESubstitution CriticalEPosition
open CriticalEFamily Stationary.FiveCornerGeometry

theorem weight_formulas {q t u : ℝ} (h : SmoothDomain q u) :
    k q t u=(Real.cos t*lowerLeft q u+Real.sin t*lowerHeight q u)*topLeft q u/
      (lowerLeft q u*topHeight q u) ∧
    ell q t u=(Real.cos t*lowerLeft q u+Real.sin t*lowerHeight q u)*topLeft q u*(2-u)/
      (lowerLeft q u*topHeight q u*topRight q u) := by
  dsimp [k,ell,lam,eta]
  constructor <;> field_simp [h.w_pos.ne',h.Y_pos.ne',h.U_pos.ne']

theorem original_bounds {q t u : ℝ}
    (hq : q∈Icc (qLower:ℝ) (qUpper:ℝ)) (ht : t∈Icc (1/10:ℝ) (4/25))
    (hu : u∈Icc (ev t uMinus) (ev t uPlus))
    (hposition : positionHalf q (Real.cos t) (Real.sin t) u=0) :
    CriticalECoefficients.Bounds t (k q t u) (ell q t u) (c q t u) (eta q u) := by
  have hr := actual_radicals .mixed hq ht hu
  have hu0 : 0≤u := by
    have h1 := hu.1
    rw [ev_minus] at h1
    linarith [ht.2]
  have hd := hr.smoothDomain ht hu0 (by norm_num [qUpper] at hq; linarith [hq.2])
  obtain ⟨hc,hs,_⟩ := tiltInterval_bounds (angle_mem ht)
  have hpos := positive_weights hd hc hs.le
  have hforms := weight_formulas (t := t) hd
  have e2 : ev t (2:Polynomial ℚ)=2 := by rw [ev]; exact map_ofNat _ 2
  let B := boxes ht hu hr
  let L := (B.cosine.mul B.w).add (B.sine.mul B.v)
  let KN := L.mul B.V
  let KD := B.w.mul B.Y
  let EN := KN.mul B.other
  let ED := KD.mul B.U
  let PN := (B.sine.mul B.r).add (B.cosine.mul B.height)
  have hp (i : Fin 6) : 0<ev t (coordinateLower .mixed i) := by
    linarith [(polynomial_coordinates .mixed i ht).1]
  have hrlo : 0<B.r.lo := by rw [B.r_lo]; exact hp 0
  have hUlo : 0<B.U.lo := by rw [B.U_lo]; exact hp 1
  have hYlo : 0<B.Y.lo := by rw [B.Y_lo]; exact hp 3
  have hwlo : 0<B.w.lo := by rw [B.w_lo]; exact hp 5
  have hKDp : 0<KD.lo := mul_pos hwlo hYlo
  have hEDp : 0<ED.lo := mul_pos hKDp hUlo
  have hsecond : 0<B.second.lo := by
    rw [B.second_lo]
    linarith [(auxiliary_bounds .mixed ht).2.2.2]
  have hpoly (i : Coefficient) : 0<ev t (cleared i) := coefficient_positive i (local_parameter ht)
  have helo : (27/100:ℝ)<eta q u := by
    apply PositiveInterval.lower_ratio B.v B.w hwlo (by norm_num)
    rw [B.w_hi,B.v_lo]
    have hh := hpoly .etaLower
    simp only [cleared,ev_sub,ev_mul,ev_C] at hh
    push_cast at hh
    linarith
  have hehi : eta q u<31/100 := by
    apply PositiveInterval.upper_ratio B.v B.w hwlo (by norm_num)
    rw [B.v_hi,B.w_lo]
    have hh := hpoly .etaUpper
    simp only [cleared,ev_sub,ev_mul,ev_C] at hh
    push_cast at hh
    linarith
  have hklo : (37/40:ℝ)<k q t u := by
    rw [hforms.1]
    apply PositiveInterval.lower_ratio KN KD hKDp (by norm_num)
    show (37/40:ℝ)*(B.w.hi*B.Y.hi)<(B.cosine.lo*B.w.lo+B.sine.lo*B.v.lo)*B.V.lo
    rw [B.w_hi,B.Y_hi,B.cosine_lo,B.w_lo,B.sine_lo,B.v_lo,B.V_lo]
    have hh := hpoly .kLower
    simp only [cleared,ev_sub,ev_mul,ev_add,ev_C] at hh
    push_cast at hh
    linarith
  have hkhi : k q t u<197/200 := by
    rw [hforms.1]
    apply PositiveInterval.upper_ratio KN KD hKDp (by norm_num)
    show (B.cosine.hi*B.w.hi+B.sine.hi*B.v.hi)*B.V.hi<(197/200:ℝ)*(B.w.lo*B.Y.lo)
    rw [B.w_hi,B.Y_lo,B.cosine_hi,B.w_lo,B.sine_hi,B.v_hi,B.V_hi]
    have hh := hpoly .kUpper
    simp only [cleared,ev_sub,ev_mul,ev_add,ev_C] at hh
    push_cast at hh
    linarith
  have hello : 0<ell q t u := hpos.2.2.2.1
  have hellhi : ell q t u<67/100 := by
    rw [hforms.2]
    apply PositiveInterval.upper_ratio EN ED hEDp (by norm_num)
    show (B.cosine.hi*B.w.hi+B.sine.hi*B.v.hi)*B.V.hi*B.other.hi<
      (67/100:ℝ)*(B.w.lo*B.Y.lo*B.U.lo)
    rw [B.w_hi,B.Y_lo,B.cosine_hi,B.w_lo,B.sine_hi,B.v_hi,B.V_hi,B.other_hi,B.U_lo]
    have hh := hpoly .ellUpper
    simp only [cleared,ev_sub,ev_mul,ev_add,ev_C,e2] at hh
    push_cast at hh
    linarith
  have helk : ell q t u<(27/40)*k q t u := by
    have hh : (2-u)/topRight q u<(27/40:ℝ) := by
      apply PositiveInterval.upper_ratio B.other B.U hUlo (by norm_num)
      rw [B.other_hi,B.U_lo]
      have hh := hpoly .ellK
      simp only [cleared,ev_sub,ev_mul,ev_C,e2] at hh
      push_cast at hh
      linarith
    have hm := mul_lt_mul_of_pos_left hh hpos.2.2.1
    have he : ell q t u=k q t u*((2-u)/topRight q u) := by
      simp only [ell]
      ring
    rw [he]
    linarith
  have hclo : (37/40:ℝ)<c q t u := by
    apply PositiveInterval.lower_ratio B.first B.second hsecond (by norm_num)
    rw [B.second_hi,B.first_lo]
    have hh := hpoly .cLower
    simp only [cleared,ev_sub,ev_mul,ev_C] at hh
    push_cast at hh
    linarith
  have hchi : c q t u<1 := by
    apply PositiveInterval.upper_ratio B.first B.second hsecond (by norm_num)
    rw [B.first_hi,B.second_lo]
    have hh := hpoly .cUpper
    simp only [cleared,ev_sub] at hh
    linarith
  have hPa : (Real.sin t*lowerRight q u+Real.cos t*u)/lowerRight q u=
      Real.sin t+Real.cos t*u/lowerRight q u := by
    field_simp [hd.r_pos.ne']
  have hpaLo : (63/100:ℝ)<Real.sin t+Real.cos t*u/lowerRight q u := by
    rw [← hPa]
    apply PositiveInterval.lower_ratio PN B.r hrlo (by norm_num)
    show (63/100:ℝ)*B.r.hi<B.sine.lo*B.r.lo+B.cosine.lo*B.height.lo
    rw [B.r_hi,B.sine_lo,B.r_lo,B.cosine_lo,B.height_lo]
    have hh := hpoly .ellCLower
    simp only [cleared,ev_sub,ev_mul,ev_add,ev_C] at hh
    push_cast at hh
    linarith
  have hpaHi : Real.sin t+Real.cos t*u/lowerRight q u<(17/25:ℝ) := by
    rw [← hPa]
    apply PositiveInterval.upper_ratio PN B.r hrlo (by norm_num)
    show B.sine.hi*B.r.hi+B.cosine.hi*B.height.hi<(17/25:ℝ)*B.r.lo
    rw [B.r_hi,B.sine_hi,B.r_lo,B.cosine_hi,B.height_hi]
    have hh := hpoly .ellCUpper
    simp only [cleared,ev_sub,ev_mul,ev_C] at hh
    push_cast at hh
    linarith
  have hel := CriticalEFamily.stationary_ratio hd hc hs.le hposition
  have helcLo : (63/100)*c q t u<ell q t u := by
    rw [hel]
    linarith [mul_lt_mul_of_pos_left hpaLo hpos.2.2.2.2]
  have helcHi : ell q t u<(17/25)*c q t u := by
    rw [hel]
    linarith [mul_lt_mul_of_pos_left hpaHi hpos.2.2.2.2]
  have hck := CriticalERatioBounds.original_ratio_upper hq ht hu hposition
  have hck' : c q t u<(51/50)*k q t u := (div_lt_iff₀ hpos.2.2.1).1 hck
  have hdiff : c q t u-k q t u<1/50 := by linarith [hkhi]
  exact ⟨ht.1,ht.2,hklo,hkhi,hclo,hchi,hello,hellhi,helk,helcLo,helcHi,hdiff,helo,hehi⟩

/-- All coefficient conditions are conclusions about the actual
geometric position minimum, for each tilt in the critical interval. -/
theorem minimizing_bounds {q t : ℝ}
    (hq : q∈Icc (qLower:ℝ) (qUpper:ℝ)) (ht : t∈Icc (1/10:ℝ) (4/25)) :
    CriticalECoefficients.Bounds t (k q t (minimizingPosition q t))
      (ell q t (minimizingPosition q t)) (c q t (minimizingPosition q t))
      (eta q (minimizingPosition q t)) := by
  have hs := minimizingPosition_strip hq ht
  have hql : (79/40:ℝ)^2≤q := by norm_num [qLower] at hq ⊢; linarith [hq.1]
  have hqu : q≤9789/2500 := by norm_num [qUpper] at hq; linarith [hq.2]
  have hz := minimizingPosition_root hql hqu (angle_mem ht)
  apply original_bounds hq ht (by rw [Set.mem_Icc,ev_minus,ev_plus]; exact ⟨hs.1.le,hs.2.le⟩)
  dsimp [jointPosition] at hz
  linarith

end SquaresInCircles.Eight.CriticalEWeightBounds
