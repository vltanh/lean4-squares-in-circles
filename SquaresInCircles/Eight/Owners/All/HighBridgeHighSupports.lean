module

public import SquaresInCircles.Eight.Owners.All.HighBridgeData
public import SquaresInCircles.Eight.Owners.All.HighZeroPositive

/-!
# Eight squares: whole-arc supports for the high-source bridge

The lower-chart target expressions are concave on their unchanged
intrinsic arcs.  The high target uses one shifted-circle support.
The high source has its two actual intrinsic endpoints.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh.Bridge

open FramePair ZeroPrimary GlobalOuterAnchor FrameCircleArc FrameLowArc FrameMidArc

theorem arcPotential_low (b : ℝ) :
    arcPotential .low b=rho*(FrameHighArc.k+FrameLowArc.u*a0)-
      (406817/10000000)*A b-(7679969/10000000)*b := by
  rw [arcPotential,arcMarker_low]
  dsimp [kappa,rho,FrameHighArc.H,FrameHighArc.u,FrameHighArc.v,
    FrameLowArc.L,FrameLowArc.u,FrameLowArc.v]
  ring

theorem arcPotential_middle (b : ℝ) :
    arcPotential .middle b=rho*(FrameHighArc.k-FrameMidArc.cM)-
      (2469943/2000000)*A b-(13082663/10000000)*b := by
  rw [arcPotential,arcMarker_middle]
  dsimp [kappa,rho,FrameHighArc.H,FrameHighArc.u,FrameHighArc.v,
    FrameMidArc.M,FrameMidArc.p,FrameMidArc.q]
  ring

theorem low_target_endpoint {b lambda g : ℝ} (hb : b∈Icc 0 b1)
    (h0 : g< -arcPotential .low 0)
    (h1 : g< -arcPotential .low b1-lambda*b1) :
    g< -arcPotential .low b-lambda*b := by
  have hh := linear_endpoint_lower (p := (406817/10000000:ℝ))
    (q := 7679969/10000000-lambda) (by norm_num) (by norm_num) b1_mem.2 hb
  have he : g+rho*(FrameHighArc.k+FrameLowArc.u*a0)<
      min (linear (406817/10000000) (7679969/10000000-lambda) 0)
        (linear (406817/10000000) (7679969/10000000-lambda) b1) := by
    apply lt_min
    · rw [arcPotential_low] at h0
      dsimp [linear]
      linarith
    · rw [arcPotential_low] at h1
      dsimp [linear]
      linarith
  have h := he.trans_le hh
  rw [arcPotential_low]
  dsimp [linear] at h
  linarith

theorem middle_target_endpoint {b lambda g : ℝ} (hb : b∈Icc b1 b2)
    (h0 : g< -arcPotential .middle b1-lambda*b1)
    (h1 : g< -arcPotential .middle b2-lambda*b2) :
    g< -arcPotential .middle b-lambda*b := by
  have hh := linear_endpoint_lower (p := (2469943/2000000:ℝ))
    (q := 13082663/10000000-lambda) (by norm_num) b1_mem.1 b2_mem.2 hb
  have he : g+rho*(FrameHighArc.k-FrameMidArc.cM)<
      min (linear (2469943/2000000) (13082663/10000000-lambda) b1)
        (linear (2469943/2000000) (13082663/10000000-lambda) b2) := by
    apply lt_min
    · rw [arcPotential_middle] at h0
      dsimp [linear]
      linarith
    · rw [arcPotential_middle] at h1
      dsimp [linear]
      linarith
  have h := he.trans_le hh
  rw [arcPotential_middle]
  dsimp [linear] at h
  linarith

theorem low_target_bound {b : ℝ} (hb : b∈Icc 0 b1) :
    -(403/250:ℝ)< -arcPotential .low b-(151/200)*b := by
  apply low_target_endpoint hb
  · rw [arcPotential_low,A_zero]
    dsimp [rho,FrameLowArc.u]
    linarith [FrameHighArc.k_bounds.2.1,a0_precise.2,a0_precise.1]
  · rw [arcPotential_low,A_b1]
    dsimp [rho,FrameLowArc.u]
    linarith [FrameHighArc.k_bounds.2.1,a0_precise.2,a1_precise.1,b1_precise.1]

theorem nonlow_target_bound (t : State) (ht : t.branch=.middle ∨ t.branch=.high) :
    -(1999/1250:ℝ)< -potential t-(69/100)*t.b := by
  rcases ht with ht | ht
  · rw [potential_arc t (by simp [ht,Branch.type]),ht]
    apply middle_target_endpoint (state_mid_chart t ht).2
    · rw [arcPotential_middle,A_b1]
      dsimp [rho,FrameMidArc.cM]
      linarith [FrameHighArc.k_bounds.2.1,a1_precise.1,b1_precise.1]
    · rw [arcPotential_middle,A_b2]
      dsimp [rho,FrameMidArc.cM]
      linarith [FrameHighArc.k_bounds.2.1,a2_bounds.1,b2_precise.1]
  · rw [potential_high t ht]
    have hh := circle_product_support t (f := kappa) (g := 69/100)
      (K := 24533/10000) (by norm_num) (by norm_num [Q0,kappa])
    dsimp only [kappa] at hh ⊢
    linarith

def endpoint (lambda g a b z : ℝ) : ℝ :=
  Real.pi/2-z+kappa*a+g+
    lambda*(1/2+(1/2-a)*Real.cos z+(1/2+b)*Real.sin z)

theorem endpoint_deriv (lambda g a b z : ℝ) :
    HasDerivAt (endpoint lambda g a b)
      (-1+lambda*((a-1/2)*Real.sin z+(b+1/2)*Real.cos z)) z := by
  have h1 : HasDerivAt (fun x : ℝ => Real.pi/2-x+kappa*a+g) (-1) z :=
    (((hasDerivAt_id' z).const_sub (Real.pi/2)).add_const (kappa*a)).add_const g
  have h2 : HasDerivAt (fun x => 1/2+(1/2-a)*Real.cos x)
      ((1/2-a)*(-Real.sin z)) z :=
    ((Real.hasDerivAt_cos z).const_mul (1/2-a)).const_add (1/2)
  have h3 : HasDerivAt (fun x => 1/2+(1/2-a)*Real.cos x+(1/2+b)*Real.sin x)
      ((1/2-a)*(-Real.sin z)+(1/2+b)*Real.cos z) z :=
    h2.fun_add ((Real.hasDerivAt_sin z).const_mul (1/2+b))
  have h : HasDerivAt (fun x => Real.pi/2-x+kappa*a+g+
      lambda*(1/2+(1/2-a)*Real.cos x+(1/2+b)*Real.sin x))
      (-1+lambda*((1/2-a)*(-Real.sin z)+(1/2+b)*Real.cos z)) z :=
    h1.fun_add (h3.const_mul lambda)
  exact h.congr_deriv (by ring)

theorem cut_endpoint_antitone {lambda g : ℝ} (hl : lambda∈Icc 0 (151/200:ℝ)) :
    AntitoneOn (endpoint lambda g a2 b2) (Icc 0 frameCap) := by
  have ha : 0≤a2-1/2 := by linarith [a2_bounds.1]
  have hb : 0≤b2+1/2 := by linarith [b2_mem.1]
  have hA : lambda*(a2-1/2)≤1057/2000 := by
    calc
      lambda*(a2-1/2)≤(151/200)*(a2-1/2) := mul_le_mul_of_nonneg_right hl.2 ha
      _≤1057/2000 := by linarith [a2_bounds.2]
  have hB : lambda*(b2+1/2)≤76557/100000 := by
    calc
      lambda*(b2+1/2)≤(151/200)*(b2+1/2) := mul_le_mul_of_nonneg_right hl.2 hb
      _≤76557/100000 := by linarith [b2_bounds.2]
  have hsq : (lambda*(a2-1/2))^2+(lambda*(b2+1/2))^2<(1:ℝ)^2 := by
    have hA2 := pow_le_pow_left₀ (mul_nonneg hl.1 ha) hA 2
    have hB2 := pow_le_pow_left₀ (mul_nonneg hl.1 hb) hB 2
    norm_num at hA2 hB2
    linarith
  apply antiOn_of_hasDeriv_nonpos
  · exact fun z _ => (endpoint_deriv lambda g a2 b2 z).continuousAt.continuousWithinAt
  · exact fun z _ => endpoint_deriv lambda g a2 b2 z
  · intro z hz
    have hp := FrameCoreArc.projection_lt (by norm_num : (0:ℝ)<1) hsq z
    nlinarith only [hp]

theorem cut_endpoint_bounds :
    (24/25:ℝ)<endpoint (151/200) (-403/250) a2 b2 frameCap ∧
    (24/25:ℝ)<endpoint (69/100) (-1999/1250) a2 b2 (1/2) := by
  have ha := a2_bounds
  have hb := b2_precise
  have hp := Arithmetic.pi_hand_enclosure.1
  have proveEndpoint (lambda g z : ℝ) (hz : z∈Icc 0 frameCap)
      (hl : lambda∈Icc 0 (151/200:ℝ)) :
      endpoint lambda g (59962803/50000000) (1284917/2500000) z≤
        endpoint lambda g a2 b2 z := by
    have tr := transport_trig hz
    have hcoef : 0≤kappa-lambda*Real.cos z := by
      have hm := mul_le_mul_of_nonneg_left tr.2.1 hl.1
      dsimp [kappa]
      linarith [hl.2]
    have h1 := mul_nonneg hcoef (show 0≤a2-59962803/50000000 by linarith [ha.1])
    have h2 := mul_nonneg (mul_nonneg hl.1 tr.2.2.1)
      (show 0≤b2-1284917/2500000 by linarith [hb.1])
    dsimp [endpoint]
    nlinarith only [h1,h2]
  constructor
  · have htransfer := proveEndpoint (151/200) (-403/250) frameCap
      ⟨by norm_num [frameCap],le_rfl⟩ ⟨by norm_num,le_rfl⟩
    have hs := sin_lower_seven (show (0:ℝ)≤frameCap by norm_num [frameCap])
    have hc := Arithmetic.cos_le_cos8 (show (0:ℝ)≤frameCap by norm_num [frameCap])
    norm_num [Arithmetic.cos8,frameCap] at hs hc
    dsimp [endpoint,kappa,frameCap] at htransfer ⊢
    linarith
  · have htransfer := proveEndpoint (69/100) (-1999/1250) (1/2)
      (by norm_num [frameCap]) (by norm_num)
    have hs := sin_lower_seven (show (0:ℝ)≤1/2 by norm_num)
    have hc := Arithmetic.cos_le_cos8 (show (0:ℝ)≤1/2 by norm_num)
    norm_num [Arithmetic.cos8] at hs hc
    dsimp [endpoint,kappa] at htransfer ⊢
    linarith

/-- A single quadratic lower bound on the complete initial interval. -/
theorem diagonal_endpoint_quadratic {lambda g z u : ℝ} (hl : 0≤lambda)
    (hz : z∈Icc 0 u) (_hu : 0≤u) :
    endpoint lambda g c0 c0 0+
      (lambda*(c0+1/2)-1)*z+
      lambda*((c0-1/2)*(1/2-u^2/24)-(c0+1/2)*u/6)*z^2≤
        endpoint lambda g c0 c0 z := by
  have h3 := mul_le_mul_of_nonneg_right hz.2 (sq_nonneg z)
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  have h4 := mul_le_mul_of_nonneg_right h2 (sq_nonneg z)
  have hs : z-u*z^2/6≤Real.sin z := by
    nlinarith [Real.sin_ge_sub_cube hz.1]
  have hc : (1/2-u^2/24)*z^2≤1-Real.cos z := by
    nlinarith [cos_upper_four hz.1]
  have hs' := mul_le_mul_of_nonneg_left hs
    (mul_nonneg hl (show 0≤c0+1/2 by linarith [c0_precise.1]))
  have hc' := mul_le_mul_of_nonneg_left hc
    (mul_nonneg hl (show 0≤c0-1/2 by linarith [c0_precise.1]))
  norm_num [endpoint] at *
  nlinarith only [hs',hc']

theorem diagonal_low_endpoint {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (24/25:ℝ)<endpoint (151/200) (-403/250) c0 c0 z := by
  have hq := diagonal_endpoint_quadratic (g := (-403/250:ℝ))
    (by norm_num : (0:ℝ)≤151/200) hz (by norm_num [frameCap])
  have hc : 0≤(151/200)*(c0+1/2)-1 := by linarith [c0_precise.1]
  have hd : 0≤(151/200)*((c0-1/2)*(1/2-frameCap^2/24)-(c0+1/2)*frameCap/6) := by
    dsimp [frameCap]
    linarith [c0_precise.1]
  have he : (24/25:ℝ)<endpoint (151/200) (-403/250) c0 c0 0 := by
    norm_num [endpoint,kappa]
    linarith [Arithmetic.pi_hand_enclosure.1,c0_precise.1]
  exact he.trans_le (by nlinarith [mul_nonneg hc hz.1,mul_nonneg hd (sq_nonneg z)])

theorem diagonal_nonlow_endpoint {z : ℝ} (hz : z∈Icc 0 (1/2:ℝ)) :
    (24/25:ℝ)<endpoint (69/100) (-1999/1250) c0 c0 z := by
  have hq := diagonal_endpoint_quadratic (g := (-1999/1250:ℝ))
    (by norm_num : (0:ℝ)≤69/100) hz (by norm_num)
  have hc : -(691/20000:ℝ)≤(69/100)*(c0+1/2)-1 := by linarith [c0_precise.1]
  have hd : (543/10000:ℝ)≤
      (69/100)*((c0-1/2)*(1/2-(1/2:ℝ)^2/24)-(c0+1/2)*(1/2)/6) := by
    norm_num
    linarith [c0_precise.1]
  have he : (9673/10000:ℝ)<endpoint (69/100) (-1999/1250) c0 c0 0 := by
    norm_num [endpoint,kappa]
    linarith [Arithmetic.pi_hand_enclosure.1,c0_precise.1]
  have hp := positive_quadratic (z := z)
    (show (0:ℝ)<543/10000 by norm_num)
    (show (-(691/20000:ℝ))^2<4*(543/10000)*(73/10000) by norm_num)
  have hl := mul_le_mul_of_nonneg_right hc hz.1
  have hu := mul_le_mul_of_nonneg_right hd (sq_nonneg z)
  nlinarith only [hq,he,hp,hl,hu]

end SquaresInCircles.Eight.GlobalAllHigh.Bridge
