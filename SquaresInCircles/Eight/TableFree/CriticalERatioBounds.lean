module

public import SquaresInCircles.Eight.TableFree.CriticalEPosition
public import SquaresInCircles.Eight.TableFree.CriticalEFamily

/-!
# The correlated c/k bound for the sharp critical family

Uncompiled source. Position stationarity expresses c/k as a ratio
which decreases with the actual position. Its denominator increases
by circle monotonicity. The comparison therefore uses the lower affine
chain itself, preserving the correlation lost by an independent box
for k and c. The endpoint polynomial covers the complete tilt strip.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalERatioBounds
open CriticalEPolynomials CriticalERadicals CriticalESubstitution CriticalEPosition
open ExactFamily.FiveCornerGeometry

def dualRatio (q t u : ℝ) : ℝ :=
  (2-u)/(topRight q u*(Real.sin t+Real.cos t*u/lowerRight q u))

theorem positionA_pos {q t u : ℝ} (h : SmoothDomain q u)
    (hc : 0<Real.cos t) (hs : 0<Real.sin t) :
    0<Real.sin t+Real.cos t*u/lowerRight q u := by
  have hh := div_nonneg (mul_nonneg hc.le h.height_nonneg) h.r_pos.le
  linarith

theorem dualRatio_antitone {q t u₀ u : ℝ}
    (h₀ : SmoothDomain q u₀) (h : SmoothDomain q u) (hu : u₀≤u)
    (hc : 0<Real.cos t) (hs : 0<Real.sin t) : dualRatio q t u≤dualRatio q t u₀ := by
  have hL0 : 0<2-u₀ := by linarith [h₀.toDomain.height_lt_two h₀.radius_lt_four]
  have hL : 0<2-u := by linarith [h.toDomain.height_lt_two h.radius_lt_four]
  have hr : lowerRight q u≤lowerRight q u₀ := upper_antitone h₀.height_nonneg hu
  have hU : topRight q u₀≤topRight q u :=
    upper_antitone hL.le (show 2-u≤2-u₀ by linarith)
  have hright : u₀/lowerRight q u₀≤u/lowerRight q u := by
    apply (div_le_div_iff₀ h₀.r_pos h.r_pos).2
    exact mul_le_mul hu hr h.r_pos.le h.height_nonneg
  have hp : Real.sin t+Real.cos t*u₀/lowerRight q u₀≤
      Real.sin t+Real.cos t*u/lowerRight q u := by
    have hh := mul_le_mul_of_nonneg_left hright hc.le
    rw [mul_div_assoc,mul_div_assoc]
    linarith
  have hp₀ := positionA_pos h₀ hc hs
  have hp₁ := positionA_pos h hc hs
  have hd := mul_le_mul hU hp hp₀.le h.U_pos.le
  dsimp [dualRatio]
  apply (div_le_div_iff₀ (mul_pos h.U_pos hp₁) (mul_pos h₀.U_pos hp₀)).2
  exact mul_le_mul (show 2-u≤2-u₀ by linarith) hd
    (mul_pos h₀.U_pos hp₀).le hL0.le

theorem stationary_ratio {q t u : ℝ} (h : SmoothDomain q u)
    (hc : 0<Real.cos t) (hs : 0<Real.sin t)
    (hposition : positionHalf q (Real.cos t) (Real.sin t) u=0) :
    CriticalEFamily.c q t u/CriticalEFamily.k q t u=dualRatio q t u := by
  have hpos := CriticalEFamily.positive_weights h hc hs.le
  have hp := positionA_pos h hc hs
  have he := CriticalEFamily.stationary_ratio h hc hs.le hposition
  have hid : CriticalEFamily.k q t u*dualRatio q t u=
      CriticalEFamily.ell q t u/(Real.sin t+Real.cos t*u/lowerRight q u) := by
    dsimp [dualRatio,CriticalEFamily.ell]
    field_simp [h.U_pos.ne',hp.ne']
  rw [he,mul_div_cancel_right₀ _ hp.ne'] at hid
  exact (div_eq_iff hpos.2.2.1.ne').2 (by linarith [hid])

theorem lower_comparison_upper {q t : ℝ}
    (hq : q∈Icc (qLower:ℝ) (qUpper:ℝ)) (ht : t∈Icc (1/10:ℝ) (4/25)) :
    dualRatio q t (ev t uMinus)<51/50 := by
  have hu : ev t uMinus∈Icc (ev t (a .lower)) (ev t (b .lower)) := ⟨le_rfl,le_rfl⟩
  have hr := actual_radicals .lower hq ht hu
  let B := boxes ht hu hr
  let X := B.other.mul B.r
  let Y := B.U.mul ((B.sine.mul B.r).add (B.cosine.mul B.height))
  have hY : 0<Y.lo := by
    have hU : 0<B.U.lo := by
      have h1 : 1/2<ev t (ULo .lower) := (polynomial_coordinates .lower 1 ht).1
      rw [B.U_lo]; linarith
    have hC : 0<B.cosine.lo := by rw [B.cosine_lo]; exact (trig_bounds ht).2.2.2
    have hu0 : 0<B.height.lo := by rw [B.height_lo]; linarith [(endpoints ht .lower).1]
    dsimp [Y,PositiveInterval.mul,PositiveInterval.add]
    exact mul_pos hU (add_pos_of_nonneg_of_pos
      (mul_nonneg B.sine.lo_nonneg B.r.lo_nonneg) (mul_pos hC hu0))
  have hpoly : X.hi<(51/50)*Y.lo := by
    have hh := coefficient_positive .cK (local_parameter ht)
    change 0<ev t (cleared .cK) at hh
    have e2 : ev t (2:Polynomial ℚ)=2 := by rw [ev]; exact map_ofNat _ 2
    have hX : X.hi=(2-ev t (a .lower))*ev t (rHi .lower) := by
      simp only [X,PositiveInterval.mul]; rw [B.other_hi,B.r_hi]
    have hY' : Y.lo=ev t (ULo .lower)*(ev t sineLo*ev t (rLo .lower)+
        ev t cosineLo*ev t (a .lower)) := by
      simp only [Y,PositiveInterval.mul,PositiveInterval.add]
      rw [B.U_lo,B.sine_lo,B.r_lo,B.cosine_lo,B.height_lo]
    simp only [cleared,ev_sub,ev_mul,ev_add,ev_C,e2] at hh
    rw [hX,hY']
    push_cast at hh
    linarith
  have hh := PositiveInterval.upper_ratio X Y hY (by norm_num : (0:ℝ)≤51/50) hpoly
  have hd := hr.smoothDomain ht (by rw [ev_minus]; linarith [ht.2])
    (by norm_num [qUpper] at hq; linarith [hq.2])
  obtain ⟨hc,hs,_⟩ := tiltInterval_bounds (angle_mem ht)
  have hp := positionA_pos hd hc hs
  have hnum : 0<Real.sin t*lowerRight q (ev t uMinus)+Real.cos t*ev t uMinus := by
    have hu0 : 0≤ev t uMinus := hd.height_nonneg
    exact add_pos_of_pos_of_nonneg (mul_pos hs hd.r_pos) (mul_nonneg hc.le hu0)
  have hid : (2-ev t uMinus)*lowerRight q (ev t uMinus)/
      (topRight q (ev t uMinus)*(Real.sin t*lowerRight q (ev t uMinus)+Real.cos t*ev t uMinus))=
      dualRatio q t (ev t uMinus) := by
    have hden : topRight q (ev t uMinus)*(Real.sin t*lowerRight q (ev t uMinus)+
        Real.cos t*ev t uMinus)=topRight q (ev t uMinus)*(Real.sin t+
        Real.cos t*ev t uMinus/lowerRight q (ev t uMinus))*lowerRight q (ev t uMinus) := by
      rw [mul_assoc,add_mul,div_mul_cancel₀ _ hd.r_pos.ne']
    rw [hden,mul_div_mul_right _ _ hd.r_pos.ne']
    rfl
  rwa [hid] at hh

theorem original_ratio_upper {q t u : ℝ}
    (hq : q∈Icc (qLower:ℝ) (qUpper:ℝ)) (ht : t∈Icc (1/10:ℝ) (4/25))
    (hu : u∈Icc (ev t uMinus) (ev t uPlus))
    (hposition : positionHalf q (Real.cos t) (Real.sin t) u=0) :
    CriticalEFamily.c q t u/CriticalEFamily.k q t u<51/50 := by
  have hl : ev t uMinus∈Icc (ev t (a .lower)) (ev t (b .lower)) := ⟨le_rfl,le_rfl⟩
  have hrl := actual_radicals .lower hq ht hl
  have hru := actual_radicals .mixed hq ht hu
  have hq4 : q<4 := by norm_num [qUpper] at hq; linarith [hq.2]
  have hm0 : 0≤ev t uMinus := by rw [ev_minus]; linarith [ht.2]
  have hd₀ := hrl.smoothDomain ht hm0 hq4
  have hd := hru.smoothDomain ht (by linarith [hu.1]) hq4
  obtain ⟨hc,hs,_⟩ := tiltInterval_bounds (angle_mem ht)
  rw [stationary_ratio hd hc hs hposition]
  exact (dualRatio_antitone hd₀ hd hu.1 hc hs).trans_lt (lower_comparison_upper hq ht)

end SquaresInCircles.Eight.TableFree.CriticalERatioBounds
