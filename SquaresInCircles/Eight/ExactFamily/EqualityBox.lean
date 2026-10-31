module

public import SquaresInCircles.Eight.ExactFamily.EqualityGeometry

/-!
# Eight squares: a box of admissible parameters

The whole five-dimensional box `InBox` lies in the admissible domain
(`admissible_of_inBox`). The half-angle formulas bound the central frame
(`box_frame_bounds`), and Cauchy–Schwarz bounds the relative cosine by one.
The chosen separating projections exceed the simple width bounds 1.1 for
axis-parallel squares and 1.05 for tilted squares. The slider corners stay
inside the circle by squaring their coordinate bounds. These are ordinary
order estimates from `sharp_coordinates`; no further interval certificates are needed.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.ExactFamily
open Coordinates EqualityParameters

theorem box_frame_bounds {p : EqualityParameters} (hp : p.InBox) :
    (0.979 ≤ p.C ∧ p.C ≤ 0.981) ∧ (0.195 ≤ p.S ∧ p.S ≤ 0.201) := by
  have hw := hp.2.2.1
  have hden : 0 < 1+p.w^2 := halfAngle_den_pos p.w
  have hw2 : (0.099:ℝ)^2 ≤ p.w^2 ∧ p.w^2 ≤ (0.101:ℝ)^2 := by
    constructor <;> nlinarith only [hw.1,hw.2,sq_nonneg (p.w-0.099),sq_nonneg (p.w-0.101)]
  dsimp [C,S,halfAngleCos,halfAngleSin]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · rw [le_div_iff₀ hden]
    nlinarith only [hw2.2]
  · rw [div_le_iff₀ hden]
    nlinarith only [hw2.1]
  · rw [le_div_iff₀ hden]
    nlinarith only [hw.1,hw2.2]
  · rw [div_le_iff₀ hden]
    nlinarith only [hw.2,hw2.1]


private theorem box_width_bounds {p : EqualityParameters} (hp : p.InBox) :
    p.W₀ ≤ 11/10 ∧ p.Wₜ sharpData ≤ 21/20 := by
  obtain ⟨hC,hS⟩ := box_frame_bounds hp
  obtain ⟨_,_,_,_,_,_,_,_,hc,hcu,hs,hsu,_⟩ := sharp_coordinates
  have hcS := positive_product_bounds ⟨hc,hcu⟩ hS (by norm_num) (by norm_num)
  have hsC := positive_product_bounds ⟨hs,hsu⟩ hC (by norm_num) (by norm_num)
  have hrel : 0 ≤ sharpData.c*p.S-sharpData.s*p.C := by
    linarith only [hcS.1,hsC.2]
  have hrelU : sharpData.c*p.S-sharpData.s*p.C ≤ 1/10 := by
    linarith only [hcS.2,hsC.1]
  have hcos := cauchy_sq (sharpData.c,sharpData.s) (p.C,p.S)
  have hu : p.C^2+p.S^2=1 := halfAngle_unit p.w
  simp only [dot,normSq] at hcos
  rw [sharpData.unit,hu] at hcos
  have hcosU : sharpData.c*p.C+sharpData.s*p.S ≤ 1 :=
    (le_abs_self _).trans (abs_le_of_sq_le_sq (by simpa using hcos) (by norm_num))
  constructor
  · rw [W₀,abs_of_nonneg (by linarith only [hS.1] : 0 ≤ p.S)]
    linarith only [hC.2,hS.2]
  · rw [Wₜ,abs_of_nonneg hrel]
    linarith only [hcosU,hrelU]

/-- Direct projection estimates on the parameter box: the chosen separating axes
have widths at most 1.1 for parallel squares and 1.05 for the tilted squares. -/
theorem admissible_of_inBox {p : EqualityParameters} (hp : p.InBox) : p.Admissible sharpData := by
  obtain ⟨hC,hS⟩ := box_frame_bounds hp
  obtain ⟨hW0,hWt⟩ := box_width_bounds hp
  obtain ⟨hx₁,hx₁u,hx₂,hx₂u,hy₃,hy₃u,hx₄,hx₄u,hc,hcu,hs,hsu,hh₁,hh₁u,hh₂,hh₂u⟩ := sharp_coordinates
  have hy := sharp_y
  have hC0 : 0 ≤ p.C := by linarith only [hC.1]
  have hS0 : 0 ≤ p.S := by linarith only [hS.1]
  have hc0 : 0 ≤ sharpData.c := by linarith only [hc]
  -- The rotated frame preserves the distance of the central square's centre.
  have hnorm := frame_norm p.centralSquare p.center
  change (p.C*p.x+p.S*p.y)^2+(-p.S*p.x+p.C*p.y)^2 = p.x^2+p.y^2 at hnorm
  have hcore : p.x^2+p.y^2 < (5/12:ℝ)^2 := by
    nlinarith only [hp.1.1,hp.1.2,hp.2.1.1,hp.2.1.2]
  -- All four axis-parallel corners have a comfortable margin above 1.1.
  have hA : 11/10 ≤ (sharpData.pA).1-p.x := by
    dsimp [pA]; linarith only [hx₁,hp.1.2]
  have hBx : (0.979:ℝ)*1.017 ≤ p.C*((sharpData.pB).1-p.x) :=
    mul_le_mul hC.1 (by dsimp [pB]; linarith only [hx₂,hp.1.2]) (by norm_num) hC0
  have hBy : (0.195:ℝ)*0.578 ≤ p.S*((sharpData.pB).2-p.y) :=
    mul_le_mul hS.1 (by dsimp [pB]; linarith only [hy.1,hp.2.1.2]) (by norm_num) hS0
  have hB : 11/10 ≤ p.C*((sharpData.pB).1-p.x)+p.S*((sharpData.pB).2-p.y) := by
    linarith only [hBx,hBy]
  have hDx : (0.195:ℝ)*0.980 ≤ p.S*(p.x-(sharpData.pD).1) :=
    mul_le_mul hS.1 (by dsimp [pD,x₃]; linarith only [hx₂u,hp.1.1]) (by norm_num) hS0
  have hDy : (0.979:ℝ)*0.953 ≤ p.C*((sharpData.pD).2-p.y) :=
    mul_le_mul hC.1 (by dsimp [pD]; linarith only [hy₃,hp.2.1.2]) (by norm_num) hC0
  have hD : 11/10 ≤ -p.S*((sharpData.pD).1-p.x)+p.C*((sharpData.pD).2-p.y) := by
    linarith only [hDx,hDy]
  have hE : 11/10 ≤ -((sharpData.pE).1-p.x) := by
    dsimp [pE]; linarith only [hx₄u,hp.1.1]
  have hT : 11/10 ≤ p.z-p.y := by linarith only [hp.2.2.2.1.1,hp.2.1.2]
  -- The centre of H lies left of -0.744 and below -1.028.
  have hc' : (0.992:ℝ) ≤ sharpData.c ∧ sharpData.c ≤ 0.993 := by
    constructor <;> linarith only [hc,hcu]
  have hs' : (0.123:ℝ) ≤ sharpData.s ∧ sharpData.s ≤ 0.124 := by
    constructor <;> linarith only [hs,hsu]
  have hu : (0.867:ℝ) ≤ -sharpData.h₁-1/2 ∧ -sharpData.h₁-1/2 ≤ 0.869 := by
    constructor <;> linarith only [hh₁,hh₁u]
  have hv : (0.929:ℝ) ≤ -sharpData.h₂-1/2 ∧ -sharpData.h₂-1/2 ≤ 0.931 := by
    constructor <;> linarith only [hh₂,hh₂u]
  have hcu := positive_product_bounds hc' hu (by norm_num) (by norm_num)
  have hsv := positive_product_bounds hs' hv (by norm_num) (by norm_num)
  have hsu := positive_product_bounds hs' hu (by norm_num) (by norm_num)
  have hcv := positive_product_bounds hc' hv (by norm_num) (by norm_num)
  have hHx : (0.744:ℝ) ≤ -(sharpData.pH).1 := by
    dsimp [pH,inFrame]; nlinarith only [hcu.1,hsv.2]
  have hHy : (1.028:ℝ) ≤ -(sharpData.pH).2 := by
    dsimp [pH,inFrame]; nlinarith only [hsu.1,hcv.1]
  have hH1 : (0.979:ℝ)*0.883 ≤ p.C*(p.x-(sharpData.pH).1) :=
    mul_le_mul hC.1 (by linarith only [hHx,hp.1.1]) (by norm_num) hC0
  have hH2 : (0.195:ℝ)*1.027 ≤ p.S*(p.y-(sharpData.pH).2) :=
    mul_le_mul hS.1 (by linarith only [hHy,hp.2.1.1]) (by norm_num) hS0
  have hH : 21/20 ≤ -(p.C*((sharpData.pH).1-p.x)+p.S*((sharpData.pH).2-p.y)) := by
    linarith only [hH1,hH2]
  -- In the tilted frame the coordinate of G is h₂ + 1/2 + eta.
  have hGid : sharpData.s*((sharpData.pG p.eta).1-p.x)-
      sharpData.c*((sharpData.pG p.eta).2-p.y) =
        -(sharpData.h₂+1/2+p.eta)+sharpData.c*p.y-sharpData.s*p.x := by
    have h := sharpData.dot_f_inFrame (sharpData.h₁+3/2) (sharpData.h₂+1/2+p.eta)
    dsimp [pG,dot,Coordinates.f] at *
    linear_combination -h
  have hcy := mul_le_mul_of_nonneg_left hp.2.1.1 hc0
  have hsx := (positive_product_bounds hs' hp.1 (by norm_num) (by norm_num)).2
  have hG : 21/20 ≤ sharpData.s*((sharpData.pG p.eta).1-p.x)-
      sharpData.c*((sharpData.pG p.eta).2-p.y) := by
    rw [hGid]
    linarith only [hcy,hsx,hc'.2,hh₂u,hp.2.2.2.2.2]
  -- The two free sliders remain inside their circle constraints.
  have hq : (3.9:ℝ) < qStar := by linarith only [qStar_limits.1]
  have htopX : (sharpData.x₂-1)^2 ≤ (0.659:ℝ)^2 :=
    pow_le_pow_left₀ (by linarith only [hx₂]) (by linarith only [hx₂u]) 2
  have htopY : (p.z+1/2)^2 ≤ (1.851:ℝ)^2 :=
    pow_le_pow_left₀ (by linarith only [hp.2.2.2.1.1]) (by linarith only [hp.2.2.2.1.2]) 2
  have htiltX : (sharpData.h₁+2)^2 ≤ (0.633:ℝ)^2 :=
    pow_le_pow_left₀ (by linarith only [hh₁]) (by linarith only [hh₁u]) 2
  have htiltY : (sharpData.h₂+p.eta)^2 ≤ (1.752:ℝ)^2 := by
    have h := pow_le_pow_left₀
      (by linarith only [hh₂u,hp.2.2.2.2.2] : 0 ≤ -(sharpData.h₂+p.eta))
      (by linarith only [hh₂,hp.2.2.2.2.1] : -(sharpData.h₂+p.eta) ≤ 1.752) 2
    simpa only [neg_sq] using h
  have hsqrt := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hsqrt0 := Real.sqrt_nonneg (2:ℝ)
  refine {
    frame_lower := by nlinarith only [hp.2.2.1.1,hsqrt,hsqrt0]
    frame_upper := by nlinarith only [hp.2.2.1.2,hsqrt,hsqrt0]
    top_lower := by linarith only [hp.2.2.2.1.1]
    top_upper := ?_
    tilted_lower := ?_
    tilted_upper := by dsimp [etaMax]; linarith only [hh₂u,hp.2.2.2.2.2]
    core_first := abs_lt_of_sq_lt_sq (by nlinarith only [hnorm,hcore,sq_nonneg (-p.S*p.x+p.C*p.y)]) (by norm_num)
    core_second := abs_lt_of_sq_lt_sq (by nlinarith only [hnorm,hcore,sq_nonneg (p.C*p.x+p.S*p.y)]) (by norm_num)
    A_sep := hW0.trans (hA.trans ((le_abs_self _).trans ((le_max_left _ _).trans (le_max_left _ _))))
    B_sep := hW0.trans (hB.trans ((le_abs_self _).trans ((le_max_left _ _).trans (le_max_right _ _))))
    D_sep := hW0.trans (hD.trans ((le_abs_self _).trans ((le_max_right _ _).trans (le_max_right _ _))))
    E_sep := hW0.trans (hE.trans ((neg_le_abs _).trans ((le_max_left _ _).trans (le_max_left _ _))))
    T_sep := hW0.trans (hT.trans ((le_abs_self _).trans ((le_max_right _ _).trans (le_max_left _ _))))
    H_sep := hWt.trans (hH.trans ((neg_le_abs _).trans ((le_max_left _ _).trans (le_max_right _ _))))
    G_sep := ?_ }
  · change p.z ≤ Real.sqrt (qStar-(sharpData.x₂-1)^2)-1/2
    have h := Real.le_sqrt_of_sq_le
      (by nlinarith only [hq,htopX,htopY] : (p.z+1/2)^2 ≤ qStar-(sharpData.x₂-1)^2)
    linarith only [h]
  · change -sharpData.h₂-Real.sqrt (qStar-(sharpData.h₁+2)^2) ≤ p.eta
    have h := Real.le_sqrt_of_sq_le
      (by nlinarith only [hq,htiltX,htiltY] : (-(sharpData.h₂+p.eta))^2 ≤ qStar-(sharpData.h₁+2)^2)
    linarith only [h]
  · apply hWt.trans (hG.trans ?_)
    have hneg := neg_le_abs (-sharpData.s*((sharpData.pG p.eta).1-p.x)+
      sharpData.c*((sharpData.pG p.eta).2-p.y))
    dsimp [Mₜ,sub,center]
    apply le_trans ?_ ((le_max_right _ _).trans (le_max_left _ _))
    linarith only [hneg]

end SquaresInCircles.Eight.ExactFamily
