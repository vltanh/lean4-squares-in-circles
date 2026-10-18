module

public import SquaresInCircles.Eight.ExactFamily.CircleConvexity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# A global curvature inequality in the tilt

Uncompiled draft.  The four circle equations and their span-three relation
imply `F_tt + 4 F > 91/45` on the complete radical domain for `q<4`.
The proof consists of two circle support inequalities and three displayed
squares.  It uses no subdivision, stationary-root localization, or assumption
that the defect is nonpositive.

The last theorems identify the displayed derivatives with the derivatives
of the actual trigonometric radical function, not independent formal jets.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

def firstTilt (q c s u : ℝ) : ℝ := s*(lowerRight q u-1)+c*u
def secondTilt (q c s u : ℝ) : ℝ := -s*lowerHeight q u-c*(lowerLeft q u-1)
def tiltFirst (q c s u : ℝ) : ℝ :=
  2*(firstComponent q c s u*firstTilt q c s u+
    secondComponent q c s u*secondTilt q c s u)
def tiltSecond (q c s u : ℝ) : ℝ :=
  2*(firstTilt q c s u^2+secondTilt q c s u^2+
    firstComponent q c s u*(2-firstComponent q c s u)+
    secondComponent q c s u*(1-secondComponent q c s u))

theorem Domain.top_circles {q u : ℝ} (hu : Domain q u) :
    topRight q u^2+(2-u)^2=q ∧
    topLeft q u^2+(2-lowerHeight q u)^2=q := by
  refine ⟨upper_circle hu.second_radicand,?_⟩
  have h := upper_circle hu.third_radicand
  dsimp [lowerHeight,topHeight]
  nlinarith

theorem top_span (q u : ℝ) : topRight q u+topLeft q u=3 := by
  dsimp [topLeft]
  ring

theorem Domain.height_sum {q u : ℝ} (hu : Domain q u) (hq : q<4) :
    4/3<u+lowerHeight q u := by
  obtain ⟨hU,hV⟩ := hu.top_circles
  have hspan := top_span q u
  have hspanSq : (topRight q u+topLeft q u)^2=9 := by rw [hspan]; norm_num
  have hv := hu.lowerHeight_pos hq
  have hUV := sq_nonneg (topRight q u-topLeft q u)
  have huv := sq_nonneg (u-lowerHeight q u)
  by_contra! hs
  nlinarith [sq_nonneg (u+lowerHeight q u-4/3)]

/-- A tangent parabola contains the upper semicircle strictly when `q<4`.
The difference is `(r-2)^2+(4-q)`, divided by four. -/
theorem circle_parabola {q x : ℝ} (hq : q<4) (hx : x^2 ≤ q) :
    upper q x<2-x^2/4 := by
  nlinarith [upper_circle hx,sq_nonneg (upper q x-2)]

theorem tilt_energy {q c s u : ℝ} (hu : Domain q u) (hunit : c^2+s^2=1) :
    firstTilt q c s u^2+secondTilt q c s u^2+
      (firstComponent q c s u-2)^2+(secondComponent q c s u-1)^2 =
      2*q+2-2*(lowerRight q u+lowerLeft q u) := by
  have hr : lowerRight q u^2+u^2=q := upper_circle hu.first_radicand
  have hw : lowerLeft q u^2+lowerHeight q u^2=q := upper_circle hu.fourth_radicand
  dsimp [firstTilt,secondTilt,firstComponent,secondComponent]
  linear_combination
    ((lowerRight q u-1)^2+u^2+lowerHeight q u^2+(lowerLeft q u-1)^2)*hunit+hr+hw

theorem tilt_curvature_identity {q c s u : ℝ}
    (hu : Domain q u) (hunit : c^2+s^2=1) :
    tiltSecond q c s u/2+2*defect q c s u =
      6*firstComponent q c s u+3*secondComponent q c s u-3-
        2*(lowerRight q u+lowerLeft q u) := by
  have h := tilt_energy hu hunit
  dsimp [tiltSecond,defect]
  nlinarith

/-- The weighted span-three Cauchy inequality supplies the otherwise
potentially negative sine coefficient. -/
theorem positive_sine_coefficient {q u : ℝ} (hq : q<4) (hu : Domain q u) :
    0<3*lowerHeight q u^2/4+6*u-3 := by
  obtain ⟨hU,hV⟩ := hu.top_circles
  have hspan := top_span q u
  have hspanSq : (topRight q u+topLeft q u)^2=9 := by rw [hspan]; norm_num
  have hCS := sq_nonneg (2*topRight q u-topLeft q u)
  nlinarith [sq_nonneg u,sq_nonneg (lowerHeight q u-1)]

theorem tilt_curvature_lower {q c s u : ℝ} (hq : q<4) (hu : Domain q u)
    (hc : 0 ≤ c) (hcu : c ≤ 1) (hs : 0 ≤ s) (hunit : c^2+s^2=1) :
    91/45<tiltSecond q c s u+4*defect q c s u := by
  let A := 3*u^2/2+3*lowerHeight q u-6
  let B := 3*lowerHeight q u^2/4+6*u-3
  let E := 6*firstComponent q c s u+3*secondComponent q c s u-3-
    2*(lowerRight q u+lowerLeft q u)
  have hr : lowerRight q u ≤ 2-u^2/4 := (circle_parabola hq hu.first_radicand).le
  have hw : lowerLeft q u ≤ 2-lowerHeight q u^2/4 :=
    (circle_parabola hq hu.fourth_radicand).le
  have hB : 0<B := positive_sine_coefficient hq hu
  have hBr := mul_nonneg (by linarith : 0 ≤ 2+6*c) (sub_nonneg.mpr hr)
  have hBw := mul_nonneg (by linarith : 0 ≤ 2+3*s) (sub_nonneg.mpr hw)
  have hE : 4+(u^2+lowerHeight q u^2)/2+c*A+s*B ≤ E := by
    dsimp [E,A,B,firstComponent,secondComponent]
    nlinarith
  have hsB := mul_nonneg hs hB.le
  have hmain : 91/90<E := by
    by_cases hA : 0 ≤ A
    · have hcA := mul_nonneg hc hA
      nlinarith [sq_nonneg u,sq_nonneg (lowerHeight q u)]
    · have hA' : A<0 := lt_of_not_ge hA
      have hcA : A ≤ c*A := by
        have hh := mul_nonneg (by linarith : 0 ≤ 1-c) (by linarith : 0 ≤ -A)
        nlinarith
      have hlow : -2+2*u^2+lowerHeight q u^2/2+3*lowerHeight q u ≤ E := by
        dsimp [A] at hcA hE
        linarith
      have hsum := hu.height_sum hq
      have hp : 0<(u+lowerHeight q u-4/3)*(4*(u+lowerHeight q u)+88/3) :=
        mul_pos (by linarith) (by linarith)
      have hsq := sq_nonneg
        (lowerHeight q u-(4*(u+lowerHeight q u)-3)/5)
      nlinarith
  have heq := tilt_curvature_identity hu hunit
  change _ = E at heq
  linarith

theorem firstComponent_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => firstComponent q (Real.cos x) (Real.sin x) u)
      (firstTilt q (Real.cos t) (Real.sin t) u) t := by
  have h := ((hasDerivAt_const t (2:ℝ)).sub
    ((Real.hasDerivAt_cos t).mul_const (lowerRight q u-1))).add
      ((Real.hasDerivAt_sin t).mul_const u)
  convert h using 1 <;> dsimp [firstComponent,firstTilt] <;> ring

theorem secondComponent_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => secondComponent q (Real.cos x) (Real.sin x) u)
      (secondTilt q (Real.cos t) (Real.sin t) u) t := by
  have h := ((hasDerivAt_const t (1:ℝ)).add
    ((Real.hasDerivAt_cos t).mul_const (lowerHeight q u))).sub
      ((Real.hasDerivAt_sin t).mul_const (lowerLeft q u-1))
  convert h using 1 <;> dsimp [secondComponent,secondTilt] <;> ring

theorem firstTilt_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => firstTilt q (Real.cos x) (Real.sin x) u)
      (2-firstComponent q (Real.cos t) (Real.sin t) u) t := by
  have h := ((Real.hasDerivAt_sin t).mul_const (lowerRight q u-1)).add
    ((Real.hasDerivAt_cos t).mul_const u)
  convert h using 1 <;> dsimp [firstTilt,firstComponent] <;> ring

theorem secondTilt_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => secondTilt q (Real.cos x) (Real.sin x) u)
      (1-secondComponent q (Real.cos t) (Real.sin t) u) t := by
  have h := (((Real.hasDerivAt_sin t).mul_const (lowerHeight q u)).neg).sub
    ((Real.hasDerivAt_cos t).mul_const (lowerLeft q u-1))
  convert h using 1 <;> dsimp [secondTilt,secondComponent] <;> ring

theorem defect_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => defect q (Real.cos x) (Real.sin x) u)
      (tiltFirst q (Real.cos t) (Real.sin t) u) t := by
  have h := (((firstComponent_angle_deriv q u t).pow 2).add
    ((secondComponent_angle_deriv q u t).pow 2)).sub (hasDerivAt_const t q)
  convert h using 1 <;> dsimp [defect,tiltFirst] <;> ring

theorem defect_angle_second_deriv (q u t : ℝ) :
    HasDerivAt (fun x => tiltFirst q (Real.cos x) (Real.sin x) u)
      (tiltSecond q (Real.cos t) (Real.sin t) u) t := by
  have h := (((firstComponent_angle_deriv q u t).mul (firstTilt_angle_deriv q u t)).add
    ((secondComponent_angle_deriv q u t).mul (secondTilt_angle_deriv q u t))).const_mul 2
  convert h using 1 <;> dsimp [tiltFirst,tiltSecond] <;> ring

/-- Whole-domain curvature for the actual trigonometric function.  The
sign assumptions include all allowed tilts `0≤t≤π/4`. -/
theorem actual_tilt_curvature {q u t : ℝ} (hq : q<4) (hu : Domain q u)
    (hc : 0 ≤ Real.cos t) (hs : 0 ≤ Real.sin t) :
    91/45 <
      deriv (fun x => deriv (fun y => defect q (Real.cos y) (Real.sin y) u) x) t+
        4*defect q (Real.cos t) (Real.sin t) u := by
  have hfirst : (fun x => deriv (fun y => defect q (Real.cos y) (Real.sin y) u) x) =
      (fun x => tiltFirst q (Real.cos x) (Real.sin x) u) := by
    funext x
    exact (defect_angle_deriv q u x).deriv
  rw [hfirst,(defect_angle_second_deriv q u t).deriv]
  apply tilt_curvature_lower hq hu hc (Real.cos_le_one t) hs
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem feasible_tilt_second_pos {q u t : ℝ} (hq : q<4) (hu : Domain q u)
    (hc : 0 ≤ Real.cos t) (hs : 0 ≤ Real.sin t)
    (hf : defect q (Real.cos t) (Real.sin t) u ≤ 0) :
    0<tiltSecond q (Real.cos t) (Real.sin t) u := by
  have h := tilt_curvature_lower hq hu hc (Real.cos_le_one t) hs
    (by nlinarith [Real.sin_sq_add_cos_sq t])
  linarith

end SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry
