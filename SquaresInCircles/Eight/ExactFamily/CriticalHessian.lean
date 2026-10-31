module

public import SquaresInCircles.Eight.ExactFamily.Convexity

/-!
# Eight squares: position curvature and the Hessian at a critical point

On the strip `(79/40)² ≤ q ≤ 9789/2500`, `87/100 ≤ u ≤ 1` (`CriticalStrip`) the circle
equations bound the radicals of `Convexity.lean` (`CriticalStrip.bounds`). Rational support lines
of the circles give `p > 3/2 - u` for the slope `p = -v'` (`slope_affine_lower`) and
`w - 1 - 6u/7 > 3/70` (`left_support_lower`), and the bounds give `Z > (13/10)(1 + p)` for the
curvature ratio `Z = q/((2-u)U²) + p q/(Y V²)` (`curvatureRatio_lower`) and `q/r³ < 4/5`
(`right_curvature_upper`).

`StripCritical` is a point of the strip with `0 ≤ s/c ≤ 1/5` where both partial derivatives of
the defect vanish; the defect may have either sign. There the tilt and position derivatives of
`(k₁, k₂)` are proportional, `k_t = κ k_u` (`StripCritical.derivative_proportionality`), and the
determinant of the Hessian is `4 k₁² (A (σ κ² - 2 τ κ + ν) + σ ν - τ²)`
(`StripCritical.normalized_hessian_identity`), where `A = |k_u|²/k₁` and `σ`, `τ`, `ν` are the
position, mixed and tilt normal terms divided by `k₁`. The circle bounds give `A > 17/50`,
`κ > 7/5`, `0 < τ < 7/8`, `ν > 9/100`, `κ σ > 3`, `σ > 27/16`, hence
`det > (237/5000) k₁² > 0` (`StripCritical.hessian_reserve`).

On `SmoothDomain` (the radical domain with `q < 4` and the four radicals positive) the nested
radicals are differentiable, `p' = -p Z` (`slopeRatio_deriv`), and the position derivative
`2 positionHalf` has position derivative `positionSecond` (`position_second_deriv`) and tilt
derivative `mixedSecond` (`mixed_angle_deriv`). The position entry is positive, since `k₁` and
`k₂` are positive and have the positive second position derivatives `rightSecond` and
`leftSecond`, which come from the curvature of the circles (`SmoothDomain.positionSecond_pos`). A
stationary chain is a critical point of the strip (`stationary_isStripCritical`). `Envelope.lean`
uses the Hessian bound for the second derivative of the envelope in the tilt. On the smaller
local rectangle, endpoint frame projections and a cancellation in the chain curvature give
bounds on the position and tilt derivatives (`local_hessian_bounds`). Shearing the quadratic
form by `3/5` makes its mixed term small, and proves positivity of the Hessian shifted by
`1/4` in the half-angle coordinates (`local_halfAngle_hessian_pos`), without a grid.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

/-! ### The strip `87/100 ≤ u ≤ 1` -/

/-- The strip `(79/40)² ≤ q ≤ 9789/2500`, `87/100 ≤ u ≤ 1`. -/
structure CriticalStrip (q u : ℝ) : Prop where
  q_lower : (79/40:ℝ)^2 ≤ q
  q_upper : q ≤ 9789/2500
  u_lower : 87/100 ≤ u
  u_upper : u ≤ 1

/-- Rational bounds on the radicals and on `p` throughout the strip. -/
structure StripBounds (q u : ℝ) : Prop where
  domain : Domain q u
  r_lower : 17/10<lowerRight q u
  r_upper : lowerRight q u<16/9
  U_lower : 1619/1000<topRight q u
  V_lower : 1292/1000<topLeft q u
  V_upper : topLeft q u<1381/1000
  Y_lower : 1411/1000<topHeight q u
  Y_upper : topHeight q u<3/2
  v_lower : 1/2<lowerHeight q u
  v_upper : lowerHeight q u<589/1000
  w_lower : 1885/1000<lowerLeft q u
  w_upper : lowerLeft q u<48/25
  p_lower : 1/2<slopeRatio q u

/-- The circle equations give the bounds of `StripBounds`. -/
theorem CriticalStrip.bounds {q u : ℝ} (h : CriticalStrip q u) : StripBounds q u := by
  have hu : 0 ≤ u := by linarith [h.u_lower]
  have hA : 1 ≤ 2-u ∧ 2-u ≤ 113/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hr : 17/10<lowerRight q u ∧ lowerRight q u<16/9 := by
    apply sqrt_between (by norm_num)
    · have hs := square_mono_nonneg hu h.u_upper
      nlinarith [h.q_lower]
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 87/100) h.u_lower
      nlinarith [h.q_upper]
  have hU : 1619/1000<topRight q u ∧ topRight q u<1708/1000 := by
    apply sqrt_between (by norm_num)
    · have hs := square_mono_nonneg (by linarith : 0 ≤ 2-u) hA.2
      nlinarith [h.q_lower]
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 1) hA.1
      nlinarith [h.q_upper]
  have hV : 1292/1000<topLeft q u ∧ topLeft q u<1381/1000 := by
    dsimp [topLeft]
    constructor <;> linarith [hU.1,hU.2]
  have hY : 1411/1000<topHeight q u ∧ topHeight q u<3/2 := by
    apply sqrt_between (by norm_num)
    · have hs := square_mono_nonneg (by linarith : 0 ≤ topLeft q u) hV.2.le
      nlinarith [h.q_lower]
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 1292/1000) hV.1.le
      nlinarith [h.q_upper]
  have hv : 1/2<lowerHeight q u ∧ lowerHeight q u<589/1000 := by
    dsimp [lowerHeight]
    constructor <;> linarith [hY.1,hY.2]
  have hw : 1885/1000<lowerLeft q u ∧ lowerLeft q u<48/25 := by
    apply sqrt_between (by norm_num)
    · have hs := square_mono_nonneg (by linarith : 0 ≤ lowerHeight q u) hv.2.le
      nlinarith [h.q_lower]
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 1/2) hv.1.le
      nlinarith [h.q_upper]
  have hUp : 0<topRight q u := by linarith [hU.1]
  have hYp : 0<topHeight q u := by linarith [hY.1]
  have hprodU : topRight q u*topHeight q u ≤ (1708/1000:ℝ)*(3/2) :=
    mul_le_mul hU.2.le hY.2.le hYp.le (by norm_num)
  have hnumL : (1292/1000:ℝ) ≤ (2-u)*topLeft q u := by
    have hh := mul_le_mul hA.1 hV.1.le (by norm_num : (0:ℝ) ≤ 1292/1000)
      (by linarith : 0 ≤ 2-u)
    nlinarith
  have hp : 1/2<slopeRatio q u := by
    dsimp [slopeRatio]
    rw [lt_div_iff₀ (mul_pos hUp hYp)]
    nlinarith
  exact ⟨domain_of_pos hu (by linarith [hr.1]) hUp hYp (by linarith [hw.1]),hr.1,hr.2,hU.1,
    hV.1,hV.2,hY.1,hY.2,hv.1,hv.2,hw.1,hw.2,hp⟩

/-- Two rational upper support lines of the top circles. -/
theorem top_support_upper {q u : ℝ} (h : CriticalStrip q u) :
    topRight q u<141/125+(29/50)*u ∧ topHeight q u<1+u/2 := by
  have hb := h.bounds
  have hUcircle : topRight q u^2+(2-u)^2=q := upper_circle hb.domain.second_radicand
  have hYcircle : topHeight q u^2+topLeft q u^2=q := upper_circle hb.domain.third_radicand
  let L : ℝ := 141/125+(29/50)*u
  let V : ℝ := 3-L
  have ht : 0 ≤ 1-u ∧ 1-u ≤ 13/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hL : 0<L := by dsimp [L]; linarith [h.u_lower]
  have hgap : q<L^2+(2-u)^2 := by
    have he : L^2+(2-u)^2-9789/2500 =
        26/15625+(117/6250)*(1-u)+(3341/2500)*(1-u)^2 := by dsimp [L]; ring
    nlinarith [h.q_upper,sq_nonneg (1-u)]
  have hUl : topRight q u<L := by
    by_contra! hh
    have hs := square_mono_nonneg hL.le hh
    nlinarith
  have hV : 0<V := by dsimp [V,L]; linarith [h.u_upper]
  have hVl : V<topLeft q u := by dsimp [V,topLeft]; linarith
  have hV2 := square_strict_mono_nonneg hV.le hVl
  have hYgap : q<(1+u/2)^2+V^2 := by
    have he : (1+u/2)^2+V^2-9789/2500 =
        229/62500-(4/3125)*(1-u)+(733/1250)*(1-u)^2 := by dsimp [V,L]; ring
    nlinarith [h.q_upper,sq_nonneg (1-u)]
  have hYl : topHeight q u<1+u/2 := by
    by_contra! hh
    have hs := square_mono_nonneg (by linarith [h.u_lower] : 0 ≤ 1+u/2) hh
    nlinarith
  exact ⟨hUl,hYl⟩

/-- `p > 3/2 - u`: after the support lines of `top_support_upper`, the difference is a cubic in
`1 - u` with positive terms. -/
theorem slope_affine_lower {q u : ℝ} (h : CriticalStrip q u) :
    3/2-u<slopeRatio q u := by
  have hb := h.bounds
  obtain ⟨hU,hY⟩ := top_support_upper h
  let L : ℝ := 141/125+(29/50)*u
  let V : ℝ := 3-L
  let Y : ℝ := 1+u/2
  have hUp : 0<topRight q u := by linarith [hb.U_lower]
  have hYp : 0<topHeight q u := by linarith [hb.Y_lower]
  have hLp : 0<L := by dsimp [L]; linarith [h.u_lower]
  have hYp' : 0<Y := by dsimp [Y]; linarith [h.u_lower]
  have hprod : topRight q u*topHeight q u ≤ L*Y :=
    mul_le_mul hU.le hY.le hYp.le hLp.le
  have hV : V<topLeft q u := by dsimp [V,L,topLeft]; linarith
  have hn := mul_le_mul_of_nonneg_left hV.le (by linarith [h.u_upper] : 0 ≤ 2-u)
  have hd := mul_le_mul_of_nonneg_left hprod (by linarith [h.u_upper] : 0 ≤ 3/2-u)
  have ht : 0 ≤ 1-u ∧ 1-u ≤ 13/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hrem : 0 ≤ (1-u)^2*(2159/1000-(29/100)*(1-u)) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hpoly : (3/2-u)*L*Y<(2-u)*V := by
    have he : (2-u)*V-(3/2-u)*L*Y =
        11/1000+(43/250)*(1-u)+(1-u)^2*(2159/1000-(29/100)*(1-u)) := by
      dsimp [V,L,Y]
      ring
    nlinarith
  dsimp [slopeRatio]
  rw [lt_div_iff₀ (mul_pos hUp hYp)]
  nlinarith

/-- `u (1 + p) > 141/100` on the strip. -/
theorem position_slope_product_lower {q u : ℝ} (h : CriticalStrip q u) :
    141/100<u*(1+slopeRatio q u) := by
  have hp := slope_affine_lower h
  have hu : 0<u := by linarith [h.u_lower]
  have hh := mul_pos hu (sub_pos.mpr hp)
  have hc := mul_nonneg (sub_nonneg.mpr h.u_lower)
    (by linarith [h.u_upper] : 0 ≤ 163/100-u)
  nlinarith

/-- Two rational lower support lines: `U > 9/10 + 4u/5` and `v < 38/25 - u`. -/
theorem top_support_lower {q u : ℝ} (h : CriticalStrip q u) :
    9/10+(4/5)*u<topRight q u ∧ lowerHeight q u<38/25-u := by
  have hb := h.bounds
  have hUcircle : topRight q u^2+(2-u)^2=q := upper_circle hb.domain.second_radicand
  have hYcircle : topHeight q u^2+topLeft q u^2=q := upper_circle hb.domain.third_radicand
  have ht : 0 ≤ 1-u ∧ 1-u ≤ 13/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hpos : 0 ≤ (1-u)*(18/25-(41/25)*(1-u)) := mul_nonneg ht.1 (by linarith)
  have hUl : 9/10+(4/5)*u<topRight q u := by
    have hg : (9/10+(4/5)*u)^2<topRight q u^2 := by
      nlinarith [h.q_lower]
    by_contra! hh
    have hs := square_mono_nonneg (x:=topRight q u) (upper_nonneg _ _) hh
    nlinarith
  have hYsq : (u+12/25)^2<topHeight q u^2 := by
    dsimp [topLeft] at hYcircle
    nlinarith [h.u_upper]
  have hY : u+12/25<topHeight q u := by
    by_contra! hh
    have hs := square_mono_nonneg (x:=topHeight q u) (upper_nonneg _ _) hh
    nlinarith
  refine ⟨hUl,?_⟩
  dsimp [lowerHeight]
  linarith

/-- A lower support line of the left circle: `w > 73/70 + 6u/7`. -/
theorem left_support_lower {q u : ℝ} (h : CriticalStrip q u) :
    3/70<lowerLeft q u-1-(6/7)*u := by
  have hb := h.bounds
  have hv := (top_support_lower h).2
  have hvp : 0 ≤ lowerHeight q u := by linarith [hb.v_lower]
  have hv2 := square_mono_nonneg hvp hv.le
  have hwcircle : lowerLeft q u^2+lowerHeight q u^2=q :=
    upper_circle hb.domain.fourth_radicand
  have ht : 0 ≤ 1-u ∧ 1-u ≤ 13/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hn := mul_nonneg ht.1 (by linarith : 0 ≤ 388/175-(85/49)*(1-u))
  have hw2 : (73/70+(6/7)*u)^2<lowerLeft q u^2 := by
    nlinarith [h.q_lower]
  have hw : 73/70+(6/7)*u<lowerLeft q u := by
    by_contra! hh
    have hs := square_mono_nonneg (x:=lowerLeft q u) (upper_nonneg _ _) hh
    nlinarith
  linarith

/-- The curvature ratio `Z = q/((2-u)U²) + p q/(Y V²)`, with `p' = -p Z` (`slopeRatio_deriv`). -/
def curvatureRatio (q u : ℝ) : ℝ :=
  q/((2-u)*topRight q u^2)+slopeRatio q u*q/(topHeight q u*topLeft q u^2)

/-- `Z > (13/10)(1 + p)`: `q/((2-u)U²)` and `q/(Y V²)` both exceed `13/10`. -/
theorem curvatureRatio_lower {q u : ℝ} (h : CriticalStrip q u) :
    (13/10)*(1+slopeRatio q u)<curvatureRatio q u := by
  have hb := h.bounds
  have hA : 1 ≤ 2-u ∧ 2-u ≤ 113/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hAs := square_mono_nonneg (by linarith : 0 ≤ 2-u) hA.2
  have hAc : 0 ≤ q-((2-u)^2+(113/100)*(2-u)+(113/100)^2) := by
    nlinarith [h.q_lower]
  have hprod := mul_nonneg (by linarith : 0 ≤ 113/100-(2-u)) hAc
  have hUcircle : topRight q u^2+(2-u)^2=q := upper_circle hb.domain.second_radicand
  have hfirstNum : (13/10)*((2-u)*topRight q u^2)<q := by
    have he := congrArg (fun x : ℝ => (2-u)*x) hUcircle
    nlinarith [h.q_upper]
  have hUp : 0<topRight q u := by linarith [hb.U_lower]
  have hYp : 0<topHeight q u := by linarith [hb.Y_lower]
  have hVp : 0<topLeft q u := by linarith [hb.V_lower]
  have hfirst : 13/10<q/((2-u)*topRight q u^2) := by
    rw [lt_div_iff₀ (mul_pos (by linarith) (sq_pos_of_pos hUp))]
    exact hfirstNum
  have hVs := square_mono_nonneg hVp.le hb.V_upper.le
  have hden := mul_le_mul hb.Y_upper.le hVs (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 3/2)
  have hsecond : 13/10<q/(topHeight q u*topLeft q u^2) := by
    rw [lt_div_iff₀ (mul_pos hYp (sq_pos_of_pos hVp))]
    nlinarith [h.q_lower]
  have hp : 0<slopeRatio q u := by linarith [hb.p_lower]
  have hh := mul_lt_mul_of_pos_left hsecond hp
  calc
    _ < q/((2-u)*topRight q u^2)+slopeRatio q u*(q/(topHeight q u*topLeft q u^2)) := by
      nlinarith
    _ = curvatureRatio q u := by dsimp [curvatureRatio]; ring

/-- `q/r³ < 4/5` on the strip. -/
theorem right_curvature_upper {q u : ℝ} (h : CriticalStrip q u) :
    q/lowerRight q u^3<4/5 := by
  have hb := h.bounds
  have hr : 0<lowerRight q u := by linarith [hb.r_lower]
  have hu : 0 ≤ u := by linarith [h.u_lower]
  have hus := square_mono_nonneg hu h.u_upper
  have hrs := square_strict_mono_nonneg (by norm_num : (0:ℝ) ≤ 17/10) hb.r_lower
  have hm := mul_nonneg (by linarith [hb.r_lower] : 0 ≤ (4/5)*lowerRight q u-34/25)
    (sq_nonneg (lowerRight q u))
  have hc : lowerRight q u^2+u^2=q := upper_circle hb.domain.first_radicand
  rw [div_lt_iff₀ (pow_pos hr 3)]
  nlinarith

/-! ### The Hessian at a critical point -/

/-- `s + c u/r`, the position derivative of `k₁`. -/
def positionA (q c s u : ℝ) : ℝ := s+c*u/lowerRight q u
/-- `c + s v/w`; the position derivative of `k₂` is `-p (c + s v/w)`. -/
def positionB (q c s u : ℝ) : ℝ := c+s*lowerHeight q u/lowerLeft q u
/-- Minus the position derivative of `k₂`. -/
def positionb (q c s u : ℝ) : ℝ := slopeRatio q u*positionB q c s u
/-- `c q/r³`, the second position derivative of `k₁`. -/
def rightSecond (q c u : ℝ) : ℝ := c*q/lowerRight q u^3
/-- The second position derivative of `k₂`. -/
def leftSecond (q c s u : ℝ) : ℝ :=
  slopeRatio q u*curvatureRatio q u*positionB q c s u+
    s*q*slopeRatio q u^2/lowerLeft q u^3
/-- `|k_u|²`, the squared norm of the position derivative of `(k₁, k₂)`. -/
def positionNorm (q c s u : ℝ) : ℝ := positionA q c s u^2+positionb q c s u^2
/-- The position normal term `k₁ k₁'' + k₂ k₂''`. -/
def positionNormal (q c s u : ℝ) : ℝ :=
  firstComponent q c s u*rightSecond q c u+secondComponent q c s u*leftSecond q c s u
/-- The mixed normal term: `(k₁, k₂)` against the tilt derivative of its position derivative. -/
def mixedNormal (q c s u : ℝ) : ℝ :=
  firstComponent q c s u*(c-s*u/lowerRight q u)+
    secondComponent q c s u*slopeRatio q u*(s-c*lowerHeight q u/lowerLeft q u)
/-- The tilt normal term `k₁ (2 - k₁) + k₂ (1 - k₂)`: `(k₁, k₂)` against its second tilt
derivative. -/
def tiltNormal (q c s u : ℝ) : ℝ :=
  2*firstComponent q c s u+secondComponent q c s u-
    (firstComponent q c s u^2+secondComponent q c s u^2)
/-- The second position derivative of the defect, `2 (|k_u|² + positionNormal)`. -/
def positionSecond (q c s u : ℝ) : ℝ :=
  2*(positionNorm q c s u+positionNormal q c s u)
/-- The mixed second derivative of the defect in the tilt and the position. -/
def mixedSecond (q c s u : ℝ) : ℝ :=
  2*(positionA q c s u*firstTilt q c s u-positionb q c s u*secondTilt q c s u+
    mixedNormal q c s u)
/-- `κ`, the tilt derivative of `k₁` divided by its position derivative. -/
def tangentRatio (q c s u : ℝ) : ℝ := firstTilt q c s u/positionA q c s u
/-- `σ`, the position normal term divided by `k₁`. -/
def normalizedPosition (q c s u : ℝ) : ℝ := positionNormal q c s u/firstComponent q c s u
/-- `τ`, the mixed normal term divided by `k₁`. -/
def normalizedMixed (q c s u : ℝ) : ℝ := mixedNormal q c s u/firstComponent q c s u
/-- `ν`, the tilt normal term divided by `k₁`. -/
def normalizedTilt (q c s u : ℝ) : ℝ := tiltNormal q c s u/firstComponent q c s u
/-- The determinant of the Hessian of the defect in the tilt and the position. -/
def hessianDeterminant (q c s u : ℝ) : ℝ :=
  positionSecond q c s u*tiltSecond q c s u-mixedSecond q c s u^2

/-- A critical point of the defect in the strip, at a tilt with `0 ≤ s/c ≤ 1/5`; the defect may
have either sign. -/
structure StripCritical (q c s u : ℝ) : Prop where
  strip : CriticalStrip q u
  cosine_pos : 0<c
  sine_nonneg : 0 ≤ s
  unit : c^2+s^2=1
  tilt_upper : s/c ≤ 1/5
  position_zero : positionHalf q c s u=0
  tilt_zero : tiltFirst q c s u=0

/-- A tilt with `0 ≤ s/c ≤ 1/5` has `c > 49/50` and `5 s ≤ c`. -/
theorem small_tilt_bounds {c s : ℝ} (hc : 0<c) (hs : 0 ≤ s)
    (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5) :
    49/50<c ∧ c ≤ 1 ∧ s ≤ 1 ∧ 5*s ≤ c := by
  have ht' : s ≤ (1/5)*c := (div_le_iff₀ hc).mp ht
  have hs2 := square_mono_nonneg hs ht'
  have hcL : 49/50<c := by
    by_contra! hh
    have hsq := square_mono_nonneg hc.le hh
    nlinarith
  obtain ⟨hcU,hsU⟩ := unit_le_one hunit
  exact ⟨hcL,hcU,hsU,by linarith⟩

theorem CriticalStrip.quotient_bounds {q u : ℝ} (h : CriticalStrip q u) :
    783/1600<u/lowerRight q u ∧ u/lowerRight q u<1 ∧
    25/96<lowerHeight q u/lowerLeft q u ∧ lowerHeight q u/lowerLeft q u<1 := by
  have hb := h.bounds
  have hr : 0<lowerRight q u := by linarith [hb.r_lower]
  have hw : 0<lowerLeft q u := by linarith [hb.w_lower]
  refine ⟨?_,?_,?_,?_⟩
  · rw [lt_div_iff₀ hr]
    nlinarith [hb.r_upper,h.u_lower]
  · rw [div_lt_iff₀ hr]
    linarith [hb.r_lower,h.u_upper]
  · rw [lt_div_iff₀ hw]
    nlinarith [hb.v_lower,hb.w_upper]
  · rw [div_lt_iff₀ hw]
    linarith [hb.v_upper,hb.w_lower]

theorem positionB_lower {q c s u : ℝ} (h : CriticalStrip q u)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5) :
    1 ≤ positionB q c s u := by
  obtain ⟨_,_,hy,_⟩ := h.quotient_bounds
  obtain ⟨_,_,_,hst⟩ := small_tilt_bounds hc hs hunit ht
  let y : ℝ := lowerHeight q u/lowerLeft q u
  have hyp : 0 ≤ y := by dsimp [y]; linarith
  have hcy := mul_le_mul_of_nonneg_left (show 1/4 ≤ y by dsimp [y]; linarith) hc.le
  have hprod := mul_nonneg hs (by nlinarith : 0 ≤ 2*c*y-s)
  have hnon : 0 ≤ c+s*y := add_nonneg hc.le (mul_nonneg hs hyp)
  have hsq : 1 ≤ (c+s*y)^2 := by nlinarith [sq_nonneg (s*y)]
  have hB : 1 ≤ c+s*y := by
    by_contra! hh
    have hbad := square_strict_mono_nonneg hnon hh
    nlinarith
  simpa [positionB,y,div_eq_mul_inv,mul_assoc] using hB

theorem StripCritical.components_pos {q c s u : ℝ} (h : StripCritical q c s u) :
    0<firstComponent q c s u ∧ 0<secondComponent q c s u := by
  obtain ⟨hc,hs⟩ := unit_le_one h.unit
  exact FiveCornerGeometry.components_pos (by linarith [h.strip.q_upper]) h.strip.bounds.domain
    h.cosine_pos hc h.sine_nonneg hs

theorem StripCritical.position_derivative_zero {q c s u : ℝ} (h : StripCritical q c s u) :
    HasDerivAt (defect q c s) 0 u := by
  have hb := h.strip.bounds
  have hd := position_deriv (q:=q) (c:=c) (s:=s) (u:=u)
    (by linarith [hb.r_lower]) (by linarith [hb.U_lower])
    (by linarith [hb.Y_lower]) (by linarith [hb.w_lower])
  simpa [h.position_zero] using hd

theorem StripCritical.norm_lt_four {q c s u : ℝ} (h : StripCritical q c s u) :
    firstComponent q c s u^2+secondComponent q c s u^2<4 :=
  position_stationary_norm_lt_four h.strip.q_lower (by linarith [h.strip.q_upper])
    h.cosine_pos h.sine_nonneg h.tilt_upper h.unit h.strip.bounds.domain h.position_derivative_zero

theorem StripCritical.position_equation {q c s u : ℝ} (h : StripCritical q c s u) :
    firstComponent q c s u*positionA q c s u=
      secondComponent q c s u*positionb q c s u := by
  have hp := h.position_zero
  dsimp [positionHalf,positionA,positionb,positionB] at *
  nlinarith

theorem StripCritical.tilt_equation {q c s u : ℝ} (h : StripCritical q c s u) :
    firstComponent q c s u*firstTilt q c s u=
      secondComponent q c s u*(-secondTilt q c s u) := by
  have hp := h.tilt_zero
  dsimp [tiltFirst] at hp
  nlinarith

theorem StripCritical.positionA_pos {q c s u : ℝ} (h : StripCritical q c s u) :
    0<positionA q c s u := by
  have hu : 0<u := by linarith [h.strip.u_lower]
  have hr : 0<lowerRight q u := by linarith [h.strip.bounds.r_lower]
  have hm := div_pos (mul_pos h.cosine_pos hu) hr
  dsimp [positionA]
  linarith [h.sine_nonneg]

theorem StripCritical.firstTilt_pos {q c s u : ℝ} (h : StripCritical q c s u) :
    0<firstTilt q c s u := by
  have hp := mul_pos h.cosine_pos (by linarith [h.strip.u_lower] : 0<u)
  have hn := mul_nonneg h.sine_nonneg (by linarith [h.strip.bounds.r_lower] : 0 ≤ lowerRight q u-1)
  dsimp [firstTilt]
  linarith

theorem secondComponent_gt_one {q c s u : ℝ} (h : CriticalStrip q u)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5) :
    1<secondComponent q c s u := by
  have hb := h.bounds
  obtain ⟨_,_,_,hst⟩ := small_tilt_bounds hc hs hunit ht
  have hv := mul_lt_mul_of_pos_left hb.v_lower hc
  have hw := mul_le_mul_of_nonneg_left (by linarith [hb.w_upper] : lowerLeft q u-1 ≤ 23/25) hs
  dsimp [secondComponent]
  nlinarith

theorem tilt_ratio_lower {q c s u : ℝ} (h : CriticalStrip q u)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5) :
    (6/7)*firstTilt q c s u< -secondTilt q c s u := by
  have hb := h.bounds
  obtain ⟨_,_,_,hst⟩ := small_tilt_bounds hc hs hunit ht
  have hw := mul_lt_mul_of_pos_left (left_support_lower h) hc
  have hv : -(1/6)<lowerHeight q u-(6/7)*(lowerRight q u-1) := by
    linarith [hb.v_lower,hb.r_upper]
  have hv' := mul_le_mul_of_nonneg_left hv.le hs
  dsimp [firstTilt,secondTilt]
  nlinarith

/-- At a critical point `k₁/2 < k₂ < 7 k₁/6`. -/
theorem StripCritical.component_ratio {q c s u : ℝ} (h : StripCritical q c s u) :
    (1/2)*firstComponent q c s u<secondComponent q c s u ∧
      secondComponent q c s u<(7/6)*firstComponent q c s u := by
  obtain ⟨hk₁,hk₂⟩ := h.components_pos
  have hnorm := h.norm_lt_four
  have hk₁u : firstComponent q c s u<2 := by nlinarith [sq_nonneg (secondComponent q c s u)]
  have hk₂l := secondComponent_gt_one h.strip h.cosine_pos h.sine_nonneg h.unit h.tilt_upper
  have he := h.tilt_equation
  have hr := tilt_ratio_lower h.strip h.cosine_pos h.sine_nonneg h.unit h.tilt_upper
  have hprod := mul_pos hk₂ (sub_pos.mpr hr)
  have hd := h.firstTilt_pos
  refine ⟨by linarith,?_⟩
  by_contra! hh
  have hp := mul_nonneg (by linarith : 0 ≤ (6/7)*secondComponent q c s u-firstComponent q c s u) hd.le
  nlinarith

/-- In the cone `x/2 < y < 7x/6` inside the circle `x² + y² < 4`,
`2x + y - (x² + y²) > 9x/100`. -/
theorem normal_reserve {x y : ℝ} (hx : 0<x) (hy : 0<y)
    (hn : x^2+y^2<4) (hlo : x/2<y) (hhi : y<(7/6)*x) :
    (9/100)*x<2*x+y-(x^2+y^2) := by
  have hcone := mul_nonneg (by linarith : 0 ≤ y-x/2) (by linarith : 0 ≤ (7/6)*x-y)
  have hside := mul_nonneg hx.le (by linarith : 0 ≤ (7/6)*x-y)
  have hsqx := sq_pos_of_pos hx
  have hquad : 4*(x^2+y^2)<((191/100)*x+y)^2 := by nlinarith
  have hnorm : 0<x^2+y^2 := by nlinarith [sq_nonneg y]
  have hbound := mul_lt_mul_of_pos_right hn hnorm
  by_contra! hh
  have hL : 0 ≤ (191/100)*x+y := by positivity
  have hs := square_mono_nonneg hL (show (191/100)*x+y ≤ x^2+y^2 by linarith)
  nlinarith

/-- `ν > 9/100`. -/
theorem StripCritical.normalizedTilt_lower {q c s u : ℝ} (h : StripCritical q c s u) :
    9/100<normalizedTilt q c s u := by
  obtain ⟨hk₁,hk₂⟩ := h.components_pos
  obtain ⟨hl,hu⟩ := h.component_ratio
  have hn := normal_reserve hk₁ hk₂ h.norm_lt_four (by linarith) hu
  dsimp [normalizedTilt,tiltNormal]
  rw [lt_div_iff₀ hk₁]
  exact hn

theorem mixed_cancellation (k₁ k₂ p c s x y : ℝ) (hunit : c^2+s^2=1)
    (hpos : k₁*(s+c*x)=k₂*p*(c+s*y)) :
    (k₁*(c-s*x)+k₂*p*(s-c*y))*(c+s*y)=k₁*(1-x*y) := by
  linear_combination -(s-c*y)*hpos+k₁*(1-x*y)*hunit

theorem StripCritical.normalizedMixed_formula {q c s u : ℝ} (h : StripCritical q c s u) :
    normalizedMixed q c s u=
      (1-(u/lowerRight q u)*(lowerHeight q u/lowerLeft q u))/positionB q c s u := by
  have hk₁ := h.components_pos.1
  have hB := positionB_lower h.strip h.cosine_pos h.sine_nonneg h.unit h.tilt_upper
  have hp := h.position_equation
  have he := mixed_cancellation (firstComponent q c s u) (secondComponent q c s u)
    (slopeRatio q u) c s (u/lowerRight q u) (lowerHeight q u/lowerLeft q u) h.unit
    (by simpa [positionA,positionb,positionB,div_eq_mul_inv,mul_assoc] using hp)
  have he' : mixedNormal q c s u*positionB q c s u=
      firstComponent q c s u*(1-(u/lowerRight q u)*(lowerHeight q u/lowerLeft q u)) := by
    simpa [mixedNormal,positionB,div_eq_mul_inv,mul_assoc] using he
  dsimp only [normalizedMixed]
  apply (div_eq_div_iff (ne_of_gt hk₁) (ne_of_gt (show 0<positionB q c s u by linarith))).2
  nlinarith

/-- `0 < τ < 7/8`. -/
theorem StripCritical.normalizedMixed_bounds {q c s u : ℝ} (h : StripCritical q c s u) :
    0<normalizedMixed q c s u ∧ normalizedMixed q c s u<7/8 := by
  obtain ⟨hxl,hxu,hyl,hyu⟩ := h.strip.quotient_bounds
  let x : ℝ := u/lowerRight q u
  let y : ℝ := lowerHeight q u/lowerLeft q u
  have hx : 0<x := by dsimp [x]; linarith
  have hy : 0<y := by dsimp [y]; linarith
  have hxyL : (783/1600:ℝ)*(25/96) ≤ x*y :=
    mul_le_mul hxl.le hyl.le (by norm_num) hx.le
  have hxyU : x*y<1 := by
    have hm := mul_lt_mul_of_pos_right hxu hy
    dsimp [x,y] at *
    nlinarith
  have hB := positionB_lower h.strip h.cosine_pos h.sine_nonneg h.unit h.tilt_upper
  have hBp : 0<positionB q c s u := by linarith
  rw [h.normalizedMixed_formula]
  change 0<(1-x*y)/positionB q c s u ∧ (1-x*y)/positionB q c s u<7/8
  refine ⟨div_pos (by linarith) hBp,?_⟩
  rw [div_lt_iff₀ hBp]
  nlinarith

/-- `|k_u|²/k₁ > 17/50`. -/
theorem StripCritical.positionNorm_lower {q c s u : ℝ} (h : StripCritical q c s u) :
    17/50<positionNorm q c s u/firstComponent q c s u := by
  have hb := h.strip.bounds
  obtain ⟨hxl,_,_,_⟩ := h.strip.quotient_bounds
  obtain ⟨hcL,_,_,_⟩ := small_tilt_bounds h.cosine_pos h.sine_nonneg h.unit h.tilt_upper
  have hB := positionB_lower h.strip h.cosine_pos h.sine_nonneg h.unit h.tilt_upper
  have hk := h.components_pos.1
  have hcx := mul_lt_mul_of_pos_left hxl h.cosine_pos
  have ha : s+19/40<positionA q c s u := by
    dsimp [positionA]
    have he : c*(u/lowerRight q u)=c*u/lowerRight q u := by ring
    nlinarith
  have hp : 0<slopeRatio q u := by linarith [hb.p_lower]
  have hbmul := mul_le_mul_of_nonneg_left hB hp.le
  have hb' : 1/2<positionb q c s u := by dsimp [positionb]; nlinarith [hb.p_lower]
  have hcr := mul_lt_mul_of_pos_left (show 7/10<lowerRight q u-1 by linarith [hb.r_lower]) h.cosine_pos
  have hsu := mul_le_mul_of_nonneg_left h.strip.u_upper h.sine_nonneg
  have hkU : firstComponent q c s u<s+657/500 := by dsimp [firstComponent]; nlinarith
  have has := square_strict_mono_nonneg (by linarith [h.sine_nonneg] : 0 ≤ s+19/40) ha
  have hbs := square_strict_mono_nonneg (by norm_num : (0:ℝ) ≤ 1/2) hb'
  dsimp [positionNorm]
  rw [lt_div_iff₀ hk]
  nlinarith [sq_nonneg s,h.sine_nonneg]

theorem StripCritical.tangentRatio_formula {q c s u : ℝ} (h : StripCritical q c s u) :
    tangentRatio q c s u=lowerRight q u-(s/c)/(s/c+u/lowerRight q u) := by
  have hr : 0<lowerRight q u := by linarith [h.strip.bounds.r_lower]
  have ha := h.positionA_pos
  have hc := h.cosine_pos
  have hh : 0 ≤ s/c := div_nonneg h.sine_nonneg hc.le
  have hx : 0<u/lowerRight q u := div_pos (by linarith [h.strip.u_lower]) hr
  have hden : 0<s/c+u/lowerRight q u := by linarith
  have hsum : 0<s*lowerRight q u+c*u := by
    nlinarith [mul_nonneg h.sine_nonneg hr.le,mul_pos hc (by linarith [h.strip.u_lower] : 0<u)]
  rw [tangentRatio,firstTilt,positionA]
  field_simp [ne_of_gt hsum]
  ring

/-- `7/5 < κ < 16/9`. -/
theorem StripCritical.tangentRatio_bounds {q c s u : ℝ} (h : StripCritical q c s u) :
    7/5<tangentRatio q c s u ∧ tangentRatio q c s u<16/9 := by
  have hb := h.strip.bounds
  obtain ⟨hxl,_,_,_⟩ := h.strip.quotient_bounds
  have hh : 0 ≤ s/c := div_nonneg h.sine_nonneg h.cosine_pos.le
  have hden : 0<s/c+u/lowerRight q u := by linarith
  have hφ : (s/c)/(s/c+u/lowerRight q u)<3/10 := by
    rw [div_lt_iff₀ hden]
    nlinarith [h.tilt_upper]
  have hφp : 0 ≤ (s/c)/(s/c+u/lowerRight q u) := div_nonneg hh hden.le
  rw [h.tangentRatio_formula]
  constructor <;> linarith [hb.r_lower,hb.r_upper]

theorem StripCritical.positionNormal_lower {q c s u : ℝ} (h : StripCritical q c s u) :
    rightSecond q c u+positionA q c s u*curvatureRatio q u ≤ normalizedPosition q c s u := by
  obtain ⟨hk₁,hk₂⟩ := h.components_pos
  have hp := h.position_equation
  dsimp [positionb] at hp
  have hq : 0 ≤ q := by linarith [h.strip.q_lower]
  have hw : 0<lowerLeft q u := by linarith [h.strip.bounds.w_lower]
  have hn : 0 ≤ s*q*slopeRatio q u^2/lowerLeft q u^3 :=
    div_nonneg (mul_nonneg (mul_nonneg h.sine_nonneg hq) (sq_nonneg _)) (pow_pos hw 3).le
  have hrem := mul_nonneg hk₂.le hn
  have he : positionNormal q c s u-firstComponent q c s u*
      (rightSecond q c u+positionA q c s u*curvatureRatio q u)=
      secondComponent q c s u*(s*q*slopeRatio q u^2/lowerLeft q u^3) := by
    dsimp [positionNormal,leftSecond]
    linear_combination -curvatureRatio q u*hp
  dsimp only [normalizedPosition]
  rw [le_div_iff₀ hk₁]
  nlinarith

/-- The bound behind `κ σ > 3`, for every tangent `h ≥ 0`. -/
theorem angular_curvature_reserve {h : ℝ} (hh : 0 ≤ h) :
    1531/500<1+(783/1600:ℝ)^2+1833/1000+273/200*h-4/5*(h/(h+783/1600)) := by
  have hd : 0<h+783/1600 := by linarith
  have key : 4/5*h<(1+(783/1600:ℝ)^2+1833/1000+273/200*h-1531/500)*(h+783/1600) := by
    nlinarith [sq_nonneg (h-9/200)]
  have hlt : 4/5*(h/(h+783/1600))<1+(783/1600:ℝ)^2+1833/1000+273/200*h-1531/500 := by
    rw [mul_div_assoc',div_lt_iff₀ hd]
    exact key
  linarith

/-- `κ σ > 3`. -/
theorem StripCritical.tangent_position_reserve {q c s u : ℝ} (h : StripCritical q c s u) :
    3<tangentRatio q c s u*normalizedPosition q c s u := by
  have hb := h.strip.bounds
  obtain ⟨hxl,_,_,_⟩ := h.strip.quotient_bounds
  obtain ⟨hcL,_,_,_⟩ := small_tilt_bounds h.cosine_pos h.sine_nonneg h.unit h.tilt_upper
  have hc := h.cosine_pos
  have hκp : 0<tangentRatio q c s u := by linarith [h.tangentRatio_bounds.1]
  have hd := h.firstTilt_pos
  have hr : 0<lowerRight q u := by linarith [hb.r_lower]
  have ht : 0 ≤ s/c := div_nonneg h.sine_nonneg hc.le
  have hden : 0<s/c+u/lowerRight q u := by linarith
  have hcs : c*(s/c)=s := mul_div_cancel₀ s (ne_of_gt hc)
  -- `κ σ ≥ c (κ Q) + d Z`, where `Q = q/r³` and `κ A = d`
  have hka : tangentRatio q c s u*positionA q c s u=firstTilt q c s u := by
    rw [tangentRatio]
    field_simp [ne_of_gt h.positionA_pos]
  have hσ : c*(tangentRatio q c s u*(q/lowerRight q u^3))+
      firstTilt q c s u*curvatureRatio q u ≤ tangentRatio q c s u*normalizedPosition q c s u := by
    have hm := mul_le_mul_of_nonneg_left h.positionNormal_lower hκp.le
    have e : tangentRatio q c s u*(rightSecond q c u+positionA q c s u*curvatureRatio q u)=
        c*(tangentRatio q c s u*(q/lowerRight q u^3))+firstTilt q c s u*curvatureRatio q u := by
      rw [← hka,rightSecond]
      ring
    linarith
  -- `κ Q = 1 + x² - φ Q`, with `x = u/r`, `φ = t/(t+x)`, `t = s/c`
  have hκQ : 1+(783/1600)^2-4/5*((s/c)/(s/c+783/1600)) <
      tangentRatio q c s u*(q/lowerRight q u^3) := by
    have he : lowerRight q u^2+u^2=q := upper_circle hb.domain.first_radicand
    have hrQ : lowerRight q u*(q/lowerRight q u^3)=1+(u/lowerRight q u)^2 := by
      have hr0 := ne_of_gt hr
      calc lowerRight q u*(q/lowerRight q u^3)=(lowerRight q u^2+u^2)/lowerRight q u^2 := by
            rw [he]
            field_simp
        _ = 1+(u/lowerRight q u)^2 := by
            field_simp
    have hφQ := mul_le_mul_of_nonneg_left (right_curvature_upper h.strip).le
      (div_nonneg ht hden.le)
    have hφ : (s/c)/(s/c+u/lowerRight q u) ≤ (s/c)/(s/c+783/1600) :=
      div_le_div_of_nonneg_left ht (by linarith) (by linarith)
    have hx := square_strict_mono_nonneg (by norm_num : (0:ℝ) ≤ 783/1600) hxl
    rw [h.tangentRatio_formula,sub_mul,hrQ]
    linarith
  -- `d Z > d (13/10) (1 + p) ≥ (1833/1000) c + (273/200) s`
  have hdZ : 1833/1000*c+273/200*s<firstTilt q c s u*curvatureRatio q u := by
    have hZ := mul_lt_mul_of_pos_left (curvatureRatio_lower h.strip) hd
    have hrp : 21/20 ≤ (lowerRight q u-1)*(1+slopeRatio q u) := by
      have hm := mul_le_mul (show 7/10 ≤ lowerRight q u-1 by linarith [hb.r_lower])
        (show 3/2 ≤ 1+slopeRatio q u by linarith [hb.p_lower]) (by norm_num)
        (by linarith [hb.r_lower])
      linarith
    have e : firstTilt q c s u*(13/10*(1+slopeRatio q u))=
        13/10*(c*(u*(1+slopeRatio q u)))+13/10*(s*((lowerRight q u-1)*(1+slopeRatio q u))) := by
      rw [firstTilt]
      ring
    have h₁ := mul_lt_mul_of_pos_left (position_slope_product_lower h.strip) hc
    have h₂ := mul_le_mul_of_nonneg_left hrp h.sine_nonneg
    linarith
  have hangle := mul_lt_mul_of_pos_left (angular_curvature_reserve ht) hc
  linarith [mul_lt_mul_of_pos_left hκQ hc]

/-- `σ > 27/16`. -/
theorem StripCritical.normalizedPosition_lower {q c s u : ℝ} (h : StripCritical q c s u) :
    27/16<normalizedPosition q c s u := by
  have hk := h.tangentRatio_bounds
  have hprod := h.tangent_position_reserve
  have hκp : 0<tangentRatio q c s u := by linarith
  have hσp : 0<normalizedPosition q c s u := by
    by_contra! hh
    have hm := mul_nonpos_of_nonneg_of_nonpos hκp.le hh
    linarith
  have hm := mul_lt_mul_of_pos_right hk.2 hσp
  nlinarith

/-- At a critical point the tilt derivative of `(k₁, k₂)` is `κ` times its position derivative. -/
theorem StripCritical.derivative_proportionality {q c s u : ℝ} (h : StripCritical q c s u) :
    firstTilt q c s u=tangentRatio q c s u*positionA q c s u ∧
      secondTilt q c s u= -tangentRatio q c s u*positionb q c s u := by
  have ha := h.positionA_pos
  have hk₂ := h.components_pos.2
  have hfirst : firstTilt q c s u=tangentRatio q c s u*positionA q c s u := by
    dsimp [tangentRatio]
    field_simp [ne_of_gt ha]
  have hp := h.position_equation
  have ht := h.tilt_equation
  have hp' := congrArg (fun x : ℝ => tangentRatio q c s u*x) hp
  have hf' := congrArg (fun x : ℝ => firstComponent q c s u*x) hfirst
  refine ⟨hfirst,?_⟩
  apply mul_left_cancel₀ (ne_of_gt hk₂)
  nlinarith

/-- The determinant of the Hessian in terms of `κ`, `|k_u|²` and the three normal terms. -/
theorem StripCritical.hessian_identity {q c s u : ℝ} (h : StripCritical q c s u) :
    hessianDeterminant q c s u=4*(
      positionNorm q c s u*(positionNormal q c s u*tangentRatio q c s u^2-
        2*mixedNormal q c s u*tangentRatio q c s u+tiltNormal q c s u)+
      positionNormal q c s u*tiltNormal q c s u-mixedNormal q c s u^2) := by
  obtain ⟨hd,he⟩ := h.derivative_proportionality
  have hmix : mixedSecond q c s u=
      2*(tangentRatio q c s u*positionNorm q c s u+mixedNormal q c s u) := by
    dsimp only [mixedSecond,positionNorm]
    rw [hd,he]
    ring
  have htt : tiltSecond q c s u=
      2*(tangentRatio q c s u^2*positionNorm q c s u+tiltNormal q c s u) := by
    dsimp only [tiltSecond,positionNorm,tiltNormal]
    rw [hd,he]
    ring
  rw [hessianDeterminant,hmix,htt,positionSecond]
  ring

theorem StripCritical.normalized_hessian_identity {q c s u : ℝ} (h : StripCritical q c s u) :
    hessianDeterminant q c s u/(4*firstComponent q c s u^2)=
      (positionNorm q c s u/firstComponent q c s u)*
        (normalizedPosition q c s u*tangentRatio q c s u^2-
          2*normalizedMixed q c s u*tangentRatio q c s u+normalizedTilt q c s u)+
      normalizedPosition q c s u*normalizedTilt q c s u-normalizedMixed q c s u^2 := by
  rw [h.hessian_identity]
  dsimp only [normalizedPosition,normalizedMixed,normalizedTilt]
  field_simp [ne_of_gt h.components_pos.1]

/-- The rational inequality behind `StripCritical.hessian_reserve`. -/
theorem normalized_determinant_reserve {A κ σ τ ν : ℝ}
    (hA : 17/50<A) (hκ : 7/5<κ) (hτl : 0<τ) (hτu : τ<7/8)
    (hν : 9/100<ν) (hκσ : 3<κ*σ) (hσ : 27/16<σ) :
    237/20000<A*(σ*κ^2-2*τ*κ+ν)+σ*ν-τ^2 := by
  have hκp : 0<κ := by linarith
  have hνp : 0<ν := by linarith
  have hterm : 5/4<κ*σ-2*τ := by linarith
  have hm := mul_lt_mul_of_pos_left hterm hκp
  have hbracket : 46/25<σ*κ^2-2*τ*κ+ν := by nlinarith
  have hbracketp : 0<σ*κ^2-2*τ*κ+ν := by linarith
  have hmA := mul_lt_mul_of_pos_right hA hbracketp
  have hmB := mul_lt_mul_of_pos_left hbracket (by norm_num : (0:ℝ)<17/50)
  have hmσ := mul_lt_mul_of_pos_right hσ hνp
  have hmν := mul_lt_mul_of_pos_left hν (by norm_num : (0:ℝ)<27/16)
  have hτsq := square_strict_mono_nonneg hτl.le hτu
  nlinarith

/-- `det Hess > (237/5000) k₁²` at every critical point of the strip. -/
theorem StripCritical.hessian_reserve {q c s u : ℝ} (h : StripCritical q c s u) :
    (237/5000)*firstComponent q c s u^2<hessianDeterminant q c s u := by
  obtain ⟨hτl,hτu⟩ := h.normalizedMixed_bounds
  have hbound := normalized_determinant_reserve h.positionNorm_lower h.tangentRatio_bounds.1
    hτl hτu h.normalizedTilt_lower h.tangent_position_reserve h.normalizedPosition_lower
  rw [← h.normalized_hessian_identity] at hbound
  have hk := h.components_pos.1
  rw [lt_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hk))] at hbound
  nlinarith

/-- The determinant of the Hessian is positive at every critical point of the strip. -/
theorem StripCritical.hessian_pos {q c s u : ℝ} (h : StripCritical q c s u) :
    0<hessianDeterminant q c s u := by
  have hp := mul_pos (by norm_num : (0:ℝ)<237/5000) (sq_pos_of_pos h.components_pos.1)
  linarith [h.hessian_reserve]

/-! ### The second derivatives -/

/-- The radical domain with `q < 4` and the four radicals positive. -/
structure SmoothDomain (q u : ℝ) : Prop extends Domain q u where
  radius_lt_four : q<4
  r_pos : 0<lowerRight q u
  U_pos : 0<topRight q u
  Y_pos : 0<topHeight q u
  w_pos : 0<lowerLeft q u

theorem circle_ratio_derivative (A U V Y q : ℝ)
    (hA : A≠0) (hU : U≠0) (hV : V≠0) (hY : Y≠0)
    (hcircle₁ : U^2+A^2=q) (hcircle₂ : Y^2+V^2=q) :
    ((-1*V+A*(-(A/U)))*(U*Y)-(A*V)*((A/U)*Y+U*(A*V/(U*Y))))/(U*Y)^2=
      -(A*V/(U*Y))*(q/(A*U^2)+(A*V/(U*Y))*q/(Y*V^2)) := by
  calc _ = -(U^2+A^2)*V/(Y*U^3)-(Y^2+V^2)*A^2/(U^2*Y^3) := by
        field_simp
        ring
    _ = -q*V/(Y*U^3)-q*A^2/(U^2*Y^3) := by rw [hcircle₁,hcircle₂]
    _ = _ := by
        field_simp
        ring

/-- `p' = -p Z`. -/
theorem slopeRatio_deriv {q u : ℝ} (h : SmoothDomain q u) :
    HasDerivAt (slopeRatio q) (-slopeRatio q u*curvatureRatio q u) u := by
  obtain ⟨_,dU,dV,dY,_,_⟩ := radical_derivatives h.r_pos h.U_pos h.Y_pos h.w_pos
  have hA : 0<2-u := by linarith [h.toDomain.height_lt_two h.radius_lt_four]
  have hV := h.toDomain.topLeft_pos h.radius_lt_four
  exact (((hasDerivAt_id' u).const_sub 2).fun_mul dV).fun_div (dU.fun_mul dY)
    (ne_of_gt (mul_pos h.U_pos h.Y_pos)) |>.congr_deriv
      (circle_ratio_derivative (2-u) (topRight q u) (topLeft q u) (topHeight q u) q
        (ne_of_gt hA) (ne_of_gt h.U_pos) (ne_of_gt hV) (ne_of_gt h.Y_pos)
        (upper_circle h.second_radicand) (upper_circle h.third_radicand))

theorem rightRatio_deriv {q u : ℝ} (h : SmoothDomain q u) :
    HasDerivAt (fun v => v/lowerRight q v) (q/lowerRight q u^3) u := by
  have hr := ne_of_gt h.r_pos
  have he : lowerRight q u^2+u^2=q := upper_circle h.first_radicand
  refine ((hasDerivAt_id' u).fun_div (radical_derivatives h.r_pos h.U_pos h.Y_pos h.w_pos).1
    hr).congr_deriv ?_
  calc _ = (lowerRight q u^2+u^2)/lowerRight q u^3 := by
        field_simp
        ring
    _ = _ := by rw [he]

theorem lowerRatio_deriv {q u : ℝ} (h : SmoothDomain q u) :
    HasDerivAt (fun v => lowerHeight q v/lowerLeft q v)
      (-slopeRatio q u*q/lowerLeft q u^3) u := by
  obtain ⟨_,_,_,_,dv,dw⟩ := radical_derivatives h.r_pos h.U_pos h.Y_pos h.w_pos
  have hw := ne_of_gt h.w_pos
  have he : lowerLeft q u^2+lowerHeight q u^2=q := upper_circle h.fourth_radicand
  refine (dv.fun_div dw hw).congr_deriv ?_
  calc _ = -slopeRatio q u*(lowerLeft q u^2+lowerHeight q u^2)/lowerLeft q u^3 := by
        field_simp
        ring
    _ = _ := by rw [he]

theorem positionA_deriv {q c s u : ℝ} (h : SmoothDomain q u) :
    HasDerivAt (positionA q c s) (rightSecond q c u) u := by
  convert ((rightRatio_deriv h).const_mul c).const_add s using 1
  · funext v
    rw [positionA]
    ring
  · rw [rightSecond]
    ring

theorem positionB_deriv {q c s u : ℝ} (h : SmoothDomain q u) :
    HasDerivAt (positionB q c s) (-s*slopeRatio q u*q/lowerLeft q u^3) u := by
  convert ((lowerRatio_deriv h).const_mul s).const_add c using 1
  · funext v
    rw [positionB]
    ring
  · ring

/-- The position derivative of `2 positionHalf` is `positionSecond`. -/
theorem position_second_deriv {q c s u : ℝ} (h : SmoothDomain q u) :
    HasDerivAt (fun v => 2*positionHalf q c s v) (positionSecond q c s u) u := by
  obtain ⟨dk₁,dk₂⟩ := components_position_deriv (c:=c) (s:=s) h.r_pos h.U_pos h.Y_pos h.w_pos
  exact ((dk₁.fun_mul (positionA_deriv h)).fun_sub
    ((dk₂.fun_mul (slopeRatio_deriv h)).fun_mul (positionB_deriv h))).const_mul 2
      |>.congr_deriv (by
        rw [positionSecond,positionNorm,positionNormal,positionb,leftSecond,positionA,
          positionB]
        ring)

/-- The position entry of the Hessian is positive wherever the four radicals are. -/
theorem SmoothDomain.positionSecond_pos {q c s u : ℝ} (h : SmoothDomain q u)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) :
    0<positionSecond q c s u := by
  have hq : 0<q := by
    have he : lowerRight q u^2+u^2=q := upper_circle h.first_radicand
    nlinarith [sq_pos_of_pos h.r_pos,sq_nonneg u]
  have hA : 0<2-u := by linarith [h.toDomain.height_lt_two h.radius_lt_four]
  have hV := h.toDomain.topLeft_pos h.radius_lt_four
  have hv := h.toDomain.lowerHeight_pos h.radius_lt_four
  have hp : 0<slopeRatio q u := div_pos (mul_pos hA hV) (mul_pos h.U_pos h.Y_pos)
  have hZ : 0<curvatureRatio q u :=
    add_pos (div_pos hq (mul_pos hA (pow_pos h.U_pos 2)))
      (div_pos (mul_pos hp hq) (mul_pos h.Y_pos (pow_pos hV 2)))
  have hB : 0<positionB q c s u := by
    have hh := div_nonneg (mul_nonneg hs hv.le) h.w_pos.le
    rw [positionB]
    linarith
  have hright : 0<rightSecond q c u := div_pos (mul_pos hc hq) (pow_pos h.r_pos 3)
  have hleft : 0<leftSecond q c s u := by
    have hh := div_nonneg (mul_nonneg (mul_nonneg hs hq.le) (sq_nonneg (slopeRatio q u)))
      (pow_nonneg h.w_pos.le 3)
    have hpZB := mul_pos (mul_pos hp hZ) hB
    rw [leftSecond]
    linarith
  obtain ⟨hcu,hsu⟩ := unit_le_one hunit
  obtain ⟨hk₁,hk₂⟩ := components_pos h.radius_lt_four h.toDomain hc hcu hs hsu
  have hnormal : 0<positionNormal q c s u :=
    add_pos (mul_pos hk₁ hright) (mul_pos hk₂ hleft)
  rw [positionSecond,positionNorm]
  nlinarith [sq_nonneg (positionA q c s u),sq_nonneg (positionb q c s u)]

theorem positionA_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => positionA q (Real.cos x) (Real.sin x) u)
      (Real.cos t-Real.sin t*u/lowerRight q u) t :=
  (Real.hasDerivAt_sin t).fun_add (((Real.hasDerivAt_cos t).mul_const u).div_const
    (lowerRight q u)) |>.congr_deriv (by ring)

theorem positionB_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => positionB q (Real.cos x) (Real.sin x) u)
      (-Real.sin t+Real.cos t*lowerHeight q u/lowerLeft q u) t :=
  (Real.hasDerivAt_cos t).fun_add (((Real.hasDerivAt_sin t).mul_const (lowerHeight q u)).div_const
    (lowerLeft q u))

/-- The tilt derivative of `2 positionHalf` is `mixedSecond`. -/
theorem mixed_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => 2*positionHalf q (Real.cos x) (Real.sin x) u)
      (mixedSecond q (Real.cos t) (Real.sin t) u) t :=
  (((firstComponent_angle_deriv q u t).fun_mul (positionA_angle_deriv q u t)).fun_sub
    (((secondComponent_angle_deriv q u t).mul_const (slopeRatio q u)).fun_mul
      (positionB_angle_deriv q u t))).const_mul 2 |>.congr_deriv (by
        rw [mixedSecond,mixedNormal,positionb,positionA,positionB]
        ring)

/-- A stationary chain is a critical point of the strip. -/
theorem stationary_isStripCritical {d : Coordinates} (hd : d.IsStationary) :
    StripCritical d.q d.c d.s (-d.y) := by
  obtain ⟨hc,hs,ht⟩ := stationary_tilt hd
  refine ⟨⟨hd.q_lower,hd.q_upper,(stationary_coordinate_lower hd).le,
    by linarith [hd.y_lower]⟩,hc,hs,d.unit,ht,?_,?_⟩
  · have hp := coordinate_positionHalf hd.toIsChain
    rw [hd.position_stationary] at hp
    linarith
  · rw [coordinate_tiltFirst hd.toIsChain]
    exact hd.tilt_stationary

/-! ### The Hessian on the local rectangle -/

private theorem enclose {x a b l u : ℝ} (h : a ≤ x ∧ x ≤ b)
    (hl : l ≤ a) (hu : b ≤ u) : l ≤ x ∧ x ≤ u :=
  ⟨hl.trans h.1,h.2.trans hu⟩

private theorem quot_bounds {x y a b c d : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) (ha : 0 ≤ a) (hc : 0 < c) :
    a/d ≤ x/y ∧ x/y ≤ b/c :=
  positive_quotient_bounds hx hy ha hc

private theorem square_bounds {x a b : ℝ} (hx : a ≤ x ∧ x ≤ b) (ha : 0 ≤ a) :
    a^2 ≤ x^2 ∧ x^2 ≤ b^2 :=
  ⟨pow_le_pow_left₀ ha hx.1 2,pow_le_pow_left₀ (ha.trans hx.1) hx.2 2⟩

/-- A projection increases through the small tilt interval when its tangent component is positive. -/
private theorem projection_mono {a b x y U : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ U)
    (hderiv : 2*a*U ≤ b*(1-U^2)) :
    a*halfAngleCos x+b*halfAngleSin x ≤ a*halfAngleCos y+b*halfAngleSin y := by
  have hxU := hxy.trans hy
  have hy0 := hx.trans hxy
  have hxyU : x*y ≤ U^2 := by
    have h := mul_le_mul hxU hy hy0 (hy0.trans hy)
    nlinarith only [h]
  have hp := mul_nonneg hb (sub_nonneg.mpr hxyU)
  have hs := mul_nonneg ha (show 0 ≤ 2*U-(x+y) by linarith only [hxU,hy])
  have hsign : 0 ≤ b*(1-x*y)-a*(x+y) := by nlinarith only [hderiv,hp,hs]
  have hdiff : (a*halfAngleCos y+b*halfAngleSin y)-(a*halfAngleCos x+b*halfAngleSin x) =
      2*(y-x)*(b*(1-x*y)-a*(x+y))/((1+x^2)*(1+y^2)) := by
    unfold halfAngleCos halfAngleSin
    field_simp [ne_of_gt (halfAngle_den_pos x),ne_of_gt (halfAngle_den_pos y)]
    ring
  have hn := div_nonneg (mul_nonneg (by linarith only [hxy] : 0 ≤ 2*(y-x)) hsign)
    (mul_pos (halfAngle_den_pos x) (halfAngle_den_pos y)).le
  linarith only [hdiff,hn]

private theorem projection_bounds {a b al au bl bu z : ℝ}
    (ha : al ≤ a ∧ a ≤ au) (hb : bl ≤ b ∧ b ≤ bu)
    (hz : 1/20 ≤ z ∧ z ≤ 81/1000)
    (hal : 0 ≤ al := by norm_num) (hbl : 0 ≤ bl := by norm_num)
    (hlo : 2*al*(81/1000) ≤ bl*(1-(81/1000:ℝ)^2) := by norm_num)
    (hhi : 2*au*(81/1000) ≤ bu*(1-(81/1000:ℝ)^2) := by norm_num) :
    al*halfAngleCos (1/20)+bl*halfAngleSin (1/20) ≤ a*halfAngleCos z+b*halfAngleSin z ∧
    a*halfAngleCos z+b*halfAngleSin z ≤ au*halfAngleCos (81/1000)+bu*halfAngleSin (81/1000) := by
  have hz0 : 0 ≤ z := by linarith only [hz.1]
  have hc := (halfAngleCos_pos (z:=z) (by rw [abs_lt]; constructor <;> linarith only [hz])).le
  have hs := (halfAngleSin_pos (z:=z) (by linarith only [hz.1])).le
  constructor
  · exact (projection_mono hal hbl (by norm_num) hz.1 hz.2 hlo).trans
      (add_le_add (mul_le_mul_of_nonneg_right ha.1 hc) (mul_le_mul_of_nonneg_right hb.1 hs))
  · exact (add_le_add (mul_le_mul_of_nonneg_right ha.2 hc) (mul_le_mul_of_nonneg_right hb.2 hs)).trans
      (projection_mono (hal.trans (ha.1.trans ha.2)) (hbl.trans (hb.1.trans hb.2))
        hz0 hz.2 le_rfl hhi)

private theorem frame_endpoints {z : ℝ} (hz : 1/20 ≤ z ∧ z ≤ 81/1000) :
    halfAngleCos (81/1000) ≤ halfAngleCos z ∧ halfAngleCos z ≤ halfAngleCos (1/20) ∧
    halfAngleSin (1/20) ≤ halfAngleSin z ∧ halfAngleSin z ≤ halfAngleSin (81/1000) := by
  have hz0 : 0 ≤ z := by linarith only [hz.1]
  have hz2 := pow_le_pow_left₀ hz0 hz.2 2
  have hz2' := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/20) hz.1 2
  have hs := projection_bounds (a:=0) (b:=1) ⟨le_rfl,le_rfl⟩ ⟨le_rfl,le_rfl⟩ hz
  simp only [zero_mul,one_mul,zero_add] at hs
  refine ⟨?_,?_,hs.1,hs.2⟩
  · norm_num [halfAngleCos]
    rw [le_div_iff₀ (halfAngle_den_pos z)]
    nlinarith only [hz2]
  · norm_num [halfAngleCos]
    rw [div_le_iff₀ (halfAngle_den_pos z)]
    nlinarith only [hz2']

/-- Shear the position/tilt quadratic form by `3/5`. The squared slopes and normal terms
leave a positive diagonal reserve and a small mixed term. -/
private theorem reserve_bounds {A b d E M N R T k₁ k₂ p : ℝ}
    (hA : 0.604 ≤ A ∧ A ≤ 0.692) (hb : 0.59 ≤ b ∧ b ≤ 0.66)
    (hd : 0.964 ≤ d ∧ d ≤ 1.049) (hE : 0.946 ≤ E ∧ E ≤ 0.985)
    (hM : 0.9 ≤ M ∧ M ≤ 0.945) (hN : 0.116 ≤ N ∧ N ≤ 0.195)
    (hR : 0.702 ≤ R ∧ R ≤ 0.737) (hT : 1.315 ≤ T ∧ T ≤ 1.52)
    (hk₁ : 1.328 ≤ k₁ ∧ k₁ ≤ 1.419) (hk₂ : 1.383 ≤ k₂ ∧ k₂ ≤ 1.47)
    (hp : 0.578 ≤ p ∧ p ≤ 0.637) :
    let YY := 2*(A^2+b^2+k₁*R+k₂*T)
    let YT := 2*(A*d+b*E+k₁*M-k₂*p*N)
    let TT := 2*(d^2+E^2+k₁*(2-k₁)+k₂*(1-k₂))
    6 ≤ YY ∧ YY ≤ 9 ∧ 0.45 ≤ TT-(6/5)*YT+(9/25)*YY ∧
    -0.53 ≤ YT-(3/5)*YY ∧ YT-(3/5)*YY ≤ 0.91 ∧ |2*(k₁*d-k₂*E)| ≤ 0.361 := by
  let YY := 2*(A^2+b^2+k₁*R+k₂*T)
  let YT := 2*(A*d+b*E+k₁*M-k₂*p*N)
  let TT := 2*(d^2+E^2+k₁*(2-k₁)+k₂*(1-k₂))
  let P := d-(3/5)*A
  let Q := E-(3/5)*b
  have prod {x y l u l' u' : ℝ} (hx : l ≤ x ∧ x ≤ u) (hy : l' ≤ y ∧ y ≤ u')
      (hl : 0 ≤ l := by norm_num) (hl' : 0 ≤ l' := by norm_num) :=
    positive_product_bounds hx hy hl hl'
  have hP : 0.5488 ≤ P ∧ P ≤ 0.6866 := by dsimp [P]; constructor <;> linarith only [hd,hA]
  have hQ : 0.55 ≤ Q ∧ Q ≤ 0.631 := by dsimp [Q]; constructor <;> linarith only [hE,hb]
  have hPs := square_bounds hP (by norm_num)
  have hQs := square_bounds hQ (by norm_num)
  have h₁ : (1.419:ℝ)*(2-1.419) ≤ k₁*(2-k₁) := by
    have hh := mul_nonneg (sub_nonneg.mpr hk₁.2)
      (show 0 ≤ 1.419+k₁-2 by linarith only [hk₁.1])
    nlinarith only [hh]
  have h₂ : (1.47:ℝ)*(1-1.47) ≤ k₂*(1-k₂) := by
    have hh := mul_nonneg (sub_nonneg.mpr hk₂.2)
      (show 0 ≤ 1.47+k₂-1 by linarith only [hk₂.1])
    nlinarith only [hh]
  have hτ₁ := prod hk₁ hM
  have hτ₂ := prod (prod hk₂ hp) hN
  have hσ₁ := prod hk₁ hR
  have hσ₂ := prod hk₂ hT
  have hS : TT-(6/5)*YT+(9/25)*YY =
      2*(P^2+Q^2+k₁*(2-k₁)+k₂*(1-k₂)-(6/5)*(k₁*M-k₂*p*N)+(9/25)*(k₁*R+k₂*T)) := by
    dsimp [TT,YT,YY,P,Q]; ring
  have hsmall : 0.4578 ≤ M-(3/5)*R ∧ M-(3/5)*R ≤ 0.5238 := by
    constructor <;> linarith only [hM,hR]
  have hpN := prod hp hN
  have hlarge : 0.856048 ≤ p*N+(3/5)*T ∧ p*N+(3/5)*T ≤ 1.036215 := by
    constructor <;> linarith only [hpN,hT]
  have hBP := prod hA hP
  have hBQ := prod hb hQ
  have hBk₁ := prod hk₁ hsmall
  have hBk₂ := prod hk₂ hlarge
  have hB : YT-(3/5)*YY = 2*(A*P+b*Q+k₁*(M-(3/5)*R)-k₂*(p*N+(3/5)*T)) := by
    dsimp [YT,YY,P,Q]; ring
  have hF₁ := prod hk₁ hd
  have hF₂ := prod hk₂ hE
  have hAs := square_bounds hA (by norm_num)
  have hbs := square_bounds hb (by norm_num)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · change 6 ≤ YY
    dsimp only [YY]
    linarith only [hAs,hbs,hσ₁,hσ₂]
  · change YY ≤ 9
    dsimp only [YY]
    linarith only [hAs,hbs,hσ₁,hσ₂]
  · change 0.45 ≤ TT-(6/5)*YT+(9/25)*YY
    rw [hS]
    linarith only [hPs,hQs,h₁,h₂,hτ₁,hτ₂,hσ₁,hσ₂]
  · change -0.53 ≤ YT-(3/5)*YY
    rw [hB]
    linarith only [hBP,hBQ,hBk₁,hBk₂]
  · change YT-(3/5)*YY ≤ 0.91
    rw [hB]
    linarith only [hBP,hBQ,hBk₁,hBk₂]
  · exact abs_le.mpr ⟨by linarith only [hF₁,hF₂],by linarith only [hF₁,hF₂]⟩

private theorem cube_bounds {x a b : ℝ} (hx : a ≤ x ∧ x ≤ b) (ha : 0 ≤ a) :
    a^3 ≤ x^3 ∧ x^3 ≤ b^3 :=
  ⟨pow_le_pow_left₀ ha hx.1 3,pow_le_pow_left₀ (ha.trans hx.1) hx.2 3⟩

/-- Endpoint projections bound the frame terms. Combining `p Z` before bounding it cancels
the small factors in the curvature ratio; the resulting circle-curvature bounds control the
sheared Hessian uniformly on the whole rectangle. -/
private theorem algebraic_hessian_bounds {q u r U V Y v w z : ℝ}
    (hq : 3.9155 ≤ q ∧ q ≤ 3.9156) (hu : 0.895 ≤ u ∧ u ≤ 0.937)
    (hr : 1.7428 ≤ r ∧ r ≤ 1.7649) (hU : 1.6414 ≤ U ∧ U ≤ 1.6691)
    (hV : 1.3309 ≤ V ∧ V ≤ 1.3586) (hY : 1.4387 ≤ Y ∧ Y ≤ 1.4643)
    (hv : 0.5357 ≤ v ∧ v ≤ 0.5613) (hw : 1.8974 ≤ w ∧ w ≤ 1.9049)
    (hz : 1/20 ≤ z ∧ z ≤ 81/1000) :
    let c := halfAngleCos z; let s := halfAngleSin z
    let p := (2-u)*V/(U*Y)
    let Z := q/((2-u)*U^2)+p*q/(Y*V^2)
    let A := s+c*u/r; let L := c+s*v/w; let b := p*L
    let d := s*(r-1)+c*u; let E := s*v+c*(w-1)
    let M := c-s*u/r; let N := c*v/w-s
    let R := c*q/r^3; let T := p*Z*L+s*q*p^2/w^3
    let k₁ := 2-c*(r-1)+s*u; let k₂ := 1+c*v-s*(w-1)
    let YY := 2*(A^2+b^2+k₁*R+k₂*T)
    let YT := 2*(A*d+b*E+k₁*M-k₂*p*N)
    let TT := 2*(d^2+E^2+k₁*(2-k₁)+k₂*(1-k₂))
    6 ≤ YY ∧ YY ≤ 9 ∧ 0.45 ≤ TT-(6/5)*YT+(9/25)*YY ∧
    -0.53 ≤ YT-(3/5)*YY ∧ YT-(3/5)*YY ≤ 0.91 ∧ |2*(k₁*d-k₂*E)| ≤ 0.361 := by
  let c := halfAngleCos z; let s := halfAngleSin z
  let p := (2-u)*V/(U*Y)
  let Z := q/((2-u)*U^2)+p*q/(Y*V^2)
  let A := s+c*u/r; let L := c+s*v/w; let b := p*L
  let d := s*(r-1)+c*u; let E := s*v+c*(w-1)
  let M := c-s*u/r; let N := c*v/w-s
  let R := c*q/r^3; let T := p*Z*L+s*q*p^2/w^3
  let k₁ := 2-c*(r-1)+s*u; let k₂ := 1+c*v-s*(w-1)
  have prod {x y l h l' h' : ℝ} (hx : l ≤ x ∧ x ≤ h) (hy : l' ≤ y ∧ y ≤ h')
      (hl : 0 ≤ l := by norm_num) (hl' : 0 ≤ l' := by norm_num) :=
    positive_product_bounds hx hy hl hl'
  obtain ⟨hcl,hcu,hsl,hsu⟩ := frame_endpoints hz
  have hc : 0.98696 ≤ c ∧ c ≤ 0.99502 :=
    enclose ⟨hcl,hcu⟩ (by norm_num [halfAngleCos]) (by norm_num [halfAngleCos])
  have hs : 0.09975 ≤ s ∧ s ≤ 0.16095 :=
    enclose ⟨hsl,hsu⟩ (by norm_num [halfAngleSin]) (by norm_num [halfAngleSin])
  have hur : 0.507 ≤ u/r ∧ u/r ≤ 0.538 :=
    enclose (quot_bounds hu hr (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hvw : 0.281 ≤ v/w ∧ v/w ≤ 0.296 :=
    enclose (quot_bounds hv hw (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hr₁ : 0.7428 ≤ r-1 ∧ r-1 ≤ 0.7649 := by constructor <;> linarith only [hr]
  have hw₁ : 0.8974 ≤ w-1 ∧ w-1 ≤ 0.9049 := by constructor <;> linarith only [hw]
  have hA : 0.604 ≤ A ∧ A ≤ 0.692 := by
    have h := enclose (projection_bounds hur (show (1:ℝ) ≤ 1 ∧ 1 ≤ 1 from ⟨le_rfl,le_rfl⟩) hz)
      (l:=0.604) (u:=0.692) (by norm_num [halfAngleCos,halfAngleSin])
      (by norm_num [halfAngleCos,halfAngleSin])
    convert h using 1 <;> dsimp only [A,c,s] <;> ring_nf
  have hL : 1.022 ≤ L ∧ L ≤ 1.035 := by
    have h := enclose (projection_bounds (show (1:ℝ) ≤ 1 ∧ 1 ≤ 1 from ⟨le_rfl,le_rfl⟩) hvw hz)
      (l:=1.022) (u:=1.035) (by norm_num [halfAngleCos,halfAngleSin])
      (by norm_num [halfAngleCos,halfAngleSin])
    convert h using 1 <;> dsimp only [L,c,s] <;> ring_nf
  have hd : 0.964 ≤ d ∧ d ≤ 1.049 := by
    have h := enclose (projection_bounds hu hr₁ hz) (l:=0.964) (u:=1.049)
      (by norm_num [halfAngleCos,halfAngleSin]) (by norm_num [halfAngleCos,halfAngleSin])
    convert h using 1 <;> dsimp only [d,c,s] <;> ring_nf
  have hE : 0.946 ≤ E ∧ E ≤ 0.985 := by
    have h := enclose (projection_bounds hw₁ hv hz) (l:=0.946) (u:=0.985)
      (by norm_num [halfAngleCos,halfAngleSin]) (by norm_num [halfAngleCos,halfAngleSin])
    convert h using 1 <;> dsimp only [E,c,s] <;> ring_nf
  have hM₀ := prod hs hur
  have hN₀ := prod hc hvw
  have hM : 0.9 ≤ M ∧ M ≤ 0.945 := by
    have he : M = c-s*(u/r) := by dsimp [M]; ring
    rw [he]; constructor <;> linarith only [hc,hM₀]
  have hN : 0.116 ≤ N ∧ N ≤ 0.195 := by
    have he : N = c*(v/w)-s := by dsimp [N]; ring
    rw [he]; constructor <;> linarith only [hs,hN₀]
  have hk₁₀ := prod hc hr₁
  have hk₁₁ := prod hs hu
  have hk₂₀ := prod hc hv
  have hk₂₁ := prod hs hw₁
  have hk₁ : 1.328 ≤ k₁ ∧ k₁ ≤ 1.419 := by
    dsimp only [k₁]; constructor <;> linarith only [hk₁₀,hk₁₁]
  have hk₂ : 1.383 ≤ k₂ ∧ k₂ ≤ 1.47 := by
    dsimp only [k₂]; constructor <;> linarith only [hk₂₀,hk₂₁]
  have ha : 1.063 ≤ 2-u ∧ 2-u ≤ 1.105 := by constructor <;> linarith only [hu]
  have hp : 0.578 ≤ p ∧ p ≤ 0.637 :=
    enclose (quot_bounds (prod ha hV) (prod hU hY) (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  have hb : 0.59 ≤ b ∧ b ≤ 0.66 := enclose (prod hp hL) (by norm_num) (by norm_num)
  have hR : 0.702 ≤ R ∧ R ≤ 0.737 :=
    enclose (quot_bounds (prod hc hq) (cube_bounds hr (by norm_num)) (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  -- Multiplying by p cancels the small factors in the curvature ratio.
  have hpZ : p*Z = q*V/(U^3*Y)+(2-u)^2*q/(U^2*Y^3) := by
    have ha0 : 2-u ≠ 0 := ne_of_gt (by linarith only [ha.1])
    have hU0 : U ≠ 0 := ne_of_gt (by linarith only [hU.1])
    have hV0 : V ≠ 0 := ne_of_gt (by linarith only [hV.1])
    have hY0 : Y ≠ 0 := ne_of_gt (by linarith only [hY.1])
    dsimp [p,Z]
    field_simp [ha0,hU0,hV0,hY0]
  have hZ₁ := quot_bounds (prod hq hV) (prod (cube_bounds hU (by norm_num)) hY)
    (by norm_num) (by norm_num)
  have hZ₂ := quot_bounds (prod (square_bounds ha (by norm_num)) hq)
    (prod (square_bounds hU (by norm_num)) (cube_bounds hY (by norm_num)))
    (by norm_num) (by norm_num)
  have hZ : 1.271 ≤ p*Z ∧ p*Z ≤ 1.4321 := by
    rw [hpZ]; constructor <;> linarith only [hZ₁,hZ₂]
  have hT₁ := prod hZ hL
  have hT₂ := quot_bounds (prod (prod hs hq) (square_bounds hp (by norm_num)))
    (cube_bounds hw (by norm_num)) (by norm_num) (by norm_num)
  have hT : 1.315 ≤ T ∧ T ≤ 1.52 := by
    dsimp only [T]; constructor <;> linarith only [hT₁,hT₂]
  exact reserve_bounds hA hb hd hE hM hN hR hT hk₁ hk₂ hp

/-- Change back to the half-angle tangent, including its angular acceleration. Completing
the square after the shear proves the `1/4`-shifted determinant positive. -/
private theorem shear_det_pos {A B C F z : ℝ}
    (hz : 1/20 ≤ z ∧ z ≤ 81/1000) (hA : 6 ≤ A)
    (hS : 0.45 ≤ C-(6/5)*B+(9/25)*A)
    (hB : -0.53 ≤ B-(3/5)*A ∧ B-(3/5)*A ≤ 0.91) (hF : |F| ≤ 0.361) :
    0 < (A-1/4)*((2/(1+z^2))^2*C-(4*z/(1+z^2)^2)*F-1/4)-(-(2/(1+z^2))*B)^2 := by
  let g := 2/(1+z^2)
  let t := 4*z/(1+z^2)^2
  let H := B-(3/5)*A
  let K := C-(6/5)*B+(9/25)*A
  let R := g^2*(K-9/100)-t*F-1/4
  have hz0 : 0 ≤ z := by linarith only [hz.1]
  have hz2 : z^2 ≤ (81/1000:ℝ)^2 := pow_le_pow_left₀ hz0 hz.2 2
  have hg : 1.98 ≤ g ∧ g ≤ 2 := by
    dsimp only [g]
    constructor
    · rw [le_div_iff₀ (halfAngle_den_pos z)]
      nlinarith only [hz2]
    · rw [div_le_iff₀ (halfAngle_den_pos z)]
      nlinarith only [sq_nonneg z]
  have hden : 1 ≤ (1+z^2)^2 := by nlinarith only [sq_nonneg z,sq_nonneg (z^2)]
  have ht : 0 ≤ t ∧ t ≤ 0.324 := by
    dsimp only [t]
    refine ⟨div_nonneg (by positivity) (sq_nonneg _),?_⟩
    rw [div_le_iff₀ (sq_pos_of_pos (halfAngle_den_pos z))]
    nlinarith only [hden,hz.2]
  have htF : |t*F| ≤ 0.12 := by
    rw [abs_mul,abs_of_nonneg ht.1]
    have h := mul_le_mul ht.2 hF (abs_nonneg F) (by norm_num : (0:ℝ) ≤ 0.324)
    linarith only [h]
  have hsq : (1.98:ℝ)^2 ≤ g^2 := pow_le_pow_left₀ (by norm_num) hg.1 2
  have hprod : (1.98:ℝ)^2*0.36 ≤ g^2*(K-9/100) :=
    mul_le_mul hsq (by dsimp [K]; linarith only [hS]) (by norm_num) (sq_nonneg g)
  have hR : 1 ≤ R := by
    have hh := (abs_le.mp htF).2
    dsimp only [R]
    linarith only [hprod,hh]
  have hH : |H+3/20| ≤ 1.06 := by
    rw [abs_le]
    dsimp only [H]
    constructor <;> linarith only [hB]
  have hcross : |g*(H+3/20)| ≤ 2.12 := by
    rw [abs_mul,abs_of_nonneg (by linarith only [hg.1] : 0 ≤ g)]
    have h := mul_le_mul hg.2 hH (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    linarith only [h]
  have hcross2 : (g*(H+3/20))^2 ≤ (2.12:ℝ)^2 :=
    by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hcross 2
  have hmain : 5.75 ≤ (A-1/4)*R := by
    have h := mul_le_mul (show (5.75:ℝ) ≤ A-1/4 by linarith only [hA]) hR
      (by norm_num : (0:ℝ) ≤ 1) (by linarith only [hA] : 0 ≤ A-1/4)
    linarith only [h]
  have he : (A-1/4)*(g^2*C-t*F-1/4)-(-g*B)^2 =
      (A-1/4)*R-(g*(H+3/20))^2 := by
    dsimp only [R,H,K]; ring
  change 0 < (A-1/4)*(g^2*C-t*F-1/4)-(-g*B)^2
  rw [he]
  linarith only [hmain,hcross2]

/-- The position entry and the two entries after shearing have uniform geometric bounds. -/
theorem local_hessian_bounds {q y z : ℝ}
    (hq : 7831/2000 ≤ q ∧ q ≤ 9789/2500)
    (hy : -937/1000 ≤ y ∧ y ≤ -179/200) (hz : 1/20 ≤ z ∧ z ≤ 81/1000) :
    let c := halfAngleCos z; let s := halfAngleSin z
    6 ≤ positionSecond q c s (-y) ∧ positionSecond q c s (-y) ≤ 9 ∧
    0.45 ≤ tiltSecond q c s (-y)-(6/5)*mixedSecond q c s (-y)+(9/25)*positionSecond q c s (-y) ∧
    -0.53 ≤ mixedSecond q c s (-y)-(3/5)*positionSecond q c s (-y) ∧
    mixedSecond q c s (-y)-(3/5)*positionSecond q c s (-y) ≤ 0.91 ∧
    |tiltFirst q c s (-y)| ≤ 0.361 := by
  let a := radicalCoordinates q y z
  obtain ⟨hrl,hru,hUl,hUu,hYl,hYu,hwl,hwu,_⟩ := radical_coordinate_bounds hq hy hz
  have hq' : 3.9155 ≤ q ∧ q ≤ 3.9156 := by constructor <;> linarith only [hq]
  have hu : 0.895 ≤ -y ∧ -y ≤ 0.937 := by constructor <;> linarith only [hy]
  have hr : 1.7428 ≤ a.x₁ ∧ a.x₁ ≤ 1.7649 := by constructor <;> linarith only [hrl,hru]
  have hU : 1.6414 ≤ a.x₂ ∧ a.x₂ ≤ 1.6691 := by constructor <;> linarith only [hUl,hUu]
  have hV : 1.3309 ≤ -a.x₃ ∧ -a.x₃ ≤ 1.3586 := by
    dsimp only [Coordinates.x₃]; constructor <;> linarith only [hUl,hUu]
  have hY : 1.4387 ≤ a.y₃ ∧ a.y₃ ≤ 1.4643 := by constructor <;> linarith only [hYl,hYu]
  have hv : 0.5357 ≤ -a.y₄ ∧ -a.y₄ ≤ 0.5613 := by
    dsimp only [Coordinates.y₄]; constructor <;> linarith only [hYl,hYu]
  have hw : 1.8974 ≤ -a.x₄ ∧ -a.x₄ ≤ 1.9049 := by constructor <;> linarith only [hwl,hwu]
  have h := algebraic_hessian_bounds hq' hu hr hU hV hY hv hw hz
  have hvalues : lowerRight q (-y) = a.x₁ ∧ topRight q (-y) = a.x₂ ∧
      topLeft q (-y) = -a.x₃ ∧ topHeight q (-y) = a.y₃ ∧
      lowerHeight q (-y) = -a.y₄ ∧ lowerLeft q (-y) = -a.x₄ := radical_coordinate_values q y z
  obtain ⟨hr',hU',hV',hY',hv',hw'⟩ := hvalues
  simp only [positionSecond,positionNorm,positionA,positionb,positionNormal,rightSecond,
    leftSecond,positionB,curvatureRatio,slopeRatio,tiltSecond,mixedSecond,mixedNormal,
    tiltFirst,firstTilt,secondTilt,firstComponent,secondComponent,hr',hU',hV',hY',hv',hw',
    sub_neg_eq_add] at ⊢
  convert h using 1 <;> ring_nf

/-- The half-angle Hessian shifted by `1/4` is positive definite throughout the rectangle. -/
theorem local_halfAngle_hessian_pos {q y z : ℝ}
    (hq : 7831/2000 ≤ q ∧ q ≤ 9789/2500)
    (hy : -937/1000 ≤ y ∧ y ≤ -179/200) (hz : 1/20 ≤ z ∧ z ≤ 81/1000) :
    let c := halfAngleCos z; let s := halfAngleSin z
    0 < (positionSecond q c s (-y)-1/4)*
      ((2/(1+z^2))^2*tiltSecond q c s (-y)-(4*z/(1+z^2)^2)*tiltFirst q c s (-y)-1/4)-
      (-(2/(1+z^2))*mixedSecond q c s (-y))^2 := by
  obtain ⟨hA,_,hS,hB₀,hB₁,hF⟩ := local_hessian_bounds hq hy hz
  exact shear_det_pos hz hA hS ⟨hB₀,hB₁⟩ hF

/-- The same derivative bounds give the position curvature used in the existence proof. -/
theorem local_positionSecond_bounds {q y z : ℝ}
    (hq : 7831/2000 ≤ q ∧ q ≤ 9789/2500)
    (hy : -937/1000 ≤ y ∧ y ≤ -179/200)
    (hz : 1/20 ≤ z ∧ z ≤ 81/1000) :
    6 ≤ positionSecond q (halfAngleCos z) (halfAngleSin z) (-y) ∧
    positionSecond q (halfAngleCos z) (halfAngleSin z) (-y) ≤ 9 := by
  have h := local_hessian_bounds hq hy hz
  exact ⟨h.1,h.2.1⟩

/-! ### Radius slope on the local rectangle -/

private theorem radius_slope_bounds {r U Y v w k₁ k₂ c s : ℝ}
    (hr : 1.7428 ≤ r ∧ r ≤ 1.7649) (hU : 1.6414 ≤ U ∧ U ≤ 1.6691)
    (hY : 1.4387 ≤ Y ∧ Y ≤ 1.4643) (hv : 0.5357 ≤ v ∧ v ≤ 0.5613)
    (hw : 1.8974 ≤ w ∧ w ≤ 1.9049) (hk₁ : 1.3198 ≤ k₁ ∧ k₁ ≤ 1.4263)
    (hk₂ : 1.3202 ≤ k₂ ∧ k₂ ≤ 1.5316) (hc : 0.986 ≤ c ∧ c ≤ 1)
    (hs : 0.099 ≤ s ∧ s ≤ 0.162) :
    -4 ≤ -1-k₁*c/r-k₂*(3*c/(U*Y)+s/w*(1+3*v/(U*Y))) ∧
    -1-k₁*c/r-k₂*(3*c/(U*Y)+s/w*(1+3*v/(U*Y))) ≤ -3 := by
  have prod {x y l h l' h' : ℝ} (hx : l ≤ x ∧ x ≤ h) (hy : l' ≤ y ∧ y ≤ h')
      (hl : 0 ≤ l := by norm_num) (hl' : 0 ≤ l' := by norm_num) :=
    positive_product_bounds hx hy hl hl'
  have hX : 0.7 ≤ k₁*c/r ∧ k₁*c/r ≤ 0.82 :=
    enclose (quot_bounds (prod hk₁ hc) hr (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hUY := prod hU hY
  have hV := quot_bounds (prod (show (3:ℝ) ≤ 3 ∧ 3 ≤ 3 from ⟨le_rfl,le_rfl⟩) hv) hUY
    (by norm_num) (by norm_num)
  have hfac : 1 ≤ 1+3*v/(U*Y) ∧ 1+3*v/(U*Y) ≤ 1.714 := by
    constructor <;> linarith only [hV]
  have hS := quot_bounds hs hw (by norm_num) (by norm_num)
  have hsf := prod hS hfac
  have hL : 1.2 ≤ 3*c/(U*Y) ∧ 3*c/(U*Y) ≤ 1.271 :=
    enclose (quot_bounds (prod (show (3:ℝ) ≤ 3 ∧ 3 ≤ 3 from ⟨le_rfl,le_rfl⟩) hc)
      hUY (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hB : 1.2 ≤ 3*c/(U*Y)+s/w*(1+3*v/(U*Y)) ∧
      3*c/(U*Y)+s/w*(1+3*v/(U*Y)) ≤ 1.42 := by
    constructor <;> linarith only [hL,hsf]
  have hk₂' : 1.32 ≤ k₂ ∧ k₂ ≤ 1.532 := by constructor <;> linarith only [hk₂]
  have hY := prod hk₂' hB
  constructor <;> linarith only [hX,hY]

/-- The local circle bounds give the uniform radius slope without a numerical certificate. -/
theorem local_radiusSlope_bounds {q y z : ℝ}
    (hq : 7831/2000 ≤ q ∧ q ≤ 9789/2500)
    (hy : -937/1000 ≤ y ∧ y ≤ -179/200) (hz : 1/20 ≤ z ∧ z ≤ 81/1000) :
    -4 ≤ radiusSlope q (halfAngleCos z) (halfAngleSin z) (-y) ∧
    radiusSlope q (halfAngleCos z) (halfAngleSin z) (-y) ≤ -3 := by
  let a := radicalCoordinates q y z
  obtain ⟨hrl,hru,hUl,hUu,hYl,hYu,hwl,hwu,hk₁l,hk₁u,hk₂l,hk₂u⟩ :=
    radical_coordinate_bounds hq hy hz
  obtain ⟨hcl,hcu,hsl,hsu⟩ := halfAngle_local_bounds hz
  have hr : 1.7428 ≤ a.x₁ ∧ a.x₁ ≤ 1.7649 := by constructor <;> linarith only [hrl,hru]
  have hU : 1.6414 ≤ a.x₂ ∧ a.x₂ ≤ 1.6691 := by constructor <;> linarith only [hUl,hUu]
  have hY : 1.4387 ≤ a.y₃ ∧ a.y₃ ≤ 1.4643 := by constructor <;> linarith only [hYl,hYu]
  have hv : 0.5357 ≤ -a.y₄ ∧ -a.y₄ ≤ 0.5613 := by
    dsimp only [Coordinates.y₄]; constructor <;> linarith only [hYl,hYu]
  have hw : 1.8974 ≤ -a.x₄ ∧ -a.x₄ ≤ 1.9049 := by constructor <;> linarith only [hwl,hwu]
  have hk₁ : 1.3198 ≤ -a.h₁ ∧ -a.h₁ ≤ 1.4263 := by constructor <;> linarith only [hk₁l,hk₁u]
  have hk₂ : 1.3202 ≤ -a.h₂ ∧ -a.h₂ ≤ 1.5316 := by constructor <;> linarith only [hk₂l,hk₂u]
  have h := radius_slope_bounds hr hU hY hv hw hk₁ hk₂ ⟨hcl,hcu⟩ ⟨hsl,hsu⟩
  have hvalues : lowerRight q (-y) = a.x₁ ∧ topRight q (-y) = a.x₂ ∧
      topLeft q (-y) = -a.x₃ ∧ topHeight q (-y) = a.y₃ ∧
      lowerHeight q (-y) = -a.y₄ ∧ lowerLeft q (-y) = -a.x₄ := radical_coordinate_values q y z
  obtain ⟨hr',hU',_,hY',hv',hw'⟩ := hvalues
  have hk₁' : firstComponent q (halfAngleCos z) (halfAngleSin z) (-y) = -a.h₁ := by
    rw [firstComponent,hr']
    change 2-halfAngleCos z*(a.x₁-1)+halfAngleSin z*(-y) =
      -(halfAngleCos z*a.x₁+halfAngleSin z*y-2-halfAngleCos z)
    ring
  have hk₂' : secondComponent q (halfAngleCos z) (halfAngleSin z) (-y) = -a.h₂ := by
    rw [secondComponent,hv',hw']
    change 1+halfAngleCos z*(-a.y₄)-halfAngleSin z*(-a.x₄-1) =
      -(-halfAngleSin z*a.x₄+halfAngleCos z*a.y₄-1-halfAngleSin z)
    ring
  simpa only [radiusSlope,hk₁',hk₂',hr',hU',hY',hv',hw'] using h

/-- The local coordinate bounds keep all four radicals in the smooth domain. -/
theorem local_smoothDomain {q y z : ℝ}
    (hq : 7831/2000 ≤ q ∧ q ≤ 9789/2500)
    (hy : -937/1000 ≤ y ∧ y ≤ -179/200)
    (hz : 1/20 ≤ z ∧ z ≤ 81/1000) : SmoothDomain q (-y) := by
  obtain ⟨hrl,_,hUl,_,hYl,_,_,hwu,_⟩ := radical_coordinate_bounds hq hy hz
  obtain ⟨hr,hU,_,hY,_,hw⟩ := radical_coordinate_values q y z
  have hrp : 0 < lowerRight q (-y) := by rw [hr]; linarith only [hrl]
  have hUp : 0 < topRight q (-y) := by rw [hU]; linarith only [hUl]
  have hYp : 0 < topHeight q (-y) := by rw [hY]; linarith only [hYl]
  have hwp : 0 < lowerLeft q (-y) := by rw [hw]; linarith only [hwu]
  exact ⟨domain_of_pos (by linarith only [hy.2]) hrp hUp hYp hwp,
    by linarith only [hq.2],hrp,hUp,hYp,hwp⟩

end SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry
