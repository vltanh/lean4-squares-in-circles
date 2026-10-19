module

public import SquaresInCircles.Eight.ExactFamily.Convexity

/-!
# Eight squares: the Hessian at a critical point

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
uses the Hessian bound for the second derivative of the envelope in the tilt.
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

end SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry
