module

public import SquaresInCircles.Eight.ExactFamily.CriticalStrip

/-!
# The mixed and normal terms at a critical point

Uncompiled draft.  The quantitative terms here are the derivatives of the
actual circle chain.  Their bounds are derived from `CriticalStrip` and
the two stationary equations; neither feasibility nor a Hessian-positivity
hypothesis is part of `StripCritical`.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

def positionA (q c s u : ℝ) : ℝ := s+c*u/lowerRight q u
def positionB (q c s u : ℝ) : ℝ := c+s*lowerHeight q u/lowerLeft q u
def positionb (q c s u : ℝ) : ℝ := slopeRatio q u*positionB q c s u
def rightSecond (q c u : ℝ) : ℝ := c*q/lowerRight q u^3
def leftSecond (q c s u : ℝ) : ℝ :=
  slopeRatio q u*curvatureRatio q u*positionB q c s u+
    s*q*slopeRatio q u^2/lowerLeft q u^3
def positionNorm (q c s u : ℝ) : ℝ := positionA q c s u^2+positionb q c s u^2
def positionNormal (q c s u : ℝ) : ℝ :=
  firstComponent q c s u*rightSecond q c u+secondComponent q c s u*leftSecond q c s u
def mixedNormal (q c s u : ℝ) : ℝ :=
  firstComponent q c s u*(c-s*u/lowerRight q u)+
    secondComponent q c s u*slopeRatio q u*(s-c*lowerHeight q u/lowerLeft q u)
def tiltNormal (q c s u : ℝ) : ℝ :=
  2*firstComponent q c s u+secondComponent q c s u-
    (firstComponent q c s u^2+secondComponent q c s u^2)
def positionSecond (q c s u : ℝ) : ℝ :=
  2*(positionNorm q c s u+positionNormal q c s u)
def mixedSecond (q c s u : ℝ) : ℝ :=
  2*(positionA q c s u*firstTilt q c s u-positionb q c s u*secondTilt q c s u+
    mixedNormal q c s u)
def tangentRatio (q c s u : ℝ) : ℝ := firstTilt q c s u/positionA q c s u
def normalizedPosition (q c s u : ℝ) : ℝ := positionNormal q c s u/firstComponent q c s u
def normalizedMixed (q c s u : ℝ) : ℝ := mixedNormal q c s u/firstComponent q c s u
def normalizedTilt (q c s u : ℝ) : ℝ := tiltNormal q c s u/firstComponent q c s u
def hessianDeterminant (q c s u : ℝ) : ℝ :=
  positionSecond q c s u*tiltSecond q c s u-mixedSecond q c s u^2

structure StripCritical (q c s u : ℝ) : Prop where
  strip : CriticalStrip q u
  cosine_pos : 0<c
  sine_nonneg : 0 ≤ s
  unit : c^2+s^2=1
  tilt_upper : s/c ≤ 1/5
  position_zero : positionHalf q c s u=0
  tilt_zero : tiltFirst q c s u=0

theorem small_tilt_bounds {c s : ℝ} (hc : 0<c) (hs : 0 ≤ s)
    (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5) :
    49/50<c ∧ c ≤ 1 ∧ s ≤ 1 ∧ 5*s ≤ c ∧ 1 ≤ c+s := by
  have ht' : s ≤ (1/5)*c := (div_le_iff₀ hc).mp ht
  have hs2 := square_mono_nonneg hs ht'
  have hcL : 49/50<c := by
    by_contra! hh
    have hsq := square_mono_nonneg hc.le hh
    nlinarith
  have hcU : c ≤ 1 := by nlinarith [sq_nonneg s,sq_nonneg (c-1)]
  have hsU : s ≤ 1 := by nlinarith [sq_nonneg c,sq_nonneg (s-1)]
  have hsum : 1 ≤ c+s := by
    by_contra! hh
    have hsq := square_strict_mono_nonneg (add_nonneg hc.le hs) hh
    nlinarith [mul_nonneg hc.le hs]
  exact ⟨hcL,hcU,hsU,by linarith,hsum⟩

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
  obtain ⟨_,_,_,hst,_⟩ := small_tilt_bounds hc hs hunit ht
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
  obtain ⟨_,hc,hs,_,_⟩ := small_tilt_bounds h.cosine_pos h.sine_nonneg h.unit h.tilt_upper
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
  obtain ⟨_,_,_,hst,_⟩ := small_tilt_bounds hc hs hunit ht
  have hv := mul_lt_mul_of_pos_left hb.v_lower hc
  have hw := mul_le_mul_of_nonneg_left (by linarith [hb.w_upper] : lowerLeft q u-1 ≤ 23/25) hs
  dsimp [secondComponent]
  nlinarith

theorem tilt_ratio_lower {q c s u : ℝ} (h : CriticalStrip q u)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5) :
    (6/7)*firstTilt q c s u< -secondTilt q c s u := by
  have hb := h.bounds
  obtain ⟨_,_,_,hst,_⟩ := small_tilt_bounds hc hs hunit ht
  have hw := mul_lt_mul_of_pos_left (left_support_lower h) hc
  have hv : -(1/6)<lowerHeight q u-(6/7)*(lowerRight q u-1) := by
    linarith [hb.v_lower,hb.r_upper]
  have hv' := mul_le_mul_of_nonneg_left hv.le hs
  dsimp [firstTilt,secondTilt]
  nlinarith

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

/-- A cone and a radius bound imply the normal reserve by a quadratic
identity.  No square-root concavity lemma is needed. -/
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

/-- Keeping the common sine term gives a stronger elementary bound than
bounding the numerator and denominator independently. -/
theorem StripCritical.positionNorm_lower {q c s u : ℝ} (h : StripCritical q c s u) :
    17/50<positionNorm q c s u/firstComponent q c s u := by
  have hb := h.strip.bounds
  obtain ⟨hxl,_,_,_⟩ := h.strip.quotient_bounds
  obtain ⟨hcL,_,_,_,_⟩ := small_tilt_bounds h.cosine_pos h.sine_nonneg h.unit h.tilt_upper
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
  have he : positionA q c s u=c*(s/c+u/lowerRight q u) := by
    dsimp [positionA]
    field_simp [ne_of_gt hc,ne_of_gt hr]
    ring
  dsimp only [tangentRatio]
  apply (div_eq_iff (ne_of_gt ha)).2
  rw [he]
  dsimp [firstTilt]
  field_simp [ne_of_gt hc,ne_of_gt hr,ne_of_gt hden]
  ring

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

/-- A single completed square handles every nonnegative tangent. -/
theorem angular_curvature_reserve {h : ℝ} (hh : 0 ≤ h) :
    1531/500<1+(783/1600:ℝ)^2+1833/1000+(273/200)*h-
      (4/5)*h/(h+783/1600) := by
  have hd : 0<h+783/1600 := by linarith
  have he : 1+(783/1600:ℝ)^2+1833/1000+(273/200)*h-(4/5)*h/(h+783/1600)=
      ((1+(783/1600:ℝ)^2+1833/1000+(273/200)*h)*(h+783/1600)-(4/5)*h)/(h+783/1600) := by
    field_simp [ne_of_gt hd]
    ring
  rw [he,lt_div_iff₀ hd]
  nlinarith [sq_nonneg (h-9/200)]

theorem StripCritical.tangent_position_reserve {q c s u : ℝ} (h : StripCritical q c s u) :
    3<tangentRatio q c s u*normalizedPosition q c s u := by
  have hb := h.strip.bounds
  obtain ⟨hxl,_,_,_⟩ := h.strip.quotient_bounds
  obtain ⟨hcL,_,_,_,_⟩ := small_tilt_bounds h.cosine_pos h.sine_nonneg h.unit h.tilt_upper
  have hκ := h.tangentRatio_bounds.1
  have hκp : 0<tangentRatio q c s u := by linarith
  have ha := h.positionA_pos
  have hd := h.firstTilt_pos
  have hr : 0<lowerRight q u := by linarith [hb.r_lower]
  have hq : 0<q := by linarith [h.strip.q_lower]
  let t : ℝ := s/c
  let x : ℝ := u/lowerRight q u
  let Q : ℝ := q/lowerRight q u^3
  let φ : ℝ := t/(t+x)
  let φ₀ : ℝ := t/(t+783/1600)
  have ht : 0 ≤ t := div_nonneg h.sine_nonneg h.cosine_pos.le
  have hx : 783/1600<x := hxl
  have hden : 0<t+x := by linarith
  have hden₀ : 0<t+783/1600 := by linarith
  have hφp : 0 ≤ φ := div_nonneg ht hden.le
  have hφ : φ ≤ φ₀ := by
    dsimp [φ,φ₀]
    apply (div_le_div_iff₀ hden hden₀).2
    have hp := mul_nonneg ht (by linarith : 0 ≤ x-783/1600)
    nlinarith
  have hQ : Q<4/5 := right_curvature_upper h.strip
  have hQp : 0<Q := div_pos hq (pow_pos hr 3)
  have hrQ : lowerRight q u*Q=1+x^2 := by
    have he := upper_circle hb.domain.first_radicand
    dsimp [Q,x]
    field_simp [ne_of_gt hr]
    change lowerRight q u^2+u^2=q at he
    nlinarith
  have hκf : tangentRatio q c s u=lowerRight q u-φ := h.tangentRatio_formula
  have hκQ : tangentRatio q c s u*Q=1+x^2-φ*Q := by
    have he := congrArg (fun v : ℝ => v*Q) hκf
    nlinarith
  have hφQ := mul_le_mul_of_nonneg_left hQ.le hφp
  have hφ' := mul_le_mul_of_nonneg_left hφ (by norm_num : (0:ℝ) ≤ 4/5)
  have hxs := square_strict_mono_nonneg (by norm_num : (0:ℝ) ≤ 783/1600) hx
  have hkq : 1+(783/1600:ℝ)^2-(4/5)*φ₀<tangentRatio q c s u*Q := by nlinarith
  have hckq := mul_lt_mul_of_pos_left hkq h.cosine_pos
  have hka : tangentRatio q c s u*positionA q c s u=firstTilt q c s u := by
    dsimp [tangentRatio]
    field_simp [ne_of_gt ha]
  have hkaZ := congrArg (fun v : ℝ => v*curvatureRatio q u) hka
  have hσ := mul_le_mul_of_nonneg_left h.positionNormal_lower hκp.le
  have hright : rightSecond q c u=c*Q := by dsimp [rightSecond,Q]; ring
  rw [hright] at hσ
  have hZ := curvatureRatio_lower h.strip
  have hdZ := mul_lt_mul_of_pos_left hZ hd
  have hup := position_slope_product_lower h.strip
  have hpp : 3/2 ≤ 1+slopeRatio q u := by linarith [hb.p_lower]
  have hrp : 21/20 ≤ (lowerRight q u-1)*(1+slopeRatio q u) := by
    have hm := mul_le_mul (show 7/10 ≤ lowerRight q u-1 by linarith [hb.r_lower])
      hpp (by norm_num : (0:ℝ) ≤ 3/2) (by linarith [hb.r_lower])
    nlinarith
  have htp := mul_le_mul_of_nonneg_left hrp ht
  have hct := mul_le_mul_of_nonneg_left htp
    (mul_nonneg h.cosine_pos.le (by norm_num : (0:ℝ) ≤ 13/10))
  have hcu := mul_lt_mul_of_pos_left hup
    (mul_pos h.cosine_pos (by norm_num : (0:ℝ)<13/10))
  have hdf : firstTilt q c s u=c*(u+t*(lowerRight q u-1)) := by
    dsimp [firstTilt,t]
    field_simp [ne_of_gt h.cosine_pos]
    ring
  have hdf' := congrArg (fun v : ℝ => v*(13/10)*(1+slopeRatio q u)) hdf
  have hdb : c*(1833/1000+(273/200)*t)<firstTilt q c s u*(13/10)*(1+slopeRatio q u) := by
    nlinarith
  have hmain : c*(1+(783/1600:ℝ)^2+1833/1000+(273/200)*t-(4/5)*φ₀)<
      tangentRatio q c s u*normalizedPosition q c s u := by
    nlinarith
  have hangle := angular_curvature_reserve ht
  have hcangle := mul_lt_mul_of_pos_left hangle h.cosine_pos
  change c*(1531/500)<c*(1+(783/1600:ℝ)^2+1833/1000+(273/200)*t-(4/5)*φ₀) at hcangle
  nlinarith

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
  ring

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

/-- The six inputs are conclusions about the actual critical chain.
The defect may be positive; no zero-defect hypothesis is used. -/
theorem StripCritical.hessian_reserve {q c s u : ℝ} (h : StripCritical q c s u) :
    (237/5000)*firstComponent q c s u^2<hessianDeterminant q c s u := by
  obtain ⟨hτl,hτu⟩ := h.normalizedMixed_bounds
  have hbound := normalized_determinant_reserve h.positionNorm_lower h.tangentRatio_bounds.1
    hτl hτu h.normalizedTilt_lower h.tangent_position_reserve h.normalizedPosition_lower
  rw [← h.normalized_hessian_identity] at hbound
  have hk := h.components_pos.1
  rw [lt_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hk))] at hbound
  nlinarith

theorem StripCritical.hessian_pos {q c s u : ℝ} (h : StripCritical q c s u) :
    0<hessianDeterminant q c s u := by
  have hp := mul_pos (by norm_num : (0:ℝ)<237/5000) (sq_pos_of_pos h.components_pos.1)
  linarith [h.hessian_reserve]

end SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry
