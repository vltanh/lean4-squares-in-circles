import SquaresInCircles.Six.Supports
import SquaresInCircles.Six.Wings.Chart

/-!
# Six squares: the angles of W and D in a missing west wing

Let W be separated from C along its own axis and from D along the secondary
axis of D, at the angles `v` and `d`, with `q = d + v ≥ 1`. Weights `b`, `z`
and `1` on the separations C–W, C–D and W–D, against bounds
`w₀ + w₁ sin q + w₂ cos q` and `D₀` on the works of the forces on W and D and
against the box of C, leave the profile
`K + b (A cos v + (1/2 + y) sin v) + z (A cos d + (1/2 - y) sin d) + α cos q + β sin q`
with `α = 1/2 - w₂` and `β = 1/2 - w₁`, nonpositive for one face `y` of the box.
At each `d` it is a constant plus a harmonic in `v`, or in `q`; at each `v`
or each `q`, a constant plus a harmonic in `d`. On an interval of `[0, π/2]`
such a function is positive when it is positive at the ends and the harmonic
has nonnegative coefficients, so on each domain below the profile is positive
once it is positive at the corners, where Taylor brackets give the sign. Four
rows of weights exclude in turn `d ≤ 3/5`, `d + v ≤ 53/50`, `v ≥ 31/50` and
`d ≤ 16/25`.
-/

noncomputable section
namespace SquaresInCircles.Six.Wings
open Normalization

/-- `(1/2) sin x + B cos x ≤ 4/5`, since `(1/2)² + B² < (4/5)²`. -/
lemma adverse_harmonic (x : ℝ) : (1/2)*Real.sin x+B*Real.cos x ≤ 4/5 := by
  have hid : ((1/2)*Real.sin x+B*Real.cos x)^2+((1/2)*Real.cos x-B*Real.sin x)^2 =
      (1/2:ℝ)^2+B^2 := by
    linear_combination ((1/2:ℝ)^2+B^2)*(Real.sin_sq_add_cos_sq x)
  nlinarith [sq_nonneg ((1/2)*Real.cos x-B*Real.sin x),
    sq_nonneg ((1/2)*Real.sin x+B*Real.cos x-4/5),show (1/2:ℝ)^2+B^2 < (4/5)^2 by norm_num [B]]

namespace WestRange

/-- The profile of the stress with weights `b`, `z`, `1` on C–W, C–D and W–D. -/
def profile (b z α β K y v d : ℝ) : ℝ :=
  K+b*(A*Real.cos v+(1/2+y)*Real.sin v)+z*(A*Real.cos d+(1/2-y)*Real.sin d)+
    α*Real.cos (d+v)+β*Real.sin (d+v)

/-! ### The profile as a harmonic in each direction -/

lemma profile_west (b z α β K y v d : ℝ) : profile b z α β K y v d =
    (K+z*(A*Real.cos d+(1/2-y)*Real.sin d))+(b*A+α*Real.cos d+β*Real.sin d)*Real.cos v+
      (b*(1/2+y)-α*Real.sin d+β*Real.cos d)*Real.sin v := by
  rw [profile,Real.cos_add,Real.sin_add]
  ring

lemma profile_gap (b z α β K y q d : ℝ) : profile b z α β K y (q-d) d =
    (K+z*(A*Real.cos d+(1/2-y)*Real.sin d))+(α+b*(A*Real.cos d-(1/2+y)*Real.sin d))*Real.cos q+
      (β+b*(A*Real.sin d+(1/2+y)*Real.cos d))*Real.sin q := by
  rw [profile,show d+(q-d)=q by ring,Real.cos_sub,Real.sin_sub]
  ring

lemma profile_diagonal (b z α β K y v d : ℝ) : profile b z α β K y v d =
    (K+b*(A*Real.cos v+(1/2+y)*Real.sin v))+(z*A+α*Real.cos v+β*Real.sin v)*Real.cos d+
      (z*(1/2-y)-α*Real.sin v+β*Real.cos v)*Real.sin d := by
  rw [profile,Real.cos_add,Real.sin_add]
  ring

lemma profile_wall (b z α β K y k d : ℝ) : profile b z α β K y (k-d) d =
    (K+α*Real.cos k+β*Real.sin k)+(z*A+b*(A*Real.cos k+(1/2+y)*Real.sin k))*Real.cos d+
      (z*(1/2-y)+b*(A*Real.sin k-(1/2+y)*Real.cos k))*Real.sin d := by
  rw [profile,show d+(k-d)=k by ring,Real.cos_sub,Real.sin_sub]
  ring

/-- The coefficients of the harmonics of the profile with the cone support of W
(`α = 1/2`, `β = -B`) are nonnegative on `[0, π/2]` when `B ≤ c A` and
`4/5 ≤ e`, for `(c, e) = (b, b (1/2 + y))` in `v` and `(z, z (1/2 - y))` in
`d`. -/
lemma cone_coefficients {c e x : ℝ} (hx : 0 ≤ x ∧ x ≤ Real.pi/2) (hcA : B ≤ c*A)
    (he : 4/5 ≤ e) :
    0 ≤ c*A+(1/2)*Real.cos x+(1/2-rhoBound)*Real.sin x ∧
      0 ≤ e-(1/2)*Real.sin x+(1/2-rhoBound)*Real.cos x := by
  have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hx.2⟩
  have ha := adverse_harmonic x
  have hp := mul_le_mul_of_nonneg_left (Real.sin_le_one x) (show (0:ℝ) ≤ B by norm_num [B])
  have hB : 1/2-rhoBound = -B := by
    norm_num [B,rhoBound]
  rw [hB]
  constructor <;> nlinarith

/-- The profile with the Taylor polynomials in place of `cos` and `sin`. -/
def lower (b z α β K y v d : ℝ) : ℝ :=
  K+b*A*cosLower v+b*(1/2+y)*sinBelow v+z*A*cosLower d+z*(1/2-y)*sinBelow d+
    α*cosLower (d+v)+min (β*sinBelow (d+v)) (β*sinAbove (d+v))

/-- The Taylor polynomials bound the profile below for nonnegative angles and
weights, a face `y` in `[0, 1/2]` and `α ≥ 0`. -/
lemma lower_le_profile {b z α β K y v d : ℝ} (hb : 0 ≤ b) (hz : 0 ≤ z)
    (hy : 0 ≤ y ∧ y ≤ 1/2) (hα : 0 ≤ α) :
    lower b z α β K y v d ≤ profile b z α β K y v d := by
  have hA : (0:ℝ) ≤ A := by norm_num [A]
  have cv := mul_le_mul_of_nonneg_left (cosLower_le v) (mul_nonneg hb hA)
  have sv := mul_le_mul_of_nonneg_left (sinBelow_le v)
    (mul_nonneg hb (show 0 ≤ 1/2+y by linarith))
  have cd := mul_le_mul_of_nonneg_left (cosLower_le d) (mul_nonneg hz hA)
  have sd := mul_le_mul_of_nonneg_left (sinBelow_le d)
    (mul_nonneg hz (show 0 ≤ 1/2-y by linarith))
  have cq := mul_le_mul_of_nonneg_left (cosLower_le (d+v)) hα
  have sq : min (β*sinBelow (d+v)) (β*sinAbove (d+v)) ≤ β*Real.sin (d+v) := by
    rcases le_total 0 β with hβ | hβ
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left (sinBelow_le _) hβ)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left (le_sinAbove _) hβ)
  simp only [lower,profile] at *
  linarith only [cv,sv,cd,sd,cq,sq]

/-! ### Positivity on the domains -/

/-- On `d₁ ≤ d ≤ d₂`, `k - d ≤ v ≤ t`, the profile is positive if the Taylor
polynomials are positive at the four corners and the harmonics of the profile in
`v`, along `v = t` and along `d + v = k` have nonnegative coefficients. -/
lemma positive_wall {b z α β K y k t d₁ d₂ v d : ℝ}
    (hb : 0 ≤ b) (hz : 0 ≤ z) (hy : 0 ≤ y ∧ y ≤ 1/2) (hα : 0 ≤ α)
    (hd : d₁ ≤ d ∧ d ≤ d₂) (hv : k-d ≤ v ∧ v ≤ t)
    (hd₁ : 0 ≤ d₁) (hd₂ : d₂ ≤ Real.pi/2) (hk : d₂ ≤ k) (ht : t ≤ Real.pi/2)
    (hwest : ∀ x, d₁ ≤ x → x ≤ d₂ →
      0 ≤ b*A+α*Real.cos x+β*Real.sin x ∧ 0 ≤ b*(1/2+y)-α*Real.sin x+β*Real.cos x)
    (htop : 0 ≤ z*A+α*Real.cos t+β*Real.sin t ∧ 0 ≤ z*(1/2-y)-α*Real.sin t+β*Real.cos t)
    (hwall : 0 ≤ z*A+b*(A*Real.cos k+(1/2+y)*Real.sin k) ∧
      0 ≤ z*(1/2-y)+b*(A*Real.sin k-(1/2+y)*Real.cos k))
    (hc : 0 < lower b z α β K y (k-d₁) d₁ ∧ 0 < lower b z α β K y t d₁ ∧
      0 < lower b z α β K y t d₂ ∧ 0 < lower b z α β K y (k-d₂) d₂) :
    0 < profile b z α β K y v d := by
  have ht0 : 0 ≤ t := by linarith
  have h1 := hc.1.trans_le (lower_le_profile hb hz hy hα)
  have h2 := hc.2.1.trans_le (lower_le_profile hb hz hy hα)
  have h3 := hc.2.2.1.trans_le (lower_le_profile hb hz hy hα)
  have h4 := hc.2.2.2.trans_le (lower_le_profile hb hz hy hα)
  rw [profile_wall] at h1 h4
  rw [profile_diagonal] at h2 h3
  have hw := harmonic_pos_of_endpoints hwall.1 hwall.2 hd₁ hd₂ hd h1 h4
  have ht' := harmonic_pos_of_endpoints htop.1 htop.2 hd₁ hd₂ hd h2 h3
  rw [← profile_wall] at hw
  rw [← profile_diagonal] at ht'
  rw [profile_west] at hw ht' ⊢
  exact harmonic_pos_of_endpoints (hwest d hd.1 hd.2).1 (hwest d hd.1 hd.2).2
    (by linarith) ht hv hw ht'

/-- On `t₁ ≤ v ≤ t₂`, `d₁ ≤ d ≤ d₂`, the profile is positive if the Taylor
polynomials are positive at the four corners and the harmonics of the profile in
`v` and in `d` have nonnegative coefficients. -/
lemma positive_rectangle {b z α β K y t₁ t₂ d₁ d₂ v d : ℝ}
    (hb : 0 ≤ b) (hz : 0 ≤ z) (hy : 0 ≤ y ∧ y ≤ 1/2) (hα : 0 ≤ α)
    (hd : d₁ ≤ d ∧ d ≤ d₂) (hv : t₁ ≤ v ∧ v ≤ t₂)
    (hd₁ : 0 ≤ d₁) (hd₂ : d₂ ≤ Real.pi/2) (ht₁ : 0 ≤ t₁) (ht₂ : t₂ ≤ Real.pi/2)
    (hwest : ∀ x, d₁ ≤ x → x ≤ d₂ →
      0 ≤ b*A+α*Real.cos x+β*Real.sin x ∧ 0 ≤ b*(1/2+y)-α*Real.sin x+β*Real.cos x)
    (hdiag : ∀ x, t₁ ≤ x → x ≤ t₂ →
      0 ≤ z*A+α*Real.cos x+β*Real.sin x ∧ 0 ≤ z*(1/2-y)-α*Real.sin x+β*Real.cos x)
    (hc : 0 < lower b z α β K y t₁ d₁ ∧ 0 < lower b z α β K y t₂ d₁ ∧
      0 < lower b z α β K y t₂ d₂ ∧ 0 < lower b z α β K y t₁ d₂) :
    0 < profile b z α β K y v d := by
  have h1 := hc.1.trans_le (lower_le_profile hb hz hy hα)
  have h2 := hc.2.1.trans_le (lower_le_profile hb hz hy hα)
  have h3 := hc.2.2.1.trans_le (lower_le_profile hb hz hy hα)
  have h4 := hc.2.2.2.trans_le (lower_le_profile hb hz hy hα)
  rw [profile_diagonal] at h1 h2 h3 h4
  have hl := harmonic_pos_of_endpoints (hdiag t₁ le_rfl (by linarith)).1
    (hdiag t₁ le_rfl (by linarith)).2 hd₁ hd₂ hd h1 h4
  have hr := harmonic_pos_of_endpoints (hdiag t₂ (by linarith) le_rfl).1
    (hdiag t₂ (by linarith) le_rfl).2 hd₁ hd₂ hd h2 h3
  rw [← profile_diagonal] at hl hr
  rw [profile_west] at hl hr ⊢
  exact harmonic_pos_of_endpoints (hwest d hd.1 hd.2).1 (hwest d hd.1 hd.2).2 ht₁ ht₂ hv hl hr

/-- On `k₁ ≤ d + v ≤ k₂`, `d₁ ≤ d ≤ d₂`, the profile is positive if the Taylor
polynomials are positive at the four corners and the harmonics of the profile in
`d` along `d + v = k` and in `d + v` at each `d` have nonnegative
coefficients. -/
lemma positive_gap {b z α β K y k₁ k₂ d₁ d₂ v d : ℝ}
    (hb : 0 ≤ b) (hz : 0 ≤ z) (hy : 0 ≤ y ∧ y ≤ 1/2) (hα : 0 ≤ α)
    (hd : d₁ ≤ d ∧ d ≤ d₂) (hq : k₁ ≤ d+v ∧ d+v ≤ k₂)
    (hd₁ : 0 ≤ d₁) (hd₂ : d₂ ≤ Real.pi/2) (hk : d₂ ≤ k₁) (hk₂ : k₂ ≤ Real.pi/2)
    (hgap : ∀ x, d₁ ≤ x → x ≤ d₂ → 0 ≤ α+b*(A*Real.cos x-(1/2+y)*Real.sin x) ∧
      0 ≤ β+b*(A*Real.sin x+(1/2+y)*Real.cos x))
    (hwall : ∀ k, k₁ ≤ k → k ≤ k₂ → 0 ≤ z*A+b*(A*Real.cos k+(1/2+y)*Real.sin k) ∧
      0 ≤ z*(1/2-y)+b*(A*Real.sin k-(1/2+y)*Real.cos k))
    (hc : 0 < lower b z α β K y (k₁-d₁) d₁ ∧ 0 < lower b z α β K y (k₂-d₁) d₁ ∧
      0 < lower b z α β K y (k₂-d₂) d₂ ∧ 0 < lower b z α β K y (k₁-d₂) d₂) :
    0 < profile b z α β K y v d := by
  have h1 := hc.1.trans_le (lower_le_profile hb hz hy hα)
  have h2 := hc.2.1.trans_le (lower_le_profile hb hz hy hα)
  have h3 := hc.2.2.1.trans_le (lower_le_profile hb hz hy hα)
  have h4 := hc.2.2.2.trans_le (lower_le_profile hb hz hy hα)
  rw [profile_wall] at h1 h2 h3 h4
  have hl := harmonic_pos_of_endpoints (hwall k₁ le_rfl (by linarith)).1
    (hwall k₁ le_rfl (by linarith)).2 hd₁ hd₂ hd h1 h4
  have hr := harmonic_pos_of_endpoints (hwall k₂ (by linarith) le_rfl).1
    (hwall k₂ (by linarith) le_rfl).2 hd₁ hd₂ hd h2 h3
  rw [← profile_wall] at hl hr
  rw [profile_gap] at hl hr
  have h := harmonic_pos_of_endpoints (hgap d hd.1 hd.2).1 (hgap d hd.1 hd.2).2
    (by linarith) hk₂ hq hl hr
  rwa [← profile_gap,show d+v-d=v by ring] at h

/-! ### The stress -/

/-- The separations of C from W and from D along their own axes and of W and D
along the secondary axis of D, with weights `b`, `z` and `1`, against bounds on
the works of the forces on W and D and against the box of C: the profile is
nonpositive on one face `y` of the box. -/
lemma profile_nonpos {X : Chart} {b z w₀ w₁ w₂ D₀ : ℝ} (hb : 0 ≤ b) (hz : 0 ≤ z)
    (hW : X.WestOwn) (hWD : X.WestDiagonal)
    (hv : 0 ≤ X.v) (hd : 0 ≤ X.d) (hq : X.d+X.v ≤ Real.pi/2)
    (hWs : (b+Real.sin (X.d+X.v))*X.aW-Real.cos (X.d+X.v)*X.bW ≤
      w₀+w₁*Real.sin (X.d+X.v)+w₂*Real.cos (X.d+X.v))
    (hDs : z*X.aD+X.bD ≤ D₀) :
    ∃ y, (y = 0 ∨ y = coreUpper) ∧
      profile b z (1/2-w₂) (1/2-w₁) (b/2+z/2+1/2-w₀-D₀) y X.v X.d ≤ 0 := by
  have hCD := X.diagonal_own
  simp only [Chart.WestOwn,Chart.WestDiagonal] at hW hWD
  have width {x : ℝ} (hx : 0 ≤ x ∧ x ≤ Real.pi/2) :
      angularWidth x=(Real.cos x+Real.sin x)/2 ∧ 0 ≤ Real.cos x ∧ 0 ≤ Real.sin x := by
    have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hx.2⟩
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [Real.pi_pos])
    exact ⟨by simp only [angularWidth,abs_of_nonneg hc,abs_of_nonneg hs],hc,hs⟩
  obtain ⟨hwv,hcv,-⟩ := width (x := X.v) ⟨hv,by linarith⟩
  obtain ⟨hwd,hcd,-⟩ := width (x := X.d) ⟨hd,by linarith⟩
  obtain ⟨hwq,-,-⟩ := width (x := X.d+X.v) ⟨by linarith,hq⟩
  rw [hwv] at hW
  rw [hwd] at hCD
  rw [hwq] at hWD
  have hx := mul_le_mul_of_nonneg_left (X.box.1.2.trans ceiling_bounds.2.2.2)
    (show 0 ≤ b*Real.cos X.v+z*Real.cos X.d by positivity)
  have hy0 := X.box.2.1
  have hy1 := X.box.2.2.trans ceiling_bounds.2.2.2
  have hcomb := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hW hb)
    (mul_le_mul_of_nonneg_left hCD hz)) hWD
  by_cases hY : 0 ≤ -b*Real.sin X.v+z*Real.sin X.d
  · refine ⟨coreUpper,Or.inr rfl,?_⟩
    have hy := mul_le_mul_of_nonneg_left hy1 hY
    simp only [profile,A,coreUpper] at hy hx ⊢
    nlinarith only [hcomb,hWs,hDs,hx,hy]
  · refine ⟨0,Or.inl rfl,?_⟩
    have hy := mul_nonpos_of_nonneg_of_nonpos hy0 (le_of_not_ge hY)
    simp only [profile,A,coreUpper] at hx ⊢
    nlinarith only [hcomb,hWs,hDs,hx,hy]

/-- The support of W when its force `(b + sin q, -cos q)` lies in the axial cone,
as it does for `b ≥ 2` and `1 ≤ q ≤ π/2`, where `cos q ≤ cos 1 ≤ 13/24`. -/
lemma west_cone {a c b q : ℝ} (hc : ContainedChart a |c|) (hb : 2 ≤ b)
    (hq : 1 ≤ q ∧ q ≤ Real.pi/2) :
    (b+Real.sin q)*a-Real.cos q*c ≤
      rhoBound*b+rhoBound*Real.sin q+0*Real.cos q := by
  obtain ⟨hcq,hs⟩ := cos_sin_nonneg (x := q) ⟨by linarith,hq.2⟩
  have hc1 := (Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith [Real.pi_pos])
    hq.1).trans (cos_upper_four (x := 1) (by norm_num))
  norm_num at hc1
  have h := cone_support hc (U := b+Real.sin q) (V := -Real.cos q) (by linarith)
    (by rw [abs_neg,abs_of_nonneg hcq]; linarith)
  linarith

/-- The far-vertex support of D, with the length of its force `(z, 1)` bounded by
`r`. -/
lemma diagonal_vertex (X : Chart) {z r : ℝ} (hz : 0 ≤ z) (hr : 0 ≤ r) (hzr : z^2+1 ≤ r^2) :
    z*X.aD+X.bD ≤ radiusBound*r-(z+1)/2 := by
  have h := vertex_support X.diagonal (U := z) (V := 1) hr (by linarith)
  norm_num [abs_of_nonneg hz] at h
  linarith

/-- The support of D when its force `(z, 1)` lies in the axial cone. -/
lemma diagonal_cone (X : Chart) {z : ℝ} (hz : 100/31 ≤ z) :
    z*X.aD+X.bD ≤ rhoBound*z := by
  have h := cone_support X.diagonal (U := z) (V := 1) (by linarith) (by rw [abs_one]; linarith)
  linarith

/-- The far-vertex support of W for the force `(27/100 + sin q, -cos q)`, whose
length `√(β² + 1 + 2β sin q)`, `β = 27/100`, lies below its tangent at
`31/25`. -/
lemma west_vertex (X : Chart) (q : ℝ) :
    (27/100+Real.sin q)*X.aW-Real.cos q*X.bW ≤
      (radiusBound*(5221/4960)-27/200)+
        (radiusBound*(27/124)-1/2)*Real.sin q+(-(1/2))*Real.cos q := by
  have hr : 0 ≤ 5221/4960+(27/124)*Real.sin q := by nlinarith [Real.neg_one_le_sin q]
  have h := vertex_support X.west (U := 27/100+Real.sin q) (V := -Real.cos q) hr
    (by nlinarith [Real.sin_sq_add_cos_sq q,sq_nonneg (Real.sin q-4647/5400)])
  linarith [le_abs_self (27/100+Real.sin q),neg_le_abs (-Real.cos q)]

/-! ### The four rows -/

/-- With W on its own axis and separated from D along the secondary axis of D,
the angle of D exceeds `3/5`: the weights `39/18` and `43/18` on C–W and C–D,
the cone support of W and the far-vertex support of D. -/
theorem diagonal_gt_three_fifths {X : Chart} (hW : X.WestOwn) (hWD : X.WestDiagonal)
    (hv : X.v ≤ 2/3) (hd : 1/2 ≤ X.d) (hgap : 1 ≤ X.d+X.v) : 3/5 < X.d := by
  by_contra! hd'
  have hq : X.d+X.v ≤ Real.pi/2 := by linarith [Real.pi_gt_d2]
  obtain ⟨y,hy,hn⟩ := profile_nonpos (b := 39/18) (z := 43/18) (by norm_num) (by norm_num)
    hW hWD (by linarith) (by linarith) hq (west_cone X.west (by norm_num) ⟨hgap,hq⟩)
    (diagonal_vertex X (r := 259/100) (by norm_num) (by norm_num) (by norm_num))
  rw [sub_zero] at hn
  have hy' : 0 ≤ y ∧ y ≤ 5641/50000 := by rcases hy with rfl | rfl <;> norm_num [coreUpper]
  have hc1 := cos_upper_four (x := 1) (by norm_num)
  have hs1 := sin_lower_seven (x := 1) (by norm_num)
  have hc0 := Real.cos_nonneg_of_mem_Icc (x := 1)
    ⟨by linarith [Real.pi_gt_d2],by linarith [Real.pi_gt_d2]⟩
  norm_num at hc1 hs1
  exact absurd hn (not_le.mpr (positive_wall (k := 1) (t := 2/3) (d₁ := 1/2) (d₂ := 3/5)
    (by norm_num) (by norm_num) ⟨hy'.1,by linarith⟩ (by norm_num) ⟨hd,hd'⟩ ⟨by linarith,hv⟩ (by norm_num)
    (by linarith [Real.pi_gt_d2]) (by norm_num) (by linarith [Real.pi_gt_d2])
    (fun x h1 h2 => cone_coefficients ⟨by linarith,by linarith [Real.pi_gt_d2]⟩
      (by norm_num [A,B]) (by nlinarith))
    (cone_coefficients ⟨by norm_num,by linarith [Real.pi_gt_d2]⟩ (by norm_num [A,B])
      (by nlinarith))
    ⟨by norm_num [A]; nlinarith,by norm_num [A]; nlinarith⟩
    (by rcases hy with rfl | rfl <;>
      norm_num [lower,A,cosLower,sinBelow,sinAbove,sinLower,sinUpper,rhoBound,radiusBound,
        coreUpper])))

/-- With W on its own axis and separated from D along the secondary axis of D,
and `3/5 ≤ d ≤ 11/14`, the gap `d + v` exceeds `53/50`: the weights `27/100` and
`57/25` on C–W and C–D and the far-vertex supports of W and D. -/
theorem gap_gt {X : Chart} (hW : X.WestOwn) (hWD : X.WestDiagonal) (hv : 0 ≤ X.v)
    (hd : 3/5 ≤ X.d ∧ X.d ≤ 11/14) (hgap : 1 ≤ X.d+X.v) : 53/50 < X.d+X.v := by
  by_contra! hq
  obtain ⟨y,hy,hn⟩ := profile_nonpos (b := 27/100) (z := 57/25) (by norm_num) (by norm_num)
    hW hWD hv (by linarith) (by linarith [Real.pi_gt_d2]) (west_vertex X (X.d+X.v))
    (diagonal_vertex X (r := 2489659/1000000) (by norm_num) (by norm_num) (by norm_num))
  have hy' : 0 ≤ y ∧ y ≤ 5641/50000 := by rcases hy with rfl | rfl <;> norm_num [coreUpper]
  exact absurd hn (not_le.mpr (positive_gap (k₁ := 1) (k₂ := 53/50) (d₁ := 3/5) (d₂ := 11/14)
    (by norm_num) (by norm_num) ⟨hy'.1,by linarith⟩ (by norm_num) hd ⟨hgap,hq⟩ (by norm_num)
    (by linarith [Real.pi_gt_d2]) (by norm_num) (by linarith [Real.pi_gt_d2])
    (fun x h1 h2 => by
      obtain ⟨hc,hs⟩ := cos_sin_nonneg (x := x) ⟨by linarith,by linarith [Real.pi_gt_d2]⟩
      constructor <;> norm_num [A,radiusBound] <;> nlinarith [Real.sin_le_one x])
    (fun k h1 h2 => by
      obtain ⟨hc,hs⟩ := cos_sin_nonneg (x := k) ⟨by linarith,by linarith [Real.pi_gt_d2]⟩
      constructor <;> norm_num [A] <;> nlinarith [Real.cos_le_one k])
    (by rcases hy with rfl | rfl <;>
      norm_num [lower,A,cosLower,sinBelow,sinAbove,radiusBound,coreUpper,sinLower,sinUpper])))

/-- With W on its own axis and separated from D along the secondary axis of D,
and `3/5 ≤ d ≤ 11/14`, the angle of W is below `31/50`: the weights `17/3` and
`14/3` on C–W and C–D and the cone supports of W and D. -/
theorem west_lt {X : Chart} (hW : X.WestOwn) (hWD : X.WestDiagonal) (hv : X.v ≤ 2/3)
    (hd : 3/5 ≤ X.d ∧ X.d ≤ 11/14) (hgap : 1 ≤ X.d+X.v) : X.v < 31/50 := by
  by_contra! hv'
  have hq : X.d+X.v ≤ Real.pi/2 := by linarith [Real.pi_gt_d2]
  obtain ⟨y,hy,hn⟩ := profile_nonpos (b := 17/3) (z := 14/3) (by norm_num) (by norm_num)
    hW hWD (by linarith) (by linarith) hq (west_cone X.west (by norm_num) ⟨hgap,hq⟩)
    (diagonal_cone X (z := 14/3) (by norm_num))
  rw [sub_zero] at hn
  have hy' : 0 ≤ y ∧ y ≤ 5641/50000 := by rcases hy with rfl | rfl <;> norm_num [coreUpper]
  exact absurd hn (not_le.mpr (positive_rectangle (t₁ := 31/50) (t₂ := 2/3) (d₁ := 3/5)
    (d₂ := 11/14) (by norm_num) (by norm_num) ⟨hy'.1,by linarith⟩ (by norm_num) hd ⟨hv',hv⟩
    (by norm_num) (by linarith [Real.pi_gt_d2]) (by norm_num) (by linarith [Real.pi_gt_d2])
    (fun x h1 h2 => cone_coefficients ⟨by linarith,by linarith [Real.pi_gt_d2]⟩
      (by norm_num [A,B]) (by nlinarith))
    (fun x h1 h2 => cone_coefficients ⟨by linarith,by linarith [Real.pi_gt_d2]⟩
      (by norm_num [A,B]) (by nlinarith))
    (by rcases hy with rfl | rfl <;>
      norm_num [lower,A,cosLower,sinBelow,sinAbove,rhoBound,coreUpper,sinLower,sinUpper])))

/-- With W on its own axis and separated from D along the secondary axis of D,
`v ≤ 31/50` and `d + v ≥ 53/50`, the angle of D exceeds `16/25`: the weights
`207/100` and `56/25` on C–W and C–D, the cone support of W and the far-vertex
support of D. -/
theorem diagonal_gt {X : Chart} (hW : X.WestOwn) (hWD : X.WestDiagonal) (hv : X.v ≤ 31/50)
    (hd : 3/5 ≤ X.d) (hgap : 53/50 ≤ X.d+X.v) : 16/25 < X.d := by
  by_contra! hd'
  have hq : X.d+X.v ≤ Real.pi/2 := by linarith [Real.pi_gt_d2]
  obtain ⟨y,hy,hn⟩ := profile_nonpos (b := 207/100) (z := 56/25) (by norm_num) (by norm_num)
    hW hWD (by linarith) (by linarith) hq (west_cone X.west (by norm_num) ⟨by linarith,hq⟩)
    (diagonal_vertex X (r := 61327/25000) (by norm_num) (by norm_num) (by norm_num))
  rw [sub_zero] at hn
  have hy' : 0 ≤ y ∧ y ≤ 5641/50000 := by rcases hy with rfl | rfl <;> norm_num [coreUpper]
  have hk := cos_sin_nonneg (x := 53/50) ⟨by norm_num,by linarith [Real.pi_gt_d2]⟩
  have hk1 := (Real.cos_le_cos_of_nonneg_of_le_pi (x := 1) (y := 53/50) (by norm_num)
    (by linarith [Real.pi_gt_d2]) (by norm_num)).trans (cos_upper_four (x := 1) (by norm_num))
  norm_num at hk1
  exact absurd hn (not_le.mpr (positive_wall (k := 53/50) (t := 31/50) (d₁ := 3/5)
    (d₂ := 16/25) (by norm_num) (by norm_num) ⟨hy'.1,by linarith⟩ (by norm_num) ⟨hd,hd'⟩
    ⟨by linarith,hv⟩ (by norm_num) (by linarith [Real.pi_gt_d2]) (by norm_num)
    (by linarith [Real.pi_gt_d2])
    (fun x h1 h2 => cone_coefficients ⟨by linarith,by linarith [Real.pi_gt_d2]⟩
      (by norm_num [A,B]) (by nlinarith))
    (cone_coefficients ⟨by norm_num,by linarith [Real.pi_gt_d2]⟩ (by norm_num [A,B])
      (by nlinarith))
    ⟨by norm_num [A]; nlinarith,by norm_num [A]; nlinarith⟩
    (by rcases hy with rfl | rfl <;>
      norm_num [lower,A,cosLower,sinBelow,sinAbove,sinLower,sinUpper,rhoBound,radiusBound,
        coreUpper])))

end WestRange

end SquaresInCircles.Six.Wings
