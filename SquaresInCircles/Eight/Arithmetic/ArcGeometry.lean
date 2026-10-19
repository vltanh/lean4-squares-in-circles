module

public import SquaresInCircles.Eight.Arithmetic.AffineTableData

/-!
# Eight squares: the endpoints of an arc

An arc of a table ends at two rational values `u` of the tangent `b / a`, at the points `(a, u a)`
of its curve. On the outer circle `(a + 1/2)² + (b + 1/2)² = Q` the endpoint has
`a = outerEndpointA Q u`, the positive root of `(1 + u²) a² + (u + 1) a + 1/2 - Q = 0`, and on the
core corner `(a - 1/2)² + (b - 1/2)² = (1/12)²` it has `a = coreEndpointA u`, the larger root of
`(1 + u²) a² - (u + 1) a + 71/144 = 0`. `outerEndpoint_facts` and `coreEndpoint_facts` show that
these points lie on the curves with `0 ≤ b ≤ a`, for `u ∈ [0, 1]` on the outer circle and
`u ∈ [6/7, 1]` on the corner.

On a circle with centre `(v, v)`, a point to the right of the centre lies on the branch
`a = circleX v ρ b` (`circle_branch`), and to the right of and above the centre `b` increases with
the tangent (`circle_tangent_lower`, `circle_tangent_upper`); so the states of an arc have `b`
between the values at its endpoints, where the radicand of `circleX` is positive
(`circle_arc_radicand_positive`). `PreparedArc.lean` applies these facts to the arcs of a table.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.Arithmetic

/-- The first coordinate of the point of tangent `u` on the outer circle
`(a + 1/2)² + (b + 1/2)² = Q`. -/
def outerEndpointA (Q u : ℝ) : ℝ :=
  (-(u+1)+Real.sqrt ((u+1)^2+4*(1+u^2)*(Q-1/2)))/(2*(1+u^2))

/-- The first coordinate of the point of tangent `u` on the core corner
`(a - 1/2)² + (b - 1/2)² = (1/12)²`, the larger root. -/
def coreEndpointA (u : ℝ) : ℝ :=
  (u+1+Real.sqrt ((u+1)^2-(1+u^2)*(71/36)))/(2*(1+u^2))

/-- For `Q > 1/2` and `u ∈ [0, 1]`, the point `(a, u a)` with `a = outerEndpointA Q u` has
`a > 0` and `0 ≤ u a ≤ a`, and lies on the outer circle. -/
theorem outerEndpoint_facts {Q u : ℝ} (hQ : 1/2 < Q) (hu : 0 ≤ u ∧ u ≤ 1) :
    0 < outerEndpointA Q u ∧ 0 ≤ u*outerEndpointA Q u ∧
    u*outerEndpointA Q u ≤ outerEndpointA Q u ∧
    (outerEndpointA Q u+1/2)^2+(u*outerEndpointA Q u+1/2)^2=Q := by
  let d := (u+1)^2+4*(1+u^2)*(Q-1/2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hs : (Real.sqrt d)^2=d := Real.sq_sqrt hd.le
  have hroot : u+1 < Real.sqrt d := by
    have hp : 0 < 4*(1+u^2)*(Q-1/2) := by positivity
    dsimp [d] at hs
    nlinarith [Real.sqrt_nonneg d]
  have hden : 0 < 2*(1+u^2) := by positivity
  have ha : 0 < outerEndpointA Q u := div_pos (by linarith) hden
  refine ⟨ha,mul_nonneg hu.1 ha.le,?_,?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) ha.le]
  · have hid : outerEndpointA Q u*(2*(1+u^2)) = -(u+1)+Real.sqrt d := by
      dsimp [outerEndpointA,d]
      exact div_mul_cancel₀ _ (ne_of_gt hden)
    have hquad : (1+u^2)*(outerEndpointA Q u)^2+(u+1)*outerEndpointA Q u+1/2-Q=0 := by
      have hsq := congrArg (fun x : ℝ => x^2) hid
      dsimp [d] at hs
      have hid2 : 4*(1+u^2)*((1+u^2)*(outerEndpointA Q u)^2+
          (u+1)*outerEndpointA Q u+1/2-Q)=0 := by nlinarith
      exact (mul_eq_zero.mp hid2).resolve_left (by positivity)
    nlinarith only [hquad]

/-- For `u ∈ [6/7, 1]`, the point `(a, u a)` with `a = coreEndpointA u` has `a > 1/2` and
`1/2 ≤ u a ≤ a`, and lies on the core corner. -/
theorem coreEndpoint_facts {u : ℝ} (hu : 6/7 ≤ u ∧ u ≤ 1) :
    1/2 < coreEndpointA u ∧ 1/2 ≤ u*coreEndpointA u ∧
    u*coreEndpointA u ≤ coreEndpointA u ∧
    (coreEndpointA u-1/2)^2+(u*coreEndpointA u-1/2)^2=(1/12 : ℝ)^2 := by
  let d := (u+1)^2-(1+u^2)*(71/36)
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hfactor : 0 ≤ (7*u-6)*(6-5*u) := mul_nonneg (by linarith [hu.1]) (by linarith [hu.2])
  have hd : 0 < d := by dsimp [d]; nlinarith
  have hs := Real.sq_sqrt hd.le
  have hr := Real.sqrt_pos.mpr hd
  have hden : 0 < 2*(1+u^2) := by positivity
  have ha : 1/2 < coreEndpointA u := by
    apply (lt_div_iff₀ hden).mpr
    dsimp [d] at hr
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu.2)]
  have hb : 1/2 ≤ u*coreEndpointA u := by
    have hsq : (1-u)^2 ≤ (u*Real.sqrt d)^2 := by
      have hp := mul_nonneg (show 0 ≤ 1+u^2 by positivity) hfactor
      have he : (u*Real.sqrt d)^2-(1-u)^2=(1+u^2)*((7*u-6)*(6-5*u))/36 := by
        rw [mul_pow,hs]
        dsimp [d]
        ring
      nlinarith
    have hroot : 1-u ≤ u*Real.sqrt d := by nlinarith [mul_nonneg hu0 hr.le]
    unfold coreEndpointA
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hden).mpr
    nlinarith
  refine ⟨ha,hb,?_,?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (show 0 ≤ coreEndpointA u by linarith)]
  · have hid : coreEndpointA u*(2*(1+u^2)) = u+1+Real.sqrt d := by
      dsimp [coreEndpointA,d]
      exact div_mul_cancel₀ _ (ne_of_gt hden)
    have hquad : (1+u^2)*(coreEndpointA u)^2-(u+1)*coreEndpointA u+71/144=0 := by
      have hsq : (coreEndpointA u*(2*(1+u^2))-(u+1))^2 = d := by
        rw [hid,show u+1+Real.sqrt d-(u+1) = Real.sqrt d by ring,hs]
      dsimp [d] at hsq
      have hid2 : 4*(1+u^2)*((1+u^2)*(coreEndpointA u)^2-
          (u+1)*coreEndpointA u+71/144)=0 := by linear_combination hsq
      exact (mul_eq_zero.mp hid2).resolve_left (by positivity : (4:ℝ)*(1+u^2) ≠ 0)
    nlinarith only [hquad]

/-- A point of the circle with centre `(v, v)` and radius `ρ` to the right of the centre lies on
the branch `circleX`. -/
theorem circle_branch {v ρ a b : ℝ} (ha : v < a)
    (hc : (a-v)^2+(b-v)^2=ρ^2) : a = circleX v ρ b := by
  have he : ρ^2-(b-v)^2=(a-v)^2 := by nlinarith only [hc]
  rw [circleX,he,Real.sqrt_sq (sub_pos.mpr ha).le]
  ring

/-- On a circle with centre `(v, v)`, a point to the right of and above the centre with tangent
at least `t` has `b` at least that of the point `(a₀, t a₀)` of the circle to the right of the
centre. -/
theorem circle_tangent_lower {v ρ a b a₀ b₀ t : ℝ}
    (ha : 0 < a) (haV : v < a) (ha₀V : v < a₀) (hbV : v ≤ b) (ht : 0 ≤ t)
    (hpoint : b₀=t*a₀) (hl : t ≤ b/a)
    (hc : (a-v)^2+(b-v)^2=ρ^2) (hc₀ : (a₀-v)^2+(b₀-v)^2=ρ^2) :
    b₀ ≤ b := by
  have hcross : t*a ≤ b := (le_div_iff₀ ha).mp hl
  by_contra hh
  have hbb : b < b₀ := lt_of_not_ge hh
  have haa : a₀ ≤ a := by
    have hp := mul_nonneg (sub_pos.mpr hbb).le (show 0 ≤ b₀+b-2*v by linarith)
    nlinarith [hc,hc₀]
  have hm := mul_le_mul_of_nonneg_left haa ht
  rw [← hpoint] at hm
  linarith

/-- On a circle with centre `(v, v)`, a point to the right of the centre with tangent at most `t`
has `b` at most that of the point `(a₁, t a₁)` of the circle to the right of and above the
centre. -/
theorem circle_tangent_upper {v ρ a b a₁ b₁ t : ℝ}
    (ha : 0 < a) (haV : v < a) (ha₁V : v < a₁) (hb₁V : v ≤ b₁) (ht : 0 ≤ t)
    (hpoint : b₁=t*a₁) (hu : b/a ≤ t)
    (hc : (a-v)^2+(b-v)^2=ρ^2) (hc₁ : (a₁-v)^2+(b₁-v)^2=ρ^2) :
    b ≤ b₁ := by
  have hcross : b ≤ t*a := (div_le_iff₀ ha).mp hu
  by_contra hh
  have hbb : b₁ < b := lt_of_not_ge hh
  have haa : a ≤ a₁ := by
    have hp := mul_nonneg (sub_pos.mpr hbb).le (show 0 ≤ b+b₁-2*v by linarith)
    nlinarith [hc,hc₁]
  have hm := mul_le_mul_of_nonneg_left haa ht
  rw [← hpoint] at hm
  linarith

/-- The radicand `ρ² - (b - v)²` of `circleX` is positive for `b` from `l ≥ v` up to the second
coordinate `u` of a point `(aU, u)` of the circle to the right of the centre. -/
theorem circle_arc_radicand_positive {v ρ l u aU : ℝ}
    (hl : v ≤ l) (ha : v < aU)
    (hc : (aU-v)^2+(u-v)^2=ρ^2) :
    ∀ b ∈ Icc l u, 0 < ρ^2-(b-v)^2 := by
  intro b hb
  have hp := mul_nonneg (sub_nonneg.mpr hb.2) (show 0 ≤ u+b-2*v by linarith [hb.1,hb.2])
  have hsq := sq_pos_of_pos (sub_pos.mpr ha)
  nlinarith

end SquaresInCircles.Eight.Arithmetic
