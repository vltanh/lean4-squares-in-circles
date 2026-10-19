module

public import SquaresInCircles.Eight.Arithmetic.ArcGeometry

/-!
# Eight squares: prepared arcs

A prepared arc (`PreparedArc`) is an arc of a table with the level `Q` and rational brackets of the
square roots in its endpoints. The coordinates of its endpoints (`aLo`, `bLo`, `aHi`, `bHi`), the
radius `ρ` of its circle (`radiusExpr`) and the ratios `(b - v) / (a - v)` at its endpoints
(`ratioLo`, `ratioHi`, zero on the core side) are closed scalar expressions (`ScalarExpr.lean`)
with these brackets, and their values are the exact numbers (`endpointExpr_value`, `aLo_value`,
`radiusExpr_value`). `NumericValid` collects the rational checks: the arc is well formed,
`Q > 1/2`, and the expressions are valid (`ScalarExpr.Valid`), that is, the brackets square to
bounds of their radicands and the denominators of the ratios are positive; then interval
evaluation encloses all these numbers.

The states of a valid prepared arc lie in its support domain (`supportDomain`): `b` between the
values at the endpoints, and either `a = 7/12` on the core side, or `a = circleX v ρ b` with a
positive radicand on a circular arc, where `(v, ρ)` is `(-1/2, √Q)` on the outer circle and
`(1/2, 1/12)` on the core corner (by `ArcGeometry.lean`). `ofArc` prepares an arc with brackets of
width `10⁻¹⁴` (`rootBracket`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.Arithmetic

def closedBoxes : Fin 0 → QInterval := Fin.elim0
def closedEnv : Fin 0 → ℝ := Fin.elim0
/-- The value of an expression without variables. -/
def ScalarExpr.value (e : ScalarExpr 0) : ℝ := e.eval closedEnv

theorem ScalarExpr.closed_sound (e : ScalarExpr 0) (he : e.Valid closedBoxes) :
    (e.range closedBoxes).Mem e.value := e.sound closedBoxes he closedEnv (fun i => Fin.elim0 i)

/-- The arc lies on the core side: a core arc with tangents up to `6/7`. -/
def ArcData.side (a : ArcData) : Bool := !a.outer && decide (a.tangent.hi ≤ 6/7)
/-- The coordinate `v` of the centre `(v, v)` of the circle of the arc: `-1/2` for the outer
circle, `1/2` for the core corner. -/
def ArcData.shift (a : ArcData) : ℚ := if a.outer then -1/2 else 1/2
/-- The first coordinate of the point of tangent `u` on the curve of the arc. -/
def ArcData.endpointA (a : ArcData) (Q u : ℝ) : ℝ :=
  if a.outer then outerEndpointA Q u else if a.side then 7/12 else coreEndpointA u

/-- The tangent interval of the arc lies in `[0, 1]`, and a core arc does not cross the
tangent `6/7`. -/
def ArcData.WellFormed (a : ArcData) : Prop :=
  0 ≤ a.tangent.lo ∧ a.tangent.lo ≤ a.tangent.hi ∧ a.tangent.hi ≤ 1 ∧
  (a.outer = false → a.tangent.hi ≤ 6/7 ∨ 6/7 ≤ a.tangent.lo)

/-- An arc with the level `Q` of its table and rational brackets of the square roots of the
discriminants at its two endpoints and, on the outer circle, of `Q`. -/
structure PreparedArc where
  data : ArcData
  radius : ℚ
  rootLo : QInterval
  rootHi : QInterval
  radiusRoot : QInterval

namespace PreparedArc

/-- The discriminant of the quadratic equation of the endpoint of tangent `u`. -/
def discriminant (a : PreparedArc) (u : ℚ) : ℚ :=
  if a.data.outer then (u+1)^2+4*(1+u^2)*(a.radius-1/2)
  else (u+1)^2-(1+u^2)*(71/36)

/-- The first coordinate of the endpoint of tangent `u`, with the bracket `root` of the square
root of the discriminant; the constant `7/12` on the core side and at the tangent `6/7` of the
corner. -/
def endpointExpr (a : PreparedArc) (u : ℚ) (root : QInterval) : ScalarExpr 0 :=
  if a.data.side then .const (7/12)
  else if a.data.outer=false ∧ u=6/7 then .const (7/12)
  else .div
    (.add (.const (if a.data.outer then -(u+1) else u+1))
      (.sqrt (.const (a.discriminant u)) root))
    (.const (2*(1+u^2)))

def aLo (a : PreparedArc) : ScalarExpr 0 := a.endpointExpr a.data.tangent.lo a.rootLo
def aHi (a : PreparedArc) : ScalarExpr 0 := a.endpointExpr a.data.tangent.hi a.rootHi
def bLo (a : PreparedArc) : ScalarExpr 0 := .mul (.const a.data.tangent.lo) a.aLo
def bHi (a : PreparedArc) : ScalarExpr 0 := .mul (.const a.data.tangent.hi) a.aHi
/-- The radius `ρ` of the circle of the arc: `√Q` for the outer circle, `1/12` for the core
corner. -/
def radiusExpr (a : PreparedArc) : ScalarExpr 0 :=
  if a.data.outer then .sqrt (.const a.radius) a.radiusRoot else .const (1/12)
/-- The ratio `(b - v) / (a - v)` at the lower endpoint, `0` on the core side; `ratioHi` is the
ratio at the upper endpoint. -/
def ratioLo (a : PreparedArc) : ScalarExpr 0 :=
  if a.data.side then .const 0 else
    .div (.sub a.bLo (.const a.data.shift)) (.sub a.aLo (.const a.data.shift))
def ratioHi (a : PreparedArc) : ScalarExpr 0 :=
  if a.data.side then .const 0 else
    .div (.sub a.bHi (.const a.data.shift)) (.sub a.aHi (.const a.data.shift))

/-- The rational checks of a prepared arc: the arc is well formed, `Q > 1/2`, and the expressions
of its endpoints, of its radius and, off the core side, of its ratios are valid. -/
def NumericValid (a : PreparedArc) : Prop :=
  a.data.WellFormed ∧ 1/2 < a.radius ∧
  a.aLo.Valid closedBoxes ∧ a.aHi.Valid closedBoxes ∧
  a.radiusExpr.Valid closedBoxes ∧
  (a.data.side = false → a.ratioLo.Valid closedBoxes ∧ a.ratioHi.Valid closedBoxes)

instance (a : PreparedArc) : Decidable a.NumericValid := by
  unfold NumericValid ArcData.WellFormed
  infer_instance

/-- The expression of an endpoint has the exact first coordinate as its value. -/
theorem endpointExpr_value (a : PreparedArc) (u : ℚ) (root : QInterval) :
    (a.endpointExpr u root).value = a.data.endpointA a.radius u := by
  cases ho : a.data.outer
  · by_cases hs : a.data.tangent.hi ≤ 6/7
    · have hside : a.data.side = true := by simp [ArcData.side,ho,hs]
      simp [endpointExpr,ArcData.endpointA,hside,ho,ScalarExpr.value,ScalarExpr.eval]
    · have hside : a.data.side = false := by simp [ArcData.side,ho,hs]
      by_cases hu : u=6/7
      · subst u
        have hsq : Real.sqrt (((6/7:ℝ)+1)^2-(1+(6/7:ℝ)^2)*(71/36)) = 1/6 := by
          rw [show ((6/7:ℝ)+1)^2-(1+(6/7:ℝ)^2)*(71/36) = (1/6)^2 by norm_num]
          exact Real.sqrt_sq (by norm_num)
        simp only [endpointExpr,ArcData.endpointA,hside,ho,ScalarExpr.value,
          ScalarExpr.eval,coreEndpointA,Bool.false_eq_true,ite_false,true_and,ite_true]
        push_cast
        rw [hsq]
        norm_num
      · simp only [endpointExpr,ArcData.endpointA,hside,ho,hu,ScalarExpr.value,
          ScalarExpr.div,ScalarExpr.eval,discriminant,coreEndpointA,Bool.false_eq_true,
          ↓reduceIte,and_false]
        push_cast
        ring
  · have hside : a.data.side = false := by simp [ArcData.side,ho]
    simp only [endpointExpr,ArcData.endpointA,hside,ho,ScalarExpr.value,
      ScalarExpr.div,ScalarExpr.eval,discriminant,outerEndpointA,Bool.false_eq_true,
      Bool.true_eq_false,↓reduceIte,false_and]
    push_cast
    ring

theorem aLo_value (a : PreparedArc) :
    a.aLo.value = a.data.endpointA a.radius a.data.tangent.lo := a.endpointExpr_value _ _
theorem aHi_value (a : PreparedArc) :
    a.aHi.value = a.data.endpointA a.radius a.data.tangent.hi := a.endpointExpr_value _ _
theorem bLo_value (a : PreparedArc) : a.bLo.value = (a.data.tangent.lo : ℝ)*a.aLo.value := rfl
theorem bHi_value (a : PreparedArc) : a.bHi.value = (a.data.tangent.hi : ℝ)*a.aHi.value := rfl

theorem radiusExpr_value (a : PreparedArc) :
    a.radiusExpr.value = if a.data.outer then Real.sqrt a.radius else 1/12 := by
  cases ho : a.data.outer <;> simp [radiusExpr,ho,ScalarExpr.value,ScalarExpr.eval]

/-- The support domain of the arc: `y` between the values of `b` at the endpoints, and `x = 7/12`
on the core side, or `x = circleX v ρ y` with the radicand positive between the endpoints. -/
def SupportDomain (a : PreparedArc) (x y : ℝ) : Prop :=
  a.bLo.value ≤ y ∧ y ≤ a.bHi.value ∧
    if a.data.side then x=7/12 else
      x=circleX a.data.shift a.radiusExpr.value y ∧
      (∀ z ∈ Icc a.bLo.value a.bHi.value,
        0 < a.radiusExpr.value^2-(z-(a.data.shift : ℝ))^2)

/-- On the core side every state of the arc lies in its support domain: there `a = 7/12`, and
`b` is `7/12` times the tangent. -/
theorem side_supportDomain {a : PreparedArc} (hs : a.data.side=true) {x y : ℝ} (hxy : a.data.Contains a.radius x y) :
    a.SupportDomain x y := by
  have ho : a.data.outer=false := by
    cases h : a.data.outer <;> simp [ArcData.side,h] at hs ⊢
  have hhi : a.data.tangent.hi ≤ 6/7 := by simpa [ArcData.side,ho] using hs
  have hx : x=7/12 := by
    have hon := hxy.2.2.2.2
    simp only [ArcData.OnCurve,ho,hhi,Bool.false_eq_true,ite_false,ite_true] at hon
    exact hon.1
  have ht := hxy.2.2.2.1
  have hl := (le_div_iff₀ hxy.1).mp ht.1
  have hu := (div_le_iff₀ hxy.1).mp ht.2
  simp only [SupportDomain,hs,ite_true]
  rw [bLo_value,bHi_value,aLo_value,aHi_value]
  simp only [ArcData.endpointA,ho,hs,Bool.false_eq_true,ite_false,ite_true]
  rw [hx] at hl hu
  exact ⟨by linarith,by linarith,hx⟩

/-- The facts about a state `(x, y)` of a circular arc and the endpoints that the support bounds
use: the three points lie on the circle, strictly to the right of the centre `(v, v)` and not below
it, and `x > 0`. -/
structure CircleFacts (a : PreparedArc) (x y : ℝ) : Prop where
  x_pos : 0 < x
  x_shift : (a.data.shift : ℝ) < x
  lower_shift : (a.data.shift : ℝ) < a.aLo.value
  upper_shift : (a.data.shift : ℝ) < a.aHi.value
  y_shift : (a.data.shift : ℝ) ≤ y
  lower_b_shift : (a.data.shift : ℝ) ≤ a.bLo.value
  upper_b_shift : (a.data.shift : ℝ) ≤ a.bHi.value
  point_circle : (x-(a.data.shift : ℝ))^2+(y-(a.data.shift : ℝ))^2=a.radiusExpr.value^2
  lower_circle : (a.aLo.value-(a.data.shift : ℝ))^2+
    (a.bLo.value-(a.data.shift : ℝ))^2=a.radiusExpr.value^2
  upper_circle : (a.aHi.value-(a.data.shift : ℝ))^2+
    (a.bHi.value-(a.data.shift : ℝ))^2=a.radiusExpr.value^2

/-- A state of a valid circular arc satisfies `CircleFacts`. -/
theorem circleFacts {a : PreparedArc} (ha : a.NumericValid)
    (hs : a.data.side=false) {x y : ℝ} (hxy : a.data.Contains a.radius x y) :
    a.CircleFacts x y := by
  have hlo0 : (0 : ℝ) ≤ a.data.tangent.lo := by exact_mod_cast ha.1.1
  have hlohi : (a.data.tangent.lo : ℝ) ≤ a.data.tangent.hi := by exact_mod_cast ha.1.2.1
  have hhi1 : (a.data.tangent.hi : ℝ) ≤ 1 := by exact_mod_cast ha.1.2.2.1
  have hQ : (1/2 : ℝ) < a.radius := by
    have h := (Rat.cast_lt (K := ℝ)).mpr ha.2.1
    rw [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
    exact h
  have hon := hxy.2.2.2.2
  have hx0 := hxy.1
  have hy0 := hxy.2.1
  cases ho : a.data.outer with
  | true =>
      have hL := outerEndpoint_facts hQ ⟨hlo0,hlohi.trans hhi1⟩
      have hU := outerEndpoint_facts hQ ⟨hlo0.trans hlohi,hhi1⟩
      have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ a.radius by linarith)
      simp only [ArcData.OnCurve,ho,ite_true] at hon
      have hsh : ((a.data.shift : ℚ) : ℝ) = -1/2 := by
        simp [ArcData.shift,ho]
      have hA : ∀ u : ℝ, a.data.endpointA a.radius u = outerEndpointA a.radius u := by
        intro u; simp [ArcData.endpointA,ho]
      have hR : a.radiusExpr.value = Real.sqrt a.radius := by
        simp [radiusExpr_value,ho]
      refine ⟨hx0,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
        simp only [bLo_value,bHi_value,aLo_value,aHi_value,hsh,hA,hR,hroot]
      · linarith
      · linarith [hL.1]
      · linarith [hU.1]
      · linarith
      · linarith [hL.2.1]
      · linarith [hU.2.1]
      · linarith [hon]
      · linarith [hL.2.2.2]
      · linarith [hU.2.2.2]
  | false =>
      have hbreak : ¬ a.data.tangent.hi ≤ 6/7 := by
        simpa [ArcData.side,ho] using hs
      have hlo : (6/7 : ℝ) ≤ a.data.tangent.lo := by
        have h := (Rat.cast_le (K := ℝ)).mpr ((ha.1.2.2.2 ho).resolve_left hbreak)
        rw [Rat.cast_div,Rat.cast_ofNat,Rat.cast_ofNat] at h
        exact h
      have hL := coreEndpoint_facts ⟨hlo,hlohi.trans hhi1⟩
      have hU := coreEndpoint_facts ⟨hlo.trans hlohi,hhi1⟩
      simp only [ArcData.OnCurve,ho,hbreak,Bool.false_eq_true,ite_false] at hon
      have hxshift : 1/2 < x := by nlinarith [hon.1,hon.2,hxy.2.2.1]
      have hsh : ((a.data.shift : ℚ) : ℝ) = 1/2 := by
        simp [ArcData.shift,ho]
      have hA : ∀ u : ℝ, a.data.endpointA a.radius u = coreEndpointA u := by
        intro u; simp [ArcData.endpointA,ho,hs]
      have hR : a.radiusExpr.value = 1/12 := by
        simp [radiusExpr_value,ho]
      refine ⟨hx0,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
        simp only [bLo_value,bHi_value,aLo_value,aHi_value,hsh,hA,hR]
      · exact hxshift
      · exact hL.1
      · exact hU.1
      · exact hon.1
      · exact hL.2.1
      · exact hU.2.1
      · linarith [hon.2]
      · linarith [hL.2.2.2]
      · linarith [hU.2.2.2]

theorem circular_supportDomain {a : PreparedArc} (ha : a.NumericValid)
    (hs : a.data.side=false) {x y : ℝ} (hxy : a.data.Contains a.radius x y)
    (hf : a.CircleFacts x y) : a.SupportDomain x y := by
  have hlo : (0 : ℝ) ≤ a.data.tangent.lo := by exact_mod_cast ha.1.1
  have hhi : (0 : ℝ) ≤ a.data.tangent.hi := by exact_mod_cast ha.1.1.trans ha.1.2.1
  have ht := hxy.2.2.2.1
  have hL := circle_tangent_lower hf.x_pos hf.x_shift hf.lower_shift hf.y_shift hlo
    (a.bLo_value) ht.1 hf.point_circle hf.lower_circle
  have hU := circle_tangent_upper hf.x_pos hf.x_shift hf.upper_shift hf.upper_b_shift hhi
    (a.bHi_value) ht.2 hf.point_circle hf.upper_circle
  refine ⟨hL,hU,?_⟩
  simp only [hs]
  exact ⟨circle_branch hf.x_shift hf.point_circle,
    circle_arc_radicand_positive hf.lower_b_shift hf.upper_shift hf.upper_circle⟩

/-- Every state of a valid prepared arc lies in its support domain. -/
theorem supportDomain {a : PreparedArc} (ha : a.NumericValid)
    {x y : ℝ} (hxy : a.data.Contains a.radius x y) : a.SupportDomain x y := by
  cases hs : a.data.side with
  | true => exact side_supportDomain hs hxy
  | false => exact circular_supportDomain ha hs hxy (circleFacts ha hs hxy)

theorem bLo_valid {a : PreparedArc} (ha : a.NumericValid) : a.bLo.Valid closedBoxes :=
  ⟨True.intro,ha.2.2.1⟩
theorem bHi_valid {a : PreparedArc} (ha : a.NumericValid) : a.bHi.Valid closedBoxes :=
  ⟨True.intro,ha.2.2.2.1⟩

theorem ratioLo_valid {a : PreparedArc} (ha : a.NumericValid) : a.ratioLo.Valid closedBoxes := by
  cases hs : a.data.side with
  | false => exact (ha.2.2.2.2.2 hs).1
  | true => simp [ratioLo,hs,ScalarExpr.Valid]

theorem ratioHi_valid {a : PreparedArc} (ha : a.NumericValid) : a.ratioHi.Valid closedBoxes := by
  cases hs : a.data.side with
  | false => exact (ha.2.2.2.2.2 hs).2
  | true => simp [ratioHi,hs,ScalarExpr.Valid]

/-- The precision of the square-root brackets. -/
def rootScale : ℕ := 10 ^ 14

/-- A bracket `[k, k + 1] / 10¹⁴` of `√x`, with `k = ⌊10¹⁴ √x⌋`; `NumericValid` checks that it
encloses the root. -/
def rootBracket (x : ℚ) : QInterval :=
  let k := Nat.sqrt ((x.num.toNat * rootScale ^ 2) / x.den)
  ⟨(k : ℚ) / rootScale, ((k + 1 : ℕ) : ℚ) / rootScale⟩

/-- The prepared arc of an arc of a table at the level `Q`: off the core side, the brackets of
the square roots of the discriminants at its two endpoints and, on the outer circle, of `Q`. -/
def ofArc (Q : ℚ) (a : ArcData) : PreparedArc :=
  let p : PreparedArc := ⟨a, Q, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩⟩
  if a.side then p else
    { p with
      rootLo := rootBracket (p.discriminant a.tangent.lo)
      rootHi := rootBracket (p.discriminant a.tangent.hi)
      radiusRoot := if a.outer then rootBracket Q else ⟨0,0⟩ }

end PreparedArc
end SquaresInCircles.Eight.Arithmetic
