module

public import SquaresInCircles.Eight.Arithmetic.ArcGeometry

/-!
# Proof-producing preparation of algebraic tangent endpoints

Only rational square-root brackets are additional data.  Endpoint coordinates
and slope ratios are fixed scalar expression trees.  Their real meanings are
proved below, so an interval is never accepted as an unexplained geometric
bound.
-/

@[expose] public section
open Set

namespace SquaresInCircles.Eight.Arithmetic

def closedBoxes : Fin 0 → QInterval := Fin.elim0
def closedEnv : Fin 0 → ℝ := Fin.elim0
def ScalarExpr.value (e : ScalarExpr 0) : ℝ := e.eval closedEnv

theorem ScalarExpr.closed_sound (e : ScalarExpr 0) (he : e.Valid closedBoxes) :
    (e.range closedBoxes).Mem e.value := e.sound closedBoxes he closedEnv (fun i => Fin.elim0 i)

def ArcData.side (a : ArcData) : Bool := !a.outer && decide (a.tangent.hi ≤ 6/7)
def ArcData.shift (a : ArcData) : ℚ := if a.outer then -1/2 else 1/2
def ArcData.endpointA (a : ArcData) (Q u : ℝ) : ℝ :=
  if a.outer then outerEndpointA Q u else if a.side then 7/12 else coreEndpointA u

def ArcData.WellFormed (a : ArcData) : Prop :=
  0 ≤ a.tangent.lo ∧ a.tangent.lo ≤ a.tangent.hi ∧ a.tangent.hi ≤ 1 ∧
  (a.outer = false → a.tangent.hi ≤ 6/7 ∨ 6/7 ≤ a.tangent.lo)

structure PreparedArc where
  data : ArcData
  radius : ℚ
  rootLo : QInterval
  rootHi : QInterval
  radiusRoot : QInterval
  deriving DecidableEq, Repr

instance : Inhabited PreparedArc := ⟨⟨default,0,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩

namespace PreparedArc

def discriminant (a : PreparedArc) (u : ℚ) : ℚ :=
  if a.data.outer then (u+1)^2+4*(1+u^2)*(a.radius-1/2)
  else (u+1)^2-(1+u^2)*(71/36)

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
def radiusExpr (a : PreparedArc) : ScalarExpr 0 :=
  if a.data.outer then .sqrt (.const a.radius) a.radiusRoot else .const (1/12)
def ratioLo (a : PreparedArc) : ScalarExpr 0 :=
  if a.data.side then .const 0 else
    .div (.sub a.bLo (.const a.data.shift)) (.sub a.aLo (.const a.data.shift))
def ratioHi (a : PreparedArc) : ScalarExpr 0 :=
  if a.data.side then .const 0 else
    .div (.sub a.bHi (.const a.data.shift)) (.sub a.aHi (.const a.data.shift))

def NumericValid (a : PreparedArc) : Prop :=
  a.data.WellFormed ∧ 1/2 < a.radius ∧
  a.aLo.Valid closedBoxes ∧ a.aHi.Valid closedBoxes ∧
  a.radiusExpr.Valid closedBoxes ∧
  (a.data.side = false → a.ratioLo.Valid closedBoxes ∧ a.ratioHi.Valid closedBoxes)

instance (a : PreparedArc) : Decidable a.NumericValid := by
  unfold NumericValid ArcData.WellFormed
  infer_instance

theorem endpointExpr_value (a : PreparedArc) (u : ℚ) (root : QInterval) :
    (a.endpointExpr u root).value = a.data.endpointA a.radius u := by
  cases ho : a.data.outer <;> simp [ArcData.side,ho] at *
  · by_cases hs : a.data.tangent.hi ≤ 6/7
    · simp [endpointExpr,ArcData.endpointA,ArcData.side,ho,hs,ScalarExpr.value,ScalarExpr.eval]
    · by_cases hu : u=6/7
      · subst u
        norm_num [endpointExpr,ArcData.endpointA,ArcData.side,ho,hs,ScalarExpr.value,
          ScalarExpr.eval,coreEndpointA]
      · simp [endpointExpr,ArcData.endpointA,ArcData.side,ho,hs,hu,ScalarExpr.value,
          ScalarExpr.div,ScalarExpr.eval,discriminant,coreEndpointA]
        push_cast
        ring
  · simp [endpointExpr,ArcData.endpointA,ArcData.side,ho,ScalarExpr.value,
      ScalarExpr.div,ScalarExpr.eval,discriminant,outerEndpointA]
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
  cases a.data.outer <;> simp [radiusExpr,ScalarExpr.value,ScalarExpr.eval]

def SupportDomain (a : PreparedArc) (x y : ℝ) : Prop :=
  a.bLo.value ≤ y ∧ y ≤ a.bHi.value ∧
    if a.data.side then x=7/12 else
      x=circleX a.data.shift a.radiusExpr.value y ∧
      (∀ z ∈ Icc a.bLo.value a.bHi.value,
        0 < a.radiusExpr.value^2-(z-(a.data.shift : ℝ))^2)

/-- The side branch maps tangent intervals to b-intervals by a constant scale. -/
theorem side_supportDomain {a : PreparedArc} (ha : a.NumericValid)
    (hs : a.data.side=true) {x y : ℝ} (hxy : a.data.Contains a.radius x y) :
    a.SupportDomain x y := by
  have ho : a.data.outer=false := by
    cases h : a.data.outer <;> simp [ArcData.side,h] at hs ⊢
  have hhi : a.data.tangent.hi ≤ 6/7 := by simpa [ArcData.side,ho] using hs
  have hx : x=7/12 := by simpa [ArcData.OnCurve,ho,hhi] using hxy.2.2.2.2
  have ht := hxy.2.2.2.1
  have hl := (le_div_iff₀ hxy.1).mp ht.1
  have hu := (div_le_iff₀ hxy.1).mp ht.2
  simp only [SupportDomain,hs,if_true]
  rw [bLo_value,bHi_value,aLo_value,aHi_value]
  simp only [ArcData.endpointA,ho,hs,Bool.false_eq_true,if_false,if_true]
  exact ⟨by nlinarith [hx],by nlinarith [hx],hx⟩

/-- Circular semantic facts are isolated as a proposition whose premises are
the explicit endpoint formulas, rather than interval-report fields. -/
structure CircleFacts (a : PreparedArc) (x y : ℝ) : Prop where
  x_pos : 0 < x
  lower_pos : 0 < a.aLo.value
  upper_pos : 0 < a.aHi.value
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

theorem circleFacts {a : PreparedArc} (ha : a.NumericValid)
    (hs : a.data.side=false) {x y : ℝ} (hxy : a.data.Contains a.radius x y) :
    a.CircleFacts x y := by
  have hlo0 : (0 : ℝ) ≤ a.data.tangent.lo := by exact_mod_cast ha.1.1
  have hlohi : (a.data.tangent.lo : ℝ) ≤ a.data.tangent.hi := by exact_mod_cast ha.1.2.1
  have hhi1 : (a.data.tangent.hi : ℝ) ≤ 1 := by exact_mod_cast ha.1.2.2.1
  have hQ : (1/2 : ℝ) < a.radius := by exact_mod_cast ha.2.1
  have hon := hxy.2.2.2.2
  cases ho : a.data.outer with
  | true =>
      have hL := outerEndpoint_facts hQ ⟨hlo0,hlohi.trans hhi1⟩
      have hU := outerEndpoint_facts hQ ⟨hlo0.trans hlohi,hhi1⟩
      have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ a.radius by linarith)
      simp only [ArcData.OnCurve,ho,if_true] at hon
      constructor <;>
        simp only [aLo_value,aHi_value,bLo_value,bHi_value,radiusExpr_value,
          ArcData.endpointA,ArcData.shift,ho,if_true] <;> push_cast <;>
        nlinarith [hxy.1,hxy.2.1,hL.1,hL.2.1,hL.2.2.2,
          hU.1,hU.2.1,hU.2.2.2,hon,hroot]
  | false =>
      have hbreak : ¬ a.data.tangent.hi ≤ 6/7 := by
        simpa [ArcData.side,ho] using hs
      have hlo : (6/7 : ℝ) ≤ a.data.tangent.lo := by
        exact_mod_cast (ha.1.2.2.2 ho).resolve_left hbreak
      have hL := coreEndpoint_facts ⟨hlo,hlohi.trans hhi1⟩
      have hU := coreEndpoint_facts ⟨hlo.trans hlohi,hhi1⟩
      simp only [ArcData.OnCurve,ho,if_false,hbreak] at hon
      have hxshift : 1/2 < x := by nlinarith [hon.1,hon.2,hxy.2.2.1]
      constructor <;>
        simp only [aLo_value,aHi_value,bLo_value,bHi_value,radiusExpr_value,
          ArcData.endpointA,ArcData.shift,ho,hs,if_false] <;> push_cast <;>
        nlinarith [hxy.1,hxy.2.1,hL.1,hL.2.1,hL.2.2.2,
          hU.1,hU.2.1,hU.2.2.2,hon.1,hon.2,hxshift]

theorem circular_supportDomain {a : PreparedArc} (ha : a.NumericValid)
    (hs : a.data.side=false) {x y : ℝ} (hxy : a.data.Contains a.radius x y)
    (hf : a.CircleFacts x y) : a.SupportDomain x y := by
  have hlo : (0 : ℝ) ≤ a.data.tangent.lo := by exact_mod_cast ha.1.1
  have hhi : (0 : ℝ) ≤ a.data.tangent.hi := by exact_mod_cast ha.1.1.trans ha.1.2.1
  have ht := hxy.2.2.2.1
  have hL := circle_tangent_lower hf.x_pos hf.lower_pos hf.x_shift hf.lower_shift
    hf.y_shift hf.lower_b_shift hlo (a.bLo_value) ht.1 hf.point_circle hf.lower_circle
  have hU := circle_tangent_upper hf.x_pos hf.upper_pos hf.x_shift hf.upper_shift
    hf.y_shift hf.upper_b_shift hhi (a.bHi_value) ht.2 hf.point_circle hf.upper_circle
  refine ⟨hL,hU,?_⟩
  simp only [hs,if_false]
  exact ⟨circle_branch hf.x_shift hf.point_circle,
    circle_arc_radicand_positive hf.lower_b_shift hf.upper_shift hf.upper_circle⟩

theorem supportDomain {a : PreparedArc} (ha : a.NumericValid)
    {x y : ℝ} (hxy : a.data.Contains a.radius x y) : a.SupportDomain x y := by
  cases hs : a.data.side with
  | true => exact side_supportDomain ha hs hxy
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

end PreparedArc
end SquaresInCircles.Eight.Arithmetic
