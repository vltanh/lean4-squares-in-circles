module

public import SquaresInCircles.Eight.Arithmetic.FourTypeProblems
public import SquaresInCircles.Eight.Generated.PairsFourType
public import SquaresInCircles.Eight.Arithmetic.CorePairGeometry

/-!
# Eight squares: the four-type pair bounds

Each vertex of a boundary cycle at the squared radius `Q₀` receives a branch (`branchOf`): its
core chart, or on the outer circle the low, middle or high range of its tangent `b / a`, cut at
`1/4` and `3/7`; the type of the branch is `0` for the core and `1`, `2`, `3` for the three
ranges. The marker of the vertex is `ψᵢ = αᵢ - σᵢ L(aᵢ, bᵢ)`, with the label `L` of its branch
(`label`), and serves both of its edges. Every edge then satisfies
`handGamma τᵢ τᵢ₊₁ < angleGap β i - (9/50) h(θᵢ₊₁ - θᵢ) + ψᵢ₊₁ - ψᵢ`, indices modulo `7`, for
the types `τ`, the frame charge `h` (`periodicFrameCost`) and the canonical angles `θ`
(`four_type_pair_bound`). `GlobalNormalization.lean` sums these bounds around the cycle
(`physical_cycle_width_bound` in `Frames.lean`) to bound the total frame charge.

A vertex is a `State`: a branch, a sign and a point of the chart of the branch with `b ≤ a` and
the tangent in the closed range of the branch. When one of two states is outer, the pair
inequality `handGamma < State.cost` holds for every frame angle difference `φ ∈ [-1, 4]` with the
gap `19/25 ≤ φ + α_s - α_t ≤ 3π/4` and a nonnegative margin of a separating axis (`pair`). For
the axes one and four it is a problem `fourTypeProblem` (`FourTypeProblems.lean`) of the pair
table of the two branches (`fourTypeTable`, `Generated/Pairs/`), proved on the six halves of
`φ ∈ [-1, 4]` (`source_pair`); the labels with `√(Q₀ - 1/4)`, `√(Q₀/2)` and `π` enter it through
the rational brackets of their constants (`branchConst_mem`). The axes two and three are the axes
four and one of the reversed edge with both signs flipped. An edge between two core vertices
follows instead from `CorePairGeometry.core_cost` and the bound of the frame charge
(`cycle_pair`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.Arithmetic.FourType

/-- The range of `b` on the chart of a branch. -/
def Branch.bBox : Branch → QInterval
  | .coreSide => ⟨0,1/2⟩
  | .coreCorner => ⟨1/2,14/25⟩
  | .low | .middle | .high => ⟨0,9/10⟩

/-- The sign `1` or `-1` of a vertex, as a real number. -/
def sign (positive : Bool) : ℝ := if positive then 1 else -1

@[simp] theorem sign_not (p : Bool) : sign (!p)= -sign p := by
  cases p <;> norm_num [sign]

/-- The coordinate `a` of the point of the chart of a branch with the coordinate `b`. -/
noncomputable def radialA (s : Branch) (b : ℝ) : ℝ :=
  match s with
  | .coreSide => 7/12
  | .coreCorner => 1/2+Real.sqrt ((1/12:ℝ)^2-(b-1/2)^2)
  | .low | .middle | .high => Real.sqrt (Q0-(b+1/2)^2)-1/2

/-- The coordinate `a` of the point of the outer circle with `b = 0`. -/
noncomputable def a0 : ℝ := Real.sqrt (Q0-1/4)-1/2
/-- The coordinates `a = b` of the point of the outer circle on the diagonal. -/
noncomputable def c0 : ℝ := Real.sqrt (Q0/2)-1/2

/-- The label of a branch for the sign `+1`, constant included: the core label
`K (7/12 - a) + g b` of `CorePairGeometry.lean` on the two core charts and an affine function of
`(a, b)` on each outer range. -/
noncomputable def label (s : Branch) (a b : ℝ) : ℝ :=
  match s with
  | .coreSide | .coreCorner => (7506931/1000000)*(7/12-a)+(269343/250000)*b
  | .low => (3231/8000)*(a-a0)+(217813/200000)*b
  | .middle => -85723/40000+(1489593/1000000)*a+(1580219/1000000)*b
  | .high => Real.pi/4-(8898/15625)*(a-c0)+(195443/500000)*(b-c0)

/-- The closed tangent range of a branch, multiplied by `a`: `4b ≤ a` on the low range, `a ≤ 4b`
and `7b ≤ 3a` on the middle one, `3a ≤ 7b` on the high one, and no condition on the core
charts. -/
def TypeMem (s : Branch) (a b : ℝ) : Prop :=
  match s with
  | .coreSide | .coreCorner => True
  | .low => 4*b ≤ a
  | .middle => a ≤ 4*b ∧ 7*b ≤ 3*a
  | .high => 3*a ≤ 7*b

/-- The index of the axis of a source problem: `3` for the axis four, `0` for the axis one. -/
def sourceAxis (four : Bool) : Fin 4 := if four then 3 else 0

@[simp] theorem gammaQ_cast (s t : Branch) :
    (gammaQ s t : ℝ)=handGamma s.type t.type := by
  simp [gammaQ,handGamma]

/-- A vertex: a branch, a sign and a point `(a, b)` of the chart of the branch, given by `b`
(`radialA`), with `b ≤ a` and the tangent in the closed range of the branch. -/
structure State where
  branch : Branch
  positive : Bool
  a : ℝ
  b : ℝ
  a_eq : a=radialA branch b
  b_mem : branch.bBox.Mem b
  canonical : b ≤ a
  type_mem : TypeMem branch a b

/-- The state with the opposite sign. -/
def State.flip (s : State) : State := { s with positive := !s.positive }

/-- The angle `σ arctan (b / a)` from the centre direction of the square to its frame
(`BoundaryCycle.alpha`). -/
noncomputable def State.offset (s : State) : ℝ := sign s.positive*Real.arctan (s.b/s.a)
/-- The signed label `σ L(a, b)` of the state. -/
noncomputable def State.signedLabel (s : State) : ℝ := sign s.positive*label s.branch s.a s.b
/-- The angle `φ + α_s - α_t` between the centre directions of two squares whose frames differ by
`φ`. -/
noncomputable def State.gap (s t : State) (φ : ℝ) : ℝ := φ+s.offset-t.offset
/-- The charged cost `φ - (9/50) h(φ) + σ_s L_s - σ_t L_t` of an edge, with the frame charge
`h`. -/
noncomputable def State.cost (s t : State) (φ : ℝ) : ℝ :=
  φ-(9/50)*periodicFrameCost φ+s.signedLabel-t.signedLabel

@[simp] theorem State.flip_offset (s : State) : s.flip.offset= -s.offset := by
  simp [State.flip,State.offset]

@[simp] theorem State.flip_label (s : State) : s.flip.signedLabel= -s.signedLabel := by
  simp [State.flip,State.signedLabel]

@[simp] theorem State.reverse_gap (s t : State) (φ : ℝ) :
    t.flip.gap s.flip φ=s.gap t φ := by
  simp [State.gap]
  ring

@[simp] theorem State.reverse_cost (s t : State) (φ : ℝ) :
    t.flip.cost s.flip φ=s.cost t φ := by
  simp [State.cost]
  ring

/-- The four-type matrix is symmetric. -/
theorem gamma_symmetric (s t : Branch) :
    handGamma t.type s.type=handGamma s.type t.type := by
  cases s <;> cases t <;> norm_num [Branch.type,handGamma,handGammaNumerator]

/-! ### The pair tables -/

section Tables

open PairCover

theorem a0_bounds : (rootA0Lo : ℝ) - 1/2 ≤ a0 ∧ a0 ≤ (rootA0Hi : ℝ) - 1/2 := by
  have h1 : (rootA0Lo : ℝ) ≤ Real.sqrt (Q0 - 1/4) :=
    Real.le_sqrt_of_sq_le (by norm_num [rootA0Lo, Q0])
  have h2 : Real.sqrt (Q0 - 1/4) ≤ rootA0Hi :=
    Real.sqrt_le_iff.mpr ⟨by norm_num [rootA0Hi], by norm_num [rootA0Hi, Q0]⟩
  unfold a0
  constructor <;> linarith

theorem c0_bounds : (rootC0Lo : ℝ) - 1/2 ≤ c0 ∧ c0 ≤ (rootC0Hi : ℝ) - 1/2 := by
  have h1 : (rootC0Lo : ℝ) ≤ Real.sqrt (Q0 / 2) :=
    Real.le_sqrt_of_sq_le (by norm_num [rootC0Lo, Q0])
  have h2 : Real.sqrt (Q0 / 2) ≤ rootC0Hi :=
    Real.sqrt_le_iff.mpr ⟨by norm_num [rootC0Hi], by norm_num [rootC0Hi, Q0]⟩
  unfold c0
  constructor <;> linarith

theorem pi_bounds : (piLo : ℝ) ≤ Real.pi ∧ Real.pi ≤ piHi := by
  have h := pi_hand_enclosure
  constructor <;> norm_num [piLo, piHi] <;> linarith [h.1, h.2]

/-- The constant of the positive label of a branch. -/
noncomputable def branchConst : Branch → ℝ
  | .coreSide | .coreCorner => 7506931/1000000*(7/12)
  | .low => -(3231/8000)*a0
  | .middle => -85723/40000
  | .high => Real.pi/4+(8898/15625-195443/500000)*c0

/-- The label of a branch is `branchQuad` with the constant `branchConst`. -/
theorem label_eq (s : Branch) (a b : ℝ) : label s a b = (branchQuad s).eval (branchConst s) a b := by
  cases s <;> simp only [label, branchQuad, branchConst, QuadLabel.eval] <;> push_cast <;> ring

/-- The rational bracket of `branchQuad` contains the constant of the label. -/
theorem branchConst_mem (s : Branch) :
    ((branchQuad s).cLo : ℝ) ≤ branchConst s ∧ branchConst s ≤ (branchQuad s).cHi := by
  have ha := a0_bounds
  have hc := c0_bounds
  have hp := pi_bounds
  cases s <;> simp only [branchQuad,
    branchConst] <;> push_cast <;> constructor <;> linarith only [ha, hc, hp]

/-- The problems of the pair table of an ordered pair of branches; none for two core
branches. -/
def fourTypeTable : Branch → Branch → List PairProblem
  | .coreSide, .coreSide | .coreSide, .coreCorner | .coreCorner, .coreSide
  | .coreCorner, .coreCorner => []
  | .coreSide, .low => Generated.Pairs.FourTypeCoreSideLow.problems
  | .coreSide, .middle => Generated.Pairs.FourTypeCoreSideMiddle.problems
  | .coreSide, .high => Generated.Pairs.FourTypeCoreSideHigh.problems
  | .coreCorner, .low => Generated.Pairs.FourTypeCoreCornerLow.problems
  | .coreCorner, .middle => Generated.Pairs.FourTypeCoreCornerMiddle.problems
  | .coreCorner, .high => Generated.Pairs.FourTypeCoreCornerHigh.problems
  | .low, .coreSide => Generated.Pairs.FourTypeLowCoreSide.problems
  | .low, .coreCorner => Generated.Pairs.FourTypeLowCoreCorner.problems
  | .low, .low => Generated.Pairs.FourTypeLowLow.problems
  | .low, .middle => Generated.Pairs.FourTypeLowMiddle.problems
  | .low, .high => Generated.Pairs.FourTypeLowHigh.problems
  | .middle, .coreSide => Generated.Pairs.FourTypeMiddleCoreSide.problems
  | .middle, .coreCorner => Generated.Pairs.FourTypeMiddleCoreCorner.problems
  | .middle, .low => Generated.Pairs.FourTypeMiddleLow.problems
  | .middle, .middle => Generated.Pairs.FourTypeMiddleMiddle.problems
  | .middle, .high => Generated.Pairs.FourTypeMiddleHigh.problems
  | .high, .coreSide => Generated.Pairs.FourTypeHighCoreSide.problems
  | .high, .coreCorner => Generated.Pairs.FourTypeHighCoreCorner.problems
  | .high, .low => Generated.Pairs.FourTypeHighLow.problems
  | .high, .middle => Generated.Pairs.FourTypeHighMiddle.problems
  | .high, .high => Generated.Pairs.FourTypeHighHigh.problems

/-- Every problem of a pair table holds. -/
theorem fourTypeTable_holds (s t : Branch) :
    ∀ P ∈ fourTypeTable s t, P.Holds ((9789/2500 : ℚ) : ℝ) 100000000 := by
  cases s <;> cases t
  · simp [fourTypeTable]
  · simp [fourTypeTable]
  · exact Generated.Pairs.FourTypeCoreSideLow.sound
  · exact Generated.Pairs.FourTypeCoreSideMiddle.sound
  · exact Generated.Pairs.FourTypeCoreSideHigh.sound
  · simp [fourTypeTable]
  · simp [fourTypeTable]
  · exact Generated.Pairs.FourTypeCoreCornerLow.sound
  · exact Generated.Pairs.FourTypeCoreCornerMiddle.sound
  · exact Generated.Pairs.FourTypeCoreCornerHigh.sound
  · exact Generated.Pairs.FourTypeLowCoreSide.sound
  · exact Generated.Pairs.FourTypeLowCoreCorner.sound
  · exact Generated.Pairs.FourTypeLowLow.sound
  · exact Generated.Pairs.FourTypeLowMiddle.sound
  · exact Generated.Pairs.FourTypeLowHigh.sound
  · exact Generated.Pairs.FourTypeMiddleCoreSide.sound
  · exact Generated.Pairs.FourTypeMiddleCoreCorner.sound
  · exact Generated.Pairs.FourTypeMiddleLow.sound
  · exact Generated.Pairs.FourTypeMiddleMiddle.sound
  · exact Generated.Pairs.FourTypeMiddleHigh.sound
  · exact Generated.Pairs.FourTypeHighCoreSide.sound
  · exact Generated.Pairs.FourTypeHighCoreCorner.sound
  · exact Generated.Pairs.FourTypeHighLow.sound
  · exact Generated.Pairs.FourTypeHighMiddle.sound
  · exact Generated.Pairs.FourTypeHighHigh.sound

/-- Each problem is in its table, as the image of its signs and source axis: the table is
`fourTypeProblem s t` mapped over `fourTypeCases`. -/
theorem fourTypeProblem_mem : ∀ s t : Branch, ∀ σ τ four : Bool, s.type ≠ 0 ∨ t.type ≠ 0 →
    fourTypeProblem s t σ τ four ∈ fourTypeTable s t := by
  intro s t σ τ four h
  have hc := List.mem_map_of_mem (f := fun c : Bool × Bool × Bool =>
    fourTypeProblem s t c.1 c.2.1 c.2.2) (mem_fourTypeCases (σ, τ, four))
  cases s <;> cases t <;> first | exact absurd h (by decide) | exact hc

/-- Every `φ ∈ [-1, 4]` is `k π / 2 ± u` on one of the six halves. -/
theorem four_type_half {φ : ℝ} (hφ : -1 ≤ φ ∧ φ ≤ 4) :
    ∃ hv ∈ fourTypeHalves, ∃ u : ℝ, 0 ≤ u ∧ u ≤ (hv.2.2 : ℝ) / ((100000000 : ℕ) : ℝ) ∧
      phiOf hv.1 hv.2.1 u = φ := by
  have hpi := pi_bounds
  have h1 : (piLo : ℝ) = 3141592653589793238 / 10 ^ 18 := by norm_num [piLo]
  have h2 : (piHi : ℝ) = 3141592653589793239 / 10 ^ 18 := by norm_num [piHi]
  rw [h1, h2] at hpi
  simp only [fourTypeHalves, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, phiOf, sgnR, Bool.false_eq_true, ↓reduceIte]
  push_cast
  by_cases h0 : φ ≤ 0
  · exact Or.inl ⟨-φ, by linarith only [h0], by linarith only [hφ], by ring⟩
  by_cases h45 : φ ≤ 4/5
  · exact Or.inr (Or.inl ⟨φ, by linarith only [h0], by linarith only [h45], by ring⟩)
  by_cases hp2 : φ ≤ Real.pi / 2
  · exact Or.inr (Or.inr (Or.inl ⟨Real.pi / 2 - φ, by linarith only [hp2],
    by linarith only [hpi, h0, h45], by ring⟩))
  by_cases hp3 : φ ≤ Real.pi / 2 + 4/5
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨φ - Real.pi / 2, by linarith only [hp2],
    by linarith only [hp3], by ring⟩)))
  by_cases hp4 : φ ≤ Real.pi
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨Real.pi - φ, by linarith only [hp4], by linarith only [hpi, hp3], by ring⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨φ - Real.pi, by linarith only [hp4], by linarith only [hφ, hpi, hp4], by ring⟩))))

/-- A state is a point of the chart of its branch, with its tangent in the branch range. -/
theorem state_mem (s : State) :
    (branchEnd s.branch s.positive).Mem ((9789/2500 : ℚ) : ℝ) s.branch.range s.a s.b := by
  have ha := s.a_eq
  have hb := s.b_mem
  have hba := s.canonical
  have ht := s.type_mem
  have hQ : ((9789/2500 : ℚ) : ℝ) = Q0 := by norm_num [Q0]
  rw [hQ]
  simp only [PairEnd.Mem, PairEnd.OnCurve, branchEnd, QInterval.Mem]
  cases hs : s.branch <;>
    simp only [hs, radialA, Branch.bBox, Branch.outer, Branch.side, Branch.range, TypeMem,
      QInterval.Mem, Bool.false_eq_true, ↓reduceIte] at ha hb ht ⊢ <;> push_cast at hb ⊢
  · -- the core side
    have hpos : 0 < s.a := by rw [ha]; norm_num
    refine ⟨hpos, hb.1, hba, ⟨div_nonneg hb.1 hpos.le, ?_⟩, ha, hb.2⟩
    rw [div_le_iff₀ hpos, ha]
    linarith only [hb.2]
  · -- the core corner
    have hr : 0 ≤ (1/12 : ℝ)^2 - (s.b - 1/2)^2 := by nlinarith only [hb.1, hb.2]
    have hsq := Real.sq_sqrt hr
    have hs0 := Real.sqrt_nonneg ((1/12 : ℝ)^2 - (s.b - 1/2)^2)
    have hsle : Real.sqrt ((1/12 : ℝ)^2 - (s.b - 1/2)^2) ≤ 1/12 := by
      rw [Real.sqrt_le_left (by norm_num)]
      nlinarith only []
    have hpos : 0 < s.a := by rw [ha]; linarith only [hba, ha, hb]
    refine ⟨hpos, by linarith only [hb.1], hba, ⟨?_, ?_⟩, hb.1, ?_⟩
    · rw [le_div_iff₀ hpos]
      linarith only [hb.1, ha, hsle]
    · rw [div_le_iff₀ hpos]
      linarith only [hba]
    · rw [ha]
      linarith only [hsq]
  all_goals
    have hr : 0 ≤ Q0 - (s.b + 1/2)^2 := by norm_num [Q0]; nlinarith only [hb.1, hb.2, ht, hba]
    have hsq := Real.sq_sqrt hr
    have hs0 := Real.sqrt_nonneg (Q0 - (s.b + 1/2)^2)
    have hlow : (139/100 : ℝ) ≤ Real.sqrt (Q0 - (s.b + 1/2)^2) := by
      apply Real.le_sqrt_of_sq_le
      norm_num [Q0]
      nlinarith only [hb.1, hb.2, hba, hQ, ha, hsq, ht]
    have hpos : 0 < s.a := by rw [ha]; linarith only [hlow]
    refine ⟨hpos, hb.1, hba, ⟨?_, ?_⟩, ?_⟩
  -- low
  · exact div_nonneg hb.1 hpos.le
  · rw [div_le_iff₀ hpos]; linarith only [ht]
  · rw [ha]; linarith only [hsq]
  -- middle
  · rw [le_div_iff₀ hpos]; linarith only [ht.1]
  · rw [div_le_iff₀ hpos]; linarith only [ht.2]
  · rw [ha]; linarith only [hsq]
  -- high
  · rw [le_div_iff₀ hpos]; linarith only [ht]
  · rw [div_le_iff₀ hpos]; linarith only [hba]
  · rw [ha]; linarith only [hsq]

end Tables

/-- The pair inequality for the axes one and four, when one of the branches is outer, from the
pair table of the two branches. -/
theorem source_pair (s t : State) (four : Bool) (φ : ℝ)
    (hφ : -1 ≤ φ ∧ φ ≤ 4)
    (hgap : 19/25 ≤ s.gap t φ ∧ s.gap t φ ≤ 3*Real.pi/4)
    (haxis : 0 ≤ SquaresInCircles.Eight.forwardMargin (sourceAxis four)
      s.a s.b t.a t.b (sign s.positive) (sign t.positive) φ)
    (hnon : s.branch.type ≠ 0 ∨ t.branch.type ≠ 0) :
    handGamma s.branch.type t.branch.type < s.cost t φ := by
  obtain ⟨hv, hmem, u, hu0, hu1, hphi⟩ := four_type_half hφ
  have hP := fourTypeTable_holds s.branch t.branch _
    (fourTypeProblem_mem s.branch t.branch s.positive t.positive four hnon)
  have hcs := QuadLabel.signed_bounds (branchConst_mem s.branch) s.positive
  have hct := QuadLabel.signed_bounds (branchConst_mem t.branch) t.positive
  have hc := hP hv hmem (sgnR s.positive * branchConst s.branch)
    (sgnR t.positive * branchConst t.branch) hcs.1 hct.2 s.a s.b t.a t.b u (state_mem s)
    (state_mem t) (by simpa using hu0) hu1
  have hσ : sgnR s.positive = sign s.positive := rfl
  have hτ : sgnR t.positive = sign t.positive := rfl
  simp only [fourTypeProblem, branchEnd, PairCover.PairProblem.gap, hphi] at hc
  have hgap' : 19/25 ≤ φ + sign s.positive * Real.arctan (s.b / s.a) -
      sign t.positive * Real.arctan (t.b / t.a) := hgap.1
  have hgap'' : φ + sign s.positive * Real.arctan (s.b / s.a) -
      sign t.positive * Real.arctan (t.b / t.a) ≤ 3 * Real.pi / 4 := hgap.2
  have hmargin : 0 ≤ forwardMargin (if four then ForwardAxis.four else ForwardAxis.one)
      (sign s.positive) (sign t.positive) s.a s.b t.a t.b φ := by
    rw [forwardMargin_actual]
    cases four <;> exact haxis
  rw [hσ, hτ] at hc
  have h := hc hgap' hgap'' hmargin
  rw [← hσ, ← hτ, QuadLabel.signed_eval, QuadLabel.signed_eval, ← label_eq, ← label_eq,
    gammaQ_cast, hσ, hτ] at h
  have hframe : frameCharge φ = periodicFrameCost φ := by
    simp only [frameCharge, periodicFrameCost]
    ring
  rw [hframe] at h
  simp only [State.cost, State.signedLabel]
  push_cast at h
  linarith

/-- The pair inequality for every separating axis, when one of the branches is outer: the axes
two and three are the axes four and one of the reversed edge with both signs flipped. -/
theorem pair (s t : State) (j : Fin 4) (φ : ℝ)
    (hφ : -1 ≤ φ ∧ φ ≤ 4)
    (hgap : 19/25 ≤ s.gap t φ ∧ s.gap t φ ≤ 3*Real.pi/4)
    (haxis : 0 ≤ SquaresInCircles.Eight.forwardMargin j
      s.a s.b t.a t.b (sign s.positive) (sign t.positive) φ)
    (hnon : s.branch.type ≠ 0 ∨ t.branch.type ≠ 0) :
    handGamma s.branch.type t.branch.type < s.cost t φ := by
  fin_cases j
  · exact source_pair s t false φ hφ hgap haxis hnon
  · have hm : 0 ≤ SquaresInCircles.Eight.forwardMargin (sourceAxis true)
        t.flip.a t.flip.b s.flip.a s.flip.b
        (sign t.flip.positive) (sign s.flip.positive) φ := by
      simpa [sourceAxis,State.flip,sign_not,SquaresInCircles.Eight.forwardMargin,
        sub_eq_add_neg,mul_add,add_mul,mul_comm,mul_left_comm,mul_assoc,
        add_comm,add_left_comm,add_assoc] using haxis
    have hh := source_pair t.flip s.flip true φ hφ (by simpa using hgap) hm hnon.symm
    change handGamma t.branch.type s.branch.type < t.flip.cost s.flip φ at hh
    rw [State.reverse_cost,gamma_symmetric] at hh
    exact hh
  · have hm : 0 ≤ SquaresInCircles.Eight.forwardMargin (sourceAxis false)
        t.flip.a t.flip.b s.flip.a s.flip.b
        (sign t.flip.positive) (sign s.flip.positive) φ := by
      simpa [sourceAxis,State.flip,sign_not,SquaresInCircles.Eight.forwardMargin,
        sub_eq_add_neg,mul_add,add_mul,mul_comm,mul_left_comm,mul_assoc,
        add_comm,add_left_comm,add_assoc] using haxis
    have hh := source_pair t.flip s.flip false φ hφ (by simpa using hgap) hm hnon.symm
    change handGamma t.branch.type s.branch.type < t.flip.cost s.flip φ at hh
    rw [State.reverse_cost,gamma_symmetric] at hh
    exact hh
  · exact source_pair s t true φ hφ hgap haxis hnon

/-- The branch of a vertex: its core chart, or the range of its tangent on the outer circle. -/
noncomputable def branchOf (C : BoundaryCycle Q0) (i : Vertex) : Branch :=
  match C.kind i with
  | .coreSide => .coreSide
  | .coreCorner => .coreCorner
  | .outer => if 4*C.b i ≤ C.a i then .low
      else if 7*C.b i ≤ 3*C.a i then .middle else .high

theorem branchOf_core_iff (C : BoundaryCycle Q0) (i : Vertex) :
    (branchOf C i).type=0 ↔ C.kind i ≠ .outer := by
  cases hk : C.kind i
  · simp only [branchOf, hk]
    split_ifs <;> simp [Branch.type]
  all_goals simp [branchOf, hk, Branch.type]

/-- The sign of a vertex, `true` for `+1`. -/
noncomputable def signOf (C : BoundaryCycle Q0) (i : Vertex) : Bool :=
  if C.sigma i=1 then true else false

theorem signOf_spec (C : BoundaryCycle Q0) (i : Vertex) : sign (signOf C i)=C.sigma i := by
  rcases C.sigma_sign i with h | h <;> norm_num [signOf,sign,h]

/-- A vertex is the point of the chart of its branch given by `b`, in the range of the branch. -/
theorem branchOf_spec (C : BoundaryCycle Q0) (i : Vertex) :
    C.a i=radialA (branchOf C i) (C.b i) ∧
      (branchOf C i).bBox.Mem (C.b i) ∧ TypeMem (branchOf C i) (C.a i) (C.b i) := by
  have ha := C.a_pos i
  have hb := C.b_nonneg i
  have hab := C.b_le_a i
  have hbU := (Candidate.canonical_bounds C le_rfl i).2.2.2
  have hboundary := C.boundary i
  cases hk : C.kind i with
  | outer =>
      have he : (C.a i+1/2)^2+(C.b i+1/2)^2=Q0 := by
        simpa [BoundaryState,hk,SquaresInCircles.phi] using hboundary
      have hr : Real.sqrt (Q0-(C.b i+1/2)^2)=C.a i+1/2 := by
        rw [show Q0-(C.b i+1/2)^2=(C.a i+1/2)^2 by linarith only [he],
          Real.sqrt_sq_eq_abs,abs_of_pos (by linarith only [ha])]
      simp only [branchOf,hk]
      split_ifs with hl hm
      · exact ⟨by simp only [radialA,hr]; ring,
          by simpa [Branch.bBox,QInterval.Mem] using And.intro hb hbU.le,hl⟩
      · exact ⟨by simp only [radialA,hr]; ring,
          by simpa [Branch.bBox,QInterval.Mem] using And.intro hb hbU.le,
          ⟨(lt_of_not_ge hl).le,hm⟩⟩
      · exact ⟨by simp only [radialA,hr]; ring,
          by simpa [Branch.bBox,QInterval.Mem] using And.intro hb hbU.le,
          (lt_of_not_ge hm).le⟩
  | coreSide =>
      have hc : C.a i=7/12 ∧ C.b i ≤ 1/2 := by
        simpa [BoundaryState,hk] using hboundary
      exact ⟨by simpa [branchOf,hk,radialA] using hc.1,
        by simpa [branchOf,hk,Branch.bBox,QInterval.Mem] using And.intro hb hc.2,
        by simp [branchOf,hk,TypeMem]⟩
  | coreCorner =>
      have hc : 1/2 ≤ C.b i ∧ (C.a i-1/2)^2+(C.b i-1/2)^2=(1/12:ℝ)^2 := by
        simpa [BoundaryState,hk] using hboundary
      have hap : 0 ≤ C.a i-1/2 := by linarith only [hc.1, hab]
      have hr : Real.sqrt ((1/12:ℝ)^2-(C.b i-1/2)^2)=C.a i-1/2 := by
        rw [show (1/12:ℝ)^2-(C.b i-1/2)^2=(C.a i-1/2)^2 by linarith only [hc.2],
          Real.sqrt_sq_eq_abs,abs_of_nonneg hap]
      have hb' : C.b i ≤ 14/25 := by
        have hs : (C.b i-1/2)^2 ≤ (C.a i-1/2)^2 :=
          pow_le_pow_left₀ (by linarith only [hc.1]) (by linarith only [hab]) 2
        nlinarith only [hc.2, hab, hs, ha]
      exact ⟨by simp only [branchOf,hk,radialA,hr]; ring,
        by simpa [branchOf,hk,Branch.bBox,QInterval.Mem] using And.intro hc.1 hb',
        by simp [branchOf,hk,TypeMem]⟩

/-- The state of a vertex; the same state serves both edges of the vertex. -/
noncomputable def stateOf (C : BoundaryCycle Q0) (i : Vertex) : State where
  branch := branchOf C i
  positive := signOf C i
  a := C.a i
  b := C.b i
  a_eq := (branchOf_spec C i).1
  b_mem := (branchOf_spec C i).2.1
  canonical := C.b_le_a i
  type_mem := (branchOf_spec C i).2.2

theorem stateOf_offset (C : BoundaryCycle Q0) (i : Vertex) :
    (stateOf C i).offset=C.alpha i := by
  simp only [State.offset,stateOf,signOf_spec,BoundaryCycle.alpha,BoundaryCycle.tangent]
  rcases C.sigma_sign i with h | h <;>
    simp [h,neg_div,Real.arctan_neg]

/-- At a core vertex the signed label is `σ` times the four-type core label. -/
theorem stateOf_core_label (C : BoundaryCycle Q0) (i : Vertex) (hk : C.kind i ≠ .outer) :
    (stateOf C i).signedLabel=
      C.sigma i*CorePairGeometry.label CorePairGeometry.K CorePairGeometry.g (C.a i) (C.b i) := by
  have hb : label (branchOf C i) (C.a i) (C.b i)=
      CorePairGeometry.label CorePairGeometry.K CorePairGeometry.g (C.a i) (C.b i) := by
    cases he : C.kind i
    · exact absurd he hk
    all_goals simp [branchOf, he, label, CorePairGeometry.label, CorePairGeometry.K,
      CorePairGeometry.g]
  simp only [State.signedLabel, stateOf, signOf_spec, hb]

/-- The frame angle difference of the edge `i`: the difference of the canonical angles of its
ends, plus `2π` on the last edge, so that it is `angleGap β i + αᵢ₊₁ - αᵢ` (`pairAngle_gap`). -/
noncomputable def pairAngle (C : BoundaryCycle Q0) (i : Vertex) : ℝ :=
  C.canonicalAngle (next i)-C.canonicalAngle i+if i=6 then 2*Real.pi else 0

theorem pairAngle_gap (C : BoundaryCycle Q0) (i : Vertex) :
    pairAngle C i=angleGap C.beta i+C.alpha (next i)-C.alpha i := by
  simp only [pairAngle,angleGap,BoundaryCycle.canonicalAngle]
  ring

theorem pairAngle_trig (C : BoundaryCycle Q0) (i : Vertex) :
    relativeC (C.square i) (C.square (next i))=Real.cos (pairAngle C i) ∧
    relativeS (C.square i) (C.square (next i))=Real.sin (pairAngle C i) := by
  have hci : (C.square i).cosine=Real.cos (C.canonicalAngle i) := C.frame_cos i
  have hsi : (C.square i).sine=Real.sin (C.canonicalAngle i) := C.frame_sin i
  have hcj : (C.square (next i)).cosine=Real.cos (C.canonicalAngle (next i)) := C.frame_cos _
  have hsj : (C.square (next i)).sine=Real.sin (C.canonicalAngle (next i)) := C.frame_sin _
  have hc : relativeC (C.square i) (C.square (next i))=
      Real.cos (C.canonicalAngle (next i)-C.canonicalAngle i) := by
    simp [relativeC,hci,hsi,hcj,hsj,Real.cos_sub]
    ring
  have hs : relativeS (C.square i) (C.square (next i))=
      Real.sin (C.canonicalAngle (next i)-C.canonicalAngle i) := by
    simp [relativeS,hci,hsi,hcj,hsj,Real.sin_sub]
    ring
  by_cases hi : i=6 <;>
    simpa [pairAngle,hi,Real.cos_add,Real.sin_add] using And.intro hc hs

theorem pairAngle_charge (C : BoundaryCycle Q0) (i : Vertex) :
    periodicFrameCost (pairAngle C i)=
      periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i) := by
  by_cases hi : i=6
  · have h := periodicFrameCost_int_quarter
      (C.canonicalAngle (next i)-C.canonicalAngle i) 4
    convert h using 1
    congr 1
    simp only [pairAngle,hi,ite_true]
    norm_num
    ring
  · simp [pairAngle,hi]

theorem pairAngle_mem (C : BoundaryCycle Q0) (i : Vertex) :
    -1 ≤ pairAngle C i ∧ pairAngle C i ≤ 4 := by
  have hl := boundary_gap_lower C le_rfl i
  have hu := boundary_gap_upper C le_rfl i
  have hα := C.alpha_range i
  have hA := C.alpha_range (next i)
  rw [pairAngle_gap]
  constructor <;> linarith [pi_lt_22_over_7]

/-- The pair bound of the edge `i` of a boundary cycle at `Q₀` for a feasible separating axis
`j`: from `CorePairGeometry.core_cost` and `CorePairGeometry.charge_upper` when both ends are
core, from `pair` otherwise. -/
theorem cycle_pair (C : BoundaryCycle Q0) (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type <
      angleGap C.beta i-
        (9/50)*periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i)+
        (C.alpha (next i)-(stateOf C (next i)).signedLabel)-
        (C.alpha i-(stateOf C i).signedLabel) := by
  by_cases hcore : (branchOf C i).type=0 ∧ (branchOf C (next i)).type=0
  · have hi := (branchOf_core_iff C i).mp hcore.1
    have hn := (branchOf_core_iff C (next i)).mp hcore.2
    have hh := CorePairGeometry.core_cost (Or.inl ⟨rfl, rfl⟩) C i hi hn
    have hc := CorePairGeometry.charge_upper (C.canonicalAngle (next i)-C.canonicalAngle i)
    have h0 : handGamma 0 0=23/25 := by norm_num [handGamma, handGammaNumerator]
    rw [stateOf_core_label C i hi, stateOf_core_label C (next i) hn, hcore.1, hcore.2, h0]
    linarith
  have hm := canonical_margin_identity j _ _ _ _ _ _ _ _ (pairAngle C i)
    (C.center_eq i) (C.center_eq (next i)) (pairAngle_trig C i).1 (pairAngle_trig C i).2
  have hmargin : 0 ≤ SquaresInCircles.Eight.forwardMargin j
      (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (C.sigma i) (C.sigma (next i))
      (pairAngle C i) := by
    rw [← hm]
    exact sub_nonneg.mpr hj
  have hgap : (stateOf C i).gap (stateOf C (next i)) (pairAngle C i)=angleGap C.beta i := by
    rw [State.gap,stateOf_offset,stateOf_offset,pairAngle_gap]
    ring
  have hh := pair (stateOf C i) (stateOf C (next i)) j (pairAngle C i)
    (pairAngle_mem C i)
    (by rw [hgap]; exact ⟨(boundary_gap_lower C le_rfl i).le,(boundary_gap_upper C le_rfl i).le⟩)
    (by simpa only [stateOf,signOf_spec] using hmargin) (not_and_or.mp hcore)
  change handGamma (branchOf C i).type (branchOf C (next i)).type <
    (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) at hh
  unfold State.cost at hh
  rw [pairAngle_charge,pairAngle_gap] at hh
  linarith

end SquaresInCircles.Eight.Arithmetic.FourType

namespace SquaresInCircles.Eight

/-- The four-type pair bounds of a boundary cycle at `Q₀`: with the type `τᵢ` and the marker
`ψᵢ` of each vertex, the same on both of its edges, every edge has
`handGamma τᵢ τᵢ₊₁ < angleGap β i - (9/50) h(θᵢ₊₁ - θᵢ) + ψᵢ₊₁ - ψᵢ`, where `h` is the frame
charge of the difference of the canonical angles. -/
theorem four_type_pair_bound (C : BoundaryCycle Q0) :
    ∃ τ : Vertex → Fin 4, ∃ ψ : Vertex → ℝ, ∀ i,
      handGamma (τ i) (τ (next i)) <
        angleGap C.beta i-
          (9/50)*periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i)+
          ψ (next i)-ψ i := by
  let τ : Vertex → Fin 4 := fun i => (Arithmetic.FourType.branchOf C i).type
  let ψ : Vertex → ℝ := fun i => C.alpha i-(Arithmetic.FourType.stateOf C i).signedLabel
  refine ⟨τ,ψ,?_⟩
  intro i
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have hh := C.feasible i
  rw [hj] at hh
  exact Arithmetic.FourType.cycle_pair C i j hh

end SquaresInCircles.Eight
