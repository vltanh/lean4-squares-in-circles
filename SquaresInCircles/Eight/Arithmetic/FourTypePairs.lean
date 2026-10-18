module

public import SquaresInCircles.Eight.Generated.PairsFourType
public import SquaresInCircles.Eight.BoundaryGeometry
public import SquaresInCircles.Eight.Frames

/-!
# The continuous four-type pair table, with its geometric meaning

The four labels and all sixteen constants are those in
`HAND_EXTERIOR_FRAME_CONCENTRATION.md`, section 2.  The closed core side and
closed core corner are kept as separate analytic charts; L, M and H are
the three closed outer tangent ranges.  A vertex chooses its chart and
sign once, and its resulting label is used on both incident edges.

For an ordered pair of charts, signs and a source axis, the pair inequality is a
problem of a pair table (`Generated/Pairs`): its ends carry the actual charts,
tangent ranges and signed labels, with rational brackets of the constants
`√(Q₀ - 1/4)`, `√(Q₀/2)` and `π`. The table proves it on the six halves of
`φ ∈ [-1, 4]`, for every state pair and angle with the physical gap and the
source-axis margin. Reflection and reversal supply both target axes.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.Arithmetic.FourType

/-- Five analytic charts for the four geometric types.  The two core
charts have the same label and the same matrix index. -/
inductive Branch | coreSide | coreCorner | low | middle | high
  deriving DecidableEq, Repr

instance : Fintype Branch where
  elems := {.coreSide, .coreCorner, .low, .middle, .high}
  complete x := by cases x <;> decide

def Branch.type : Branch → Fin 4
  | .coreSide | .coreCorner => 0
  | .low => 1 | .middle => 2 | .high => 3

def Branch.bBox : Branch → QInterval
  | .coreSide => ⟨0,1/2⟩
  | .coreCorner => ⟨1/2,14/25⟩
  | .low | .middle | .high => ⟨0,9/10⟩

def signQ (positive : Bool) : ℚ := if positive then 1 else -1
def sign (positive : Bool) : ℝ := if positive then 1 else -1

@[simp] theorem signQ_cast (p : Bool) : (signQ p : ℝ)=sign p := by
  cases p <;> norm_num [signQ,sign]

@[simp] theorem sign_not (p : Bool) : sign (!p)= -sign p := by
  cases p <;> norm_num [sign]

noncomputable def radialA (s : Branch) (b : ℝ) : ℝ :=
  match s with
  | .coreSide => 7/12
  | .coreCorner => 1/2+Real.sqrt ((1/12:ℝ)^2-(b-1/2)^2)
  | .low | .middle | .high => Real.sqrt (Q0-(b+1/2)^2)-1/2

noncomputable def a0 : ℝ := Real.sqrt (Q0-1/4)-1/2
noncomputable def c0 : ℝ := Real.sqrt (Q0/2)-1/2

/-- Exact positive-half labels, including the constant terms. -/
noncomputable def label (s : Branch) (a b : ℝ) : ℝ :=
  match s with
  | .coreSide | .coreCorner => (7506931/1000000)*(7/12-a)+(269343/250000)*b
  | .low => (3231/8000)*(a-a0)+(217813/200000)*b
  | .middle => -85723/40000+(1489593/1000000)*a+(1580219/1000000)*b
  | .high => Real.pi/4-(8898/15625)*(a-c0)+(195443/500000)*(b-c0)

/-- Multiplication removes the strictly positive denominator from each
tangent-type restriction.  Every chart includes both of its endpoints. -/
def TypeMem (s : Branch) (a b : ℝ) : Prop :=
  match s with
  | .coreSide | .coreCorner => True
  | .low => 4*b ≤ a
  | .middle => a ≤ 4*b ∧ 7*b ≤ 3*a
  | .high => 3*a ≤ 7*b

def sourceAxis (four : Bool) : Fin 4 := if four then 3 else 0

def gammaQ (s t : Branch) : ℚ := handGammaNumerator s.type t.type/10000

@[simp] theorem gammaQ_cast (s t : Branch) :
    (gammaQ s t : ℝ)=handGamma s.type t.type := by
  simp [gammaQ,handGamma]

/-- An actual closed chart point.  None of its fields is a pair inequality. -/
structure State where
  branch : Branch
  positive : Bool
  a : ℝ
  b : ℝ
  a_eq : a=radialA branch b
  b_mem : branch.bBox.Mem b
  canonical : b ≤ a
  type_mem : TypeMem branch a b

def State.flip (s : State) : State := { s with positive := !s.positive }

noncomputable def State.offset (s : State) : ℝ := sign s.positive*Real.arctan (s.b/s.a)
noncomputable def State.signedLabel (s : State) : ℝ := sign s.positive*label s.branch s.a s.b
noncomputable def State.gap (s t : State) (φ : ℝ) : ℝ := φ+s.offset-t.offset
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

theorem gamma_symmetric (s t : Branch) :
    handGamma t.type s.type=handGamma s.type t.type := by
  cases s <;> cases t <;> norm_num [Branch.type,handGamma,handGammaNumerator]

/-! ### The pair tables -/

section Tables

open PairCover

/-- Rational brackets of `√(Q₀ - 1/4)`, `√(Q₀/2)` and `π`. -/
def rootA0Lo : ℚ := 191457567100389113870 / 10 ^ 20
def rootA0Hi : ℚ := 191457567100389113871 / 10 ^ 20
def rootC0Lo : ℚ := 139921406510940991183 / 10 ^ 20
def rootC0Hi : ℚ := 139921406510940991184 / 10 ^ 20
def piLo : ℚ := 3141592653589793238 / 10 ^ 18
def piHi : ℚ := 3141592653589793239 / 10 ^ 18

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

/-- The positive label of a branch, with a rational bracket of its constant. -/
def branchQuad : Branch → QuadLabel
  | .coreSide | .coreCorner => ⟨7506931/1000000*(7/12), 7506931/1000000*(7/12), -(7506931/1000000),
      269343/250000, 0, 0⟩
  | .low => ⟨-(3231/8000)*(rootA0Hi-1/2), -(3231/8000)*(rootA0Lo-1/2), 3231/8000, 217813/200000,
      0, 0⟩
  | .middle => ⟨-85723/40000, -85723/40000, 1489593/1000000, 1580219/1000000, 0, 0⟩
  | .high => ⟨piLo/4+(8898/15625-195443/500000)*(rootC0Lo-1/2),
      piHi/4+(8898/15625-195443/500000)*(rootC0Hi-1/2), -(8898/15625), 195443/500000, 0, 0⟩

/-- The constant of the positive label of a branch. -/
noncomputable def branchConst : Branch → ℝ
  | .coreSide | .coreCorner => 7506931/1000000*(7/12)
  | .low => -(3231/8000)*a0
  | .middle => -85723/40000
  | .high => Real.pi/4+(8898/15625-195443/500000)*c0

theorem label_eq (s : Branch) (a b : ℝ) : label s a b = (branchQuad s).eval (branchConst s) a b := by
  cases s <;> simp only [label, branchQuad, branchConst, QuadLabel.eval] <;> push_cast <;> ring

theorem branchConst_mem (s : Branch) :
    ((branchQuad s).cLo : ℝ) ≤ branchConst s ∧ branchConst s ≤ (branchQuad s).cHi := by
  have ha := a0_bounds
  have hc := c0_bounds
  have hp := pi_bounds
  cases s <;> simp only [branchQuad,
    branchConst] <;> push_cast <;> constructor <;> linarith only [ha, hc, hp]

/-- The chart and the tangent range of a branch. -/
def Branch.outer : Branch → Bool
  | .low | .middle | .high => true
  | .coreSide | .coreCorner => false

def Branch.side : Branch → Bool
  | .coreSide => true
  | _ => false

def Branch.range : Branch → QInterval
  | .coreSide => ⟨0, 6/7⟩
  | .coreCorner => ⟨6/7, 1⟩
  | .low => ⟨0, 1/4⟩
  | .middle => ⟨1/4, 3/7⟩
  | .high => ⟨3/7, 1⟩

/-- The end of a pair at a vertex of the branch `s` and sign `σ`. -/
def branchEnd (s : Branch) (σ : Bool) : PairEnd :=
  ⟨s.outer, s.side, σ, s.range, (branchQuad s).signed σ⟩

/-- The six halves `(k, r, u⁺)` of `φ ∈ [-1, 4]`, with `u⁺` over `10⁸`. -/
def fourTypeHalves : List (ℕ × Bool × ℕ) :=
  [(0, false, 100000000), (0, true, 80000000), (1, false, 80000000), (1, true, 80000000),
    (2, false, 80000000), (2, true, 86000000)]

/-- The pair problem of the branches `s`, `t`, the signs `σ`, `τ` and the source axis. -/
def fourTypeProblem (s t : Branch) (σ τ four : Bool) : PairProblem :=
  ⟨branchEnd s σ, branchEnd t τ, if four then .four else .one, 9/50, gammaQ s t, fourTypeHalves⟩

/-- The pair table of an ordered pair of branches. -/
def fourTypeTable : Branch → Branch → List PairProblem
  | .coreSide, .coreSide => Generated.Pairs.FourTypeCoreSideCoreSide.problems
  | .coreSide, .coreCorner => Generated.Pairs.FourTypeCoreSideCoreCorner.problems
  | .coreSide, .low => Generated.Pairs.FourTypeCoreSideLow.problems
  | .coreSide, .middle => Generated.Pairs.FourTypeCoreSideMiddle.problems
  | .coreSide, .high => Generated.Pairs.FourTypeCoreSideHigh.problems
  | .coreCorner, .coreSide => Generated.Pairs.FourTypeCoreCornerCoreSide.problems
  | .coreCorner, .coreCorner => Generated.Pairs.FourTypeCoreCornerCoreCorner.problems
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

theorem fourTypeTable_holds (s t : Branch) :
    ∀ P ∈ fourTypeTable s t, P.Holds ((9789/2500 : ℚ) : ℝ) 100000000 := by
  cases s <;> cases t
  · exact Generated.Pairs.FourTypeCoreSideCoreSide.sound
  · exact Generated.Pairs.FourTypeCoreSideCoreCorner.sound
  · exact Generated.Pairs.FourTypeCoreSideLow.sound
  · exact Generated.Pairs.FourTypeCoreSideMiddle.sound
  · exact Generated.Pairs.FourTypeCoreSideHigh.sound
  · exact Generated.Pairs.FourTypeCoreCornerCoreSide.sound
  · exact Generated.Pairs.FourTypeCoreCornerCoreCorner.sound
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

theorem fourTypeProblem_mem :
    ∀ s t : Branch, ∀ σ τ four : Bool, fourTypeProblem s t σ τ four ∈ fourTypeTable s t := by
  decide +kernel

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

/-- Soundness of each source-axis problem, on every point of its full
closed state box and its closed physical angular domain. -/
theorem source_pair (s t : State) (four : Bool) (φ : ℝ)
    (hφ : -1 ≤ φ ∧ φ ≤ 4)
    (hgap : 19/25 ≤ s.gap t φ ∧ s.gap t φ ≤ 3*Real.pi/4)
    (haxis : 0 ≤ SquaresInCircles.Eight.forwardMargin (sourceAxis four)
      s.a s.b t.a t.b (sign s.positive) (sign t.positive) φ) :
    handGamma s.branch.type t.branch.type < s.cost t φ := by
  obtain ⟨hv, hmem, u, hu0, hu1, hphi⟩ := four_type_half hφ
  have hP := fourTypeTable_holds s.branch t.branch _
    (fourTypeProblem_mem s.branch t.branch s.positive t.positive four)
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

/-- Original target axes are covered by reflected reversal, with both
vertex signs and both vertex labels transported together. -/
theorem pair (s t : State) (j : Fin 4) (φ : ℝ)
    (hφ : -1 ≤ φ ∧ φ ≤ 4)
    (hgap : 19/25 ≤ s.gap t φ ∧ s.gap t φ ≤ 3*Real.pi/4)
    (haxis : 0 ≤ SquaresInCircles.Eight.forwardMargin j
      s.a s.b t.a t.b (sign s.positive) (sign t.positive) φ) :
    handGamma s.branch.type t.branch.type < s.cost t φ := by
  fin_cases j
  · exact source_pair s t false φ hφ hgap haxis
  · have hm : 0 ≤ SquaresInCircles.Eight.forwardMargin (sourceAxis true)
        t.flip.a t.flip.b s.flip.a s.flip.b
        (sign t.flip.positive) (sign s.flip.positive) φ := by
      simpa [sourceAxis,State.flip,sign_not,SquaresInCircles.Eight.forwardMargin,
        sub_eq_add_neg,mul_add,add_mul,mul_comm,mul_left_comm,mul_assoc,
        add_comm,add_left_comm,add_assoc] using haxis
    have hh := source_pair t.flip s.flip true φ hφ (by simpa using hgap) hm
    change handGamma t.branch.type s.branch.type < t.flip.cost s.flip φ at hh
    rw [State.reverse_cost,gamma_symmetric] at hh
    exact hh
  · have hm : 0 ≤ SquaresInCircles.Eight.forwardMargin (sourceAxis false)
        t.flip.a t.flip.b s.flip.a s.flip.b
        (sign t.flip.positive) (sign s.flip.positive) φ := by
      simpa [sourceAxis,State.flip,sign_not,SquaresInCircles.Eight.forwardMargin,
        sub_eq_add_neg,mul_add,add_mul,mul_comm,mul_left_comm,mul_assoc,
        add_comm,add_left_comm,add_assoc] using haxis
    have hh := source_pair t.flip s.flip false φ hφ (by simpa using hgap) hm
    change handGamma t.branch.type s.branch.type < t.flip.cost s.flip φ at hh
    rw [State.reverse_cost,gamma_symmetric] at hh
    exact hh
  · exact source_pair s t true φ hφ hgap haxis

noncomputable def branchOf (C : BoundaryCycle Q0) (i : Vertex) : Branch :=
  match C.kind i with
  | .coreSide => .coreSide
  | .coreCorner => .coreCorner
  | .outer => if 4*C.b i ≤ C.a i then .low
      else if 7*C.b i ≤ 3*C.a i then .middle else .high

noncomputable def signOf (C : BoundaryCycle Q0) (i : Vertex) : Bool :=
  if C.sigma i=1 then true else false

theorem signOf_spec (C : BoundaryCycle Q0) (i : Vertex) : sign (signOf C i)=C.sigma i := by
  rcases C.sigma_sign i with h | h <;> norm_num [signOf,sign,h]

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

/-- One consistent representative for a vertex, before either incident
pair is considered. -/
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

/-- The last edge includes its genuine full-turn winding. -/
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
    simp [relativeC,hci,hsi,hcj,hsj,Real.cos_sub] <;> ring
  have hs : relativeS (C.square i) (C.square (next i))=
      Real.sin (C.canonicalAngle (next i)-C.canonicalAngle i) := by
    simp [relativeS,hci,hsi,hcj,hsj,Real.sin_sub] <;> ring
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
    simp only [pairAngle,hi,if_true]
    norm_num <;> ring
  · simp [pairAngle,hi]

theorem pairAngle_mem (C : BoundaryCycle Q0) (i : Vertex) :
    -1 ≤ pairAngle C i ∧ pairAngle C i ≤ 4 := by
  have hl := boundary_gap_lower C le_rfl i
  have hu := boundary_gap_upper C le_rfl i
  have hα := C.alpha_range i
  have hA := C.alpha_range (next i)
  rw [pairAngle_gap]
  constructor <;> linarith [pi_lt_22_over_7]

/-- The four-type inequality for every actual retained forward axis. -/
theorem cycle_pair (C : BoundaryCycle Q0) (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type <
      angleGap C.beta i-
        (9/50)*periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i)+
        (C.alpha (next i)-(stateOf C (next i)).signedLabel)-
        (C.alpha i-(stateOf C i).signedLabel) := by
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
    (by simpa only [stateOf,signOf_spec] using hmargin)
  change handGamma (branchOf C i).type (branchOf C (next i)).type <
    (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) at hh
  unfold State.cost at hh
  rw [pairAngle_charge,pairAngle_gap] at hh
  linarith

end SquaresInCircles.Eight.Arithmetic.FourType

namespace SquaresInCircles.Eight

/-- Complete actual continuous four-type pair bridge.  Type and marker
are chosen once per vertex.  Every originally feasible signed axis is
covered, including simultaneous feasible ties. -/
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
