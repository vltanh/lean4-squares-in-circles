module

public import SquaresInCircles.Eight.Generated.PairsWords
public import SquaresInCircles.Eight.Arithmetic.WordProblems
public import SquaresInCircles.Eight.CycleActions
public import SquaresInCircles.Eight.Arithmetic.CorePairGeometry
public import SquaresInCircles.Eight.Candidate.GeometricCoreQuarter

/-!
# Eight squares: the six non-candidate quarter words

The quarter word of a quarter lift of a boundary cycle at the level `Q0`, whose gaps exceed
`19/25`, is admissible (`QuarterWords.lean`). This file excludes the six classes of admissible
words other than that of the candidate, so the word is equivalent to `0101011`
(`quarter_word_candidate`). On the edge `i` the phase `φᵢ = θᵢ₊₁ - θᵢ + kᵢ π/2` of the lift
(`phaseValue`) is the relative angle of the two frames (`relative_phase`), and `φᵢ + αᵢ - αᵢ₊₁`
is the gap of the centre directions (`phase_gap`), so the phases add up to `2π`. A marker `ψ`
with one value at each vertex, used on both edges of the vertex, telescopes: the edge costs
`φᵢ + ψᵢ - ψᵢ₊₁` add up to `2π` (`marker_budget`), so lower bounds of them add up to at most `2π`.

The words with a digit `2` are excluded together (`no_double`): with the common markers
(`commonMarker`) the cost of an edge exceeds `commonGamma` of its digit (`common_pair`), and these
bounds add up to more than `2π` on every admissible word with a digit `2`. On an edge between two
core squares the bound follows from the separation of the centres
(`Arithmetic/CorePairGeometry.lean`). The two other words, `0010111` and `0011011`, have markers
that depend on the role of the vertex (`wrongMarker`), with bounds `wrongGamma` that add up to
more than `2π` (`wrong_word_impossible`).

Each remaining pair bound is a problem of a pair table of `Generated/Pairs/` (`word_pair`): its
ends carry the radial charts, signs and labels of the two squares, and the table proves it for
every pair of states and every frame difference `|d| ≤ 7/10` with the gap in `[19/25, 3π/4]` and
a nonnegative margin of the separating axis. The tables define their problems by
`commonPairProblem` and `wrongPairProblem` (`Arithmetic/WordProblems.lean`), and leave out the
radial kinds, signs and axes for which the axis cannot separate (`original_not_core_excluded`, by
the margins of `Candidate/GeometricPrimaryExclusion.lean`,
`Candidate/GeometricSecondaryExclusion.lean` and `Candidate/GeometricCoreQuarter.lean`). On the
two words the two initial zero digits force the sign `+1` at the role `0` and `-1` at the role
`2` (`initial_signs`), and no zero edge goes from the sign `-1` to the sign `+1`
(`zero_not_negative_positive`), which leaves nineteen sign pairs on the seven edges of each word.

A word equivalent to a representative is taken to it by a rotation or reflection of the cycle
(`normalize_word`), which acts on the squares themselves (`CycleAction.boundary` and
`QuarterLift.act` of `CycleActions.lean`). A reflection reverses each edge, so the vertex shift of
a reflected action has an extra `1` (`normalizingAction`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.WordGeometry

open Arithmetic Arithmetic.PairCover WordProblems

/-- `true` when the transverse sign `σᵢ` of the vertex `i` is `+1`. -/
def positiveOf (C : BoundaryCycle Q0) (i : Vertex) : Bool :=
  if C.sigma i=1 then true else false

lemma positiveOf_spec (C : BoundaryCycle Q0) (i : Vertex) :
    (WordProblems.sign (positiveOf C i) : ℝ)=C.sigma i := by
  rcases C.sigma_sign i with h | h <;> norm_num [positiveOf,WordProblems.sign,h]

lemma alpha_formula (C : BoundaryCycle Q0) (i : Vertex) :
    C.alpha i=(WordProblems.sign (positiveOf C i):ℝ)*Real.arctan (C.b i/C.a i) := by
  rw [positiveOf_spec]
  rcases C.sigma_sign i with h | h <;>
    simp [BoundaryCycle.alpha,BoundaryCycle.tangent,h,neg_div,Real.arctan_neg]

lemma unsigned_angle_nonneg (C : BoundaryCycle Q0) (i : Vertex) :
    0 ≤ Real.arctan (C.b i/C.a i) := by
  have h := Real.arctan_mono (div_nonneg (C.b_nonneg i) (C.a_pos i).le)
  simpa using h

lemma alpha_nonpos (C : BoundaryCycle Q0) (i : Vertex) (h : positiveOf C i=false) :
    C.alpha i ≤ 0 := by
  rw [alpha_formula,h]
  simp only [WordProblems.sign,Bool.false_eq_true,ite_false,Rat.cast_neg,Rat.cast_one,neg_one_mul]
  exact neg_nonpos.mpr (unsigned_angle_nonneg C i)

lemma alpha_nonneg (C : BoundaryCycle Q0) (i : Vertex) (h : positiveOf C i=true) :
    0 ≤ C.alpha i := by
  rw [alpha_formula,h]
  simpa [WordProblems.sign] using unsigned_angle_nonneg C i

lemma positiveOf_of_alpha_pos (C : BoundaryCycle Q0) (i : Vertex) (h : 0<C.alpha i) :
    positiveOf C i=true := by
  cases hp : positiveOf C i
  · exact (not_lt_of_ge (alpha_nonpos C i hp) h).elim
  · rfl

lemma positiveOf_of_alpha_neg (C : BoundaryCycle Q0) (i : Vertex) (h : C.alpha i<0) :
    positiveOf C i=false := by
  cases hp : positiveOf C i
  · rfl
  · exact (not_lt_of_ge (alpha_nonneg C i hp) h).elim

/-- The frame difference `θᵢ₊₁ - θᵢ` of the edge `i`. -/
def difference {C : BoundaryCycle Q0} (F : QuarterLift C) (i : Vertex) : ℝ :=
  F.theta (next i)-F.theta i

/-- The phase `φᵢ = θᵢ₊₁ - θᵢ + kᵢ π/2` of the edge `i`, with the digit `kᵢ` of the quarter word:
the relative angle of the frames of its two squares (`relative_phase`). -/
def phaseValue {C : BoundaryCycle Q0} (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) : ℝ :=
  difference F i+((F.word hgap pi_lt_22_over_7 i).val:ℝ)*Real.pi/2

lemma theta_spread {C : BoundaryCycle Q0} (F : QuarterLift C) (i j : Vertex) :
    |F.theta j-F.theta i|<7/10 := by
  apply abs_lt.mpr
  constructor <;> linarith [(F.theta_range i).1,(F.theta_range i).2,
    (F.theta_range j).1,(F.theta_range j).2,F.small]

lemma difference_small {C : BoundaryCycle Q0} (F : QuarterLift C) (i : Vertex) :
    |difference F i|<7/10 := theta_spread F i (next i)

/-- The phase plus `αᵢ - αᵢ₊₁` is the gap of the centre directions. -/
lemma phase_gap (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) :
    phaseValue F hgap i+C.alpha i-C.alpha (next i)=angleGap C.beta i := by
  have hk : ((F.word hgap pi_lt_22_over_7 i).val:ℝ)=
      (integerQuarterIncrement F.quarter i:ℝ) := by
    exact_mod_cast F.word_cast hgap pi_lt_22_over_7 i
  rw [phaseValue,hk]
  have hh := F.edge_identity i
  dsimp [difference]
  linarith

/-- The phases of the seven edges add up to `2π`. -/
lemma phase_sum (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) :
    (∑ i,phaseValue F hgap i)=2*Real.pi := by
  have he (i : Vertex) : phaseValue F hgap i=
      angleGap C.beta i-C.alpha i+C.alpha (next i) := by
    linarith [phase_gap C F hgap i]
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,sum_next,angleGap_sum]
  ring

lemma canonical_phase (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) :
    C.canonicalAngle (next i)-C.canonicalAngle i=
      phaseValue F hgap i-if i=6 then 2*Real.pi else 0 := by
  have h := phase_gap C F hgap i
  by_cases hi : i=6 <;>
    simp [BoundaryCycle.canonicalAngle,angleGap,hi] at * <;> linarith

/-- The relative cosine and sine of the frames of the edge `i` are those of its phase. -/
lemma relative_phase (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) :
    relativeC (C.square i) (C.square (next i))=Real.cos (phaseValue F hgap i) ∧
    relativeS (C.square i) (C.square (next i))=Real.sin (phaseValue F hgap i) := by
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
  rw [canonical_phase C F hgap i] at hc hs
  by_cases hi : i=6 <;>
    simpa [hi,Real.cos_sub,Real.sin_sub] using And.intro hc hs

/-- A separating forward axis of the edge `i` has a nonnegative margin `forwardMargin` at the
phase, in the states and signs of the two squares. -/
lemma original_margin (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    0 ≤ forwardMargin j (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
      (WordProblems.sign (positiveOf C i)) (WordProblems.sign (positiveOf C (next i)))
      (phaseValue F hgap i) := by
  rw [positiveOf_spec,positiveOf_spec]
  have he := canonical_margin_identity j _ _ _ _ _ _ _ _ (phaseValue F hgap i)
    (C.center_eq i) (C.center_eq (next i)) (relative_phase C F hgap i).1
    (relative_phase C F hgap i).2
  rw [← he]
  exact sub_nonneg.mpr hj

/-- No separating forward axis of an edge is in a class of `CoreSeparatorExcluded`: on a zero
edge the primary axis of a core square does not separate, the secondary axis of the source
against a core target needs the source sign `+1`, the secondary axis of the target against a core
source needs the target sign `-1`, and on a quarter edge no axis separates a core source of sign
`+1` from a core target of sign `-1`. -/
lemma original_not_core_excluded (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    ¬ CoreSeparatorExcluded (F.word hgap pi_lt_22_over_7 i)
      (C.kind i) (C.kind (next i)) (positiveOf C i) (positiveOf C (next i)) j := by
  have hm := original_margin C F hgap i j hj
  rw [positiveOf_spec,positiveOf_spec] at hm
  have hσ : |C.sigma i*C.b i| ≤ C.a i := by
    rw [Candidate.signed_b_abs]
    exact C.b_le_a i
  have hτ : |C.sigma (next i)*C.b (next i)| ≤ C.a (next i) := by
    rw [Candidate.signed_b_abs]
    exact C.b_le_a (next i)
  have hsmall (hk : F.word hgap pi_lt_22_over_7 i=0) : |phaseValue F hgap i| ≤ 7/10 := by
    simpa [phaseValue,hk] using (difference_small F i).le
  rintro (⟨hk,⟨rfl,ht⟩ | ⟨rfl,hs⟩⟩ | ⟨rfl,hnegative,ht⟩ | ⟨rfl,hpositive,hs⟩ |
    ⟨hk,hs,ht,hpositive,hnegative⟩)
  · have hp := Candidate.Geometric.primary_margin_upper (C.a_pos i).le hσ (hsmall hk)
      (X := C.a (next i))
    have hcore := Candidate.Geometric.core_primary_upper C (next i) ht
    simp [forwardMargin] at hm
    nlinarith [C.a_pos i]
  · have hp := Candidate.Geometric.primary_margin_upper (C.a_pos (next i)).le
      (v := -(C.sigma (next i)*C.b (next i))) (by simpa only [abs_neg] using hτ) (hsmall hk)
      (X := C.a i)
    have hcore := Candidate.Geometric.core_primary_upper C i hs
    simp [forwardMargin] at hm
    nlinarith [C.a_pos (next i)]
  · have hsource : C.sigma i*C.b i ≤ 0 := by
      rw [← positiveOf_spec C i,hnegative]
      simpa [WordProblems.sign] using C.b_nonneg i
    have hn := Candidate.Geometric.target_core_secondary_margin (a := C.a i) hsource
      (C.a_pos (next i)).le (Candidate.Geometric.core_primary_upper C (next i) ht) hτ
      (t := phaseValue F hgap i)
    linarith
  · have htarget : 0 ≤ C.sigma (next i)*C.b (next i) := by
      rw [← positiveOf_spec C (next i),hpositive]
      simpa [WordProblems.sign] using C.b_nonneg (next i)
    have hn := Candidate.Geometric.source_core_secondary_margin (A := C.a (next i)) htarget
      (C.a_pos i).le (Candidate.Geometric.core_primary_upper C i hs) hσ
      (t := phaseValue F hgap i)
    linarith
  · have hsign : C.sigma i=1 := by
      rw [← positiveOf_spec C i, hpositive]
      norm_num [WordProblems.sign]
    have htsign : C.sigma (next i)= -1 := by
      rw [← positiveOf_spec C (next i), hnegative]
      norm_num [WordProblems.sign]
    have hphase : phaseValue F hgap i=Real.pi/2+difference F i := by
      simp [phaseValue, hk, add_comm]
    have he := phase_gap C F hgap i
    rw [hphase, alpha_formula, alpha_formula, hpositive, hnegative] at he
    norm_num [WordProblems.sign] at he
    have hn := Candidate.Geometric.core_quarter_opposite_margin
      ⟨(Candidate.Geometric.canonical_primary_gt_half C i).le,
        Candidate.Geometric.core_primary_upper C i hs⟩
      ⟨(Candidate.Geometric.canonical_primary_gt_half C (next i)).le,
        Candidate.Geometric.core_primary_upper C (next i) ht⟩
      ⟨C.b_nonneg i, C.b_le_a i⟩ ⟨C.b_nonneg (next i), C.b_le_a (next i)⟩
      (difference_small F i).le
      (by linarith [Candidate.Geometric.cycle_gap_lt_seven_quarters C.beta hgap i]) j
    rw [hsign, htsign, hphase] at hm
    linarith

/-- The common label of a vertex of radial kind `kind`, sign `σ` and transverse coordinate `b`, at
the primary coordinate `a` of its curve: `σ (-9/100 + (13/200) a + (203/200) b)` on the outer
curve and `σ ((73/10)(7/12 - a) + (291/250) b)` on the core curves. -/
def commonValue (kind : RadialKind) (σ : Bool) (b : ℝ) : ℝ :=
  let a := primaryValue kind b
  (WordProblems.sign σ:ℝ)*(if kind=.outer then -9/100+(13/200)*a+(203/200)*b
    else (73/10)*(7/12-a)+(291/250)*b)

/-- The common label at the vertex `i`: the marker of the words with a digit `2`. -/
def commonMarker (C : BoundaryCycle Q0) (i : Vertex) : ℝ :=
  commonValue (C.kind i) (positiveOf C i) (C.b i)

/-- The label of the word `w` at the role `i`, with coefficients over `10⁵` that depend on the
role, the radial kind (outer or core) and the sign: `c + p a + σ q b` for `0010111` and
`σ (c + p a + q b + r b² + s a b)` for `0011011`. -/
def wrongValue (w : WrongWord) (i : Vertex) (kind : RadialKind) (σ : Bool) (b : ℝ) : ℝ :=
  let a := primaryValue kind b
  match w with
  | .short =>
      let v := shortCoefficients i (radialIndex kind) (signIndex σ)
      (v 0:ℝ)/100000+(v 1:ℝ)/100000*a+(WordProblems.sign σ:ℝ)*(v 2:ℝ)/100000*b
  | .second =>
      let v := secondCoefficients i (radialIndex kind) (signIndex σ)
      (WordProblems.sign σ:ℝ)*((v 0:ℝ)/100000+(v 1:ℝ)/100000*a+
        (v 2:ℝ)/100000*b+(v 3:ℝ)/100000*b^2+(v 4:ℝ)/100000*a*b)

/-- The label of the word `w` at the vertex `i`: its marker. -/
def wrongMarker (C : BoundaryCycle Q0) (w : WrongWord) (i : Vertex) : ℝ :=
  wrongValue w i (C.kind i) (positiveOf C i) (C.b i)

/-! ### The pair tables -/

/-- The common pair tables of the digits `0`, `1` and `2`. -/
def commonTable : Fin 3 → List PairProblem :=
  ![Generated.Pairs.Common0.problems, Generated.Pairs.Common1.problems,
    Generated.Pairs.Common2.problems]

/-- The pair tables of the seven edges of the words `0010111` and `0011011`. -/
def wrongTable : WrongWord → Vertex → List PairProblem
  | .short => ![Generated.Pairs.Short0.problems, Generated.Pairs.Short1.problems,
      Generated.Pairs.Short2.problems, Generated.Pairs.Short3.problems,
      Generated.Pairs.Short4.problems, Generated.Pairs.Short5.problems,
      Generated.Pairs.Short6.problems]
  | .second => ![Generated.Pairs.Second0.problems, Generated.Pairs.Second1.problems,
      Generated.Pairs.Second2.problems, Generated.Pairs.Second3.problems,
      Generated.Pairs.Second4.problems, Generated.Pairs.Second5.problems,
      Generated.Pairs.Second6.problems]

/-- Every problem of a common table holds at the level `Q0`, with angles over `10⁸`. -/
theorem commonTable_holds (k : Fin 3) :
    ∀ P ∈ commonTable k, P.Holds ((9789/2500 : ℚ) : ℝ) 100000000 := by
  fin_cases k
  · exact Generated.Pairs.Common0.sound
  · exact Generated.Pairs.Common1.sound
  · exact Generated.Pairs.Common2.sound

/-- Every problem of a table of the two words holds at the level `Q0`, with angles over `10⁸`. -/
theorem wrongTable_holds (w : WrongWord) (i : Vertex) :
    ∀ P ∈ wrongTable w i, P.Holds ((9789/2500 : ℚ) : ℝ) 100000000 := by
  cases w <;> fin_cases i
  · exact Generated.Pairs.Short0.sound
  · exact Generated.Pairs.Short1.sound
  · exact Generated.Pairs.Short2.sound
  · exact Generated.Pairs.Short3.sound
  · exact Generated.Pairs.Short4.sound
  · exact Generated.Pairs.Short5.sound
  · exact Generated.Pairs.Short6.sound
  · exact Generated.Pairs.Second0.sound
  · exact Generated.Pairs.Second1.sound
  · exact Generated.Pairs.Second2.sound
  · exact Generated.Pairs.Second3.sound
  · exact Generated.Pairs.Second4.sound
  · exact Generated.Pairs.Second5.sound
  · exact Generated.Pairs.Second6.sound

/-- Each common problem is in its table, as the image of its case: the table is
`commonPairProblem k` mapped over `commonCases k`. -/
theorem commonPairProblem_mem : ∀ (k : Fin 3) (ks kt : RadialKind) (σ τ : Bool) (j : Fin 4),
    (ks = .outer ∨ kt = .outer) → ¬ CoreSeparatorExcluded k ks kt σ τ j →
      commonPairProblem k ks kt σ τ j ∈ commonTable k := by
  intro k ks kt σ τ j h h'
  have hc := List.mem_map_of_mem (f := fun c : RadialKind × RadialKind × Bool × Bool × Fin 4 =>
    commonPairProblem k c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2) (mem_commonCases h h')
  fin_cases k <;> exact hc

/-- Each wrong-word problem is in its table, as the image of its case: the table is
`wrongPairProblem w i` mapped over `wrongCases w i`. -/
theorem wrongPairProblem_mem : ∀ (w : WrongWord) (i : Vertex) (ks kt : RadialKind)
    (σ τ : Bool) (j : Fin 4), allowed w i σ τ →
      ¬ CoreSeparatorExcluded (wrongWord w i) ks kt σ τ j →
      wrongPairProblem w i ks kt σ τ j ∈ wrongTable w i := by
  intro w i ks kt σ τ j h h'
  have hc := List.mem_map_of_mem (f := fun c : RadialKind × RadialKind × Bool × Bool × Fin 4 =>
    wrongPairProblem w i c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2) (mem_wrongCases h h')
  cases w <;> fin_cases i <;> exact hc

lemma sign_cast (σ : Bool) : ((WordProblems.sign σ : ℚ) : ℝ) = sgnR σ := by
  cases σ <;> simp [WordProblems.sign, sgnR]

/-- A vertex is a point of the chart of its radial kind, with its tangent in the chart range. -/
lemma vertex_mem (C : BoundaryCycle Q0) (i : Vertex) (σ : Bool) (L : QuadLabel) :
    (kindEnd (C.kind i) σ L).Mem ((9789/2500 : ℚ) : ℝ) (kindEnd (C.kind i) σ L).range
      (C.a i) (C.b i) := by
  have hb := C.boundary i
  have ha0 := C.a_pos i
  have hb0 := C.b_nonneg i
  have hba := C.b_le_a i
  have hQ : ((9789/2500 : ℚ) : ℝ) = Q0 := by norm_num [Q0]
  rw [hQ]
  cases hk : C.kind i
  · rw [hk] at hb
    simp only [kindEnd, kindRange, PairEnd.Mem, PairEnd.OnCurve, QInterval.Mem, decide_true,
      ↓reduceIte]
    push_cast
    refine ⟨ha0, hb0, hba, ⟨div_nonneg hb0 ha0.le, (div_le_one ha0).mpr hba⟩, ?_⟩
    simpa [BoundaryState, SquaresInCircles.phi] using hb
  · rw [hk] at hb
    obtain ⟨hA, hB⟩ := hb
    simp only [kindEnd, kindRange, PairEnd.Mem, PairEnd.OnCurve, QInterval.Mem,
      reduceCtorEq, decide_false, decide_true, Bool.false_eq_true, ↓reduceIte]
    push_cast
    refine ⟨ha0, hb0, hba, ⟨div_nonneg hb0 ha0.le, ?_⟩, hA, hB⟩
    rw [div_le_iff₀ ha0, hA]
    linarith
  · rw [hk] at hb
    obtain ⟨hB, he⟩ := hb
    simp only [kindEnd, kindRange, PairEnd.Mem, PairEnd.OnCurve, QInterval.Mem,
      reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte]
    push_cast
    have haU : C.a i ≤ 7/12 := by nlinarith [sq_nonneg (C.b i - 1/2)]
    refine ⟨ha0, hb0, hba, ⟨?_, (div_le_one ha0).mpr hba⟩, hB, he⟩
    rw [le_div_iff₀ ha0]
    linarith

/-- The pair bound of the edge `i`: if the problem with the ends of the edge, its original axis
`j` and the target `γ` holds, then `γ` is below the cost `φᵢ + L_s(aᵢ, bᵢ) - L_t(aᵢ₊₁, bᵢ₊₁)` of
the edge, for every admissible pair of label constants. -/
lemma word_pair (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) (Ls Lt : QuadLabel) (γ : ℚ)
    (hP : (⟨kindEnd (C.kind i) (positiveOf C i) Ls, kindEnd (C.kind (next i)) (positiveOf C (next i)) Lt,
      axisOf (j.val + 1), 0, γ, wordHalves (F.word hgap pi_lt_22_over_7 i).val⟩ : PairProblem).Holds
      ((9789/2500 : ℚ) : ℝ) 100000000)
    {cs ct : ℝ} (hcs : (Ls.cLo : ℝ) ≤ cs) (hct : ct ≤ Lt.cHi) :
    (γ : ℝ) < phaseValue F hgap i + Ls.eval cs (C.a i) (C.b i) -
      Lt.eval ct (C.a (next i)) (C.b (next i)) := by
  set k := F.word hgap pi_lt_22_over_7 i
  set d := difference F i
  have hd := abs_lt.mp (difference_small F i)
  set r : Bool := decide (0 ≤ d)
  have hphi : phiOf k.val r |d| = phaseValue F hgap i := by
    simp only [phiOf, phaseValue, r]
    by_cases h0 : 0 ≤ d
    · simp [h0, sgnR, abs_of_nonneg h0, d]
      ring
    · simp [h0, sgnR, abs_of_neg (lt_of_not_ge h0), d]
      ring
  have hmem : (k.val, r, 70000000) ∈ wordHalves k.val := by
    cases hr : r <;> simp [wordHalves]
  have hc := hP _ hmem cs ct hcs hct (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) |d|
    (vertex_mem C i _ _) (vertex_mem C (next i) _ _) (by simp) (by
      have := difference_small F i
      norm_num
      linarith)
  have he := phase_gap C F hgap i
  rw [alpha_formula, alpha_formula, sign_cast, sign_cast] at he
  simp only [PairProblem.gap, hphi] at hc
  dsimp only [kindEnd] at hc
  have hg1 : 19/25 ≤ phaseValue F hgap i + sgnR (positiveOf C i) * Real.arctan (C.b i / C.a i) -
      sgnR (positiveOf C (next i)) * Real.arctan (C.b (next i) / C.a (next i)) := by
    rw [he]
    exact (hgap i).le
  have hg2 : phaseValue F hgap i + sgnR (positiveOf C i) * Real.arctan (C.b i / C.a i) -
      sgnR (positiveOf C (next i)) * Real.arctan (C.b (next i) / C.a (next i)) ≤
        3 * Real.pi / 4 := by
    rw [he]
    exact (boundary_gap_upper C le_rfl i).le
  have hm : 0 ≤ Arithmetic.forwardMargin (axisOf (j.val + 1)) (sgnR (positiveOf C i))
      (sgnR (positiveOf C (next i))) (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
      (phaseValue F hgap i) := by
    rw [forwardMargin_actual]
    have hax : (axisOf (j.val + 1)).index = j := by fin_cases j <;> rfl
    rw [hax, ← sign_cast, ← sign_cast]
    exact original_margin C F hgap i j hj
  have h := hc hg1 hg2 hm
  push_cast at h
  linarith

lemma commonValue_eq (kind : RadialKind) (σ : Bool) (b : ℝ) :
    commonValue kind σ b = (commonQuad kind σ).eval (commonQuad kind σ).cLo
      (primaryValue kind b) b := by
  cases kind <;> cases σ <;>
    simp [commonValue, commonQuad, QuadLabel.signed, QuadLabel.neg, QuadLabel.eval,
      WordProblems.sign] <;> ring

lemma wrongValue_eq (w : WrongWord) (i : Vertex) (kind : RadialKind) (σ : Bool) (b : ℝ) :
    wrongValue w i kind σ b = (wrongQuad w i kind σ).eval (wrongQuad w i kind σ).cLo
      (primaryValue kind b) b := by
  cases w <;> cases σ <;>
    simp [wrongValue, wrongQuad, QuadLabel.signed, QuadLabel.neg, QuadLabel.eval,
      WordProblems.sign]
  ring

/-- On its radial curve the primary coordinate of a vertex is `primaryValue` of its transverse
coordinate. -/
lemma primary_vertex (C : BoundaryCycle Q0) (i : Vertex) : primaryValue (C.kind i) (C.b i) = C.a i :=
  (actual_primary (C.kind i) (by linarith [(Candidate.canonical_bounds C le_rfl i).1])
    (C.b_nonneg i) (C.b_le_a i) (C.boundary i)).1.symm

/-- For any marker `ψ`, the edge costs `φᵢ + ψᵢ - ψᵢ₊₁` add up to `2π`. -/
lemma marker_budget (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (marker : Vertex→ℝ) :
    (∑ i,(phaseValue F hgap i+marker i-marker (next i)))=2*Real.pi := by
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,sum_next,phase_sum C F hgap]
  ring

/-- At a core vertex the common marker is `σ` times the common core label. -/
lemma commonMarker_core_eq (C : BoundaryCycle Q0) (i : Vertex) (hk : C.kind i ≠ .outer) :
    commonMarker C i=C.sigma i*CorePairGeometry.label (73/10) (291/250) (C.a i) (C.b i) := by
  simp [commonMarker, commonValue, primary_vertex, hk, positiveOf_spec, CorePairGeometry.label]

/-- The cost of the edge `i` with the common markers exceeds `commonGamma` of its digit, for every
separating forward axis: by the separation of the centres when both squares are core, by the
common table otherwise. -/
lemma common_pair (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (commonGamma (F.word hgap pi_lt_22_over_7 i):ℝ)<
      phaseValue F hgap i+commonMarker C i-commonMarker C (next i) := by
  by_cases hcore : C.kind i ≠ .outer ∧ C.kind (next i) ≠ .outer
  · have h := CorePairGeometry.core_cost (Or.inr ⟨rfl, rfl⟩) C i hcore.1 hcore.2
    rw [← commonMarker_core_eq C i hcore.1, ← commonMarker_core_eq C (next i) hcore.2] at h
    have hγ : (commonGamma (F.word hgap pi_lt_22_over_7 i):ℝ) ≤ 391/400 := by
      generalize F.word hgap pi_lt_22_over_7 i = k
      fin_cases k <;> norm_num [commonGamma]
    linarith [phase_gap C F hgap i]
  have hP := commonTable_holds _ _ (commonPairProblem_mem (F.word hgap pi_lt_22_over_7 i)
    (C.kind i) (C.kind (next i)) (positiveOf C i) (positiveOf C (next i)) j (by tauto)
    (original_not_core_excluded C F hgap i j hj))
  have h := word_pair C F hgap i j hj _ _ _ hP le_rfl le_rfl
  rw [commonMarker, commonMarker, commonValue_eq, commonValue_eq, primary_vertex, primary_vertex]
  have hhi : ((commonQuad (C.kind (next i)) (positiveOf C (next i))).cLo : ℝ) =
      (commonQuad (C.kind (next i)) (positiveOf C (next i))).cHi := by
    cases C.kind (next i) <;> cases positiveOf C (next i) <;>
      simp [commonQuad, QuadLabel.signed, QuadLabel.neg]
  rw [hhi]
  exact h

lemma commonGamma_numerator (k : Fin 3) :
    (commonGamma k:ℝ)=(doubleWordCostNumerator k:ℝ)/10000 := by
  fin_cases k <;> norm_num [commonGamma,doubleWordCostNumerator]

/-- No digit of the quarter word of a cycle is `2`: the bounds `commonGamma` of the edge costs add
up to `6.295 > 2π` on every admissible word with a digit `2`. -/
theorem no_double (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) :
    ¬ ∃ i,F.word hgap pi_lt_22_over_7 i=2 := by
  apply no_double_word_of_cost_bound (F.word hgap pi_lt_22_over_7)
    (F.word_admissible hgap pi_lt_22_over_7)
    (fun i => phaseValue F hgap i+commonMarker C i-commonMarker C (next i))
  · intro i
    obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
    have h := common_pair C F hgap i j (by simpa [← hj] using C.feasible i)
    rw [commonGamma_numerator] at h
    exact h.le
  · exact (marker_budget C F hgap (commonMarker C)).le
  · exact pi_lt_22_over_7

/-- On a zero edge the sign does not go from `-1` to `+1`: the gap would be at most the frame
difference, below `7/10`, while it exceeds `19/25`. -/
lemma zero_not_negative_positive (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex)
    (hz : F.word hgap pi_lt_22_over_7 i=0) :
    ¬ (positiveOf C i=false ∧ positiveOf C (next i)=true) := by
  rintro ⟨hs,ht⟩
  have hs' := alpha_nonpos C i hs
  have ht' := alpha_nonneg C (next i) ht
  have hd := (abs_lt.mp (difference_small F i)).2
  have he := phase_gap C F hgap i
  simp only [phaseValue,hz,Fin.val_zero,Nat.cast_zero,zero_mul,zero_div,add_zero] at he
  linarith [hgap i]

/-- On the words `0010111` and `0011011` the two initial zero digits force `α₀ > 0` and `α₂ < 0`:
the gaps of the edges `0` and `1` exceed `19/25`, while `θ₂ - θ₀` is below `7/10` and each `αᵢ`
lies in `[-π/4, π/4]`. -/
lemma initial_signs (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (w : WrongWord)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord w) :
    positiveOf C 0=true ∧ positiveOf C 2=false := by
  have hz0 : F.word hgap pi_lt_22_over_7 0=0 := by cases w <;> simp [hw,wrongWord]
  have hz1 : F.word hgap pi_lt_22_over_7 1=0 := by cases w <;> simp [hw,wrongWord]
  have h0 := phase_gap C F hgap 0
  have h1 := phase_gap C F hgap 1
  simp only [phaseValue,hz0,Fin.val_zero,Nat.cast_zero,zero_mul,zero_div,add_zero] at h0
  simp only [phaseValue,hz1,Fin.val_zero,Nat.cast_zero,zero_mul,zero_div,add_zero] at h1
  norm_num [difference,next] at h0 h1
  have ht := (abs_lt.mp (theta_spread F 0 2)).2
  have hd : 41/50<C.alpha 0-C.alpha 2 := by linarith [hgap 0,hgap 1]
  have ha := C.alpha_range 0
  have hb := C.alpha_range 2
  have hapos : 0<C.alpha 0 := by linarith [pi_lt_22_over_7]
  have hbneg : C.alpha 2<0 := by linarith [pi_lt_22_over_7]
  exact ⟨positiveOf_of_alpha_pos C 0 hapos,positiveOf_of_alpha_neg C 2 hbneg⟩

/-- On a cycle with the word `w`, the signs of the two squares of each edge are allowed
(`allowed`). -/
lemma actual_allowed (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (w : WrongWord)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord w) (i : Vertex) :
    allowed w i (positiveOf C i) (positiveOf C (next i)) := by
  obtain ⟨h0,h2⟩ := initial_signs C F hgap w hw
  refine ⟨?_,?_,?_,?_,?_⟩
  · rintro rfl
    exact h0
  · rintro rfl
    exact h2
  · intro hi
    simpa [hi] using h0
  · intro hi
    simpa [hi] using h2
  · intro hz
    exact zero_not_negative_positive C F hgap i (by simpa [hw] using hz)

/-- On a cycle with the word `w`, the cost of the edge `i` with the markers of `w` exceeds
`wrongGamma w i`, for every separating forward axis. -/
lemma wrong_pair (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (w : WrongWord)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord w) (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (wrongGamma w i:ℝ)<phaseValue F hgap i+wrongMarker C w i-wrongMarker C w (next i) := by
  have hP := wrongTable_holds w i _ (wrongPairProblem_mem w i (C.kind i) (C.kind (next i))
    (positiveOf C i) (positiveOf C (next i)) j (actual_allowed C F hgap w hw i)
    (by simpa [hw] using original_not_core_excluded C F hgap i j hj))
  have hk : wordHalves (wrongWord w i).val =
      wordHalves (F.word hgap pi_lt_22_over_7 i).val := by rw [hw]
  simp only [wrongPairProblem, hk] at hP
  have h := word_pair C F hgap i j hj _ _ _ hP le_rfl le_rfl
  rw [wrongMarker, wrongMarker, wrongValue_eq, wrongValue_eq, primary_vertex, primary_vertex]
  have hhi : ((wrongQuad w (next i) (C.kind (next i)) (positiveOf C (next i))).cLo : ℝ) =
      (wrongQuad w (next i) (C.kind (next i)) (positiveOf C (next i))).cHi := by
    cases w <;> cases positiveOf C (next i) <;> simp [wrongQuad, QuadLabel.signed, QuadLabel.neg]
  rw [hhi]
  exact h

lemma wrongGamma_sum (w : WrongWord) :
    (710/113:ℝ)<∑ i,(wrongGamma w i:ℝ) := by
  cases w <;> norm_num [wrongGamma,Fin.sum_univ_succ]

/-- The quarter word of a cycle is neither `0010111` nor `0011011`: the bounds `wrongGamma` of the
edge costs add up to more than `2π`. -/
theorem wrong_word_impossible (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (w : WrongWord) :
    F.word hgap pi_lt_22_over_7 ≠ wrongWord w := by
  intro hw
  have hcost (i : Vertex) : (wrongGamma w i:ℝ) ≤
      phaseValue F hgap i+wrongMarker C w i-wrongMarker C w (next i) := by
    obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
    exact (wrong_pair C F hgap w hw i j (by simpa [← hj] using C.feasible i)).le
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcost i)
  rw [marker_budget C F hgap (wrongMarker C w)] at hh
  linarith [wrongGamma_sum w,two_pi_lt_710_over_113]

/-- The cycle action that takes a word `quarterDihedral shift reversed v` to `v`: its edge `i` is
the edge `i - shift`, or `shift - i` when reversed. A reflection reverses each edge, which adds
`1` to the vertex shift. -/
def normalizingAction (shift : Vertex) (reversed : Bool) : CycleAction where
  shift := if reversed then shift+1 else -shift
  reversed := reversed
  rotation := 0

lemma normalizing_edge (shift : Vertex) (reversed : Bool) (i : Vertex) :
    (if reversed then shift-(normalizingAction shift reversed).edge i
      else (normalizingAction shift reversed).edge i+shift)=i := by
  cases reversed <;>
    simp [normalizingAction,CycleAction.edge,CycleAction.index,next]

/-- The word of the lift moved by `G` is the word of the lift on the edges of `G`. -/
lemma word_act (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (G : CycleAction) :
    (F.act G).word (boundary_gap_lower (G.boundary C) le_rfl) pi_lt_22_over_7=
      fun i => F.word hgap pi_lt_22_over_7 (G.edge i) := by
  funext i
  apply Fin.ext
  change (integerQuarterIncrement (G.quarter F.quarter) i).toNat=
    (integerQuarterIncrement F.quarter (G.edge i)).toNat
  rw [G.quarter_increment]

/-- A word equivalent to `v` is taken to `v` by a cycle action. -/
lemma normalize_word (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (v : QuarterWord)
    (hv : (F.word hgap pi_lt_22_over_7).DihedralEquivalent v) :
    ∃ G : CycleAction,
      (F.act G).word (boundary_gap_lower (G.boundary C) le_rfl) pi_lt_22_over_7=v := by
  obtain ⟨shift,reversed,hword⟩ := hv
  refine ⟨normalizingAction shift reversed,?_⟩
  rw [word_act C F hgap]
  funext i
  rw [hword]
  change v (if reversed then shift-(normalizingAction shift reversed).edge i
    else (normalizingAction shift reversed).edge i+shift)=v i
  rw [normalizing_edge]

/-- The quarter word of a cycle is not equivalent to any of the six representatives other than the
candidate: four have a digit `2` (`no_double`), and the other two are the words of
`wrong_word_impossible`. Every rotation and reflection is covered by `normalize_word`. -/
theorem six_exclusions (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (j : Fin 6) :
    ¬ (F.word hgap pi_lt_22_over_7).DihedralEquivalent (quarterRepresentatives j.castSucc) := by
  intro heq
  obtain ⟨G,hword⟩ := normalize_word C F hgap (quarterRepresentatives j.castSucc) heq
  let D := G.boundary C
  let H := F.act G
  have hg : ∀ i,19/25<angleGap D.beta i := boundary_gap_lower D le_rfl
  have he : H.word hg pi_lt_22_over_7=quarterRepresentatives j.castSucc := hword
  fin_cases j
  · apply no_double D H hg
    exact ⟨6,by rw [he]; norm_num [quarterRepresentatives]⟩
  · apply no_double D H hg
    exact ⟨6,by rw [he]; norm_num [quarterRepresentatives]⟩
  · apply no_double D H hg
    exact ⟨4,by rw [he]; norm_num [quarterRepresentatives]⟩
  · apply no_double D H hg
    exact ⟨6,by rw [he]; norm_num [quarterRepresentatives]⟩
  · apply wrong_word_impossible D H hg .short
    simpa [quarterRepresentatives,wrongWord] using he
  · apply wrong_word_impossible D H hg .second
    simpa [quarterRepresentatives,wrongWord] using he

end SquaresInCircles.Eight.WordGeometry

namespace SquaresInCircles.Eight

/-- The quarter word of a boundary cycle at the level `Q0` is equivalent to the candidate word
`0101011`. -/
theorem quarter_word_candidate (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) :
    (F.word hgap pi_lt_22_over_7).DihedralEquivalent candidateQuarterWord := by
  exact candidate_word_after_six_exclusions _ (F.word_admissible hgap pi_lt_22_over_7)
    (WordGeometry.six_exclusions C F hgap)

end SquaresInCircles.Eight
