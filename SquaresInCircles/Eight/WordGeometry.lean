module

public import SquaresInCircles.Eight.Generated.PairsWords
public import SquaresInCircles.Eight.Arithmetic.WordProblems
public import SquaresInCircles.Eight.CycleActions
public import SquaresInCircles.Eight.Arithmetic.CorePairGeometry
public import SquaresInCircles.Eight.Candidate.GeometricCoreQuarter

/-!
# Actual geometric exclusion of the six noncandidate quarter words

The common increment costs first exclude every word containing a two: on an
edge between two core vertices from the separation of the centres
(`CorePairGeometry.core_cost`), on the other edges from the common table.
The two remaining wrong words use their separate role-dependent label
systems.  A marker is evaluated once per vertex, so the target value on
one edge is exactly the source value on the next edge.

Each pair inequality is a problem of a pair table (`Generated/Pairs`): its
ends carry the actual radial charts, signs and labels, and the table proves
it for every state pair and frame difference `|d| ≤ 7/10` with the physical
gap and the original separating-axis margin. The tables leave out the kinds,
signs and axes that no feasible separator has (`original_not_core_excluded`).
The nineteen allowed sign cases follow from the two initial zero increments and
the impossibility of a negative-to-positive zero edge.

Dihedral normalization acts on actual squares and lifts through
`CycleAction.boundary` and `QuarterLift.act`.  In particular reflection
reverses an edge before transporting its separating axis.  The extra one
in the reflected vertex shift accounts for that endpoint reversal.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.WordGeometry

open Arithmetic Arithmetic.PairCover WordProblems

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
  simp only [WordProblems.sign,Bool.false_eq_true,if_false,Rat.cast_neg,Rat.cast_one,neg_one_mul]
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

def difference {C : BoundaryCycle Q0} (F : QuarterLift C) (i : Vertex) : ℝ :=
  F.theta (next i)-F.theta i

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
    simp [relativeC,hci,hsi,hcj,hsj,Real.cos_sub] <;> ring
  have hs : relativeS (C.square i) (C.square (next i))=
      Real.sin (C.canonicalAngle (next i)-C.canonicalAngle i) := by
    simp [relativeS,hci,hsi,hcj,hsj,Real.sin_sub] <;> ring
  rw [canonical_phase C F hgap i] at hc hs
  by_cases hi : i=6 <;>
    simpa [hi,Real.cos_sub,Real.sin_sub] using And.intro hc hs

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

/-- No feasible original axis of an edge is in a class of `CoreSeparatorExcluded`: a primary
axis on a zero edge needs an outer far square, a secondary axis against a core square needs
the transverse sign pointing outward, and no axis separates two core squares of opposite signs
on a quarter edge. -/
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

def commonValue (kind : RadialKind) (σ : Bool) (b : ℝ) : ℝ :=
  let a := primaryValue kind b
  (WordProblems.sign σ:ℝ)*(if kind=.outer then -9/100+(13/200)*a+(203/200)*b
    else (73/10)*(7/12-a)+(291/250)*b)

def commonMarker (C : BoundaryCycle Q0) (i : Vertex) : ℝ :=
  commonValue (C.kind i) (positiveOf C i) (C.b i)

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

def wrongMarker (C : BoundaryCycle Q0) (w : WrongWord) (i : Vertex) : ℝ :=
  wrongValue w i (C.kind i) (positiveOf C i) (C.b i)

/-! ### The pair tables -/

/-- The tangent range of a radial kind. -/
def kindRange : RadialKind → QInterval
  | .outer => ⟨0, 1⟩
  | .coreSide => ⟨0, 6/7⟩
  | .coreCorner => ⟨6/7, 1⟩

/-- The end of a pair at a vertex of radial kind `kind`, sign `σ` and label `L`. -/
def kindEnd (kind : RadialKind) (σ : Bool) (L : QuadLabel) : PairEnd :=
  ⟨decide (kind = .outer), decide (kind = .coreSide), σ, kindRange kind, L⟩

/-- The common label of a radial kind with the sign `σ`. -/
def commonQuad (kind : RadialKind) (σ : Bool) : QuadLabel :=
  (if kind = .outer then (⟨-9/100, -9/100, 13/200, 203/200, 0, 0⟩ : QuadLabel)
    else ⟨73/10*(7/12), 73/10*(7/12), -(73/10), 291/250, 0, 0⟩).signed σ

/-- The label of a wrong word at a role, for a radial kind and the sign `σ`. -/
def wrongQuad (w : WrongWord) (i : Vertex) (kind : RadialKind) (σ : Bool) : QuadLabel :=
  match w with
  | .short =>
      let v := shortCoefficients i (radialIndex kind) (signIndex σ)
      ⟨v 0/100000, v 0/100000, v 1/100000, sign σ*v 2/100000, 0, 0⟩
  | .second =>
      let v := secondCoefficients i (radialIndex kind) (signIndex σ)
      (⟨v 0/100000, v 0/100000, v 1/100000, v 2/100000, v 3/100000, v 4/100000⟩ : QuadLabel).signed σ

/-- The two halves `(k, ±, 7/10)` of the frame difference, with `u⁺` over `10⁸`. -/
def wordHalves (k : ℕ) : List (ℕ × Bool × ℕ) := [(k, true, 70000000), (k, false, 70000000)]

/-- The pair problem of a common increment `k`. -/
def commonPairProblem (k : Fin 3) (ks kt : RadialKind) (σ τ : Bool) (j : Fin 4) : PairProblem :=
  ⟨kindEnd ks σ (commonQuad ks σ), kindEnd kt τ (commonQuad kt τ), axisOf (j.val + 1), 0,
    commonGamma k, wordHalves k.val⟩

/-- The pair problem of the edge `i` of a wrong word. -/
def wrongPairProblem (w : WrongWord) (i : Vertex) (ks kt : RadialKind) (σ τ : Bool) (j : Fin 4) :
    PairProblem :=
  ⟨kindEnd ks σ (wrongQuad w i ks σ), kindEnd kt τ (wrongQuad w (next i) kt τ),
    axisOf (j.val + 1), 0, wrongGamma w i, wordHalves (wrongWord w i).val⟩

/-- The common tables. -/
def commonTable : Fin 3 → List PairProblem :=
  ![Generated.Pairs.Common0.problems, Generated.Pairs.Common1.problems,
    Generated.Pairs.Common2.problems]

/-- The tables of the edges of the wrong words. -/
def wrongTable : WrongWord → Vertex → List PairProblem
  | .short => ![Generated.Pairs.Short0.problems, Generated.Pairs.Short1.problems,
      Generated.Pairs.Short2.problems, Generated.Pairs.Short3.problems,
      Generated.Pairs.Short4.problems, Generated.Pairs.Short5.problems,
      Generated.Pairs.Short6.problems]
  | .second => ![Generated.Pairs.Second0.problems, Generated.Pairs.Second1.problems,
      Generated.Pairs.Second2.problems, Generated.Pairs.Second3.problems,
      Generated.Pairs.Second4.problems, Generated.Pairs.Second5.problems,
      Generated.Pairs.Second6.problems]

theorem commonTable_holds (k : Fin 3) :
    ∀ P ∈ commonTable k, P.Holds ((9789/2500 : ℚ) : ℝ) 100000000 := by
  fin_cases k
  · exact Generated.Pairs.Common0.sound
  · exact Generated.Pairs.Common1.sound
  · exact Generated.Pairs.Common2.sound

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

theorem commonPairProblem_mem : ∀ (k : Fin 3) (ks kt : RadialKind) (σ τ : Bool) (j : Fin 4),
    (ks = .outer ∨ kt = .outer) → ¬ CoreSeparatorExcluded k ks kt σ τ j →
      commonPairProblem k ks kt σ τ j ∈ commonTable k := by
  decide +kernel

theorem wrongPairProblem_mem : ∀ (w : WrongWord) (i : Vertex) (ks kt : RadialKind)
    (σ τ : Bool) (j : Fin 4), allowed w i σ τ →
      ¬ CoreSeparatorExcluded (wrongWord w i) ks kt σ τ j →
      wrongPairProblem w i ks kt σ τ j ∈ wrongTable w i := by
  decide +kernel

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

/-- A pair problem of the tables with the actual ends of the edge `i` gives the charged
inequality of the edge, for every admissible pair of label constants. -/
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
      WordProblems.sign] <;> ring

lemma primary_vertex (C : BoundaryCycle Q0) (i : Vertex) : primaryValue (C.kind i) (C.b i) = C.a i :=
  (actual_primary (C.kind i) (by linarith [(Candidate.canonical_bounds C le_rfl i).1])
    (C.b_nonneg i) (C.b_le_a i) (C.boundary i)).1.symm

lemma marker_budget (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (marker : Vertex→ℝ) :
    (∑ i,(phaseValue F hgap i+marker i-marker (next i)))=2*Real.pi := by
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,sum_next,phase_sum C F hgap]
  ring

/-- At a core vertex the common marker is `σ` times the common core label. -/
lemma commonMarker_core_eq (C : BoundaryCycle Q0) (i : Vertex) (hk : C.kind i ≠ .outer) :
    commonMarker C i=C.sigma i*CorePairGeometry.label (73/10) (291/250) (C.a i) (C.b i) := by
  simp [commonMarker, commonValue, primary_vertex, hk, positiveOf_spec, CorePairGeometry.label]

/-- The common cost of an edge for every feasible original axis: from the separation of the
centres when both vertices are core, from the common table otherwise. -/
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

/-- The two initial zero increments force strictly positive alpha at role
0 and strictly negative alpha at role 2, without a sign choice by search. -/
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

/-- Normalizing the EDGE word requires an extra vertex shift in the
reflected case.  The physical action itself is the shared actual-square
action, with its complete signed-axis transport. -/
def normalizingAction (shift : Vertex) (reversed : Bool) : CycleAction where
  shift := if reversed then shift+1 else -shift
  reversed := reversed
  rotation := 0

lemma normalizing_edge (shift : Vertex) (reversed : Bool) (i : Vertex) :
    (if reversed then shift-(normalizingAction shift reversed).edge i
      else (normalizingAction shift reversed).edge i+shift)=i := by
  cases reversed <;>
    simp [normalizingAction,CycleAction.edge,CycleAction.index,next] <;> abel

lemma word_act (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (G : CycleAction) :
    (F.act G).word (boundary_gap_lower (G.boundary C) le_rfl) pi_lt_22_over_7=
      fun i => F.word hgap pi_lt_22_over_7 (G.edge i) := by
  funext i
  apply Fin.ext
  change (integerQuarterIncrement (G.quarter F.quarter) i).toNat=
    (integerQuarterIncrement F.quarter (G.edge i)).toNat
  rw [G.quarter_increment]

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

/-- All six representatives are excluded as actual geometric cycles,
including every cyclic shift and every reflected orientation. -/
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

/-- The complete quarter-word reduction, now supplied with all six actual
continuous exclusions.  No word-exclusion premise remains. -/
theorem quarter_word_candidate (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) :
    (F.word hgap pi_lt_22_over_7).DihedralEquivalent candidateQuarterWord := by
  exact candidate_word_after_six_exclusions _ (F.word_admissible hgap pi_lt_22_over_7)
    (WordGeometry.six_exclusions C F hgap)

end SquaresInCircles.Eight
