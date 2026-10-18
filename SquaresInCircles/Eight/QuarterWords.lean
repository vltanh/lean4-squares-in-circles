module

public import SquaresInCircles.Eight.Frames
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Complete quarter-word classification

Source: `SEVEN_QUARTER_WORDS.md`. Every ordered word is included before the
dihedral quotient. The finite classification concerns quarter increments,
not radial kinds: no outer/core word is removed here.

All enumeration proofs below use ordinary `decide`. They are source drafts
and have not been evaluated by Lean or by a native checker in this session.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight

abbrev QuarterWord := Vertex → Fin 3

def QuarterWord.Admissible (w : QuarterWord) : Prop :=
  (∑ i, (w i).val) = 4 ∧
    ∀ i, ¬ (w i = 0 ∧ w (next i) = 0 ∧ w (next (next i)) = 0)

instance (w : QuarterWord) : Decidable (QuarterWord.Admissible w) := inferInstance

/-- The seven representatives, in the manuscript order. -/
def quarterRepresentatives : Fin 7 → QuarterWord :=
  ![![0, 0, 1, 0, 0, 1, 2],
    ![0, 0, 1, 0, 1, 0, 2],
    ![0, 0, 1, 0, 2, 0, 1],
    ![0, 0, 1, 1, 0, 0, 2],
    ![0, 0, 1, 0, 1, 1, 1],
    ![0, 0, 1, 1, 0, 1, 1],
    ![0, 1, 0, 1, 0, 1, 1]]

def candidateQuarterWord : QuarterWord := quarterRepresentatives 6

/-- Rotation and reflection are kept explicit, including their index action. -/
def quarterDihedral (shift : Vertex) (reversed : Bool) (w : QuarterWord) : QuarterWord :=
  fun i => w (if reversed then shift - i else i + shift)

def QuarterWord.DihedralEquivalent (w v : QuarterWord) : Prop :=
  ∃ shift reversed, w = quarterDihedral shift reversed v

instance (w v : QuarterWord) : Decidable (QuarterWord.DihedralEquivalent w v) := inferInstance

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem quarter_word_complete_classification :
    ∀ w : QuarterWord, w.Admissible →
      ∃ j : Fin 7, w.DihedralEquivalent (quarterRepresentatives j) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem admissible_quarter_word_count :
    (Finset.univ.filter QuarterWord.Admissible).card = 70 := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem quarter_representatives_inequivalent :
    ∀ i j : Fin 7, (quarterRepresentatives i).DihedralEquivalent (quarterRepresentatives j) →
      i = j := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem quarter_word_at_most_one_double :
    ∀ w : QuarterWord, w.Admissible → (Finset.univ.filter (fun i => w i = 2)).card ≤ 1 := by
  decide

lemma quarterDihedral_preserves_admissibility :
    ∀ (shift : Vertex) (reversed : Bool) (w : QuarterWord),
      (quarterDihedral shift reversed w).Admissible ↔ w.Admissible := by
  decide

lemma candidate_quarter_admissible : candidateQuarterWord.Admissible := by decide

/-- Raw integer increment, including the winding contribution on the last
edge. This is four full quarter turns, not an assumed word sum. -/
def integerQuarterIncrement (m : Vertex → ℤ) (i : Vertex) : ℤ :=
  m (next i) - m i + if i = 6 then 4 else 0

lemma integerQuarterIncrement_sum (m : Vertex → ℤ) :
    ∑ i, integerQuarterIncrement m i = 4 := by
  simp [integerQuarterIncrement, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_next]

/-- Real frame lifts with their actual quarter representatives. The source
frames are recovered by the equality `beta+alpha=theta+m*pi/2`. -/
structure QuarterLift {q : ℝ} (C : BoundaryCycle q) where
  theta : Vertex → ℝ
  quarter : Vertex → ℤ
  left : ℝ
  diameter : ℝ
  small : diameter < 7 / 10
  theta_range : ∀ i, left ≤ theta i ∧ theta i ≤ left + diameter
  represents : ∀ i, C.beta i + C.alpha i = theta i + (quarter i : ℝ) * (Real.pi / 2)

lemma BoundaryCycle.alpha_range {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    -Real.pi / 4 ≤ C.alpha i ∧ C.alpha i ≤ Real.pi / 4 := by
  have ht := C.tangent_mem i
  have hl := Real.arctan_le_arctan ht.1
  have hu := Real.arctan_le_arctan ht.2
  simpa [BoundaryCycle.alpha, Real.arctan_neg, Real.arctan_one, neg_div] using And.intro hl hu

lemma QuarterLift.edge_identity {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C) (i : Vertex) :
    angleGap C.beta i = F.theta (next i) - F.theta i +
      (integerQuarterIncrement F.quarter i : ℝ) * (Real.pi / 2) + C.alpha i - C.alpha (next i) := by
  have h₁ := F.represents i
  have h₂ := F.represents (next i)
  by_cases hi : i = 6
  · simp only [angleGap, integerQuarterIncrement, hi, if_true, Int.cast_add,
      Int.cast_sub, Int.cast_ofNat]
    linarith
  · simp only [angleGap, integerQuarterIncrement, hi, if_false, add_zero, Int.cast_sub]
    linarith

/-- Digit restriction with every range and radius-independent angle input
visible. It is applied only after the common-point gap theorem. -/
lemma quarter_digit_range {δ ε a b D : ℝ} {k : ℤ}
    (hδ : 19 / 25 < δ ∧ δ < 2 * Real.pi - 114 / 25)
    (hε : -D ≤ ε ∧ ε ≤ D) (hD : D < 7 / 10)
    (ha : -Real.pi / 4 ≤ a ∧ a ≤ Real.pi / 4)
    (hb : -Real.pi / 4 ≤ b ∧ b ≤ Real.pi / 4)
    (he : δ = ε + (k : ℝ) * (Real.pi / 2) + a - b)
    (hpi : Real.pi < 22 / 7) : 0 ≤ k ∧ k ≤ 2 := by
  constructor
  · by_contra! hn
    have hk : k ≤ -1 := by omega
    have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast hk
    have hm := mul_le_mul_of_nonneg_right hk' (show 0 ≤ Real.pi / 2 by positivity)
    linarith [hδ.1, hε.2, ha.2, hb.1]
  · by_contra! hn
    have hk : 3 ≤ k := by omega
    have hk' : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hm := mul_le_mul_of_nonneg_right hk' (show 0 ≤ Real.pi / 2 by positivity)
    linarith [hδ.2, hε.1, ha.1, hb.2]

lemma QuarterLift.digit_range {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C)
    (hgap : ∀ i, 19 / 25 < angleGap C.beta i)
    (hpi : Real.pi < 22 / 7) (i : Vertex) :
    0 ≤ integerQuarterIncrement F.quarter i ∧ integerQuarterIncrement F.quarter i ≤ 2 := by
  have hsum := angleGap_sum C.beta
  have hupper : angleGap C.beta i < 2 * Real.pi - 114 / 25 := by
    have hrest := Finset.sum_lt_sum (s := Finset.univ.erase i)
      (fun j _ => (hgap j).le)
      (by
        obtain ⟨j, hj⟩ := Finset.card_pos.mp
          (show 0 < (Finset.univ.erase i : Finset Vertex).card by simp)
        exact ⟨j, hj, hgap j⟩)
    have hsplit := Finset.sum_erase_add (s := Finset.univ) (f := angleGap C.beta)
      (Finset.mem_univ i)
    norm_num at hrest
    linarith
  apply quarter_digit_range ⟨hgap i, hupper⟩
    (D := F.diameter) (ε := F.theta (next i) - F.theta i)
    (a := C.alpha i) (b := C.alpha (next i))
  · constructor <;> linarith [(F.theta_range i).1, (F.theta_range i).2,
      (F.theta_range (next i)).1, (F.theta_range (next i)).2]
  · exact F.small
  · exact C.alpha_range i
  · exact C.alpha_range (next i)
  · exact F.edge_identity i
  · exact hpi

lemma QuarterLift.no_three_zero_increments {q : ℝ} {C : BoundaryCycle q}
    (F : QuarterLift C) (hgap : ∀ i, 19 / 25 < angleGap C.beta i)
    (hpi : Real.pi < 22 / 7) (i : Vertex) :
    ¬ (integerQuarterIncrement F.quarter i = 0 ∧
      integerQuarterIncrement F.quarter (next i) = 0 ∧
      integerQuarterIncrement F.quarter (next (next i)) = 0) := by
  rintro ⟨hi, hj, hk⟩
  have h₁ := F.edge_identity i
  have h₂ := F.edge_identity (next i)
  have h₃ := F.edge_identity (next (next i))
  rw [hi] at h₁
  rw [hj] at h₂
  rw [hk] at h₃
  norm_num at h₁ h₂ h₃
  have hlo := (F.theta_range i).1
  have hhi := (F.theta_range (next (next (next i)))).2
  have ha := (C.alpha_range i).2
  have hb := (C.alpha_range (next (next (next i)))).1
  linarith [hgap i, hgap (next i), hgap (next (next i)), F.small]

def QuarterLift.word {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C)
    (hgap : ∀ i, 19 / 25 < angleGap C.beta i) (hpi : Real.pi < 22 / 7) : QuarterWord :=
  fun i => ⟨(integerQuarterIncrement F.quarter i).toNat,
    by have h := F.digit_range hgap hpi i; omega⟩

lemma QuarterLift.word_cast {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C)
    (hgap : ∀ i, 19 / 25 < angleGap C.beta i) (hpi : Real.pi < 22 / 7) (i : Vertex) :
    ((F.word hgap hpi i).val : ℤ) = integerQuarterIncrement F.quarter i := by
  exact Int.toNat_of_nonneg (F.digit_range hgap hpi i).1

theorem QuarterLift.word_admissible {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C)
    (hgap : ∀ i, 19 / 25 < angleGap C.beta i) (hpi : Real.pi < 22 / 7) :
    (F.word hgap hpi).Admissible := by
  constructor
  · have hsum := integerQuarterIncrement_sum F.quarter
    have he : (∑ i, ((F.word hgap hpi i).val : ℤ)) = 4 := by
      simpa only [F.word_cast hgap hpi] using hsum
    exact_mod_cast he
  · intro i hi
    apply F.no_three_zero_increments hgap hpi i
    refine ⟨?_, ?_, ?_⟩
    · have he := F.word_cast hgap hpi i
      rw [hi.1] at he
      norm_num at he
      exact he.symm
    · have he := F.word_cast hgap hpi (next i)
      rw [hi.2.1] at he
      norm_num at he
      exact he.symm
    · have he := F.word_cast hgap hpi (next (next i))
      rw [hi.2.2] at he
      norm_num at he
      exact he.symm

theorem QuarterLift.seven_classes {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C)
    (hgap : ∀ i, 19 / 25 < angleGap C.beta i) (hpi : Real.pi < 22 / 7) :
    ∃ j : Fin 7, (F.word hgap hpi).DihedralEquivalent (quarterRepresentatives j) :=
  quarter_word_complete_classification _ (F.word_admissible hgap hpi)

/-- The common three-increment table's exact per-digit lower constants. -/
def doubleWordCostNumerator : Fin 3 → ℕ := ![9775, 7850, 8150]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem double_word_cost_numerator :
    ∀ w : QuarterWord, w.Admissible → (∃ i, w i = 2) →
      (∑ i, doubleWordCostNumerator (w i)) = 62950 := by
  decide

/-- Finite summation of the continuous common-table inequalities excludes
every double-increment word at once. The continuous inequalities remain
explicit arguments of this intermediate theorem. -/
lemma no_double_word_of_cost_bound (w : QuarterWord) (hw : w.Admissible)
    (cost : Vertex → ℝ)
    (hcost : ∀ i, (doubleWordCostNumerator (w i) : ℝ) / 10000 ≤ cost i)
    (hbudget : ∑ i, cost i ≤ 2 * Real.pi) (hpi : Real.pi < 22 / 7) :
    ¬ ∃ i, w i = 2 := by
  intro hd
  have hn := double_word_cost_numerator w hw hd
  have he : ∑ i, (doubleWordCostNumerator (w i) : ℝ) = 62950 := by exact_mod_cast hn
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcost i)
  rw [← Finset.sum_div, he] at hh
  linarith

/-- The finite assembler only selects the remaining class after its six
continuous geometric exclusions have been provided. -/
lemma candidate_word_after_six_exclusions (w : QuarterWord) (hw : w.Admissible)
    (hexcluded : ∀ j : Fin 6, ¬ w.DihedralEquivalent (quarterRepresentatives j.castSucc)) :
    w.DihedralEquivalent candidateQuarterWord := by
  obtain ⟨j, hj⟩ := quarter_word_complete_classification w hw
  by_cases hlast : j = 6
  · simpa [candidateQuarterWord, hlast] using hj
  · have hjlt : j.val < 6 := by omega
    exact (hexcluded ⟨j.val, hjlt⟩ (by simpa using hj)).elim

end SquaresInCircles.Eight
