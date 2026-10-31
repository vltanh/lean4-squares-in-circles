module

public import SquaresInCircles.Eight.Boundary.Frames
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Eight squares: quarter words

The quarter word of a boundary cycle records, for each edge, how many quarter turns the
canonical frame of the target is ahead of that of the source (`QuarterLift.word`). An admissible
word has digits `0`, `1`, `2` adding up to `4` and no three consecutive zeros, cyclically. Up to
rotation and reflection of the cycle there are seven admissible words
(`quarter_word_complete_classification`); the last, `0101011`, is the word of the optimal packing
(`candidateQuarterWord`). The classification covers every ordered word before the quotient by
these symmetries, and it concerns the quarter increments only, whatever the radial curves of the
squares.

The classification runs through all `3 ^ 7` words as digit vectors: the kernel evaluates
Boolean checks on the seven digits and never enumerates the function type itself. The summed
cost bound of words with a digit `2` follows instead by counting
(`double_word_cost_numerator`): no three consecutive zeros forces at least three occupied
positions, so a word of total sum four with a `2` has exactly one `2`, two `1`s and four zeros.

If the frames lie in an interval shorter than `7/10` and the gaps exceed `19/25`, the word of the
cycle is admissible (`QuarterLift.word_admissible`): a digit below `0` or above `2` would make a
gap too small or too large, and three zeros would make three consecutive gaps add up to less than
`7/10 + π/2`. The words with a `2` are excluded together by summing one table of costs
(`no_double_word_of_cost_bound`), and once the six other classes are excluded, the candidate word
remains (`candidate_word_after_six_exclusions`); the cost bounds are proved in
`Boundary/Pairs.lean`.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight

abbrev QuarterWord := Vertex → Fin 3

def QuarterWord.Admissible (w : QuarterWord) : Prop :=
  (∑ i, (w i).val) = 4 ∧
    ∀ i, ¬ (w i = 0 ∧ w (next i) = 0 ∧ w (next (next i)) = 0)

/-- The seven representatives `0010012`, `0010102`, `0010201`, `0011002`, `0010111`, `0011011`
and `0101011`. -/
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

/-! ### Words as digit vectors

A word is determined by its seven digits, so a statement about all words is a
statement about seven digits in `Fin 3`. The kernel checks such statements on
the Boolean functions below. -/

/-- Every word is the vector of its seven digits. -/
private theorem QuarterWords.eq_vec (w : QuarterWord) :
    w = ![w 0, w 1, w 2, w 3, w 4, w 5, w 6] := by
  funext i
  fin_cases i <;> rfl

private theorem QuarterWords.forall_vertex {Q : Vertex → Prop} :
    (∀ i, Q i) ↔ Q 0 ∧ Q 1 ∧ Q 2 ∧ Q 3 ∧ Q 4 ∧ Q 5 ∧ Q 6 :=
  ⟨fun h => ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6⟩,
    fun ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ i => by fin_cases i <;> assumption⟩

/-- Admissibility of the word with digits `a₀, …, a₆`, written out. -/
private def QuarterWords.admissibleDigits (a₀ a₁ a₂ a₃ a₄ a₅ a₆ : Fin 3) : Bool :=
  a₀.val + a₁.val + a₂.val + a₃.val + a₄.val + a₅.val + a₆.val == 4 &&
    !(a₀ == 0 && a₁ == 0 && a₂ == 0) && !(a₁ == 0 && a₂ == 0 && a₃ == 0) &&
    !(a₂ == 0 && a₃ == 0 && a₄ == 0) && !(a₃ == 0 && a₄ == 0 && a₅ == 0) &&
    !(a₄ == 0 && a₅ == 0 && a₆ == 0) && !(a₅ == 0 && a₆ == 0 && a₀ == 0) &&
    !(a₆ == 0 && a₀ == 0 && a₁ == 0)

private theorem QuarterWords.admissible_vec (a₀ a₁ a₂ a₃ a₄ a₅ a₆ : Fin 3) :
    QuarterWord.Admissible ![a₀, a₁, a₂, a₃, a₄, a₅, a₆] ↔
      QuarterWords.admissibleDigits a₀ a₁ a₂ a₃ a₄ a₅ a₆ = true := by
  simp [QuarterWord.Admissible, QuarterWords.admissibleDigits, Fin.sum_univ_seven,
    QuarterWords.forall_vertex, next, and_assoc, -not_and, not_and_or, or_assoc]

/-- Some rotation or reflection of a representative has the digits `a₀, …, a₆`. -/
private def QuarterWords.isImage (a₀ a₁ a₂ a₃ a₄ a₅ a₆ : Fin 3) : Bool :=
  (List.finRange 7).any fun j => (List.finRange 7).any fun s => [false, true].any fun r =>
    a₀ == quarterDihedral s r (quarterRepresentatives j) 0 &&
    a₁ == quarterDihedral s r (quarterRepresentatives j) 1 &&
    a₂ == quarterDihedral s r (quarterRepresentatives j) 2 &&
    a₃ == quarterDihedral s r (quarterRepresentatives j) 3 &&
    a₄ == quarterDihedral s r (quarterRepresentatives j) 4 &&
    a₅ == quarterDihedral s r (quarterRepresentatives j) 5 &&
    a₆ == quarterDihedral s r (quarterRepresentatives j) 6

private theorem QuarterWords.isImage_spec {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : Fin 3}
    (h : QuarterWords.isImage a₀ a₁ a₂ a₃ a₄ a₅ a₆ = true) :
    ∃ j, QuarterWord.DihedralEquivalent ![a₀, a₁, a₂, a₃, a₄, a₅, a₆]
      (quarterRepresentatives j) := by
  simp only [QuarterWords.isImage, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    and_assoc] at h
  obtain ⟨j, -, s, -, r, -, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  exact ⟨j, s, r, (QuarterWords.eq_vec _).symm⟩

/-- A Boolean property of seven digits, checked for every choice of the digits. -/
private def QuarterWords.allDigits
    (p : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Bool) : Bool :=
  (List.finRange 3).all fun a₀ => (List.finRange 3).all fun a₁ =>
    (List.finRange 3).all fun a₂ => (List.finRange 3).all fun a₃ =>
    (List.finRange 3).all fun a₄ => (List.finRange 3).all fun a₅ =>
    (List.finRange 3).all fun a₆ => p a₀ a₁ a₂ a₃ a₄ a₅ a₆

private theorem QuarterWords.allDigits_spec
    {p : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Bool}
    (h : QuarterWords.allDigits p = true) :
    ∀ a₀ a₁ a₂ a₃ a₄ a₅ a₆, p a₀ a₁ a₂ a₃ a₄ a₅ a₆ = true := by
  simpa [QuarterWords.allDigits] using h

theorem quarter_word_complete_classification :
    ∀ w : QuarterWord, w.Admissible →
      ∃ j : Fin 7, w.DihedralEquivalent (quarterRepresentatives j) := by
  -- The kernel runs through all `3 ^ 7` digit vectors.
  have key := QuarterWords.allDigits_spec (p := fun a₀ a₁ a₂ a₃ a₄ a₅ a₆ =>
    !QuarterWords.admissibleDigits a₀ a₁ a₂ a₃ a₄ a₅ a₆ ||
      QuarterWords.isImage a₀ a₁ a₂ a₃ a₄ a₅ a₆) (by decide +kernel)
  intro w hw
  rw [QuarterWords.eq_vec w] at hw ⊢
  rw [QuarterWords.admissible_vec] at hw
  exact QuarterWords.isImage_spec
    (by simpa [hw] using key (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6))

/-- The integer increment of the quarter offsets on the edge `i`, with the winding of four
quarter turns added on the last edge, so that the increments add up to `4`
(`integerQuarterIncrement_sum`). -/
def integerQuarterIncrement (m : Vertex → ℤ) (i : Vertex) : ℤ :=
  m (next i) - m i + if i = 6 then 4 else 0

lemma integerQuarterIncrement_sum (m : Vertex → ℤ) :
    ∑ i, integerQuarterIncrement m i = 4 := by
  simp [integerQuarterIncrement, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_next]

/-- Real representatives `theta` of the frames modulo quarter turns, in an interval of length
less than `7/10`, with integer quarter offsets `m`: the canonical axis of each square has the
direction `beta + alpha = theta + m π/2`. -/
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
  have hl := Real.arctan_mono ht.1
  have hu := Real.arctan_mono ht.2
  simpa [BoundaryCycle.alpha, Real.arctan_neg, Real.arctan_one, neg_div] using And.intro hl hu

lemma QuarterLift.edge_identity {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C) (i : Vertex) :
    angleGap C.beta i = F.theta (next i) - F.theta i +
      (integerQuarterIncrement F.quarter i : ℝ) * (Real.pi / 2) + C.alpha i - C.alpha (next i) := by
  have h₁ := F.represents i
  have h₂ := F.represents (next i)
  by_cases hi : i = 6
  · subst hi
    simp only [angleGap, integerQuarterIncrement, ite_true, Int.cast_add,
      Int.cast_sub, Int.cast_ofNat]
    linarith
  · simp only [angleGap, integerQuarterIncrement, hi, ite_false, add_zero, Int.cast_sub]
    linarith

/-- A digit lies in `{0, 1, 2}` when its gap lies in `(19/25, 2π - 114/25)`, the frame
difference is at most `D < 7/10` and both canonical angles are within `π/4`. None of the inputs
depends on the radius; the gap bounds come from the common-point lemma of
`Boundary/Geometry.lean`. -/
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

/-- The lower bounds of the common table for the cost of an edge with the digit `0`, `1` or
`2`, in units of `10⁻⁴`. -/
def doubleWordCostNumerator : Fin 3 → ℕ := ![9775, 7850, 8150]

/-- Count occupied positions in the seven overlapping triples. Their total is at least seven,
so there are at least three occupied positions. The digit sum four and the presence of a `2`
then force three occupied positions, one of them double, which determines the total cost. -/
theorem double_word_cost_numerator :
    ∀ w : QuarterWord, w.Admissible → (∃ i, w i = 2) →
      (∑ i, doubleWordCostNumerator (w i)) = 62950 := by
  intro w hw hd
  let occupied (i : Vertex) : ℕ := if w i = 0 then 0 else 1
  let doubles (i : Vertex) : ℕ := if w i = 2 then 1 else 0
  -- Each cyclic triple contains an occupied position.
  have hthree (i : Vertex) : 1 ≤ occupied i + occupied (next i) + occupied (next (next i)) := by
    have h := hw.2 i
    dsimp [occupied]
    split_ifs <;> omega
  have htotal := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hthree i)
  simp only [Finset.sum_add_distrib, sum_next] at htotal
  have hnext2 : (∑ i, occupied (next (next i))) = ∑ i, occupied i :=
    (sum_next (fun i => occupied (next i))).trans (sum_next occupied)
  rw [hnext2] at htotal
  norm_num at htotal
  -- Each occupied position contributes one, with one extra for every digit `2`.
  have hsplit (i : Vertex) : (w i).val = occupied i + doubles i := by
    dsimp [occupied, doubles]
    generalize w i = d
    fin_cases d <;> norm_num
  have hdigits : (∑ i, occupied i) + (∑ i, doubles i) = 4 := by
    rw [← Finset.sum_add_distrib]
    simpa only [← hsplit] using hw.1
  have hdouble : 1 ≤ ∑ i, doubles i := by
    obtain ⟨i, hi⟩ := hd
    have h := Finset.single_le_sum (f := doubles) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    simpa [doubles, hi] using h
  have hoc : (∑ i, occupied i) = 3 := by omega
  have hdc : (∑ i, doubles i) = 1 := by omega
  -- A zero costs 9775; an occupied position saves 1925, and a `2` adds 300.
  have hcost (i : Vertex) : doubleWordCostNumerator (w i) + 1925 * occupied i =
      9775 + 300 * doubles i := by
    dsimp [occupied, doubles]
    generalize w i = d
    fin_cases d <;> norm_num [doubleWordCostNumerator]
  have hsum : (∑ i, (doubleWordCostNumerator (w i) + 1925 * occupied i)) =
      ∑ i, (9775 + 300 * doubles i) := Finset.sum_congr rfl (fun i _ => hcost i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hoc,hdc] at hsum
  norm_num at hsum
  omega

/-- Summing the cost bounds of the common table round the cycle excludes every word with a
digit `2` at once: the bounds add up to `6.295 > 2π`. The cost inequalities are hypotheses
here. -/
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

/-- An admissible word outside the six other classes is equivalent to the candidate word
`0101011`. The six exclusions are hypotheses here. -/
lemma candidate_word_after_six_exclusions (w : QuarterWord) (hw : w.Admissible)
    (hexcluded : ∀ j : Fin 6, ¬ w.DihedralEquivalent (quarterRepresentatives j.castSucc)) :
    w.DihedralEquivalent candidateQuarterWord := by
  obtain ⟨j, hj⟩ := quarter_word_complete_classification w hw
  by_cases hlast : j = 6
  · simpa [candidateQuarterWord, hlast] using hj
  · have hjlt : j.val < 6 := by omega
    exact (hexcluded ⟨j.val, hjlt⟩ (by simpa using hj)).elim

end SquaresInCircles.Eight
