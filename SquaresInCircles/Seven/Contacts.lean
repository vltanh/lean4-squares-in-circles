import SquaresInCircles.Seven.PairModel

/-!
# Contacts

The three kinds of contact between labelled states: two side states, or a side
state and an axial state. A side state is `(1, 1/2)`, on the circle
`φ = 13/4`; an axial state `(a, 0)` keeps `a` free. So every contact has a
state on the circle, and no contact is strictly admissible.

`PairProperty` is what the gap of `π/3` is shown to satisfy, case by case:
the support sum is nonnegative and vanishes only at a contact.
-/
noncomputable section
namespace SquaresInCircles.Seven

abbrev SideState (a u : ℝ) : Prop := a = 1 ∧ u = 1/2
abbrev AxialState (a u : ℝ) : Prop := u = 0 ∧ 1/2 ≤ a ∧ a ≤ columnLimit

def OrderedContact (a u A v : ℝ) (s t : TransverseSign) : Prop :=
  (s = .negative ∧ t = .positive ∧ SideState a u ∧ SideState A v) ∨
  (s = .positive ∧ SideState a u ∧ AxialState A v) ∨
  (t = .negative ∧ AxialState a u ∧ SideState A v)

lemma remainder_zero {a u : ℝ} (h : Admissible a u)
    (hz : remainder a u = 0) : SideState a u := by
  have he := remainder_identity a u
  have hs := h.slack_nonneg
  exact ⟨by nlinarith [sq_nonneg (u-1/2)],
    by nlinarith [sq_nonneg (a-1)]⟩

lemma axial_of_transverse_zero {a u : ℝ} (h : Admissible a u) (hu : u = 0) :
    AxialState a u := ⟨hu,h.half_le,h.a_le_sqrt_three_sub_half⟩

lemma side_label : label 1 (1/2) = Real.pi/6 := by
  have hp := pi_lt_22_over_7
  have hp0 := Real.pi_pos
  unfold label axial side
  rw [min_eq_right (a := (5*(1/2)/4 : ℝ)) (by linarith), min_eq_left (by linarith)]
  ring

lemma axial_label {a u : ℝ} (h : Admissible a u) (ha : AxialState a u) :
    label a u = 0 := h.label_zero_iff.mpr ha.1

lemma side_neq_cap : label 1 (1/2) ≠ Real.pi/4 := by
  rw [side_label]
  linarith [Real.pi_pos]

lemma contact_label_not_cap {a u A v : ℝ} {s t : TransverseSign}
    (h : Admissible a u) (h' : Admissible A v)
    (hc : OrderedContact a u A v s t) :
    label a u ≠ Real.pi/4 ∧ label A v ≠ Real.pi/4 := by
  rcases hc with ⟨_,_,hs,ht⟩ | ⟨_,hs,ht⟩ | ⟨_,hs,ht⟩
  · simpa [hs.1,hs.2,ht.1,ht.2] using And.intro side_neq_cap side_neq_cap
  · rw [hs.1,hs.2,axial_label h' ht]
    exact ⟨side_neq_cap,by linarith [Real.pi_pos]⟩
  · rw [ht.1,ht.2,axial_label h hs]
    exact ⟨by linarith [Real.pi_pos],side_neq_cap⟩

lemma reflected_reverse_contact {a u A v : ℝ} {s t : TransverseSign}
    (hc : OrderedContact A v a u t.flip s.flip) : OrderedContact a u A v s t := by
  cases s <;> cases t <;>
    simp only [OrderedContact,TransverseSign.flip] at hc ⊢ <;> aesop

/-- Every contact has a side state `(1, 1/2)`, where `φ = 13/4`. -/
lemma contact_not_strict {a u A v : ℝ} {s t : TransverseSign}
    (hc : OrderedContact a u A v s t)
    (h : StrictlyAdmissible a u) (h' : StrictlyAdmissible A v) : False := by
  have side {a u : ℝ} (hs : SideState a u) (h : StrictlyAdmissible a u) : False := by
    have hp := h.phi_lt
    rw [hs.1,hs.2] at hp
    norm_num [phi,targetSq] at hp
  rcases hc with ⟨-,-,hs,-⟩ | ⟨-,hs,-⟩ | ⟨-,-,hs⟩
  · exact side hs h
  · exact side hs h
  · exact side hs h'

/-- An active label is axial or side. -/
def ActiveLabel (a u : ℝ) : Prop := label a u = axial u ∨ label a u = side a u

/-- The support assertion at the gap `π/3`: nonnegative, and zero only at a
contact. -/
def PairProperty (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4) : Prop :=
  0 ≤ pairSupport a u A v s t k gap ∧
    (pairSupport a u A v s t k gap = 0 → OrderedContact a u A v s t)

lemma PairProperty.of_pos {a u A v : ℝ} {s t : TransverseSign} {k : Fin 4}
    (hp : 0 < pairSupport a u A v s t k gap) : PairProperty a u A v s t k :=
  ⟨hp.le,fun hz => absurd hz hp.ne'⟩

/-- A lower bound by a side remainder and a turn that vanish together only at the
side state with the second state axial: the contact of a side square with the
top or bottom square. -/
lemma PairProperty.of_side_axial {a u A v : ℝ} {t : TransverseSign} {k : Fin 4} {e : ℝ}
    (h : Admissible a u) (h' : Admissible A v) (hA : label A v = axial v)
    (he : e = label a u-t.coe*label A v-Real.pi/6) {c : ℝ} (hc : 0 < c)
    (hlow : (2/15)*remainder a u+c*|e| ≤ pairSupport a u A v .positive t k gap) :
    PairProperty a u A v .positive t k := by
  have hW := h.remainder_nonneg
  have he0 := abs_nonneg e
  refine ⟨by nlinarith,fun hz => ?_⟩
  have hr : remainder a u = 0 := by nlinarith
  have hs := remainder_zero h hr
  have hee : e = 0 := abs_eq_zero.mp (by nlinarith)
  rw [he,hs.1,hs.2,side_label,hA] at hee
  have hv : v = 0 := by cases t <;> dsimp [TransverseSign.coe,axial] at hee <;> linarith [h'.u_nonneg]
  exact Or.inr (Or.inl ⟨rfl,hs,axial_of_transverse_zero h' hv⟩)

end SquaresInCircles.Seven
