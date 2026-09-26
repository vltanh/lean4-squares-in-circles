import SquaresInCircles.Seven.EasySectors
import SquaresInCircles.Seven.ForwardNegativeTarget
import SquaresInCircles.Seven.ForwardBothNegative
import SquaresInCircles.Seven.OppositeForward
import SquaresInCircles.Seven.InwardAxialTarget
import SquaresInCircles.Seven.InwardSideTarget
import SquaresInCircles.Seven.InwardOpposite

/-!
# The gap of `π/3`

The support sums at the gap `π/3` on all four axes, for all signs and labels,
are nonnegative for admissible states and vanish only at contacts. Each active
case is one of the sector theorems. Where a label is `π/4` the support sums are
affine in its state, and the capped region is a triangle whose vertices are
admissible ties; so a support sum at a capped state is at least its value at a
vertex, and a zero would pass to a vertex as a contact with a capped label,
which does not exist.
-/
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Seven

/-- Exhaustive A/T partition, with no omitted axis or sign. -/
theorem fixed_gap_active (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v)
    (ha : ActiveLabel a u) (hb : ActiveLabel A v) :
    PairProperty a u A v s t k := by
  fin_cases k
  · exact .of_pos (fixed_gap_outward h h' s t)
  · cases s <;> cases t
    · exact .of_pos (fixed_gap_forward_positive h h')
    · exact fixed_gap_forward_negative_target .positive h h' (Or.inl rfl) hb
    · exact fixed_gap_forward_opposite_active h h' ha hb
    · rcases ha with hA | hT
      · exact fixed_gap_forward_negative_target .negative h h' (Or.inr hA) hb
      · exact .of_pos (fixed_gap_forward_both_negative_side h h' hT hb)
  · cases s
    · cases t
      · rcases hb with hB | hT
        · rcases ha with hA | hT'
          · exact .of_pos (inward_axial_axial_pos h h' hA hB)
          · exact inward_side_axial_property h h' hT' hB
        · exact .of_pos (fixed_gap_inward_side_target h h' hT)
      · exact fixed_gap_inward_opposite_active h h' ha hb
    · exact .of_pos (fixed_gap_inward_negative h h' t)
  · exact .of_pos (fixed_gap_backward h h' s t)

def capVertex : Fin 3 → Point :=
  ![(Real.pi/5,Real.pi/5),((7-Real.pi/5)/9,Real.pi/5),((7-Real.pi)/5,(7-Real.pi)/5)]

lemma capVertex_admissible (i : Fin 3) :
    Admissible (capVertex i).1 (capVertex i).2 := by
  have hp0 := Real.pi_gt_d2
  have hp1 := pi_lt_22_over_7
  have hr (a u : ℝ) (ha0 : 1/2 ≤ a) (hu0 : 0 ≤ u)
      (hau : u ≤ a) (ha1 : a < 193/250) (hu1 : u < 193/250) :
      Admissible a u := by
    refine ⟨hu0,hau,ha0,?_⟩
    dsimp [phi,targetSq]
    nlinarith
  fin_cases i <;> apply hr <;> norm_num [capVertex] <;> linarith

lemma capVertex_label (i : Fin 3) :
    label (capVertex i).1 (capVertex i).2 = Real.pi/4 := by
  apply min_eq_right (le_min ?_ ?_)
  · fin_cases i <;> norm_num [capVertex,axial] <;> linarith [pi_lt_22_over_7]
  · fin_cases i <;> norm_num [capVertex,side] <;> linarith [pi_lt_22_over_7]

lemma capVertex_active (i : Fin 3) : ActiveLabel (capVertex i).1 (capVertex i).2 := by
  rw [ActiveLabel,capVertex_label]
  fin_cases i
  · exact Or.inl (by simp [capVertex,axial]; ring)
  · exact Or.inl (by simp [capVertex,axial]; ring)
  · exact Or.inr (by simp [capVertex,side]; ring)

/-- Some one of three values, times the total of nonnegative weights, is at most
their weighted sum. -/
lemma exists_le_weighted_sum {w f : Fin 3 → ℝ} (hw : ∀ i,0 ≤ w i) :
    ∃ i,f i*∑ j,w j ≤ ∑ j,w j*f j := by
  obtain ⟨i,-,hi⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  refine ⟨i,?_⟩
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ j)) (hw j)

/-- A capped state is a convex combination of the vertices of the capped
triangle, so an affine function of it is at least its value at a vertex. -/
lemma cap_vertex_le {a u : ℝ} (h : Admissible a u) (hcap : label a u = Real.pi/4)
    (p q r : ℝ) : ∃ i, p+q*(capVertex i).1+r*(capVertex i).2 ≤ p+q*a+r*u := by
  have hA := h.label_le_axial
  have hT := h.label_le_side
  rw [hcap] at hA hT
  dsimp [axial,side] at hA hT
  let w : Fin 3 → ℝ := ![7-Real.pi-9*a+4*u,9*(a-u),5*u-Real.pi]
  have hw (i : Fin 3) : 0 ≤ w i := by
    fin_cases i <;> simp [w] <;> linarith [h.u_le]
  obtain ⟨i,hi⟩ := exists_le_weighted_sum (f := fun i => p+q*(capVertex i).1+r*(capVertex i).2) hw
  have hsum : ∑ j,w j = 7-2*Real.pi := by
    simp only [Fin.sum_univ_three,w]
    norm_num
    ring
  have hval : ∑ j,w j*(p+q*(capVertex j).1+r*(capVertex j).2) = (p+q*a+r*u)*(7-2*Real.pi) := by
    simp only [Fin.sum_univ_three,w,capVertex]
    norm_num
    ring
  rw [hsum,hval] at hi
  exact ⟨i,le_of_mul_le_mul_right hi (by linarith [pi_lt_22_over_7])⟩

lemma pairProperty_cap_first {a u A v : ℝ} {s t : TransverseSign} {k : Fin 4}
    (h : Admissible a u) (h' : Admissible A v) (hcap : label a u = Real.pi/4)
    (hv : ∀ i, PairProperty (capVertex i).1 (capVertex i).2 A v s t k) :
    PairProperty a u A v s t k := by
  let θ := cardinalAngle k
  let c := (|Real.cos θ|+|Real.sin θ|)/2+
    support A (t.coe*v) (θ+Real.pi-gap-s.coe*(Real.pi/4)+t.coe*label A v)
  have he (x y : ℝ) (hxy : label x y = Real.pi/4) :
      pairSupport x y A v s t k gap = c+Real.cos θ*x+s.coe*Real.sin θ*y := by
    simp only [pairSupport,support,hxy,c,θ]
    ring
  obtain ⟨i,hi⟩ := cap_vertex_le h hcap c (Real.cos θ) (s.coe*Real.sin θ)
  rw [← he _ _ (capVertex_label i),← he a u hcap] at hi
  exact ⟨(hv i).1.trans hi,fun hz => absurd (capVertex_label i) (contact_label_not_cap
    (capVertex_admissible i) h' ((hv i).2 (le_antisymm (hi.trans hz.le) (hv i).1))).1⟩

lemma pairProperty_cap_second {a u A v : ℝ} {s t : TransverseSign} {k : Fin 4}
    (h : Admissible a u) (h' : Admissible A v) (hcap : label A v = Real.pi/4)
    (hv : ∀ i, PairProperty a u (capVertex i).1 (capVertex i).2 s t k) :
    PairProperty a u A v s t k := by
  let φ := cardinalAngle k+Real.pi-gap-s.coe*label a u+t.coe*(Real.pi/4)
  let c := support a (s.coe*u) (cardinalAngle k)+(|Real.cos φ|+|Real.sin φ|)/2
  have he (x y : ℝ) (hxy : label x y = Real.pi/4) :
      pairSupport a u x y s t k gap = c+Real.cos φ*x+t.coe*Real.sin φ*y := by
    simp only [pairSupport,support,hxy,c,φ]
    ring
  obtain ⟨i,hi⟩ := cap_vertex_le h' hcap c (Real.cos φ) (t.coe*Real.sin φ)
  rw [← he _ _ (capVertex_label i),← he A v hcap] at hi
  exact ⟨(hv i).1.trans hi,fun hz => absurd (capVertex_label i) (contact_label_not_cap
    h (capVertex_admissible i) ((hv i).2 (le_antisymm (hi.trans hz.le) (hv i).1))).2⟩

/-- It is enough to prove the support property for active labels. -/
theorem fixed_gap_of_active_cases
    (H : ∀ (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4),
      Admissible a u → Admissible A v → ActiveLabel a u → ActiveLabel A v →
      PairProperty a u A v s t k) :
    ∀ (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4),
      Admissible a u → Admissible A v → PairProperty a u A v s t k := by
  have target (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4)
      (ha : Admissible a u) (hb : Admissible A v) (hact : ActiveLabel a u) :
      PairProperty a u A v s t k := by
    rcases hb.selected with hA | hT | hcap
    · exact H a u A v s t k ha hb hact (Or.inl hA)
    · exact H a u A v s t k ha hb hact (Or.inr hT)
    · exact pairProperty_cap_second ha hb hcap fun i =>
        H a u _ _ s t k ha (capVertex_admissible i) hact (capVertex_active i)
  intro a u A v s t k ha hb
  rcases ha.selected with hA | hT | hcap
  · exact target a u A v s t k ha hb (Or.inl hA)
  · exact target a u A v s t k ha hb (Or.inr hT)
  · exact pairProperty_cap_first ha hb hcap fun i =>
      target _ _ A v s t k (capVertex_admissible i) hb (capVertex_active i)

/-- Complete fixed-angle support theorem including capped labels. -/
theorem fixed_gap_property (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) :
    PairProperty a u A v s t k :=
  fixed_gap_of_active_cases fixed_gap_active a u A v s t k h h'

lemma fixed_gap_nonneg {a u A v : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) :
    0≤pairSupport a u A v s t k gap :=
  (fixed_gap_property a u A v s t k h h').1

/-- A zero of a support sum at the gap `π/3` is a contact. -/
theorem fixed_gap_zero {a u A v : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v)
    (hz : pairSupport a u A v s t k gap = 0) : OrderedContact a u A v s t :=
  (fixed_gap_property a u A v s t k h h').2 hz

end SquaresInCircles.Seven
