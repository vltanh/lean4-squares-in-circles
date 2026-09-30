module
public import SquaresInCircles.Six.Candidate
public import SquaresInCircles.Common.Constructions

@[expose] public section

/-!
# Attainment by the six-square candidate

This proves only that the displayed candidate is a packing. Optimality is a
separate obligation: no lower bound for an arbitrary packing is assumed here.
The diagonal square is handled as a genuinely rotated square, not by replacing
it with an axis-parallel square or a bounding box.
-/

noncomputable section
namespace SquaresInCircles.Six

/-- Converse to the farthest-vertex bound for the actual square predicate. -/
lemma inDisk_of_phi_le {S : UnitSquare} {o : Point} {R : ℝ}
    (hphi : phi (alpha S o) (beta S o) ≤ R ^ 2)
    {p : Point} (hp : closedSquare S p) : inDisk o R p := by
  have hx : |localX S p - localX S o| ≤ alpha S o + 1 / 2 := by
    have hh := abs_add_le (localX S p) (-localX S o)
    rw [abs_neg, ← sub_eq_add_neg] at hh
    dsimp [alpha]
    linarith [hp.1]
  have hy : |localY S p - localY S o| ≤ beta S o + 1 / 2 := by
    have hh := abs_add_le (localY S p) (-localY S o)
    rw [abs_neg, ← sub_eq_add_neg] at hh
    dsimp [beta]
    linarith [hp.2]
  have hxp := mul_nonneg (sub_nonneg.mpr hx)
    (show 0 ≤ alpha S o + 1 / 2 + |localX S p - localX S o| by
      linarith [alpha_nonneg S o, abs_nonneg (localX S p - localX S o)])
  have hyp := mul_nonneg (sub_nonneg.mpr hy)
    (show 0 ≤ beta S o + 1 / 2 + |localY S p - localY S o| by
      linarith [beta_nonneg S o, abs_nonneg (localY S p - localY S o)])
  change normSq (sub p o) ≤ R ^ 2
  rw [← frame_distance S]
  dsimp [phi] at hphi
  nlinarith [sq_abs (localX S p - localX S o), sq_abs (localY S p - localY S o)]

/-- The five parallel squares, in C,N,E,W,S order. -/
def axisCenters : Fin 5 → Point :=
  ![(sStar, sStar), (sStar, sStar + 1), (sStar + 1, sStar),
    (sStar - 1, tStar), (tStar, sStar - 1)]

lemma axisCenters_separated (i j : Fin 5) (hij : i ≠ j) :
    AxisSeparated (axisCenters i) (axisCenters j) := by
  fin_cases i <;> fin_cases j
  all_goals try exact False.elim (hij rfl)
  all_goals dsimp [axisCenters, AxisSeparated]
  all_goals first
    | exact Or.inl (by linarith [sStar_lt_fifth, tStar_bounds.1])
    | exact Or.inr (Or.inl (by linarith [sStar_lt_fifth, tStar_bounds.1]))
    | exact Or.inr (Or.inr (Or.inl (by linarith [sStar_lt_fifth, tStar_bounds.1])))
    | exact Or.inr (Or.inr (Or.inr (by linarith [sStar_lt_fifth, tStar_bounds.1])))

lemma axisCenters_contained (i : Fin 5) :
    (|(axisCenters i).1| + 1 / 2) ^ 2 +
      (|(axisCenters i).2| + 1 / 2) ^ 2 ≤ radius ^ 2 := by
  have hs : 0 < sStar + 1 := by linarith [sStar_pos]
  have hw : sStar - 1 < 0 := by linarith [sStar_lt_fifth]
  have ht : 0 < tStar := by linarith [tStar_bounds.1]
  rw [radius_sq]
  fin_cases i
  · change (|sStar| + 1 / 2) ^ 2 + (|sStar| + 1 / 2) ^ 2 ≤ qStar
    rw [abs_of_pos sStar_pos]
    nlinarith [east_radius_identity, sStar_pos]
  · change (|sStar| + 1 / 2) ^ 2 + (|sStar + 1| + 1 / 2) ^ 2 ≤ qStar
    rw [abs_of_pos sStar_pos, abs_of_pos hs]
    nlinarith [east_radius_identity]
  · change (|sStar + 1| + 1 / 2) ^ 2 + (|sStar| + 1 / 2) ^ 2 ≤ qStar
    rw [abs_of_pos sStar_pos, abs_of_pos hs]
    nlinarith [east_radius_identity]
  · change (|sStar - 1| + 1 / 2) ^ 2 + (|tStar| + 1 / 2) ^ 2 ≤ qStar
    rw [abs_of_neg hw, abs_of_pos ht]
    nlinarith [west_radius_identity]
  · change (|tStar| + 1 / 2) ^ 2 + (|sStar - 1| + 1 / 2) ^ 2 ≤ qStar
    rw [abs_of_neg hw, abs_of_pos ht]
    nlinarith [west_radius_identity]

lemma parallel_packing :
    Packing (fun i : Fin 5 => axisSquare (axisCenters i)) (0, 0) radius :=
  axis_packing radius_pos.le axisCenters_separated axisCenters_contained

lemma diagonal_contained (p : Point) (hp : closedSquare diagonalSquare p) :
    inDisk (0, 0) radius p := by
  have hh := hStar_pos
  have hd := dStar_pos
  have hx : alpha diagonalSquare (0, 0) = 2 * hStar * dStar := by
    change |hStar * (0 - (-dStar)) + hStar * (0 - (-dStar))| = _
    rw [show hStar * (0 - (-dStar)) + hStar * (0 - (-dStar)) =
      2 * hStar * dStar by ring, abs_of_nonneg (by positivity)]
  have hy : beta diagonalSquare (0, 0) = 0 := by
    change |-hStar * (0 - (-dStar)) + hStar * (0 - (-dStar))| = 0
    rw [show -hStar * (0 - (-dStar)) + hStar * (0 - (-dStar)) = 0 by ring,
      abs_zero]
  apply inDisk_of_phi_le (S := diagonalSquare) (o := (0, 0)) (R := radius) _ hp
  rw [phi, hx, hy, radius_sq, diagonal_radius_identity]
  have he : (2 * hStar * dStar + 1 / 2) ^ 2 + (0 + 1 / 2) ^ 2 =
      2 * dStar ^ 2 + 2 * hStar * dStar + 1 / 2 := by
    linear_combination 4 * dStar ^ 2 * hStar_sq
  exact he.le

/-- Strict coordinate upper bounds for points in the rotated square's interior. -/
lemma diagonal_open_upper {p : Point} (hp : openSquare diagonalSquare p) :
    p.1 < tStar - 1 / 2 ∧ p.2 < tStar - 1 / 2 := by
  have hx : p.1 + dStar = hStar *
      (localX diagonalSquare p - localY diagonalSquare p) := by
    dsimp [localX, localY, diagonalSquare]
    linear_combination (-2 * (p.1 + dStar)) * hStar_sq
  have hy : p.2 + dStar = hStar *
      (localX diagonalSquare p + localY diagonalSquare p) := by
    dsimp [localX, localY, diagonalSquare]
    linear_combination (-2 * (p.2 + dStar)) * hStar_sq
  have hmX := mul_lt_mul_of_pos_left
    (show localX diagonalSquare p - localY diagonalSquare p < 1 by
      linarith [(abs_lt.mp hp.1).2, (abs_lt.mp hp.2).1]) hStar_pos
  have hmY := mul_lt_mul_of_pos_left
    (show localX diagonalSquare p + localY diagonalSquare p < 1 by
      linarith [(abs_lt.mp hp.1).2, (abs_lt.mp hp.2).2]) hStar_pos
  rw [← hx, mul_one] at hmX
  rw [← hy, mul_one] at hmY
  have he : hStar - dStar = tStar - 1 / 2 := by dsimp [dStar]; ring
  exact ⟨by linarith, by linarith⟩

lemma central_diagonal_disjoint :
    ∀ p, ¬ (openSquare (axisSquare (sStar, sStar)) p ∧
      openSquare diagonalSquare p) := by
  rintro p ⟨hc, hd⟩
  rw [axisSquare_open] at hc
  have hxy : 2 * (sStar + dStar) - 1 < p.1 + p.2 + 2 * dStar := by
    linarith [(abs_lt.mp hc.1).1, (abs_lt.mp hc.2).1]
  have hm := mul_lt_mul_of_pos_left hxy hStar_pos
  have ht := mul_lt_mul_of_pos_left
    (show (18 : ℝ) / 25 < 2 * (sStar + dStar) - 1 by
      linarith [central_diagonal_clearance]) hStar_pos
  have hv : (1 : ℝ) / 2 < hStar * (18 / 25) := by linarith [hStar_lower]
  have hl : localX diagonalSquare p = hStar * (p.1 + p.2 + 2 * dStar) := by
    dsimp [localX, diagonalSquare]
    ring
  have hu := (abs_lt.mp hd.1).2
  rw [hl] at hu
  linarith

lemma axis_diagonal_disjoint {c : Point} (hc : tStar ≤ c.1 ∨ tStar ≤ c.2) :
    ∀ p, ¬ (openSquare (axisSquare c) p ∧ openSquare diagonalSquare p) := by
  rintro p ⟨ha, hd⟩
  rw [axisSquare_open] at ha
  have hb := diagonal_open_upper hd
  rcases hc with h | h
  · linarith [(abs_lt.mp ha.1).1, hb.1]
  · linarith [(abs_lt.mp ha.2).1, hb.2]

lemma parallel_diagonal_disjoint (i : Fin 5) :
    ∀ p, ¬ (openSquare (axisSquare (axisCenters i)) p ∧
      openSquare diagonalSquare p) := by
  fin_cases i
  · exact central_diagonal_disjoint
  · apply axis_diagonal_disjoint
    right
    change tStar ≤ sStar + 1
    linarith [tStar_bounds.2, sStar_pos]
  · apply axis_diagonal_disjoint
    left
    change tStar ≤ sStar + 1
    linarith [tStar_bounds.2, sStar_pos]
  · exact axis_diagonal_disjoint (Or.inr le_rfl)
  · exact axis_diagonal_disjoint (Or.inl le_rfl)

@[simp] lemma model_castSucc (i : Fin 5) :
    model i.castSucc = axisSquare (axisCenters i) := by fin_cases i <;> rfl

@[simp] lemma model_last : model (Fin.last 5) = diagonalSquare := rfl

/-- Attainment at the candidate radius, using the original unrestricted
`Packing` predicate with pairwise disjoint open interiors. -/
theorem model_packing : Packing model (0, 0) radius := by
  refine ⟨radius_pos.le, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact diagonal_contained
    · simpa only [model_castSucc] using parallel_packing.2.1 j
  · intro i
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · intro j
      refine Fin.lastCases ?_ (fun j' => ?_) j
      · intro hne
        exact False.elim (hne rfl)
      · intro _ p hp
        apply parallel_diagonal_disjoint j' p
        simpa only [model_last, model_castSucc] using And.intro hp.2 hp.1
    · intro j
      refine Fin.lastCases ?_ (fun j' => ?_) j
      · intro _ p hp
        apply parallel_diagonal_disjoint i' p
        simpa only [model_castSucc, model_last] using hp
      · intro hne p hp
        have hij : i' ≠ j' := by
          intro he
          apply hne
          exact congrArg Fin.castSucc he
        apply parallel_packing.disjoint i' j' hij p
        simpa only [model_castSucc] using hp

/-- A concrete witness for the upper-bound half of the six-square theorem. -/
theorem attainment : ∃ S : Fin 6 → UnitSquare, Packing S (0, 0) radius :=
  ⟨model, model_packing⟩

end SquaresInCircles.Six
