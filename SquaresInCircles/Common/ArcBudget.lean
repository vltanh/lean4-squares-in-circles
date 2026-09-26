import SquaresInCircles.Common.Coordinates

/-!
# The angular budget of a packing

Disjoint squares hold disjoint arcs of a circle about the disk centre, and at
most one of them contains the disk centre; five squares replace that square by
its radial sweep, which stays disjoint from the others. Three to five squares
derive their lower bounds from uniqueness: a packing in a smaller disk would
have the normal form of the optimal layout, which reaches the larger circle.
-/
noncomputable section
open Set
namespace SquaresInCircles

/-- Of two or more disjoint squares, some square does not contain `o`. -/
lemma exists_exterior {n : ℕ} (hn : 2 ≤ n) {S : Fin n → UnitSquare} (hd : InteriorDisjoint S)
    (o : Point) : ∃ i, ¬ openSquare (S i) o := by
  by_contra h
  push Not at h
  exact hd ⟨0,by omega⟩ ⟨1,by omega⟩ (by simp [Fin.ext_iff]) o ⟨h _,h _⟩

/-- The radial sweep of a square containing `o`, and any other square itself. -/
def rayRegions {n : ℕ} (S : Fin n → UnitSquare) (o : Point) (i : Fin n) : Set Point :=
  by
    classical
    exact if openSquare (S i) o then openRay (S i) o else {p | openSquare (S i) p}

lemma rayRegions_disjoint {n : ℕ} {S : Fin n → UnitSquare} {o : Point}
    (hd : InteriorDisjoint S) (hp : ∀ i, P8 (alpha (S i) o) (beta (S i) o)) :
    Pairwise (fun i j => Disjoint (rayRegions S o i) (rayRegions S o j)) := by
  classical
  intro i j hij
  by_cases hi : openSquare (S i) o <;> by_cases hj : openSquare (S j) o <;>
    simp only [rayRegions,hi,hj,ite_true,ite_false]
  · exact False.elim (hd i j hij o ⟨hi,hj⟩)
  · exact safe_openRay_of_disjoint (S i) (S j) o (hd i j hij) (hp i) (hp j)
  · exact (safe_openRay_of_disjoint (S j) (S i) o (hd j i hij.symm) (hp j) (hp i)).symm
  · exact hd.pairwise hij

/-- `n ≥ 2` disjoint squares with octagon centres cannot all hold arcs of
half-width at least `π/n` in their regions, strictly more for the squares that
do not contain `o`. -/
theorem ray_budget_impossible {n : ℕ} (hn : 2 ≤ n) {S : Fin n → UnitSquare} {o : Point}
    {r : ℝ} (hd : InteriorDisjoint S) (h8 : ∀ i, P8 (alpha (S i) o) (beta (S i) o))
    (hin : ∀ i, openSquare (S i) o →
      ∃ A : OpenArc o r (openRay (S i) o), Real.pi/n ≤ A.halfWidth)
    (hex : ∀ i, ¬ openSquare (S i) o →
      ∃ A : OpenArc o r {p | openSquare (S i) p}, Real.pi/n < A.halfWidth) : False := by
  classical
  have harcs : ∀ i, ∃ A : OpenArc o r (rayRegions S o i), Real.pi/n ≤ A.halfWidth ∧
      (¬ openSquare (S i) o → Real.pi/n < A.halfWidth) := by
    intro i
    by_cases hi : openSquare (S i) o
    · rw [show rayRegions S o i = openRay (S i) o from ite_eq_left hi]
      obtain ⟨A,hA⟩ := hin i hi
      exact ⟨A,hA,fun h => (h hi).elim⟩
    · rw [show rayRegions S o i = {p | openSquare (S i) p} from ite_eq_right hi]
      obtain ⟨A,hA⟩ := hex i hi
      exact ⟨A,hA.le,fun _ => hA⟩
  choose A hA hstrict using harcs
  obtain ⟨i,hi⟩ := exists_exterior hn hd o
  exact uniform_arc_excess A (rayRegions_disjoint hd h8) hA ⟨i,hstrict i hi⟩

/-- The lower bound from uniqueness: if every packing in the disk of radius `R`
has the normal form of `c`, and a square of `c` reaches the circle of radius
`R`, then no packing fits in a smaller disk. -/
theorem optimality_of_uniqueness {n : ℕ} {c : Fin n → Point} {R : ℝ}
    (huniq : ∀ (S : Fin n → UnitSquare) (o : Point), Packing S o R → HasNormalForm S o c)
    (hc : ∃ i x y, closedAxisSquare (c i) x y ∧ R^2 ≤ x^2+y^2)
    {S : Fin n → UnitSquare} {o : Point} {R' : ℝ} (hp : Packing S o R') : R ≤ R' := by
  by_contra hlt
  push Not at hlt
  have hR' := hp.1
  have hsq : R'^2 < R^2 := by nlinarith
  obtain ⟨i,x,y,hxy,hR⟩ := hc
  obtain ⟨φ,σ,hφ⟩ := huniq S o
    ⟨hR'.trans hlt.le,fun j p hj => (hp.2.1 j p hj).trans hsq.le,hp.2.2⟩
  have hin := hp.2.1 (σ i) _ ((hφ i x y).2.mpr hxy)
  rw [inDisk,pointInDirection_norm] at hin
  linarith

end SquaresInCircles
