module

public import SquaresInCircles.Eight.Stationary.CenterCompletion
public import SquaresInCircles.Eight.Boundary.Normalization

/-!
# Eight squares: the boundary cycle at the stationary radius

A packing in the disk of squared radius `q ≤ qStar` also packs the disk of squared radius
`qStar`, and the boundary normalization at that level gives a boundary cycle whose recovered
exterior squares have squared radius `qStar`, with the separating axes chosen on the packing
(`stationary_normalization_exists`). The normalization relabels, turns and
possibly reflects the packing, so its squares still pack the disk of squared radius `q`
(`normalized_at_original_radius`). `originalPositions` lists the centres of the exterior squares
in the cyclic order of the family; they stay in that disk
(`source_contained_at_original_radius`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GeometricModel
open Stationary Coordinates

theorem sharp_source_level : sourceLevel qStar=qStar := by
  apply max_eq_left
  simpa [qMinus] using qStar_limits.1.le

theorem sharp_le_Q1 : qStar ≤ Q1 := by
  simpa [Q1] using qStar_limits.2.1.le

/-- A configuration congruent to a packing in the disk of squared radius `q` about `o` packs
the disk of squared radius `q` about the origin. -/
theorem sqPacking_forward_of_congruent {n : ℕ}
    {S M : Fin n → UnitSquare} {o : Point} {q : ℝ}
    (h : Congruent S o M) (hp : SqPacking S o q) :
    SqPacking M (0,0) q := by
  obtain ⟨φ,σ,hφ⟩ := h
  refine ⟨hp.1,?_,?_⟩
  · intro i p hi
    have hclosed : closedSquare (S (σ i)) (frameEquiv o φ p) := by
      simpa only [frameEquiv_apply] using (hφ i p).2.mpr hi
    have hb := hp.2.1 (σ i) (frameEquiv o φ p) hclosed
    have hn := frameEquiv_distance o φ p (0,0)
    rw [frameEquiv_zero] at hn
    rw [hn] at hb
    exact hb
  · intro i j hij p hpij
    apply hp.2.2 (σ i) (σ j) (σ.injective.ne hij) (frameEquiv o φ p)
    constructor
    · simpa only [frameEquiv_apply] using (hφ i p).1.mpr hpij.1
    · simpa only [frameEquiv_apply] using (hφ j p).1.mpr hpij.2

theorem sqPacking_reflection {n : ℕ} {S : Fin n → UnitSquare} {q : ℝ}
    (hp : SqPacking S (0,0) q) :
    SqPacking (fun i => reflectDiagonalSquare (S i)) (0,0) q :=
  (sqPacking_iff_packing _ _ hp.1).2
    (packing_reflectDiagonal ((sqPacking_iff_packing _ _ hp.1).1 hp))

/-- The normalization at `qStar` relabels, turns and possibly reflects the packing, so its
squares still pack the disk of squared radius `q`. -/
theorem normalized_at_original_radius {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S qStar) (hp : SqPacking S (0,0) q) :
    SqPacking N.squares (0,0) q := by
  have h := sqPacking_forward_of_congruent N.congruent hp
  cases hb : N.reflected
  · simpa [hb] using h
  · have h' := sqPacking_reflection h
    simpa [hb,reflectionSquare_twice] using h'

/-- The boundary normalization at `qStar` of a packing in the disk of squared radius
`q ≤ qStar`: its squares pack that disk, and the signed axes chosen on the packing are those of
the recovered cycle. -/
theorem stationary_normalization_exists
    {S : Fin 8 → UnitSquare} {q : ℝ}
    (hp : SqPacking S (0,0) q) (hq : q ≤ qStar) :
    ∃ N : GlobalNormalization S qStar,
      SqPacking N.squares (0,0) q ∧
      N.source.selected=N.recovered.selected := by
  have hpStar : SqPacking S (0,0) qStar :=
    ⟨hp.1.trans hq,fun i p h => (hp.2.1 i p h).trans hq,hp.2.2⟩
  obtain ⟨B⟩ := boundary_normalization_exists hpStar sharp_le_Q1
  let D := B.data hpStar
  obtain ⟨K⟩ := boundary_candidate_normalization D.expanded
  let M := D.act K.action
  obtain ⟨b,hb⟩ := M.congruent
  let N : GlobalNormalization S qStar := {
    squares := M.squares
    packing := M.packing
    central_core := M.central_core
    reflected := b
    congruent := hb
    source := M.source
    source_square := M.source_square
    source_order := M.source_order
    recovered := M.recovered
    expanded := M.expanded
    expansion := M.expansion
    frame := K.frame
    eHalf := K.eHalf
    source_frames := M.source_frames
    source_selected := M.source_selected }
  have hbase : D.source.selected=D.recovered.selected :=
    D.source_selected.trans B.selected_eq
  have hselected : N.source.selected=N.recovered.selected := by
    funext i
    change K.action.axis (D.source.selected (K.action.edge i)) =
      K.action.axis (D.recovered.selected (K.action.edge i))
    rw [hbase]
  exact ⟨N,normalized_at_original_radius N hp,hselected⟩

def originalPositions {S : Fin 8 → UnitSquare}
    (N : GlobalNormalization S qStar) : OriginalDual.Positions :=
  OriginalDual.ofCycle (fun i => (N.source.square i).center)

theorem source_contained_at_original_radius {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S qStar) (hp : SqPacking N.squares (0,0) q) :
    ∀ i p, closedSquare (N.source.square i) p → normSq p ≤ q := by
  intro i p h
  have h' : closedSquare (N.squares i.succ) p := by
    simpa only [N.source_square] using h
  simpa [sub] using hp.2.1 i.succ p h'

theorem source_recovered_frames {S : Fin 8 → UnitSquare}
    (N : GlobalNormalization S qStar) (i : Vertex) :
    SameFrame (N.source.square i) (N.recovered.square i) :=
  ⟨(N.source_frames i).1.trans (N.expansion.same_frames i).1,
    (N.source_frames i).2.trans (N.expansion.same_frames i).2⟩

end SquaresInCircles.Eight.GeometricModel
