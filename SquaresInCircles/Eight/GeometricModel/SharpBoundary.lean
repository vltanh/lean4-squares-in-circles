module

public import SquaresInCircles.Eight.GlobalNormalization
public import SquaresInCircles.Eight.GeometricModel.SharpOriginal

/-!
# A fresh boundary construction at the exact sharp ceiling

Uncompiled source draft of HAND_SHARP_RADIUS_BOUNDARY_ASSEMBLY.md,
Sections 2--4.

For an original packing at q <= qStar, boundary normalization is invoked on
that same packing with ceiling qStar. Consequently its recovered outer
states have squared radius qStar by construction. The original records are
retained separately and remain contained at q.

This file reuses the existing global frame/quarter-word normalization. Its
dependencies are not claimed to be a new formalization of the complete
table-free primary-owner entry. That distinct construction is addressed by
the compatibility and replacement interfaces in SharpAssembly.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GeometricModel
open ExactFamily Coordinates

theorem sharp_source_level : sourceLevel qStar=qStar := by
  apply max_eq_left
  simpa [qMinus] using qStar_limits.1.le

theorem sharp_le_Q1 : qStar ≤ Q1 := by
  simpa [Q1] using qStar_limits.2.1.le

/-- The forward direction is useful here: a known original packing induces
containment of its congruent normalized records at the same original q. -/
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

/-- Normalization at qStar does not replace the original containing radius.
Its labels, quarter-turn records, rotation and possible reflection are actual
congruences, so the normalized original squares are still contained at q. -/
theorem normalized_at_original_radius {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S qStar) (hp : SqPacking S (0,0) q) :
    SqPacking N.squares (0,0) q := by
  have h := sqPacking_forward_of_congruent N.congruent hp
  cases hb : N.reflected
  · simpa [hb] using h
  · have h' := sqPacking_reflection h
    simpa [hb,reflectionSquare_twice] using h'

/-- The stronger fresh construction keeps the selection equality discarded
by the older GlobalNormalization record. The same initially chosen signed
axes are feasible on the recovered qStar boundary before expansion. -/
theorem fresh_normalization_with_retained_source_exists
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

/-- A concrete fresh construction, not a relabeling of old outer states
from an unrelated lower working radius. -/
theorem fresh_normalization_exists {S : Fin 8 → UnitSquare} {q : ℝ}
    (hp : SqPacking S (0,0) q) (hq : q ≤ qStar) :
    ∃ N : GlobalNormalization S qStar, SqPacking N.squares (0,0) q := by
  obtain ⟨N,hN,hselected⟩ := fresh_normalization_with_retained_source_exists hp hq
  exact ⟨N,hN⟩

noncomputable def freshNormalization {S : Fin 8 → UnitSquare} {q : ℝ}
    (hp : SqPacking S (0,0) q) (hq : q ≤ qStar) :
    GlobalNormalization S qStar :=
  Classical.choose (fresh_normalization_exists hp hq)

theorem freshNormalization_original_packing {S : Fin 8 → UnitSquare} {q : ℝ}
    (hp : SqPacking S (0,0) q) (hq : q ≤ qStar) :
    SqPacking (freshNormalization hp hq).squares (0,0) q :=
  Classical.choose_spec (fresh_normalization_exists hp hq)

/-- The actual recovered boundary record has the exact sharp ceiling. -/
def sharpBoundary {S : Fin 8 → UnitSquare}
    (N : GlobalNormalization S qStar) : BoundaryCycle qStar := by
  simpa only [sharp_source_level] using N.recovered

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

/-- Exact source witnesses retained by the fixed-witness deformation and
the later radial expansion. Center equality is neither a premise nor a
conclusion of this transport. -/
theorem source_retained_normal {S : Fin 8 → UnitSquare}
    (N : GlobalNormalization S qStar) (i : Vertex) :
    (N.source.selected i).normal (N.source.square i)
        (N.source.square (next i)) =
      (N.expanded.selected i).normal (N.expanded.square i)
        (N.expanded.square (next i)) := by
  rw [N.source_selected]
  exact signed_normal_same_frames
    (N.source_frames i) (N.source_frames (next i)) (N.expanded.selected i)

theorem source_retained_feasible {S : Fin 8 → UnitSquare}
    (N : GlobalNormalization S qStar) (i : Vertex) :
    (N.source.selected i).Feasible (N.source.square i)
      (N.source.square (next i)) :=
  N.source.feasible i

theorem source_recovered_frames {S : Fin 8 → UnitSquare}
    (N : GlobalNormalization S qStar) (i : Vertex) :
    SameFrame (N.source.square i) (N.recovered.square i) :=
  ⟨(N.source_frames i).1.trans (N.expansion.same_frames i).1,
    (N.source_frames i).2.trans (N.expansion.same_frames i).2⟩

/-- This is the actual original-to-sharp-boundary normal equality required
by the table-free source proof, before the temporary larger-radius cycle. -/
theorem source_retained_recovered_normal {S : Fin 8 → UnitSquare}
    (N : GlobalNormalization S qStar)
    (hselected : N.source.selected=N.recovered.selected) (i : Vertex) :
    (N.source.selected i).normal (N.source.square i)
        (N.source.square (next i)) =
      (N.recovered.selected i).normal (N.recovered.square i)
        (N.recovered.square (next i)) := by
  rw [hselected]
  exact signed_normal_same_frames
    (source_recovered_frames N i) (source_recovered_frames N (next i))
    (N.recovered.selected i)

theorem source_selected_feasible_on_recovered {S : Fin 8 → UnitSquare}
    (N : GlobalNormalization S qStar)
    (hselected : N.source.selected=N.recovered.selected) (i : Vertex) :
    (N.source.selected i).Feasible (N.recovered.square i)
      (N.recovered.square (next i)) := by
  rw [hselected]
  exact N.recovered.feasible i

/-- The original-circle upper bound used by the final assembly. -/
theorem source_original_dual_le {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S qStar) (hp : SqPacking N.squares (0,0) q)
    (hf : TableFree.StationaryFrames sharpData N.source.square)
    (hn : ∀ i, (N.source.selected i).normal (N.source.square i)
      (N.source.square (next i))=TableFree.stationaryNormal sharpData i) :
    OriginalDual.value sharpData (originalPositions N) ≤ q := by
  apply OriginalDual.value_le sharpData_stationary.weightDomain
  · exact TableFree.vertices_at_original_radius hf
      (source_contained_at_original_radius N hp)
  · exact TableFree.gaps_of_retained_normals sharpData_stationary.weightDomain
      hf N.source.selected N.source.feasible hn

end SquaresInCircles.Eight.GeometricModel
