module

public import SquaresInCircles.Eight.Boundary.Normalization
public import SquaresInCircles.Eight.Boundary.SourceEquality
public import SquaresInCircles.Eight.Stationary.FixedEval
public import SquaresInCircles.Eight.Stationary.System

/-!
# Eight squares: the dual at the original centres

The completed identity of the stationary chain (`OriginalDual.exact_identity`) is evaluated at the
centres of the packing itself, not at those of the moved boundary cycle, and bounded with the
squared radius `q` of the packing: if the five anchored corners lie in the disk and the seven gaps
are nonnegative, then `qStar` plus a positive combination of the squared distances of the five
anchors from their stationary positions is at most `q` (`original_dual_quantitative`). Hence
`qStar ≤ q`, and at `q = qStar` the anchors are at their stationary positions, every gap vanishes
and `T` and `G` lie on their slider lines (`original_radius_and_centers`). With the stationary
frames and normals of the chosen separating axes, these hypotheses hold
(`sharp_rigidity_of_original_witnesses`).
-/

section
/-!
## The boundary cycle at the stationary radius

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
end
end
end

section
@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.GeometricModel
open Stationary Coordinates OriginalDual

/-- The completed identity at the centres `p`, bounded with the squared radius `q` of the
disk that holds the anchored corners. -/
theorem original_dual_quantitative {d : Coordinates}
    (hd : d.IsChain) (hw : d.WeightDomain)
    (hz : d.defect=0) (hs : d.positionDerivative=0)
    {q : ℝ} {p : Positions}
    (hv : ∀ i : Fin 5,
      normSq (add (p i.castSucc.castSucc) (d.anchorOffsets i)) ≤ q)
    (hg : ∀ e : Fin 7, 0 ≤ OriginalDual.gap d p e) :
    d.q + ∑ i : Fin 5,
      d.mu i * normSq (sub (p i.castSucc.castSucc) (d.anchorCenters i)) ≤ q := by
  rw [← OriginalDual.exact_identity hd hw hz hs p]
  exact OriginalDual.value_le hw hv hg

theorem original_dual_radius_lower {d : Coordinates}
    (hd : d.IsChain) (hw : d.WeightDomain)
    (hz : d.defect=0) (hs : d.positionDerivative=0)
    {q : ℝ} {p : Positions}
    (hv : ∀ i : Fin 5,
      normSq (add (p i.castSucc.castSucc) (d.anchorOffsets i)) ≤ q)
    (hg : ∀ e : Fin 7, 0 ≤ OriginalDual.gap d p e) : d.q ≤ q := by
  have h := original_dual_quantitative hd hw hz hs hv hg
  have he : 0 ≤ ∑ i : Fin 5,
      d.mu i * normSq (sub (p i.castSucc.castSucc) (d.anchorCenters i)) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (hw.mu_pos i).le (normSq_nonneg _)
  linarith

/-- At `q ≤ d.q`: the squared radius is `d.q`, the anchors are at their positions in `d`,
every gap vanishes and `T`, `G` lie on their slider lines. -/
theorem original_radius_and_centers {d : Coordinates}
    (hd : d.IsChain) (hw : d.WeightDomain)
    (hz : d.defect=0) (hs : d.positionDerivative=0)
    {q : ℝ} {p : Positions} (hq : q ≤ d.q)
    (hv : ∀ i : Fin 5,
      normSq (add (p i.castSucc.castSucc) (d.anchorOffsets i)) ≤ q)
    (hg : ∀ e : Fin 7, 0 ≤ OriginalDual.gap d p e) :
    q=d.q ∧
      (∀ i : Fin 5, p i.castSucc.castSucc=d.anchorCenters i) ∧
      (∀ e : Fin 7, OriginalDual.gap d p e=0) ∧
      ∃ Z η : ℝ, p 5=d.pT Z ∧ p 6=d.pG η := by
  have hlow := original_dual_radius_lower hd hw hz hs hv hg
  have hqeq : q=d.q := le_antisymm hq hlow
  have hrigid := OriginalDual.original_centers_rigid hd hw hz hs
    (fun i => (hv i).trans hq) hg
  refine ⟨hqeq,hrigid.1,hrigid.2,?_⟩
  exact OriginalDual.slider_coordinates
    (hrigid.1 1) (hrigid.1 4) (hrigid.2 1) (hrigid.2 5)

theorem sharp_original_radius_and_centers {q : ℝ} {p : Positions}
    (hq : q ≤ qStar)
    (hv : ∀ i : Fin 5,
      normSq (add (p i.castSucc.castSucc) (sharpData.anchorOffsets i)) ≤ q)
    (hg : ∀ e : Fin 7, 0 ≤ OriginalDual.gap sharpData p e) :
    q=qStar ∧
      (∀ i : Fin 5, p i.castSucc.castSucc=sharpData.anchorCenters i) ∧
      (∀ e : Fin 7, OriginalDual.gap sharpData p e=0) ∧
      ∃ Z η : ℝ, p 5=sharpData.pT Z ∧ p 6=sharpData.pG η :=
  original_radius_and_centers sharpData_stationary.toIsChain
    sharpData_stationary.weightDomain sharpData_stationary.zero_defect
    sharpData_stationary.position_stationary hq hv hg

/-- The same conclusion at `qStar`, from the containment of the squares, their stationary
frames and the stationary normals of the chosen separating axes. -/
theorem sharp_rigidity_of_original_witnesses {q : ℝ}
    {K : Vertex → UnitSquare} (hq : q ≤ qStar)
    (hc : ∀ i p, closedSquare (K i) p → normSq p ≤ q)
    (hf : Eight.StationaryFrames sharpData K)
    (selected : Vertex → SignedAxis)
    (hfeasible : ∀ i, (selected i).Feasible (K i) (K (next i)))
    (hnormal : ∀ i, (selected i).normal (K i) (K (next i)) =
      Eight.stationaryNormal sharpData i) :
    let p := OriginalDual.ofCycle (fun i => (K i).center)
    q=qStar ∧
      (∀ i : Fin 5, p i.castSucc.castSucc=sharpData.anchorCenters i) ∧
      (∀ e : Fin 7, OriginalDual.gap sharpData p e=0) ∧
      ∃ Z η : ℝ, p 5=sharpData.pT Z ∧ p 6=sharpData.pG η := by
  apply sharp_original_radius_and_centers hq
  · exact Eight.vertices_at_original_radius hf hc
  · exact Eight.gaps_of_retained_normals sharpData_stationary.weightDomain
      hf selected hfeasible hnormal

/-! ## The dual at arbitrary centres -/

end SquaresInCircles.Eight.GeometricModel
end
end
end
