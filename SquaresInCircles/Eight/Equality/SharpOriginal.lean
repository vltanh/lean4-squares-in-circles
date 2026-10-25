module

public import SquaresInCircles.Eight.Boundary.OriginalWitnesses
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
