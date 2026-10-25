module

public import SquaresInCircles.Eight.TableFree.OriginalWitnesses
public import SquaresInCircles.Eight.ExactFamily.Stationary

/-!
# The sharp dual at the original containing radius

Uncompiled source draft of HAND_SHARP_RADIUS_BOUNDARY_ASSEMBLY.md,
Sections 4--5.

The boundary construction is absent from the algebra in this file.
Containment is used at the original squared radius, and all seven gaps are
gaps of the original centers. In particular, a circle equality attached to a
moved outer state is never asserted of an unchanged original center.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.GeometricModel
open ExactFamily Coordinates OriginalDual

/-- The completed identity is evaluated at the original centers and its
upper bound uses the original squared containing radius q. -/
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

/-- Radius equality, original anchor equality, all original contact
equalities, and the two original slider lines follow in one application. -/
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

theorem sharp_original_dual_quantitative {q : ℝ} {p : Positions}
    (hv : ∀ i : Fin 5,
      normSq (add (p i.castSucc.castSucc) (sharpData.anchorOffsets i)) ≤ q)
    (hg : ∀ e : Fin 7, 0 ≤ OriginalDual.gap sharpData p e) :
    qStar + ∑ i : Fin 5,
      sharpData.mu i *
        normSq (sub (p i.castSucc.castSucc) (sharpData.anchorCenters i)) ≤ q :=
  original_dual_quantitative sharpData_stationary.toIsChain
    sharpData_stationary.weightDomain sharpData_stationary.zero_defect
    sharpData_stationary.position_stationary hv hg

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

/-- The concrete geometric hypotheses are only actual original containment,
the physical frames, and the retained signed normal equalities. -/
theorem sharp_rigidity_of_original_witnesses {q : ℝ}
    {K : Vertex → UnitSquare} (hq : q ≤ qStar)
    (hc : ∀ i p, closedSquare (K i) p → normSq p ≤ q)
    (hf : TableFree.StationaryFrames sharpData K)
    (selected : Vertex → SignedAxis)
    (hfeasible : ∀ i, (selected i).Feasible (K i) (K (next i)))
    (hnormal : ∀ i, (selected i).normal (K i) (K (next i)) =
      TableFree.stationaryNormal sharpData i) :
    let p := OriginalDual.ofCycle (fun i => (K i).center)
    q=qStar ∧
      (∀ i : Fin 5, p i.castSucc.castSucc=sharpData.anchorCenters i) ∧
      (∀ e : Fin 7, OriginalDual.gap sharpData p e=0) ∧
      ∃ Z η : ℝ, p 5=sharpData.pT Z ∧ p 6=sharpData.pG η := by
  apply sharp_original_radius_and_centers hq
  · exact TableFree.vertices_at_original_radius hf hc
  · exact TableFree.gaps_of_retained_normals sharpData_stationary.weightDomain
      hf selected hfeasible hnormal

/-! ## Arbitrary containing-circle center -/

def positionsAbout (o : Point) (p : Positions) : Positions :=
  fun i => sub (p i) o

theorem gap_positionsAbout (d : Coordinates) (o : Point) (p : Positions)
    (e : Fin 7) :
    OriginalDual.gap d (positionsAbout o p) e=OriginalDual.gap d p e := by
  fin_cases e <;>
    simp [OriginalDual.gap,positionsAbout,Coordinates.e,Coordinates.f,
      dot,sub] <;> ring

theorem offset_positionsAbout (o : Point) (p : Positions) (i : Fin 7)
    (v : Point) :
    add (positionsAbout o p i) v=sub (add (p i) v) o := by
  ext <;> simp [positionsAbout,add,sub] <;> ring

theorem point_eq_of_centered_eq {o p P : Point} (h : sub p o=P) :
    p=add o P := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  ext <;> dsimp [sub,add] at * <;> linarith

/-- The same conclusion for a circle about an arbitrary point o. No
assumption about the location of o relative to these seven centers is used. -/
theorem sharp_original_radius_and_centers_about {q : ℝ} {o : Point}
    {p : Positions} (hq : q ≤ qStar)
    (hv : ∀ i : Fin 5,
      normSq (sub (add (p i.castSucc.castSucc) (sharpData.anchorOffsets i)) o) ≤ q)
    (hg : ∀ e : Fin 7, 0 ≤ OriginalDual.gap sharpData p e) :
    q=qStar ∧
      (∀ i : Fin 5, p i.castSucc.castSucc=add o (sharpData.anchorCenters i)) ∧
      (∀ e : Fin 7, OriginalDual.gap sharpData p e=0) ∧
      ∃ Z η : ℝ, p 5=add o (sharpData.pT Z) ∧ p 6=add o (sharpData.pG η) := by
  have hv' (i : Fin 5) :
      normSq (add (positionsAbout o p i.castSucc.castSucc)
        (sharpData.anchorOffsets i)) ≤ q := by
    rw [offset_positionsAbout]
    exact hv i
  have hg' (e : Fin 7) :
      0 ≤ OriginalDual.gap sharpData (positionsAbout o p) e := by
    rw [gap_positionsAbout]
    exact hg e
  obtain ⟨heq,ha,hg0,Z,η,hT,hG⟩ :=
    sharp_original_radius_and_centers hq hv' hg'
  refine ⟨heq,?_,?_,Z,η,?_,?_⟩
  · intro i
    exact point_eq_of_centered_eq (ha i)
  · intro e
    simpa only [gap_positionsAbout] using hg0 e
  · exact point_eq_of_centered_eq hT
  · exact point_eq_of_centered_eq hG

end SquaresInCircles.Eight.GeometricModel
