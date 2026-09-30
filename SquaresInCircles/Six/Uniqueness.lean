module
public import SquaresInCircles.Six.LowerBound
public import SquaresInCircles.Six.Equality.AnalyticReconstruction
public import SquaresInCircles.Common.Optimum

@[expose] public section

/-!
# The unrestricted six-square equality theorem

The analytic fixed-pair closure retains the actual separating sources. Eight
candidate-frame contact inequalities and exact disk supports then determine
all centers. Point-set reconstruction and the candidate's diagonal symmetry
absorb the single recorded reflection without changing Congruent.

The legacy pair-envelope checker and BalancedClosure are no longer imported.
The remaining internal fixed-row classification is explicit in
Classification.Reduction. No external-script success is a theorem premise.
Compilation and kernel acceptance remain deferred.
-/

noncomputable section
namespace SquaresInCircles.Six

/-- Every six-square packing at the candidate radius is the candidate, up to
the original rotation, translation and relabeling congruence. -/
theorem uniqueness {S : Fin 6 → UnitSquare} {o : Point}
    (hp : Packing S o Six.radius) : Congruent S o Six.model := by
  have hR : Six.radius^2≤Six.qStar := by rw [radius_sq]
  obtain ⟨P,htrace⟩ := Normalization.normalize_of_candidate hp hR
  exact Equality.AnalyticReconstruction.original_congruent_of_reduction
    P hR (Classification.reduction P) htrace

/-- An inhabitant of the unchanged unrestricted uniqueness goal. -/
theorem uniqueness_goal : Goals.Uniqueness := by
  intro S o hp
  exact uniqueness hp

/-- The upper-right corner of the east square lies on the candidate circle. -/
theorem model_reaches : ∃ (i : Fin 6) (p : Point),
    closedSquare (Six.model i) p ∧ Six.radius^2≤normSq p := by
  refine ⟨2,(sStar+3/2,sStar+1/2),?_,?_⟩
  · change closedSquare (axisSquare (sStar+1,sStar)) (sStar+3/2,sStar+1/2)
    constructor
    · change |(sStar+3/2)-(sStar+1)|≤1/2
      rw [show (sStar+3/2)-(sStar+1)=(1:ℝ)/2 by ring]
      norm_num
    · change |(sStar+1/2)-sStar|≤1/2
      rw [show (sStar+1/2)-sStar=(1:ℝ)/2 by ring]
      norm_num
  · dsimp [normSq]
    nlinarith [radius_sq,east_radius_identity]

/-- The six-square case in the same public `Optimum` interface as cases 1–5
and 7. No problem predicate or equality notion has been changed. -/
def optimum : Optimum 6 :=
  Optimum.ofUnique Six.model model_packing model_reaches
    (fun S o hp => uniqueness hp)

/-- Lower bound, explicit attainment, and equality classification together. -/
theorem characterization :
    (∀ (S : Fin 6 → UnitSquare) (o : Point) (R : ℝ), Packing S o R → Six.radius≤R) ∧
    Packing Six.model (0,0) Six.radius ∧
    (∀ (S : Fin 6 → UnitSquare) (o : Point), Packing S o Six.radius → Congruent S o Six.model) :=
  ⟨fun _ _ _ hp => lower_bound hp,model_packing,fun _ _ hp => uniqueness hp⟩

end SquaresInCircles.Six
