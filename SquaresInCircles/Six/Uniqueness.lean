import SquaresInCircles.Six.Analytic.CompleteReduction
import SquaresInCircles.Six.Construction
import SquaresInCircles.Six.Containing
import SquaresInCircles.Six.Equality.AnalyticReconstruction
import SquaresInCircles.Common.Optimum

/-!
# Six squares: uniqueness

A packing of six unit squares in the closed disk of radius `radius` is first
normalized: one square contains the disk centre, five fixed pins label the
others, and the packing is read in a frame of the central square, possibly
after a reflection in a diagonal. The reduction then supplies the separating
axes and the angle domains of the stress; at the optimal radius the eight
contacts of the stress are tight and fix every centre, and the diagonal
symmetry of the model absorbs the reflection.

The file ends with `optimum`: the case as an `Optimum`, which also gives the
lower bound.
-/

noncomputable section
namespace SquaresInCircles.Six

/-- Every packing of six unit squares in a closed disk of radius `radius` is
congruent to `model`. -/
theorem uniqueness (S : Fin 6 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : Congruent S o model := by
  obtain ⟨P,htrace⟩ := Normalization.normalize_of_candidate hp radius_sq.le
  exact Equality.AnalyticReconstruction.original_congruent_of_reduction
    P radius_sq.le (Analytic.FixedPair.complete_reduction P) htrace

/-- The corner `(sStar + 3/2, sStar + 1/2)` of the square to the right of the
central one lies on the circle of radius `radius`. -/
lemma model_reaches : ∃ (i : Fin 6) (p : Point),
    closedSquare (model i) p ∧ radius ^ 2 ≤ normSq p := by
  refine ⟨2,(sStar+3/2,sStar+1/2),(axisSquare_closed _ _).2 ?_,?_⟩
  · constructor <;> norm_num
  · dsimp [normSq]
    nlinarith [radius_sq,east_radius_identity]

/-- The optimum for six squares: `radius`, attained only by the configurations
congruent to `model`. -/
def optimum : Optimum 6 :=
  .ofUnique model model_packing model_reaches uniqueness

end SquaresInCircles.Six
