import SquaresInCircles.Six.Classification.A22Edges
import SquaresInCircles.Six.Classification.A23Edges
import SquaresInCircles.Six.Classification.Pattern26Edges
import SquaresInCircles.Six.Classification.CardinalEdges

/-!
# Universal candidate D-edge graph

The four W/S canonical-bit combinations are discharged independently by the
corresponding exact fixed-stress tables. Consequently every normalized packing
has the same surviving diagonal graph before the pattern-specific candidate
closure: W--D is W-secondary and D--S is S-secondary.
-/

noncomputable section
namespace SquaresInCircles.Six.Classification
open Normalization

theorem candidate_diagonal_edges {R : ℝ} (P : NormalizedPacking R) :
    DWSelected P 2 ∧ DSSelected P 6 ∧ 1/2<P.diagonalAngle := by
  cases hW : P.ownBits 2 <;> cases hS : P.ownBits 4
  · exact cardinalWS_candidate_diagonal_edges P hW hS
  · exact cardinalW_ownS_candidate_diagonal_edges P hW hS
  · exact a22_candidate_diagonal_edges P hW hS
  · exact a23_candidate_diagonal_edges P hW hS

end SquaresInCircles.Six.Classification
