import SquaresInCircles.Six.Classification.CandidateGraph
import SquaresInCircles.Six.Stress.RowTactics

/-!
# Source-independent candidate tails

Once the universal candidate D-edge graph is known, the fixed tail stresses
reduce each W/S bit family to the compact angle box used by its candidate
closure. These statements use only C,W,D,S and therefore do not depend on the
E/N bits.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

noncomputable section
namespace SquaresInCircles.Six.Classification
open Normalization Stress

/-- Pattern-10 family: W and S cardinal. -/
theorem cardinalWS_tail_box {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.ownBits 4=false) :
    -1/6<P.helperAngle 2 ∧
    -3/10<P.helperAngle 4 ∧ P.helperAngle 4<3/10 := by
  have hg := candidate_diagonal_edges P
  have hw := abs_lt.mp (P.cardinal_angle 2 hW)
  have hs := abs_lt.mp (P.cardinal_angle 4 hS)
  have hslo : -3/10<P.helperAngle 4 := by
    by_contra! h
    exclude_main 15 for P
  have hshi : P.helperAngle 4<3/10 := by
    by_contra! h
    exclude_main 16 for P
  have hwlo : -1/6<P.helperAngle 2 := by
    by_contra! h
    exclude_main 17 for P
  exact ⟨hwlo,hslo,hshi⟩

/-- The W-cardinal/S-cardinal bridge removes the remaining upper S band. -/
theorem cardinalWS_small_box {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.ownBits 4=false) :
    -1/6<P.helperAngle 2 ∧
    -3/10<P.helperAngle 4 ∧ P.helperAngle 4<1/6 := by
  obtain ⟨hw,hslo,hshi⟩ := cardinalWS_tail_box P hW hS
  have hs : P.helperAngle 4<1/6 := by
    by_contra! h
    exclude_bridge 0 for P
  exact ⟨hw,hslo,hs⟩

/-- Pattern-14/A2.2 family: W own, S cardinal. -/
theorem ownW_cardinalS_tail_box {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=true) (hS : P.ownBits 4=false) :
    -21/50<P.helperAngle 2 ∧ P.helperAngle 2<2/25 := by
  have hg := candidate_diagonal_edges P
  have hw := P.helper_windows.2.2.1
  have hs := abs_lt.mp (P.cardinal_angle 4 hS)
  have hwup : P.helperAngle 2<2/25 := by
    by_contra! h
    exclude_main 21 for P
  have hwlo : -21/50<P.helperAngle 2 := by
    by_contra! h
    by_cases h0 : P.helperAngle 4≤-3/20
    · exclude_main 22 for P
    by_cases h1 : P.helperAngle 4≤1/10
    · exclude_main 23 for P
    · exclude_main 24 for P
  exact ⟨hwlo,hwup⟩

/-- Pattern-26 family: W cardinal, S own. -/
theorem cardinalW_ownS_tail_box {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.ownBits 4=true) :
    -1/6<P.helperAngle 2 ∧
    -1/6<P.helperAngle 4 ∧ P.helperAngle 4<1/2 := by
  have hg := candidate_diagonal_edges P
  have hw := abs_lt.mp (P.cardinal_angle 2 hW)
  have hs := P.helper_windows.2.2.2
  have hslo : -1/6<P.helperAngle 4 := by
    by_contra! h
    exclude_app 96 for P
  have hshi : P.helperAngle 4<1/2 := by
    by_contra! h
    exclude_app 97 for P
  have hwlo : -1/6<P.helperAngle 2 := by
    by_contra! h
    exclude_app 98 for P
  exact ⟨hwlo,hslo,hshi⟩

/-- The two Pattern-27 bridge stresses give the narrower S strip used by
Patterns 24,25,27. -/
theorem cardinalW_ownS_survivor_box {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.ownBits 4=true) :
    -1/6<P.helperAngle 2 ∧
    -2/25<P.helperAngle 4 ∧ P.helperAngle 4<11/25 := by
  obtain ⟨hw,hslo,hshi⟩ := cardinalW_ownS_tail_box P hW hS
  have hlo : -2/25<P.helperAngle 4 := by
    by_contra! h
    exclude_bridge 1 for P
  have hhi : P.helperAngle 4<11/25 := by
    by_contra! h
    exclude_bridge 2 for P
  exact ⟨hw,hlo,hhi⟩

/-- A2.3 family: W and S own. -/
theorem ownWS_tail_box {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=true) (hS : P.ownBits 4=true) :
    -21/50<P.helperAngle 2 ∧ P.helperAngle 2<2/25 ∧
    -1/6<P.helperAngle 4 ∧ P.helperAngle 4<1/2 := by
  have hg := candidate_diagonal_edges P
  have hw := P.helper_windows.2.2.1
  have hs := P.helper_windows.2.2.2
  have hslo : -1/6<P.helperAngle 4 := by
    by_contra! h
    by_cases h0 : P.helperAngle 4≤-3/10
    · exclude_app 50 for P
    · exclude_app 51 for P
  have hshi : P.helperAngle 4<1/2 := by
    by_contra! h
    by_cases hw0 : P.helperAngle 2≤-1/6
    · by_cases hs0 : P.helperAngle 4≤13/20
      · exclude_app 52 for P
      · exclude_app 53 for P
    · by_cases hw1 : P.helperAngle 2≤2/5
      · by_cases hs1 : P.helperAngle 4≤2/3
        · exclude_app 54 for P
        · exclude_app 55 for P
      · exclude_app 56 for P
  have hwup : P.helperAngle 2<2/25 := by
    by_contra! h
    by_cases h0 : P.helperAngle 2≤1/4
    · exclude_app 57 for P
    by_cases h1 : P.helperAngle 2≤1/2
    · exclude_app 58 for P
    · exclude_app 59 for P
  have hwlo : -21/50<P.helperAngle 2 := by
    by_contra! h
    exclude_tail 0 for P
  exact ⟨hwlo,hwup,hslo,hshi⟩

end SquaresInCircles.Six.Classification
