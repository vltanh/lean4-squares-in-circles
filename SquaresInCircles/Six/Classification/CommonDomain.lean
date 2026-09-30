import SquaresInCircles.Six.Classification.CandidateTails
import SquaresInCircles.Six.Stress.DiagonalVertexCheck

/-!
# A common compact domain for the balanced candidate stress

The rectangle is a consequence of the proved exact fixed-stress tail rows,
not an additional assumption on a normalized packing. It covers all four W/S
bit cases and does not impose any E/N bit choice.
-/

noncomputable section
namespace SquaresInCircles.Six.Classification
open Normalization Stress

/-- The two remaining own/own tails narrow the last S interval. -/
theorem ownWS_survivor_box {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=true) (hS : P.ownBits 4=true) :
    (-21/50<P.helperAngle 2 ∧ P.helperAngle 2<2/25) ∧
      (-2/25<P.helperAngle 4 ∧ P.helperAngle 4<21/50) := by
  obtain ⟨hwlo,hwhi,hslo,hshi⟩ := ownWS_tail_box P hW hS
  have hg := candidate_diagonal_edges P
  have hd := P.diagonal_angle_range
  have hslow : -2/25<P.helperAngle 4 := by
    by_contra! h
    exclude_tail 1 for P
  have hshigh : P.helperAngle 4<21/50 := by
    by_contra! h
    exclude_tail 2 for P
  exact ⟨⟨hwlo,hwhi⟩,⟨hslow,hshigh⟩⟩

/-- Every normalized packing lies in the same W/S rectangle. -/
theorem common_west_south_rectangle {R : ℝ} (P : NormalizedPacking R) :
    (-11/25≤P.helperAngle 2 ∧ P.helperAngle 2≤2/5) ∧
      (-2/5≤P.helperAngle 4 ∧ P.helperAngle 4≤11/25) := by
  cases hW : P.ownBits 2 <;> cases hS : P.ownBits 4
  · have h := cardinalWS_small_box P hW hS
    have hw := abs_lt.mp (P.cardinal_angle 2 hW)
    exact ⟨⟨by linarith [h.1],hw.2.le⟩,
      ⟨by linarith [h.2.1],by linarith [h.2.2]⟩⟩
  · have h := cardinalW_ownS_survivor_box P hW hS
    have hw := abs_lt.mp (P.cardinal_angle 2 hW)
    exact ⟨⟨by linarith [h.1],hw.2.le⟩,
      ⟨by linarith [h.2.1],h.2.2.le⟩⟩
  · have h := ownW_cardinalS_tail_box P hW hS
    have hs := abs_lt.mp (P.cardinal_angle 4 hS)
    exact ⟨⟨by linarith [h.1],by linarith [h.2]⟩,
      ⟨hs.1.le,by linarith [hs.2]⟩⟩
  · have h := ownWS_survivor_box P hW hS
    exact ⟨⟨by linarith [h.1.1],by linarith [h.1.2]⟩,
      ⟨by linarith [h.2.1],by linarith [h.2.2]⟩⟩

/-- Both adjacent pairs fit the exact common pair-envelope rectangle. -/
theorem common_pair_domains {R : ℝ} (P : NormalizedPacking R) :
    (-3/10≤P.helperAngle 1 ∧ P.helperAngle 1≤5/12) ∧
    (-11/25≤P.helperAngle 2 ∧ P.helperAngle 2≤2/5) ∧
    (-3/10≤-P.helperAngle 0 ∧ -P.helperAngle 0≤5/12) ∧
    (-11/25≤-P.helperAngle 4 ∧ -P.helperAngle 4≤2/5) := by
  have hw := common_west_south_rectangle P
  have hh := P.helper_windows
  exact ⟨⟨hh.2.1.1.le,hh.2.1.2.le⟩,hw.1,
    ⟨by linarith [hh.1.2],by linarith [hh.1.1]⟩,
    ⟨by linarith [hw.2.2],by linarith [hw.2.1]⟩⟩

/-- The diagonal term uses the same common domain and the proved d>1/2. -/
theorem common_diagonal_domain {R : ℝ} (P : NormalizedPacking R) :
    DiagonalDomain (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle := by
  have hw := common_west_south_rectangle P
  have hd := candidate_diagonal_edges P
  exact ⟨hw.1,hw.2,⟨hd.2.2.le,P.diagonal_angle_range.2⟩⟩

end SquaresInCircles.Six.Classification
