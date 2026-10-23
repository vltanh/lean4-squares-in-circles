module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighBridgeResiduals

/-!
# The outer-bridge cap from the six unchanged original physical edges

The actual G1 inequalities telescope with the same marker at each
shared vertex.  The six-edge frame path pays the width of DE by the
metric triangle inequality.  The residual type bonus is derived from
the original six chart pairs.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge

open Candidate FramePair GlobalOuterAnchor

def markerCharge (C : BoundaryCycle Q0) (theta : Vertex→ℝ) (i : Vertex) : ℝ :=
  phi theta i+((stateOf C i).signedLabel-(stateOf C (next i)).signedLabel)

theorem markerCharge_sum (C : BoundaryCycle Q0) (theta : Vertex→ℝ) :
    (∑i,markerCharge C theta i)=2*Real.pi := by
  simp only [markerCharge,Finset.sum_add_distrib,sum_phi,sum_marker_difference,add_zero]

theorem frame_pair_bound {C : BoundaryCycle Q0} (F : Candidate.Frame C) (i : Vertex) :
    handGamma (stateOf C i).branch.type (stateOf C (next i)).branch.type<
      markerCharge C F.theta i-(9/50)*frameCost |delta F.theta i| := by
  have hh := FrameAllPairs.all_pair C i
  rw [State.cost,pairAngle_charge,← frameCost_eq_actual F i] at hh
  have hphase : pairAngle C i=phi F.theta i :=
    (pairAngle_gap C i).trans (F.physical_angle i).symm
  rw [hphase] at hh
  dsimp [markerCharge]
  linarith

theorem markerCharge_DE (C : BoundaryCycle Q0) (theta : Vertex→ℝ)
    (hD : transverse (stateOf C D)≤0) (hE : transverse (stateOf C E)≤0) :
    markerCharge C theta D=oldCharge (stateOf C D) (stateOf C E) (delta theta D) := by
  have hd := GlobalQuarterSign.signed_of_nonpos (stateOf C D) hD
  have he := GlobalQuarterSign.signed_of_nonpos (stateOf C E) hE
  rw [markerCharge,show next D=E by decide,hd,he]
  simp only [oldCharge,phi,show word D=1 by decide,Int.cast_one,one_mul]
  ring

theorem six_edge_return {C : BoundaryCycle Q0} (F : Candidate.Frame C) :
    frameCost |delta F.theta D|≤
      frameCost |delta F.theta E|+frameCost |delta F.theta H|+
      frameCost |delta F.theta G|+frameCost |delta F.theta A|+
      frameCost |delta F.theta B|+frameCost |delta F.theta T| := by
  have hrange (i j : Vertex) : |F.theta j-F.theta i|∈Icc 0 (Real.pi/4) := by
    refine ⟨abs_nonneg _,?_⟩
    linarith [F.spread j i,Real.pi_gt_three]
  have hG := frameCost_triangle (hrange E H) (hrange H G) (hrange E G)
    (abs_sub_le (F.theta G) (F.theta H) (F.theta E))
  have hA := frameCost_triangle (hrange E G) (hrange G A) (hrange E A)
    (abs_sub_le (F.theta A) (F.theta G) (F.theta E))
  have hB := frameCost_triangle (hrange E A) (hrange A B) (hrange E B)
    (abs_sub_le (F.theta B) (F.theta A) (F.theta E))
  have hT := frameCost_triangle (hrange E B) (hrange B T) (hrange E T)
    (abs_sub_le (F.theta T) (F.theta B) (F.theta E))
  have hD := frameCost_triangle (hrange E T) (hrange T D) (hrange E D)
    (abs_sub_le (F.theta D) (F.theta T) (F.theta E))
  have hsum : frameCost |F.theta D-F.theta E|≤
      frameCost |F.theta H-F.theta E|+frameCost |F.theta G-F.theta H|+
      frameCost |F.theta A-F.theta G|+frameCost |F.theta B-F.theta A|+
      frameCost |F.theta T-F.theta B|+frameCost |F.theta D-F.theta T| := by linarith
  simpa only [delta,E,H,G,A,B,T,D,next,abs_sub_comm] using hsum

theorem frame_six_pairs {C : BoundaryCycle Q0} (F : Candidate.Frame C) :
    sixTypeCost (stateOf C E).branch.type (stateOf C H).branch.type
      (stateOf C G).branch.type (stateOf C A).branch.type (stateOf C B).branch.type
      (stateOf C T).branch.type (stateOf C D).branch.type<
    markerCharge C F.theta E+markerCharge C F.theta H+markerCharge C F.theta G+
      markerCharge C F.theta A+markerCharge C F.theta B+markerCharge C F.theta T-
      (9/50)*(frameCost |delta F.theta E|+frameCost |delta F.theta H|+
        frameCost |delta F.theta G|+frameCost |delta F.theta A|+
        frameCost |delta F.theta B|+frameCost |delta F.theta T|) := by
  have hE := frame_pair_bound F E
  have hH := frame_pair_bound F H
  have hG := frame_pair_bound F G
  have hA := frame_pair_bound F A
  have hB := frame_pair_bound F B
  have hT := frame_pair_bound F T
  dsimp [sixTypeCost,E,H,G,A,B,T,D,next] at hE hH hG hA hB hT ⊢
  linarith

/-- The only cap used by the complete bridge theorem is now a
consequence of the actual original seven-cycle. -/
theorem original_cap {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hD : transverse (stateOf C D)≤0) (hE : transverse (stateOf C E)≤0) :
    augmentedOld (stateOf C D) (stateOf C E) (delta F.theta D)<
      cap-bonus (stateOf C D).branch.type (stateOf C E).branch.type := by
  have htypes := six_type_bonus (stateOf C E).branch.type (stateOf C H).branch.type
    (stateOf C G).branch.type (stateOf C A).branch.type (stateOf C B).branch.type
    (stateOf C T).branch.type (stateOf C D).branch.type
  rw [bonus_symm (stateOf C E).branch.type (stateOf C D).branch.type] at htypes
  have hpairs := frame_six_pairs F
  have hreturn := six_edge_return F
  have hsum := markerCharge_sum C F.theta
  simp only [Fin.sum_univ_succ] at hsum
  have hDE := markerCharge_DE C F.theta hD hE
  have hcomp : markerCharge C F.theta E+markerCharge C F.theta H+markerCharge C F.theta G+
      markerCharge C F.theta A+markerCharge C F.theta B+markerCharge C F.theta T+
      oldCharge (stateOf C D) (stateOf C E) (delta F.theta D)=2*Real.pi := by
    dsimp [H,G,A,B,T,D,E] at hDE ⊢
    linarith
  dsimp [augmentedOld,cap]
  linarith [Arithmetic.two_pi_lt_710_over_113]

end SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge
