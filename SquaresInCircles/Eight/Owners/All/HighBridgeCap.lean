module

public import SquaresInCircles.Eight.Owners.All.HighBridgeResiduals

/-!
# Eight squares: the outer-bridge cap from the six unchanged original physical edges

The actual G1 inequalities telescope with the same marker at each
shared vertex.  The six-edge frame path pays the width of DE by the
metric triangle inequality.  The residual type bonus is derived from
the original six chart pairs.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.GlobalAllHigh.Bridge

open Candidate FramePair GlobalOuterAnchor

def markerCharge (C : BoundaryCycle Q0) (theta : Vertex→ℝ) (i : Vertex) : ℝ :=
  Candidate.phi theta i+((stateOf C i).signedLabel-(stateOf C (next i)).signedLabel)

theorem markerCharge_sum (C : BoundaryCycle Q0) (theta : Vertex→ℝ) :
    (∑i,markerCharge C theta i)=2*Real.pi := by
  simp only [markerCharge,Finset.sum_add_distrib,sum_phi,sum_marker_difference,add_zero]

theorem frame_pair_bound {C : BoundaryCycle Q0} (F : Candidate.Frame C) (i : Vertex) :
    handGamma (stateOf C i).branch.type (stateOf C (next i)).branch.type<
      markerCharge C F.theta i-(9/50)*frameCost |delta F.theta i| := by
  have hh := FrameAllPairs.all_pair C i
  rw [State.cost,pairAngle_charge,← frameCost_eq_actual F i] at hh
  have hphase : pairAngle C i=Candidate.phi F.theta i :=
    (pairAngle_gap C i).trans (F.physical_angle i).symm
  rw [hphase] at hh
  change handGamma (stateOf C i).branch.type (stateOf C (next i)).branch.type<_ at hh
  dsimp [markerCharge]
  linarith

theorem markerCharge_DE (C : BoundaryCycle Q0) (theta : Vertex→ℝ)
    (hD : transverse (stateOf C D)≤0) (hE : transverse (stateOf C E)≤0) :
    markerCharge C theta D=unsignedCharge (stateOf C D) (stateOf C E) (delta theta D) := by
  have hd := GlobalQuarterSign.signed_of_nonpos (stateOf C D) hD
  have he := GlobalQuarterSign.signed_of_nonpos (stateOf C E) hE
  rw [markerCharge,show next D=E by decide,hd,he]
  simp only [unsignedCharge,Candidate.phi,show word D=1 by decide,Int.cast_one,one_mul]
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
    (by linarith [abs_sub_le (F.theta G) (F.theta H) (F.theta E)])
  have hA := frameCost_triangle (hrange E G) (hrange G A) (hrange E A)
    (by linarith [abs_sub_le (F.theta A) (F.theta G) (F.theta E)])
  have hB := frameCost_triangle (hrange E A) (hrange A B) (hrange E B)
    (by linarith [abs_sub_le (F.theta B) (F.theta A) (F.theta E)])
  have hT := frameCost_triangle (hrange E B) (hrange B T) (hrange E T)
    (by linarith [abs_sub_le (F.theta T) (F.theta B) (F.theta E)])
  have hD := frameCost_triangle (hrange E T) (hrange T D) (hrange E D)
    (by linarith [abs_sub_le (F.theta D) (F.theta T) (F.theta E)])
  have hsum : frameCost |F.theta D-F.theta E|≤
      frameCost |F.theta H-F.theta E|+frameCost |F.theta G-F.theta H|+
      frameCost |F.theta A-F.theta G|+frameCost |F.theta B-F.theta A|+
      frameCost |F.theta T-F.theta B|+frameCost |F.theta D-F.theta T| := by linarith
  have eE : delta F.theta E=F.theta H-F.theta E := by rw [delta,show next E=H by decide]
  have eH : delta F.theta H=F.theta G-F.theta H := by rw [delta,show next H=G by decide]
  have eG : delta F.theta G=F.theta A-F.theta G := by rw [delta,show next G=A by decide]
  have eA : delta F.theta A=F.theta B-F.theta A := by rw [delta,show next A=B by decide]
  have eB : delta F.theta B=F.theta T-F.theta B := by rw [delta,show next B=T by decide]
  have eT : delta F.theta T=F.theta D-F.theta T := by rw [delta,show next T=D by decide]
  have eD : delta F.theta D=F.theta E-F.theta D := by rw [delta,show next D=E by decide]
  rw [eE,eH,eG,eA,eB,eT,eD,abs_sub_comm (F.theta E) (F.theta D)]
  exact hsum

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
    augmentedUnsigned (stateOf C D) (stateOf C E) (delta F.theta D)<
      cap-bonus (stateOf C D).branch.type (stateOf C E).branch.type := by
  have htypes := six_type_bonus (stateOf C E).branch.type (stateOf C H).branch.type
    (stateOf C G).branch.type (stateOf C A).branch.type (stateOf C B).branch.type
    (stateOf C T).branch.type (stateOf C D).branch.type
  rw [bonus_symm (stateOf C E).branch.type (stateOf C D).branch.type] at htypes
  have hpairs := frame_six_pairs F
  have hreturn := six_edge_return F
  have hsum := markerCharge_sum C F.theta
  rw [Fin.sum_univ_seven] at hsum
  have hDE := markerCharge_DE C F.theta hD hE
  have hcomp : markerCharge C F.theta E+markerCharge C F.theta H+markerCharge C F.theta G+
      markerCharge C F.theta A+markerCharge C F.theta B+markerCharge C F.theta T+
      unsignedCharge (stateOf C D) (stateOf C E) (delta F.theta D)=2*Real.pi := by
    dsimp [H,G,A,B,T,D,E] at hDE ⊢
    linarith
  dsimp [augmentedUnsigned,cap]
  linarith [Arithmetic.two_pi_lt_710_over_113]

end SquaresInCircles.Eight.GlobalAllHigh.Bridge
