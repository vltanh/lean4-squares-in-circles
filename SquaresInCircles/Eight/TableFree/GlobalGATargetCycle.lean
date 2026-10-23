module

public import SquaresInCircles.Eight.TableFree.GlobalGATargetPath
public import SquaresInCircles.Eight.TableFree.GlobalOriginalOwners

/-!
# A retained high-GA target has signed tangent below one half

Uncompiled transcription of the final original-cycle join in
`HAND_G3_HIGH_GA_TARGET_HAS_SMALL_TANGENT.md`.
The four return edges keep arbitrary original owners and radial states.
Their actual G1 charges pay the return allowance, and the very same
original markers telescope with the three-edge path to exactly 2 pi.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Target
open Candidate FramePair ZeroPrimary GlobalOuterAnchor GlobalAllHigh
open GlobalAllHigh.Bridge

theorem four_edge_return {C : BoundaryCycle Q0} (F : Candidate.Frame C) :
    frameCost |delta F.theta H+delta F.theta G+delta F.theta A|≤
      frameCost |delta F.theta B|+frameCost |delta F.theta T|+
      frameCost |delta F.theta D|+frameCost |delta F.theta E| := by
  have hrange (i j : Vertex) : |F.theta j-F.theta i|∈Icc 0 (Real.pi/4) := by
    exact ⟨abs_nonneg _,by linarith [F.spread j i,Real.pi_gt_three]⟩
  have hD := frameCost_triangle (hrange B T) (hrange T D) (hrange B D)
    (abs_sub_le (F.theta D) (F.theta T) (F.theta B))
  have hE := frameCost_triangle (hrange B D) (hrange D E) (hrange B E)
    (abs_sub_le (F.theta E) (F.theta D) (F.theta B))
  have hH := frameCost_triangle (hrange B E) (hrange E H) (hrange B H)
    (abs_sub_le (F.theta H) (F.theta E) (F.theta B))
  have hs : delta F.theta H+delta F.theta G+delta F.theta A=F.theta B-F.theta H := by
    dsimp [delta,H,G,A,B,next]
    ring
  rw [hs,abs_sub_comm]
  change frameCost |F.theta H-F.theta B|≤
    frameCost |F.theta T-F.theta B|+frameCost |F.theta D-F.theta T|+
      frameCost |F.theta E-F.theta D|+frameCost |F.theta H-F.theta E|
  linarith

theorem return_charge {C : BoundaryCycle Q0} (F : Candidate.Frame C) :
    4*(8833/10000:ℝ)+(9/50)*frameCost |delta F.theta H+delta F.theta G+delta F.theta A|<
      markerCharge C F.theta B+markerCharge C F.theta T+
      markerCharge C F.theta D+markerCharge C F.theta E := by
  have hpair (i : Vertex) : (8833/10000:ℝ)<
      markerCharge C F.theta i-(9/50)*frameCost |delta F.theta i| :=
    (handGamma_lower _ _).trans_lt (frame_pair_bound F i)
  have hB := hpair B
  have hT := hpair T
  have hD := hpair D
  have hE := hpair E
  have hreturn := four_edge_return F
  linarith

theorem path_marker_identity {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hH : 0≤transverse (stateOf C H)) (hB : transverse (stateOf C B)≤0) :
    markerCharge C F.theta H+markerCharge C F.theta G+markerCharge C F.theta A=
      pathCharge (stateOf C H) (stateOf C B)
        (delta F.theta H) (delta F.theta G) (delta F.theta A) := by
  have hh := GlobalQuarterSign.signed_of_nonneg (stateOf C H) hH
  have hb := GlobalQuarterSign.signed_of_nonpos (stateOf C B) hB
  simp only [markerCharge,show next H=G by decide,show next G=A by decide,
    show next A=B by decide,phi,show word H=0 by decide,show word G=1 by decide,
    show word A=0 by decide,Int.cast_zero,Int.cast_one,mul_zero,zero_mul,one_mul,
    zero_add,hh,hb,pathCharge]
  ring

theorem fixed_target_small {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0) (j : Fin 4) (hhigh : j=2 ∨ j=3)
    (hGA : (forwardAxis j).Feasible (C.square G) (C.square A)) :
    transverse (stateOf C A)<1/2 := by
  by_contra! hlarge
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hH := GlobalOriginalOwners.frame_H_anchor F hq
  have hG := GlobalQuarterOuter.frame_high_anchor F hq G (by norm_num [word,G])
    j hhigh (by simpa [G,A,next] using hGA)
  have hB := GlobalOriginalOwners.frame_B_anchor F hq hE
  have hHy := (state_positive_of_tangent C H hH.2).le
  have hGy := (state_negative_of_tangent C G hG.2).le
  have hBy := (state_negative_of_tangent C B hB.2).le
  let jH := SignedCycle.retainedOwner F H
  let jA := SignedCycle.retainedOwner F A
  have hHG : (forwardAxis jH).Feasible (C.square H) (C.square (next H)) :=
    (SignedCycle.atFrame_feasible F H jH).1 (SignedCycle.retainedOwner_feasible F H)
  have hAB : (forwardAxis jA).Feasible (C.square A) (C.square (next A)) :=
    (SignedCycle.atFrame_feasible F A jA).1 (SignedCycle.retainedOwner_feasible F A)
  have hHowner := GlobalZeroSign.of_frame F hq H (by norm_num [word,H]) jH hHG
  have hAowner := GlobalZeroSign.of_frame F hq A (by norm_num [word,A]) jA hAB
  have hHowners : jH=0 ∨ jH=2 := hHowner.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1)
  have hAowners : jA=0 ∨ jA=2 := hAowner.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1)
  have hHGstate : (stateOf C H).Feasible (stateOf C G) jH (delta F.theta H) := by
    simpa [phi,word,H,G,next] using frame_state_feasible F H jH hHG
  have hGAstate : (stateOf C G).Feasible (stateOf C A) j (Real.pi/2+delta F.theta G) := by
    have hh := frame_state_feasible F G j (by simpa [G,A,next] using hGA)
    simpa [phi,word,G,A,next] using hh
  have hABstate : (stateOf C A).Feasible (stateOf C B) jA (delta F.theta A) := by
    simpa [phi,word,A,B,next] using frame_state_feasible F A jA hAB
  have hspan : |delta F.theta H+delta F.theta G+delta F.theta A|≤frameCap := by
    have he : delta F.theta H+delta F.theta G+delta F.theta A=F.theta B-F.theta H := by
      dsimp [delta,H,G,A,B,next]
      ring
    rw [he]
    exact (F.spread B H).le
  have hpath := original_path (stateOf C H) (stateOf C G) (stateOf C A) (stateOf C B)
    (state_outer_of_kind C H hH.1) (state_outer_of_kind C G hG.1)
    (state_outer_of_kind C B hB.1) hHy hGy hlarge hBy
    (by simpa [frameCap] using (F.delta_small H).le)
    (by simpa [frameCap] using (F.delta_small G).le)
    (by simpa [frameCap] using (F.delta_small A).le) hspan
    jH j jA hHowners hhigh hAowners hHGstate hGAstate hABstate
  have hreturn := return_charge F
  have hid := path_marker_identity F hHy hBy
  have hsum := markerCharge_sum C F.theta
  simp only [Fin.sum_univ_succ] at hsum
  have htotal : pathCharge (stateOf C H) (stateOf C B)
      (delta F.theta H) (delta F.theta G) (delta F.theta A)+
      markerCharge C F.theta B+markerCharge C F.theta T+
      markerCharge C F.theta D+markerCharge C F.theta E=2*Real.pi := by
    dsimp [H,G,A,B,T,D,E] at hid ⊢
    linarith
  have hpi := Arithmetic.two_pi_lt_710_over_113
  linarith

theorem fixed_frame_target_small {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0) (j : Fin 4) (hhigh : j=2 ∨ j=3)
    (hGA : (forwardAxis j).Feasible (C.square G) (C.square A)) :
    ((SignedCycle.atFrame F).point A).y<1/2 := by
  have hh := fixed_target_small F hE j hhigh hGA
  simpa only [transverse,stateOf,signOf_spec,SignedCycle.atFrame] using hh

end SquaresInCircles.Eight.TableFree.GlobalGA.Target
