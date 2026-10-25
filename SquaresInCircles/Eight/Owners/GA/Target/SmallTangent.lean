module

public import SquaresInCircles.Eight.Owners.GA.Target.Path
public import SquaresInCircles.Eight.Owners.OriginalOwners

/-!
# Eight squares: the high-GA target cut on the boundary cycle

The cut is first proved at `Q0` (`fixed_frame_target_small`). `frame_target_small` passes to `q`
through the auxiliary radius expansion, which keeps every weak axis and its index, the tangent
ratio and the common frame. A positive signed coordinate can only grow under that expansion, so
the cut on the circle of `Q0` implies the cut at `q`.
-/

section
/-!
## The target of a high GA witness has signed tangent below one half

The four return edges keep their owners and radial states, whatever they are. Their G1 charges pay
the return allowance (`return_charge`), and the same markers telescope with the three-edge path to
exactly `2π` (`path_marker_identity`), which gives `fixed_target_small`.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.Target
open Candidate FramePair ZeroPrimary GlobalOuterAnchor GlobalAllHigh
open GlobalAllHigh.Bridge

theorem four_edge_return {C : BoundaryCycle Q0} (F : Candidate.Frame C) :
    frameCost |delta F.theta H+delta F.theta G+delta F.theta A|≤
      frameCost |delta F.theta B|+frameCost |delta F.theta T|+
      frameCost |delta F.theta D|+frameCost |delta F.theta E| := by
  have hrange (i j : Vertex) : |F.theta j-F.theta i|∈Icc 0 (Real.pi/4) := by
    exact ⟨abs_nonneg _,by linarith [F.spread j i,Real.pi_gt_three]⟩
  have hD := frameCost_triangle (hrange B T) (hrange T D) (hrange B D)
    (by linarith [abs_sub_le (F.theta D) (F.theta T) (F.theta B)])
  have hE := frameCost_triangle (hrange B D) (hrange D E) (hrange B E)
    (by linarith [abs_sub_le (F.theta E) (F.theta D) (F.theta B)])
  have hH := frameCost_triangle (hrange B E) (hrange E H) (hrange B H)
    (by linarith [abs_sub_le (F.theta H) (F.theta E) (F.theta B)])
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
    show next A=B by decide,Candidate.phi,show word H=0 by decide,show word G=1 by decide,
    show word A=0 by decide,Int.cast_zero,Int.cast_one,zero_mul,one_mul,
    hh,hb,pathCharge]
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
    simpa [Candidate.phi,word,H,G,next] using frame_state_feasible F H jH hHG
  have hGAstate : (stateOf C G).Feasible (stateOf C A) j (Real.pi/2+delta F.theta G) := by
    have hh := frame_state_feasible F G j (by simpa [G,A,next] using hGA)
    simpa [Candidate.phi,word,G,A,next] using hh
  have hABstate : (stateOf C A).Feasible (stateOf C B) jA (delta F.theta A) := by
    simpa [Candidate.phi,word,A,B,next] using frame_state_feasible F A jA hAB
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
  rw [Fin.sum_univ_seven] at hsum
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

end SquaresInCircles.Eight.GlobalGA.Target
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.Target
open Candidate

theorem frame_target_small {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (j : Fin 4) (hhigh : j=2 ∨ j=3)
    (hGA : (forwardAxis j).Feasible (C.square G) (C.square A)) :
    ((SignedCycle.atFrame F).point A).y<1/2 := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let F' : Candidate.Frame D := FramePhysicalTransport.candidatePushforward F hR le_rfl
  have hE' : D.tangent E≤0 := by rw [hR.same_tangents]; exact hE
  have hGA' : (forwardAxis j).Feasible (D.square G) (D.square A) := by
    have hh := hR.preserves_all_axes G (forwardAxis j) (by simpa [G,A,next] using hGA)
    simpa [G,A,next] using hh
  have hcut := fixed_frame_target_small F' hE' j hhigh hGA'
  have hfactor : 1≤C.expansionFactor Q0 A := C.expansionFactor_ge_one
    ⟨hq.1,hq.2.trans (by norm_num [Q0])⟩ (by norm_num [Q0]) hq.2 A
  have hy : ((SignedCycle.atFrame F').point A).y=
      C.expansionFactor Q0 A*((SignedCycle.atFrame F).point A).y := by
    dsimp [SignedCycle.atFrame,D,FramePhysicalTransport.auxiliary,BoundaryCycle.expand]
    ring
  by_contra! hlarge
  have hm := mul_le_mul_of_nonneg_right hfactor
    (show 0≤((SignedCycle.atFrame F).point A).y by linarith)
  rw [hy] at hcut
  linarith

end SquaresInCircles.Eight.GlobalGA.Target
end
end
end
