module

public import SquaresInCircles.Eight.TableFree.GlobalBTReturnScalar
public import SquaresInCircles.Eight.TableFree.GlobalEHHighRestriction

/-!
# The complete three-edge return bound on the original physical cycle

All EH/GA owners and both HG transverse owners are retained.  The
three original G1 gains, the original projection sum and the complete
marker scalar yield the strict return charge 103/40.  Only the two
endpoint signs enter; no H/G sign or radial-kind restriction is used.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT

open Candidate FramePair GlobalOuterAnchor GlobalQuarterSign

def returnCharge (C : BoundaryCycle Q0) (theta : Vertex→ℝ) : ℝ :=
  Real.pi+delta theta E+delta theta H+delta theta G-
    kappa*(stateOf C A).b-ZeroPrimary.unsigned (stateOf C E)
def tailCharge (C : BoundaryCycle Q0) (theta : Vertex→ℝ) : ℝ :=
  Real.pi+delta theta A+delta theta B+delta theta T+delta theta D+
    kappa*(stateOf C A).b+ZeroPrimary.unsigned (stateOf C E)

theorem return_tail_sum (C : BoundaryCycle Q0) (theta : Vertex→ℝ) :
    returnCharge C theta+tailCharge C theta=2*Real.pi := by
  simp only [returnCharge,tailCharge,delta,show next E=H by decide,show next H=G by decide,
    show next G=A by decide,show next A=B by decide,show next B=T by decide,
    show next T=D by decide,show next D=E by decide]
  ring

theorem three_frameCost_lower {r v t : ℝ}
    (hr : |r|≤frameCap) (hv : |v|≤frameCap) (ht : |t|≤frameCap) :
    frameCost (min (|r|+|v|+|t|) (3/10))≤
      frameCost |r|+frameCost |v|+frameCost |t| := by
  have hdom {x : ℝ} (hx : |x|≤frameCap) : |x|∈Icc 0 (Real.pi/4) := by
    refine ⟨abs_nonneg _,?_⟩
    dsimp [frameCap] at hx
    linarith [Real.pi_gt_three]
  have hw : min (|r|+|v|) (3/10)∈Icc 0 (Real.pi/4) := by
    refine ⟨le_min (add_nonneg (abs_nonneg r) (abs_nonneg v)) (by norm_num),?_⟩
    linarith [min_le_right (|r|+|v|) (3/10:ℝ),Real.pi_gt_three]
  have hk : min (|r|+|v|+|t|) (3/10)∈Icc 0 (Real.pi/4) := by
    refine ⟨le_min (by positivity) (by norm_num),?_⟩
    linarith [min_le_right (|r|+|v|+|t|) (3/10:ℝ),Real.pi_gt_three]
  have hfirst := frameCost_triangle (hdom hr) (hdom hv) hw (min_le_left _ _)
  have htriangle : min (|r|+|v|+|t|) (3/10)≤ min (|r|+|v|) (3/10)+|t| := by
    by_cases hshort : |r|+|v|≤(3/10:ℝ)
    · rw [min_eq_left hshort]
      exact min_le_left _ _
    · rw [min_eq_right (le_of_not_ge hshort)]
      linarith [min_le_right (|r|+|v|+|t|) (3/10:ℝ),abs_nonneg t]
  have hsecond := frameCost_triangle hw (hdom ht) hk htriangle
  linarith

theorem frame_return {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0) (hA : 0≤C.tangent A) :
    returnThreshold<returnCharge C F.theta := by
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have he : transverse (stateOf C E)≤0 := by
    rw [GlobalAllHigh.state_transverse_eq]
    exact mul_nonpos_of_nonneg_of_nonpos (C.a_pos E).le hE
  have ha : 0≤transverse (stateOf C A) := by
    rw [GlobalAllHigh.state_transverse_eq]
    exact mul_nonneg (C.a_pos A).le hA
  have hex (i : Vertex) :
      ∃ k : Fin 4,(forwardAxis k).Feasible (C.square i) (C.square (next i)) := by
    obtain ⟨k,hk⟩ := F.forward_complete i (C.selected i) (C.feasible i)
    exact ⟨k,hk ▸ C.feasible i⟩
  choose owner hf using hex
  have hHGowner : owner H=0 ∨ owner H=2 := by
    rcases GlobalZeroSign.of_frame F hq H (by norm_num [word,H]) (owner H) (hf H) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hEH : (stateOf C E).Feasible (stateOf C H) (owner E)
      (Real.pi/2+delta F.theta E) := by
    simpa [Candidate.phi,word,E,H,next] using
      GlobalAllHigh.frame_state_feasible F E (owner E) (hf E)
  have hHG : (stateOf C H).Feasible (stateOf C G) (owner H) (delta F.theta H) := by
    simpa [Candidate.phi,word,H,G,next] using
      GlobalAllHigh.frame_state_feasible F H (owner H) (hf H)
  have hGA : (stateOf C G).Feasible (stateOf C A) (owner G)
      (Real.pi/2+delta F.theta G) := by
    simpa [Candidate.phi,word,G,A,next] using
      GlobalAllHigh.frame_state_feasible F G (owner G) (hf G)
  let R : ℝ := |delta F.theta E|+|delta F.theta H|+|delta F.theta G|
  let gain : ℝ := frameCost |delta F.theta E|+frameCost |delta F.theta H|+
    frameCost |delta F.theta G|
  have hsmall : R≤3/10 → (stateOf C A).b≤4*c0-3+R := by
    intro hshort
    exact short_return_endpoint (stateOf C E) (stateOf C H) (stateOf C G) (stateOf C A)
      (owner E) (owner H) (owner G) he ha hHGowner hshort hEH hHG hGA
  have hg : frameCost (min R (3/10))≤gain :=
    three_frameCost_lower (by simpa only [frameCap] using (F.delta_small E).le)
      (by simpa only [frameCap] using (F.delta_small H).le)
      (by simpa only [frameCap] using (F.delta_small G).le)
  have hs := return_marker_reserve (stateOf C A) (by dsimp [R]; positivity) hg hsmall
  have hp (i : Vertex) : (8833/10000:ℝ)+(9/50)*frameCost |delta F.theta i|<
      GlobalAllHigh.Bridge.markerCharge C F.theta i := by
    have hg := ZeroPrimary.handGamma_lower (stateOf C i).branch.type
      (stateOf C (next i)).branch.type
    have hh := GlobalAllHigh.Bridge.frame_pair_bound F i
    linarith
  have heLabel := signed_of_nonpos (stateOf C E) he
  have haLabel := signed_of_nonneg (stateOf C A) ha
  have hsum : GlobalAllHigh.Bridge.markerCharge C F.theta E+
      GlobalAllHigh.Bridge.markerCharge C F.theta H+
      GlobalAllHigh.Bridge.markerCharge C F.theta G=
      Real.pi+delta F.theta E+delta F.theta H+delta F.theta G-
        ZeroPrimary.unsigned (stateOf C E)-ZeroPrimary.unsigned (stateOf C A) := by
    simp only [GlobalAllHigh.Bridge.markerCharge,
      show next E=H by decide,show next H=G by decide,show next G=A by decide,
      heLabel,haLabel,Candidate.phi,show word E=1 by decide,show word H=0 by decide,
      show word G=1 by decide,Int.cast_one,Int.cast_zero,zero_mul,one_mul]
    ring
  have hpE := hp E
  have hpH := hp H
  have hpG := hp G
  dsimp [returnCharge,gain] at hs ⊢
  linarith

/-- This strict cap on the unchanged four-edge tail is the target for
the full BT0/1 dual bounds. -/
theorem frame_tail_cap {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0) (hA : 0≤C.tangent A) :
    tailCharge C F.theta<pathThreshold := by
  have hr := frame_return F hE hA
  have hs := return_tail_sum C F.theta
  have ht := thresholds_sum
  linarith [Arithmetic.two_pi_lt_710_over_113]

end SquaresInCircles.Eight.TableFree.GlobalBT
