module

public import SquaresInCircles.Eight.Owners.EH.Path
public import SquaresInCircles.Eight.Owners.Zero.LowCycle

/-!
# Eight squares: every original high EH axis is excluded in the presence of a low GA axis

The complete three-edge charge is joined to four unchanged original G1
edges.  Their return allowance is bounded by the metric triangle
inequality on the actual four-edge frame path.  No other quarter-owner,
anchor, middle-order or mismatch hypothesis is used.  Fixed-ray
expansion preserves both putative original witnesses at every source
radius in the full interval.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.GlobalEH

open Candidate FramePair QuarterWordGeometry GlobalOuterAnchor GlobalQuarterSign

theorem four_edge_return (C : BoundaryCycle Q0) (F : QuarterLift C) :
    frameCost |F.theta A-F.theta E|≤
      frameCost |difference F A|+frameCost |difference F B|+
      frameCost |difference F T|+frameCost |difference F D| := by
  have hrange (i j : Vertex) : |F.theta j-F.theta i|∈Icc 0 (Real.pi/4) := by
    refine ⟨abs_nonneg _,?_⟩
    linarith [theta_spread F i j,Real.pi_gt_three]
  have hAT := frameCost_triangle (hrange A B) (hrange B T) (hrange A T)
    ((abs_sub_le (F.theta T) (F.theta B) (F.theta A)).trans_eq (add_comm _ _))
  have hAD := frameCost_triangle (hrange A T) (hrange T D) (hrange A D)
    ((abs_sub_le (F.theta D) (F.theta T) (F.theta A)).trans_eq (add_comm _ _))
  have hAE := frameCost_triangle (hrange A D) (hrange D E) (hrange A E)
    ((abs_sub_le (F.theta E) (F.theta D) (F.theta A)).trans_eq (add_comm _ _))
  have hsum : frameCost |F.theta E-F.theta A|≤
      frameCost |F.theta B-F.theta A|+frameCost |F.theta T-F.theta B|+
      frameCost |F.theta D-F.theta T|+frameCost |F.theta E-F.theta D| := by linarith
  have hA : difference F A=F.theta B-F.theta A := by
    simp only [difference,show next A=B by decide]
  have hB : difference F B=F.theta T-F.theta B := by
    simp only [difference,show next B=T by decide]
  have hT : difference F T=F.theta D-F.theta T := by
    simp only [difference,show next T=D by decide]
  have hD : difference F D=F.theta E-F.theta D := by
    simp only [difference,show next D=E by decide]
  rw [hA,hB,hT,hD,abs_sub_comm (F.theta A) (F.theta E)]
  exact hsum

theorem ceiling_high_low_false (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hquarter : F.quarter=offsets)
    (jE jG : Fin 4) (hEowner : jE=2 ∨ jE=3) (hGowner : jG=0 ∨ jG=1)
    (hEH : (forwardAxis jE).Feasible (C.square E) (C.square H))
    (hGA : (forwardAxis jG).Feasible (C.square G) (C.square A)) : False := by
  let hgap : ∀i,19/25<angleGap C.beta i := boundary_gap_lower C le_rfl
  have hinc (i : Vertex) : integerQuarterIncrement F.quarter i=word i := by
    rw [hquarter,GlobalZeroSign.offset_increment]
  have hiE : integerQuarterIncrement F.quarter E=1 := by simpa [word,E] using hinc E
  have hiH : integerQuarterIncrement F.quarter H=0 := by simpa [word,H] using hinc H
  have hiG : integerQuarterIncrement F.quarter G=1 := by simpa [word,G] using hinc G
  have hEsign := GlobalQuarterSign.ceiling_source_negative C F E hiE jE hEowner
    (by simpa [E,H,next] using hEH)
  have hHsign := GlobalZeroLow.ceiling_zero_low_source_positive C F H hiH
    (by simpa [H,G,next] using hiG) jG hGowner (by simpa [H,G,A,next] using hGA)
  have hGsign : C.tangent G<0 := by
    simpa [E,H,G,next] using GlobalZeroLow.ceiling_high_zero_target_negative C F E hiE
      (by simpa [E,H,next] using hiH) jE hEowner (by simpa [E,H,next] using hEH)
  have hAsign : 0<C.tangent A := by
    simpa [G,A,next] using GlobalQuarterSign.ceiling_target_positive C F G hiG jG hGowner
      (by simpa [G,A,next] using hGA)
  have he : transverse (stateOf C E)≤0 := by
    have hh := (div_lt_iff₀ (C.a_pos E)).1 hEsign
    simpa only [transverse,stateOf,signOf_spec,mul_zero,zero_mul] using hh.le
  have hh : 0≤transverse (stateOf C H) := by
    have hh := (lt_div_iff₀ (C.a_pos H)).1 hHsign
    simpa only [transverse,stateOf,signOf_spec,mul_zero,zero_mul] using hh.le
  have hg : transverse (stateOf C G)≤0 := by
    have hh := (div_lt_iff₀ (C.a_pos G)).1 hGsign
    simpa only [transverse,stateOf,signOf_spec,mul_zero,zero_mul] using hh.le
  have ha : 0≤transverse (stateOf C A) := by
    have hh := (lt_div_iff₀ (C.a_pos A)).1 hAsign
    simpa only [transverse,stateOf,signOf_spec,mul_zero,zero_mul] using hh.le
  obtain ⟨jZ,hjZ⟩ := boundary_forward_complete C le_rfl H (C.selected H) (C.feasible H)
  have hHG : (forwardAxis jZ).Feasible (C.square H) (C.square (next H)) := by
    simpa only [hjZ] using C.feasible H
  have hZowner := GlobalZeroSign.secondary C (by norm_num [Q0]) F H hiH jZ hHG
  have hphaseE : pairAngle C E=Real.pi/2+difference F E := by
    simpa [hiE,add_comm] using pair_angle_increment C F hgap E
  have hphaseH : pairAngle C H=difference F H := by
    simpa [hiH] using pair_angle_increment C F hgap H
  have hphaseG : pairAngle C G=Real.pi/2+difference F G := by
    simpa [hiG,add_comm] using pair_angle_increment C F hgap G
  have hpairE : (stateOf C E).Feasible (stateOf C H) jE (Real.pi/2+difference F E) := by
    have hp := stateOf_feasible C E jE (by simpa [E,H,next] using hEH)
    rw [hphaseE] at hp
    simpa [E,H,next] using hp
  have hpairH : (stateOf C H).Feasible (stateOf C G) jZ (difference F H) := by
    have hp := stateOf_feasible C H jZ hHG
    rw [hphaseH] at hp
    simpa [H,G,next] using hp
  have hpairG : (stateOf C G).Feasible (stateOf C A) jG (Real.pi/2+difference F G) := by
    have hp := stateOf_feasible C G jG (by simpa [G,A,next] using hGA)
    rw [hphaseG] at hp
    simpa [G,A,next] using hp
  have hnE : next E=H := by decide
  have hnH : next H=G := by decide
  have hnG : next G=A := by decide
  have hEHsum : difference F E+difference F H=F.theta G-F.theta E := by
    simp only [difference,hnE,hnH]
    ring
  have hHGsum : difference F H+difference F G=F.theta A-F.theta H := by
    simp only [difference,hnH,hnG]
    ring
  have hsum : difference F E+difference F H+difference F G=F.theta A-F.theta E := by
    simp only [difference,hnE,hnH,hnG]
    ring
  have hpath := original_path_charge (stateOf C E) (stateOf C H) (stateOf C G) (stateOf C A)
    (by simpa only [frameCap] using (difference_small F E).le)
    (by simpa only [frameCap] using (difference_small F H).le)
    (by simpa only [frameCap] using (difference_small F G).le)
    (by rw [hEHsum]; simpa only [frameCap] using (theta_spread F E G).le)
    (by rw [hHGsum]; simpa only [frameCap] using (theta_spread F H A).le)
    (by rw [hsum]; simpa only [frameCap] using (theta_spread F E A).le)
    he hh hg ha jE jZ jG hEowner hZowner hGowner hpairE hpairH hpairG
  let cost : Vertex→ℝ := fun i => phaseValue F hgap i+
    (stateOf C i).signedLabel-(stateOf C (next i)).signedLabel
  have hpair (i : Vertex) : (8833/10000:ℝ)+(9/50)*frameCost |difference F i|<cost i := by
    have hp := (ZeroPrimary.handGamma_lower (branchOf C i).type
      (branchOf C (next i)).type).trans_lt (FrameAllPairs.all_pair C i)
    rw [ZeroPrimary.frame_pair_cost C F hgap i] at hp
    dsimp [cost]
    linarith
  have hphaseE' : phaseValue F hgap E=Real.pi/2+difference F E := by
    linarith [phase_gap C F hgap E,pairAngle_gap C E]
  have hphaseH' : phaseValue F hgap H=difference F H := by
    linarith [phase_gap C F hgap H,pairAngle_gap C H]
  have hphaseG' : phaseValue F hgap G=Real.pi/2+difference F G := by
    linarith [phase_gap C F hgap G,pairAngle_gap C G]
  have hcharge : cost E+cost H+cost G=
      pathCharge (stateOf C E) (stateOf C A) (difference F E) (difference F H) (difference F G) := by
    dsimp only [cost,pathCharge]
    rw [hphaseE',hphaseH',hphaseG',hnE,hnH,hnG]
    have heLabel := signed_of_nonpos (stateOf C E) he
    have haLabel := signed_of_nonneg (stateOf C A) ha
    rw [heLabel,haLabel]
    ring
  have hbudget : (∑i,cost i)=2*Real.pi := marker_budget C F hgap
    (fun i => (stateOf C i).signedLabel)
  have hsplit : (∑i,cost i)=cost H+cost G+cost A+cost B+cost T+cost D+cost E := by
    rw [Fin.sum_univ_seven]
    rfl
  rw [hsplit] at hbudget
  have hreturn := four_edge_return C F
  rw [← hsum] at hreturn
  have hA := hpair A
  have hB := hpair B
  have hT := hpair T
  have hD := hpair D
  linarith [Arithmetic.two_pi_lt_710_over_113]

theorem original_high_low_false {q : ℝ} (C : BoundaryCycle q)
    (hq : q∈Icc (5/2:ℝ) Q0) (F : QuarterLift C) (hquarter : F.quarter=offsets)
    (jE jG : Fin 4) (hEowner : jE=2 ∨ jE=3) (hGowner : jG=0 ∨ jG=1)
    (hEH : (forwardAxis jE).Feasible (C.square E) (C.square H))
    (hGA : (forwardAxis jG).Feasible (C.square G) (C.square A)) : False := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G' : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  apply ceiling_high_low_false D G' hquarter jE jG hEowner hGowner
  · have hh := hR.preserves_all_axes E (forwardAxis jE) (by simpa [E,H,next] using hEH)
    simpa [E,H,next] using hh
  · have hh := hR.preserves_all_axes G (forwardAxis jG) (by simpa [G,A,next] using hGA)
    simpa [G,A,next] using hh

/-- The low GA premise is one actual witness.  The conclusion covers
every original EH axis separately, including all weak ties. -/
theorem frame_EH_low_of_GA_low {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (jG : Fin 4) (hGowner : jG=0 ∨ jG=1)
    (hGA : (forwardAxis jG).Feasible (C.square G) (C.square A))
    (jE : Fin 4) (hEH : (forwardAxis jE).Feasible (C.square E) (C.square H)) :
    jE=0 ∨ jE=1 := by
  by_contra hbad
  have hEowner : jE=2 ∨ jE=3 := by fin_cases jE <;> simp_all
  obtain ⟨G',hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro k; simpa only [mul_div_assoc] using F.canonical_eq k)
  exact original_high_low_false C hq G' hGquarter jE jG hEowner hGowner hEH hGA

end SquaresInCircles.Eight.GlobalEH
