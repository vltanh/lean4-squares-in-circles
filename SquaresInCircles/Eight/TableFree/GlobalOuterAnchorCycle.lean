module

public import SquaresInCircles.Eight.TableFree.GlobalOuterAnchorPath
public import SquaresInCircles.Eight.TableFree.GlobalQuarterSignCycle

/-!
# Original radial anchors beside the actual zero edges

A zero edge followed by an original high-quarter witness has an outer
common vertex.  Reflected reversal gives the corresponding result for
a low-quarter witness followed by a zero edge.  These two statements
cover all four anchors of the normal owner family.  The common marker,
physical axes, source radius and weak ties are retained throughout.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.TableFree.GlobalOuterAnchor

open FramePair TableFreeWordGeometry

theorem pair_angle_increment (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex) :
    pairAngle C i=difference F i+(integerQuarterIncrement F.quarter i:ℝ)*Real.pi/2 := by
  have hcast : ((F.word hgap pi_lt_22_over_7 i).val:ℝ)=
      (integerQuarterIncrement F.quarter i:ℝ) := by
    exact_mod_cast F.word_cast hgap pi_lt_22_over_7 i
  have hp : pairAngle C i=phaseValue F hgap i := by
    linarith [pairAngle_gap C i,phase_gap C F hgap i]
  simpa only [phaseValue,hcast] using hp

theorem consecutive_difference_bound {C : BoundaryCycle Q0} (F : QuarterLift C)
    (i : Vertex) : |difference F i+difference F (next i)|≤frameCap := by
  have he : difference F i+difference F (next i)=F.theta (next (next i))-F.theta i := by
    dsimp [difference]
    ring
  rw [he]
  simpa only [frameCap] using (theta_spread F i (next (next i))).le

/-- Five unchanged original G1 edges strictly bound the uncharged sum
on any two consecutive edges.  No return-frame payment is required. -/
theorem two_edge_charge_lt_two (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex) :
    phaseValue F hgap i+phaseValue F hgap (next i)+
      (stateOf C i).signedLabel-(stateOf C (next (next i))).signedLabel<2 := by
  let g : Vertex→ℝ := fun j => phaseValue F hgap j+
    (stateOf C j).signedLabel-(stateOf C (next j)).signedLabel
  have hpair (j : Vertex) : (8833/10000:ℝ)<g j := by
    have hh := (ZeroPrimary.handGamma_lower (branchOf C j).type
      (branchOf C (next j)).type).trans_lt (FrameAllPairs.all_pair C j)
    rw [ZeroPrimary.frame_pair_cost C F hgap j] at hh
    have hf := GlobalQuarterSign.frame_abs_nonneg
      (show |difference F j|≤frameCap by simpa only [frameCap] using (difference_small F j).le)
    dsimp [g]
    linarith
  have hne : next i≠i := by fin_cases i <;> decide
  have hsum := Finset.sum_lt_sum_of_nonempty
    (s := ((Finset.univ.erase i).erase (next i) : Finset Vertex))
    (by
      have hc : ((Finset.univ.erase i).erase (next i) : Finset Vertex).card=5 := by simp [hne]
      exact Finset.card_pos.1 (by omega))
    (fun j _ => hpair j)
  have hcost : (∑j,g j)=2*Real.pi := marker_budget C F hgap
    (fun j => (stateOf C j).signedLabel)
  have hsplit₁ := Finset.sum_erase_add (s := Finset.univ) (f := g) (Finset.mem_univ i)
  have hsplit₂ := Finset.sum_erase_add (s := Finset.univ.erase i) (f := g)
    (show next i∈(Finset.univ.erase i : Finset Vertex) by simp [hne])
  rw [hcost] at hsplit₁
  norm_num [hne] at hsum
  have hresult : g i+g (next i)<2 := by
    linarith [Arithmetic.two_pi_lt_710_over_113]
  dsimp [g] at hresult
  linarith

private theorem original_zero_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0) :
    ∃p : Bool,(forwardAxis (leftOwner p)).Feasible (C.square i) (C.square (next i)) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [hj] using C.feasible i
  have hs := GlobalZeroSign.secondary C (by norm_num [Q0]) F i hi j haxis
  rcases hs with rfl | rfl
  · exact ⟨false,haxis⟩
  · exact ⟨true,haxis⟩

theorem ceiling_zero_high_outer (C : BoundaryCycle Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0)
    (hj : integerQuarterIncrement F.quarter (next i)=1)
    (j : Fin 4) (howner : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square (next i)) (C.square (next (next i)))) :
    C.kind (next i)=.outer := by
  by_contra hcore
  let hgap : ∀k,19/25<angleGap C.beta k := boundary_gap_lower C le_rfl
  have hc : (stateOf C (next i)).branch.type=0 := (branchOf_core_iff C (next i)).2 hcore
  have hnegative := GlobalQuarterSign.ceiling_source_negative C F (next i) hj j howner haxis
  have htrans : transverse (stateOf C (next i))≤0 := by
    have hy := (div_lt_iff₀ (C.a_pos (next i))).1 hnegative
    simp only [mul_zero] at hy
    simpa only [transverse,stateOf,signOf_spec] using hy.le
  obtain ⟨p,hp⟩ := original_zero_owner C F i hi
  obtain ⟨q,hq⟩ : ∃q : Bool,rightOwner q=j := by
    rcases howner with rfl | rfl
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩
  have hphaseL : pairAngle C i=difference F i := by
    simpa only [hi,Int.cast_zero,zero_mul,zero_div,add_zero] using pair_angle_increment C F hgap i
  have hphaseR : pairAngle C (next i)=Real.pi/2+difference F (next i) := by
    simpa [hj,add_comm] using pair_angle_increment C F hgap (next i)
  have hl := stateOf_feasible C i (leftOwner p) hp
  have hr := stateOf_feasible C (next i) j haxis
  rw [hphaseL] at hl
  rw [hphaseR,← hq] at hr
  have hcharge := core_path_charge (stateOf C i) (stateOf C (next i))
    (stateOf C (next (next i))) p q hc htrans
    (by simpa only [frameCap] using (difference_small F i).le)
    (by simpa only [frameCap] using (difference_small F (next i)).le)
    (consecutive_difference_bound F i) hl hr
  have hreturn := two_edge_charge_lt_two C F hgap i
  have hphase₁ : phaseValue F hgap i=difference F i := by
    linarith [phase_gap C F hgap i,pairAngle_gap C i]
  have hphase₂ : phaseValue F hgap (next i)=Real.pi/2+difference F (next i) := by
    linarith [phase_gap C F hgap (next i),pairAngle_gap C (next i)]
  rw [hphase₁,hphase₂] at hreturn
  linarith

/-- Reflected reversal is applied to the retained two-edge formulas;
no different global cycle or new separator is introduced. -/
theorem ceiling_low_zero_outer (C : BoundaryCycle Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (hj : integerQuarterIncrement F.quarter (next i)=0)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind (next i)=.outer := by
  by_contra hcore
  let hgap : ∀k,19/25<angleGap C.beta k := boundary_gap_lower C le_rfl
  let s := stateOf C i
  let c := stateOf C (next i)
  let t := stateOf C (next (next i))
  have hc : c.flip.branch.type=0 := (branchOf_core_iff C (next i)).2 hcore
  have hpositive := GlobalQuarterSign.ceiling_target_positive C F i hi j howner haxis
  have htrans : transverse c.flip≤0 := by
    have hy := (lt_div_iff₀ (C.a_pos (next i))).1 hpositive
    simp only [zero_mul] at hy
    have ht : 0≤transverse c := by
      simpa only [c,transverse,stateOf,signOf_spec] using hy.le
    simpa only [transverse,State.flip,sign_not,neg_mul] using neg_nonpos.mpr ht
  have hphaseL : pairAngle C i=Real.pi/2+difference F i := by
    simpa [hi,add_comm] using pair_angle_increment C F hgap i
  have hphaseR : pairAngle C (next i)=difference F (next i) := by
    simpa only [hj,Int.cast_zero,zero_mul,zero_div,add_zero] using pair_angle_increment C F hgap (next i)
  obtain ⟨p,hp⟩ := original_zero_owner C F (next i) hj
  have hzero : c.Feasible t (leftOwner p) (difference F (next i)) := by
    have hh := stateOf_feasible C (next i) (leftOwner p) hp
    simpa only [hphaseR] using hh
  have hquarter : s.Feasible c j (Real.pi/2+difference F i) := by
    have hh := stateOf_feasible C i j haxis
    simpa only [hphaseL] using hh
  obtain ⟨p',hp'⟩ : ∃p' : Bool,t.flip.Feasible c.flip (leftOwner p') (difference F (next i)) := by
    cases p
    · refine ⟨true,?_⟩
      apply (State.target_secondary_reverse t.flip c.flip (difference F (next i))).2
      simpa [State.flip,leftOwner] using hzero
    · exact ⟨false,(State.target_secondary_reverse c t (difference F (next i))).1 hzero⟩
  obtain ⟨q,hq⟩ : ∃q : Bool,c.flip.Feasible s.flip (rightOwner q) (Real.pi/2+difference F i) := by
    rcases howner with rfl | rfl
    · refine ⟨false,?_⟩
      apply (State.target_secondary_reverse c.flip s.flip (Real.pi/2+difference F i)).2
      simpa [State.flip] using hquarter
    · exact ⟨true,(State.target_primary_reverse s c (Real.pi/2+difference F i)).1 hquarter⟩
  have hcharge := core_path_charge t.flip c.flip s.flip p' q hc htrans
    (by simpa only [frameCap] using (difference_small F (next i)).le)
    (by simpa only [frameCap] using (difference_small F i).le)
    (by simpa only [add_comm] using consecutive_difference_bound F i) hp' hq
  have hreturn := two_edge_charge_lt_two C F hgap i
  have hphase₁ : phaseValue F hgap i=Real.pi/2+difference F i := by
    linarith [phase_gap C F hgap i,pairAngle_gap C i]
  have hphase₂ : phaseValue F hgap (next i)=difference F (next i) := by
    linarith [phase_gap C F hgap (next i),pairAngle_gap C (next i)]
  rw [hphase₁,hphase₂] at hreturn
  simp only [State.flip_label] at hcharge
  dsimp [s,t] at hcharge
  linarith

theorem zero_high_outer {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0)
    (hj : integerQuarterIncrement F.quarter (next i)=1)
    (j : Fin 4) (howner : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square (next i)) (C.square (next (next i)))) :
    C.kind (next i)=.outer := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  have hh := ceiling_zero_high_outer D G i hi hj j howner
    (hR.preserves_all_axes (next i) (forwardAxis j) haxis)
  simpa only [hR.same_kind] using hh

theorem low_zero_outer {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (hj : integerQuarterIncrement F.quarter (next i)=0)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind (next i)=.outer := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  have hh := ceiling_low_zero_outer D G i hi hj j howner
    (hR.preserves_all_axes i (forwardAxis j) haxis)
  simpa only [hR.same_kind] using hh

end SquaresInCircles.Eight.TableFree.GlobalOuterAnchor
