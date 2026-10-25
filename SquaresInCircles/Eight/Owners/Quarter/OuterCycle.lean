module

public import SquaresInCircles.Eight.Owners.Quarter.OuterPath
public import SquaresInCircles.Eight.Owners.Zero.LowCycle

/-!
# Eight squares: the complementary radial anchors beside a zero edge

A low quarter after a zero edge has an outer target (`zero_low_outer`), and reflection of the
two-edge formulas gives an outer source for a high quarter before a zero edge (`high_zero_outer`);
the latter includes the anchor E in the all-high branch. Both results hold at every radius in
`[5/2, Q0]`, for each feasible weak axis.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalQuarterOuter

open FramePair QuarterWordGeometry GlobalOuterAnchor GlobalQuarterSign

theorem ceiling_zero_low_outer (C : BoundaryCycle Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0)
    (hj : integerQuarterIncrement F.quarter (next i)=1)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square (next i)) (C.square (next (next i)))) :
    C.kind (next (next i))=.outer := by
  by_contra hcore
  let hgap : ∀k,19/25<angleGap C.beta k := boundary_gap_lower C le_rfl
  have hspos := GlobalZeroLow.ceiling_zero_low_source_positive C F i hi hj j howner haxis
  have htpos := GlobalQuarterSign.ceiling_target_positive C F (next i) hj j howner haxis
  have hs : 0≤transverse (stateOf C i) := by
    have hh := (lt_div_iff₀ (C.a_pos i)).1 hspos
    simpa only [transverse,stateOf,signOf_spec,zero_mul,mul_zero] using hh.le
  have ht : 0≤transverse (stateOf C (next (next i))) := by
    have hh := (lt_div_iff₀ (C.a_pos (next (next i)))).1 htpos
    simpa only [transverse,stateOf,signOf_spec,zero_mul,mul_zero] using hh.le
  have hc : (stateOf C (next (next i))).branch.type=0 :=
    (branchOf_core_iff C (next (next i))).2 hcore
  obtain ⟨z,hz⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have hzero : (forwardAxis z).Feasible (C.square i) (C.square (next i)) := by
    simpa only [hz] using C.feasible i
  have hzeroOwner := GlobalZeroSign.secondary C (by norm_num [Q0]) F i hi z hzero
  have hcancel : z=2 → transverse (stateOf C (next i))≤0 := by
    intro hz2
    have hh := GlobalZeroSign.ceiling_target_negative C F i hi (by simpa only [hz2] using hzero)
    have hh' := (div_lt_iff₀ (C.a_pos (next i))).1 hh
    simpa only [transverse,stateOf,signOf_spec,zero_mul,mul_zero] using hh'.le
  have hphaseL : pairAngle C i=difference F i := by
    simpa [hi] using pair_angle_increment C F hgap i
  have hphaseR : pairAngle C (next i)=Real.pi/2+difference F (next i) := by
    simpa [hj,add_comm] using pair_angle_increment C F hgap (next i)
  have hmZ := stateOf_feasible C i z hzero
  have hmQ := stateOf_feasible C (next i) j haxis
  rw [hphaseL] at hmZ
  rw [hphaseR] at hmQ
  have hcharge := core_target_path_charge (stateOf C i) (stateOf C (next i))
    (stateOf C (next (next i))) hc
    (by simpa only [frameCap] using (difference_small F i).le)
    (by simpa only [frameCap] using (difference_small F (next i)).le)
    hs ht z j hzeroOwner howner hmZ hmQ hcancel
  have hreturn := GlobalZeroLow.two_edge_charge_lt C F hgap i
  have hphase₁ : phaseValue F hgap i=difference F i := by
    linarith [phase_gap C F hgap i,pairAngle_gap C i]
  have hphase₂ : phaseValue F hgap (next i)=Real.pi/2+difference F (next i) := by
    linarith [phase_gap C F hgap (next i),pairAngle_gap C (next i)]
  rw [hphase₁,hphase₂] at hreturn
  linarith

/-- At `Q0`, a high quarter before a zero edge has an outer source; reflection preserves the error
and the marker charge, and carries the zero-sign implication with its owner. -/
theorem ceiling_high_zero_outer (C : BoundaryCycle Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (hj : integerQuarterIncrement F.quarter (next i)=0)
    (j : Fin 4) (howner : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind i=.outer := by
  by_contra hcore
  let hgap : ∀k,19/25<angleGap C.beta k := boundary_gap_lower C le_rfl
  let s := stateOf C i
  let c := stateOf C (next i)
  let t := stateOf C (next (next i))
  have hsneg := GlobalQuarterSign.ceiling_source_negative C F i hi j howner haxis
  have htneg := GlobalZeroLow.ceiling_high_zero_target_negative C F i hi hj j howner haxis
  have hs : 0≤transverse s.flip := by
    have hh := (div_lt_iff₀ (C.a_pos i)).1 hsneg
    have hh' : transverse s≤0 := by
      simpa only [s,transverse,stateOf,signOf_spec,zero_mul,mul_zero] using hh.le
    simpa only [transverse,State.flip,sign_not,neg_mul] using neg_nonneg.mpr hh'
  have ht : 0≤transverse t.flip := by
    have hh := (div_lt_iff₀ (C.a_pos (next (next i)))).1 htneg
    have hh' : transverse t≤0 := by
      simpa only [t,transverse,stateOf,signOf_spec,zero_mul,mul_zero] using hh.le
    simpa only [transverse,State.flip,sign_not,neg_mul] using neg_nonneg.mpr hh'
  have hc : s.flip.branch.type=0 := (branchOf_core_iff C i).2 hcore
  have hphaseL : pairAngle C i=Real.pi/2+difference F i := by
    simpa [hi,add_comm] using pair_angle_increment C F hgap i
  have hphaseR : pairAngle C (next i)=difference F (next i) := by
    simpa [hj] using pair_angle_increment C F hgap (next i)
  have hmQ : s.Feasible c j (Real.pi/2+difference F i) := by
    have hh := stateOf_feasible C i j haxis
    simpa only [hphaseL] using hh
  obtain ⟨z,hz⟩ := boundary_forward_complete C le_rfl (next i)
    (C.selected (next i)) (C.feasible (next i))
  have hzero : (forwardAxis z).Feasible (C.square (next i)) (C.square (next (next i))) := by
    simpa only [hz] using C.feasible (next i)
  have hmZ : c.Feasible t z (difference F (next i)) := by
    have hh := stateOf_feasible C (next i) z hzero
    simpa only [hphaseR] using hh
  have hzeroClass := GlobalZeroSign.classify C (by norm_num [Q0]) F (next i) hj z hzero
  obtain ⟨z',hzOwner,hzAxis,hzCancel⟩ : ∃z' : Fin 4,(z'=0 ∨ z'=2) ∧
      t.flip.Feasible c.flip z' (difference F (next i)) ∧
      (z'=2 → transverse c.flip≤0) := by
    rcases hzeroClass with ⟨hz0,hcpos⟩ | ⟨hz2,_⟩
    · refine ⟨2,Or.inr rfl,?_,?_⟩
      · apply (State.target_secondary_reverse t.flip c.flip (difference F (next i))).2
        simpa [State.flip,hz0] using hmZ
      · intro _
        have hh := (lt_div_iff₀ (C.a_pos (next i))).1 hcpos
        have hh' : 0≤transverse c := by
          simpa only [c,transverse,stateOf,signOf_spec,zero_mul,mul_zero] using hh.le
        simpa only [transverse,State.flip,sign_not,neg_mul] using neg_nonpos.mpr hh'
    · refine ⟨0,Or.inl rfl,?_,by intro hh; norm_num at hh⟩
      apply (State.target_secondary_reverse c t (difference F (next i))).1
      simpa only [hz2] using hmZ
  obtain ⟨q,hqOwner,hqAxis⟩ : ∃q : Fin 4,(q=0 ∨ q=1) ∧
      c.flip.Feasible s.flip q (Real.pi/2+difference F i) := by
    rcases howner with rfl | rfl
    · exact ⟨0,Or.inl rfl,(State.target_secondary_reverse s c _).1 hmQ⟩
    · refine ⟨1,Or.inr rfl,?_⟩
      apply (State.target_primary_reverse c.flip s.flip _).2
      simpa [State.flip] using hmQ
  have hcharge := core_target_path_charge t.flip c.flip s.flip hc
    (by simpa only [frameCap] using (difference_small F (next i)).le)
    (by simpa only [frameCap] using (difference_small F i).le)
    ht hs z' q hzOwner hqOwner hzAxis hqAxis hzCancel
  have hreturn := GlobalZeroLow.two_edge_charge_lt C F hgap i
  have hphase₁ : phaseValue F hgap i=Real.pi/2+difference F i := by
    linarith [phase_gap C F hgap i,pairAngle_gap C i]
  have hphase₂ : phaseValue F hgap (next i)=difference F (next i) := by
    linarith [phase_gap C F hgap (next i),pairAngle_gap C (next i)]
  rw [hphase₁,hphase₂] at hreturn
  simp only [State.flip_label] at hcharge
  dsimp [s,t] at hcharge
  linarith

theorem zero_low_outer {q : ℝ} (C : BoundaryCycle q)
    (hq : q∈Icc (5/2:ℝ) Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0)
    (hj : integerQuarterIncrement F.quarter (next i)=1)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square (next i)) (C.square (next (next i)))) :
    C.kind (next (next i))=.outer := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  have hh := ceiling_zero_low_outer D G i hi hj j howner
    (hR.preserves_all_axes (next i) (forwardAxis j) haxis)
  simpa only [hR.same_kind] using hh

theorem high_zero_outer {q : ℝ} (C : BoundaryCycle q)
    (hq : q∈Icc (5/2:ℝ) Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (hj : integerQuarterIncrement F.quarter (next i)=0)
    (j : Fin 4) (howner : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind i=.outer := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  have hh := ceiling_high_zero_outer D G i hi hj j howner
    (hR.preserves_all_axes i (forwardAxis j) haxis)
  simpa only [hR.same_kind] using hh

end SquaresInCircles.Eight.GlobalQuarterOuter
