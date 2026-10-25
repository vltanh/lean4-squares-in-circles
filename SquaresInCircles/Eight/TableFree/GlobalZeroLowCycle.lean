module

public import SquaresInCircles.Eight.TableFree.GlobalZeroLowSupport
public import SquaresInCircles.Eight.TableFree.GlobalOuterAnchorCycle

/-!
# Global sign propagation through an original zero--quarter pair

Every low quarter after a zero forces the source of that zero to be
strictly positive.  The reflected original path gives the negative
target after a high quarter and a zero.  Five unchanged G1 edges close
both contradictions.  Radius expansion is used only inside the proof
and preserves every original weak witness and signed tangent.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.TableFree.GlobalZeroLow

open FramePair TableFreeWordGeometry GlobalOuterAnchor GlobalQuarterSign

theorem two_edge_charge_lt (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex) :
    phaseValue F hgap i+phaseValue F hgap (next i)+
      (stateOf C i).signedLabel-(stateOf C (next (next i))).signedLabel<19/10 := by
  let g : Vertex→ℝ := fun j => phaseValue F hgap j+
    (stateOf C j).signedLabel-(stateOf C (next j)).signedLabel
  have hpair (j : Vertex) : (8833/10000:ℝ)<g j := by
    have hh := (ZeroPrimary.handGamma_lower (branchOf C j).type
      (branchOf C (next j)).type).trans_lt (FrameAllPairs.all_pair C j)
    rw [ZeroPrimary.frame_pair_cost C F hgap j] at hh
    have hf := frame_abs_nonneg
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
  have hresult : g i+g (next i)<19/10 := by
    linarith [Arithmetic.two_pi_lt_710_over_113]
  dsimp [g] at hresult
  linarith

private theorem original_secondary (C : BoundaryCycle Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0) :
    ∃j : Fin 4,(j=0 ∨ j=2) ∧
      (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [hj] using C.feasible i
  exact ⟨j,GlobalZeroSign.secondary C (by norm_num [Q0]) F i hi j haxis,haxis⟩

theorem ceiling_zero_low_source_positive (C : BoundaryCycle Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0)
    (hj : integerQuarterIncrement F.quarter (next i)=1)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square (next i)) (C.square (next (next i)))) :
    0<C.tangent i := by
  by_contra! hbad
  let hgap : ∀k,19/25<angleGap C.beta k := boundary_gap_lower C le_rfl
  obtain ⟨k,hk,hzero⟩ := original_secondary C F i hi
  have hzero2 : (forwardAxis 2).Feasible (C.square i) (C.square (next i)) := by
    rcases hk with rfl | rfl
    · have hh := GlobalZeroSign.ceiling_source_positive C F i hi hzero
      exact (not_lt_of_ge hbad hh).elim
    · exact hzero
  have hcneg := GlobalZeroSign.ceiling_target_negative C F i hi hzero2
  have htpos := GlobalQuarterSign.ceiling_target_positive C F (next i) hj j howner haxis
  have hs : transverse (stateOf C i)≤0 := by
    have hh := (div_le_iff₀ (C.a_pos i)).1 hbad
    simpa only [transverse,stateOf,signOf_spec,mul_zero,zero_mul] using hh
  have hc : transverse (stateOf C (next i))≤0 := by
    have hh := (div_lt_iff₀ (C.a_pos (next i))).1 hcneg
    simpa only [transverse,stateOf,signOf_spec,mul_zero,zero_mul] using hh.le
  have ht : 0≤transverse (stateOf C (next (next i))) := by
    have hh := (lt_div_iff₀ (C.a_pos (next (next i)))).1 htpos
    simpa only [transverse,stateOf,signOf_spec,mul_zero,zero_mul] using hh.le
  have hphaseL : pairAngle C i=difference F i := by
    simpa [hi] using pair_angle_increment C F hgap i
  have hphaseR : pairAngle C (next i)=Real.pi/2+difference F (next i) := by
    simpa [hj,add_comm] using pair_angle_increment C F hgap (next i)
  have hmZ := stateOf_feasible C i 2 hzero2
  have hmQ := stateOf_feasible C (next i) j haxis
  rw [hphaseL] at hmZ
  rw [hphaseR] at hmQ
  have hcharge := path_charge (stateOf C i) (stateOf C (next i))
    (stateOf C (next (next i)))
    (by simpa only [frameCap] using (difference_small F i).le)
    (by simpa only [frameCap] using (difference_small F (next i)).le)
    (consecutive_difference_bound F i) hs hc ht hmZ j howner hmQ
  have hreturn := two_edge_charge_lt C F hgap i
  have hphase₁ : phaseValue F hgap i=difference F i := by
    linarith [phase_gap C F hgap i,pairAngle_gap C i]
  have hphase₂ : phaseValue F hgap (next i)=Real.pi/2+difference F (next i) := by
    linarith [phase_gap C F hgap (next i),pairAngle_gap C (next i)]
  rw [hphase₁,hphase₂,signed_of_nonpos _ hs,signed_of_nonneg _ ht] at hreturn
  dsimp [charge] at hcharge
  linarith

/-- The reflected path uses the original quarter and zero contacts in
reverse order.  It does not construct or classify a different cycle. -/
theorem ceiling_high_zero_target_negative (C : BoundaryCycle Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (hj : integerQuarterIncrement F.quarter (next i)=0)
    (j : Fin 4) (howner : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.tangent (next (next i))<0 := by
  by_contra! hbad
  let hgap : ∀k,19/25<angleGap C.beta k := boundary_gap_lower C le_rfl
  let s := stateOf C i
  let c := stateOf C (next i)
  let t := stateOf C (next (next i))
  obtain ⟨k,hk,hzero⟩ := original_secondary C F (next i) hj
  have hzero0 : (forwardAxis 0).Feasible (C.square (next i)) (C.square (next (next i))) := by
    rcases hk with rfl | rfl
    · exact hzero
    · have hh := GlobalZeroSign.ceiling_target_negative C F (next i) hj hzero
      exact (not_lt_of_ge hbad hh).elim
  have hcpos := GlobalZeroSign.ceiling_source_positive C F (next i) hj hzero0
  have hsneg := GlobalQuarterSign.ceiling_source_negative C F i hi j howner haxis
  have hs : transverse s≤0 := by
    have hh := (div_lt_iff₀ (C.a_pos i)).1 hsneg
    simpa only [s,transverse,stateOf,signOf_spec,mul_zero,zero_mul] using hh.le
  have hc : 0≤transverse c := by
    have hh := (lt_div_iff₀ (C.a_pos (next i))).1 hcpos
    simpa only [c,transverse,stateOf,signOf_spec,mul_zero,zero_mul] using hh.le
  have ht : 0≤transverse t := by
    have hh := (le_div_iff₀ (C.a_pos (next (next i)))).1 hbad
    simpa only [t,transverse,stateOf,signOf_spec,mul_zero,zero_mul] using hh
  have hsf : 0≤transverse s.flip := by
    simpa only [transverse,State.flip,sign_not,neg_mul] using neg_nonneg.mpr hs
  have hcf : transverse c.flip≤0 := by
    simpa only [transverse,State.flip,sign_not,neg_mul] using neg_nonpos.mpr hc
  have htf : transverse t.flip≤0 := by
    simpa only [transverse,State.flip,sign_not,neg_mul] using neg_nonpos.mpr ht
  have hphaseL : pairAngle C i=Real.pi/2+difference F i := by
    simpa [hi,add_comm] using pair_angle_increment C F hgap i
  have hphaseR : pairAngle C (next i)=difference F (next i) := by
    simpa [hj] using pair_angle_increment C F hgap (next i)
  have hmZ : c.Feasible t 0 (difference F (next i)) := by
    simpa only [hphaseR] using stateOf_feasible C (next i) 0 hzero0
  have hmQ : s.Feasible c j (Real.pi/2+difference F i) := by
    simpa only [hphaseL] using stateOf_feasible C i j haxis
  have hmZf : t.flip.Feasible c.flip 2 (difference F (next i)) := by
    apply (State.target_secondary_reverse t.flip c.flip (difference F (next i))).2
    simpa [State.flip] using hmZ
  obtain ⟨j',hj',hmQf⟩ : ∃j' : Fin 4,(j'=0 ∨ j'=1) ∧
      c.flip.Feasible s.flip j' (Real.pi/2+difference F i) := by
    rcases howner with rfl | rfl
    · exact ⟨0,Or.inl rfl,(State.target_secondary_reverse s c _).1 hmQ⟩
    · refine ⟨1,Or.inr rfl,?_⟩
      apply (State.target_primary_reverse c.flip s.flip _).2
      simpa [State.flip] using hmQ
  have hcharge := path_charge t.flip c.flip s.flip
    (by simpa only [frameCap] using (difference_small F (next i)).le)
    (by simpa only [frameCap] using (difference_small F i).le)
    (by simpa only [add_comm] using consecutive_difference_bound F i)
    htf hcf hsf hmZf j' hj' hmQf
  have hreturn := two_edge_charge_lt C F hgap i
  have hphase₁ : phaseValue F hgap i=Real.pi/2+difference F i := by
    linarith [phase_gap C F hgap i,pairAngle_gap C i]
  have hphase₂ : phaseValue F hgap (next i)=difference F (next i) := by
    linarith [phase_gap C F hgap (next i),pairAngle_gap C (next i)]
  have hlabelS : (stateOf C i).signedLabel= -ZeroPrimary.unsigned s := signed_of_nonpos s hs
  have hlabelT : (stateOf C (next (next i))).signedLabel=ZeroPrimary.unsigned t :=
    signed_of_nonneg t ht
  rw [hphase₁,hphase₂,hlabelS,hlabelT] at hreturn
  have hflipS : ZeroPrimary.unsigned s.flip=ZeroPrimary.unsigned s := rfl
  have hflipT : ZeroPrimary.unsigned t.flip=ZeroPrimary.unsigned t := rfl
  rw [charge,hflipS,hflipT] at hcharge
  linarith

theorem zero_low_source_positive {q : ℝ} (C : BoundaryCycle q)
    (hq : q∈Icc (5/2:ℝ) Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0)
    (hj : integerQuarterIncrement F.quarter (next i)=1)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square (next i)) (C.square (next (next i)))) :
    0<C.tangent i := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  have hh := ceiling_zero_low_source_positive D G i hi hj j howner
    (hR.preserves_all_axes (next i) (forwardAxis j) haxis)
  simpa only [hR.same_tangents] using hh

theorem high_zero_target_negative {q : ℝ} (C : BoundaryCycle q)
    (hq : q∈Icc (5/2:ℝ) Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (hj : integerQuarterIncrement F.quarter (next i)=0)
    (j : Fin 4) (howner : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.tangent (next (next i))<0 := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  have hh := ceiling_high_zero_target_negative D G i hi hj j howner
    (hR.preserves_all_axes i (forwardAxis j) haxis)
  simpa only [hR.same_tangents] using hh

end SquaresInCircles.Eight.TableFree.GlobalZeroLow
