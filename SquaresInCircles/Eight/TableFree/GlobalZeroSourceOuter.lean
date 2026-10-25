module

public import SquaresInCircles.Eight.TableFree.GlobalOuterAnchorBridge

/-!
# Every original nonpositive zero source is outer

One original target-secondary zero projection suffices.  A putative
core source would have error above `.4`, target transverse coordinate
above `.82`, and source transverse coordinate below `.1`.  Its actual
core marker and the common target marker then give charge above
`2493/2500`, contradicting the six unchanged original G1 edges.

No neighboring quarter owner, sign, frame order, mismatch bound or
source radial substitution is used.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.TableFree.GlobalZeroSourceOuter

open FramePair ZeroPrimary GlobalZeroSign GlobalQuarterSign GlobalOuterAnchor
open TableFreeWordGeometry

theorem core_small_marker (s : State) (hs : s.branch.type=0) (hb : s.b<1/2) :
    unsigned s≤(27/25)*s.b := by
  have ha := (FrameCoreArc.label_side (FrameCoreArc.state_core_chart s hs) hb).1
  cases hbr : s.branch <;> simp [hbr,Branch.type] at hs
  all_goals
    dsimp [unsigned]
    rw [hbr]
    dsimp [FramePair.label]
    rw [ha]
    nlinarith [s.b_nonneg]

theorem core_source_domain (s t : State) {d : ℝ}
    (hcore : s.branch.type=0) (hd : |d|≤frameCap)
    (hs : transverse s≤0) (ht : transverse t≤0)
    (haxis : s.Feasible t 2 d) :
    (2/5:ℝ)<d ∧ (41/50:ℝ)<t.b ∧ s.b<1/10 := by
  have ha := (core_bounds s hcore).1
  have htarget := (coordinates t).2.2.2.2
  have hm : GlobalOuterAnchor.width d≤ s.a*Real.sin d-s.b*Real.cos d+t.b := by
    have hh := (left_margin s t true hd ht).1 haxis
    dsimp [leftProjection] at hh
    have hsy : transverse s= -s.b := transverse_nonpos_eq s hs
    rw [hsy,neg_mul,← sub_eq_add_neg] at hh
    exact hh
  have hcos : 0≤Real.cos d := by linarith [(signed_trig hd).1]
  have hbc : 0≤ s.b*Real.cos d := mul_nonneg s.b_nonneg hcos
  have hdpos : 0<d := by
    by_contra! hn
    have hsin := sine_nonpos hd hn
    have hprod := mul_nonpos_of_nonneg_of_nonpos s.a_pos.le hsin
    linarith [width_ge_one hd]
  have hd' : d∈Icc 0 frameCap := ⟨hdpos.le,(le_abs_self d).trans hd⟩
  have tr := transport_trig hd'
  have hsin : Real.sin d<13/20 := by linarith [tr.2.2.2.1]
  have hcos' : 19/25<Real.cos d := by linarith [tr.1]
  have hprod := mul_le_mul_of_nonneg_right ha tr.2.2.1
  have hbasic : 1/2+Real.cos d/2-Real.sin d/12+s.b*Real.cos d≤t.b := by
    dsimp [GlobalOuterAnchor.width] at hm
    rw [abs_of_nonneg tr.2.2.1] at hm
    nlinarith only [hm,hprod]
  have hlarge : (2/5:ℝ)<d := by
    by_contra! hn
    have hd2 := pow_le_pow_left₀ hdpos.le hn 2
    have hc := Real.one_sub_sq_div_two_le_cos (x := d)
    have hsine := Real.sin_le hdpos.le
    norm_num at hd2
    nlinarith only [hbasic,htarget,hbc,hd2,hc,hsine,hn]
  have htarget' : (41/50:ℝ)<t.b := by
    linarith only [hbasic,hcos',hsin,hbc]
  have hsmall : s.b<1/10 := by
    by_contra! hb
    have hprod := mul_le_mul_of_nonneg_right hb hcos
    nlinarith only [hbasic,htarget,hprod,hcos',hsin]
  exact ⟨hlarge,htarget',hsmall⟩

theorem core_source_charge (s t : State) {d : ℝ}
    (hcore : s.branch.type=0) (hd : |d|≤frameCap)
    (hs : transverse s≤0) (ht : transverse t≤0)
    (haxis : s.Feasible t 2 d) :
    (2493/2500:ℝ)<d+s.signedLabel-t.signedLabel := by
  obtain ⟨hlarge,htarget,hsmall⟩ := core_source_domain s t hcore hd hs ht haxis
  have hsource := core_small_marker s hcore (by linarith)
  have htargetMarker := GlobalOuterAnchor.marker_lower t
  rw [signed_of_nonpos s hs,signed_of_nonpos t ht]
  dsimp [k] at htargetMarker
  nlinarith only [hlarge,htarget,hsmall,hsource,htargetMarker]

theorem closed_charge_impossible (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hcharge : (2493/2500:ℝ)<phaseValue F hgap i+
      (stateOf C i).signedLabel-(stateOf C (next i)).signedLabel) : False := by
  let g : Vertex→ℝ := fun j => phaseValue F hgap j+
    (stateOf C j).signedLabel-(stateOf C (next j)).signedLabel
  have hother (j : Vertex) : (8833/10000:ℝ)<g j := by
    have hh := (ZeroPrimary.handGamma_lower (branchOf C j).type
      (branchOf C (next j)).type).trans_lt (FrameAllPairs.all_pair C j)
    rw [ZeroPrimary.frame_pair_cost C F hgap j] at hh
    have hnonneg := frame_abs_nonneg
      (show |difference F j|≤frameCap by simpa only [frameCap] using (difference_small F j).le)
    dsimp [g]
    linarith
  have hsum := Finset.sum_lt_sum_of_nonempty
    (s := (Finset.univ.erase i : Finset Vertex))
    (by
      have hc : (Finset.univ.erase i : Finset Vertex).card=6 := by simp
      exact Finset.card_pos.1 (by omega))
    (fun j _ => hother j)
  have hcost : (∑j,g j)=2*Real.pi := marker_budget C F hgap
    (fun j => (stateOf C j).signedLabel)
  have hsplit := Finset.sum_erase_add (s := Finset.univ) (f := g) (Finset.mem_univ i)
  rw [hcost] at hsplit
  norm_num at hsum
  change (2493/2500:ℝ)<g i at hcharge
  linarith [Arithmetic.two_pi_lt_710_over_113]

/-- The radial conclusion is global for one original zero edge;
the source tangent is allowed to vanish. -/
theorem ceiling_nonpositive_source_outer (C : BoundaryCycle Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0)
    (hs : C.tangent i≤0) : C.kind i=.outer := by
  by_contra hcore
  let hgap : ∀j,19/25<angleGap C.beta j := boundary_gap_lower C le_rfl
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [hj] using C.feasible i
  have howner := GlobalZeroSign.classify C (by norm_num [Q0]) F i hi j haxis
  have htwo : j=2 ∧ C.tangent (next i)<0 := by
    rcases howner with ⟨_,hpos⟩ | hh
    · exact (not_lt_of_ge hs hpos).elim
    · exact hh
  have hphase : pairAngle C i=difference F i := by
    simpa [hi] using pair_angle_increment C F hgap i
  have hp := stateOf_feasible C i j haxis
  rw [htwo.1,hphase] at hp
  have hs' : transverse (stateOf C i)≤0 := by
    have hh := (div_le_iff₀ (C.a_pos i)).1 hs
    simpa only [transverse,stateOf,signOf_spec,zero_mul] using hh
  have ht' : transverse (stateOf C (next i))≤0 := by
    have hh := (div_lt_iff₀ (C.a_pos (next i))).1 htwo.2
    simpa only [transverse,stateOf,signOf_spec,zero_mul,mul_zero] using hh.le
  have hc : (stateOf C i).branch.type=0 := (branchOf_core_iff C i).2 hcore
  have hcharge := core_source_charge (stateOf C i) (stateOf C (next i)) hc
    (by simpa only [frameCap] using (difference_small F i).le) hs' ht' hp
  apply closed_charge_impossible C F hgap i
  have hphase' : phaseValue F hgap i=difference F i := by
    linarith [phase_gap C F hgap i,pairAngle_gap C i]
  simpa only [hphase'] using hcharge

theorem nonpositive_source_outer {q : ℝ} (C : BoundaryCycle q)
    (hq : q∈Icc (5/2:ℝ) Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0)
    (hs : C.tangent i≤0) : C.kind i=.outer := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  have hh := ceiling_nonpositive_source_outer D G i hi
    (by simpa only [hR.same_tangents] using hs)
  simpa only [hR.same_kind] using hh

theorem frame_nonpositive_source_outer {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0)
    (i : Vertex) (hi : Candidate.word i=0) (hs : C.tangent i≤0) :
    C.kind i=.outer := by
  obtain ⟨G,hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro k; simpa only [mul_div_assoc] using F.canonical_eq k)
  have hinc : integerQuarterIncrement G.quarter i=0 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hi]
  exact nonpositive_source_outer C hq G i hinc hs

end SquaresInCircles.Eight.TableFree.GlobalZeroSourceOuter
