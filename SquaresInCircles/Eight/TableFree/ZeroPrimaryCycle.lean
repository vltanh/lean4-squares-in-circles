module

public import SquaresInCircles.Eight.TableFree.ZeroPrimarySupport

/-!
# The closed-tour exclusion of an original zero-primary witness

The original primary edge has boosted cost greater than `.985`. The
other six original edges each have G1 cost greater than `.8833`.
The closed physical frame tour pays at least the exceptional edge's
frame cost on its return path, so these estimates exceed `2*pi` after
the unchanged original vertex labels cancel.

The continuous G1 pair estimates are the explicit upstream input to
this assembly. The exceptional primary estimate and the closed-tour
return estimate are proved here and in `ZeroPrimarySupport`; neither
wrong-word exclusion is an input. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Set

namespace SquaresInCircles.Eight.TableFree.ZeroPrimary

open FramePair TableFreeWordGeometry

/-- A metric transform of the actual closed frame tour pays twice any
one edge's cost. No extrema or preferred axis are selected. -/
theorem twice_frame_edge_le_tour {C : BoundaryCycle Q0} (F : QuarterLift C)
    (i : Vertex) :
    2*frameCost |difference F i|≤∑j,frameCost |difference F j| := by
  have hrange (j k : Vertex) : |F.theta k-F.theta j|∈Icc 0 (Real.pi/4) := by
    refine ⟨abs_nonneg _,?_⟩
    linarith [theta_spread F j k,Real.pi_gt_three]
  let r : Vertex → ℝ := fun j => frameCost |F.theta j-F.theta i|
  have hstep (j : Vertex) : |r (next j)-r j|≤frameCost |difference F j| := by
    have h₁ := frameCost_triangle (hrange i j) (hrange j (next j))
      (hrange i (next j)) (by linarith [abs_sub_le (F.theta (next j)) (F.theta j) (F.theta i)])
    have h₂ := frameCost_triangle (hrange i (next j)) (hrange (next j) j)
      (hrange i j) (by linarith [abs_sub_le (F.theta j) (F.theta (next j)) (F.theta i)])
    rw [abs_sub_comm (F.theta j) (F.theta (next j))] at h₂
    apply abs_le.2
    dsimp [r,difference]
    constructor <;> linarith
  have htour := closed_walk_range_bound r i (next i)
  have hzero : r i=0 := by simp [r,frameCost_zero]
  have hnext : r (next i)=frameCost |difference F i| := rfl
  have hnn : 0≤frameCost |difference F i| := frameCost_nonneg (hrange i (next i))
  rw [hzero,hnext,sub_zero,abs_of_nonneg hnn] at htour
  exact htour.trans (Finset.sum_le_sum (fun j _ => hstep j))

/-- The six-edge return path pays the selected edge's actual width. -/
theorem frame_edge_le_return {C : BoundaryCycle Q0} (F : QuarterLift C)
    (i : Vertex) :
    frameCost |difference F i|≤
      ∑j∈(Finset.univ.erase i : Finset Vertex),frameCost |difference F j| := by
  have htour := twice_frame_edge_le_tour F i
  have hsplit := Finset.sum_erase_add (s := Finset.univ)
    (f := fun j => frameCost |difference F j|) (Finset.mem_univ i)
  linarith

lemma frame_pair_cost (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex) :
    (stateOf C i).cost (stateOf C (next i)) (FramePair.pairAngle C i)=
      phaseValue F hgap i+(stateOf C i).signedLabel-
        (stateOf C (next i)).signedLabel-(9/50)*frameCost |difference F i| := by
  have hphase : FramePair.pairAngle C i=phaseValue F hgap i := by
    linarith [FramePair.pairAngle_gap C i,phase_gap C F hgap i]
  have hshort : |difference F i|≤Real.pi/4 := by
    linarith [difference_small F i,Real.pi_gt_three]
  have hperiod : periodicFrameCost (phaseValue F hgap i)=
      frameCost |difference F i| := by
    have hh := periodicFrameCost_int_quarter (difference F i)
      ((F.word hgap pi_lt_22_over_7 i).val:ℤ)
    have hid : phaseValue F hgap i=difference F i+
        (((F.word hgap pi_lt_22_over_7 i).val:ℤ):ℝ)*(Real.pi/2) := by
      simp [phaseValue]
      ring
    rw [hid,hh,periodicFrameCost_of_short hshort]
  simp only [FramePair.State.cost,hphase,hperiod]
  ring

lemma handGamma_lower (i j : Fin 4) : (8833/10000:ℝ)≤handGamma i j := by
  fin_cases i <;> fin_cases j <;> norm_num [handGamma,handGammaNumerator]

/-- The upstream G1 pair theorem is needed only on the other six edges.
Every quantity in this statement is evaluated on the same original
boundary cycle and the same chosen signed representations. -/
theorem no_primary_of_return_pair_costs (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hpair : ∀k, k≠i →
      handGamma (branchOf C k).type (branchOf C (next k)).type<
        (stateOf C k).cost (stateOf C (next k)) (FramePair.pairAngle C k))
    (hk : F.word hgap pi_lt_22_over_7 i=0) (j : Fin 4) (hj : j=1 ∨ j=3)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) : False := by
  let g : Vertex → ℝ := fun k => phaseValue F hgap k+
    (stateOf C k).signedLabel-(stateOf C (next k)).signedLabel
  let v : Vertex → ℝ := fun k => frameCost |difference F k|
  have hboost : (197/200:ℝ)<g i+(9/50)*v i :=
    actual_boost C F hgap i hk j hj howner
  have hother (k : Vertex) (hki : k≠i) : (8833/10000:ℝ)<g k-(9/50)*v k := by
    have hh := (handGamma_lower (branchOf C k).type (branchOf C (next k)).type).trans_lt
      (hpair k hki)
    simpa only [frame_pair_cost C F hgap k,g,v] using hh
  have hsum := Finset.sum_lt_sum_of_nonempty
    (s := (Finset.univ.erase i : Finset Vertex))
    (by
      have hc : (Finset.univ.erase i : Finset Vertex).card=6 := by simp
      exact Finset.card_pos.1 (by omega))
    (fun k hk => hother k (Finset.mem_erase.mp hk).1)
  have hconst : ∑ _k∈(Finset.univ.erase i : Finset Vertex),(8833/10000:ℝ)=26499/5000 := by
    rw [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ i)]
    norm_num
  have hcost : (∑k,g k)=2*Real.pi := marker_budget C F hgap
    (fun k => (stateOf C k).signedLabel)
  have hsplit := Finset.sum_erase_add (s := Finset.univ) (f := g) (Finset.mem_univ i)
  have hreturn : v i≤∑k∈(Finset.univ.erase i : Finset Vertex),v k :=
    frame_edge_le_return F i
  rw [hconst,Finset.sum_sub_distrib,← Finset.mul_sum] at hsum
  rw [hcost] at hsplit
  linarith [Arithmetic.two_pi_lt_710_over_113]

/-- All G1 pairs on the original cycle discharge the only upstream
continuous input of the zero-primary cycle argument. -/
theorem no_primary_of_pair_costs (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hpair : ∀k,handGamma (branchOf C k).type (branchOf C (next k)).type<
      (stateOf C k).cost (stateOf C (next k)) (FramePair.pairAngle C k))
    (i : Vertex) (hk : F.word hgap pi_lt_22_over_7 i=0)
    (j : Fin 4) (hj : j=1 ∨ j=3)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) : False :=
  no_primary_of_return_pair_costs C F hgap i (fun k _ => hpair k) hk j hj howner

/-- Every feasible original zero-edge witness is secondary, including
ties between originally feasible separating axes. -/
theorem original_zero_secondary (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hpair : ∀k,handGamma (branchOf C k).type (branchOf C (next k)).type<
      (stateOf C k).cost (stateOf C (next k)) (FramePair.pairAngle C k))
    (i : Vertex) (hk : F.word hgap pi_lt_22_over_7 i=0)
    (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) : j=0 ∨ j=2 := by
  fin_cases j
  · exact Or.inl rfl
  · exact (no_primary_of_pair_costs C F hgap hpair i hk 1 (Or.inl rfl) howner).elim
  · exact Or.inr rfl
  · exact (no_primary_of_pair_costs C F hgap hpair i hk 3 (Or.inr rfl) howner).elim

/-- Existence is taken from the original boundary separator; the new
conclusion only identifies its surviving geometric kind. -/
theorem original_zero_witness (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hpair : ∀k,handGamma (branchOf C k).type (branchOf C (next k)).type<
      (stateOf C k).cost (stateOf C (next k)) (FramePair.pairAngle C k))
    (i : Vertex) (hk : F.word hgap pi_lt_22_over_7 i=0) :
    ∃j : Fin 4,(j=0 ∨ j=2) ∧
      (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa [← hj] using C.feasible i
  exact ⟨j,original_zero_secondary C F hgap hpair i hk j howner,howner⟩

end SquaresInCircles.Eight.TableFree.ZeroPrimary
