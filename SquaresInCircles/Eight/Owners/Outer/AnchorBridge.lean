module

public import SquaresInCircles.Eight.Owners.Outer.AnchorDomain
public import SquaresInCircles.Eight.Owners.Quarter.SignCycle
public import SquaresInCircles.Eight.Owners.Quarter.SignScalar

/-!
# Eight squares: four original radial anchors from the actual normal owner family

Only the original feasible quarter axes are used.  The surrounding
zero edges obtain their own original secondary witnesses from the
global zero-edge theorem.  No separate anchor-circle or anchor-sign
premise is needed.
-/

section
/-!
## No core anchor between a zero edge and a high quarter

Each projection receives its positive coefficient `mass`, and the shared core point has positive
combined force coordinates (`force_component_lower`, `force_sum_upper`). With the bounds on the
core coordinates their sum leaves a strict reserve in all four cases of endpoint signs
(`path_scalar_reserve`), so the two-edge charge exceeds `2` (`core_path_charge`). The return along
the other five edges is a separate statement.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalOuterAnchor

open FramePair ZeroPrimary GlobalQuarterSign

def forceX (primary : Bool) (lam d : ℝ) : ℝ := if primary then 0 else lam*Real.sin d
def forceY (primary : Bool) (lam d : ℝ) : ℝ :=
  if primary then lam/Real.cos d else lam*Real.cos d
def angle (primary : Bool) (lam a d : ℝ) : ℝ :=
  if primary then primaryAngle lam a d else secondaryAngle lam d
def scale (primary : Bool) (lam d : ℝ) : ℝ := if primary then lam/Real.cos d else lam
def forceCap (bad : Bool) : ℝ := if bad then m*(25/19) else k*(10/7)

theorem mass_positive (bad : Bool) : 0< mass bad := by cases bad <;> norm_num [mass,k,m]

theorem scale_nonneg (p : Bool) {lam d : ℝ} (hlam : 0≤lam) (hd : |d|≤frameCap) :
    0≤ scale p lam d := by
  have hc : 0≤Real.cos d := by linarith [(signed_trig hd).1]
  cases p
  · exact hlam
  · exact div_nonneg hlam hc

theorem left_charge (s c : State) (p : Bool) {lam d : ℝ}
    (hlam : 0≤lam) (hd : |d|≤frameCap)
    (hl : lam*transverse s≤ s.signedLabel) (hm : width d≤leftProjection p s c d) :
    lam/2+angle p lam s.a d-forceX p lam d*(c.a-1/2)-forceY p lam d*(c.b-1/2)≤
      d+s.signedLabel := by
  have hc : Real.cos d≠0 := ne_of_gt (by linarith [(signed_trig hd).1])
  have hid : lam/2+angle p lam s.a d-forceX p lam d*(c.a-1/2)-forceY p lam d*(c.b-1/2)=
      d+lam*transverse s+scale p lam d*(width d-leftProjection p s c d) := by
    cases p <;> dsimp [angle,forceX,forceY,scale,leftProjection,width,
      primaryAngle,secondaryAngle] <;> field_simp [hc] <;> ring
  rw [hid]
  have hn := mul_nonpos_of_nonneg_of_nonpos (scale_nonneg p hlam hd) (sub_nonpos.mpr hm)
  linarith

theorem right_charge (c t : State) (p : Bool) {lam d : ℝ}
    (hlam : 0≤lam) (hd : |d|≤frameCap)
    (hl : -(lam*transverse t)≤ -t.signedLabel) (hm : width d≤rightProjection p c t d) :
    lam/2+angle p lam t.a d-forceY p lam d*(c.a-1/2)-forceX p lam d*(c.b-1/2)≤
      d-t.signedLabel := by
  have hc : Real.cos d≠0 := ne_of_gt (by linarith [(signed_trig hd).1])
  have hid : lam/2+angle p lam t.a d-forceY p lam d*(c.a-1/2)-forceX p lam d*(c.b-1/2)=
      d-lam*transverse t+scale p lam d*(width d-rightProjection p c t d) := by
    cases p <;> dsimp [angle,forceX,forceY,scale,rightProjection,width,
      primaryAngle,secondaryAngle] <;> field_simp [hc] <;> ring
  rw [hid]
  have hn := mul_nonpos_of_nonneg_of_nonpos (scale_nonneg p hlam hd) (sub_nonpos.mpr hm)
  linarith

theorem force_component_lower (p bad : Bool) {d : ℝ} (hd : |d|≤frameCap)
    (hp : bad=true → p=true) :
    -k*(13/20)≤forceX p (mass bad) d ∧
      k*(19/25)≤forceY p (mass bad) d := by
  have ht := signed_trig hd
  have hs : -(13/20:ℝ)≤Real.sin d := by linarith [neg_le_abs (Real.sin d)]
  have hsec := (secant_upper hd).2.1
  have hdiv (lam : ℝ) : lam/Real.cos d=lam*(1/Real.cos d) := by ring
  cases hb : bad
  · cases p <;> dsimp [forceX,forceY,mass,k] <;> (try rw [hdiv]) <;>
      constructor <;> nlinarith
  · have hpp : p=true := hp hb
    rw [hpp]
    dsimp [forceX,forceY,mass,k,m]
    rw [hdiv]
    constructor <;> nlinarith

theorem force_sum_upper (p bad : Bool) {d : ℝ} (hd : |d|≤frameCap)
    (hp : bad=true → p=true) :
    forceX p (mass bad) d+forceY p (mass bad) d<forceCap bad := by
  have hsec := (secant_upper hd).2.2
  have hsum := sine_cosine_sum_upper d
  have hdiv (lam : ℝ) : lam/Real.cos d=lam*(1/Real.cos d) := by ring
  cases hb : bad
  · cases p <;> dsimp [forceX,forceY,mass,forceCap,k] <;> (try rw [hdiv]) <;> nlinarith
  · have hpp : p=true := hp hb
    rw [hpp]
    dsimp [forceX,forceY,mass,forceCap,m]
    rw [hdiv]
    nlinarith

theorem angle_k_lower (p : Bool) {a d : ℝ} (ha : 447/800≤a) (hA : a≤283/200)
    (hd : |d|≤frameCap) : negativeCost (max 0 (-d))≤angle p k a d := by
  cases p
  · exact secondary_k_lower hd
  · exact primary_k_lower ha hA hd

theorem negative_part_mem {d : ℝ} (hd : |d|≤frameCap) : max 0 (-d)∈Icc 0 frameCap := by
  exact ⟨le_max_left _ _,max_le (by norm_num [frameCap]) ((neg_le_abs d).trans hd)⟩

/-- The masses and the angle bounds leave a strict reserve in all four cells of endpoint signs, over
the whole frame domain of the path. -/
theorem path_scalar_reserve (p q badL badR : Bool) {a A v d : ℝ}
    (ha : 447/800≤a) (hA : a≤283/200) (ha' : 447/800≤A) (hA' : A≤283/200)
    (hv : |v|≤frameCap) (hd : |d|≤frameCap) (hsum : |v+d|≤frameCap)
    (hp : badL=true → p=true ∧ 0<v) (hq : badR=true → q=true ∧ 0<d) :
    2<Real.pi/2+(mass badL+mass badR)/2+
      angle p (mass badL) a v+angle q (mass badR) A d-
        (forceCap badL+forceCap badR)/12 := by
  have hnv := negative_part_mem hv
  have hnd := negative_part_mem hd
  cases hbL : badL <;> cases hbR : badR
  · have hl := angle_k_lower p ha hA hv
    have hr := angle_k_lower q ha' hA' hd
    have hc := negative_cost_sum hnv.1 hnd.1 (negative_parts_sum hv hd hsum)
    dsimp [mass,forceCap,k,m] at *
    linarith [half_pi_lower]
  · have hright := hq hbR
    have hr := primary_m_positive_lower hA'
      ⟨hright.2.le,(le_abs_self d).trans hd⟩
    have hl := angle_k_lower p ha hA hv
    have hc := negative_cost_lower hnv
    rw [hright.1]
    dsimp [mass,forceCap,angle,k,m] at *
    linarith [half_pi_lower]
  · have hleft := hp hbL
    have hl := primary_m_positive_lower hA
      ⟨hleft.2.le,(le_abs_self v).trans hv⟩
    have hr := angle_k_lower q ha' hA' hd
    have hc := negative_cost_lower hnd
    rw [hleft.1]
    dsimp [mass,forceCap,angle,k,m] at *
    linarith [half_pi_lower]
  · have hleft := hp hbL
    have hright := hq hbR
    have hl := primary_m_positive_lower hA
      ⟨hleft.2.le,(le_abs_self v).trans hv⟩
    have hr := primary_m_positive_lower hA'
      ⟨hright.2.le,(le_abs_self d).trans hd⟩
    rw [hleft.1,hright.1]
    dsimp [mass,forceCap,angle,k,m] at *
    linarith [half_pi_lower]

/-- Around a core vertex with nonpositive transverse coordinate, the two-edge charge exceeds `2`,
for both zero owners and both high-quarter owners and any endpoint signs. -/
theorem core_path_charge (s c t : State) (p q : Bool) {v d : ℝ}
    (hcore : c.branch.type=0) (hc : transverse c≤0)
    (hv : |v|≤frameCap) (hd : |d|≤frameCap) (hsum : |v+d|≤frameCap)
    (hl : s.Feasible c (leftOwner p) v)
    (hr : c.Feasible t (rightOwner q) (Real.pi/2+d)) :
    2<Real.pi/2+v+d+s.signedLabel-t.signedLabel := by
  have hlm := (left_margin s c p hv hc).1 hl
  have hrm := (right_margin c t q hd hc).1 hr
  obtain ⟨badL,hlabelL,hbadL⟩ := left_mass_exists s c p hcore hv hlm
  obtain ⟨badR,hlabelR,hbadR⟩ := right_mass_exists c t q hcore hd hrm
  have hleft := left_charge s c p (mass_positive badL).le hv hlabelL hlm
  have hright := right_charge c t q (mass_positive badR).le hd hlabelR hrm
  have hfl := force_component_lower p badL hv (fun hh => (hbadL hh).1)
  have hfr := force_component_lower q badR hd (fun hh => (hbadR hh).1)
  have hU : 0≤forceX p (mass badL) v+forceY q (mass badR) d := by
    dsimp [k] at hfl hfr
    linarith
  have hV : 0≤forceY p (mass badL) v+forceX q (mass badR) d := by
    dsimp [k] at hfl hfr
    linarith
  have hcb := core_bounds c hcore
  have hcoreA := mul_le_mul_of_nonneg_left (show c.a-1/2≤(1/12:ℝ) by linarith) hU
  have hcoreB := mul_le_mul_of_nonneg_left (show c.b-1/2≤(1/12:ℝ) by linarith) hV
  have hcapL := force_sum_upper p badL hv (fun hh => (hbadL hh).1)
  have hcapR := force_sum_upper q badR hd (fun hh => (hbadR hh).1)
  have hscalar := path_scalar_reserve p q badL badR
    (primary_lower s).le (coordinates s).2.1.le
    (primary_lower t).le (coordinates t).2.1.le hv hd hsum hbadL hbadR
  nlinarith only [hleft,hright,hcoreA,hcoreB,hcapL,hcapR,hscalar]

end SquaresInCircles.Eight.GlobalOuterAnchor
end
end
end

section
/-!
## Radial anchors beside the zero edges

A zero edge followed by a high-quarter witness has an outer common vertex (`zero_high_outer`), and
reflected reversal gives the same for a low-quarter witness followed by a zero edge
(`low_zero_outer`). These two statements cover the four anchors of the normal owners. On a cycle at
`Q0` the pair bounds of the other five edges bound the uncharged sum on two consecutive edges
(`two_edge_charge_lt_two`, `ceiling_zero_high_outer`, `ceiling_low_zero_outer`), and the
statements carry over to every radius `q ∈ [5/2, Q0]`, with the common marker, the axes and the
weak ties.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.GlobalOuterAnchor

open FramePair QuarterWordGeometry

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

/-- The pair bounds of the other five edges bound strictly the uncharged sum on any two consecutive
edges; no payment by the return frame is needed. -/
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
    simp only [zero_mul] at hy
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

/-- At `Q0`, a low-quarter witness followed by a zero edge has an outer common vertex: reflected
reversal of the two-edge formulas, with the same cycle and separators. -/
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

end SquaresInCircles.Eight.GlobalOuterAnchor
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalOuterAnchor

open Candidate

theorem frame_zero_high_outer {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex)
    (hi : word i=0) (hj : word (next i)=1)
    (j : Fin 4) (howner : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square (next i)) (C.square (next (next i)))) :
    C.kind (next i)=.outer := by
  obtain ⟨G,hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro k; simpa only [mul_div_assoc] using F.canonical_eq k)
  have hinc : integerQuarterIncrement G.quarter i=0 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hi]
  have hinc' : integerQuarterIncrement G.quarter (next i)=1 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hj]
  exact zero_high_outer C hq G i hinc hinc' j howner haxis

theorem frame_low_zero_outer {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex)
    (hi : word i=1) (hj : word (next i)=0)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind (next i)=.outer := by
  obtain ⟨G,hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro k; simpa only [mul_div_assoc] using F.canonical_eq k)
  have hinc : integerQuarterIncrement G.quarter i=1 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hi]
  have hinc' : integerQuarterIncrement G.quarter (next i)=0 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hj]
  exact low_zero_outer C hq G i hinc hinc' j howner haxis

theorem frame_low_anchor {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex)
    (hi : word i=1) (hj : word (next i)=0)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind (next i)=.outer ∧ 0<C.tangent (next i) := by
  refine ⟨frame_low_zero_outer F hq i hi hj j howner haxis,?_⟩
  rcases GlobalQuarterSign.of_frame F hq i hi j haxis with ⟨_,ht⟩ | ⟨hh,_⟩
  · exact ht
  · rcases howner with rfl | rfl <;> rcases hh with hh | hh <;> norm_num at hh

theorem frame_high_anchor {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex)
    (hi : word i=0) (hj : word (next i)=1)
    (j : Fin 4) (howner : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square (next i)) (C.square (next (next i)))) :
    C.kind (next i)=.outer ∧ C.tangent (next i)<0 := by
  refine ⟨frame_zero_high_outer F hq i hi hj j howner haxis,?_⟩
  rcases GlobalQuarterSign.of_frame F hq (next i) hj j haxis with ⟨hh,_⟩ | ⟨_,ht⟩
  · rcases howner with rfl | rfl <;> rcases hh with hh | hh <;> norm_num at hh
  · exact ht

/-- The original normal owner theorem alone supplies every radial and
sign anchor required by the sharp same-radius source record. -/
theorem normal_anchors {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0)
    (howners : Candidate.OwnerRestriction C SignedCycle.normalOwners) :
    (C.kind H=.outer ∧ 0<C.tangent H) ∧
      (C.kind A=.outer ∧ 0<C.tangent A) ∧
      (C.kind B=.outer ∧ C.tangent B<0) ∧
      (C.kind D=.outer ∧ C.tangent D<0) := by
  let w := SignedCycle.retainedWitnesses F howners
  have hf (i : Vertex) : (forwardAxis (w.owner i)).Feasible
      (C.square i) (C.square (next i)) :=
    (SignedCycle.atFrame_feasible F i (w.owner i)).1 (w.feasible i)
  have hG : w.owner G=0 ∨ w.owner G=1 := by
    simpa [SignedCycle.normalOwners,G] using w.allowed G
  have hB : w.owner B=2 ∨ w.owner B=3 := by
    simpa [SignedCycle.normalOwners,B] using w.allowed B
  have hD : w.owner D=2 ∨ w.owner D=3 := by
    simpa [SignedCycle.normalOwners,D] using w.allowed D
  have hE : w.owner E=0 ∨ w.owner E=1 := by
    simpa [SignedCycle.normalOwners,E] using w.allowed E
  have hHanchor := frame_low_anchor F hq E (by norm_num [word,E])
    (by norm_num [word,E,next]) (w.owner E) hE (hf E)
  have hAanchor := frame_low_anchor F hq G (by norm_num [word,G])
    (by norm_num [word,G,next]) (w.owner G) hG (hf G)
  have hBanchor := frame_high_anchor F hq A (by norm_num [word,A])
    (by norm_num [word,A,next]) (w.owner B) hB
    (by simpa [A,B,next] using hf B)
  have hDanchor := frame_high_anchor F hq T (by norm_num [word,T])
    (by norm_num [word,T,next]) (w.owner D) hD
    (by simpa [T,D,next] using hf D)
  exact ⟨by simpa [E,H,next] using hHanchor,
    by simpa [G,A,next] using hAanchor,
    by simpa [A,B,next] using hBanchor,
    by simpa [T,D,next] using hDanchor⟩

theorem normal_outer {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0)
    (howners : Candidate.OwnerRestriction C SignedCycle.normalOwners) :
    ∀i∈({H,A,B,D} : Finset Vertex),C.kind i=.outer := by
  have hh := normal_anchors F hq howners
  intro i hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact hh.1.1
  · exact hh.2.1.1
  · exact hh.2.2.1.1
  · exact hh.2.2.2.1

end SquaresInCircles.Eight.GlobalOuterAnchor
end
end
end
