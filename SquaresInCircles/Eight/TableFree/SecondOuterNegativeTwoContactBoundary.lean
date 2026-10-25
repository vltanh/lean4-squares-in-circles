module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoContactConcavity
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoAligned

/-!
# Actual boundary reduction for the lower target-secondary owner

Every original weak separator first gives an actual contact on the same
circle, with no larger cost.  At a fixed target coordinate, explicit
intermediate-value contacts furnish both ends of the feasible source
interval.  Strict contact concavity then selects one of the four genuine
boundary types.  The axial and aligned types are discharged here.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

structure BoundaryContact (B : ℝ) where
  b : ℝ
  x : ℝ
  source : b∈Icc 0 outerDiagonal
  angle : x∈Icc 0 (7/10)
  contact : TargetContact.B b x=B
  boundary : b=0 ∨ b=outerDiagonal ∨ x=0 ∨ x=7/10

lemma target_shift_mem {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    B-1/2∈Icc (-(1/2)) (2/5) :=
  ⟨by linarith [hB.1],by linarith [hB.2,outer_endpoint_bounds.2.2.2]⟩

lemma fixed_contact_value {b B x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hB : B∈Icc 0 outerDiagonal)
    (hc : TargetContact.B b x=B) :
    ContactCurvature.fixedCost (B-1/2) b=value b B (Real.pi/2-x) := by
  have hd : TargetContact.Domain b x := ⟨hb,hx,by rw [hc]; exact hB⟩
  have he := ContactInverse.original_angle hd
  rw [hc] at he
  dsimp [ContactCurvature.fixedCost,value]
  rw [he,show B-1/2+1/2=B by ring]

lemma left_boundary_contact {b B x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hB : B∈Icc 0 outerDiagonal)
    (hc : TargetContact.B b x=B) :
    ∃ w : BoundaryContact B, w.b≤b := by
  by_cases hleft : B≤TargetContact.B 0 (7/10)
  · have hstart : TargetContact.B 0 0≤B := by
      rw [TargetContact.B_zero,ShortOuterOne.SameContact.arc_zero]
      linarith [hB.1,outer_endpoint_bounds.1]
    have hcont : Continuous (TargetContact.B 0) :=
      continuous_iff_continuousAt.2 fun t => (TargetContact.B_angle_hasDerivAt 0 t).continuousAt
    obtain ⟨t,ht,hcontact⟩ := intermediate_value_Icc
      (show (0:ℝ)≤7/10 by norm_num) hcont.continuousOn ⟨hstart,hleft⟩
    exact ⟨⟨0,t,outer_zero_mem,ht,hcontact,Or.inl rfl⟩,hb.1⟩
  · have hcap := TargetContact.B_angle_monotone hb hx
      (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num) hx.2
    rw [hc] at hcap
    have hcont : Continuous (fun t => TargetContact.B t (7/10)) := by
      dsimp [TargetContact.B,arc]
      fun_prop
    obtain ⟨l,hl,hcontact⟩ := intermediate_value_Icc hb.1 hcont.continuousOn
      (show B∈Icc (TargetContact.B 0 (7/10)) (TargetContact.B b (7/10)) from
        ⟨by linarith,hcap⟩)
    exact ⟨⟨l,7/10,⟨hl.1,hl.2.trans hb.2⟩,by norm_num,hcontact,
      Or.inr (Or.inr (Or.inr rfl))⟩,hl.2⟩

lemma right_boundary_contact {b B x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hB : B∈Icc 0 outerDiagonal)
    (hc : TargetContact.B b x=B) :
    ∃ w : BoundaryContact B, b≤w.b := by
  have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
  by_cases hright : TargetContact.B outerDiagonal 0≤B
  · have hend := TargetContact.B_source_monotone hx hb hd hb.2
    dsimp only at hend
    rw [hc] at hend
    have hcont : Continuous (TargetContact.B outerDiagonal) :=
      continuous_iff_continuousAt.2 fun t =>
        (TargetContact.B_angle_hasDerivAt outerDiagonal t).continuousAt
    obtain ⟨t,ht,hcontact⟩ := intermediate_value_Icc hx.1 hcont.continuousOn
      (show B∈Icc (TargetContact.B outerDiagonal 0) (TargetContact.B outerDiagonal x) from
        ⟨hright,hend⟩)
    exact ⟨⟨outerDiagonal,t,hd,⟨ht.1,ht.2.trans hx.2⟩,hcontact,
      Or.inr (Or.inl rfl)⟩,hb.2⟩
  · have hstart := TargetContact.B_angle_monotone hb (by norm_num) hx hx.1
    rw [hc] at hstart
    have hcont : Continuous (fun t => TargetContact.B t 0) := by
      dsimp [TargetContact.B,arc]
      fun_prop
    obtain ⟨r,hr,hcontact⟩ := intermediate_value_Icc hb.2 hcont.continuousOn
      (show B∈Icc (TargetContact.B b 0) (TargetContact.B outerDiagonal 0) from
        ⟨hstart,by linarith⟩)
    exact ⟨⟨r,0,⟨hb.1.trans hr.1,hr.2⟩,by norm_num,hcontact,
      Or.inr (Or.inr (Or.inl rfl))⟩,hr.1⟩

theorem contact_boundary {b B x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hB : B∈Icc 0 outerDiagonal)
    (hc : TargetContact.B b x=B) :
    ∃ w : BoundaryContact B, value w.b B (Real.pi/2-w.x)≤value b B (Real.pi/2-x) := by
  obtain ⟨l,hl⟩ := left_boundary_contact hb hx hB hc
  obtain ⟨r,hr⟩ := right_boundary_contact hb hx hB hc
  have hmin := (ContactCurvature.fixedCost_concave (target_shift_mem hB)).min_le_of_mem_Icc
    l.source r.source ⟨hl,hr⟩
  rw [fixed_contact_value l.source l.angle hB l.contact,
    fixed_contact_value r.source r.angle hB r.contact,
    fixed_contact_value hb hx hB hc] at hmin
  rcases le_total (value l.b B (Real.pi/2-l.x)) (value r.b B (Real.pi/2-r.x)) with h|h
  · exact ⟨l,by simpa only [min_eq_left h] using hmin⟩
  · exact ⟨r,by simpa only [min_eq_right h] using hmin⟩

lemma original_lower_contact {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2-x)) :
    ∃ b' B', b'∈Icc 0 outerDiagonal ∧ B'∈Icc 0 outerDiagonal ∧
      TargetContact.B b' x=B' ∧ value b' B' (Real.pi/2-x)≤value b B (Real.pi/2-x) := by
  have hb := source_mem hs
  have hB := source_mem ht
  have hcut := lower_target_cut hs hx hm
  by_cases hpos : 0≤TargetContact.B b x
  · have hc : TargetContact.B b x∈Icc 0 outerDiagonal := ⟨hpos,hcut.trans hB.2⟩
    have hT := T_monotone hc hB hcut
    refine ⟨b,TargetContact.B b x,hb,hc,rfl,?_⟩
    dsimp [value]
    linarith
  · have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
    have hdiag := TargetContact.B_angle_monotone hd (by norm_num) hx hx.1
    rw [TargetContact.B_zero,ShortOuterOne.SameContact.arc_diagonal] at hdiag
    have hcont : Continuous (fun t => TargetContact.B t x) := by
      dsimp [TargetContact.B,arc]
      fun_prop
    obtain ⟨b',hb',he⟩ := intermediate_value_Icc hb.2 hcont.continuousOn
      (show (0:ℝ)∈Icc (TargetContact.B b x) (TargetContact.B outerDiagonal x) by
        constructor <;> linarith [outer_endpoint_bounds.2.2.2])
    have hbnew : b'∈Icc 0 outerDiagonal := ⟨hb.1.trans hb'.1,hb'.2⟩
    have hP := P_monotone hb hbnew hb'.1
    have hT := T_monotone outer_zero_mem hB hB.1
    refine ⟨b',0,hbnew,outer_zero_mem,he,?_⟩
    dsimp [value]
    linarith

theorem original_lower_boundary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2-x)) :
    ∃ B', B'∈Icc 0 outerDiagonal ∧ ∃ w : BoundaryContact B',
      value w.b B' (Real.pi/2-w.x)≤value b B (Real.pi/2-x) := by
  obtain ⟨b',B',hb',hB',hc,hstep⟩ := original_lower_contact hs ht hx hm
  obtain ⟨w,hw⟩ := contact_boundary hb' hx hB' hc
  exact ⟨B',hB',w,hw.trans hstep⟩

lemma axial_reference_target : (37/500:ℝ)<TargetContact.B 0 (13/20) := by
  have hs := sin_lower_seven (show (0:ℝ)≤13/20 by norm_num)
  have hc := cos_le_cos8 (show (0:ℝ)≤13/20 by norm_num)
  have hcos0 : 0≤Real.cos (13/20) := by
    linarith [(positive_trig (show (13/20:ℝ)∈Icc 0 (7/10) by norm_num)).1]
  have hmul := mul_le_mul
    (show outerAxial-1/2≤(183/200:ℝ) by linarith [outer_endpoint_bounds.2.1]) hc hcos0
    (by norm_num : (0:ℝ)≤183/200)
  norm_num [cos8] at hs hc hmul
  dsimp [TargetContact.B]
  rw [ShortOuterOne.SameContact.arc_zero]
  nlinarith

theorem axial_contact_lower {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : TargetContact.B 0 x=B) :
    (9/10:ℝ)<value 0 B (Real.pi/2-x) := by
  by_cases hearly : x≤13/20
  · have hT := T_lower hB
    dsimp [value]
    rw [P_zero]
    linarith [pi_hand_enclosure.1]
  · have hmono := TargetContact.B_angle_monotone outer_zero_mem
      (show (13/20:ℝ)∈Icc 0 (7/10) by norm_num) hx (by linarith)
    rw [hc] at hmono
    have hT := T_increment_lower outer_zero_mem hB hB.1
    rw [T_zero] at hT
    dsimp [value]
    rw [P_zero]
    linarith [axial_reference_target,pi_hand_enclosure.1,hx.2]

theorem aligned_contact_lower {b B : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (hc : TargetContact.B b 0=B) :
    (8977827/10000000:ℝ)<value b B (Real.pi/2) := by
  rw [TargetContact.B_zero] at hc
  exact original_aligned (ShortOuterOne.SameContact.arc_state hb)
    (ShortOuterOne.SameContact.arc_state hB) (by linarith)

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo
