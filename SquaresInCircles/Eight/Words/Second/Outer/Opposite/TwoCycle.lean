module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeSourcePrimary
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoUpperSourcePrimary
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoLowerStripContact
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroAsymmetric
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoTargetPrimaryLabel

/-!
# Eight squares: original physical and cyclic opposite edge-two inequalities

The scalar theorem is stated for the original role labels and physical weak separating axes
(`original_role`). Reflected reversal transports both the owner (`reflectedOwner`) and the two
vertex labels (`original_reflected`). The cycle theorem `actual` takes the original selected
witness and keeps the original circle, signs and frame lift.
-/

section
/-!
## Both original upper-secondary opposite edge-three owners

The original weak separator bounds the total transverse and primary
displacement by two fifths of the angle.  At primary height at least
one the comparison is with the corresponding aligned state.  Below
one the actual circle slope compares with its primary-one endpoint.
The angular gain pays the entire label loss in both cases.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeThree

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma upper_secondary_displacement {a b x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10)) : upperSecondary b x+1-a≤(2/5)*x := by
  have ht := positive_trig hx
  have hprimary := NegativeTwo.primary_mem hs
  have htransverse := NegativeTwo.source_mem hs
  have ha : 0≤a-1/2 := by linarith [hprimary.1,fine_outer_endpoint_bounds.2]
  have hc := mul_nonneg ha (sub_nonneg.mpr ht.2.1)
  have hsine := mul_le_mul_of_nonneg_right
    (show b-1/2≤2/5 by linarith [htransverse.2,outer_endpoint_bounds.2.2.2]) ht.2.2.1
  dsimp [upperSecondary]
  rw [(ShortOuterOne.SameContact.actual_arc hs).1]
  nlinarith [ht.2.2.2.2.1]

lemma tail_coordinate {a b : ℝ} (hs : OuterState a b) (ha : a≤1) :
    bOne≤b ∧ (43/50)*(b-bOne)≤1-a := by
  have hb := NegativeTwo.source_mem hs
  have hstate := ShortOuterOne.SameContact.primary_state primary_one_mem
  change OuterState 1 bOne at hstate
  have ha0 : 0≤a := hs.1.trans hs.2.1
  have horder : bOne≤b := by
    by_contra hh
    have hsq : (b+1/2)^2<(bOne+1/2)^2 := by
      nlinarith [mul_pos (sub_pos.2 (lt_of_not_ge hh))
        (show 0<bOne+b+1 by linarith [OppositeTwo.bOne_mem.1,hb.1])]
    nlinarith [hs.2.2,hstate.2.2,mul_nonneg (sub_nonneg.2 ha) (show 0≤a+2 by linarith)]
  have hr : (43/50:ℝ)<ratio bOne := by
    norm_num [ratio,OppositeTwo.bOne_arc]
    linarith [OppositeTwo.bOne_bounds.1]
  have hdom {t : ℝ} (ht : t∈Icc bOne outerDiagonal) : t∈Icc 0 outerDiagonal :=
    ⟨OppositeTwo.bOne_mem.1.trans ht.1,ht.2⟩
  have hmon : MonotoneOn (fun t => -arc t-(43/50)*t) (Icc bOne outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (((ShortOuterOne.SameContact.arc_hasDerivAt
        (outer_domain (hdom ht))).fun_neg).fun_sub
          ((hasDerivAt_id' t).const_mul (43/50))).continuousAt.continuousWithinAt)
      (fun t ht => ((ShortOuterOne.SameContact.arc_hasDerivAt
        (outer_domain (hdom (Ioo_subset_Icc_self ht)))).fun_neg).fun_sub
          ((hasDerivAt_id' t).const_mul (43/50)))
      (fun t ht => by
        have hh := ShortOuterOne.SameContact.ratio_monotone
          (outer_domain OppositeTwo.bOne_mem)
          (outer_domain (hdom (Ioo_subset_Icc_self ht))) ht.1.le
        linarith)
  have hh := hmon ⟨le_rfl,OppositeTwo.bOne_mem.2⟩ ⟨horder,hb.2⟩ horder
  dsimp only at hh
  rw [OppositeTwo.bOne_arc,(ShortOuterOne.SameContact.actual_arc hs).1] at hh
  exact ⟨horder,by linarith⟩

lemma T_tail_loss {a b : ℝ} (hs : OuterState a b) (ha : a≤1) :
    T b-T bOne≤(7/5)*(1-a) := by
  have hc := tail_coordinate hs ha
  have hh := T_increment_upper OppositeTwo.bOne_mem (NegativeTwo.source_mem hs) hc.1
  nlinarith

lemma L_tail_loss {a b : ℝ} (hs : OuterState a b) (ha : a≤1) :
    L b-L bOne≤(7/5)*(1-a) := by
  have hc := tail_coordinate hs ha
  have hh := L_increment_upper OppositeTwo.bOne_mem (NegativeTwo.source_mem hs) hc.1
  nlinarith

lemma primary_minus_one_mem {a b : ℝ} (hs : OuterState a b) (ha : 1≤a) :
    a-1∈Icc 0 outerDiagonal := by
  have hp := NegativeTwo.primary_mem hs
  constructor
  · linarith
  · linarith [hp.2,outer_endpoint_bounds.2.1,fine_outer_endpoint_bounds.2]

theorem original_upper_source_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  have hcut := upper_source_secondary ht hx hm
  have hdisp : b+1-A≤(2/5)*x := by
    linarith [upper_secondary_displacement ht hx]
  by_cases hA : 1≤A
  · let j := A-1
    have hj : j∈Icc 0 outerDiagonal := primary_minus_one_mem ht hA
    have hstate := ShortOuterOne.SameContact.arc_state hj
    have haligned := aligned_first hstate ht (show 1≤A-j by dsimp [j]; linarith)
    by_cases hbj : b≤j
    · have hT := T_monotone hb hj hbj
      dsimp [value] at *
      linarith [hx.1]
    · have hT := T_increment_upper hj hb (le_of_not_ge hbj)
      have hd : b-j≤(2/5)*x := by dsimp [j]; linarith
      dsimp [value] at *
      nlinarith [hx.1]
  · have hzero := ShortOuterOne.SameContact.arc_state outer_zero_mem
    have hone := ShortOuterOne.SameContact.primary_state primary_one_mem
    change OuterState 1 bOne at hone
    have haligned := aligned_first hzero hone (by norm_num)
    have hT := T_increment_upper outer_zero_mem hb hb.1
    have hL := L_tail_loss ht (le_of_not_ge hA)
    have hsmall : T b-T 0≤(7/5)*b := by nlinarith [hb.1]
    dsimp [value] at *
    nlinarith [hx.1]

theorem original_upper_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  have hcut := upper_target_secondary hs hx hm
  have hdisp : B+1-a≤(2/5)*x := by
    linarith [upper_secondary_displacement hs hx]
  by_cases ha : 1≤a
  · let j := a-1
    have hj : j∈Icc 0 outerDiagonal := primary_minus_one_mem hs ha
    have hstate := ShortOuterOne.SameContact.arc_state hj
    have haligned := aligned_last hs hstate (show 1≤a-j by dsimp [j]; linarith)
    by_cases hBj : B≤j
    · have hL := L_monotone hB hj hBj
      dsimp [value] at *
      linarith [hx.1]
    · have hL := L_increment_upper hj hB (le_of_not_ge hBj)
      have hd : B-j≤(2/5)*x := by dsimp [j]; linarith
      dsimp [value] at *
      nlinarith [hx.1]
  · have hzero := ShortOuterOne.SameContact.arc_state outer_zero_mem
    have hone := ShortOuterOne.SameContact.primary_state primary_one_mem
    change OuterState 1 bOne at hone
    have haligned := aligned_last hone hzero (by norm_num)
    have hT := T_tail_loss hs (le_of_not_ge ha)
    have hL := L_increment_upper outer_zero_mem hB hB.1
    have hsmall : L B-L 0≤(7/5)*B := by nlinarith [hB.1]
    dsimp [value] at *
    nlinarith [hx.1]

end SquaresInCircles.Eight.SecondWord.OppositeThree
end
end
end

section
/-!
## The increasing original lower-primary contact

The contact rotates the original circle point.  Its speed is positive
on the whole physical angle interval, and the exact circle identity
identifies that speed with the primary-coordinate radical whenever
the original weak separator keeps the contact on the physical arc.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def lowerSpeed (a b x : ℝ) : ℝ :=
  (a+1/2)*Real.cos x-(b+1/2)*Real.sin x

lemma lowerPrimary_zero (a b : ℝ) : lowerPrimary a b 0=1+b := by
  norm_num [lowerPrimary]
  ring

lemma lowerPrimary_hasDerivAt (a b x : ℝ) :
    HasDerivAt (lowerPrimary a b) (lowerSpeed a b x) x := by
  have hd := (((Real.hasDerivAt_sin x).const_mul (a+1/2)).const_add (1/2)).fun_add
    ((Real.hasDerivAt_cos x).const_mul (b+1/2))
  exact hd.congr_deriv (by dsimp [lowerSpeed]; ring)

lemma lowerSpeed_hasDerivAt (a b x : ℝ) :
    HasDerivAt (lowerSpeed a b) (1/2-lowerPrimary a b x) x := by
  have hd := ((Real.hasDerivAt_cos x).const_mul (a+1/2)).fun_sub
    ((Real.hasDerivAt_sin x).const_mul (b+1/2))
  exact hd.congr_deriv (by dsimp [lowerPrimary]; ring)

lemma lowerSpeed_positive {a b x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10)) : 0<lowerSpeed a b x := by
  have ht := positive_trig hx
  have hcos : 0<Real.cos x := by linarith [ht.1]
  have hfirst := mul_nonneg (sub_nonneg.mpr hs.2.1) hcos.le
  have hlast := mul_pos (show 0<b+1/2 by linarith [hs.1])
    (show 0<Real.cos x-Real.sin x by linarith [ht.1,ht.2.2.2.1])
  dsimp [lowerSpeed]
  nlinarith

lemma lowerPrimary_monotone {a b : ℝ} (hs : OuterState a b) :
    MonotoneOn (lowerPrimary a b) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (lowerPrimary_hasDerivAt a b x).continuousAt.continuousWithinAt)
    (fun x _ => lowerPrimary_hasDerivAt a b x)
    (fun _ hx => (lowerSpeed_positive hs (Ioo_subset_Icc_self hx)).le)

lemma lowerPrimary_norm {a b : ℝ} (hs : OuterState a b) (x : ℝ) :
    (lowerPrimary a b x-1/2)^2+(lowerSpeed a b x)^2=Q0 := by
  have ht := Real.sin_sq_add_cos_sq x
  dsimp [lowerPrimary,lowerSpeed]
  linear_combination hs.2.2+((a+1/2)^2+(b+1/2)^2)*ht

lemma lower_contact_domain {a b c x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10)) (hc : c≤outerAxial)
    (hcut : lowerPrimary a b x≤c) {t : ℝ} (ht : t∈Icc 0 x) :
    lowerPrimary a b t∈Icc 1 outerAxial := by
  have ht' : t∈Icc 0 (7/10) := ⟨ht.1,ht.2.trans hx.2⟩
  have hlo := lowerPrimary_monotone hs (by norm_num) ht' ht.1
  have hhi := lowerPrimary_monotone hs ht' hx ht.2
  rw [lowerPrimary_zero] at hlo
  exact ⟨by linarith [hs.1],hhi.trans (hcut.trans hc)⟩

lemma lowerSpeed_eq_primarySpeed {a b x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10))
    (hcut : lowerPrimary a b x∈Icc 1 outerAxial) :
    lowerSpeed a b x=primarySpeed (lowerPrimary a b x) := by
  have hleft := lowerSpeed_positive hs hx
  have hright := primarySpeed_data hcut
  have hnorm := lowerPrimary_norm hs x
  nlinarith

end SquaresInCircles.Eight.SecondWord.OppositeTwo
end
end
end

section
/-!
## The original weak lower source-primary owner

The original separator bounds the increasing physical contact by the original source primary
coordinate. The whole backward path stays on the same circle, and its cost increases from the
aligned point (`original_lower_source_primary`). Both equality endpoints and weak owners are
kept.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic

theorem original_lower_source_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2-x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2-x) := by
  have hcut : lowerPrimary A B x≤a := by
    have hw := lower_width hx
    norm_num [forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
    dsimp [lowerPrimary]
    linarith
  have hdom {t : ℝ} (htx : t∈Icc 0 x) :
      lowerPrimary A B t∈Icc 1 outerAxial :=
    lower_contact_domain ht hx (outer_bounds hs).2.1 hcut htx
  let f : ℝ→ℝ := fun t => Real.pi/2-t+
    PPrimaryLabel.outer (lowerPrimary A B t)-V B
  have hd {t : ℝ} (htx : t∈Icc 0 x) :
      HasDerivAt f (-1+PPrimaryLabel.d1 (lowerPrimary A B t)*lowerSpeed A B t) t := by
    have hh := (PPrimaryLabel.outer_hasDerivAt (primary_domain
      (target_primary_domain (hdom htx)))).comp t (lowerPrimary_hasDerivAt A B t)
    exact (((hasDerivAt_id' t).const_sub (Real.pi/2)).fun_add hh).sub_const (V B)
  have hmono : MonotoneOn f (Icc 0 x) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t htx => (hd htx).continuousAt.continuousWithinAt
    · exact fun t htx => hd (Ioo_subset_Icc_self htx)
    · intro t htx
      have hI := Ioo_subset_Icc_self htx
      have ht' : t∈Icc 0 (7/10) := ⟨hI.1,hI.2.trans hx.2⟩
      have hs' := lowerSpeed_eq_primarySpeed ht ht' (hdom hI)
      have hM := M_first_lower (target_primary_domain (hdom hI))
      have hv := (primarySpeed_data (hdom hI)).1
      rw [←hs'] at hv
      have hp := mul_lt_mul hM hv.le (by norm_num)
        (by linarith : 0≤PPrimaryLabel.d1 (lowerPrimary A B t))
      linarith
  have hstep := hmono ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1
  have hsource := M_monotone (target_primary_domain (hdom ⟨hx.1,le_rfl⟩))
    (primary_mem hs) hcut
  have he : PPrimaryLabel.outer a= -P b := PLabel.primary_actual hs
  rw [he] at hsource
  have hB : B∈Icc 0 (outerAxial-1) := by
    have hz := hdom ⟨le_rfl,hx.1⟩
    rw [lowerPrimary_zero] at hz
    exact ⟨ht.1,by linarith [hz.2]⟩
  have hbase := aligned_right hB
  dsimp [f] at hstep
  rw [lowerPrimary_zero] at hstep
  norm_num only [sub_zero] at hstep
  dsimp [value]
  linarith

end SquaresInCircles.Eight.SecondWord.OppositeTwo
end
end
end

section
/-!
## The original weak lower target-primary owner

The actual rotating target contact has curvature greater than 2.5.
Its aligned derivative is bounded below by the original circle-speed
product.  A single tangent parabola therefore controls the entire
physical contact and all weak original target-primary separators.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

theorem original_lower_target_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 1 a b A B (-1) 1 (Real.pi/2-x)) :
    (901/1000:ℝ)<value b B (Real.pi/2-x) := by
  have hcut : lowerPrimary a b x≤A := by
    have hw := lower_width hx
    norm_num [forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
    dsimp [lowerPrimary]
    linarith
  have hdom {t : ℝ} (htx : t∈Icc 0 x) : lowerPrimary a b t∈Icc 1 outerAxial :=
    lower_contact_domain hs hx (outer_bounds ht).2.1 hcut htx
  let f : ℝ→ℝ := fun t => Real.pi/2-t-P b+VPrimaryLabel.outer (lowerPrimary a b t)
  let df : ℝ→ℝ := fun t => -1+VPrimaryLabel.d1 (lowerPrimary a b t)*lowerSpeed a b t
  let ddf : ℝ→ℝ := fun t => VPrimaryLabel.d2 (lowerPrimary a b t)*(lowerSpeed a b t)^2+
    VPrimaryLabel.d1 (lowerPrimary a b t)*(1/2-lowerPrimary a b t)
  have hd {t : ℝ} (htx : t∈Icc 0 x) : HasDerivAt f (df t) t := by
    have hN := (VPrimaryLabel.outer_hasDerivAt (primary_domain
      (target_primary_domain (hdom htx)))).comp t (lowerPrimary_hasDerivAt a b t)
    exact (((hasDerivAt_id t).const_sub (Real.pi/2)).sub_const (P b)).add hN
  have hdd {t : ℝ} (htx : t∈Icc 0 x) : HasDerivAt df (ddf t) t := by
    have hN := (VPrimaryLabel.d1_hasDerivAt (primary_domain
      (target_primary_domain (hdom htx)))).comp t (lowerPrimary_hasDerivAt a b t)
    exact ((hN.mul (lowerSpeed_hasDerivAt a b t)).const_add (-1)).congr_deriv
      (by dsimp [ddf]; ring)
  have hcurv {t : ℝ} (htx : t∈Icc 0 x) : (5/2:ℝ)<ddf t := by
    have ht' : t∈Icc 0 (7/10) := ⟨htx.1,htx.2.trans hx.2⟩
    have he := lowerSpeed_eq_primarySpeed hs ht' (hdom htx)
    have hh := target_curvature_lower (hdom htx)
    dsimp [ddf]
    rw [he]
    nlinarith
  have hzero := hdom ⟨le_rfl,hx.1⟩
  rw [lowerPrimary_zero] at hzero
  have hbase : (227/250:ℝ)<f 0 := by
    have hj := primary_state (target_primary_domain hzero)
    have hh := aligned_left_original hs hj (le_refl (1+b))
    have he : VPrimaryLabel.outer (1+b)= -V (arc (1+b)) := VLabel.primary_actual hj
    dsimp [f]
    rw [lowerPrimary_zero,he]
    dsimp [value] at hh
    linarith
  have hfirst : -(9/50:ℝ)<df 0 := by
    have hh := targetProduct_lower hzero
    have hv := lowerSpeed_eq_primarySpeed (x := 0) hs (by norm_num)
      (by simpa only [lowerPrimary_zero] using hzero)
    rw [lowerPrimary_zero] at hv
    dsimp [df]
    rw [lowerPrimary_zero,hv]
    dsimp [targetProduct] at hh
    linarith
  have htan := curvature_tangent (κ := (5/2:ℝ))
    (show x∈Icc 0 x from ⟨hx.1,le_rfl⟩)
    (show (0:ℝ)∈Icc 0 x from ⟨le_rfl,hx.1⟩)
    (fun t htx => hd htx) (fun t htx => hdd htx) (fun t htx => (hcurv htx).le)
  have hlin := mul_nonneg (show 0≤df 0+9/50 by linarith) hx.1
  have hsq := sq_nonneg (x-9/125)
  have hf : (901/1000:ℝ)<f x := by nlinarith
  have htarget := V_primary_monotone
    (target_primary_domain (hdom ⟨hx.1,le_rfl⟩)) (primary_mem ht) hcut
  have he : VPrimaryLabel.outer A= -V B := VLabel.primary_actual ht
  rw [he] at htarget
  dsimp [f,value] at *
  linarith

end SquaresInCircles.Eight.SecondWord.OppositeTwo
end
end
end

section
/-!
## The complete original lower target-secondary short interval

The actual weak separator first places the target below its source
contact.  A zero-target source endpoint is obtained by the intermediate
value theorem between that original source and the aligned source.
The actual contact curvature and its negative endpoint derivative
concentrate the cost there; the zero-target inverse bound finishes.
No additional contact, endpoint, or strict-owner hypothesis is used.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerStrip

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

theorem original {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (1/100))
    (hm : 0≤forwardMargin 2 a b A B (-1) 1 (Real.pi/2-x)) :
    (44889/50000:ℝ)<OppositeTwo.value b B (Real.pi/2-x) := by
  have hangle := angle_mem hx
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2⟩
  have hcut : B≤contact x b := by
    have hw := lower_width hangle
    norm_num [forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
    dsimp [contact,lowerCut]
    rw [(ShortOuterOne.SameContact.actual_arc hs).1]
    linarith
  have hcontact : 0≤contact x b := ht.1.trans hcut
  have ha : 1≤a := by
    have hh := contact_upper hb hangle
    rw [(ShortOuterOne.SameContact.actual_arc hs).1] at hh
    linarith
  have ha' : a∈Icc outerDiagonal outerAxial :=
    ⟨(outer_bounds hs).1,(outer_bounds hs).2.1⟩
  have hbone := ShortOuterOne.SameContact.arc_antitone
    (primary_domain primary_one_mem) (primary_domain ha') ha
  rw [(ShortOuterOne.SameContact.actual_arc hs).2] at hbone
  change b≤bOne at hbone
  have hc : Continuous (fun y => -contact x y) := by
    dsimp [contact,lowerCut,arc]
    fun_prop
  obtain ⟨β,hβ,hzero'⟩ := intermediate_value_Icc hbone hc.continuousOn
    (show (0:ℝ)∈Icc (-contact x b) (-contact x bOne) from
      ⟨by linarith,(neg_nonneg.mpr (contact_bOne hangle))⟩)
  have hzero : contact x β=0 := by linarith
  have hβmem : β∈Icc 0 bOne := ⟨hs.1.trans hβ.1,hβ.2⟩
  have hβouter : β∈Icc 0 outerDiagonal :=
    ⟨hβmem.1,hβmem.2.trans bOne_mem.2⟩
  have hβband := zero_endpoint_band hx hβmem hzero
  have hdom {y : ℝ} (hy : y∈Icc b β) : y∈Icc 0 bOne :=
    ⟨hs.1.trans hy.1,hy.2.trans hβ.2⟩
  have houter {y : ℝ} (hy : y∈Icc b β) : y∈Icc 0 outerDiagonal :=
    ⟨(hdom hy).1,(hdom hy).2.trans bOne_mem.2⟩
  have htarget {y : ℝ} (hy : y∈Icc b β) : contact x y∈earlyTarget := by
    have hh := contact_antitone hangle (houter hy) hβouter hy.2
    rw [hzero] at hh
    exact contact_early (houter hy) hangle hh
  have hfirst : MonotoneOn (contactFirst x) (Icc b β) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun y hy =>
        (contactFirst_hasDerivAt (houter hy) (htarget hy)).continuousAt.continuousWithinAt
    · exact fun y hy =>
        contactFirst_hasDerivAt (houter (Ioo_subset_Icc_self hy))
          (htarget (Ioo_subset_Icc_self hy))
    · intro y hy
      linarith [contactSecond_lower (hdom (Ioo_subset_Icc_self hy)) hx
        (htarget (Ioo_subset_Icc_self hy))]
  have hright : contactFirst x β<0 := first_zero_negative hβband hx hzero
  have hcost : AntitoneOn (contactValue x) (Icc b β) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun y hy =>
        (contactValue_hasDerivAt (houter hy) (htarget hy)).continuousAt.continuousWithinAt
    · exact fun y hy =>
        contactValue_hasDerivAt (houter (Ioo_subset_Icc_self hy))
          (htarget (Ioo_subset_Icc_self hy))
    · intro y hy
      have hh := hfirst (Ioo_subset_Icc_self hy) ⟨hβ.1,le_rfl⟩ hy.2.le
      linarith
  have hstep := hcost ⟨le_rfl,hβ.1⟩ ⟨hβ.1,le_rfl⟩ hβ.1
  rw [zero_contact_value hβouter hangle hzero] at hstep
  have haxis := axis_lower hβband
  have hc0 := contact_early hb hangle hcontact
  have hB : B∈earlyTarget := ⟨ht.1,hcut.trans hc0.2⟩
  have hV := target_monotone hB hc0 hcut
  dsimp [contactValue,OppositeTwo.value] at *
  linarith

end SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerStrip
end
end
end

section
/-!
## The original lower target-secondary owner on its entire physical angle range

The short interval is concentrated on the original zero-target contact.
The complementary interval uses a single concave circle-support scalar.
Their common endpoint is included in both arguments.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic

theorem original_lower_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 2 a b A B (-1) 1 (Real.pi/2-x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2-x) := by
  by_cases hshort : x≤1/100
  · exact LowerStrip.original hs ht ⟨hx.1,hshort⟩ hm
  · exact LowerSupport.original_tail hs ht ⟨by linarith,hx.2⟩ hm

end SquaresInCircles.Eight.SecondWord.OppositeTwo
end
end
end

section
/-!
## Every original weak owner for the second-word opposite edge two

Both physical half-angle intervals and all four original separating axes are covered, with the
endpoint ties (`original_scalar`, `original_at_angle`). The contact concentration and the
endpoint choices come from the geometric modules of this edge.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic

theorem original_scalar {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc (-(7/10)) (7/10)) (j : Fin 4)
    (hm : 0≤forwardMargin j a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases hx0 : 0≤x
  · have hupper : x∈Icc 0 (7/10) := ⟨hx0,hx.2⟩
    fin_cases j
    · exact original_upper_source_secondary hs ht hupper hm
    · exact original_upper_target_primary hs ht hupper hm
    · exact original_upper_target_secondary hs ht hupper hm
    · exact original_upper_source_primary hs ht hupper hm
  · have hlower : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [hx.1]⟩
    have he : Real.pi/2+x=Real.pi/2-(-x) := by ring
    rw [he] at hm ⊢
    fin_cases j
    · exact LowerSecondary.original hs ht hlower hm
    · have hh := original_lower_target_primary hs ht hlower hm
      linarith
    · exact original_lower_target_secondary hs ht hlower hm
    · exact original_lower_source_primary hs ht hlower hm

theorem original_scalar_abs {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hx : |x|≤7/10) (j : Fin 4)
    (hm : 0≤forwardMargin j a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) :=
  original_scalar hs ht (abs_le.mp hx) j hm

theorem original_at_angle {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤forwardMargin j a b A B (-1) 1 φ) :
    (44889/50000:ℝ)<value b B φ := by
  have he : Real.pi/2+(φ-Real.pi/2)=φ := by ring
  have hh := original_scalar_abs hs ht hφ j (by simpa only [he] using hm)
  simpa only [he] using hh

end SquaresInCircles.Eight.SecondWord.OppositeTwo
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord

open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

def reflectedOwner (j : Fin 4) : Fin 4 := j+2

lemma margin_reflection (j : Fin 4) (a b A B σ τ φ : ℝ) :
    SquaresInCircles.Eight.forwardMargin (reflectedOwner j) A B a b (-τ) (-σ) φ=
      SquaresInCircles.Eight.forwardMargin j a b A B σ τ φ := by
  fin_cases j <;> norm_num [reflectedOwner,SquaresInCircles.Eight.forwardMargin] <;> ring

namespace OppositeTwo

theorem original_cost {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤SquaresInCircles.Eight.forwardMargin j a b A B (-1) 1 φ) :
    (44889/50000:ℝ)<SecondWord.cost 2 .outer .outer false true a b A B φ := by
  rw [cost_identity hs ht]
  exact original_at_angle hs ht hφ j hm

theorem original_reflected {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤SquaresInCircles.Eight.forwardMargin j a b A B (-1) 1 φ) :
    (44889/50000:ℝ)<SecondWord.cost 6 .outer .outer false true a b A B φ := by
  have hrev : 0≤SquaresInCircles.Eight.forwardMargin (reflectedOwner j)
      A B a b (-1) 1 φ := by
    simpa only [neg_neg] using
      (show 0≤SquaresInCircles.Eight.forwardMargin (reflectedOwner j)
        A B a b (-(1:ℝ)) (-(-1:ℝ)) φ from by
          rw [margin_reflection]
          exact hm)
  have hh := original_cost ht hs hφ (reflectedOwner j) hrev
  have he := cost_reflection (2:Vertex) .outer .outer false true A B a b φ
  norm_num [reverseEdge] at he
  rwa [←he] at hh

theorem original_role (i : Vertex) (hi : i=2 ∨ i=6)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤SquaresInCircles.Eight.forwardMargin j a b A B (-1) 1 φ) :
    threshold i<SecondWord.cost i .outer .outer false true a b A B φ := by
  rw [threshold_value]
  rcases hi with rfl | rfl
  · linarith [original_cost hs ht hφ j hm]
  · linarith [original_reflected hs ht hφ j hm]

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : i=2 ∨ i=6)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hσ : positiveOf C i=false) (hτ : positiveOf C (next i)=true)
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hi with rfl | rfl <;> norm_num [WordProblems.wrongWord]
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa [State,hs] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa [State,ht] using actual_state C (next i)
  have hm := original_margin C F hgap i j howner
  simp only [hσ,hτ,WordProblems.sign,Bool.false_eq_true,↓reduceIte,
    Rat.cast_neg,Rat.cast_one] at hm
  have hh := original_role i hi hsource htarget hφ j hm
  simpa only [SecondWord.cost,label,wrongMarker,hs,ht,hσ,hτ] using hh

/-- Every original selected separator is covered, through its forward-axis index. -/
theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : i=2 ∨ i=6)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hσ : positiveOf C i=false) (hτ : positiveOf C (next i)=true) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hi hs ht hσ hτ j howner

end OppositeTwo

end SquaresInCircles.Eight.SecondWord
end
end
end
