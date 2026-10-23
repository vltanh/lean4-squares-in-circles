module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoTargetPrimaryLabel

/-!
# A finite circle comparison for the original upper target-primary axis

The weak original separator bounds the transverse displacement from
alignment.  A single circle support pays that displacement by the
angular gain.  If the target primary height is below one, the primary
label tangent pays its simultaneous loss.  No contact minimum or
endpoint selection is assumed.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def displacement (b : ℝ) : ℝ := U b-1+(7/20)*W b

lemma P_first_lower_actual {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (773/1000:ℝ)<PLabel.d1 b := by
  have ha := (outer_bounds (ShortOuterOne.SameContact.arc_state hb)).2.1
  have hr := outer_ratio_bounds hb
  have hm := mul_nonneg hb.1 (show 0≤ratio b by linarith [hr.1])
  dsimp [RoleLabel.d1,PLabel]
  nlinarith [outer_endpoint_bounds.2.1]

lemma P_first_increasing : MonotoneOn PLabel.d1 (Icc 0 outerDiagonal) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun b hb => (PLabel.d1_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt
  · exact fun b hb => PLabel.d1_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb))
  · intro b hb
    have hB := Ioo_subset_Icc_self hb
    have hr := outer_ratio_bounds hB
    have hm := mul_nonneg hB.1 hr.2.2.1.le
    dsimp [RoleLabel.d2,PLabel]
    nlinarith [hr.1]

lemma P_increasing : MonotoneOn P (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (PLabel.outer_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => PLabel.outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by linarith [P_first_lower_actual (Ioo_subset_Icc_self hb)])

lemma P_affine_difference_hasDerivAt (c : ℝ) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (fun t => c*t-P t) (c-PLabel.d1 b) b := by
  convert ((hasDerivAt_id b).const_mul c).sub
    (PLabel.outer_hasDerivAt (outer_domain hb)) using 1 <;> dsimp [P] <;> ring

lemma P_chord_at {l b : ℝ} (hl : l∈Icc 0 outerDiagonal) (hb : b∈Icc 0 outerDiagonal)
    (hlb : l≤b) : P b-P l≤PLabel.d1 b*(b-l) := by
  have hdom {t : ℝ} (ht : t∈Icc l b) : t∈Icc 0 outerDiagonal :=
    ⟨hl.1.trans ht.1,ht.2.trans hb.2⟩
  have hm : MonotoneOn (fun t => PLabel.d1 b*t-P t) (Icc l b) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t ht => (P_affine_difference_hasDerivAt (PLabel.d1 b) (hdom ht)).continuousAt.continuousWithinAt
    · exact fun t ht => P_affine_difference_hasDerivAt (PLabel.d1 b) (hdom (Ioo_subset_Icc_self ht))
    · intro t ht
      linarith [P_first_increasing (hdom (Ioo_subset_Icc_self ht)) hb ht.2.le]
  have hh := hm ⟨le_rfl,hlb⟩ ⟨hlb,le_rfl⟩ hlb
  nlinarith

lemma target_primary_loss_below_one {A : ℝ} (hA : A∈Icc outerDiagonal 1) :
    VPrimaryLabel.outer 1-VPrimaryLabel.outer A≤(11/25)*(1-A) := by
  have hdom {t : ℝ} (ht : t∈Icc A 1) : t∈Icc outerDiagonal outerAxial :=
    ⟨hA.1.trans ht.1,ht.2.trans primary_one_mem.2⟩
  have hd {t : ℝ} (ht : t∈Icc A 1) :
      HasDerivAt (fun s => (11/25)*s-VPrimaryLabel.outer s)
        (11/25-VPrimaryLabel.d1 t) t := by
    convert ((hasDerivAt_id t).const_mul (11/25)).sub
      (VPrimaryLabel.outer_hasDerivAt (primary_domain (hdom ht))) using 1 <;> ring
  have hm : MonotoneOn (fun s => (11/25)*s-VPrimaryLabel.outer s) (Icc A 1) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t ht => (hd ht).continuousAt.continuousWithinAt
    · exact fun t ht => hd (Ioo_subset_Icc_self ht)
    · intro t ht
      have hh := V_primary_first_monotone (hdom (Ioo_subset_Icc_self ht))
        primary_one_mem ht.2.le
      linarith [V_primary_one_first.2]
  have hh := hm ⟨le_rfl,hA.2⟩ ⟨hA.2,le_rfl⟩ hA.2
  nlinarith

lemma displacement_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : 0<displacement b := by
  dsimp [displacement]
  linarith [(UW_bounds hb).1,(UW_bounds hb).2.2.1]

lemma weighted_displacement {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    PLabel.d1 b*displacement b<981/1000 := by
  have hu := UW_bounds hb
  have hc := UW_circle (outer_domain hb)
  have hs := sq_nonneg ((51/100)*U b-W b)
  have hsupport : U b+(51/100)*W b<223/100 := by
    norm_num [Q0] at hc
    nlinarith
  have hA : PLabel.d1 b<53/80+(223/1000)*W b := by
    dsimp [W]
    linarith [P_first_affine hb]
  have hApos : 0<53/80+(223/1000)*W b := by linarith [hu.2.2.1]
  have hD : displacement b<123/100-(4/25)*W b := by
    dsimp [displacement]
    linarith
  have hfirst := mul_lt_mul_of_pos_right hA (displacement_positive hb)
  have hsecond := mul_lt_mul_of_pos_left hD hApos
  have hpoly := mul_nonneg
    (show 0≤7/5-W b by linarith [hu.2.2.2])
    (show 0≤16829/100000-(223/6250)*(7/5+W b) by linarith [hu.2.2.2])
  nlinarith

lemma upper_primary_displacement {a b A B x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 1 a b A B (-1) 1 (Real.pi/2+x)) :
    b+1-A≤displacement b*x := by
  have hw := upper_width hx
  have hcut : upperPrimary a b x≤A := by
    norm_num [forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
    dsimp [upperPrimary]
    linarith
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2⟩
  have hu : 0≤U b-1 := by linarith [(UW_bounds hb).1]
  have hW : 0≤W b := by linarith [(UW_bounds hb).2.2.1]
  have hcos := cos_lower_two hx.1
  have hsin := mul_le_mul_of_nonneg_left (positive_trig hx).2.2.2.2.1 hu
  have hquadratic := mul_nonneg hx.1 (show 0≤7/10-x by linarith [hx.2])
  have hcircle := mul_nonneg hW (show 0≤(7/20)*x-(1-Real.cos x) by nlinarith)
  dsimp [upperPrimary] at hcut
  rw [←(ShortOuterOne.SameContact.actual_arc hs).1] at hcut
  change 1/2+W b*Real.cos x-(U b-1)*Real.sin x≤A at hcut
  dsimp [displacement,W] at *
  nlinarith

/-- The original weak upper target-primary owner is closed by a finite
circle displacement comparison, including both primary-height regimes. -/
theorem original_upper_target_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 1 a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2⟩
  have hdisp := upper_primary_displacement hs hx hm
  have hp : 0≤PLabel.d1 b := by linarith [P_first_lower_actual hb]
  have hpaid := mul_le_mul_of_nonneg_right (weighted_displacement hb).le hx.1
  have hstep := mul_le_mul_of_nonneg_left hdisp hp
  by_cases hA : 1≤A
  · have hbase : A-1∈Icc 0 outerDiagonal := by
      refine ⟨by linarith,?_⟩
      linarith [(outer_bounds ht).2.1,outer_endpoint_bounds.2.1,fine_outer_endpoint_bounds.2]
    have halign := aligned_left_original (ShortOuterOne.SameContact.arc_state hbase) ht
      (show 1+(A-1)≤A by linarith)
    by_cases hsource : b≤A-1
    · have hP := P_increasing hb hbase hsource
      dsimp [value] at *
      linarith
    · have hP := P_chord_at hbase hb (by linarith)
      dsimp [value] at *
      nlinarith
  · have hApr : A∈Icc outerDiagonal 1 := ⟨(outer_bounds ht).1,by linarith⟩
    have htarget := target_primary_loss_below_one hApr
    have hactual : VPrimaryLabel.outer A= -V B := VLabel.primary_actual ht
    have hone : VPrimaryLabel.outer 1= -V bOne := by
      simpa [VPrimaryLabel,bOne] using VLabel.primary_actual (primary_state primary_one_mem)
    rw [hactual,hone] at htarget
    have hsource := P_chord_at outer_zero_mem hb hb.1
    have hgap := mul_le_mul_of_nonneg_right
      (show (11/25:ℝ)≤PLabel.d1 b by linarith [P_first_lower_actual hb])
      (show 0≤1-A by linarith)
    have halign := reverse_aligned_axial_value
    dsimp [value] at *
    nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo
