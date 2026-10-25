module

public import SquaresInCircles.Eight.Words.Second.Outer.MinimumCalculus
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroLReferences

/-!
# Eight squares: label shapes and the small-angle support in the symmetric zero edge

The whole-arc third derivative, its tangent at one half, the two
restricted chords, and the single support tangent are kept separate.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratioD ratioDD)

open StationaryPrimitives (Interval)

private lemma r82_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r82_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl
private lemma r82_mp_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).lo = S.lo := by subst e; rfl
private lemma r82_mp_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).hi = S.hi := by subst e; rfl

private lemma r82_rootAt_lo {b : ℝ} (hb : b∈Icc 0 (9/10)) : (Reference.rootAt b hb).lo =
    (OppositeThree.ReferenceAlgebra.rootThree (Interval.point (Q0-(b+1/2)^2)) (2-b/2)
      (by linarith [hb.2]) (by norm_num [Interval.point,Q0]; nlinarith [hb.1,hb.2])).lo := by
  unfold Reference.rootAt
  rw [r82_mpr_lo, r82_mp_lo]
  all_goals simp [U,ShortOuterOne.SameContact.arc]
private lemma r82_rootAt_hi {b : ℝ} (hb : b∈Icc 0 (9/10)) : (Reference.rootAt b hb).hi =
    (OppositeThree.ReferenceAlgebra.rootThree (Interval.point (Q0-(b+1/2)^2)) (2-b/2)
      (by linarith [hb.2]) (by norm_num [Interval.point,Q0]; nlinarith [hb.1,hb.2])).hi := by
  unfold Reference.rootAt
  rw [r82_mpr_hi, r82_mp_hi]
  all_goals simp [U,ShortOuterOne.SameContact.arc]

private lemma r82_coordinate_eq {y : ℝ} : ShortOuterOne.SameContact.arc y = U y-1/2 := by
  dsimp [U]; ring
private lemma r82_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (OppositeThree.ReferenceAlgebra.coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r82_mpr_lo r82_coordinate_eq (congrArg _ r82_coordinate_eq) _
private lemma r82_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (OppositeThree.ReferenceAlgebra.coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r82_mpr_hi r82_coordinate_eq (congrArg _ r82_coordinate_eq) _

attribute [local simp ↓] r82_rootAt_lo r82_rootAt_hi r82_coordinate_lo r82_coordinate_hi

lemma half_references : (781/1250:ℝ)<LLabel.d1 (1/2) ∧
    -(311/10000:ℝ)<LLabel.d2 (1/2) ∧ LLabel.d2 (1/2)<0 := by
  have h1 := (Reference.firstAt LLabel (1/2) (by norm_num)).mem.1
  have h2 := (Reference.secondAt LLabel (1/2) (by norm_num)).mem
  have r1 : (781/1250:ℝ)<(Reference.firstAt LLabel (1/2) (by norm_num)).lo := by
    opposite_reference_arithmetic
  have r2 : -(311/10000:ℝ)<(Reference.secondAt LLabel (1/2) (by norm_num)).lo := by
    opposite_reference_arithmetic
  have r3 : (Reference.secondAt LLabel (1/2) (by norm_num)).hi<0 := by
    opposite_reference_arithmetic
  exact ⟨r1.trans_le h1,r2.trans_le h2.1,h2.2.trans_lt r3⟩

lemma third_strong {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (2:ℝ)<LLabel.d3 b := by
  have hu := U_positive (outer_domain hb)
  have hc := UW_circle (outer_domain hb)
  have hU : U b<2 := by
    norm_num [Q0] at hc
    nlinarith [sq_nonneg (W b)]
  have hU3 : (U b)^3<(2:ℝ)^3 := by gcongr
  have hD : (39/80:ℝ)<ratioD b := by
    change (39/80:ℝ)<Q0/(U b)^3
    apply (lt_div_iff₀ (pow_pos hu 3)).2
    norm_num [Q0] at hU3 ⊢
    linarith
  have hDD := ratioDD_positive hb
  have hp := mul_nonneg hb.1 hDD.le
  norm_num [RoleLabel.d3,LLabel]
  nlinarith

lemma first_strong_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (1249/2000:ℝ)<LLabel.d1 b := by
  have hh := curvature_tangent (f := LLabel.d1) (d := LLabel.d2)
    (dd := LLabel.d3) (κ := 2) hb L_half_mem
    (fun t ht => LLabel.d1_hasDerivAt (outer_domain ht))
    (fun t ht => LLabel.d2_hasDerivAt (outer_domain ht))
    (fun t ht => (third_strong ht).le)
  have hhalf := half_references
  have hsq : (LLabel.d2 (1/2))^2<(311/10000:ℝ)^2 := by
    nlinarith [hhalf.2.1,hhalf.2.2]
  nlinarith [sq_nonneg (b-1/2+LLabel.d2 (1/2)/2)]

lemma first_upper_between {l u b M : ℝ} (hl : l∈Icc 0 outerDiagonal)
    (hu : u∈Icc 0 outerDiagonal) (hb : b∈Icc l u)
    (hleft : LLabel.d1 l<M) (hright : LLabel.d1 u<M) : LLabel.d1 b<M := by
  have hdom {t : ℝ} (ht : t∈Icc l u) : t∈Icc 0 outerDiagonal :=
    ⟨hl.1.trans ht.1,ht.2.trans hu.2⟩
  have hc : ConcaveOn ℝ (Icc l u) (fun t => M-LLabel.d1 t) :=
    concave_of_deriv2
      (fun t ht => (LLabel.d1_hasDerivAt (outer_domain (hdom ht))).const_sub M)
      (fun t ht => (LLabel.d2_hasDerivAt (outer_domain (hdom ht))).neg)
      (fun t ht => neg_nonpos.mpr (L_third_positive (hdom ht)).le)
  have hh := concave_gt_of_endpoints hc hb
    (sub_pos.mpr hleft) (sub_pos.mpr hright)
  linarith

lemma first_middle_upper {b : ℝ} (hb : b∈Icc (1/10:ℝ) (17/20)) :
    LLabel.d1 b<51/50 :=
  first_upper_between (Asymmetric.rational_outer_mem (by norm_num))
    (Asymmetric.rational_outer_mem (by norm_num)) hb L_tenth_first L_85_first

lemma first_inner_upper {b : ℝ} (hb : b∈Icc (1/5:ℝ) (19/25)) :
    LLabel.d1 b<17/20 :=
  first_upper_between (Asymmetric.rational_outer_mem (by norm_num))
    (Asymmetric.rational_outer_mem (by norm_num)) hb L_fifth_first L_76_first

lemma first_outside_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hout : b≤2/5 ∨ 3/5≤b) : (649/1000:ℝ)<LLabel.d1 b := by
  rcases hout with hlo | hhi
  · have hh := L_first_early_antitone
      ⟨hb.1,by linarith⟩ (by norm_num : (2/5:ℝ)∈Icc 0 (1/2)) hlo
    exact L_four_first.trans_le hh
  · have hh := L_first_late_monotone
      ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num :
        (3/5:ℝ)∈Icc 0 (899/1000))).2⟩ ⟨by linarith,hb.2⟩ hhi
    exact L_six_first.trans_le hh

lemma small_chord {B : ℝ} (hB : B∈Icc (0:ℝ) (3/20)) :
    LLabel.outer 0+charge*B≤LLabel.outer B := by
  let f : ℝ→ℝ := fun t => LLabel.outer t-LLabel.outer 0-charge*t
  have hdom {t : ℝ} (ht : t∈Icc (0:ℝ) (3/20)) : t∈Icc 0 outerDiagonal :=
    Asymmetric.rational_outer_mem ⟨ht.1,by linarith [ht.2]⟩
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (3/20)) f :=
    concave_of_deriv2
      (fun t ht => ((LLabel.outer_hasDerivAt (outer_domain (hdom ht))).sub_const
        (LLabel.outer 0)).sub (((hasDerivAt_id' t).const_mul charge).congr_deriv (mul_one _)))
      (fun t ht => (LLabel.d1_hasDerivAt (outer_domain (hdom ht))).sub_const charge)
      (fun t ht => (L_second_early ⟨ht.1,by linarith [ht.2]⟩).le)
  have hh := hc.min_le_of_mem_Icc (by norm_num) (by norm_num) hB
  have hleft : f 0=0 := by simp [f]
  have hright : 0≤f (3/20) := by
    dsimp [f]
    linarith [L_small_chord_reference]
  rw [hleft,min_eq_left hright] at hh
  dsimp [f] at hh
  linarith

lemma support_early {b : ℝ} (hb : b∈Icc (0:ℝ) (3/5)) :
    -(15957/100000:ℝ)<LLabel.outer b-charge*b := by
  have hdom {t : ℝ} (ht : t∈Icc (0:ℝ) (3/5)) : t∈Icc 0 outerDiagonal :=
    Asymmetric.rational_outer_mem ⟨ht.1,by linarith [ht.2]⟩
  have hh := MinimumCalculus.endpoint_minimum
    (f := fun t => LLabel.outer t-charge*t)
    (d := fun t => LLabel.d1 t-charge) (dd := LLabel.d2) (ddd := LLabel.d3) hb
    (fun t ht => (LLabel.outer_hasDerivAt (outer_domain (hdom ht))).sub
      (((hasDerivAt_id' t).const_mul charge).congr_deriv (mul_one _)))
    (fun t ht => (LLabel.d1_hasDerivAt (outer_domain (hdom ht))).sub_const charge)
    (fun t ht => LLabel.d2_hasDerivAt (outer_domain (hdom ht)))
    (fun t ht => (L_third_positive (hdom ht)).le)
    (by dsimp [charge]; linarith [L_six_first_upper])
  have hzero : -(15957/100000:ℝ)<LLabel.outer 0-charge*0 := by
    norm_num [RoleLabel.outer,RoleLabel.eval,LLabel]
  exact (lt_min hzero support_references.1).trans_le hh

lemma support_late {b : ℝ} (hb : b∈Icc (3/5:ℝ) outerDiagonal) :
    -(15957/100000:ℝ)<LLabel.outer b-charge*b := by
  have hdom {t : ℝ} (ht : t∈Icc (3/5:ℝ) outerDiagonal) : t∈Icc 0 outerDiagonal :=
    ⟨by linarith [ht.1],ht.2⟩
  have hcurv {t : ℝ} (ht : t∈Icc (3/5:ℝ) outerDiagonal) :
      (1/2:ℝ)<LLabel.d2 t :=
    L_six_second.trans_le (L_second_monotone
      (Asymmetric.rational_outer_mem (by norm_num)) (hdom ht) ht.1)
  have hh := curvature_tangent (f := fun t => LLabel.outer t-charge*t)
    (d := fun t => LLabel.d1 t-charge) (dd := LLabel.d2) (κ := (1/2:ℝ)) hb
    (show (17/20:ℝ)∈Icc (3/5:ℝ) outerDiagonal from
      ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num)).2⟩)
    (fun t ht => (LLabel.outer_hasDerivAt (outer_domain (hdom ht))).sub
      (((hasDerivAt_id' t).const_mul charge).congr_deriv (mul_one _)))
    (fun t ht => (LLabel.d1_hasDerivAt (outer_domain (hdom ht))).sub_const charge)
    (fun t ht => (hcurv ht).le)
  have hd := abs_lt.mp support_references.2.2
  have hsq : (LLabel.d1 (17/20)-charge)^2<(1/200:ℝ)^2 := by nlinarith
  nlinarith [support_references.2.1,
    sq_nonneg ((b-17/20)/2+(LLabel.d1 (17/20)-charge))]

lemma support_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    -(15957/100000:ℝ)<LLabel.outer b-charge*b := by
  by_cases he : b≤3/5
  · exact support_early ⟨hb.1,he⟩
  · exact support_late ⟨by linarith,hb.2⟩

end SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
