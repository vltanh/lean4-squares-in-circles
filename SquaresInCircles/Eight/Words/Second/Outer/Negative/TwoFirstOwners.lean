module

public import SquaresInCircles.Eight.Words.Second.Outer.FourthKernel
public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeData

/-!
# Eight squares: the first two original weak axes on the whole negative-quarter window

The target circle supplies an affine primary-coordinate decrease.  It
combines with the target label's slope to pay its full original transverse
coordinate.  The remaining angle inequality follows from a whole-interval
quadratic Taylor support.  The second lower axis implies the axial first
axis; its upper half uses the original angle and a direct small-source cut.
-/

section
/-!
## Whole-arc source and target labels for the negative quarter edge

The target slope is bounded below by its tangent parabola at `3/5`.
Its upper bound follows from convexity and its two physical endpoints.
The source chord is proved on the whole circle arc by concavity of the
affine difference.  All strict references use rational square brackets.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

lemma diagonal_fine :
    (89921406510940/100000000000000:ℝ)<outerDiagonal ∧
      outerDiagonal<89921406510941/100000000000000 := by
  have h₁ : (139921406510940/100000000000000:ℝ)<Real.sqrt (Q0/2) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num [Q0]
  have h₂ : Real.sqrt (Q0/2)<139921406510941/100000000000000 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num [Q0]
  unfold outerDiagonal
  constructor <;> linarith

lemma outer_ratioD_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (557/1000:ℝ)<ratioD b := by
  have hu := U_positive (outer_domain hb)
  have hc := pow_le_pow_left₀ hu.le (UW_bounds hb).2.1.le 3
  change (557/1000:ℝ)<Q0/(U b)^3
  apply (lt_div_iff₀ (pow_pos hu 3)).2
  norm_num [Q0]
  nlinarith

lemma T_third_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (8/5:ℝ)<TLabel.d3 b := by
  have hd := outer_ratioD_lower hb
  have hh := ratioDD_positive hb
  have hm := mul_nonneg hb.1 hh.le
  norm_num [RoleLabel.d3,TLabel]
  nlinarith

lemma T_second_monotone : MonotoneOn TLabel.d2 (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (TLabel.d2_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => TLabel.d2_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by linarith [T_third_lower (Ioo_subset_Icc_self hb)])

lemma T_six_mem : (3/5:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by constructor <;> norm_num)

lemma T_six_first : (6101/10000:ℝ)<TLabel.d1 (3/5) ∧
    TLabel.d1 (3/5)<611/1000 := by
  exact TLabel.first_chart_reference (outer_domain T_six_mem)
    (l := (411217703899/250000000000:ℝ))
    (u := (1644870815597/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])

lemma T_six_second : -(49/1000:ℝ)<TLabel.d2 (3/5) ∧
    TLabel.d2 (3/5)< -(6/125:ℝ) := by
  exact TLabel.second_chart_reference (outer_domain T_six_mem)
    (l := (411217703899/250000000000:ℝ))
    (u := (1644870815597/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])

lemma T_first_zero_bounds : (1068495/1000000:ℝ)<TLabel.d1 0 ∧
    TLabel.d1 0<133562/125000 := by
  norm_num [RoleLabel.d1,TLabel,ShortOuterOne.SameContact.arc_zero]
  constructor <;> linarith [ShortOuterZero.fine_axial_bounds.1,
    ShortOuterZero.fine_axial_bounds.2]

lemma T_first_diagonal : TLabel.d1 outerDiagonal=
    121161/50000-(5734/3125)*outerDiagonal := by
  norm_num [RoleLabel.d1,TLabel,ShortOuterOne.SameContact.arc_diagonal,ratio_diagonal]
  ring

lemma T_first_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (609/1000:ℝ)<TLabel.d1 b := by
  have ht := curvature_tangent (f := TLabel.d1) (d := TLabel.d2)
    (dd := TLabel.d3) (κ := (8/5:ℝ)) hb T_six_mem
    (fun y hy => TLabel.d1_hasDerivAt (outer_domain hy))
    (fun y hy => TLabel.d2_hasDerivAt (outer_domain hy))
    (fun y hy => (T_third_lower hy).le)
  have hs : (TLabel.d2 (3/5))^2<(49/1000:ℝ)^2 := by
    nlinarith [T_six_second.1,T_six_second.2]
  have hsq := sq_nonneg ((4/5:ℝ)*(b-3/5)+TLabel.d2 (3/5)/2)
  nlinarith [T_six_first.1]

lemma T_first_upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    TLabel.d1 b<1069/1000 := by
  have hh := positive_of_second_nonpos (f := fun t => (1069/1000:ℝ)-TLabel.d1 t)
    (d := fun t => -TLabel.d2 t) (dd := fun t => -TLabel.d3 t) hb
    (fun t ht => (TLabel.d1_hasDerivAt (outer_domain ht)).const_sub (1069/1000))
    (fun t ht => (TLabel.d2_hasDerivAt (outer_domain ht)).neg)
    (fun t ht => by linarith [T_third_lower ht])
    (by linarith [T_first_zero_bounds.2])
    (by rw [T_first_diagonal]; linarith [fine_outer_endpoint_bounds.2])
  linarith

lemma T_monotone : MonotoneOn T (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (TLabel.outer_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => TLabel.outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by linarith [T_first_lower (Ioo_subset_Icc_self hb)])

lemma T_zero : T 0=(167/10000:ℝ) := by
  norm_num [T,RoleLabel.outer,RoleLabel.eval,TLabel]

lemma T_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : (167/10000:ℝ)≤T b := by
  simpa only [T_zero] using T_monotone outer_zero_mem hb hb.1

lemma T_increment_lower {b B : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (h : b≤B) :
    (609/1000:ℝ)*(B-b)≤T B-T b := by
  have hd {t : ℝ} (ht : t∈Icc 0 outerDiagonal) :
      HasDerivAt (fun y => T y-(609/1000)*y) (TLabel.d1 t-609/1000) t := by
    have h := (TLabel.outer_hasDerivAt (outer_domain ht)).sub
      ((hasDerivAt_id' t).const_mul (609/1000:ℝ))
    exact h.congr_deriv (by ring)
  have hm := monoOn_of_hasDeriv_nonneg
    (fun t ht => (hd ht).continuousAt.continuousWithinAt)
    (fun t ht => hd (Ioo_subset_Icc_self ht))
    (fun t ht => by linarith [T_first_lower (Ioo_subset_Icc_self ht)])
  linarith [hm hb hB h]

lemma T_increment_upper {b B : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (h : b≤B) :
    T B-T b≤(1069/1000:ℝ)*(B-b) := by
  have hd {t : ℝ} (ht : t∈Icc 0 outerDiagonal) :
      HasDerivAt (fun y => (1069/1000)*y-T y) (1069/1000-TLabel.d1 t) t := by
    have h := ((hasDerivAt_id' t).const_mul (1069/1000:ℝ)).sub
      (TLabel.outer_hasDerivAt (outer_domain ht))
    exact h.congr_deriv (by ring)
  have hm := monoOn_of_hasDeriv_nonneg
    (fun t ht => (hd ht).continuousAt.continuousWithinAt)
    (fun t ht => hd (Ioo_subset_Icc_self ht))
    (fun t ht => by linarith [T_first_upper (Ioo_subset_Icc_self ht)])
  linarith [hm hb hB h]

lemma P_zero : P 0=(1239/50000:ℝ) := by
  norm_num [P,RoleLabel.outer,RoleLabel.eval,PLabel]

lemma P_chord {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    P b≤1239/50000+(853/1000)*b := by
  let f : ℝ→ℝ := fun y => (1239/50000:ℝ)+(853/1000)*y-P y
  have hc : ConcaveOn ℝ (Icc 0 outerDiagonal) f :=
    concave_of_deriv2
      (fun y hy => by
        convert (PLabel.affine_difference_hasDerivAt (853/1000) (outer_domain hy)).const_add
          (1239/50000) using 1
        dsimp [f,P]; ring_nf)
      (fun y hy => (PLabel.d1_hasDerivAt (outer_domain hy)).const_sub (853/1000))
      (fun y hy => neg_nonpos.mpr (P_second_positive hy).le)
  have hz : f 0=0 := by dsimp [f]; rw [P_zero]; ring
  have he : 0<f outerDiagonal := by
    have hp : 0<outerDiagonal := by linarith [fine_outer_endpoint_bounds.2]
    have hh : 0<(4346/50000)*outerDiagonal-1543/20000 := by
      linarith [fine_outer_endpoint_bounds.2]
    have hm := mul_pos hp hh
    dsimp [f,P,RoleLabel.outer,RoleLabel.eval,PLabel]
    rw [ShortOuterOne.SameContact.arc_diagonal]
    nlinarith
  by_cases h : b=0
  · subst b
    rw [P_zero]
    simp
  · have hh := concave_pos_of_zero_left hc ⟨lt_of_le_of_ne hb.1 (Ne.symm h),hb.2⟩ hz he
    dsimp [f] at hh
    linarith

lemma P_diagonal_upper : P outerDiagonal<(79091/100000:ℝ) := by
  have hc := UW_circle (outer_domain
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩))
  norm_num [U,W,ShortOuterOne.SameContact.arc_diagonal,Q0] at hc
  dsimp [P,RoleLabel.outer,RoleLabel.eval,PLabel]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  nlinarith [diagonal_fine.2]

lemma T_diagonal_upper : T outerDiagonal<(67949/100000:ℝ) := by
  have hc := UW_circle (outer_domain
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩))
  norm_num [U,W,ShortOuterOne.SameContact.arc_diagonal,Q0] at hc
  dsimp [T,RoleLabel.outer,RoleLabel.eval,TLabel]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  nlinarith [diagonal_fine.2]

lemma T_upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    T b<(67949/100000:ℝ) :=
  (T_monotone hb ⟨outer_zero_mem.2,le_rfl⟩ hb.2).trans_lt T_diagonal_upper

lemma T_second_early {b : ℝ} (hb : b∈Icc 0 (3/5)) :
    TLabel.d2 b< -(6/125:ℝ) :=
  (T_second_monotone ⟨hb.1,hb.2.trans T_six_mem.2⟩ T_six_mem hb.2).trans_lt
    T_six_second.2

lemma T_third_small {b : ℝ} (hb : b∈Icc 0 (101/1000)) :
    TLabel.d3 b<(427/250:ℝ) := by
  have ht : (101/1000:ℝ)∈Icc 0 outerDiagonal :=
    Asymmetric.rational_outer_mem (by constructor <;> norm_num)
  have hu := shifted_chart_reference (outer_domain ht)
    (l := (1885311380117/1000000000000:ℝ))
    (u := (942655690059/500000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1885311380117/1000000000000)
    hu.1.le 5
  have he := TLabel.third_numerator (outer_domain ht)
  have hu5 := pow_pos (U_positive (outer_domain ht)) 5
  have hr : TLabel.d3 (101/1000)<(427/250:ℝ) := by
    have hv : -3*Q0*(TLabel.s*Q0+(TLabel.p-TLabel.s/2)*W (101/1000))=
        101672815709673/2500000000000 := by
      norm_num [TLabel,W,Q0]
    rw [hv] at he
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hu5.le
    norm_num at hp
    linarith
  exact (T_third_monotone ⟨hb.1,hb.2.trans ht.2⟩ ht hb.2).trans_lt hr

end SquaresInCircles.Eight.SecondWord
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma target_primary_decrease {A B : ℝ} (ht : OuterState A B) :
    A+(261/1000)*B≤outerAxial := by
  have hA := primary_mem ht
  have hD : 0≤outerAxial-A := sub_nonneg.mpr hA.2
  have hz := (ShortOuterOne.SameContact.arc_state outer_zero_mem).2.2
  rw [ShortOuterOne.SameContact.arc_zero] at hz
  have he : (outerAxial-A)*(outerAxial+A+1)=B^2+B := by
    linear_combination hz-ht.2.2
  have hupper : outerAxial+A+1≤383/100 := by
    linarith [hA.2,outer_endpoint_bounds.2.1]
  have hm := mul_le_mul_of_nonneg_left hupper hD
  nlinarith [sq_nonneg B,ht.1]

def firstBase (x : ℝ) : ℝ :=
  Real.pi/2-x-1239/50000+167/10000+853/2000+
    (853/2000)*Real.sin x-(853/1000)*(outerAxial-1/2)*Real.cos x

lemma first_base_lower {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (19/20:ℝ)<firstBase x := by
  have ht := positive_trig hx
  have hs := positive_taylor_reserves hx
  have hc0 : 0≤Real.cos x := by linarith [ht.1]
  have hrad : (outerAxial-1/2)*Real.cos x≤(183/200)*Real.cos x := by
    apply mul_le_mul_of_nonneg_right _ hc0
    linarith [outer_endpoint_bounds.2.1]
  have hfactor : 0≤(12323/20000:ℝ)-(183/500)*(x+7/10) := by
    linarith [hx.2]
  have hpoly := mul_nonneg (show 0≤(7/10:ℝ)-x by linarith [hx.2]) hfactor
  dsimp [firstBase]
  nlinarith [pi_hand_enclosure.1,sq_nonneg x]

theorem original_lower_source_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) (-1) (Real.pi/2-x)) :
    (19/20:ℝ)<value b B (Real.pi/2-x) := by
  have hw := lower_width hx
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
  have hc := positive_trig hx
  have hP := P_chord (source_mem hs)
  have hT := T_increment_lower outer_zero_mem (source_mem ht) ht.1
  rw [T_zero] at hT
  have hA := mul_le_mul_of_nonneg_right (target_primary_decrease ht)
    (show 0≤Real.cos x by linarith [hc.1])
  have hpay : 0≤(609/1000:ℝ)+(853/1000)*(261/1000)*Real.cos x-
      (853/1000)*Real.sin x := by
    linarith [hc.1,hc.2.2.2.1]
  have hcharge := mul_nonneg ht.1 hpay
  have hbase := first_base_lower hx
  dsimp [value,firstBase] at *
  nlinarith

theorem original_upper_source_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) (-1) (Real.pi/2+x)) :
    (19/20:ℝ)<value b B (Real.pi/2+x) := by
  have hu := upper_width hx
  have hl := lower_width hx
  have hBS := mul_nonneg ht.1 (positive_trig hx).2.2.1
  have hminus : 0≤Eight.forwardMargin 0 a b A B (-1) (-1) (Real.pi/2-x) := by
    norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,Real.sin_add,Real.cos_add,
      hu,hl] at hm ⊢
    nlinarith
  have hh := original_lower_source_secondary hs ht hx hminus
  dsimp [value] at *
  linarith [hx.1]

lemma lower_second_implies_axial_first {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) (-1) (Real.pi/2-x)) :
    0≤Eight.forwardMargin 0 a b outerAxial 0 (-1) (-1) (Real.pi/2-x) := by
  have hw := lower_width hx
  have hc := positive_trig hx
  have hsin0 := hc.2.2.1
  have hcos0 : 0<Real.cos x := by linarith [hc.1]
  have ha := mul_le_mul_of_nonneg_right (primary_mem hs).1 hsin0
  have hA := (primary_mem ht).2
  have hcut : b*Real.cos x≤outerAxial-outerDiagonal*Real.sin x-
      (1+Real.cos x+Real.sin x)/2 := by
    norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
    linarith
  have hprod := mul_le_mul_of_nonneg_right
    (show outerAxial-1/2≤(183/200:ℝ) by linarith [outer_endpoint_bounds.2.1]) hsin0
  have hbracket : 0≤outerDiagonal+1/2-Real.cos x/2-
      (outerAxial-1/2)*Real.sin x := by
    linarith [fine_outer_endpoint_bounds.2,hc.2.1,hc.2.2.2.1]
  have hpay := mul_nonneg hsin0 hbracket
  have hid : (outerAxial*Real.cos x-(1+Real.cos x+Real.sin x)/2)*Real.cos x-
      (outerAxial-outerDiagonal*Real.sin x-(1+Real.cos x+Real.sin x)/2)=
        Real.sin x*(outerDiagonal+1/2-Real.cos x/2-
          (outerAxial-1/2)*Real.sin x) := by
    linear_combination (outerAxial-1/2)*(Real.sin_sq_add_cos_sq x)
  have hb : b≤outerAxial*Real.cos x-(1+Real.cos x+Real.sin x)/2 := by
    nlinarith
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw]
  linarith

theorem original_lower_target_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) (-1) (Real.pi/2-x)) :
    (19/20:ℝ)<value b B (Real.pi/2-x) := by
  have hz : OuterState outerAxial 0 := by
    simpa only [ShortOuterOne.SameContact.arc_zero] using
      ShortOuterOne.SameContact.arc_state outer_zero_mem
  have hf := original_lower_source_secondary hs hz hx
    (lower_second_implies_axial_first hs ht hx hm)
  have hT := T_lower (source_mem ht)
  dsimp [value] at *
  rw [T_zero] at hf
  linarith

lemma upper_second_small_source {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (11/100))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) (-1) (Real.pi/2+x)) :
    b<3/5 := by
  have hcap : x∈Icc 0 (7/10) := ⟨hx.1,by linarith [hx.2]⟩
  have hw := upper_width hcap
  have htrig := positive_trig hcap
  have hsine : Real.sin x≤11/100 := htrig.2.2.2.2.1.trans hx.2
  have hcosine : (19879/20000:ℝ)≤Real.cos x := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := x)
    have hsq := pow_le_pow_left₀ hx.1 hx.2 2
    nlinarith
  have hprod := mul_le_mul (primary_mem hs).2 hsine htrig.2.2.1
    (by linarith [outer_endpoint_bounds.1] : 0≤outerAxial)
  have hA := (primary_mem ht).2
  have hbpos := hs.1
  have hcosprod := mul_le_mul_of_nonneg_left hcosine hbpos
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  nlinarith [outer_endpoint_bounds.2.1,htrig.2.2.2.2.2]

theorem original_upper_target_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) (-1) (Real.pi/2+x)) :
    (9/10:ℝ)<value b B (Real.pi/2+x) := by
  have hT := T_lower (source_mem ht)
  by_cases hsmall : x≤11/100
  · have hb := upper_second_small_source hs ht ⟨hx.1,hsmall⟩ hm
    have hP := P_chord (source_mem hs)
    dsimp [value]
    linarith [pi_hand_enclosure.1,hx.1]
  · have hP := P_monotone (source_mem hs) ⟨outer_zero_mem.2,le_rfl⟩ (source_mem hs).2
    have hp := P_diagonal_upper
    dsimp [value]
    linarith [pi_hand_enclosure.1]

end SquaresInCircles.Eight.SecondWord.NegativeTwo
end
end
end
