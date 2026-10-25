module

public import SquaresInCircles.Eight.Words.Second.Outer.HigherCalculus
public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds

/-!
# Eight squares: whole-arc source and target labels for the negative quarter edge

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
          (1239/50000) using 1 <;> dsimp [f,P] <;> ring)
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
