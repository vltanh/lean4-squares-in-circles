module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeUpperTargetCurvature

/-!
# One target concavity bound on the entire primary rectangle

The middle numerator of the third derivative is negative everywhere.
The two remaining positive terms are bounded on the complete rectangle,
and the literal `L'''` endpoint exceeds their sum.  The fixed left
target curvature is negative, hence so is every later target curvature.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.UpperTarget
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

lemma third_negative {b B : ℝ} (hb : b∈Icc 0 (1/10))
    (hB : B∈Icc (83/125) outerDiagonal) : third b B<0 := by
  have hg := rectangle_geometry hb hB
  have hBf := target_domain hB
  have hu := U_positive (outer_domain hBf)
  have hv : 0<speed b B := by linarith [hg.2.2.2.2]
  have hr := outer_ratio_bounds hBf
  have hr0 : 0<ratio B := by linarith [hr.1]
  have hz0 : 0<z B := by linarith [hg.2.2.1]
  have hU3 := pow_lt_pow_left₀ hu.le hg.2.1 (by norm_num : (3:ℕ)≠0)
  have hD : (19/20:ℝ)<ratioD B := by
    change (19/20:ℝ)<Q0/(U B)^3
    apply (lt_div_iff₀ (pow_pos hu 3)).2
    norm_num [Q0] at *
    nlinarith
  have hmiddleNum : (ratio B)^2-3*z B*ratioD B<0 := by
    have hp := mul_lt_mul hg.2.2.1 hD (by norm_num) hz0.le
    nlinarith [hr.2.1]
  have hmiddle : ratio B*((ratio B)^2-3*z B*ratioD B)/(speed b B)^3<0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hr0 hmiddleNum) (pow_pos hv 3)
  have hU5 := pow_lt_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000)
    hg.1 (by norm_num : (5:ℕ)≠0)
  have hden := mul_lt_mul hU5 hg.2.2.2.2 (by norm_num)
    (pow_pos hu 5).le
  have hW : W B<(7/5:ℝ) := by
    dsimp [W]
    linarith [hB.2,outer_endpoint_bounds.2.2.2]
  have hfirst : ratioDD B/speed b B<(37/10:ℝ) := by
    change (3*Q0*W B/(U B)^5)/speed b B<(37/10:ℝ)
    rw [div_div]
    apply (div_lt_iff₀ (mul_pos (pow_pos hu 5) hv)).2
    norm_num [Q0] at *
    nlinarith
  have hv5 := pow_lt_pow_left₀ (by norm_num : (0:ℝ)≤17/20)
    hg.2.2.2.2 (by norm_num : (5:ℕ)≠0)
  have hz2 : (z B)^2<(601/1000:ℝ)^2 := by nlinarith [hg.2.2.2.1]
  have hr3 : (ratio B)^3≤1 := by
    have hh := pow_le_pow_left₀ hr0.le hr.2.1 3
    simpa using hh
  have hprod := mul_le_mul hz2.le hr3 (pow_nonneg hr0.le 3) (by norm_num)
  have hlast : 3*(z B)^2*(ratio B)^3/(speed b B)^5<(5/2:ℝ) := by
    apply (div_lt_iff₀ (pow_pos hv 5)).2
    norm_num at hprod hv5
    nlinarith
  have hL := target_start_third.trans_le
    (L_third_monotone target_start_mem hBf hB.1)
  dsimp [third]
  linarith

lemma target_start_ratio : (3637/5000:ℝ)<ratio (83/125) := by
  have hu := U_positive (outer_domain target_start_mem)
  change (3637/5000:ℝ)<(83/125+1/2)/U (83/125)
  apply (lt_div_iff₀ hu).2
  nlinarith [target_start_U.2]

lemma target_start_ratioD : ratioD (83/125)<(239/250:ℝ) := by
  have hu := U_positive (outer_domain target_start_mem)
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤160021/100000)
    target_start_U.1.le 3
  change Q0/(U (83/125))^3<(239/250:ℝ)
  apply (div_lt_iff₀ (pow_pos hu 3)).2
  norm_num [Q0] at *
  nlinarith

lemma target_start_product : (127/400:ℝ)<z (83/125)*(ratio (83/125))^2 := by
  have hz : (60021/100000:ℝ)<z (83/125) := by
    have hh := target_start_U.1
    dsimp [z,U] at *
    linarith
  have hr := target_start_ratio
  have hs : (3637/5000:ℝ)^2<(ratio (83/125))^2 := by nlinarith
  have hp := mul_lt_mul hz hs (by norm_num) (by linarith : 0≤z (83/125))
  norm_num at hp
  linarith

lemma second_at_start {b : ℝ} (hb : b∈Icc 0 (1/10)) :
    second b (83/125)<(-(7/25):ℝ) := by
  have hstart : (83/125:ℝ)∈Icc (83/125) outerDiagonal := ⟨le_rfl,target_start_mem.2⟩
  have hg := rectangle_geometry hb hstart
  have hv : 0<speed b (83/125) := by linarith [hg.2.2.2.2]
  have hfirst : ratioD (83/125)/speed b (83/125)<(9/8:ℝ) := by
    apply (div_lt_iff₀ hv).2
    nlinarith [target_start_ratioD]
  have hvhi := target_start_speed hb
  have hv3 := pow_lt_pow_left₀ hv.le hvhi (by norm_num : (3:ℕ)≠0)
  have hsecond : (9/20:ℝ)<z (83/125)*(ratio (83/125))^2/(speed b (83/125))^3 := by
    apply (lt_div_iff₀ (pow_pos hv 3)).2
    norm_num at hv3
    nlinarith [target_start_product]
  dsimp [second]
  linarith [target_start_second]

lemma second_negative {b B : ℝ} (hb : b∈Icc 0 (1/10))
    (hB : B∈Icc (83/125) outerDiagonal) : second b B<0 := by
  have hbf := UpperDiagonal.early_domain hb
  have hanti : AntitoneOn (second b) (Icc (83/125) outerDiagonal) :=
    antiOn_of_hasDeriv_nonpos
      (fun t ht => (second_hasDerivAt hbf (target_domain ht)).continuousAt.continuousWithinAt)
      (fun t ht => second_hasDerivAt hbf (target_domain (Ioo_subset_Icc_self ht)))
      (fun t ht => (third_negative hb (Ioo_subset_Icc_self ht)).le)
  have hh := hanti ⟨le_rfl,target_start_mem.2⟩ hB hB.1
  linarith [second_at_start hb]

theorem concave {b : ℝ} (hb : b∈Icc 0 (1/10)) :
    ConcaveOn ℝ (Icc (83/125) outerDiagonal) (cost b) :=
  concave_of_deriv2
    (fun t ht => cost_hasDerivAt (UpperDiagonal.early_domain hb) (target_domain ht))
    (fun t ht => first_hasDerivAt (UpperDiagonal.early_domain hb) (target_domain ht))
    (fun t ht => (second_negative hb ht).le)

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.UpperTarget
