module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeTargetGeometry

/-!
# The analytic continuation used by the written diagonal proof

Uncompiled source draft.  The label formulas and their exact derivatives
are valid through coordinate `.9`, just beyond the physical diagonal.
The following signs are proved on that whole interval from the circle
radical.  They are the derivative signs used in the written P and L
negative-target arguments; no physical state is added to the cycle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.Labels
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def domain : Set ℝ := Icc 0 (9/10)

lemma chart_domain {B : ℝ} (hB : B∈domain) : B∈Icc 0 outerAxial :=
  ⟨hB.1,by linarith [hB.2,outer_endpoint_bounds.1]⟩

lemma coordinates {B : ℝ} (hB : B∈domain) :
    0<U B ∧ (1/2:ℝ)≤W B ∧ W B≤7/5 ∧ (39/20:ℝ)<(U B)^2 := by
  have hc := UW_circle (chart_domain hB)
  have hw : W B∈Icc (1/2:ℝ) (7/5) := by
    dsimp [W]
    constructor <;> linarith [hB.1,hB.2]
  have hs := pow_le_pow_left₀ (by linarith [hw.1] : 0≤W B) hw.2 2
  exact ⟨U_positive (chart_domain hB),hw.1,hw.2,by norm_num [Q0] at hc; linarith⟩

lemma ratio_signs {B : ℝ} (hB : B∈domain) :
    0<ratio B ∧ 0<ratioD B ∧ 0<ratioDD B ∧ 0<ratioDDD B ∧ 0<ratioDDDD B := by
  have hc := coordinates hB
  have hu : 0<U B := hc.1
  have hw : 0<W B := by linarith [hc.2.1]
  have hs : 0<(U B)^2 := sq_pos_of_pos hu
  change 0<W B/U B ∧ 0<Q0/(U B)^3 ∧ 0<3*Q0*W B/(U B)^5 ∧
    0<3*Q0*((U B)^2+5*(W B)^2)/(U B)^7 ∧
    0<15*Q0*W B*(3*(U B)^2+7*(W B)^2)/(U B)^9
  refine ⟨?_,?_,?_,?_,?_⟩ <;> norm_num [Q0] <;> positivity

lemma P_second_positive {B : ℝ} (hB : B∈domain) : 0<PLabel.d2 B := by
  have hh := ratio_signs hB
  have hp := mul_nonneg hB.1 hh.2.1.le
  norm_num [RoleLabel.d2,PLabel]
  nlinarith [hh.1]

lemma P_third_positive {B : ℝ} (hB : B∈domain) : 0<PLabel.d3 B := by
  have hh := ratio_signs hB
  have hp := mul_nonneg hB.1 hh.2.2.1.le
  norm_num [RoleLabel.d3,PLabel]
  nlinarith [hh.2.1]

lemma P_fourth_positive {B : ℝ} (hB : B∈domain) : 0<PLabel.d4 B := by
  have hh := ratio_signs hB
  have hp := mul_nonneg hB.1 hh.2.2.2.1.le
  norm_num [RoleLabel.d4,PLabel]
  nlinarith [hh.2.2.1]

lemma P_fifth_positive {B : ℝ} (hB : B∈domain) : 0<PLabel.d5 B := by
  have hh := ratio_signs hB
  have hp := mul_nonneg hB.1 hh.2.2.2.2.le
  norm_num [RoleLabel.d5,PLabel]
  nlinarith [hh.2.2.2.1]

lemma P_first_monotone : MonotoneOn PLabel.d1 domain :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => (PLabel.d1_hasDerivAt (chart_domain hB)).continuousAt.continuousWithinAt)
    (fun B hB => PLabel.d1_hasDerivAt (chart_domain (Ioo_subset_Icc_self hB)))
    (fun B hB => (P_second_positive (Ioo_subset_Icc_self hB)).le)

lemma P_second_monotone : MonotoneOn PLabel.d2 domain :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => (PLabel.d2_hasDerivAt (chart_domain hB)).continuousAt.continuousWithinAt)
    (fun B hB => PLabel.d2_hasDerivAt (chart_domain (Ioo_subset_Icc_self hB)))
    (fun B hB => (P_third_positive (Ioo_subset_Icc_self hB)).le)

lemma P_third_monotone : MonotoneOn PLabel.d3 domain :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => (PLabel.d3_hasDerivAt (chart_domain hB)).continuousAt.continuousWithinAt)
    (fun B hB => PLabel.d3_hasDerivAt (chart_domain (Ioo_subset_Icc_self hB)))
    (fun B hB => (P_fourth_positive (Ioo_subset_Icc_self hB)).le)

lemma L_third_positive {B : ℝ} (hB : B∈domain) : 0<LLabel.d3 B := by
  have hh := ratio_signs hB
  have hp := mul_nonneg hB.1 hh.2.2.1.le
  norm_num [RoleLabel.d3,LLabel]
  nlinarith [hh.2.1]

lemma L_fourth_positive {B : ℝ} (hB : B∈domain) : 0<LLabel.d4 B := by
  have hh := ratio_signs hB
  have hp := mul_nonneg hB.1 hh.2.2.2.1.le
  norm_num [RoleLabel.d4,LLabel]
  nlinarith [hh.2.2.1]

lemma L_second_monotone : MonotoneOn LLabel.d2 domain :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => (LLabel.d2_hasDerivAt (chart_domain hB)).continuousAt.continuousWithinAt)
    (fun B hB => LLabel.d2_hasDerivAt (chart_domain (Ioo_subset_Icc_self hB)))
    (fun B hB => (L_third_positive (Ioo_subset_Icc_self hB)).le)

lemma L_third_monotone : MonotoneOn LLabel.d3 domain :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => (LLabel.d3_hasDerivAt (chart_domain hB)).continuousAt.continuousWithinAt)
    (fun B hB => LLabel.d3_hasDerivAt (chart_domain (Ioo_subset_Icc_self hB)))
    (fun B hB => (L_fourth_positive (Ioo_subset_Icc_self hB)).le)

lemma L_fifth_identity {B : ℝ} (hB : B∈domain) :
    LLabel.d5 B=LLabel.d3 B*(5/(U B)^2+35*(W B)^2/(U B)^4)-
      (15*(94721/50000)*Q0*W B)/(U B)^7 := by
  have hp := (coordinates hB).1
  dsimp [RoleLabel.d5,RoleLabel.d3,LLabel,ratioD,ratioDD,ratioDDD,ratioDDDD,U,W]
  field_simp [show arc B+1/2≠0 from hp.ne']
  ring

lemma L_fifth_upper {B : ℝ} (hB : B∈domain) : LLabel.d5 B<21*LLabel.d3 B := by
  have hc := coordinates hB
  have hu2 := sq_pos_of_pos hc.1
  have hu4 := pow_pos hc.1 4
  have hW2 : (W B)^2≤(7/5:ℝ)^2 :=
    pow_le_pow_left₀ (by linarith [hc.2.1]) hc.2.2.1 2
  have hU4 : (39/20:ℝ)^2≤(U B)^4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤39/20) hc.2.2.2.le 2
    nlinarith
  have hfirst : 5/(U B)^2≤(100/39:ℝ) := (div_le_iff₀ hu2).2 (by nlinarith [hc.2.2.2])
  have hsecond : 35*(W B)^2/(U B)^4≤(27440/1521:ℝ) :=
    (div_le_iff₀ hu4).2 (by nlinarith)
  have hsum : 5/(U B)^2+35*(W B)^2/(U B)^4<21 := by linarith
  have hprod := mul_lt_mul_of_pos_left hsum (L_third_positive hB)
  have hlast : 0<(15*(94721/50000)*Q0*W B)/(U B)^7 := by
    have hw : 0<W B := by linarith [hc.2.1]
    norm_num [Q0]
    positivity
  rw [L_fifth_identity hB]
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.Labels
