module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeReferences

/-!
# Complete aligned bounds for the three mixed zero rows

Uncompiled source draft.  J is concave and P increases.  The initial L
arc has a convex derivative ending negative, and the remaining arc has
uniform positive curvature.  A single exact value-and-slope reference
then controls its minimum on that entire remaining arc.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite
open CommonQuarter CorePairGeometry Arithmetic

lemma J_aligned_endpoints : (1801/2000:ℝ)<aligned 0 0 ∧
    (1801/2000:ℝ)<aligned 0 outerDiagonal := by
  constructor
  · change (1801/2000:ℝ)<125/100000+(103981/100000)*(1-0)+J 0
    rw [J_zero]
    linarith [outer_endpoint_bounds.2.1]
  · have hd := ShortMixedZero.fine_diagonal_bounds
    have hs : (449607/500000:ℝ)^2<outerDiagonal^2 := by
      nlinarith [hd.1]
    change (1801/2000:ℝ)<125/100000+(103981/100000)*(1-outerDiagonal)+J outerDiagonal
    rw [J_diagonal]
    nlinarith [hd.1,hd.2]

lemma J_aligned {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (1801/2000:ℝ)<aligned 0 B := by
  have hc : ConcaveOn ℝ (Icc 0 outerDiagonal) (aligned 0) :=
    concave_of_deriv2 (fun t ht => aligned_hasDerivAt 0 ht)
      (fun t ht => alignedD_hasDerivAt 0 ht)
      (fun t ht => by norm_num [F]; linarith [J_second_upper ht])
  exact concave_gt_of_endpoints hc hB J_aligned_endpoints.1 J_aligned_endpoints.2

lemma P_aligned_monotone : MonotoneOn (aligned 1) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun t ht => (aligned_hasDerivAt 1 ht).continuousAt.continuousWithinAt)
    (fun t ht => aligned_hasDerivAt 1 (Ioo_subset_Icc_self ht))
    (fun t ht => by
      norm_num [alignedD,F,g]
      linarith [(P_first_bounds (Ioo_subset_Icc_self ht)).1])

lemma P_aligned {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (17033/20000:ℝ)≤aligned 1 B := by
  have hh := P_aligned_monotone outer_zero_mem hB hB.1
  have hz : aligned 1 0=(17033/20000:ℝ) := by
    norm_num [aligned,c,g,F,RoleLabel.outer,RoleLabel.eval,PLabel]
  rw [hz] at hh
  exact hh

lemma P_aligned_late {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (hcut : (87/200:ℝ)≤B) :
    (463/500:ℝ)<aligned 1 B :=
  References.P_target.trans_le (P_aligned_monotone
    (Asymmetric.rational_outer_mem (by norm_num)) hB hcut)

lemma L_aligned_early {B : ℝ} (hB : B∈Icc (0:ℝ) (3/5)) :
    (901/1000:ℝ)<aligned 2 B := by
  have hdom {t : ℝ} (ht : t∈Icc (0:ℝ) (3/5)) : t∈Icc 0 outerDiagonal :=
    ⟨ht.1,ht.2.trans References.six_mem.2⟩
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (3/5)) (fun t => -alignedD 2 t) :=
    concave_of_deriv2
      (fun t ht => (alignedD_hasDerivAt 2 (hdom ht)).neg)
      (fun t ht => (LLabel.d2_hasDerivAt (outer_domain (hdom ht))).neg)
      (fun t ht => neg_nonpos.mpr (L_third_positive (hdom ht)).le)
  have hh := endpoint_minimum_of_convex_derivative hB
    (fun t ht => aligned_hasDerivAt 2 (hdom ht)) hc References.L_six.2.1.le
  have hz : (901/1000:ℝ)<aligned 2 0 := by
    norm_num [aligned,c,g,F,LLabel,RoleLabel.outer,RoleLabel.eval]
  exact (lt_min hz (by linarith [References.L_six.1])).trans_le hh

lemma L_aligned_curvature {B : ℝ} (hB : B∈Icc (3/5:ℝ) outerDiagonal) :
    (1/2:ℝ)<LLabel.d2 B :=
  References.L_six.2.2.trans_le (L_second_monotone References.six_mem
    ⟨by linarith [hB.1],hB.2⟩ hB.1)

lemma L_aligned_tangent {B : ℝ} (hB : B∈Icc (3/5:ℝ) outerDiagonal) :
    aligned 2 (1027/1250)+alignedD 2 (1027/1250)*(B-1027/1250)+
      (1/4)*(B-1027/1250)^2≤aligned 2 B := by
  convert curvature_tangent (κ := (1/2:ℝ)) hB
    (show (1027/1250:ℝ)∈Icc (3/5:ℝ) outerDiagonal from
      ⟨by norm_num,References.minimum_mem.2⟩)
    (fun t ht => aligned_hasDerivAt 2 ⟨by linarith [ht.1],ht.2⟩)
    (fun t ht => alignedD_hasDerivAt 2 ⟨by linarith [ht.1],ht.2⟩)
    (fun t ht => (L_aligned_curvature ht).le) using 1 <;> ring

lemma L_aligned_late {B : ℝ} (hB : B∈Icc (3/5:ℝ) outerDiagonal) :
    (901/1000:ℝ)<aligned 2 B := by
  have ht := L_aligned_tangent hB
  have hs := abs_lt.mp References.L_minimum.2
  have hp := mul_pos (show 0<alignedD 2 (1027/1250)+1/10000 by linarith [hs.1])
    (show 0<(1/10000:ℝ)-alignedD 2 (1027/1250) by linarith [hs.2])
  have hq := sq_nonneg ((B-1027/1250)/2+alignedD 2 (1027/1250))
  nlinarith [References.L_minimum.1]

lemma L_aligned {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (901/1000:ℝ)<aligned 2 B := by
  by_cases he : B≤3/5
  · exact L_aligned_early ⟨hB.1,he⟩
  · exact L_aligned_late ⟨by linarith,hB.2⟩

lemma high_aligned (r : Row) (hr : r≠1) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (1801/2000:ℝ)<aligned r B := by
  fin_cases r
  · exact J_aligned hB
  · exact (hr rfl).elim
  · linarith [L_aligned hB]

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite
