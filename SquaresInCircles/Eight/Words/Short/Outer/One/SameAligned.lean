module

public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameAlignedReferences

/-!
# Eight squares: every aligned state for the paired same-sign owners

Two rows decrease to the diagonal endpoint. The first row uses its
single strongly convex scalar and the stated interior reference.
The final theorem starts with the weak original aligned separator.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD)

lemma eta_mem : eta∈Icc 0 b0 := ⟨by norm_num [eta],by dsimp [eta]; linarith [b0_bounds.1]⟩

lemma alignedD_zero_monotone : MonotoneOn (alignedD 0) (Icc 0 b0) :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => (alignedD_hasDerivAt 0 hB).continuousAt.continuousWithinAt)
    (fun B hB => alignedD_hasDerivAt 0 (Ioo_subset_Icc_self hB))
    (fun B hB => by linarith [aligned_curvature (Ioo_subset_Icc_self hB)])

lemma aligned_later_antitone (r : Row) (hr : r=1 ∨ r=2) :
    AntitoneOn (aligned r) (Icc 0 b0) := antiOn_of_hasDeriv_nonpos
  (fun B hB => (aligned_hasDerivAt r hB).continuousAt.continuousWithinAt)
  (fun B hB => aligned_hasDerivAt r (Ioo_subset_Icc_self hB))
  (fun B hB => (aligned_later_derivative r hr (Ioo_subset_Icc_self hB)).le)

theorem aligned_lower (r : Row) {B : ℝ} (hB : B∈Icc 0 b0) :
    (8981/10000:ℝ)<aligned r B := by
  by_cases hzero : r=0
  · subst r
    have href : (517/10000:ℝ)∈Icc 0 b0 :=
      ⟨by norm_num,by linarith [b0_bounds.1]⟩
    have hh := CenteredMonomialBounds.second_derivative_tangent_lower
      (κ := (1:ℝ)) (fun y hy => aligned_hasDerivAt 0 hy)
      (fun y hy => alignedD_hasDerivAt 0 hy)
      (fun y hy => (aligned_curvature hy).le) href hB
    have hs := sq_nonneg (B-517/10000+alignedD 0 (517/10000))
    nlinarith [Reference.convex_reference]
  · have hr : r=1 ∨ r=2 := by fin_cases r <;> simp_all
    exact (Reference.diagonal_endpoints r hr).trans_le
      (aligned_later_antitone r hr hB ⟨b0_mem.1,le_rfl⟩ hB.2)

lemma aligned_initial_antitone (r : Row) : AntitoneOn (aligned r) (Icc 0 eta) := by
  have hdom : ∀B∈Icc 0 eta,B∈Icc 0 b0 := fun B hB => ⟨hB.1,hB.2.trans eta_mem.2⟩
  apply antiOn_of_hasDeriv_nonpos
  · intro B hB
    exact (aligned_hasDerivAt r (hdom B hB)).continuousAt.continuousWithinAt
  · intro B hB
    exact aligned_hasDerivAt r (hdom B (Ioo_subset_Icc_self hB))
  · intro B hB
    by_cases hzero : r=0
    · subst r
      have hh := alignedD_zero_monotone (hdom B (Ioo_subset_Icc_self hB)) eta_mem hB.2.le
      exact hh.trans Reference.eta_derivative.le
    · have hr : r=1 ∨ r=2 := by fin_cases r <;> simp_all
      exact (aligned_later_derivative r hr (hdom B (Ioo_subset_Icc_self hB))).le

lemma aligned_initial_lower (r : Row) {B : ℝ} (hB : B∈Icc 0 eta) :
    (89908/100000:ℝ)<aligned r B :=
  (Reference.eta_values r).trans_le
    (aligned_initial_antitone r hB ⟨eta_mem.1,le_rfl⟩ hB.2)

lemma initialAngle_monotone (r : Row) : MonotoneOn (initialAngle r) (Icc 0 b0) := by
  intro B hB D hD hBD
  have hdB := aligned_domains hB
  have hdD := aligned_domains hD
  have hr := SameContact.ratio_monotone (primary_domain hdD.2.2)
    (primary_domain hdB.2.2) (by linarith)
  have hq : 0≤q r := by fin_cases r <;> norm_num [q]
  have hsource : sourceD r (1-D)≤ sourceD r (1-B) := by
    have hh := mul_le_mul_of_nonneg_left hr hq
    dsimp [sourceD]
    linarith
  have harc := SameContact.arc_antitone (SameContact.outer_domain hdB.1)
    (SameContact.outer_domain hdD.1) hBD
  have hproduct := mul_le_mul hsource (show arc D-1/2≤arc B-1/2 by linarith)
    (show 0≤arc D-1/2 by linarith [aligned_target_root hD])
    (show 0≤ sourceD r (1-B) by linarith [sourceD_lower r hdB.2.2])
  dsimp [initialAngle]
  linarith

lemma initialAngle_lower (r : Row) {B : ℝ} (hB : B∈Icc 0 b0) :
    -(1/50:ℝ)< initialAngle r B :=
  (Reference.angle_zero r).trans_le
    (initialAngle_monotone r ⟨le_rfl,b0_mem.1⟩ hB hB.1)

lemma initialAngle_negative_location (r : Row) {B : ℝ} (hB : B∈Icc 0 b0)
    (hne : initialAngle r B<0) : B<eta := by
  by_contra! hbad
  have hh := initialAngle_monotone r eta_mem hB hbad
  linarith [Reference.angle_eta r]

/-- The original aligned primary separator, including source-diagonal slack. -/
theorem aligned_original (r : Row) {a b A B : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hm : 1≤a+B) :
    (8981/10000:ℝ)<Real.pi/2+c r+p r*a-q r*b-P r*A+t r*B := by
  have ha : a∈Icc outerDiagonal outerAxial := ⟨(outer_bounds hs).1,(outer_bounds hs).2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hsource : source r a=p r*a-q r*b := by rw [source,(SameContact.actual_arc hs).2]
  have htarget : target r B= -P r*A+t r*B := by rw [target,(SameContact.actual_arc ht).1]
  by_cases hsmall : B≤b0
  · have hd := aligned_domains ⟨hB.1,hsmall⟩
    have hmono := source_monotone r hd.2.2 ha (by linarith)
    have hh := aligned_lower r ⟨hB.1,hsmall⟩
    dsimp [aligned] at hh
    rw [hsource] at hmono
    rw [htarget] at hh
    linarith
  · have hd : outerDiagonal∈Icc outerDiagonal outerAxial := ⟨le_rfl,SameContact.diagonal_le_axial⟩
    have hmonoS := source_monotone r hd ha ha.1
    have hmonoT := target_monotone r b0_mem hB (le_of_not_ge hsmall)
    have hh := aligned_lower r (show b0∈Icc 0 b0 from ⟨b0_mem.1,le_rfl⟩)
    have he : 1-b0=outerDiagonal := by dsimp [b0]; ring
    dsimp [aligned] at hh
    rw [he] at hh
    rw [hsource] at hmonoS
    rw [htarget] at hmonoT
    linarith

end SquaresInCircles.Eight.ShortOuterOne.Same
