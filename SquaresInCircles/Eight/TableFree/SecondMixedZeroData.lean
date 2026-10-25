module

public import SquaresInCircles.Eight.TableFree.SecondOuterJBounds
public import SquaresInCircles.Eight.TableFree.SecondOuterKBounds
public import SquaresInCircles.Eight.TableFree.ShortMixedZeroPositiveCore
public import SquaresInCircles.Eight.TableFree.WrongZeroOriginalOwners

/-!
# The exact mixed zero-quarter labels of the second wrong word

Uncompiled source draft.  The bounds in this module hold on the whole
physical outer arc.  They will be used only after the original weak
secondary separator has been retained.  The two core pieces share these
literal affine labels; no replacement of a core point is made here.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry

abbrev SameRow := Fin 2

def coreC : SameRow → ℝ := ![125/100000,4970/100000]
def coreG : SameRow → ℝ := ![103981/100000,94831/100000]
def targetLabel : SameRow → RoleLabel := ![JLabel,KLabel]
def outerC : SameRow → ℝ := ![19555/100000,16823/100000]
def outerG : SameRow → ℝ := ![63132/100000,62312/100000]
def sourceLabel : SameRow → RoleLabel := ![PLabel,LLabel]
def sourceSlope : SameRow → ℝ := ![7/10,311/500]

lemma core_coefficients (r : SameRow) :
    (94831/100000:ℝ)≤coreG r ∧ coreG r≤103981/100000 := by
  fin_cases r <;> norm_num [coreG]

lemma outer_coefficients (r : SameRow) :
    0≤outerG r ∧ outerG r<(191/250:ℝ) ∧
      0≤ sourceSlope r ∧ sourceSlope r≤1 := by
  fin_cases r <;> norm_num [outerG,sourceSlope]

lemma target_slope_upper (r : SameRow) {B : ℝ}
    (hB : B∈Icc 0 outerDiagonal) : (targetLabel r).d1 B<(11/10:ℝ) := by
  fin_cases r
  · simpa [targetLabel] using (J_first_bounds hB).2.trans (by norm_num : (541/500:ℝ)<11/10)
  · simpa [targetLabel] using (K_first_bounds hB).2.trans (by norm_num : (116/125:ℝ)<11/10)

lemma target_zero_negative (r : SameRow) : (targetLabel r).outer 0<0 := by
  fin_cases r
  · change J 0<0
    rw [J_zero]
    nlinarith [outer_endpoint_bounds.1]
  · change K 0<0
    linarith [K_zero_bounds.2]

lemma target_affine_upper (r : SameRow) {B : ℝ}
    (hB : B∈Icc 0 outerDiagonal) : (targetLabel r).outer B≤(11/10)*B := by
  have hd {t : ℝ} (ht : t∈Icc 0 outerDiagonal) :
      HasDerivAt (fun t => (11/10)*t-(targetLabel r).outer t) (11/10-(targetLabel r).d1 t) t := by
    have h := ((hasDerivAt_id' t).const_mul (11/10:ℝ)).sub
      ((targetLabel r).outer_hasDerivAt (outer_domain ht))
    exact h.congr_deriv (by ring)
  have hm : MonotoneOn (fun t => (11/10)*t-(targetLabel r).outer t) (Icc 0 outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (hd ht).continuousAt.continuousWithinAt)
      (fun t ht => hd (Ioo_subset_Icc_self ht))
      (fun t ht => by linarith [target_slope_upper r (Ioo_subset_Icc_self ht)])
  have hh := hm outer_zero_mem hB hB.1
  simp only at hh
  linarith [target_zero_negative r]

lemma source_slope_lower (r : SameRow) {b : ℝ}
    (hb : b∈Icc 0 outerDiagonal) : sourceSlope r<(sourceLabel r).d1 b := by
  fin_cases r
  · norm_num [sourceSlope,sourceLabel]
    linarith [(P_first_bounds hb).1]
  · simpa [sourceSlope,sourceLabel] using L_first_lower hb

lemma source_affine_lower (r : SameRow) {b : ℝ}
    (hb : b∈Icc 0 outerDiagonal) :
    (sourceLabel r).outer 0+sourceSlope r*b≤(sourceLabel r).outer b := by
  have hd {t : ℝ} (ht : t∈Icc 0 outerDiagonal) :
      HasDerivAt (fun t => (sourceLabel r).outer t-sourceSlope r*t)
        ((sourceLabel r).d1 t-sourceSlope r) t := by
    have h := ((sourceLabel r).outer_hasDerivAt (outer_domain ht)).sub
      ((hasDerivAt_id' t).const_mul (sourceSlope r))
    exact h.congr_deriv (by ring)
  have hm : MonotoneOn (fun t => (sourceLabel r).outer t-sourceSlope r*t)
      (Icc 0 outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (hd ht).continuousAt.continuousWithinAt)
      (fun t ht => hd (Ioo_subset_Icc_self ht))
      (fun t ht => by linarith [source_slope_lower r (Ioo_subset_Icc_self ht)])
  have hh := hm outer_zero_mem hb hb.1
  simp only [mul_zero,sub_zero] at hh
  linarith

lemma source_zero (r : SameRow) :
    (sourceLabel r).outer 0=![2478/100000,3965/100000] r := by
  fin_cases r <;> norm_num [sourceLabel,RoleLabel.outer,RoleLabel.eval,PLabel,LLabel]

lemma same_core_literal (r : SameRow) (kind : RadialKind) (hk : kind≠.outer)
    {a b A B x : ℝ} (ht : OuterState A B) :
    cost (![0,4] r) kind .outer true true a b A B x=
      x+coreC r+coreG r*b-(targetLabel r).outer B := by
  rw [(targetLabel r).outer_actual ht]
  revert hk
  fin_cases r <;> cases kind <;>
    norm_num [cost,label,wrongValue,WordProblems.secondCoefficients,
      WordProblems.radialIndex,WordProblems.signIndex,WordProblems.sign,
      next,coreC,coreG,targetLabel,JLabel,KLabel,RoleLabel.eval] <;> ring

lemma same_outer_literal (r : SameRow) (kind : RadialKind) (hk : kind≠.outer)
    {a b A B x : ℝ} (hs : OuterState a b) :
    cost (![0,4] r) .outer kind true true a b A B x=
      x+(sourceLabel r).outer b-outerC r-outerG r*B := by
  rw [(sourceLabel r).outer_actual hs]
  revert hk
  fin_cases r <;> cases kind <;>
    norm_num [cost,label,wrongValue,WordProblems.secondCoefficients,
      WordProblems.radialIndex,WordProblems.signIndex,WordProblems.sign,
      next,outerC,outerG,sourceLabel,PLabel,LLabel,RoleLabel.eval] <;> ring

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero
