module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroOppositeNegativeMultiplier

/-!
# All six negative-angle opposite-sign short-word zero contacts

Uncompiled transcription of the conclusion of Section 2. Four target
intervals are concave between their two actual diagonal endpoints;
the two remaining rows use the written constant multiplier. The
original weak separator is restored using the increasing source label.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Negative
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma concave_contact_lower (r : Row) (hr : ConcaveRow r) {B x : ℝ}
    (hd : MinusDomain B x) : (89809/100000:ℝ)<minusCost r B x := by
  obtain ⟨a,ha,hentry,hdom⟩ := entry hd
  have hleft : MinusDomain a x := hdom a ⟨le_rfl,ha.2.trans hd.1.2⟩
  have hc : ConcaveOn ℝ (Icc a outerDiagonal) (fun C => minusCost r C x) :=
    concave_of_deriv2
      (fun C hC => minusCost_target_hasDerivAt r (hdom C hC))
      (fun C hC => minusTarget_hasDerivAt r (hdom C hC))
      (fun C hC => (target_curvature_negative r hr (hdom C hC)).le)
  apply concave_gt_of_endpoints hc ⟨ha.2,hd.1.2⟩
  · exact SourceDiagonal.original_lower r hleft hentry
  · exact TargetDiagonal.lower r hr ⟨hd.2.1.1,original_angle hd⟩

/-- No row-specific curvature, support or contact-boundary premise remains. -/
theorem contact_lower (r : Row) {B x : ℝ} (hd : MinusDomain B x) :
    (89809/100000:ℝ)<minusCost r B x := by
  by_cases hrows : Multiplier.Rows r
  · exact Multiplier.contact_lower r hrows hd
  · have hconcave : ConcaveRow r := by
      fin_cases r <;> simp_all [Multiplier.Rows,ConcaveRow]
    exact concave_contact_lower r hconcave hd

theorem original (r : Row) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) (-x)) :
    (89809/100000:ℝ)<-x+c r+p r*a+q r*b+v r*A+t r*B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hcut : minus B x≤b := by
    have hw := signed_width (show |-x|≤7/10 by rw [abs_neg,abs_of_nonneg hx.1]; exact hx.2)
    rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg (positive_trig hx).2.2.1] at hw
    norm_num [Eight.forwardMargin,Real.sin_neg,Real.cos_neg] at hm
    rw [hw] at hm
    dsimp [minus,SecondWord.OppositeZero.minus]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
    linarith
  have hd : MinusDomain B x := ⟨hB,hx,⟨by
    linarith [SecondWord.OppositeZero.minus_aligned_le hB hx,hB.2,outer_endpoint_bounds.2.2.2],
    hcut.trans hb.2⟩⟩
  have hsource := source_monotone r hd.2.2 hb hcut
  rw [(source r).outer_actual hs] at hsource
  have hl := contact_lower r hd
  dsimp [minusCost] at hl
  rw [(target r).outer_actual ht] at hl
  dsimp [source,target,SecondWord.RoleLabel.eval] at *
  linarith

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Negative
