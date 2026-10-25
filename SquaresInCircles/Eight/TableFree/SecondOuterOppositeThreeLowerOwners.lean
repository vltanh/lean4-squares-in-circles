module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeData

/-!
# Exact lower-half owner reduction on the original common circle

Rotate the original source farthest corner into the target frame.
The target-primary separator increases its first coordinate by at
least one.  Equality of the two circle norms then decreases its second
coordinate.  Rotating this inequality back gives the corresponding
source-secondary separator.  The reversed argument treats the other
primary owner.  This retains every original weak contact and needs
no change of state, radius or labels.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma lower_primary_dominates_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hprimary : lowerPrimary b x≤A) : b≤lowerSecondary B x := by
  let r := (a+1/2)*Real.sin x+(b+1/2)*Real.cos x
  let s := (a+1/2)*Real.cos x-(b+1/2)*Real.sin x
  have htr := positive_trig hx
  have hc : 0<Real.cos x := by linarith [htr.1]
  have hsin := htr.2.2.1
  have hcs : 0<Real.cos x-Real.sin x := by linarith [htr.1,htr.2.2.2.1]
  have hu : 0<a+1/2 := by linarith [hs.1,hs.2.1]
  have hv : 0<b+1/2 := by linarith [hs.1]
  have hr0 : 0≤r := by dsimp [r]; positivity
  have hs0 : 0<s := by
    have h1 := mul_pos hu hcs
    have h2 := mul_nonneg (sub_nonneg.mpr hs.2.1) hsin
    dsimp [s]
    nlinarith
  have hrot : r^2+s^2=Q0 := by
    dsimp [r,s]
    linear_combination ((a+1/2)^2+(b+1/2)^2)*(Real.sin_sq_add_cos_sq x)+hs.2.2
  have hback : r*Real.cos x-s*Real.sin x=b+1/2 := by
    dsimp [r,s]
    linear_combination (b+1/2)*(Real.sin_sq_add_cos_sq x)
  have hX : 1+r≤A+1/2 := by
    dsimp [lowerPrimary] at hprimary
    rw [(ShortOuterOne.SameContact.actual_arc hs).1] at hprimary
    dsimp [r]
    linarith
  have hY : B+1/2≤ s := by
    have hX0 : 0≤A+1/2 := by linarith [ht.1,ht.2.1]
    have hY0 : 0≤B+1/2 := by linarith [ht.1]
    have hprod := mul_nonneg
      (show 0≤A+1/2-r by linarith)
      (show 0≤A+1/2+r by linarith)
    nlinarith [ht.2.2]
  have hp := mul_nonneg (show 0≤A+1/2-1-r by linarith) hc.le
  have hq := mul_nonneg (sub_nonneg.mpr hY) hsin
  dsimp [lowerSecondary]
  rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  nlinarith

theorem original_lower_target_primary_implies_first {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) 1 (Real.pi/2-x)) :
    0≤Eight.forwardMargin 0 a b A B (-1) 1 (Real.pi/2-x) := by
  have hcut := lower_primary_dominates_secondary hs ht hx
    (lower_target_primary hs hx hm)
  dsimp [lowerSecondary] at hcut
  rw [(ShortOuterOne.SameContact.actual_arc ht).1] at hcut
  norm_num [Eight.forwardMargin,NegativeTwo.lower_width hx,Real.sin_sub,Real.cos_sub]
  linarith

theorem original_lower_source_primary_implies_third {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) 1 (Real.pi/2-x)) :
    0≤Eight.forwardMargin 2 a b A B (-1) 1 (Real.pi/2-x) := by
  have hcut := lower_primary_dominates_secondary ht hs hx
    (lower_source_primary ht hx hm)
  dsimp [lowerSecondary] at hcut
  rw [(ShortOuterOne.SameContact.actual_arc hs).1] at hcut
  norm_num [Eight.forwardMargin,NegativeTwo.lower_width hx,Real.sin_sub,Real.cos_sub]
  linarith

theorem original_lower_reduced_owner {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (j : Fin 4) (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 (Real.pi/2-x)) :
    ∃ k : Fin 4, (k=0 ∨ k=2) ∧
      0≤Eight.forwardMargin k a b A B (-1) 1 (Real.pi/2-x) := by
  fin_cases j
  · exact ⟨0,Or.inl rfl,hm⟩
  · exact ⟨0,Or.inl rfl,original_lower_target_primary_implies_first hs ht hx hm⟩
  · exact ⟨2,Or.inr rfl,hm⟩
  · exact ⟨2,Or.inr rfl,original_lower_source_primary_implies_third hs ht hx hm⟩

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree
