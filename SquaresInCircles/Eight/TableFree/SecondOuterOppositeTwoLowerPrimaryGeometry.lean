module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoTargetPrimaryLabel

/-!
# The increasing original lower-primary contact

The contact rotates the original circle point.  Its speed is positive
on the whole physical angle interval, and the exact circle identity
identifies that speed with the primary-coordinate radical whenever
the original weak separator keeps the contact on the physical arc.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def lowerSpeed (a b x : ℝ) : ℝ :=
  (a+1/2)*Real.cos x-(b+1/2)*Real.sin x

lemma lowerPrimary_zero (a b : ℝ) : lowerPrimary a b 0=1+b := by
  norm_num [lowerPrimary]
  ring

lemma lowerPrimary_hasDerivAt (a b x : ℝ) :
    HasDerivAt (lowerPrimary a b) (lowerSpeed a b x) x := by
  convert ((((Real.hasDerivAt_sin x).const_mul (a+1/2)).const_add (1/2)).add
    ((Real.hasDerivAt_cos x).const_mul (b+1/2))) using 1 <;>
    dsimp [lowerPrimary,lowerSpeed] <;> ring

lemma lowerSpeed_hasDerivAt (a b x : ℝ) :
    HasDerivAt (lowerSpeed a b) (1/2-lowerPrimary a b x) x := by
  convert ((Real.hasDerivAt_cos x).const_mul (a+1/2)).sub
    ((Real.hasDerivAt_sin x).const_mul (b+1/2)) using 1 <;>
    dsimp [lowerPrimary,lowerSpeed] <;> ring

lemma lowerSpeed_positive {a b x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10)) : 0<lowerSpeed a b x := by
  have ht := positive_trig hx
  have hcos : 0<Real.cos x := by linarith [ht.1]
  have hfirst := mul_nonneg (sub_nonneg.mpr hs.2.1) hcos.le
  have hlast := mul_pos (show 0<b+1/2 by linarith [hs.1])
    (show 0<Real.cos x-Real.sin x by linarith [ht.1,ht.2.2.2.1])
  dsimp [lowerSpeed]
  nlinarith

lemma lowerPrimary_monotone {a b : ℝ} (hs : OuterState a b) :
    MonotoneOn (lowerPrimary a b) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (lowerPrimary_hasDerivAt a b x).continuousAt.continuousWithinAt)
    (fun x _ => lowerPrimary_hasDerivAt a b x)
    (fun x hx => (lowerSpeed_positive hs (Ioo_subset_Icc_self hx)).le)

lemma lowerPrimary_norm {a b : ℝ} (hs : OuterState a b) (x : ℝ) :
    (lowerPrimary a b x-1/2)^2+(lowerSpeed a b x)^2=Q0 := by
  have ht := Real.sin_sq_add_cos_sq x
  dsimp [lowerPrimary,lowerSpeed]
  linear_combination hs.2.2+((a+1/2)^2+(b+1/2)^2)*ht

lemma lower_contact_domain {a b c x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10)) (hc : c≤outerAxial)
    (hcut : lowerPrimary a b x≤c) {t : ℝ} (ht : t∈Icc 0 x) :
    lowerPrimary a b t∈Icc 1 outerAxial := by
  have ht' : t∈Icc 0 (7/10) := ⟨ht.1,ht.2.trans hx.2⟩
  have hlo := lowerPrimary_monotone hs (by norm_num) ht' ht.1
  have hhi := lowerPrimary_monotone hs ht' hx ht.2
  rw [lowerPrimary_zero] at hlo
  exact ⟨by linarith [hs.1],hhi.trans (hcut.trans hc)⟩

lemma lowerSpeed_eq_primarySpeed {a b x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10))
    (hcut : lowerPrimary a b x∈Icc 1 outerAxial) :
    lowerSpeed a b x=primarySpeed (lowerPrimary a b x) := by
  have hleft := lowerSpeed_positive hs hx
  have hright := primarySpeed_data hcut
  have hnorm := lowerPrimary_norm hs x
  nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo
