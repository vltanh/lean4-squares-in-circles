module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3DEnvelope

/-!
# The wider D minorant at the unchanged sorted outer point

Uncompiled source bridge for the negative-A BT3 envelope.  A negative
first force in the reversed mixed quadrant is treated by the genuine
diagonal support inequality, which only requires a nonnegative total
force.  The other three quadrants use their proved positive forces.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.DEnvelope
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3

theorem actual_support {Q c x y : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : P.y≤0) (hP : P.Contained Q) (hQ : Q≤qCap)
    (hc : c∈Icc 1 Cmax) (hxy : SignedDomain x y) :
    forceA c x y*P.a+forceB c x y*(-P.y)≤sortedSupport (forceA c x y) (forceB c x y) := by
  have ha := signed_domain_angles hxy
  have huse (hp : 0<forceA c x y ∧ 0<forceB c x y) :=
    actual_sorted_support hs hy hP hQ hp.1.le hp.2.le
  by_cases hx0 : 0≤x
  · have hx : x∈Icc 0 frameCap := ⟨hx0,(le_abs_self x).trans ha.1⟩
    by_cases hy0 : 0≤y
    · exact huse (positive_force_positive hc hx ⟨hy0,(le_abs_self y).trans ha.2⟩)
    · have hn : -y∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs y).trans ha.2⟩
      apply huse
      simpa only [neg_neg] using forward_force_positive hc hx hn
  · have hn : -x∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs x).trans ha.1⟩
    by_cases hy0 : 0≤y
    · have ht : y∈Icc 0 frameCap := ⟨hy0,(le_abs_self y).trans ha.2⟩
      have hnt := transport_trig hn
      have htt := transport_trig ht
      have hphi := CorrelatedSameBlock.one_le_phi hn
      have hmul := mul_le_mul_of_nonneg_left hphi (by linarith [hc.1] : 0≤c)
      have hfg : forceA c x y≤forceB c x y := by
        dsimp [forceA,forceB,phi] at *
        rw [Real.cos_neg,Real.sin_neg] at hphi hnt hmul
        nlinarith [Real.cos_le_one y,hc.1,htt.2.2.1]
      have hdiff : 0<Real.cos (-x)-Real.sin (-x) := by
        linarith [hnt.1,hnt.2.2.2.1]
      have hscaled := mul_pos (by linarith [hc.1] : 0<c) hdiff
      have hsum : 0≤forceA c x y+forceB c x y := by
        dsimp [forceA,forceB]
        rw [Real.cos_neg,Real.sin_neg] at hscaled
        linarith [htt.1,htt.2.2.1]
      have hcircle : (P.a+1/2)^2+(-P.y+1/2)^2≤qCap := by
        simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos hy] using hP.trans hQ
      have hb : -P.y≤P.a := by simpa [abs_of_nonpos hy] using hs.2
      have hh := raw_clipped_support hcircle hb (by linarith [hs.1]) hsum
      simpa [clippedSupport,sortedSupport,hfg] using hh
    · have htotal : -x+(-y)∈Icc 0 frameCap := by
        refine ⟨by linarith,?_⟩
        simpa [negativeTotal,negativePart,max_eq_left (show 0≤ -x by linarith),
          max_eq_left (show 0≤ -y by linarith)] using hxy.2
      have hp := negative_force_positive hc htotal
        (show -x∈Icc 0 (-x+(-y)) by constructor <;> linarith)
      apply huse
      simpa only [neg_neg,show -x+(-y)-(-x)= -y by ring] using hp

/-- Exact original-point form of the wider signed D envelope. -/
theorem actual_minorant {Q c x y : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : P.y≤0) (hP : P.Contained Q) (hQ : Q≤qCap)
    (hc : c∈Icc 1 Cmax) (hxy : SignedDomain x y) :
    -slope*positiveTotal x y+vstar (negativeTotal x y)≤
      c*(edgeWidth x-1)+edgeWidth y-1+(1+c)*diagonal-
        (forceA c x y*P.a+forceB c x y*(-P.y)) := by
  have hsupp := actual_support hs hy hP hQ hc hxy
  have hminor := lower hc hxy
  dsimp [D] at hminor
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.DEnvelope
