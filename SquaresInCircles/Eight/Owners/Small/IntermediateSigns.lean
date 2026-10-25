module

public import SquaresInCircles.Eight.Words.Crossed.SmallWrongSign
public import SquaresInCircles.Eight.Owners.Wide.SmallWrongSign
public import SquaresInCircles.Eight.Words.Wrong.SignCapture

/-!
# Eight squares: the signs of the intermediates on the small side after middle alignment

The ordered and the crossed alternatives of the outer frame cover the whole interval `[0.28, 0.5]`
of the middle tangent, and both use the budget of the cycle. So G is negative and T positive
(`HardInput.small_middle_G_negative`, `HardInput.small_middle_T_positive`), with no assumption on
the outer ordering, the opposite intermediate sign or the sign of the outer error.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate
namespace SignedCycle

theorem HardOuterGeometry.small_middle_G_negative {q : ℝ} (I : HardOuterGeometry q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (7/25 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGsmall : (I.cycle.point G).y<1/10) : (I.cycle.point G).y<0 := by
  by_contra! hwrong
  by_cases hAH : I.cycle.theta A≤I.cycle.theta H
  · have hTy := I.large_middle_T_positive hq hAB hnorm hTA hAG
      (by linarith [hsmall.2])
    exact I.wide_small_wrong_G_impossible hqL hq hAB hnorm hsmall hTA hAH hTy.le hwrong hGsmall
  · exact I.crossed_small_wrong_G_impossible hqL hq hAB hnorm hsmall hTA hAG
      (lt_of_not_ge hAH) hwrong hGsmall

theorem HardOuterGeometry.small_middle_T_positive {q : ℝ} (I : HardOuterGeometry q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : -(I.cycle.point B).y∈Icc (7/25 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hTsmall : -(1/10 : ℝ)<(I.cycle.point T).y) : 0<(I.cycle.point T).y := by
  have hAB' : I.reflected.cycle.theta A=I.reflected.cycle.theta B := by
    change I.cycle.theta B-I.cycle.theta B=I.cycle.theta B-I.cycle.theta A
    linarith
  have hnorm' : (I.reflected.cycle.point A).y-(I.reflected.cycle.point B).y=1 := by
    change -(I.cycle.point B).y-(-(I.cycle.point A).y)=1
    linarith
  have hTA' : I.reflected.cycle.theta T≤I.reflected.cycle.theta A := by
    change I.cycle.theta B-I.cycle.theta G≤I.cycle.theta B-I.cycle.theta B
    linarith
  have hAG' : I.reflected.cycle.theta A≤I.reflected.cycle.theta G := by
    change I.cycle.theta B-I.cycle.theta B≤I.cycle.theta B-I.cycle.theta T
    linarith
  have hh := I.reflected.small_middle_G_negative hqL hq hAB' hnorm' hsmall hTA' hAG'
    (show -(I.cycle.point T).y<1/10 by linarith)
  change -(I.cycle.point T).y<0 at hh
  linarith

theorem HardInput.small_middle_G_negative {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (7/25 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G) : (I.cycle.point G).y<0 :=
  I.outerGeometry.small_middle_G_negative hqL hq hAB hnorm hsmall hTA hAG
    (I.small_intermediate_signs hq).1

theorem HardInput.small_middle_T_positive {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : -(I.cycle.point B).y∈Icc (7/25 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G) : 0<(I.cycle.point T).y :=
  I.outerGeometry.small_middle_T_positive hqL hq hAB hnorm hsmall hTA hAG
    (I.small_intermediate_signs hq).2

end SignedCycle
end SquaresInCircles.Eight
