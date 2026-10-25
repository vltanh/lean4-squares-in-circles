module

public import SquaresInCircles.Eight.TableFree.OrderedNormalSharp
public import SquaresInCircles.Eight.TableFree.SmallWrongZeroEndpoint
public import SquaresInCircles.Eight.TableFree.SignedOppositeHardSigns
public import SquaresInCircles.Eight.TableFree.WrongSignCapture

/-!
# Ordered hard sharpness with arbitrary original G/T signs

Uncompiled source draft.  The signed opposite envelope excludes a wrong
sign on the larger middle tangent.  Its normal large-side geometry then
places the opposite original tangent above .335.  A small wrong sign
would reach the actual zero endpoint excluded by the unchanged mixed
budget.  Both original signs are therefore recovered before applying
the complete four-owner ordered sharpness theorem to the source itself.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate
open ExactFamily (qStar qStar_limits)
namespace SignedCycle

theorem HardInput.ordered_intermediate_signs {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B) :
    (I.cycle.point G).y<0 ∧ 0<(I.cycle.point T).y := by
  have hTA : I.cycle.theta T≤I.cycle.theta A := by rw [hAB]; exact hTB
  have hsmall := I.small_intermediate_signs hq
  constructor
  · by_contra! hwrong
    have hAsmall : (I.cycle.point A).y<1/2 := by
      by_contra! hlarge
      exact not_lt_of_ge hwrong (I.large_middle_G_negative hq hAB hnorm hTA hAG hlarge)
    have hBlarge : 1/2≤ -(I.cycle.point B).y := by linarith
    have hTnormal := I.large_middle_T_positive hq hAB hnorm hTA hAG hBlarge
    have hBupper := I.ordered_large_B_upper hqL hq hDB hTB hTnormal.le hBlarge
    have hArange : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2) :=
      ⟨by linarith,hAsmall.le⟩
    exact I.outerGeometry.small_wrong_G_impossible hqL hq hAB hnorm hArange
      hTA hAH hTnormal.le hwrong hsmall.1
  · by_contra! hwrong
    have hBsmall : -(I.cycle.point B).y<1/2 := by
      by_contra! hlarge
      exact not_lt_of_ge hwrong (I.large_middle_T_positive hq hAB hnorm hTA hAG hlarge)
    have hAlarge : 1/2≤(I.cycle.point A).y := by linarith
    have hGnormal := I.large_middle_G_negative hq hAB hnorm hTA hAG hAlarge
    have hAupper := I.ordered_large_A_upper hqL hq hAH hAG hGnormal.le hAlarge
    let J := I.outerGeometry.reflected
    have hJAB : J.cycle.theta A=J.cycle.theta B := by
      change I.cycle.theta B-I.cycle.theta B=I.cycle.theta B-I.cycle.theta A
      linarith
    have hJnorm : (J.cycle.point A).y-(J.cycle.point B).y=1 := by
      change -(I.cycle.point B).y-(-(I.cycle.point A).y)=1
      linarith
    have hJrange : (J.cycle.point A).y∈Icc (67/200 : ℝ) (1/2) := by
      change -(I.cycle.point B).y∈Icc (67/200 : ℝ) (1/2)
      exact ⟨by linarith,hBsmall.le⟩
    have hJTA : J.cycle.theta T≤J.cycle.theta A := by
      change I.cycle.theta B-I.cycle.theta G≤I.cycle.theta B-I.cycle.theta B
      linarith
    have hJAH : J.cycle.theta A≤J.cycle.theta H := by
      change I.cycle.theta B-I.cycle.theta B≤I.cycle.theta B-I.cycle.theta D
      linarith
    have hJTy : 0≤(J.cycle.point T).y := by
      change 0≤ -(I.cycle.point G).y
      linarith
    have hJGy : 0≤(J.cycle.point G).y := by
      change 0≤ -(I.cycle.point T).y
      linarith
    have hJGsmall : (J.cycle.point G).y<1/10 := by
      change -(I.cycle.point T).y<1/10
      linarith [hsmall.2]
    exact J.small_wrong_G_impossible hqL hq hJAB hJnorm hJrange
      hJTA hJAH hJTy hJGy hJGsmall

/-- No original intermediate sign or outer-error sign is assumed.
All selected normal HG/TD owners and all original mixed E owners are
covered, and the conclusions concern the literal original source. -/
theorem HardInput.ordered_hard_sharp {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B) :
    I.cycle.theta A=I.cycle.theta B ∧
      (I.cycle.point A).y-(I.cycle.point B).y=1 ∧
      q=qStar ∧ I.cycle.theta G=I.cycle.theta H ∧
      I.cycle.theta B=I.cycle.theta T ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  have hsigns := I.ordered_intermediate_signs hqL (hq.trans qStar_limits.2.2.le)
    hAB hnorm hAH hAG hDB hTB
  exact I.ordered_normal_sharp hqL hq hAB hnorm hAH hAG hDB hTB hsigns.1.le hsigns.2.le

theorem HardInput.ordered_hard_lower_bound {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B) : qStar≤q := by
  by_cases h : qStar≤q
  · exact h
  · exact (I.ordered_hard_sharp hqL (lt_of_not_ge h).le hAB hnorm
      hAH hAG hDB hTB).2.2.1.symm.le

end SignedCycle
end SquaresInCircles.Eight.TableFree
