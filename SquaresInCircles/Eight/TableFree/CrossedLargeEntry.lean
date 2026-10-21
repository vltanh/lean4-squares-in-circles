module

public import SquaresInCircles.Eight.TableFree.CrossedClampInverse
public import SquaresInCircles.Eight.TableFree.SmallIntermediateSigns
public import SquaresInCircles.Eight.TableFree.HardOuterOrder

/-!
# Actual normal-sign entry to the large crossed common-frame clamp

Uncompiled source draft.  After GA alignment, the short original HG0
error forces H's tangent above .75 and the unchanged opposite middle
tangent above .28.  The already proved small-side sign theorem then
recovers the actual T sign before any common-frame clamp is invoked.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open EndpointRotationPenalty

namespace CrossedLargeEntry

theorem actual_pair {q r : ℝ} {H G A : SignedPoint}
    (hq : q≤qCap) (hHs : H.Sorted) (hGs : G.Sorted) (hAs : A.Sorted)
    (hHc : H.AvoidsCore) (hGc : G.AvoidsCore) (hAc : A.AvoidsCore)
    (hHq : H.Contained q) (hGq : G.Contained q) (hAq : A.Contained q)
    (hHy : 0≤H.y) (hGy : G.y≤0) (hAy : 1/2≤A.y)
    (hr : r∈Icc (0:ℝ) (1/25))
    (hHG : zeroFeasible H G r 0) (hGA : quarterFeasible G A 0 0) :
    3/4<H.y ∧ A.y<18/25 := by
  have ht := CrossedClampInverse.trig hr
  have hHbounds := SignedPoint.coordinate_bounds hHs hHc hHq hq
  have hGbounds := SignedPoint.coordinate_bounds hGs hGc hGq hq
  have hHupper : H.y<9/10 := (le_abs_self H.y).trans_lt hHbounds.2.2
  have hGa : G.a-1/2≤183/200 := by linarith [hGbounds.2.1]
  have hga : 1≤G.y+A.a := by simpa [quarterFeasible,quarterProjection] using hGA
  have hAcircle : (A.a+1/2)^2+(A.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,
      abs_of_nonneg (show 0≤A.y by linarith)] using hAq.trans hq
  have hAa : A.a≤151/125 := by
    have hq' := hAcircle
    dsimp [qCap] at hq'
    nlinarith [hAs.1]
  have hg : -G.y≤26/125 := by linarith
  have hc := mul_le_mul_of_nonneg_right
    (show 73/250≤1/2+G.y by linarith) (show 0≤Real.cos r by linarith [ht.2.2.2.1])
  have hc' := mul_le_mul_of_nonneg_left ht.2.2.2.1 (by norm_num : (0:ℝ)≤73/250)
  have hs := mul_le_mul hGa ht.2.2.1 ht.2.1 (by norm_num : (0:ℝ)≤183/200)
  have hHG' := hHG
  rw [zeroFeasible,edgeWidth_positive_formula ht.1] at hHG'
  simp only [zeroProjection,Matrix.cons_val_zero] at hHG'
  have hHlower : 3/4<H.y := by nlinarith
  have hcharge := ZeroSignedCharge.signed_right hHs hGs hHc hGc hHq hGq hq hHy
    (show |r|≤frameCap by rw [abs_of_nonneg hr.1]; exact ht.1.2) (Or.inl hHG)
  have hAlower : 11/10-2/49<A.a := by
    dsimp [charge] at hcharge
    nlinarith [hr.2]
  have hAyupper : A.y<18/25 := by
    dsimp [qCap] at hAcircle
    nlinarith
  exact ⟨hHlower,hAyupper⟩

end CrossedLargeEntry

namespace SignedCycle
open Candidate

theorem HardOuterGeometry.crossed_large_aligned_entry {q : ℝ}
    (I : HardOuterGeometry q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hGAframe : I.cycle.theta G=I.cycle.theta A)
    (hHA : I.cycle.theta H≤I.cycle.theta A)
    (hshort : I.cycle.theta A-I.cycle.theta H≤1/25)
    (hlarge : 1/2≤(I.cycle.point A).y) (hHG : I.cycle.Feasible H 0) :
    3/4<(I.cycle.point H).y ∧ 7/25< -(I.cycle.point B).y ∧
      0<(I.cycle.point T).y := by
  have hTA : I.cycle.theta T≤I.cycle.theta A := by
    have hh := I.intermediate_order hq
    linarith
  have hAG : I.cycle.theta A≤I.cycle.theta G := hGAframe.symm.le
  have hG := I.large_middle_G_negative hq hAB hnorm hTA hAG hlarge
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G)
      (I.cycle.theta A-I.cycle.theta H) 0 := by
    simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,hGAframe] using hHG
  have hGA' : quarterFeasible (I.cycle.point G) (I.cycle.point A) 0 0 := by
    simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,hGAframe] using I.GA_hard
  obtain ⟨hH,hA⟩ := CrossedLargeEntry.actual_pair hq
    (I.necessary.sorted H) (I.necessary.sorted G) (I.necessary.sorted A)
    (I.necessary.core H) (I.necessary.core G) (I.necessary.core A)
    (I.necessary.contained H) (I.necessary.contained G) (I.necessary.contained A)
    I.anchors_normal.H_nonneg hG.le hlarge ⟨sub_nonneg.mpr hHA,hshort⟩ hHG' hGA'
  have hsmall : -(I.cycle.point B).y∈Icc (7/25 : ℝ) (1/2) := by
    constructor <;> linarith
  have hT := I.small_middle_T_positive hqL hq hAB hnorm hsmall hTA hAG
    (I.small_intermediate_signs hq).2
  exact ⟨hH,by linarith,hT⟩

end SignedCycle
end SquaresInCircles.Eight.TableFree
