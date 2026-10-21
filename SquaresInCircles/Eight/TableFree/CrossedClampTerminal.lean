module

public import SquaresInCircles.Eight.TableFree.CrossedBTGeometry
public import SquaresInCircles.Eight.TableFree.CrossedTDClampCycle
public import SquaresInCircles.Eight.TableFree.OrderedHardSharp

/-!
# Strict common-frame clamp losses cannot reach a sharp terminal

Uncompiled source draft.  At an H-clamped endpoint, G=A=B=H.  The actual
nonpositive HG bound places the opposite middle tangent above .335.
Every hypothetical crossed TD branch would then align T with B=G,
contradicting the strict intermediate order of its actual descendant.
Thus the endpoint is in the already proved ordered hard domain.  The
D-clamped argument is the reflected local construction on the original
hard cycle.  Both conclusions use the proved ordered theorem, never an
assumed universal hard theorem.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SignedCycle
open Candidate

theorem HardInput.crossedGAData_after_T {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) :
    I.cycle.theta T<I.cycle.theta A :=
  (I.fromCrossedGAData hAB O).intermediate_order hq

theorem HardInput.crossedBTData_before_G {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedBTData q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T)) :
    I.cycle.theta B<I.cycle.theta G :=
  (I.fromCrossedBTData hAB O).intermediate_order hq

theorem HardInput.no_crossed_TD_of_GA_aligned {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hGA : I.cycle.theta G=I.cycle.theta A)
    (hfloor : 67/200≤ -(I.cycle.point B).y) : I.cycle.theta D≤I.cycle.theta B := by
  by_contra! hBD
  have hTA : I.cycle.theta T≤I.cycle.theta A := by
    have hh := I.intermediate_order hq
    linarith
  have hAG : I.cycle.theta A≤I.cycle.theta G := hGA.symm.le
  have hbad (O : CrossedBTData q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T)) : False := by
    have hh := I.crossedBTData_before_G hq hAB O
    linarith
  have howner : I.witnesses.owner T=0 ∨ I.witnesses.owner T=2 := by
    simpa [normalOwners,T] using I.witnesses.allowed T
  have hw := I.witnesses.feasible T
  by_cases hlarge : 1/2≤ -(I.cycle.point B).y
  · rcases howner with howner | howner
    · have hTD : I.cycle.Feasible T 0 := by simpa only [howner] using hw
      obtain ⟨_,⟨O⟩⟩ := I.crossed_TD0_large_output hqL hq hAB hnorm hTA hAG hBD hlarge hTD
      exact hbad O
    · have hTD : I.cycle.Feasible T 2 := by simpa only [howner] using hw
      obtain ⟨_,⟨O⟩⟩ := I.crossed_TD2_large_output hqL hq hAB hnorm hTA hAG hBD.le hlarge hTD
      exact hbad O.toCrossedBTData
  · have hsmall : -(I.cycle.point B).y∈Icc (67/200 : ℝ) (1/2) :=
      ⟨hfloor,(lt_of_not_ge hlarge).le⟩
    rcases howner with howner | howner
    · have hTD : I.cycle.Feasible T 0 := by simpa only [howner] using hw
      obtain ⟨_,_,⟨O⟩⟩ := I.crossed_TD0_small_output hqL hq hAB hnorm hTA hAG hBD hsmall hTD
      exact hbad O
    · have hTD : I.cycle.Feasible T 2 := by simpa only [howner] using hw
      obtain ⟨_,_,⟨O⟩⟩ := I.crossed_TD2_small_output hqL hq hAB hnorm hTA hAG hBD hsmall hTD
      exact hbad O.toCrossedBTData

theorem HardInput.no_crossed_HG_of_BT_aligned {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTB : I.cycle.theta T=I.cycle.theta B)
    (hfloor : 67/200≤(I.cycle.point A).y) : I.cycle.theta A≤I.cycle.theta H := by
  by_contra! hHA
  have hTA : I.cycle.theta T≤I.cycle.theta A := by linarith
  have hAG : I.cycle.theta A≤I.cycle.theta G := by
    have hh := I.intermediate_order hq
    linarith
  have hbad (O : CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) : False := by
    have hh := I.crossedGAData_after_T hq hAB O
    linarith
  have howner : I.witnesses.owner H=0 ∨ I.witnesses.owner H=2 := by
    simpa [normalOwners,H] using I.witnesses.allowed H
  have hw := I.witnesses.feasible H
  by_cases hlarge : 1/2≤(I.cycle.point A).y
  · rcases howner with howner | howner
    · have hHG : I.cycle.Feasible H 0 := by simpa only [howner] using hw
      obtain ⟨_,⟨O⟩⟩ := I.crossed_HG0_large_output hqL hq hAB hnorm hTA hAG hHA.le hlarge hHG
      exact hbad O.toCrossedGAData
    · have hHG : I.cycle.Feasible H 2 := by simpa only [howner] using hw
      obtain ⟨_,⟨O⟩⟩ := I.crossed_HG2_large_output hqL hq hAB hnorm hTA hAG hHA hlarge hHG
      exact hbad O
  · have hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2) :=
      ⟨hfloor,(lt_of_not_ge hlarge).le⟩
    rcases howner with howner | howner
    · have hHG : I.cycle.Feasible H 0 := by simpa only [howner] using hw
      obtain ⟨_,_,⟨O⟩⟩ := I.crossed_HG0_small_output hqL hq hAB hnorm hTA hAG hHA hsmall hHG
      exact hbad O.toCrossedGAData
    · have hHG : I.cycle.Feasible H 2 := by simpa only [howner] using hw
      obtain ⟨_,_,⟨O⟩⟩ := I.crossed_HG2_small_output hqL hq hAB hnorm hTA hAG hHA hsmall hHG
      exact hbad O

theorem HardInput.common_H_all_anchors_on {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hGH : I.cycle.theta G=I.cycle.theta H)
    (hGA : I.cycle.theta G=I.cycle.theta A) : AllAnchorsOn qStar I.cycle := by
  have hcap : q≤qCap := hq.trans qStar_limits.2.2.le
  have hAupper := I.outerGeometry.nonpositive_HG_middle_upper hcap hGA.symm.le hGH.le
  have hBfloor : 67/200≤ -(I.cycle.point B).y := by linarith
  have hDB := I.no_crossed_TD_of_GA_aligned hqL hcap hAB hnorm hGA hBfloor
  have hAH : I.cycle.theta A≤I.cycle.theta H := by linarith
  have hTB : I.cycle.theta T≤I.cycle.theta B := by
    have hh := I.intermediate_order hcap
    linarith
  obtain ⟨_,_,_,_,_,_,_,_,hOn,_⟩ :=
    I.ordered_hard_sharp hqL hq hAB hnorm hAH hGA.symm.le hDB hTB
  exact hOn

theorem HardInput.common_D_all_anchors_on {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hTB : I.cycle.theta T=I.cycle.theta B) : AllAnchorsOn qStar I.cycle := by
  have hcap : q≤qCap := hq.trans qStar_limits.2.2.le
  have hAG' : I.outerGeometry.reflected.cycle.theta A≤I.outerGeometry.reflected.cycle.theta G := by
    change I.cycle.theta B-I.cycle.theta B≤I.cycle.theta B-I.cycle.theta T
    linarith
  have hGH' : I.outerGeometry.reflected.cycle.theta G≤I.outerGeometry.reflected.cycle.theta H := by
    change I.cycle.theta B-I.cycle.theta T≤I.cycle.theta B-I.cycle.theta D
    linarith
  have hBupper := I.outerGeometry.reflected.nonpositive_HG_middle_upper hcap hAG' hGH'
  change -(I.cycle.point B).y<133/200 at hBupper
  have hAfloor : 67/200≤(I.cycle.point A).y := by linarith
  have hAH := I.no_crossed_HG_of_BT_aligned hqL hcap hAB hnorm hTB hAfloor
  have hAG : I.cycle.theta A≤I.cycle.theta G := by
    have hh := I.intermediate_order hcap
    linarith
  have hDB : I.cycle.theta D≤I.cycle.theta B := by linarith
  obtain ⟨_,_,_,_,_,_,_,_,hOn,_⟩ :=
    I.ordered_hard_sharp hqL hq hAB hnorm hAH hAG hDB hTB.le
  exact hOn

theorem HardInput.crossed_clamp_endpoint_impossible {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar) (hHA : I.cycle.theta H≤I.cycle.theta A)
    (O : CrossedClampData q (I.cycle.point H) (I.cycle.point T)
      0 (I.cycle.theta H-I.cycle.theta T)) : False := by
  have O' : CrossedClampData q (I.cycle.point H) (I.cycle.point T)
      (I.cycle.theta H-I.cycle.theta H) (I.cycle.theta H-I.cycle.theta T) := by
    simpa only [sub_self] using O
  let J := I.fromCrossedClamp ⟨le_rfl,hHA⟩ O'
  have hOn := J.common_H_all_anchors_on hqL hq rfl O'.tangent_sum rfl rfl
  have hA := hOn A (by simp [anchorVertices])
  have hstrict : (J.cycle.point A).circle<q := O'.A_strict
  rw [hA] at hstrict
  linarith

theorem HardInput.crossed_TD_clamp_endpoint_impossible {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar) (hBD : I.cycle.theta B≤I.cycle.theta D)
    (O : CrossedTDClampData q (I.cycle.point G) (I.cycle.point D)
      0 (I.cycle.theta G-I.cycle.theta D)) : False := by
  have O' : CrossedTDClampData q (I.cycle.point G) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta D) (I.cycle.theta G-I.cycle.theta D) := by
    simpa only [sub_self] using O
  let J := I.fromCrossedTDClamp ⟨hBD,le_rfl⟩ O'
  have hOn := J.common_D_all_anchors_on hqL hq rfl O'.tangent_sum rfl rfl
  have hA := hOn A (by simp [anchorVertices])
  have hstrict : (J.cycle.point A).circle<q := O'.A_strict
  rw [hA] at hstrict
  linarith

end SquaresInCircles.Eight.TableFree.SignedCycle
