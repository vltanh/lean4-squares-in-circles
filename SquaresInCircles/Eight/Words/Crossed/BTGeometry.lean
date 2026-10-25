module

public import SquaresInCircles.Eight.Words.Crossed.BTOutput
public import SquaresInCircles.Eight.Words.Crossed.CancelingGeometry
public import SquaresInCircles.Eight.Words.Crossed.SmallConstruction
public import SquaresInCircles.Eight.Owners.Small.CancelingGeometry

/-!
# Eight squares: all four crossed BT-side outputs at the original E

The local necessary geometry and proved source
budget are reflected, each corresponding HG theorem constructs its
actual same-q output, and only the local output is reflected back.
The public hard-source statements derive their intermediate sign bounds
from the original system and retain the original E and mixed witnesses.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCycle
open Candidate

theorem HardOuterGeometry.reflected_middle_parameters {q : ℝ}
    (I : HardOuterGeometry q) (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G) :
    I.reflected.cycle.theta A=I.reflected.cycle.theta B ∧
      (I.reflected.cycle.point A).y-(I.reflected.cycle.point B).y=1 ∧
      I.reflected.cycle.theta T≤I.reflected.cycle.theta A ∧
      I.reflected.cycle.theta A≤I.reflected.cycle.theta G := by
  refine ⟨?_,?_,?_,?_⟩
  · change I.cycle.theta B-I.cycle.theta B=I.cycle.theta B-I.cycle.theta A
    linarith
  · change -(I.cycle.point B).y-(-(I.cycle.point A).y)=1
    linarith
  · change I.cycle.theta B-I.cycle.theta G≤I.cycle.theta B-I.cycle.theta B
    linarith
  · change I.cycle.theta B-I.cycle.theta B≤I.cycle.theta B-I.cycle.theta T
    linarith

theorem HardInput.crossed_TD2_large_output {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hBD : I.cycle.theta B≤I.cycle.theta D)
    (hlarge : 1/2≤ -(I.cycle.point B).y) (hTD : I.cycle.Feasible T 2) :
    I.cycle.theta D-I.cycle.theta B<1/25 ∧
      Nonempty (CrossedBTOutput q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
        (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T)) := by
  let J := I.outerGeometry.reflected
  obtain ⟨hJAB,hJsum,hJTA,hJAG⟩ := I.outerGeometry.reflected_middle_parameters hAB hnorm hTA hAG
  have hJHA : J.cycle.theta H≤J.cycle.theta A := by
    change I.cycle.theta B-I.cycle.theta D≤I.cycle.theta B-I.cycle.theta B
    linarith
  have hJlarge : 1/2≤(J.cycle.point A).y := hlarge
  have hJHG : J.cycle.Feasible H 0 := by
    have hh := (reflected_feasible I.cycle H 2).2
      (by simpa [reflectedIndex,next,H,T] using hTD)
    simpa [J,HardOuterGeometry.reflected,HardInput.outerGeometry,reflectedOwner] using hh
  obtain ⟨hshort,⟨O⟩⟩ := J.crossed_HG0_large_output hqL hq hJAB hJsum hJTA hJAG
    hJHA hJlarge hJHG
  have O' : CrossedGAOutput q (I.cycle.point D).reflect (I.cycle.point T).reflect
      (I.cycle.point B).reflect (I.cycle.theta D-I.cycle.theta B)
      (I.cycle.theta B-I.cycle.theta T) := by
    change CrossedGAOutput q (I.cycle.point D).reflect (I.cycle.point T).reflect
      (I.cycle.point B).reflect
      ((I.cycle.theta B-I.cycle.theta B)-(I.cycle.theta B-I.cycle.theta D))
      ((I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta B)) at O
    simpa only [sub_self,sub_zero,zero_sub,neg_sub] using O
  refine ⟨?_,⟨O'.reflectBT⟩⟩
  change (I.cycle.theta B-I.cycle.theta B)-(I.cycle.theta B-I.cycle.theta D)<1/25 at hshort
  simpa only [sub_self,zero_sub,neg_sub] using hshort

theorem HardInput.crossed_TD0_large_output {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hBD : I.cycle.theta B<I.cycle.theta D)
    (hlarge : 1/2≤ -(I.cycle.point B).y) (hTD : I.cycle.Feasible T 0) :
    I.cycle.theta D-I.cycle.theta B<1/25 ∧
      Nonempty (CrossedBTData q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
        (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T)) := by
  let J := I.outerGeometry.reflected
  obtain ⟨hJAB,hJsum,hJTA,hJAG⟩ := I.outerGeometry.reflected_middle_parameters hAB hnorm hTA hAG
  have hJHA : J.cycle.theta H<J.cycle.theta A := by
    change I.cycle.theta B-I.cycle.theta D<I.cycle.theta B-I.cycle.theta B
    linarith
  have hJlarge : 1/2≤(J.cycle.point A).y := hlarge
  have hJHG : J.cycle.Feasible H 2 := by
    have hh := (reflected_feasible I.cycle H 0).2
      (by simpa [reflectedIndex,next,H,T] using hTD)
    simpa [J,HardOuterGeometry.reflected,HardInput.outerGeometry,reflectedOwner] using hh
  have hJT : -(1/10 : ℝ)<(J.cycle.point T).y := by
    change -(1/10 : ℝ)< -(I.cycle.point G).y
    linarith [(I.small_intermediate_signs hq).1]
  obtain ⟨O⟩ := J.crossed_HG2_large_data hqL hq hJAB hJsum hJTA hJAG hJHA hJlarge hJHG hJT
  let K := J.fromCrossedGAData hJAB O
  have hKsum : (K.cycle.point A).y-(K.cycle.point B).y=1 := by
    change O.pointA.y-(J.cycle.point B).y=1
    rw [O.A_tangent]
    exact hJsum
  have hKlarge : 1/2≤(K.cycle.point A).y := by
    change 1/2≤O.pointA.y
    rw [O.A_tangent]
    exact hJlarge
  have hKHG : K.cycle.Feasible H 0 := by
    simpa [K,HardOuterGeometry.fromCrossedGAData,crossedGACycle,Feasible,slack,edge,word,
      delta,next,H,G,A,zeroFeasible,sub_nonneg] using O.HG_zero
  have hcap := K.crossed_HG0_large_reserve hqL hq hJAB hKsum hJTA le_rfl hJHA.le hKlarge hKHG
  have O' : CrossedGAData q (I.cycle.point D).reflect (I.cycle.point T).reflect
      (I.cycle.point B).reflect (I.cycle.theta D-I.cycle.theta B)
      (I.cycle.theta B-I.cycle.theta T) := by
    change CrossedGAData q (I.cycle.point D).reflect (I.cycle.point T).reflect
      (I.cycle.point B).reflect
      ((I.cycle.theta B-I.cycle.theta B)-(I.cycle.theta B-I.cycle.theta D))
      ((I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta B)) at O
    simpa only [sub_self,sub_zero,zero_sub,neg_sub] using O
  refine ⟨?_,⟨O'.reflectBT⟩⟩
  have hh := hcap.1
  change (I.cycle.theta B-I.cycle.theta B)-(I.cycle.theta B-I.cycle.theta D)<1/25 at hh
  simpa only [sub_self,zero_sub,neg_sub] using hh

theorem HardInput.crossed_TD2_small_output {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hBD : I.cycle.theta B<I.cycle.theta D)
    (hsmall : -(I.cycle.point B).y∈Icc (67/200 : ℝ) (1/2))
    (hTD : I.cycle.Feasible T 2) :
    47/98< -(I.cycle.point B).y ∧ I.cycle.theta D-I.cycle.theta B<1/100 ∧
      Nonempty (CrossedBTOutput q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
        (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T)) := by
  let J := I.outerGeometry.reflected
  obtain ⟨hJAB,hJsum,hJTA,hJAG⟩ := I.outerGeometry.reflected_middle_parameters hAB hnorm hTA hAG
  have hJHA : J.cycle.theta H<J.cycle.theta A := by
    change I.cycle.theta B-I.cycle.theta D<I.cycle.theta B-I.cycle.theta B
    linarith
  have hJsmall : (J.cycle.point A).y∈Icc (67/200 : ℝ) (1/2) := hsmall
  have hTy := I.small_middle_T_positive hqL hq hAB hnorm
    ⟨by linarith [hsmall.1],hsmall.2⟩ hTA hAG
  have hJGy : (J.cycle.point G).y≤0 := by
    change -(I.cycle.point T).y≤0
    linarith
  have hJHG : J.cycle.Feasible H 0 := by
    have hh := (reflected_feasible I.cycle H 2).2
      (by simpa [reflectedIndex,next,H,T] using hTD)
    simpa [J,HardOuterGeometry.reflected,HardInput.outerGeometry,reflectedOwner] using hh
  obtain ⟨hsmall',hshort,⟨O⟩⟩ := J.crossed_HG0_small_output hqL hq hJAB hJsum hJTA hJAG
    hJHA hJsmall hJGy hJHG
  have O' : CrossedGAOutput q (I.cycle.point D).reflect (I.cycle.point T).reflect
      (I.cycle.point B).reflect (I.cycle.theta D-I.cycle.theta B)
      (I.cycle.theta B-I.cycle.theta T) := by
    change CrossedGAOutput q (I.cycle.point D).reflect (I.cycle.point T).reflect
      (I.cycle.point B).reflect
      ((I.cycle.theta B-I.cycle.theta B)-(I.cycle.theta B-I.cycle.theta D))
      ((I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta B)) at O
    simpa only [sub_self,sub_zero,zero_sub,neg_sub] using O
  refine ⟨hsmall',?_,⟨O'.reflectBT⟩⟩
  change (I.cycle.theta B-I.cycle.theta B)-(I.cycle.theta B-I.cycle.theta D)<1/100 at hshort
  simpa only [sub_self,zero_sub,neg_sub] using hshort

theorem HardInput.crossed_TD0_small_output {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hBD : I.cycle.theta B<I.cycle.theta D)
    (hsmall : -(I.cycle.point B).y∈Icc (67/200 : ℝ) (1/2))
    (hTD : I.cycle.Feasible T 0) :
    47/98< -(I.cycle.point B).y ∧ I.cycle.theta D-I.cycle.theta B<1/100 ∧
      Nonempty (CrossedBTData q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
        (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T)) := by
  let J := I.outerGeometry.reflected
  obtain ⟨hJAB,hJsum,hJTA,hJAG⟩ := I.outerGeometry.reflected_middle_parameters hAB hnorm hTA hAG
  have hJHA : J.cycle.theta H<J.cycle.theta A := by
    change I.cycle.theta B-I.cycle.theta D<I.cycle.theta B-I.cycle.theta B
    linarith
  have hJsmall : (J.cycle.point A).y∈Icc (67/200 : ℝ) (1/2) := hsmall
  have hTy := I.small_middle_T_positive hqL hq hAB hnorm
    ⟨by linarith [hsmall.1],hsmall.2⟩ hTA hAG
  have hJGy : (J.cycle.point G).y≤0 := by
    change -(I.cycle.point T).y≤0
    linarith
  have hJHG : J.cycle.Feasible H 2 := by
    have hh := (reflected_feasible I.cycle H 0).2
      (by simpa [reflectedIndex,next,H,T] using hTD)
    simpa [J,HardOuterGeometry.reflected,HardInput.outerGeometry,reflectedOwner] using hh
  obtain ⟨hsmall',hshort,⟨O⟩⟩ := J.crossed_HG2_small_output hqL hq hJAB hJsum hJTA hJAG
    hJHA hJsmall hJGy hJHG
  have O' : CrossedGAData q (I.cycle.point D).reflect (I.cycle.point T).reflect
      (I.cycle.point B).reflect (I.cycle.theta D-I.cycle.theta B)
      (I.cycle.theta B-I.cycle.theta T) := by
    change CrossedGAData q (I.cycle.point D).reflect (I.cycle.point T).reflect
      (I.cycle.point B).reflect
      ((I.cycle.theta B-I.cycle.theta B)-(I.cycle.theta B-I.cycle.theta D))
      ((I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta B)) at O
    simpa only [sub_self,sub_zero,zero_sub,neg_sub] using O
  refine ⟨hsmall',?_,⟨O'.reflectBT⟩⟩
  change (I.cycle.theta B-I.cycle.theta B)-(I.cycle.theta B-I.cycle.theta D)<1/100 at hshort
  simpa only [sub_self,zero_sub,neg_sub] using hshort

end SquaresInCircles.Eight.SignedCycle
