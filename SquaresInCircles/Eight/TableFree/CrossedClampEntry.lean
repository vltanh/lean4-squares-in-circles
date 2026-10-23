module

public import SquaresInCircles.Eight.TableFree.CrossedSmallConstruction
public import SquaresInCircles.Eight.TableFree.SmallCancelingGeometry
public import SquaresInCircles.Eight.TableFree.CrossedCancelingGeometry
public import SquaresInCircles.Eight.TableFree.HardOuterOrder
public import SquaresInCircles.Eight.TableFree.CrossedBTGeometry

/-!
# Every crossed GA reduction supplies the common-clamp hypotheses

Uncompiled source draft.  The aligned hard contact bounds the actual G
tangent by the actual A primary coordinate.  Together with the short
HG0 error this forces the unchanged H tangent above .75 and A below
.72.  The opposite tangent is therefore above .28, so its actual sign
follows from the previously proved whole-order sign theorem.  No new
normal-sign premise is introduced by the common-clamp entry.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate

namespace CrossedClampEntry

theorem HG_tangent_lower {H G : SignedPoint} {r rmax gmax : ℝ}
    (hr : r∈Icc 0 rmax) (hrmax : rmax≤frameCap)
    (hGa : G.a≤283/200) (hGy : -gmax≤G.y) (hgmax : gmax≤1/2)
    (hHG : zeroFeasible H G r 0) :
    1/2+(1/2-gmax)*(1-rmax^2/2)-(183/200)*rmax≤H.y := by
  have hi : r∈Icc 0 frameCap := ⟨hr.1,hr.2.trans hrmax⟩
  have ht := transport_trig hi
  have hc0 : 0≤Real.cos r := by linarith [ht.1]
  have hr2 := pow_le_pow_left₀ hr.1 hr.2 2
  have hc : 1-rmax^2/2≤Real.cos r := by nlinarith [Real.one_sub_sq_div_two_le_cos r]
  have hs : Real.sin r≤rmax := (Real.sin_le hr.1).trans hr.2
  have hm1 := mul_le_mul_of_nonneg_right
    (show 1/2-gmax≤1/2+G.y by linarith) hc0
  have hm2 := mul_le_mul_of_nonneg_left hc (show 0≤1/2-gmax by linarith)
  have hm3 := mul_le_mul_of_nonneg_right
    (show G.a-1/2≤183/200 by linarith) ht.2.2.1
  have hm4 := mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤183/200)
  have hh := hHG
  rw [zeroFeasible,edgeWidth_positive_formula hi] at hh
  simp only [zeroProjection,Matrix.cons_val_zero] at hh
  nlinarith

theorem aligned_G_primary {G A : SignedPoint} (hGA : quarterFeasible G A 0 0) :
    -G.y≤A.a-1 := by
  have hh := SignedOppositeHardEnvelope.negative_hard_contact
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show quarterFeasible G A (-(0:ℝ)) 0 by simpa using hGA)
  simp only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero] at hh
  linarith

theorem H_high_large {q r : ℝ} {H G A : SignedPoint}
    (hq : q≤qCap) (hAs : A.Sorted) (hAq : A.Contained q) (hAy : 1/2≤A.y)
    (hGa : G.a≤283/200) (hr : r∈Icc (0:ℝ) (1/25))
    (hHG : zeroFeasible H G r 0) (hGA : quarterFeasible G A 0 0) : 3/4<H.y := by
  have hcircle : (A.a+1/2)^2+(A.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg (show 0≤A.y by linarith)]
      using hAq.trans hq
  have hAa : A.a<151/125 := by
    dsimp [qCap] at hcircle
    nlinarith [hAs.1,sq_nonneg (A.y-1/2)]
  have hGy : -(26/125:ℝ)≤G.y := by linarith [aligned_G_primary hGA]
  have hh := HG_tangent_lower hr (by norm_num [frameCap] : (1/25:ℝ)≤frameCap)
    hGa hGy (by norm_num : (26/125:ℝ)≤1/2) hHG
  norm_num at hh ⊢
  linarith

theorem H_high_small {q r : ℝ} {H G A : SignedPoint}
    (hq : q≤qCap) (hAs : A.Sorted) (hAq : A.Contained q) (hAy : 47/98≤A.y)
    (hGa : G.a≤283/200) (hr : r∈Icc (0:ℝ) (1/100))
    (hHG : zeroFeasible H G r 0) (hGA : quarterFeasible G A 0 0) : 3/4<H.y := by
  have hcircle : (A.a+1/2)^2+(A.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg (show 0≤A.y by linarith)]
      using hAq.trans hq
  have hAa : A.a<61/50 := by
    dsimp [qCap] at hcircle
    nlinarith [hAs.1,sq_nonneg (A.y-47/98)]
  have hGy : -(11/50:ℝ)≤G.y := by linarith [aligned_G_primary hGA]
  have hh := HG_tangent_lower hr (by norm_num [frameCap] : (1/100:ℝ)≤frameCap)
    hGa hGy (by norm_num : (11/50:ℝ)≤1/2) hHG
  norm_num at hh ⊢
  linarith

theorem A_tangent_upper {q r : ℝ} {H G A : SignedPoint}
    (hq : q≤qCap) (hAs : A.Sorted) (hAq : A.Contained q) (hHy : H.y<9/10)
    (hGa : G.a≤283/200) (hr : r∈Icc (0:ℝ) (1/25))
    (hHG : zeroFeasible H G r 0) (hGA : quarterFeasible G A 0 0) : A.y<18/25 := by
  by_contra hAy
  have hAy' : 18/25≤A.y := le_of_not_gt hAy
  have hcircle : (A.a+1/2)^2+(A.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg (show 0≤A.y by linarith)]
      using hAq.trans hq
  have hAa : A.a<53/50 := by
    dsimp [qCap] at hcircle
    nlinarith [hAs.1,sq_nonneg (A.y-18/25)]
  have hGy : -(3/50:ℝ)≤G.y := by linarith [aligned_G_primary hGA]
  have hh := HG_tangent_lower hr (by norm_num [frameCap] : (1/25:ℝ)≤frameCap)
    hGa hGy (by norm_num : (3/50:ℝ)≤1/2) hHG
  norm_num at hh
  linarith

end CrossedClampEntry

namespace SignedCycle

structure CommonFrameEntry {q : ℝ} (I : HardOuterGeometry q) : Prop where
  AB_aligned : I.cycle.theta A=I.cycle.theta B
  GA_aligned : I.cycle.theta G=I.cycle.theta A
  tangent_sum : (I.cycle.point A).y-(I.cycle.point B).y=1
  G_nonpos : (I.cycle.point G).y≤0
  T_positive : 0<(I.cycle.point T).y
  H_before : I.cycle.theta H<I.cycle.theta A
  T_before : I.cycle.theta T<I.cycle.theta A
  short_error : I.cycle.theta A-I.cycle.theta H<1/25
  H_tangent : (I.cycle.point H).y∈Ioo (3/4:ℝ) (9/10)
  opposite_tangent : 7/25< -(I.cycle.point B).y
  HG_zero : I.cycle.Feasible H 0

theorem HardOuterGeometry.common_HG0_entry {q : ℝ} (I : HardOuterGeometry q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hGA : I.cycle.theta G=I.cycle.theta A)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hr : I.cycle.theta A-I.cycle.theta H<1/25)
    (hG : (I.cycle.point G).y≤0) (hHG : I.cycle.Feasible H 0)
    (hentry : 1/2≤(I.cycle.point A).y ∨
      (47/98≤(I.cycle.point A).y ∧ I.cycle.theta A-I.cycle.theta H<1/100)) :
    CommonFrameEntry I := by
  let r := I.cycle.theta A-I.cycle.theta H
  have hri : r∈Icc (0:ℝ) (1/25) := ⟨by dsimp [r]; linarith,hr.le⟩
  have hGa := (SignedPoint.coordinate_bounds (I.necessary.sorted G) (I.necessary.core G)
    (I.necessary.contained G) hq).2.1.le
  have hHy : (I.cycle.point H).y<9/10 :=
    (le_abs_self _).trans_lt ((SignedPoint.coordinate_bounds (I.necessary.sorted H)
      (I.necessary.core H) (I.necessary.contained H) hq).2.2)
  have hGA0 : quarterFeasible (I.cycle.point G) (I.cycle.point A) 0 0 := by
    simpa [Feasible,slack,edge,word,delta,next,G,A,hGA,quarterFeasible,sub_nonneg]
      using I.GA_hard
  have hHG0 : zeroFeasible (I.cycle.point H) (I.cycle.point G) r 0 := by
    simpa [r,Feasible,slack,edge,word,delta,next,H,G,hGA,zeroFeasible,sub_nonneg]
      using hHG
  have hAy := CrossedClampEntry.A_tangent_upper hq (I.necessary.sorted A)
    (I.necessary.contained A) hHy hGa hri hHG0 hGA0
  have hHhigh : 3/4<(I.cycle.point H).y := by
    rcases hentry with hlarge | hsmall
    · exact CrossedClampEntry.H_high_large hq (I.necessary.sorted A)
        (I.necessary.contained A) hlarge hGa hri hHG0 hGA0
    · exact CrossedClampEntry.H_high_small hq (I.necessary.sorted A)
        (I.necessary.contained A) hsmall.1 hGa ⟨hri.1,hsmall.2.le⟩ hHG0 hGA0
  have hTA : I.cycle.theta T<I.cycle.theta A := by
    rw [←hGA]
    exact I.intermediate_order hq
  have hBfloor : 7/25< -(I.cycle.point B).y := by linarith
  have hT : 0<(I.cycle.point T).y := by
    by_cases hlargeB : 1/2≤ -(I.cycle.point B).y
    · exact I.large_middle_T_positive hq hAB hnorm hTA.le hGA.symm.le hlargeB
    · exact I.small_middle_T_positive hqL hq hAB hnorm
        ⟨hBfloor.le,(lt_of_not_ge hlargeB).le⟩ hTA.le hGA.symm.le
        (I.small_intermediate_signs hq).2
  exact ⟨hAB,hGA,hnorm,hG,hT,hHA,hTA,hr,⟨hHhigh,hHy⟩,hBfloor,hHG⟩

theorem HardInput.fromCrossedGAData_entry {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (O : CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A))
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hr : I.cycle.theta A-I.cycle.theta H<1/25)
    (hentry : 1/2≤(I.cycle.point A).y ∨
      (47/98≤(I.cycle.point A).y ∧ I.cycle.theta A-I.cycle.theta H<1/100)) :
    CommonFrameEntry (I.fromCrossedGAData hAB O).outerGeometry := by
  let J := I.fromCrossedGAData hAB O
  apply J.outerGeometry.common_HG0_entry hqL hq
  · simpa [J,HardInput.fromCrossedGAData,crossedGACycle,A,B,G] using hAB
  · simpa [J,HardInput.fromCrossedGAData,crossedGACycle,A,B,G,O.A_tangent] using hnorm
  · simp [J,HardInput.fromCrossedGAData,crossedGACycle,A,G]
  · simpa [J,HardInput.fromCrossedGAData,crossedGACycle,A,H,G] using hHA
  · simpa [J,HardInput.fromCrossedGAData,crossedGACycle,A,H,G] using hr
  · exact O.G_nonpos
  · simpa [J,HardInput.fromCrossedGAData,crossedGACycle,Feasible,slack,edge,word,delta,next,
      H,G,A,zeroFeasible,sub_nonneg] using O.HG_zero
  · simpa [J,HardInput.fromCrossedGAData,crossedGACycle,A,H,G,O.A_tangent] using hentry

theorem HardInput.crossed_HG_large_entry {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A) (hlarge : 1/2≤(I.cycle.point A).y) :
    ∃ O : CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A),
      CommonFrameEntry (I.fromCrossedGAData hAB O).outerGeometry := by
  have howner : I.witnesses.owner H=0 ∨ I.witnesses.owner H=2 := by
    simpa [normalOwners,H] using I.witnesses.allowed H
  rcases howner with h0 | h2
  · have hHG : I.cycle.Feasible H 0 := by simpa [h0] using I.witnesses.feasible H
    obtain ⟨hr,⟨O⟩⟩ := I.crossed_HG0_large_output hqL hq hAB hnorm hTA hAG hHA.le hlarge hHG
    exact ⟨O.toCrossedGAData,I.fromCrossedGAData_entry hqL hq hAB hnorm
      O.toCrossedGAData hHA hr (Or.inl hlarge)⟩
  · have hHG : I.cycle.Feasible H 2 := by simpa [h2] using I.witnesses.feasible H
    obtain ⟨hr,⟨O⟩⟩ := I.crossed_HG2_large_output hqL hq hAB hnorm hTA hAG hHA hlarge hHG
    exact ⟨O,I.fromCrossedGAData_entry hqL hq hAB hnorm O hHA hr (Or.inl hlarge)⟩

theorem HardInput.crossed_HG_small_entry {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hsmall : (I.cycle.point A).y∈Icc (67/200:ℝ) (1/2)) :
    ∃ O : CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A),
      CommonFrameEntry (I.fromCrossedGAData hAB O).outerGeometry := by
  have howner : I.witnesses.owner H=0 ∨ I.witnesses.owner H=2 := by
    simpa [normalOwners,H] using I.witnesses.allowed H
  rcases howner with h0 | h2
  · have hHG : I.cycle.Feasible H 0 := by simpa [h0] using I.witnesses.feasible H
    obtain ⟨hAy,hr,⟨O⟩⟩ := I.crossed_HG0_small_output hqL hq hAB hnorm hTA hAG hHA hsmall hHG
    exact ⟨O.toCrossedGAData,I.fromCrossedGAData_entry hqL hq hAB hnorm
      O.toCrossedGAData hHA (by linarith) (Or.inr ⟨hAy.le,hr⟩)⟩
  · have hHG : I.cycle.Feasible H 2 := by simpa [h2] using I.witnesses.feasible H
    obtain ⟨hAy,hr,⟨O⟩⟩ := I.crossed_HG2_small_output hqL hq hAB hnorm hTA hAG hHA hsmall hHG
    exact ⟨O,I.fromCrossedGAData_entry hqL hq hAB hnorm O hHA
      (by linarith) (Or.inr ⟨hAy.le,hr⟩)⟩

/-- The reflected entry is taken only after constructing the actual
BT descendant in the original cycle.  Its original E remains fixed;
the reflected object is local geometry with the proved source budget. -/
theorem HardInput.fromCrossedBTData_entry {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (O : CrossedBTData q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T))
    (hBD : I.cycle.theta B<I.cycle.theta D)
    (hr : I.cycle.theta D-I.cycle.theta B<1/25)
    (hentry : 1/2≤ -(I.cycle.point B).y ∨
      (47/98≤ -(I.cycle.point B).y ∧ I.cycle.theta D-I.cycle.theta B<1/100)) :
    CommonFrameEntry (I.fromCrossedBTData hAB O).outerGeometry.reflected := by
  let J := I.fromCrossedBTData hAB O
  let R := J.outerGeometry.reflected
  have hJAB : J.cycle.theta A=J.cycle.theta B := hAB
  have hJnorm : (J.cycle.point A).y-(J.cycle.point B).y=1 := by
    change (I.cycle.point A).y-O.pointB.y=1
    rw [O.B_tangent]
    exact hnorm
  have hRAy : (R.cycle.point A).y= -(I.cycle.point B).y := by
    change -O.pointB.y= -(I.cycle.point B).y
    rw [O.B_tangent]
  have hRHr : R.cycle.theta A-R.cycle.theta H=I.cycle.theta D-I.cycle.theta B := by
    change (I.cycle.theta B-I.cycle.theta B)-(I.cycle.theta B-I.cycle.theta D)=
      I.cycle.theta D-I.cycle.theta B
    ring
  apply R.common_HG0_entry hqL hq
  · change J.cycle.theta B-J.cycle.theta B=J.cycle.theta B-J.cycle.theta A
    linarith
  · change -(J.cycle.point B).y-(-(J.cycle.point A).y)=1
    linarith
  · change I.cycle.theta B-I.cycle.theta B=I.cycle.theta B-I.cycle.theta B
    rfl
  · change I.cycle.theta B-I.cycle.theta D<I.cycle.theta B-I.cycle.theta B
    linarith
  · rw [hRHr]
    exact hr
  · change -O.pointT.y≤0
    linarith [O.T_nonneg]
  · have hJTD : J.cycle.Feasible T 2 := by
      simpa [J,HardInput.fromCrossedBTData,crossedBTCycle,Feasible,slack,edge,word,delta,next,
        B,T,D,zeroFeasible,sub_nonneg] using O.TD_two
    have hh := (reflected_feasible J.cycle H 2).2
      (by simpa [reflectedIndex,next,H,T] using hJTD)
    simpa [R,HardOuterGeometry.reflected,HardInput.outerGeometry,reflectedOwner] using hh
  · rw [hRAy,hRHr]
    exact hentry

theorem HardInput.crossed_TD_large_entry {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hBD : I.cycle.theta B<I.cycle.theta D) (hlarge : 1/2≤ -(I.cycle.point B).y) :
    ∃ O : CrossedBTData q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T),
      CommonFrameEntry (I.fromCrossedBTData hAB O).outerGeometry.reflected := by
  have howner : I.witnesses.owner T=0 ∨ I.witnesses.owner T=2 := by
    simpa [normalOwners,T] using I.witnesses.allowed T
  rcases howner with h0 | h2
  · have hTD : I.cycle.Feasible T 0 := by simpa [h0] using I.witnesses.feasible T
    obtain ⟨hr,⟨O⟩⟩ := I.crossed_TD0_large_output hqL hq hAB hnorm hTA hAG hBD hlarge hTD
    exact ⟨O,I.fromCrossedBTData_entry hqL hq hAB hnorm O hBD hr (Or.inl hlarge)⟩
  · have hTD : I.cycle.Feasible T 2 := by simpa [h2] using I.witnesses.feasible T
    obtain ⟨hr,⟨O⟩⟩ := I.crossed_TD2_large_output hqL hq hAB hnorm hTA hAG hBD.le hlarge hTD
    exact ⟨O.toCrossedBTData,I.fromCrossedBTData_entry hqL hq hAB hnorm
      O.toCrossedBTData hBD hr (Or.inl hlarge)⟩

theorem HardInput.crossed_TD_small_entry {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hBD : I.cycle.theta B<I.cycle.theta D)
    (hsmall : -(I.cycle.point B).y∈Icc (67/200:ℝ) (1/2)) :
    ∃ O : CrossedBTData q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T),
      CommonFrameEntry (I.fromCrossedBTData hAB O).outerGeometry.reflected := by
  have howner : I.witnesses.owner T=0 ∨ I.witnesses.owner T=2 := by
    simpa [normalOwners,T] using I.witnesses.allowed T
  rcases howner with h0 | h2
  · have hTD : I.cycle.Feasible T 0 := by simpa [h0] using I.witnesses.feasible T
    obtain ⟨hBy,hr,⟨O⟩⟩ := I.crossed_TD0_small_output hqL hq hAB hnorm hTA hAG hBD hsmall hTD
    exact ⟨O,I.fromCrossedBTData_entry hqL hq hAB hnorm O hBD
      (by linarith) (Or.inr ⟨hBy.le,hr⟩)⟩
  · have hTD : I.cycle.Feasible T 2 := by simpa [h2] using I.witnesses.feasible T
    obtain ⟨hBy,hr,⟨O⟩⟩ := I.crossed_TD2_small_output hqL hq hAB hnorm hTA hAG hBD hsmall hTD
    exact ⟨O.toCrossedBTData,I.fromCrossedBTData_entry hqL hq hAB hnorm
      O.toCrossedBTData hBD (by linarith) (Or.inr ⟨hBy.le,hr⟩)⟩

end SignedCycle
end SquaresInCircles.Eight.TableFree
