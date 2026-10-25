module

public import SquaresInCircles.Eight.TableFree.NegativeNoncancelingCycle
public import SquaresInCircles.Eight.TableFree.AlignedMixedE

/-!
# Actual shared-circle bounds with retained negative core composites

Uncompiled draft.  Each outer path is either aligned or retains its
original negative HG0/TD2 pair.  The same original core supplies its
composite.  Shared A/B circles and the actual AB axis then bound all four
anchors and the total H/D span.  No E frame, sign change, or mixed-owner
selection enters these non-E estimates.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace NonpositiveChainBounds
open PositiveCancelingOuter NegativeNoncancelingBarrier AlignedChainBounds

theorem single_contact {H A : SignedPoint} {Θ t : ℝ}
    (hHy : H.y<9/10) (hAa : 1/2<A.a) (hAy : 0≤A.y)
    (hAc : A.Contained qCap) (hΘ : Θ∈Icc 0 (7/10 : ℝ)) (ht : t∈Icc 0 Θ)
    (hf : 0≤NegativeNoncancelingBarrier.F H A Θ t) :
    11/10<A.a ∧ A.y<133/200 ∧
      2+(A.y+1/2)*Real.sin t+(9/10)*Real.sin (Θ-t)≤H.y+A.a := by
  have ht' : t∈Icc 0 (7/10 : ℝ) := ⟨ht.1,ht.2.trans hΘ.2⟩
  have he : Θ-t∈Icc 0 (7/10 : ℝ) :=
    ⟨by linarith [ht.2],by linarith [ht.1,hΘ.2]⟩
  have hV := feasible_primary hHy he hf
  have hD := D_lower he
  have hVu := V_upper hAa hAy ht'
  have ha : 11/10<A.a := by linarith
  have hb : A.y<133/200 := by
    have hc := hAc
    rw [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hAy] at hc
    dsimp [qCap] at hc
    by_contra! hbad
    have hAsq := pow_le_pow_left₀ (show (0:ℝ)≤8/5 by norm_num)
      (show 8/5≤A.a+1/2 by linarith) 2
    have hYsq := pow_le_pow_left₀ (show (0:ℝ)≤233/200 by norm_num)
      (show 233/200≤A.y+1/2 by linarith) 2
    nlinarith
  have hloss := AlignedMixedE.cosine_loss he
  have hetrig := transport_trig he
  have htloss := mul_nonneg (show 0≤A.a-1/2 by linarith)
    (sub_nonneg.mpr (Real.cos_le_one t))
  have hVl : 1-V A t≤2/5 := by linarith
  have hVloss := mul_le_mul_of_nonneg_right hVl
    (sub_nonneg.mpr (Real.cos_le_one (Θ-t)))
  have hcosloss := mul_le_mul_of_nonneg_left hloss (show (0:ℝ)≤2/5 by norm_num)
  have hid : H.y+A.a-2-(A.y+1/2)*Real.sin t-(9/10)*Real.sin (Θ-t)=
      NegativeNoncancelingBarrier.F H A Θ t+
      (A.a-1/2)*(1-Real.cos t)+((13/12)-(9/10))*Real.sin (Θ-t)-
      (1-V A t)*(1-Real.cos (Θ-t)) := by
    dsimp [NegativeNoncancelingBarrier.F,V]
    ring
  refine ⟨ha,hb,?_⟩
  have hgain : 0≤H.y+A.a-2-(A.y+1/2)*Real.sin t-(9/10)*Real.sin (Θ-t) := by
    rw [hid]
    nlinarith [hetrig.2.2.1]
  linarith

theorem charged_contact {H A : SignedPoint} {Θ t : ℝ}
    (hHy : H.y<9/10) (hAa : 1/2<A.a) (hAy : 67/200≤A.y)
    (hAc : A.Contained qCap) (hΘ : Θ∈Icc 0 (7/10 : ℝ)) (ht : t∈Icc 0 Θ)
    (hf : 0≤NegativeNoncancelingBarrier.F H A Θ t) :
    2+(167/200)*Real.sin Θ≤H.y+A.a := by
  have hsingle := single_contact hHy hAa (by linarith : 0≤A.y) hAc hΘ ht hf
  have ht' : t∈Icc 0 (7/10 : ℝ) := ⟨ht.1,ht.2.trans hΘ.2⟩
  have he : Θ-t∈Icc 0 (7/10 : ℝ) :=
    ⟨by linarith [ht.2],by linarith [ht.1,hΘ.2]⟩
  have hst := (transport_trig ht').2.2.1
  have hse := (transport_trig he).2.2.1
  have hsum := sine_sum ht' he
  rw [show t+(Θ-t)=Θ by ring] at hsum
  have hcoef := mul_le_mul_of_nonneg_right (show 167/200≤A.y+1/2 by linarith) hst
  nlinarith [hsingle.2.2]

structure Bounds (C : SignedCycle) : Prop where
  span_nonneg : 0≤C.theta H-C.theta D
  span_lt : C.theta H-C.theta D<27/100
  A_primary : 11/10<(C.point A).a ∧ (C.point A).a<647/500
  B_primary : 11/10<(C.point B).a ∧ (C.point B).a<647/500
  A_tangent : (C.point A).y∈Ioo (67/200) (133/200)
  B_tangent : -(C.point B).y∈Ioo (67/200) (133/200)
  H_tangent : 353/500<(C.point H).y ∧ (C.point H).y<9/10
  D_tangent : 353/500< -(C.point D).y ∧ -(C.point D).y<9/10
  H_primary : 1/2<(C.point H).a ∧ (C.point H).a<11/10
  D_primary : 1/2<(C.point D).a ∧ (C.point D).a<11/10
  primary_sum : (C.point H).a+(C.point D).a<
    1248/625-(359/500)*Real.sin (C.theta H-C.theta D)

end NonpositiveChainBounds

namespace SignedCycle

private theorem r60_feasible_zero {C : SignedCycle} {i : Vertex} (hw : Candidate.word i=0)
    (j : Fin 4) : C.Feasible i j ↔
      zeroFeasible (C.point i) (C.point (next i)) (C.theta (next i)-C.theta i) j := by
  simp only [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,hw,↓reduceIte,
    zeroFeasible,delta,sub_nonneg]

/-- A literal aligned zero edge supplies either zero owner. -/
theorem HardInput.aligned_HG_zero {q : ℝ} (I : HardInput q)
    (hGH : I.cycle.theta G=I.cycle.theta H) : I.cycle.Feasible H 0 := by
  have hj : I.witnesses.owner H=0 ∨ I.witnesses.owner H=2 := by
    simpa [normalOwners,H] using I.witnesses.allowed H
  rcases hj with hj | hj
  · simpa [hj] using I.witnesses.feasible H
  · have hf := (r60_feasible_zero (C := I.cycle) (i := H) (by decide) _).1
      (I.witnesses.feasible H)
    rw [hj,show next H=G by decide,hGH,sub_self] at hf
    apply (r60_feasible_zero (C := I.cycle) (i := H) (by decide) 0).2
    rw [show next H=G by decide,hGH,sub_self]
    simp only [zeroFeasible,zeroProjection_aligned] at hf ⊢
    simpa using hf

theorem HardInput.aligned_TD_two {q : ℝ} (I : HardInput q)
    (hTD : I.cycle.theta T=I.cycle.theta D) : I.cycle.Feasible T 2 := by
  have hj : I.witnesses.owner T=0 ∨ I.witnesses.owner T=2 := by
    simpa [normalOwners,T] using I.witnesses.allowed T
  rcases hj with hj | hj
  · have hf := (r60_feasible_zero (C := I.cycle) (i := T) (by decide) _).1
      (I.witnesses.feasible T)
    rw [hj,show next T=D by decide,hTD,sub_self] at hf
    apply (r60_feasible_zero (C := I.cycle) (i := T) (by decide) 2).2
    rw [show next T=D by decide,hTD,sub_self]
    simp only [zeroFeasible,zeroProjection_aligned] at hf ⊢
    simpa using hf
  · simpa [hj] using I.witnesses.feasible T

/-- The source negative HG0 core composite, including its aligned limit. -/
theorem HardInput.negative_HG0_composite {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hHG : I.cycle.Feasible H 0) :
    0≤NegativeNoncancelingBarrier.F (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H-I.cycle.theta A) (I.cycle.theta G-I.cycle.theta A) := by
  have hΘ : I.cycle.theta H-I.cycle.theta A∈Icc 0 (7/10 : ℝ) :=
    ⟨by linarith,(le_abs_self _).trans (I.necessary.spread H A)⟩
  have ht : I.cycle.theta G-I.cycle.theta A∈Icc 0 (I.cycle.theta H-I.cycle.theta A) := by
    constructor <;> linarith
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G)
      ((I.cycle.theta G-I.cycle.theta A)-(I.cycle.theta H-I.cycle.theta A)) 0 := by
    rw [show (I.cycle.theta G-I.cycle.theta A)-(I.cycle.theta H-I.cycle.theta A)=
      I.cycle.theta G-I.cycle.theta H by ring]
    simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg] using hHG
  have hGA' : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (-(I.cycle.theta G-I.cycle.theta A)) 0 := by
    simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,neg_sub]
      using I.GA_hard
  exact (NegativeNoncancelingOuter.original_composite hq
    (I.necessary.sorted H) (I.necessary.sorted G) (I.necessary.sorted A)
    (I.necessary.core H) (I.necessary.core G) (I.necessary.core A)
    (I.necessary.contained H) (I.necessary.contained A)
    I.anchors_normal.H_nonneg I.anchors_normal.A_nonneg hΘ ht hHG' hGA').2.2

theorem HardInput.negative_TD2_composite {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hTD : I.cycle.Feasible T 2) :
    0≤NegativeNoncancelingBarrier.F (I.cycle.point D).reflect (I.cycle.point B).reflect
      (I.cycle.theta B-I.cycle.theta D) (I.cycle.theta B-I.cycle.theta T) := by
  have hΘ : I.cycle.theta B-I.cycle.theta D∈Icc 0 (7/10 : ℝ) :=
    ⟨by linarith,(le_abs_self _).trans (I.necessary.spread B D)⟩
  have ht : I.cycle.theta B-I.cycle.theta T∈Icc 0 (I.cycle.theta B-I.cycle.theta D) := by
    constructor <;> linarith
  have hTD' : zeroFeasible (I.cycle.point T) (I.cycle.point D)
      ((I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)) 2 := by
    rw [show (I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)=
      I.cycle.theta D-I.cycle.theta T by ring]
    simpa [Feasible,slack,edge,word,delta,next,T,D,zeroFeasible,sub_nonneg] using hTD
  have hBT' : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-(I.cycle.theta B-I.cycle.theta T)) 2 := by
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg,neg_sub]
      using I.BT_hard
  have hHG : zeroFeasible (I.cycle.point D).reflect (I.cycle.point T).reflect
      ((I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)) 0 := by
    simpa [reflectedOwner] using (zeroFeasible_reflect _ _ _ 2).2 hTD'
  have hGA : quarterFeasible (I.cycle.point T).reflect (I.cycle.point B).reflect
      (-(I.cycle.theta B-I.cycle.theta T)) 0 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect _ _ _ 2).2 hBT'
  exact (NegativeNoncancelingOuter.original_composite hq
    (by simpa using I.necessary.sorted D) (by simpa using I.necessary.sorted T)
    (by simpa using I.necessary.sorted B) (by simpa using I.necessary.core D)
    (by simpa using I.necessary.core T) (by simpa using I.necessary.core B)
    (by simpa using I.necessary.contained D) (by simpa using I.necessary.contained B)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.D_nonpos)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.B_nonpos)
    hΘ ht hHG hGA).2.2

theorem HardInput.nonpositive_composite_bounds {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2) :
    NonpositiveChainBounds.Bounds I.cycle := by
  let Θ := I.cycle.theta H-I.cycle.theta A
  let Υ := I.cycle.theta B-I.cycle.theta D
  let t := I.cycle.theta G-I.cycle.theta A
  let u := I.cycle.theta B-I.cycle.theta T
  let H' := I.cycle.point H
  let A' := I.cycle.point A
  let B' := (I.cycle.point B).reflect
  let D' := (I.cycle.point D).reflect
  have hΘ : Θ∈Icc 0 (7/10 : ℝ) :=
    ⟨by dsimp [Θ]; linarith,(le_abs_self _).trans (I.necessary.spread H A)⟩
  have hΥ : Υ∈Icc 0 (7/10 : ℝ) :=
    ⟨by dsimp [Υ]; linarith,(le_abs_self _).trans (I.necessary.spread B D)⟩
  have ht : t∈Icc 0 Θ := by dsimp [t,Θ]; constructor <;> linarith
  have hu : u∈Icc 0 Υ := by dsimp [u,Υ]; constructor <;> linarith
  have hspanEq : Θ+Υ=I.cycle.theta H-I.cycle.theta D := by dsimp [Θ,Υ]; rw [hAB]; ring
  have hspan : Θ+Υ∈Icc 0 (7/10 : ℝ) := by
    refine ⟨add_nonneg hΘ.1 hΥ.1,?_⟩
    rw [hspanEq]
    exact (le_abs_self _).trans (I.necessary.spread H D)
  have hc (i : Vertex) : (I.cycle.point i).Contained qCap := (I.necessary.contained i).trans hq
  have hHc : H'.Contained qCap := hc H
  have hAc : A'.Contained qCap := hc A
  have hBc : B'.Contained qCap := by simpa [B'] using hc B
  have hDc : D'.Contained qCap := by simpa [D'] using hc D
  have hAs : A'.Sorted := I.necessary.sorted A
  have hBs : B'.Sorted := by simpa [B'] using I.necessary.sorted B
  have hHs : H'.Sorted := I.necessary.sorted H
  have hDs : D'.Sorted := by simpa [D'] using I.necessary.sorted D
  have hHy : 0≤H'.y := I.anchors_normal.H_nonneg
  have hAy : 0≤A'.y := I.anchors_normal.A_nonneg
  have hBy : 0≤B'.y := by dsimp [B',SignedPoint.reflect]; linarith [I.anchors_normal.B_nonpos]
  have hDy : 0≤D'.y := by dsimp [D',SignedPoint.reflect]; linarith [I.anchors_normal.D_nonpos]
  have hHu : H'.y<9/10 := by
    simpa [H',abs_of_nonneg hHy] using
      (SignedPoint.coordinate_bounds (I.necessary.sorted H) (I.necessary.core H) (I.necessary.contained H) hq).2.2
  have hDu : D'.y<9/10 := by
    simpa [D',SignedPoint.reflect,abs_of_nonpos I.anchors_normal.D_nonpos] using
      (SignedPoint.coordinate_bounds (I.necessary.sorted D) (I.necessary.core D) (I.necessary.contained D) hq).2.2
  have hAa : 1/2<A'.a := SignedPoint.primary_gt_half hAs (I.necessary.core A)
  have hBa : 1/2<B'.a := SignedPoint.primary_gt_half hBs (by simpa [B'] using I.necessary.core B)
  have hHF := I.negative_HG0_composite hq hAG hGH hHG
  have hDF := I.negative_TD2_composite hq hDT hTB hTD
  have hHsingle := NonpositiveChainBounds.single_contact hHu hAa hAy hAc hΘ ht hHF
  have hDsingle := NonpositiveChainBounds.single_contact hDu hBa hBy hBc hΥ hu hDF
  have hABsum : 1≤A'.y+B'.y := by
    have hj : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
      simpa [normalOwners,A] using I.witnesses.allowed A
    have hf := (r60_feasible_zero (C := I.cycle) (i := A) (by decide) _).1
      (I.witnesses.feasible A)
    rw [show next A=B by decide,hAB,sub_self] at hf
    simp only [zeroFeasible,zeroProjection_aligned,edgeWidth_zero] at hf
    simp only [A',B',SignedPoint.reflect]
    rcases hj with hj | hj <;> rw [hj] at hf <;> simp at hf <;> linarith
  have hAylo : 67/200<A'.y := by linarith [hDsingle.2.1]
  have hBylo : 67/200<B'.y := by linarith [hHsingle.2.1]
  have hHcharge := NonpositiveChainBounds.charged_contact hHu hAa hAylo.le hAc hΘ ht hHF
  have hDcharge := NonpositiveChainBounds.charged_contact hDu hBa hBylo.le hBc hΥ hu hDF
  have hmiddle := AlignedChainBounds.middle_primary_sum hAs hBs hAy hBy hAc hBc hABsum
  have hsines := AlignedChainBounds.sine_sum hΘ hΥ
  have hcharge : 4953/3125+(167/200)*Real.sin (Θ+Υ)<H'.y+D'.y := by nlinarith
  have hsum := AlignedChainBounds.outer_primary_sum hHs.1 hDs.1 hHy hDy hHc hDc hspan hcharge
  have hshort : Θ+Υ<27/100 := by
    by_contra! hlong
    have hsin : Real.sin (27/100)≤Real.sin (Θ+Υ) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith [hspan.2,Real.pi_gt_three]) hlong
    have hlower := Real.sin_ge_sub_cube (show (0:ℝ)≤27/100 by norm_num)
    norm_num at hlower
    linarith
  have hAu := AlignedChainBounds.primary_upper_of_tangent hAs.1 hAylo hAc
  have hBu := AlignedChainBounds.primary_upper_of_tangent hBs.1 hBylo hBc
  have hHlo : 353/500<H'.y := by
    have hs := (transport_trig hΘ).2.2.1
    linarith
  have hDlo : 353/500<D'.y := by
    have hs := (transport_trig hΥ).2.2.1
    linarith
  refine {
    span_nonneg := by rw [←hspanEq]; exact hspan.1
    span_lt := by rwa [←hspanEq]
    A_primary := ⟨hHsingle.1,hAu⟩
    B_primary := ⟨hDsingle.1,hBu⟩
    A_tangent := ⟨hAylo,hHsingle.2.1⟩
    B_tangent := ⟨hBylo,hDsingle.2.1⟩
    H_tangent := ⟨hHlo,hHu⟩
    D_tangent := ⟨hDlo,hDu⟩
    H_primary := ⟨SignedPoint.primary_gt_half hHs (I.necessary.core H),
      AlignedChainBounds.outer_primary_upper hHs.1 hHlo hHc⟩
    D_primary := ⟨SignedPoint.primary_gt_half (I.necessary.sorted D) (I.necessary.core D),
      (AlignedChainBounds.outer_primary_upper hDs.1 hDlo hDc : D'.a<11/10)⟩
    primary_sum := ?_ }
  rw [hspanEq] at hsum
  simpa [H',D',SignedPoint.reflect] using hsum

end SignedCycle
end SquaresInCircles.Eight.TableFree
