module

public import SquaresInCircles.Eight.TableFree.PositiveSmallScalar
public import SquaresInCircles.Eight.TableFree.HardCancelingOuterCycle

/-!
# Actual positive small-side alignment without lifting an original anchor

Uncompiled source draft.  The same original G circle supplies a convex
scalar on its full feasible interval.  The only other scalar endpoint is
an actual zero-G point on that same q-circle, excluded by the unchanged
mixed endpoint budget.  The original H/A composite therefore has strict
slack, part of which is spent on an actual decrease of A's primary.
All other anchors and the opposite intermediate stay fixed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate HardCancelingOuter
namespace SignedCycle

theorem HardInput.positive_HG0_small_reserve {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hHGorder : I.cycle.theta H<I.cycle.theta G)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y)
    (hHG : I.cycle.Feasible H 0) :
    0<quarterProjection (SignedPoint.flat ((I.cycle.point H).y-1))
      (I.cycle.point A) (I.cycle.theta A-I.cycle.theta H) 0-
        edgeWidth (I.cycle.theta A-I.cycle.theta H) := by
  let P := (I.cycle.point A).a-1/2
  let Y := (I.cycle.point A).y+1/2
  let Θ := I.cycle.theta H-I.cycle.theta A
  let e := I.cycle.theta G-I.cycle.theta H
  let z := I.cycle.theta G-I.cycle.theta A
  have harg : Θ+e=z := by dsimp [Θ,e,z]; ring
  have he0 : 0<e := sub_pos.mpr hHGorder
  have hΘ0 : 0≤Θ := sub_nonneg.mpr hAH
  have hz : z∈Icc 0 frameCap :=
    ⟨by dsimp [z]; linarith,(le_abs_self z).trans (I.necessary.spread G A)⟩
  have hΘ : Θ∈Icc 0 frameCap :=
    ⟨hΘ0,(le_abs_self Θ).trans (I.necessary.spread H A)⟩
  have he : e∈Icc 0 frameCap :=
    ⟨he0.le,(le_abs_self e).trans (I.necessary.spread G H)⟩
  have hAa := SignedPoint.primary_gt_half (I.necessary.sorted A) (I.necessary.core A)
  have hAq : (P+1)^2+Y^2≤q := by
    simpa [SignedPoint.Contained,SignedPoint.circle,P,Y,
      abs_of_nonneg I.anchors_normal.A_nonneg,show
        (I.cycle.point A).a-1/2+1=(I.cycle.point A).a+1/2 by ring]
      using I.necessary.contained A
  have hGA : -(I.cycle.point G).y+1/2≤PositiveSmallScalar.V P Y z := by
    have hf : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-z) 0 := by
      simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,z,neg_sub]
        using I.GA_hard
    rw [quarterFeasible,edgeWidth_negative_formula hz] at hf
    simp [quarterProjection,Real.cos_neg,Real.sin_neg] at hf
    dsimp [PositiveSmallScalar.V,P,Y]
    linarith
  have hV : 1/2≤PositiveSmallScalar.V P Y z := by linarith
  have hVp : PositiveSmallScalar.V P Y z≤P := by
    have hh := PositiveCancelingOuter.V_upper hAa I.anchors_normal.A_nonneg hz
    simpa [PositiveCancelingOuter.V,PositiveSmallScalar.V,P,Y] using hh
  have hPupper : P≤397/500 := by
    have hAq' := hAq.trans hq
    have hY : 167/200≤Y := by dsimp [Y]; linarith [hsmall.1]
    have hY2 := pow_le_pow_left₀ (show (0:ℝ)≤167/200 by norm_num) hY 2
    dsimp [qCap] at hAq'
    dsimp [P] at *
    nlinarith
  have S : PositiveSmallScalar.CapData q P Y := {
    P_mem := ⟨by linarith,hPupper⟩
    Y_mem := by dsimp [Y]; constructor <;> linarith [hsmall.1,hsmall.2]
    circle := hAq
    ceiling := hq }
  let J := (I.cycle.point H).y-1/2+PositiveSmallScalar.V P Y Θ
  have hpair : 1≤J+PositiveSmallScalar.F q P Y Θ e := by
    let R := SignedPoint.outerAt q (PositiveSmallScalar.V P Y z-1/2)
    have hyR : 0≤PositiveSmallScalar.V P Y z-1/2 := by linarith
    have hbound : |PositiveSmallScalar.V P Y z-1/2|≤diagonalCoordinate q := by
      rw [abs_of_nonneg hyR]
      linarith [(uniform_circle_reserves hqL hq).1]
    obtain ⟨hRs,hRo,hRc⟩ := SignedPoint.outerAt_spec hqL hbound
    have hsupport := PositiveCancelingOuter.sorted_support_mono
      (H := (I.cycle.point G).reflect) (J := R)
      (by simpa using I.necessary.sorted G) hRs
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (show 0≤R.y from hyR)
      (show (I.cycle.point G).reflect.circle≤R.circle by
        simpa using (I.necessary.contained G).trans_eq hRo.symm)
      (show (I.cycle.point G).reflect.y≤R.y by
        dsimp [SignedPoint.reflect,R,SignedPoint.outerAt]; linarith) he
    have hRwidth : R.a+1/2=PositiveSmallScalar.W q P Y z := by
      simp [R,SignedPoint.outerAt,PositiveSmallScalar.W,abs_of_nonneg hyR]
    have hRa : R.a=PositiveSmallScalar.W q P Y z-1/2 := by linarith
    have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) e 0 := by
      simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg,e] using hHG
    rw [zeroFeasible,edgeWidth_positive_formula he] at hHG'
    simp [zeroProjection] at hHG'
    have hinv := PositiveSmallScalar.inverse_identity P Y Θ e
    rw [harg] at hinv
    change (I.cycle.point G).a*Real.sin e+(-(I.cycle.point G).y)*Real.cos e≤
      R.a*Real.sin e+(PositiveSmallScalar.V P Y z-1/2)*Real.cos e at hsupport
    rw [hRa] at hsupport
    dsimp [J,PositiveSmallScalar.F,PositiveSmallScalar.T]
    rw [harg]
    nlinarith
  obtain ⟨Z,hzZ,hZu,hZE,hVinterval⟩ := PositiveSmallScalar.contact_endpoint S hz hV
  let M := Z-Θ
  have hM : 0<M := by dsimp [M]; linarith
  have heM : e≤M := by dsimp [M]; linarith
  have hMbound : M<2/5 := by dsimp [M]; linarith
  have hargM : Θ+M=Z := by dsimp [M]; ring
  have hdom (s : ℝ) (hs : s∈Icc 0 M) :
      Θ+s∈Icc 0 frameCap ∧ 1/2≤PositiveSmallScalar.V P Y (Θ+s) := by
    have hx : Θ+s∈Icc 0 Z := ⟨by linarith [hs.1],by dsimp [M] at hs; linarith [hs.2]⟩
    exact ⟨⟨hx.1,by dsimp [frameCap]; linarith [hx.2]⟩,hVinterval _ hx⟩
  have hnoend : ¬1≤J+PositiveSmallScalar.F q P Y Θ M := by
    intro hf
    let Q := SignedPoint.outerAt q 0
    have hQbound : |(0:ℝ)|≤diagonalCoordinate q := by
      have hh := (uniform_circle_reserves hqL hq).1
      norm_num
      linarith
    obtain ⟨hQs,hQo,hQc⟩ := SignedPoint.outerAt_spec hqL hQbound
    have hMi : M∈Icc 0 frameCap := by
      dsimp [frameCap]; exact ⟨hM.le,by linarith⟩
    have hZi : Z∈Icc 0 frameCap := by
      dsimp [frameCap]; exact ⟨by linarith [hz.1],by linarith⟩
    have hWZ : PositiveSmallScalar.W q P Y Z=Real.sqrt (q-1/4) := by
      norm_num [PositiveSmallScalar.W,hZE]
    have hHGQ : zeroFeasible (I.cycle.point H) Q M 0 := by
      have hinv := PositiveSmallScalar.inverse_identity P Y Θ M
      rw [hargM,hZE] at hinv
      dsimp [J,PositiveSmallScalar.F,PositiveSmallScalar.T] at hf
      rw [hargM,hWZ] at hf
      rw [zeroFeasible,edgeWidth_positive_formula hMi]
      simp [Q,SignedPoint.outerAt,zeroProjection]
      nlinarith
    have hGAQ : quarterFeasible Q (I.cycle.point A) (-Z) 0 := by
      rw [quarterFeasible,edgeWidth_negative_formula hZi]
      simp [Q,SignedPoint.outerAt,quarterProjection,Real.cos_neg,Real.sin_neg]
      dsimp [PositiveSmallScalar.V,P,Y] at hZE
      nlinarith
    apply I.small_positive_G_zero_impossible hq hAB hnorm hsmall hTA hAH hTy
      (I.cycle.point A) Q (I.necessary.sorted A) (I.necessary.core A)
      (I.necessary.contained A) rfl hQo.le rfl
      (show I.cycle.theta H<I.cycle.theta A+Z by dsimp [M,Θ] at hM; linarith)
      (show I.cycle.theta A+Z-I.cycle.theta A≤frameCap by linarith [hZi.2])
    · convert hHGQ using 1
      dsimp [M,Θ]
      ring
    · convert hGAQ using 1
      ring
  have heMstrict : e<M := by
    apply lt_of_le_of_ne heM
    intro heq
    exact hnoend (by simpa only [←heq] using hpair)
  have hstrict := strict_endpoint_of_second_derivative
    (f := fun s => -PositiveSmallScalar.F q P Y Θ s)
    (df := fun s => -PositiveSmallScalar.F1 q P Y Θ s)
    (ddf := fun s => -PositiveSmallScalar.F2 q P Y Θ s)
    (by norm_num : (0:ℝ)<3/50) (show e∈Ioo 0 M from ⟨he0,heMstrict⟩)
    (fun s hs => (PositiveSmallScalar.F_hasDerivAt
      (PositiveSmallScalar.point_bounds S (hdom s hs).1 (hdom s hs).2).radicand_pos).neg)
    (fun s hs => (PositiveSmallScalar.F1_hasDerivAt
      (PositiveSmallScalar.point_bounds S (hdom s hs).1 (hdom s hs).2).radicand_pos).neg)
    (fun s hs => by
      have hc := PositiveSmallScalar.curvature_lower S
        (show s∈Icc 0 (2/5 : ℝ) from ⟨hs.1,by linarith [hs.2]⟩)
        (hdom s hs).1 (hdom s hs).2
      linarith)
  have hJ : 1<J := by
    rcases hstrict with hleft | hright
    · have hzero : PositiveSmallScalar.F q P Y Θ 0=0 := by simp [PositiveSmallScalar.F]
      rw [hzero] at hleft
      linarith
    · exact False.elim (hnoend (by linarith))
  have hnegative : I.cycle.theta A-I.cycle.theta H= -Θ := by dsimp [Θ]; ring
  rw [hnegative,edgeWidth_negative_formula hΘ]
  simp [quarterProjection,SignedPoint.flat,Real.cos_neg,Real.sin_neg]
  dsimp [J,PositiveSmallScalar.V,P,Y] at hJ
  linarith

/-- Every strictly positive HG0 error on the small normal side aligns
at the original q and spends a strict loss on A's original circle. -/
theorem HardInput.align_positive_HG0_small {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hHGorder : I.cycle.theta H<I.cycle.theta G)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y)
    (hHG : I.cycle.Feasible H 0) :
    ∃ J : HardInput q,
      J.cycle.theta G=J.cycle.theta H ∧ J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point A).y=(I.cycle.point A).y ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i,i≠G → J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i≠G → i≠A → J.cycle.point i=I.cycle.point i) := by
  let Θ := I.cycle.theta H-I.cycle.theta A
  let r := quarterProjection (SignedPoint.flat ((I.cycle.point H).y-1))
    (I.cycle.point A) (-Θ) 0-edgeWidth (-Θ)
  have hr : 0<r := by
    simpa [r,Θ,neg_sub] using I.positive_HG0_small_reserve hqL hq hAB hnorm
      hsmall hTA hAH hHGorder hGy hTy hHG
  let δ := min (1/2 : ℝ) r
  have hδ : 0<δ := lt_min (by norm_num) hr
  have hδu : δ≤1/2 := min_le_left _ _
  have hδr : δ≤r := min_le_right _ _
  have hΘ : Θ∈Icc 0 (7/10 : ℝ) :=
    ⟨sub_nonneg.mpr hAH,(le_abs_self Θ).trans (I.necessary.spread H A)⟩
  obtain ⟨O⟩ := alignment_of_reserve (t := Θ-δ) hqL hq
    (I.necessary.sorted H) (I.necessary.sorted A)
    (I.necessary.core H) (I.necessary.core A)
    (I.necessary.contained H) (I.necessary.contained A)
    I.anchors_normal.H_nonneg I.anchors_normal.A_nonneg hΘ
    (by constructor <;> linarith) (by change (3/20)*(Θ-(Θ-δ))≤r; linarith)
  refine ⟨I.fromCancelingHG hAB O,rfl,hAB,O.A_tangent,?_,?_,?_,?_⟩
  · intro i hi
    by_cases hiA : i=A
    · subst i; exact O.A_circle
    by_cases hiG : i=G
    · subst i; simp [anchorVertices,H,G,A,B,D,E] at hi
    · exact (congrArg SignedPoint.circle
        (alignGACycle_unchanged I.cycle O.pointG O.pointA i hiG hiA).1).le
  · exact ⟨A,by simp [anchorVertices],O.A_strict (by linarith)⟩
  · intro i hi
    change (alignGACycle I.cycle O.pointG O.pointA).theta i=I.cycle.theta i
    simp [alignGACycle_theta,hi]
  · intro i hiG hiA
    exact (alignGACycle_unchanged I.cycle O.pointG O.pointA i hiG hiA).1

end SignedCycle
end SquaresInCircles.Eight.TableFree
