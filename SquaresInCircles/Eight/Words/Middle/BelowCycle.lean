module

public import SquaresInCircles.Eight.Words.Middle.CrossingCycle

/-!
# Eight squares: direct negative-AB0 contraction below T

For `θB < θA ≤ θT`, rotate the original sorted B corner and add the two exact contact shifts
(`actual_B_contraction`). The point stays sorted, keeps both original weak contacts, and has a
strictly smaller original circle. With the contraction for A at or above T, this covers a
negative AB0 error in every A/T frame order (`HardInput.align_negative_AB0_all_orders`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate MiddlePositiveContraction

namespace MiddleBelowContraction

def comparisonX (X Y γ d : ℝ) : ℝ :=
  X*Real.cos d+Y*Real.sin d+(1-Real.cos d)-Real.sin d+
    Real.tan γ*Real.sin d

/-- The target point is sorted, and the span bound makes its first coordinate smaller than the
strict reference contraction. -/
theorem comparison_geometry {X Y γ d : ℝ}
    (hXY : Y ≤ X) (hY : 1/2 ≤ Y) (hd : 0 < d) (hγ : 0 ≤ γ)
    (hspan : γ+d ≤ 7/10)
    (htransverse : 1/2 < MiddleNegativeContraction.comparisonY X Y d) :
    MiddleNegativeContraction.comparisonY X Y d ≤ comparisonX X Y γ d ∧
      (comparisonX X Y γ d)^2+(MiddleNegativeContraction.comparisonY X Y d)^2 <
        X^2+Y^2 := by
  have hdm : d ∈ Icc 0 (7/10 : ℝ) := ⟨hd.le,by linarith⟩
  have hγm : γ ∈ Icc 0 (7/10 : ℝ) := ⟨hγ,by linarith⟩
  have hum : γ+d ∈ Icc 0 (7/10 : ℝ) := ⟨by linarith,hspan⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hdm
  obtain ⟨hcg,hcg1,hsg0,hsg,hsgc⟩ := transport_trig hγm
  have hsu := (transport_trig hum).2.2.2.1
  have hc0 : 0 < Real.cos d := by linarith
  have hcg0 : 0 < Real.cos γ := by linarith
  let c := Real.cos d
  let s := Real.sin d
  let v := 1-c
  let r := c/(1+s)
  have hunit : s^2+c^2=1 := Real.sin_sq_add_cos_sq d
  have hsp : 0 < 1+s := by dsimp [s]; linarith
  have ht0 : 0 ≤ Real.tan γ := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg hsg0 hcg0.le
  have hsorted : MiddleNegativeContraction.comparisonY X Y d ≤ comparisonX X Y γ d := by
    have hp := mul_nonneg (sub_nonneg.mpr hXY) (show 0 ≤ c+s by dsimp [c,s]; linarith)
    have ht := mul_nonneg hs0 (show 0 ≤ 2*Y+Real.tan γ-1 by linarith)
    dsimp [comparisonX,MiddleNegativeContraction.comparisonY]
    dsimp [c,s] at hp
    linarith
  have hAx : Real.tan γ*c+s-1 < 0 := by
    have hid : (Real.tan γ*c+s-1)*Real.cos γ=Real.sin (γ+d)-Real.cos γ := by
      dsimp [c,s]
      rw [Real.tan_eq_sin_div_cos,Real.sin_add]
      field_simp [hcg0.ne']
    by_contra! hn
    have hp := mul_nonneg hn hcg0.le
    rw [hid] at hp
    linarith
  have hrid : r*(1+s)=c := by dsimp [r]; field_simp [hsp.ne']
  have hrc : r*c=1-s := by
    have hp : (r*c-(1-s))*(1+s)=0 := by
      linear_combination c*hrid+hunit
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hsp.ne')
  have htan : Real.tan γ ≤ r := by
    by_contra! hn
    have hp := mul_pos (sub_pos.mpr hn) hc0
    linarith
  have hshift : v-s+s*r= -v*r := by
    dsimp [r,v]
    field_simp [hsp.ne']
    linear_combination -hunit
  have hcompare : comparisonX X Y γ d ≤ X*c+Y*s-v*r := by
    have hp := mul_le_mul_of_nonneg_right htan hs0
    change X*c+Y*s+v-s+Real.tan γ*s ≤ X*c+Y*s-v*r
    linarith
  have hpositive : 0 ≤ comparisonX X Y γ d := by linarith
  have hX2 := pow_le_pow_left₀ hpositive hcompare 2
  have href := MiddleNegativeContraction.reference_norm_strict hXY hY hd hdm.2
  change (X*c+Y*s-v*r)^2+(-X*s+Y*c+v)^2 < X^2+Y^2 at href
  refine ⟨hsorted,?_⟩
  change (comparisonX X Y γ d)^2+(-X*s+Y*c+v)^2 < X^2+Y^2
  linarith

structure BWeakContraction (A B T : SignedPoint) (δ : ℝ) where
  point : SignedPoint
  sorted : point.Sorted
  avoids : point.AvoidsCore
  normal : point.y < 0
  circle_lt : point.circle < B.circle
  AB_gap : 1 ≤ A.y-point.y
  AB_zero : zeroFeasible A point 0 0
  AB_two : zeroFeasible A point 0 2
  BT : quarterFeasible point T δ 2

/-- The contraction on the original circle keeps the original BT slack exactly in corner form.
Both aligned AB owners are feasible. -/
theorem actual_B_contraction {A B T : SignedPoint} {γ d : ℝ}
    (hsA : A.Sorted) (hcA : A.AvoidsCore) (hqA : A.circle ≤ qCap)
    (hsB : B.Sorted) (hyB : B.y ≤ 0) (hyT : -(1/10 : ℝ) ≤ T.y)
    (hd : 0 < d) (hγ : 0 ≤ γ) (hspan : γ+d ≤ 7/10)
    (hAB : zeroFeasible A B (-d) 0)
    (hBT : quarterFeasible B T (γ+d) 2) : Nonempty (BWeakContraction A B T γ) := by
  let D := T.y+1/2
  let X := B.a+1/2
  let Y := -B.y+1/2
  let X' := comparisonX X Y γ d
  let Y' := MiddleNegativeContraction.comparisonY X Y d
  have hdm : d ∈ Icc 0 (7/10 : ℝ) := ⟨hd.le,by linarith⟩
  have hγm : γ ∈ Icc 0 (7/10 : ℝ) := ⟨hγ,by linarith⟩
  have hum : γ+d ∈ Icc 0 (7/10 : ℝ) := ⟨by linarith,hspan⟩
  have hD : 2/5 ≤ D := by dsimp [D]; linarith
  have hAy : A.y < 9/10 := by
    have hh := (SignedPoint.coordinate_bounds hsA hcA hqA le_rfl).2.2
    linarith [le_abs_self A.y]
  have hXY : Y ≤ X := by
    have hh := hsB.2
    rw [abs_of_nonpos hyB] at hh
    dsimp [X,Y]
    linarith
  have hY : 1/2 ≤ Y := by dsimp [Y]; linarith
  have hAB' : 3/2-A.y ≤ Y' := by
    have hh := hAB
    simp [zeroFeasible,zeroProjection] at hh
    rw [edgeWidth_positive_formula hdm] at hh
    dsimp [Y',MiddleNegativeContraction.comparisonY,X,Y]
    linarith
  have hY' : 3/5 < Y' := by linarith
  obtain ⟨hYX,hdrop⟩ := comparison_geometry hXY hY hd hγ hspan
    (show 1/2 < Y' by linarith)
  change Y' ≤ X' at hYX
  change X'^2+Y'^2 < X^2+Y^2 at hdrop
  have hc0 : 0 < Real.cos γ := by linarith [(transport_trig_coarse hγm).1]
  have hs0 := (transport_trig_coarse hγm).2.1
  have hBTsrc : D ≤ (X-1)*Real.cos (γ+d)+(Y-1)*Real.sin (γ+d) := by
    have hh := hBT
    simp [quarterFeasible,quarterProjection] at hh
    rw [edgeWidth_positive_formula hum] at hh
    dsimp [D,X,Y]
    linarith
  have hBTid : (X'-1)*Real.cos γ+(Y'-1)*Real.sin γ=
      (X-1)*Real.cos (γ+d)+(Y-1)*Real.sin (γ+d) := by
    dsimp [X',Y',comparisonX,MiddleNegativeContraction.comparisonY]
    rw [Real.cos_add,Real.sin_add,Real.tan_eq_sin_div_cos]
    field_simp [hc0.ne']
    ring
  have hBTtarget : D ≤ (X'-1)*Real.cos γ+(Y'-1)*Real.sin γ := by
    rw [hBTid]
    exact hBTsrc
  have hprimary : 6/5 ≤ X' := by
    have hsortprod := mul_nonneg hs0 (sub_nonneg.mpr hYX)
    have hX1 : 1 < X' := by
      by_contra! hn
      have hp := mul_nonpos_of_nonpos_of_nonneg (show X'-1 ≤ 0 by linarith) hc0.le
      have ht := mul_nonpos_of_nonpos_of_nonneg (show Y'-1 ≤ 0 by linarith) hs0
      linarith
    have hp := mul_nonneg (show 0 ≤ X'-1 by linarith)
      (show 0 ≤ 2-Real.cos γ-Real.sin γ by
        linarith [Real.cos_le_one γ,Real.sin_le_one γ])
    linarith
  let B' : SignedPoint := ⟨X'-1/2,-(Y'-1/2)⟩
  have hnormal : B'.y < 0 := by dsimp [B']; linarith
  have hsource : X^2+Y^2=B.circle := by
    simp [X,Y,SignedPoint.circle,abs_of_nonpos hyB]
  have hcircle : B'.circle=X'^2+Y'^2 := by
    dsimp [SignedPoint.circle]
    rw [abs_of_neg hnormal]
    dsimp [B']
    ring
  have hgap : 1 ≤ A.y-B'.y := by dsimp [B']; linarith
  refine ⟨{
    point := B'
    sorted := ⟨by dsimp [B']; linarith,?_⟩
    avoids := ?_
    normal := hnormal
    circle_lt := by rw [hcircle,← hsource]; exact hdrop
    AB_gap := hgap
    AB_zero := by simpa [zeroFeasible,zeroProjection] using hgap
    AB_two := by simpa [zeroFeasible,zeroProjection] using hgap
    BT := ?_
  }⟩
  · rw [abs_of_neg hnormal]
    dsimp [B']
    linarith
  · have ha : (7/10 : ℝ) ≤ B'.a := by dsimp [B']; linarith
    dsimp [SignedPoint.AvoidsCore,SignedPoint.coreDistance]
    rw [max_eq_left (by linarith : 0 ≤ B'.a-1/2)]
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/5)
      (show 1/5 ≤ B'.a-1/2 by linarith) 2
    linarith [sq_nonneg (max (|B'.y|-1/2) 0)]
  · change edgeWidth γ ≤ B'.a*Real.cos γ-B'.y*Real.sin γ-T.y
    rw [edgeWidth_positive_formula hγm]
    dsimp [B',D] at *
    linarith

end MiddleBelowContraction

open MiddleBelowContraction
namespace SignedCycle

def Witnesses.replaceBWeak {C : SignedCycle} (w : C.Witnesses)
    (O : BWeakContraction (C.point A) (C.point B) (C.point T) (C.theta T-C.theta A)) :
    (SignedCycle.replaceB C O.point).Witnesses where
  owner i := if i=B then 2 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · exact (replacePoint_other_feasible (v := B) (by decide : H ≠ B)
        (by decide : next H ≠ B)).2 (w.feasible H)
    · exact (replacePoint_other_feasible (v := B) (by decide : G ≠ B)
        (by decide : next G ≠ B)).2 (w.feasible G)
    · have hj : w.owner A=0 ∨ w.owner A=2 := by
        simpa [normalOwners,A] using w.allowed A
      rcases hj with hj | hj
      · have hAB : A ≠ B := by decide
        exact (replaceB_AB C O.point _).2 (by
          show zeroFeasible (C.point A) O.point 0 (if A = B then 2 else w.owner A)
          simp only [hAB,↓reduceIte,hj]
          exact O.AB_zero)
      · have hAB : A ≠ B := by decide
        exact (replaceB_AB C O.point _).2 (by
          show zeroFeasible (C.point A) O.point 0 (if A = B then 2 else w.owner A)
          simp only [hAB,↓reduceIte,hj]
          exact O.AB_two)
    · exact (replaceB_BT C O.point 2).2 O.BT
    · exact (replacePoint_other_feasible (v := B) (by decide : T ≠ B)
        (by decide : next T ≠ B)).2 (w.feasible T)
    · exact (replacePoint_other_feasible (v := B) (by decide : D ≠ B)
        (by decide : next D ≠ B)).2 (w.feasible D)
    · exact (replacePoint_other_feasible (v := B) (by decide : E ≠ B)
        (by decide : next E ≠ B)).2 (w.feasible E)
  allowed := by
    intro i
    by_cases hi : i=B
    · subst i; norm_num [normalOwners,B]
    · simpa [hi] using w.allowed i

def HardInput.fromBelowMiddle {q : ℝ} (I : HardInput q)
    (O : BWeakContraction (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta T-I.cycle.theta A)) : HardInput q where
  cycle := SignedCycle.replaceB I.cycle O.point
  necessary := {
    sorted := by
      intro i
      by_cases hi : i=B
      · subst i; simpa [replaceB,replacePoint] using O.sorted
      · simpa [replaceB,replacePoint,hi] using I.necessary.sorted i
    contained := by
      intro i
      by_cases hi : i=B
      · subst i
        have hh := O.circle_lt.le.trans (I.necessary.contained B)
        simpa [replaceB,replacePoint,SignedPoint.Contained] using hh
      · simpa [replaceB,replacePoint,hi] using I.necessary.contained i
    core := by
      intro i
      by_cases hi : i=B
      · subst i; simpa [replaceB,replacePoint] using O.avoids
      · simpa [replaceB,replacePoint,hi] using I.necessary.core i
    spread := replaceB_spread I.necessary.spread O.point }
  anchors_normal := by
    constructor
    · simpa [replaceB,replacePoint,H,B] using I.anchors_normal.H_nonneg
    · simpa [replaceB,replacePoint,A,B] using I.anchors_normal.A_nonneg
    · simpa [replaceB,replacePoint] using O.normal.le
    · simpa [replaceB,replacePoint,D,B] using I.anchors_normal.D_nonpos
  E_nonpos := by simpa [replaceB,replacePoint,E,B] using I.E_nonpos
  witnesses := I.witnesses.replaceBWeak O
  GA_hard := (replacePoint_other_feasible (v := B) (by decide : G ≠ B)
    (by decide : next G ≠ B)).2 I.GA_hard
  BT_hard := (replaceB_BT I.cycle O.point 2).2 O.BT
  zero_signs := {
    HG_canceling := by
      intro hh
      have hj : I.witnesses.owner H=2 := by simpa [Witnesses.replaceBWeak,H,B] using hh
      simpa [replaceB,replacePoint,G,B] using I.zero_signs.HG_canceling hj
    TD_canceling := by
      intro hh
      have hj : I.witnesses.owner T=0 := by simpa [Witnesses.replaceBWeak,T,B] using hh
      simpa [replaceB,replacePoint,T,B] using I.zero_signs.TD_canceling hj }
  E_radial := by simpa [replaceB,replacePoint,H,D,E,B] using I.E_radial

theorem HardInput.below_middle_contraction {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hd : I.cycle.theta B < I.cycle.theta A)
    (hAT : I.cycle.theta A ≤ I.cycle.theta T)
    (hAB : I.cycle.Feasible A 0) :
    Nonempty (BWeakContraction (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta T-I.cycle.theta A)) := by
  have hspan : (I.cycle.theta T-I.cycle.theta A)+
      (I.cycle.theta A-I.cycle.theta B) ≤ 7/10 := by
    have hh := I.necessary.spread T B
    have ha := le_abs_self (I.cycle.theta T-I.cycle.theta B)
    dsimp [frameCap] at hh
    linarith
  have hAB' : zeroFeasible (I.cycle.point A) (I.cycle.point B)
      (-(I.cycle.theta A-I.cycle.theta B)) 0 := by
    rw [neg_sub]
    simpa [Feasible,slack,edge,Candidate.word,delta,next,A,B,zeroFeasible,sub_nonneg]
      using hAB
  have hBT' : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      ((I.cycle.theta T-I.cycle.theta A)+(I.cycle.theta A-I.cycle.theta B)) 2 := by
    rw [show (I.cycle.theta T-I.cycle.theta A)+
      (I.cycle.theta A-I.cycle.theta B)=I.cycle.theta T-I.cycle.theta B by ring]
    simpa [Feasible,slack,edge,Candidate.word,delta,next,B,T,quarterFeasible,sub_nonneg]
      using I.BT_hard
  exact MiddleBelowContraction.actual_B_contraction
    (I.necessary.sorted A) (I.necessary.core A) ((I.necessary.contained A).trans hq)
    (I.necessary.sorted B) I.anchors_normal.B_nonpos hyT
    (sub_pos.mpr hd) (sub_nonneg.mpr hAT) hspan hAB' hBT'

theorem HardInput.align_negative_AB0_below_T {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hd : I.cycle.theta B < I.cycle.theta A)
    (hAT : I.cycle.theta A ≤ I.cycle.theta T)
    (hAB : I.cycle.Feasible A 0) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧ J.cycle.theta B=I.cycle.theta A ∧
      1 ≤ (J.cycle.point A).y-(J.cycle.point B).y ∧
      (J.cycle.point B).circle < (I.cycle.point B).circle ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨O⟩ := I.below_middle_contraction hq hyT hd hAT hAB
  refine ⟨I.fromBelowMiddle O,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [HardInput.fromBelowMiddle,replaceB,replacePoint,A,B]
  · simp [HardInput.fromBelowMiddle,replaceB,replacePoint]
  · simpa [HardInput.fromBelowMiddle,replaceB,replacePoint,A,B] using O.AB_gap
  · simpa [HardInput.fromBelowMiddle,replaceB,replacePoint] using O.circle_lt
  · intro i hi
    by_cases hb : i=B
    · subst i
      simpa [HardInput.fromBelowMiddle,replaceB,replacePoint] using O.circle_lt.le
    · exact (congrArg SignedPoint.circle (replaceB_unchanged I.cycle O.point i hb).1).le
  · refine ⟨B,by simp [anchorVertices],?_⟩
    simpa [HardInput.fromBelowMiddle,replaceB,replacePoint] using O.circle_lt
  · exact replaceB_unchanged I.cycle O.point

/-- Every negative original AB0 error contracts B to A, for all G/T/H/D frame orders. The AB
gap is only bounded below by 1. -/
theorem HardInput.align_negative_AB0_all_orders {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hd : I.cycle.theta B < I.cycle.theta A)
    (hAB : I.cycle.Feasible A 0) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧ J.cycle.theta B=I.cycle.theta A ∧
      1 ≤ (J.cycle.point A).y-(J.cycle.point B).y ∧
      (J.cycle.point B).circle < (I.cycle.point B).circle ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  rcases le_total (I.cycle.theta T) (I.cycle.theta A) with hTA | hAT
  · obtain ⟨J,halign,hframe,hgap,hloss,hnon,hstrict,hfixed⟩ :=
      I.align_nonzero_AB0_A_above_T hq hyT hTA (ne_of_gt hd) hAB
    exact ⟨J,halign,hframe,hgap.symm.le,hloss,hnon,hstrict,hfixed⟩
  · exact I.align_negative_AB0_below_T hq hyT hd hAT hAB

end SignedCycle
end SquaresInCircles.Eight
