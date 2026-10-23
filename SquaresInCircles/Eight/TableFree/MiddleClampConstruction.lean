module

public import SquaresInCircles.Eight.TableFree.MiddleNegativeZeroCap

/-!
# Actual-circle construction for an exterior common middle frame

Uncompiled draft.  The negative-quarter zero comparison and the opposite
positive-cap gain make the two endpoint caps sum to more than two.  Each
cap uses its own original anchor radius.  Two explicit transverse corners
strictly below those caps sum to two; their exact hard-contact primaries
give strict circle loss at both original middle anchors.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.MiddleClampConstruction
open HardSplitCap MiddlePositiveContraction

theorem cap_upper {q D θ : ℝ} (h : MiddleHardCap.Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hY : 1/2 ≤ cap q D θ) : cap q D θ < 7/5 := by
  have hX := MiddleHardCap.primary_lower h.transverse hθ
    (show 0 ≤ cap q D θ by linarith) (HardSplitCap.corner_contact q D θ).ge
  have hprimary : 7/5 ≤ cornerX q D θ := by linarith [h.transverse]
  have hXs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 7/5) hprimary 2
  have hnorm := MiddleHardCap.corner_norm h hθ
  have hq := h.ceiling
  dsimp [qCap] at hq
  by_contra! hn
  have hYs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 7/5) hn 2
  nlinarith

def contactPoint (D Y θ : ℝ) : SignedPoint :=
  ⟨primaryCorner D Y θ-1/2,Y-1/2⟩

theorem contactPoint_properties {q D θ Y : ℝ} (h : MiddleHardCap.Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hY : 1/2 < Y) (hcap : Y < cap q D θ) :
    (contactPoint D Y θ).Sorted ∧ (contactPoint D Y θ).AvoidsCore ∧
      0 < (contactPoint D Y θ).y ∧ (contactPoint D Y θ).circle < q ∧
      (contactPoint D Y θ).a*Real.cos θ-(contactPoint D Y θ).y*Real.sin θ=
        edgeWidth θ+D-1/2 := by
  obtain ⟨hprimary,hnorm,hsorted⟩ := MiddleHardCap.strict_contact_norm h hθ hY.le hcap
  have hnormal : 0 < (contactPoint D Y θ).y := by dsimp [contactPoint]; linarith
  have hcircle : (contactPoint D Y θ).circle=(primaryCorner D Y θ)^2+Y^2 := by
    dsimp [SignedPoint.circle]
    rw [abs_of_pos hnormal]
    dsimp [contactPoint]
    ring
  refine ⟨⟨by dsimp [contactPoint]; linarith,?_⟩,?_,hnormal,?_,?_⟩
  · rw [abs_of_pos hnormal]
    dsimp [contactPoint]
    linarith
  · have ha : (9/10 : ℝ) ≤ (contactPoint D Y θ).a := by dsimp [contactPoint]; linarith
    dsimp [SignedPoint.AvoidsCore,SignedPoint.coreDistance]
    rw [max_eq_left (by linarith : 0 ≤ (contactPoint D Y θ).a-1/2)]
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2/5)
      (show 2/5 ≤ (contactPoint D Y θ).a-1/2 by linarith) 2
    nlinarith [sq_nonneg (max (|(contactPoint D Y θ).y|-1/2) 0)]
  · rw [hcircle]
    exact hnorm
  · have hc0 : Real.cos θ ≠ 0 := ne_of_gt (by
      linarith [(transport_trig_coarse hθ).1] : 0 < Real.cos θ)
    have hh := primaryCorner_contact (D := D) (Y := Y) hc0
    rw [edgeWidth_positive_formula hθ]
    dsimp [contactPoint]
    nlinarith

structure PairClamp (G A B T : SignedPoint) (t u : ℝ) where
  pointA : SignedPoint
  pointB : SignedPoint
  sorted_A : pointA.Sorted
  sorted_B : pointB.Sorted
  avoids_A : pointA.AvoidsCore
  avoids_B : pointB.AvoidsCore
  normal_A : 0 < pointA.y
  normal_B : pointB.y < 0
  circle_A : pointA.circle < A.circle
  circle_B : pointB.circle < B.circle
  AB_exact : pointA.y-pointB.y=1
  AB_zero : zeroFeasible pointA pointB 0 0
  AB_two : zeroFeasible pointA pointB 0 2
  GA_exact : quarterProjection G pointA (-t) 0=edgeWidth (-t)
  BT_exact : quarterProjection pointB T (-u) 2=edgeWidth (-u)

theorem actual_above_pair {G A B T : SignedPoint} {r η : ℝ}
    (hsA : A.Sorted) (hqA : A.circle ≤ qCap) (hqB : B.circle ≤ qCap)
    (hyA : 0 ≤ A.y) (hyB : B.y ≤ 0)
    (hyG : G.y ≤ (1/10 : ℝ)) (hyT : -(1/10 : ℝ) ≤ T.y)
    (hr : 0 < r) (hη : 0 ≤ η) (hspan : r+η ≤ 7/10)
    (hgap : 1 ≤ A.y-B.y)
    (hGA : quarterFeasible G A r 0)
    (hBT : quarterFeasible B T (-(r+η)) 2) : Nonempty (PairClamp G A B T 0 η) := by
  let DA := 1/2-G.y
  let DB := 1/2+T.y
  let XA := A.a+1/2
  let YA := A.y+1/2
  let XB := B.a+1/2
  let YB := -B.y+1/2
  let LA := cap A.circle DA 0
  let LB := cap B.circle DB η
  have hrm : r ∈ Icc 0 (7/10 : ℝ) := ⟨hr.le,by linarith⟩
  have hηm : η ∈ Icc 0 (7/10 : ℝ) := ⟨hη,by linarith⟩
  have hum : r+η ∈ Icc 0 (7/10 : ℝ) := ⟨by linarith,hspan⟩
  have hzero : (0:ℝ) ∈ Icc 0 (7/10 : ℝ) := by norm_num
  have hDA : 2/5 ≤ DA := by dsimp [DA]; linarith
  have hDB : 2/5 ≤ DB := by dsimp [DB]; linarith
  have hYA : 1/2 ≤ YA := by dsimp [YA]; linarith
  have hYB : 1/2 ≤ YB := by dsimp [YB]; linarith
  have hXYA : YA ≤ XA := by
    have hh := hsA.2
    rw [abs_of_nonneg hyA] at hh
    dsimp [XA,YA]
    linarith
  have hcircleA : XA^2+YA^2=A.circle := by
    simp [XA,YA,SignedPoint.circle,abs_of_nonneg hyA]
  have hcircleB : XB^2+YB^2=B.circle := by
    simp [XB,YB,SignedPoint.circle,abs_of_nonpos hyB]
  have hcontactA : DA ≤ (XA-1)*Real.cos r+(YA-1)*Real.sin r := by
    have hh := hGA
    simp [quarterFeasible,quarterProjection] at hh
    rw [edgeWidth_positive_formula hrm] at hh
    dsimp [DA,XA,YA]
    nlinarith
  have hcontactB : DB ≤ (XB-1)*Real.cos (r+η)-YB*Real.sin (r+η) := by
    have hh := hBT
    simp [quarterFeasible,quarterProjection] at hh
    rw [edgeWidth_positive_formula hum] at hh
    dsimp [DB,XB,YB]
    nlinarith
  obtain ⟨hfA,hgainA⟩ := MiddleNegativeZeroCap.negative_zero_loss
    hqA hDA hXYA hYA hrm hr hcontactA hcircleA.le
  have hfB := MiddleHardCap.feasible_of_contact hqB hDB hum hYB hcontactB hcircleB.le
  have hcapB := MiddleHardCap.cap_majorizes hfB hum
    (show 0 ≤ YB by linarith) hcontactB hcircleB.le
  have hgainB := MiddleHardCap.cap_gain hfB hum hη
    (show η < r+η by linarith) (hYB.trans hcapB)
  have hsum : 2 < LA+LB := by
    dsimp [LA,LB] at *
    dsimp [YA,YB] at hgainA hcapB hYA hYB
    linarith
  have hLBfloor : 1/2 ≤ LB := by dsimp [LB]; linarith
  have hLBupper : LB < 7/5 := cap_upper hfB hηm hLBfloor
  have hLAfloor : 1/2 ≤ LA := by linarith
  have hLAupper : LA < 7/5 := cap_upper hfA hzero hLAfloor
  let YA' := (2+LA-LB)/2
  let YB' := (2+LB-LA)/2
  have hYA' : 1/2 < YA' := by dsimp [YA']; linarith
  have hYB' : 1/2 < YB' := by dsimp [YB']; linarith
  have hYAcap : YA' < LA := by dsimp [YA']; linarith
  have hYBcap : YB' < LB := by dsimp [YB']; linarith
  obtain ⟨hsP,hcP,hnP,hqP,hhP⟩ := contactPoint_properties hfA hzero hYA' hYAcap
  obtain ⟨hsR,hcR,hnR,hqR,hhR⟩ := contactPoint_properties hfB hηm hYB' hYBcap
  let P := contactPoint DA YA' 0
  let R := (contactPoint DB YB' η).reflect
  have hABexact : P.y-R.y=1 := by
    dsimp [P,R,contactPoint,SignedPoint.reflect,YA',YB']
    ring
  refine ⟨{
    pointA := P
    pointB := R
    sorted_A := hsP
    sorted_B := by simpa [R] using hsR
    avoids_A := hcP
    avoids_B := by simpa [R] using hcR
    normal_A := hnP
    normal_B := by simpa [R,SignedPoint.reflect] using neg_neg_of_pos hnR
    circle_A := hqP
    circle_B := by simpa [R] using hqR
    AB_exact := hABexact
    AB_zero := by simpa [zeroFeasible,zeroProjection,hABexact]
    AB_two := by simpa [zeroFeasible,zeroProjection,hABexact]
    GA_exact := ?_
    BT_exact := ?_
  }⟩
  · change G.y+P.a*Real.cos (-(0:ℝ))+P.y*Real.sin (-(0:ℝ))=edgeWidth (-(0:ℝ))
    change P.a*Real.cos 0-P.y*Real.sin 0=edgeWidth 0+DA-1/2 at hhP
    simp only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero,edgeWidth_zero] at hhP
    simp only [neg_zero,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero,edgeWidth_zero]
    dsimp [DA] at hhP
    linarith
  · change R.a*Real.cos (-η)-R.y*Real.sin (-η)-T.y=edgeWidth (-η)
    rw [Real.cos_neg,Real.sin_neg,edgeWidth_neg]
    dsimp [R,SignedPoint.reflect,DB] at *
    nlinarith

def PairClamp.reflected {G A B T : SignedPoint} {t u : ℝ}
    (O : PairClamp T.reflect B.reflect A.reflect G.reflect t u) : PairClamp G A B T u t where
  pointA := O.pointB.reflect
  pointB := O.pointA.reflect
  sorted_A := by simpa using O.sorted_B
  sorted_B := by simpa using O.sorted_A
  avoids_A := by simpa using O.avoids_B
  avoids_B := by simpa using O.avoids_A
  normal_A := by simpa [SignedPoint.reflect] using neg_pos.mpr O.normal_B
  normal_B := by simpa [SignedPoint.reflect] using neg_neg_of_pos O.normal_A
  circle_A := by simpa using O.circle_B
  circle_B := by simpa using O.circle_A
  AB_exact := by
    have hh := O.AB_exact
    dsimp [SignedPoint.reflect]
    linarith
  AB_zero := (zeroFeasible_reflect O.pointB.reflect O.pointA.reflect 0 0).1
    (by simpa [reflectedOwner] using O.AB_two)
  AB_two := (zeroFeasible_reflect O.pointB.reflect O.pointA.reflect 0 2).1
    (by simpa [reflectedOwner] using O.AB_zero)
  GA_exact := by
    have hp := quarterProjection_reflect G O.pointB.reflect (-u) 0
    have he : quarterProjection O.pointB G.reflect (-u) 2=
        quarterProjection G O.pointB.reflect (-u) 0 := by simpa [reflectedOwner] using hp
    exact he.symm.trans O.BT_exact
  BT_exact := by
    have hp := quarterProjection_reflect O.pointA.reflect T (-t) 2
    have he : quarterProjection T.reflect O.pointA (-t) 0=
        quarterProjection O.pointA.reflect T (-t) 2 := by simpa [reflectedOwner] using hp
    exact he.symm.trans O.GA_exact

theorem actual_below_pair {G A B T : SignedPoint} {r η : ℝ}
    (hsB : B.Sorted) (hqA : A.circle ≤ qCap) (hqB : B.circle ≤ qCap)
    (hyA : 0 ≤ A.y) (hyB : B.y ≤ 0)
    (hyG : G.y ≤ (1/10 : ℝ)) (hyT : -(1/10 : ℝ) ≤ T.y)
    (hr : 0 < r) (hη : 0 ≤ η) (hspan : r+η ≤ 7/10)
    (hgap : 1 ≤ A.y-B.y)
    (hGA : quarterFeasible G A (-(r+η)) 0)
    (hBT : quarterFeasible B T r 2) : Nonempty (PairClamp G A B T η 0) := by
  have hGAref : quarterFeasible T.reflect B.reflect r 0 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect B T r 2).2 hBT
  have hBTref : quarterFeasible A.reflect G.reflect (-(r+η)) 2 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect G A (-(r+η)) 0).2 hGA
  obtain ⟨O⟩ := actual_above_pair (by simpa using hsB)
    (by simpa using hqB) (by simpa using hqA)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hyB)
    (by simpa [SignedPoint.reflect] using neg_nonpos.mpr hyA)
    (show T.reflect.y ≤ (1/10 : ℝ) by dsimp [SignedPoint.reflect]; linarith)
    (show -(1/10 : ℝ) ≤ G.reflect.y by dsimp [SignedPoint.reflect]; linarith)
    hr hη hspan
    (show 1 ≤ B.reflect.y-A.reflect.y by dsimp [SignedPoint.reflect]; linarith)
    hGAref hBTref
  exact ⟨O.reflected⟩

end SquaresInCircles.Eight.TableFree.MiddleClampConstruction
