module

public import SquaresInCircles.Eight.TableFree.HardSplitConstruction

/-!
# Strict loss at both middle anchors for an interior hard split

Uncompiled draft.  The strict endpoint AB slack is used by an explicit
small motion along each retained hard contact.  In positive own-frame
coordinates the motion is `(-ε sin θ, -ε cos θ)`.  Both hard projections
remain exact, the AB slack stays positive, and both actual corner radii
decrease strictly.  No continuity choice or common fixed ceiling is needed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.HardSplitCap

def inward (p : SignedPoint) (θ ε : ℝ) : SignedPoint :=
  ⟨p.a-ε*Real.sin θ,p.y-ε*Real.cos θ⟩

theorem inward_hard (p : SignedPoint) (θ ε : ℝ) :
    (inward p θ ε).a*Real.cos θ-(inward p θ ε).y*Real.sin θ=
      p.a*Real.cos θ-p.y*Real.sin θ := by
  dsimp [inward]
  ring

/-- The numerical margins belong to the explicitly constructed cap
endpoints.  They are not assumed of the original middle centers. -/
theorem inward_properties {p : SignedPoint} {θ ε : ℝ}
    (hθ : θ ∈ Icc 0 (7/10 : ℝ))
    (ha : 11/10 ≤ p.a) (hy : 67/200 < p.y ∧ p.y < 133/200)
    (hε : 0 < ε) (hεu : ε ≤ 1/10) :
    (inward p θ ε).Sorted ∧ (inward p θ ε).AvoidsCore ∧
      0 < (inward p θ ε).y ∧ (inward p θ ε).circle < p.circle := by
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hc0 : 0 ≤ Real.cos θ := by linarith
  have hes : 0 ≤ ε*Real.sin θ := mul_nonneg hε.le hs
  have hec : 0 ≤ ε*Real.cos θ := mul_nonneg hε.le hc0
  have hesu : ε*Real.sin θ ≤ 1/10 := by
    have hh := mul_le_mul_of_nonneg_left (Real.sin_le_one θ) hε.le
    nlinarith
  have hecu : ε*Real.cos θ ≤ 1/10 := by
    have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hε.le
    nlinarith
  have ha' : 1 ≤ (inward p θ ε).a := by dsimp [inward]; linarith
  have hy' : 0 < (inward p θ ε).y := by dsimp [inward]; linarith [hy.1]
  have hyu : (inward p θ ε).y < 133/200 := by dsimp [inward]; linarith [hy.2]
  have hyp : 0 < p.y := by linarith [hy.1]
  refine ⟨?_,?_,hy',?_⟩
  · exact ⟨by linarith,by rw [abs_of_pos hy']; linarith⟩
  · dsimp [SignedPoint.AvoidsCore,SignedPoint.coreDistance]
    rw [max_eq_left (by linarith : 0 ≤ (inward p θ ε).a-1/2)]
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2)
      (show 1/2 ≤ (inward p θ ε).a-1/2 by linarith) 2
    nlinarith [sq_nonneg (max (|(inward p θ ε).y|-1/2) 0)]
  · let R := (p.a+1/2)*Real.sin θ+(p.y+1/2)*Real.cos θ
    have hfirst : 0 ≤ (p.a+1/2)*Real.sin θ :=
      mul_nonneg (by linarith) hs
    have hsecond : (167/200 : ℝ)*(3/4) ≤ (p.y+1/2)*Real.cos θ := by
      exact mul_le_mul (by linarith [hy.1]) (by linarith)
        (by norm_num) (by linarith [hy.1])
    have hR : 1/2 < R := by dsimp [R]; linarith
    have hid : (inward p θ ε).circle=p.circle-2*ε*R+ε^2 := by
      dsimp [SignedPoint.circle]
      rw [abs_of_pos hy',abs_of_pos hyp]
      dsimp [inward,R]
      linear_combination ε^2*(Real.sin_sq_add_cos_sq θ)
    have hdrop : 0 < ε*(2*R-ε) := mul_pos hε (by linarith)
    rw [hid]
    nlinarith

/-- The base endpoint records the unchanged total frame span and its
choice of common endpoint frame.  The new points have strictly smaller
corner radii than the two original anchors. -/
structure InteriorImprovement (G A B T : SignedPoint) (t u : ℝ) where
  base : PairEndpoint G A B T t u
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
  GA_exact : quarterProjection G pointA (-base.angleA) 0=edgeWidth (-base.angleA)
  BT_exact : quarterProjection pointB T (-base.angleB) 2=edgeWidth (-base.angleB)
  AB_strict : 1 < pointA.y-pointB.y
  AB_zero : zeroFeasible pointA pointB 0 0
  AB_two : zeroFeasible pointA pointB 0 2

theorem improve_interior {G A B T : SignedPoint} {t u : ℝ}
    (O : PairEndpoint G A B T t u) (ht : 0 < t) (hu : 0 < u) :
    Nonempty (InteriorImprovement G A B T t u) := by
  have hslack := O.strict_if_interior ht hu
  let ε : ℝ := min (1/10) ((O.pointA.y-O.pointB.y-1)/4)
  have hε : 0 < ε := lt_min (by norm_num) (by linarith)
  have hεu : ε ≤ 1/10 := min_le_left _ _
  have hεs : ε ≤ (O.pointA.y-O.pointB.y-1)/4 := min_le_right _ _
  have hBprimary : 11/10 ≤ O.pointB.reflect.a := O.primary_B
  have hBtransverse : 67/200 < O.pointB.reflect.y ∧
      O.pointB.reflect.y < 133/200 := O.transverse_B
  obtain ⟨hAs,hAc,hAn,hAq⟩ := inward_properties O.angleA_mem O.primary_A
    O.transverse_A hε hεu
  obtain ⟨hBs,hBc,hBn,hBq⟩ := inward_properties O.angleB_mem hBprimary
    hBtransverse hε hεu
  let A' := inward O.pointA O.angleA ε
  let B' := (inward O.pointB.reflect O.angleB ε).reflect
  have hdrop : ε*(Real.cos O.angleA+Real.cos O.angleB) ≤ 2*ε := by
    have hh := mul_le_mul_of_nonneg_left
      (add_le_add (Real.cos_le_one O.angleA) (Real.cos_le_one O.angleB)) hε.le
    nlinarith
  have hAB : 1 < A'.y-B'.y := by
    dsimp [A',B',inward,SignedPoint.reflect]
    nlinarith
  refine ⟨{
    base := O
    pointA := A'
    pointB := B'
    sorted_A := hAs
    sorted_B := by simpa [B'] using hBs
    avoids_A := hAc
    avoids_B := by simpa [B'] using hBc
    normal_A := hAn
    normal_B := by dsimp [B',SignedPoint.reflect]; linarith
    circle_A := hAq.trans_eq O.circle_A
    circle_B := ?_
    GA_exact := ?_
    BT_exact := ?_
    AB_strict := hAB
    AB_zero := by simpa [zeroFeasible,zeroProjection] using hAB.le
    AB_two := by simpa [zeroFeasible,zeroProjection] using hAB.le
  }⟩
  · have hh : B'.circle < O.pointB.circle := by simpa [B'] using hBq
    exact hh.trans_eq O.circle_B
  · calc
      quarterProjection G A' (-O.angleA) 0 =
          quarterProjection G O.pointA (-O.angleA) 0 := by
        simp [quarterProjection,A',inward]
        ring
      _ = edgeWidth (-O.angleA) := O.GA_exact
  · calc
      quarterProjection B' T (-O.angleB) 2 =
          quarterProjection O.pointB T (-O.angleB) 2 := by
        simp [quarterProjection,B',inward,SignedPoint.reflect]
        ring
      _ = edgeWidth (-O.angleB) := O.BT_exact

/-- Actual original witnesses produce strict loss at both middle anchors
whenever both original tilts are positive. -/
theorem actual_interior_pair_improvement {G A B T : SignedPoint} {t u : ℝ}
    (hA : A.circle ≤ qCap) (hB : B.circle ≤ qCap)
    (hyA : 0 ≤ A.y) (hyB : B.y ≤ 0)
    (hyG : G.y ≤ -(1/10 : ℝ)) (hyT : (1/10 : ℝ) ≤ T.y)
    (ht : 0 < t) (hu : 0 < u) (hspan : t+u ≤ 7/10)
    (hGA : quarterFeasible G A (-t) 0)
    (hBT : quarterFeasible B T (-u) 2)
    (hAB : zeroFeasible A B 0 0) : Nonempty (InteriorImprovement G A B T t u) := by
  obtain ⟨O⟩ := actual_pair_endpoint hA hB hyA hyB hyG hyT ht.le hu.le hspan hGA hBT hAB
  exact improve_interior O ht hu

end SquaresInCircles.Eight.TableFree.HardSplitCap
