module

public import SquaresInCircles.Eight.TableFree.MiddleClampConstruction
public import SquaresInCircles.Eight.TableFree.CircleGeometry

/-!
# Realizing strict crossed cap-sum slack at the actual radius

Uncompiled source draft.  The two middle points are constructed on their
literal hard-contact lines with transverse corners strictly below the
two actual-q caps.  Their tangents sum to one and both circles are
strictly below q.  The supplied inverse-HG point is kept literally;
the final-endpoint wrapper constructs that point on its q-circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree

structure CrossedClampData (q : ℝ) (H T : SignedPoint) (r u : ℝ) where
  pointG : SignedPoint
  pointA : SignedPoint
  pointB : SignedPoint
  G_sorted : pointG.Sorted
  G_avoids : pointG.AvoidsCore
  G_contained : pointG.Contained q
  G_nonpos : pointG.y≤0
  A_sorted : pointA.Sorted
  A_avoids : pointA.AvoidsCore
  A_strict : pointA.circle<q
  A_nonneg : 0≤pointA.y
  B_sorted : pointB.Sorted
  B_avoids : pointB.AvoidsCore
  B_strict : pointB.circle<q
  B_nonpos : pointB.y≤0
  tangent_sum : pointA.y-pointB.y=1
  HG_zero : zeroFeasible H pointG r 0
  GA_hard : quarterFeasible pointG pointA 0 0
  AB_zero : zeroFeasible pointA pointB 0 0
  AB_two : zeroFeasible pointA pointB 0 2
  BT_hard : quarterFeasible pointB T (-u) 2

namespace CrossedClampConstruction
open HardSplitCap MiddleClampConstruction

theorem actual_data_of_caps {q r u : ℝ} {H G T : SignedPoint}
    (hGs : G.Sorted) (hGc : G.AvoidsCore) (hGq : G.Contained q) (hGy : G.y≤0)
    (hHG : zeroFeasible H G r 0)
    (hA : MiddleHardCap.Feasible q (1/2-G.y))
    (hB : MiddleHardCap.Feasible q (1/2+T.y))
    (hu : u∈Icc 0 frameCap)
    (hLA : 1/2≤cap q (1/2-G.y) 0)
    (hLB : 1/2≤cap q (1/2+T.y) u)
    (hsum : 2<cap q (1/2-G.y) 0+cap q (1/2+T.y) u) :
    ∃ O : CrossedClampData q H T r u, O.pointG=G := by
  let LA := cap q (1/2-G.y) 0
  let LB := cap q (1/2+T.y) u
  have hzero : (0 : ℝ)∈Icc 0 (7/10) := by norm_num
  have hLAupper : LA<7/5 := cap_upper hA hzero hLA
  have hLBupper : LB<7/5 := cap_upper hB hu hLB
  let YA := (2+LA-LB)/2
  let YB := (2+LB-LA)/2
  have hYA : 1/2<YA := by dsimp [YA,LA,LB] at *; linarith
  have hYB : 1/2<YB := by dsimp [YB,LA,LB] at *; linarith
  have hYAcap : YA<cap q (1/2-G.y) 0 := by dsimp [YA,LA,LB]; linarith
  have hYBcap : YB<cap q (1/2+T.y) u := by dsimp [YB,LA,LB]; linarith
  obtain ⟨hAs,hAc,hAy,hAq,hGA⟩ := contactPoint_properties hA hzero hYA hYAcap
  obtain ⟨hBs,hBc,hBy,hBq,hBT⟩ := contactPoint_properties hB hu hYB hYBcap
  let P := contactPoint (1/2-G.y) YA 0
  let Q := (contactPoint (1/2+T.y) YB u).reflect
  have hAB : P.y-Q.y=1 := by
    dsimp [P,Q,contactPoint,SignedPoint.reflect,YA,YB]
    ring
  refine ⟨{
    pointG := G
    pointA := P
    pointB := Q
    G_sorted := hGs
    G_avoids := hGc
    G_contained := hGq
    G_nonpos := hGy
    A_sorted := hAs
    A_avoids := hAc
    A_strict := hAq
    A_nonneg := hAy.le
    B_sorted := by simpa [Q] using hBs
    B_avoids := by simpa [Q] using hBc
    B_strict := by simpa [Q] using hBq
    B_nonpos := by simpa [Q,SignedPoint.reflect] using neg_nonpos.mpr hBy.le
    tangent_sum := hAB
    HG_zero := hHG
    GA_hard := ?_
    AB_zero := by simpa [zeroFeasible,zeroProjection,hAB]
    AB_two := by simpa [zeroFeasible,zeroProjection,hAB]
    BT_hard := ?_ },rfl⟩
  · change P.a*Real.cos 0-P.y*Real.sin 0=edgeWidth 0+(1/2-G.y)-1/2 at hGA
    simp only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero,edgeWidth_zero] at hGA
    simpa [quarterFeasible,quarterProjection] using (show (1:ℝ)≤G.y+P.a by linarith)
  · change Q.a*Real.cos (-u)-Q.y*Real.sin (-u)-T.y≥edgeWidth (-u)
    rw [Real.cos_neg,Real.sin_neg,edgeWidth_neg]
    change (contactPoint (1/2+T.y) YB u).a*Real.cos u-
      (contactPoint (1/2+T.y) YB u).y*Real.sin u-T.y≥edgeWidth u
    linarith

/-- At the final common frame H, its actual tangent determines G without
any source-equality assertion.  Strict cap slack creates separate middle
losses even if either original middle point already lay inside q. -/
theorem endpoint_data {q u : ℝ} {H T : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap) (hHy : H.y∈Ioo (3/4 : ℝ) (9/10))
    (hB : MiddleHardCap.Feasible q (1/2+T.y)) (hu : u∈Icc 0 frameCap)
    (hLB : 1/2≤cap q (1/2+T.y) u)
    (hsum : 2<Real.sqrt (q-(5/2-H.y)^2)+cap q (1/2+T.y) u) :
    Nonempty (CrossedClampData q H T 0 u) := by
  let G := SignedPoint.outerAt q (H.y-1)
  have hGy : G.y=H.y-1 := rfl
  have hD : 1/2-G.y=3/2-H.y := by rw [hGy]; ring
  have hdiag : |H.y-1|≤diagonalCoordinate q := by
    rw [abs_of_nonpos (by linarith [hHy.2] : H.y-1≤0)]
    linarith [hHy.1,(uniform_circle_reserves hqL hq).1]
  obtain ⟨hGs,hGq,hGc⟩ := SignedPoint.outerAt_spec hqL hdiag
  have hA : MiddleHardCap.Feasible q (1/2-G.y) := by
    refine ⟨hq,by rw [hD]; linarith [hHy.2],?_⟩
    rw [hD]
    have hqL' := hqL
    dsimp [qLow] at hqL'
    have hbase : 0≤3/2-H.y+1 := by linarith [hHy.2]
    have hupper : 3/2-H.y+1≤7/4 := by linarith [hHy.1]
    have hs := pow_le_pow_left₀ hbase hupper 2
    nlinarith
  have hcap : cap q (1/2-G.y) 0=Real.sqrt (q-(5/2-H.y)^2) := by
    simp [cap,root,contact,hD,show 3/2-H.y+1=5/2-H.y by ring]
  have hLA : 1/2≤cap q (1/2-G.y) 0 := by
    have hr : 0≤q-((1/2-G.y)+1)^2 := by linarith [hA.corner]
    have hs := Real.sq_sqrt hr
    have hs0 := Real.sqrt_nonneg (q-((1/2-G.y)+1)^2)
    simp only [cap,Real.cos_zero,Real.sin_zero,one_mul,zero_mul,sub_zero,root,contact] at *
    nlinarith [hA.corner]
  have hHG : zeroFeasible H G 0 0 := by
    simpa [zeroFeasible,zeroProjection,hGy] using (show (1:ℝ)≤H.y-(H.y-1) by linarith)
  obtain ⟨O,_⟩ := actual_data_of_caps hGs hGc hGq.le
    (by rw [hGy]; linarith [hHy.2]) hHG hA hB hu hLA hLB (by rwa [hcap])
  exact ⟨O⟩

end CrossedClampConstruction
end SquaresInCircles.Eight.TableFree
