module

public import SquaresInCircles.Eight.TableFree.CrossedLargeGeometry
public import SquaresInCircles.Eight.TableFree.CrossedGAOutput

/-!
# Realizing the crossed large-side alignment at the actual q

Uncompiled source draft.  A positive G-frame motion spends half of the
proved reserve by lowering the lifted A primary.  The adjacent G is then
placed on the same actual q-circle.  This gives an actual HG0/GA0 pair
and a strict A circle loss below q.  At zero motion the original A/G are
retained, so every already strict A inequality is preserved as well.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate PositiveSmallScalar

namespace CrossedLargeConstruction

structure Pair (q Y r : ℝ) (H : SignedPoint) where
  pointG : SignedPoint
  pointA : SignedPoint
  G_sorted : pointG.Sorted
  G_avoids : pointG.AvoidsCore
  G_circle : pointG.circle=q
  G_nonpos : pointG.y≤0
  A_sorted : pointA.Sorted
  A_avoids : pointA.AvoidsCore
  A_circle : pointA.circle<q
  A_tangent : pointA.y=Y-1/2
  HG : zeroFeasible H pointG r 0
  GA : quarterFeasible pointG pointA 0 0

theorem strict_pair_of_bounds {q P Y r z : ℝ} {H : SignedPoint}
    (hPmem : P∈Icc (1/2 : ℝ) (3/4)) (hYmem : Y∈Icc (1/2 : ℝ) (13/10))
    (hcircle : (P+1)^2+Y^2≤q) (hqL : qLow≤q) (hq : q≤qCap)
    (hr : r∈Icc 0 frameCap) (hz : z∈Ioc 0 frameCap)
    (hGA : 1/2≤V P Y z)
    (hgain : CrossedLargeScalar.demand q P Y r 0+z/150≤H.y) :
    Nonempty (Pair q Y r H) := by
  have hzI : z∈Icc 0 frameCap := ⟨hz.1.le,hz.2⟩
  have htr := transport_trig hzI
  have hsin : 0<Real.sin z := Real.sin_pos_of_pos_of_lt_pi hz.1
    (by dsimp [frameCap] at hz; linarith [hz.2,Real.pi_gt_three])
  have hPcos := mul_le_mul_of_nonneg_left htr.2.1 (show 0≤P by linarith [hPmem.1])
  have hYsin := mul_pos (show 0<Y by linarith [hYmem.1]) hsin
  have hP : 1/2<P := by dsimp [V] at hGA; linarith
  let η := min ((P-1/2)/2) (z/300)
  have hη : 0<η := lt_min (by linarith) (by linarith [hz.1])
  have hηP : η≤(P-1/2)/2 := min_le_left _ _
  have hηz : η≤z/300 := min_le_right _ _
  let C := P-η
  have hC : C∈Icc (1/2 : ℝ) (3/4) := by
    dsimp [C]
    constructor <;> linarith [hPmem.2]
  let G' := SignedPoint.outerAt q (1/2-C)
  let A' : SignedPoint := ⟨C+1/2,Y-1/2⟩
  have hGy : G'.y≤0 := by dsimp [G',SignedPoint.outerAt]; linarith [hC.1]
  have hdiag : |1/2-C|≤diagonalCoordinate q := by
    rw [abs_of_nonpos (show 1/2-C≤0 by linarith [hC.1])]
    linarith [hC.2,(uniform_circle_reserves hqL hq).1]
  obtain ⟨hGs,hGq,hGc⟩ := SignedPoint.outerAt_spec hqL hdiag
  have hAy : 0≤A'.y := by dsimp [A']; linarith [hYmem.1]
  have hAs : A'.Sorted := by
    constructor
    · dsimp [A']; linarith [hC.1]
    · rw [abs_of_nonneg hAy]
      dsimp [A']
      linarith [hC.1,hYmem.2]
  have hAc : A'.AvoidsCore := by
    have ha : 1≤A'.a := by dsimp [A']; linarith [hC.1]
    dsimp [SignedPoint.AvoidsCore,SignedPoint.coreDistance]
    rw [max_eq_left (by linarith : 0≤A'.a-1/2)]
    have h1 : (1/2:ℝ)^2≤(A'.a-1/2)^2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    linarith [sq_nonneg (max (|A'.y|-1/2) 0)]
  have hAq : A'.circle<q := by
    have hp : C+1<P+1 := by dsimp [C]; linarith
    have hs := pow_lt_pow_left₀ hp (show 0≤C+1 by linarith [hC.1]) (by decide : (2:ℕ)≠0)
    have hc : A'.circle=(C+1)^2+Y^2 := by
      dsimp [SignedPoint.circle]
      rw [abs_of_nonneg hAy]
      dsimp [A']
      ring
    rw [hc]
    linarith [hcircle]
  have hradP : 0≤q-P^2 := by linarith [hcircle,hPmem.1,sq_nonneg Y]
  have hCP : C≤P := by dsimp [C]; linarith
  have hC2 := pow_le_pow_left₀ (show 0≤C by linarith [hC.1]) hCP 2
  have hW : Real.sqrt (q-P^2)≤Real.sqrt (q-C^2) :=
    Real.sqrt_le_sqrt (by linarith)
  have hrtr := transport_trig hr
  have hWsin := mul_le_mul_of_nonneg_right hW hrtr.2.2.1
  have hηcos := mul_le_mul_of_nonneg_left hrtr.2.1 hη.le
  have hGa : G'.a=Real.sqrt (q-C^2)-1/2 := by
    dsimp [G',SignedPoint.outerAt]
    rw [abs_of_nonpos (show 1/2-C≤0 by linarith [hC.1])]
    congr 2
    ring
  have hGyEq : G'.y=1/2-C := rfl
  have hHG : zeroFeasible H G' r 0 := by
    have hcap := hgain
    simp only [CrossedLargeScalar.demand,V,Real.cos_zero,Real.sin_zero,mul_one,
      mul_zero,sub_zero,add_zero] at hcap
    have hW0 : W q P Y 0=Real.sqrt (q-P^2) := by simp [W,V]
    rw [hW0] at hcap
    rw [zeroFeasible,edgeWidth_positive_formula hr]
    simp only [zeroProjection,Matrix.cons_val_zero,hGa,hGyEq]
    dsimp [C] at hWsin ⊢
    linarith
  have hGA' : quarterFeasible G' A' 0 0 := by
    simp [quarterFeasible,quarterProjection,G',A',SignedPoint.outerAt]
    linarith
  exact ⟨{
    pointG := G'
    pointA := A'
    G_sorted := hGs
    G_avoids := hGc
    G_circle := hGq
    G_nonpos := hGy
    A_sorted := hAs
    A_avoids := hAc
    A_circle := hAq
    A_tangent := rfl
    HG := hHG
    GA := hGA' }⟩

theorem strict_pair {q P Y r z : ℝ} {H : SignedPoint}
    (S : CrossedLargeScalar.CapData q P Y) (hqL : qLow≤q)
    (hr : r∈Icc 0 frameCap) (hz : z∈Ioc 0 frameCap)
    (hGA : 1/2≤V P Y z)
    (hgain : CrossedLargeScalar.demand q P Y r 0+z/150≤H.y) :
    Nonempty (Pair q Y r H) :=
  strict_pair_of_bounds ⟨S.P_mem.1,by linarith [S.P_mem.2]⟩
    ⟨by linarith [S.Y_mem.1],S.Y_mem.2⟩ S.circle.le hqL S.ceiling hr hz hGA hgain

end CrossedLargeConstruction

namespace SignedCycle
open CrossedLargeGeometry CrossedLargeConstruction

theorem HardOuterGeometry.crossed_HG0_large_output {q : ℝ}
    (I : HardOuterGeometry q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H≤I.cycle.theta A)
    (hlarge : 1/2≤(I.cycle.point A).y) (hHG : I.cycle.Feasible H 0) :
    I.cycle.theta A-I.cycle.theta H<1/25 ∧
      Nonempty (CrossedGAOutput q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
        (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) := by
  let r := I.cycle.theta A-I.cycle.theta H
  let z := I.cycle.theta G-I.cycle.theta A
  have hr : r∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hHA,(le_abs_self r).trans (I.necessary.spread A H)⟩
  have hz : z∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hAG,(le_abs_self z).trans (I.necessary.spread G A)⟩
  have hGnormal := I.large_middle_G_negative hq hAB hnorm hTA hAG hlarge
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-z) 0 := by
    simpa [z,Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,neg_sub]
      using I.GA_hard
  have hreserve := I.crossed_HG0_large_reserve hqL hq hAB hnorm hTA hAG hHA hlarge hHG
  refine ⟨hreserve.1,?_⟩
  by_cases hz0 : z=0
  · have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) r 0 := by
      have hframes : I.cycle.theta 1=I.cycle.theta A := by
        change I.cycle.theta G=I.cycle.theta A; dsimp [z] at hz0; linarith
      simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg,hframes,r] using hHG
    refine ⟨{
      pointG := I.cycle.point G
      pointA := I.cycle.point A
      G_sorted := I.necessary.sorted G
      G_avoids := I.necessary.core G
      G_contained := I.necessary.contained G
      G_nonpos := hGnormal.le
      A_sorted := I.necessary.sorted A
      A_avoids := I.necessary.core A
      A_contained := I.necessary.contained A
      A_tangent := rfl
      HG_zero := hHG'
      GA_hard := by simpa [hz0] using hGA
      A_strict := by intro h; change 0<z at h; linarith
      A_loss := fun h => h
      at_zero := fun _ => ⟨rfl,rfl⟩ }⟩
  · have hzpos : 0<z := lt_of_le_of_ne hz.1 (Ne.symm hz0)
    obtain ⟨S,hcap⟩ := actual_hard_cap hq (I.necessary.sorted A) (I.necessary.core A)
      (I.necessary.contained A) hlarge hGnormal.le hz hGA
    obtain ⟨O⟩ := strict_pair S hqL hr ⟨hzpos,hz.2⟩
      (show 1/2≤V (capP q (I.cycle.point A)) (capY (I.cycle.point A)) z by linarith)
      hreserve.2
    exact ⟨{
      pointG := O.pointG
      pointA := O.pointA
      G_sorted := O.G_sorted
      G_avoids := O.G_avoids
      G_contained := O.G_circle.le
      G_nonpos := O.G_nonpos
      A_sorted := O.A_sorted
      A_avoids := O.A_avoids
      A_contained := O.A_circle.le
      A_tangent := by simpa [capY] using O.A_tangent
      HG_zero := O.HG
      GA_hard := O.GA
      A_strict := fun _ => O.A_circle
      A_loss := fun _ => O.A_circle
      at_zero := by intro h; exact (hz0 h).elim }⟩

theorem HardInput.crossed_HG0_large_output {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H≤I.cycle.theta A)
    (hlarge : 1/2≤(I.cycle.point A).y) (hHG : I.cycle.Feasible H 0) :
    I.cycle.theta A-I.cycle.theta H<1/25 ∧
      Nonempty (CrossedGAOutput q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
        (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) :=
  I.outerGeometry.crossed_HG0_large_output hqL hq hAB hnorm hTA hAG hHA hlarge hHG

end SignedCycle
end SquaresInCircles.Eight.TableFree
