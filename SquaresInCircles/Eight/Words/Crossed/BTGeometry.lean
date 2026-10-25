module

public import SquaresInCircles.Eight.Owners.Small.CancelingGeometry
public import SquaresInCircles.Eight.Owners.Small.PositiveReflection
public import SquaresInCircles.Eight.Words.Crossed.GACycle
public import SquaresInCircles.Eight.Words.Crossed.LowerInverseRate
public import SquaresInCircles.Eight.Words.Crossed.LargeGeometry
public import SquaresInCircles.Eight.Words.Crossed.SmallGeometry
public import SquaresInCircles.Eight.Words.Wrong.SignCapture

/-!
# Eight squares: all four crossed BT-side outputs at the original E

The local necessary geometry and proved source
budget are reflected, each corresponding HG theorem constructs its
actual same-q output, and only the local output is reflected back.
The public hard-source statements derive their intermediate sign bounds
from the original system and retain the original E and mixed witnesses.
-/

section
/-!
## Crossed large HG2 reduction on the hard source

The larger-middle sign theorem and the one-tenth opposite capture of the original cycle supply
every sign bound used by the local construction (`HardOuterGeometry.crossed_HG2_large_data`).
The new HG0 contact then enters the large crossing capture at the same q
(`HardInput.crossed_HG2_large_output`). The original H, B, T, D and E data and every inherited
anchor deficit are kept.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCycle
open Candidate EndpointRotationPenalty EndpointBudgetScalars

theorem HardOuterGeometry.crossed_HG2_large_data {q : ℝ}
    (I : HardOuterGeometry q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hlarge : 1/2≤(I.cycle.point A).y) (hHG : I.cycle.Feasible H 2)
    (hT : -(1/10:ℝ)<(I.cycle.point T).y) :
    Nonempty (CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) := by
  let r := I.cycle.theta A-I.cycle.theta H
  let z := I.cycle.theta G-I.cycle.theta A
  let u := I.cycle.theta A-I.cycle.theta T
  have hr : r∈Ioc 0 frameCap :=
    ⟨sub_pos.mpr hHA,(le_abs_self r).trans (I.necessary.spread A H)⟩
  have hz : z∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hAG,(le_abs_self z).trans (I.necessary.spread G A)⟩
  have hu : u∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hTA,(le_abs_self u).trans (I.necessary.spread A T)⟩
  have hspan : z+r≤frameCap := by
    have hh := (le_abs_self (I.cycle.theta G-I.cycle.theta H)).trans (I.necessary.spread G H)
    dsimp [z,r]
    linarith
  have hG := I.large_middle_G_negative hq hAB hnorm hTA hAG hlarge
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) (z+r) 2 := by
    convert hHG using 1
    simp [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,z,r]
  have hGA' : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-z) 0 := by
    simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,z] using I.GA_hard
  have hBT' : quarterFeasible (I.cycle.point B) (I.cycle.point T) (-u) 2 := by
    rw [show -u=I.cycle.theta T-I.cycle.theta B by dsimp [u]; rw [←hAB]; ring]
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible] using I.BT_hard
  have hTD := (signed_outer_charges hq I.necessary I.anchors_normal I.witnesses I.zero_signs).2
  have hep := I.endpoint_bound hq
  have hbudget : (I.cycle.point H).y-(I.cycle.point T).y+EndpointRotationPenalty.charge*(r-u)<1-S0 := by
    dsimp [r,u,epsilon] at *
    linarith
  exact CrossedCancelingConstruction.actual_output hqL hq
    (I.necessary.sorted H) (I.necessary.sorted A) (I.necessary.sorted B)
    (I.necessary.core A) (I.necessary.contained H) (I.necessary.contained A)
    (I.necessary.contained B) I.anchors_normal.H_nonneg hlarge I.anchors_normal.B_nonpos
    hG.le hT hnorm hr hz hu hspan hHG' hGA' hBT' hbudget

theorem HardInput.crossed_HG2_large_output {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hlarge : 1/2≤(I.cycle.point A).y) (hHG : I.cycle.Feasible H 2) :
    I.cycle.theta A-I.cycle.theta H<1/25 ∧
      Nonempty (CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
        (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) := by
  obtain ⟨O⟩ := I.outerGeometry.crossed_HG2_large_data hqL hq hAB hnorm hTA hAG hHA
    hlarge hHG (I.small_intermediate_signs hq).2
  let J := I.fromCrossedGAData hAB O
  have hAB' : J.cycle.theta A=J.cycle.theta B := hAB
  have hsum' : (J.cycle.point A).y-(J.cycle.point B).y=1 := by
    change O.pointA.y-(I.cycle.point B).y=1
    rw [O.A_tangent]
    exact hnorm
  have hlarge' : 1/2≤(J.cycle.point A).y := by
    change 1/2≤O.pointA.y
    rw [O.A_tangent]
    exact hlarge
  have hHG' : J.cycle.Feasible H 0 := by
    simpa [J,HardInput.fromCrossedGAData,crossedGACycle,Feasible,slack,edge,word,
      delta,next,H,G,A,zeroFeasible,HardInput.outerGeometry] using O.HG_zero
  have hcap := J.crossed_HG0_large_reserve hqL hq hAB' hsum' hTA le_rfl hHA.le hlarge' hHG'
  exact ⟨hcap.1,⟨O⟩⟩

end SquaresInCircles.Eight.SignedCycle
end
end
end

section
/-!
## Realizing the crossed large-side alignment at the same q

A positive G-frame motion spends half of the reserve by lowering the lifted A primary, and the
adjacent G is placed on the same q-circle (`strict_pair`). This gives an HG0/GA0 pair and a
strict A circle loss below q (`HardInput.crossed_HG0_large_output`). At zero motion the original
A and G are kept, so every strict A inequality of the source is preserved as well.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
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
end SquaresInCircles.Eight
end
end
end

section
/-!
## GA-aligned output from the small crossed source

The captures of the source sharpen its lifted cap to `P < .7195`. The aligned-pair construction
of `CrossedLargeConstruction` then spends part of the reserve `z/100` on A, producing a strict A
deficit below the same q (`HardInput.crossed_HG0_small_output`). If the original GA angle is
zero both points are kept.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate PositiveSmallScalar CrossedLargeGeometry CrossedLargeConstruction
namespace SignedCycle

theorem HardOuterGeometry.crossed_HG0_small_output {q : ℝ}
    (I : HardOuterGeometry q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hGy : (I.cycle.point G).y≤0) (hHG : I.cycle.Feasible H 0) :
    47/98<(I.cycle.point A).y ∧ I.cycle.theta A-I.cycle.theta H<1/100 ∧
      Nonempty (CrossedGAOutput q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
        (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) := by
  let r := I.cycle.theta A-I.cycle.theta H
  let z := I.cycle.theta G-I.cycle.theta A
  have hr : r∈Icc 0 frameCap :=
    ⟨(sub_pos.mpr hHA).le,(le_abs_self r).trans (I.necessary.spread A H)⟩
  have hz : z∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hAG,(le_abs_self z).trans (I.necessary.spread G A)⟩
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-z) 0 := by
    simpa [z,Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,neg_sub] using I.GA_hard
  obtain ⟨hb,hshort,hgain⟩ := I.crossed_HG0_small_reserve hqL hq hAB hnorm
    hTA hAG hHA hsmall hGy hHG
  refine ⟨hb,hshort,?_⟩
  by_cases hz0 : z=0
  · have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) r 0 := by
      have hframes : I.cycle.theta 1=I.cycle.theta A := by
        change I.cycle.theta G=I.cycle.theta A; dsimp [z] at hz0; linarith
      simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg,hframes,r] using hHG
    exact ⟨{
      pointG := I.cycle.point G
      pointA := I.cycle.point A
      G_sorted := I.necessary.sorted G
      G_avoids := I.necessary.core G
      G_contained := I.necessary.contained G
      G_nonpos := hGy
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
    obtain ⟨S,hcap⟩ := CrossedSmallGeometry.actual_hard_cap hqL hq
      (I.necessary.sorted A) (I.necessary.core A) (I.necessary.contained A) hsmall hGy hz hGA
    have hY : 48/49≤capY (I.cycle.point A) := by dsimp [capY]; linarith
    have hP := CrossedSmallScalar.tight_primary S hY
    have hgain' : CrossedLargeScalar.demand q (capP q (I.cycle.point A))
        (capY (I.cycle.point A)) r 0+z/150≤(I.cycle.point H).y := by
      change CrossedLargeScalar.demand q (capP q (I.cycle.point A))
        (capY (I.cycle.point A)) r 0+z/100≤(I.cycle.point H).y at hgain
      linarith
    obtain ⟨O⟩ := strict_pair_of_bounds
      (show capP q (I.cycle.point A)∈Icc (1/2 : ℝ) (3/4) from
        ⟨S.P_mem.1,by linarith⟩)
      (show capY (I.cycle.point A)∈Icc (1/2 : ℝ) (13/10) from
        ⟨by linarith [S.Y_mem.1],by linarith [S.Y_mem.2]⟩)
      S.circle.le hqL hq hr ⟨hzpos,hz.2⟩
      (show 1/2≤V (capP q (I.cycle.point A)) (capY (I.cycle.point A)) z by linarith)
      hgain'
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

theorem HardInput.crossed_HG0_small_output {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2)) (hHG : I.cycle.Feasible H 0) :
    47/98<(I.cycle.point A).y ∧ I.cycle.theta A-I.cycle.theta H<1/100 ∧
      Nonempty (CrossedGAOutput q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
        (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) := by
  have hG := I.small_middle_G_negative hqL hq hAB hnorm
    ⟨by linarith [hsmall.1],hsmall.2⟩ hTA hAG
  exact I.outerGeometry.crossed_HG0_small_output hqL hq hAB hnorm hTA hAG hHA hsmall hG.le hHG

end SignedCycle
end SquaresInCircles.Eight
end
end
end

section
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
end
end
end
