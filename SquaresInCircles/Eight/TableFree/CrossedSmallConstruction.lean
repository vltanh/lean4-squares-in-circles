module

public import SquaresInCircles.Eight.TableFree.CrossedSmallGeometry
public import SquaresInCircles.Eight.TableFree.CrossedLargeConstruction
public import SquaresInCircles.Eight.TableFree.SmallIntermediateSigns

/-!
# Actual GA-aligned output from the small crossed source

Uncompiled source draft.  The source captures sharpen its actual lifted
cap to P<.7195.  The shared explicit aligned-pair construction can then
spend part of the z/100 reserve on A, producing a strict A deficit below
the same q.  If the original GA angle is zero both points are retained.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
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
end SquaresInCircles.Eight.TableFree
