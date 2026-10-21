module

public import SquaresInCircles.Eight.TableFree.AlignedChainBounds

/-!
# Quantitative bounds invoked on the actual aligned hard cycle

Uncompiled draft.  Original HG/TD witnesses are canceled with the original
GA0/BT2 inequalities.  The resulting estimates use the unchanged H/A/B/D
points and their actual containing circles.  No E frame or owner has yet
been restricted.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace SignedCycle

theorem HardInput.aligned_composites {q : ℝ} (I : HardInput q)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D) :
    1+edgeWidth (I.cycle.theta H-I.cycle.theta A)≤
      (I.cycle.point H).y+(I.cycle.point A).a*Real.cos (I.cycle.theta H-I.cycle.theta A)-
        (I.cycle.point A).y*Real.sin (I.cycle.theta H-I.cycle.theta A) ∧
    1+edgeWidth (I.cycle.theta A-I.cycle.theta D)≤
      -(I.cycle.point D).y+(I.cycle.point B).a*Real.cos (I.cycle.theta A-I.cycle.theta D)+
        (I.cycle.point B).y*Real.sin (I.cycle.theta A-I.cycle.theta D) ∧
    1≤(I.cycle.point A).y-(I.cycle.point B).y := by
  have hHowner : I.witnesses.owner H=0 ∨ I.witnesses.owner H=2 := by
    simpa [normalOwners,H] using I.witnesses.allowed H
  have hTowner : I.witnesses.owner T=0 ∨ I.witnesses.owner T=2 := by
    simpa [normalOwners,T] using I.witnesses.allowed T
  have hAowner : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
    simpa [normalOwners,A] using I.witnesses.allowed A
  have hHsep : 1≤(I.cycle.point H).y-(I.cycle.point G).y := by
    rcases hHowner with hj | hj <;>
      simpa [Feasible,slack,edge,word,delta,next,H,G,hHG,hj,zeroProjection,sub_nonneg]
        using I.witnesses.feasible H
  have hTsep : 1≤(I.cycle.point T).y-(I.cycle.point D).y := by
    rcases hTowner with hj | hj <;>
      simpa [Feasible,slack,edge,word,delta,next,T,D,hTD,hj,zeroProjection,sub_nonneg]
        using I.witnesses.feasible T
  have hAB' : 1≤(I.cycle.point A).y-(I.cycle.point B).y := by
    rcases hAowner with hj | hj <;>
      simpa [Feasible,slack,edge,word,delta,next,A,B,hAB,hj,zeroProjection,sub_nonneg]
        using I.witnesses.feasible A
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (-(I.cycle.theta H-I.cycle.theta A)) 0 := by
    simpa [Feasible,slack,edge,word,delta,next,G,A,hHG,quarterFeasible,sub_nonneg,neg_sub]
      using I.GA_hard
  have hBT : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-(I.cycle.theta A-I.cycle.theta D)) 2 := by
    simpa [Feasible,slack,edge,word,delta,next,B,T,hTD,hAB,quarterFeasible,sub_nonneg,neg_sub]
      using I.BT_hard
  simp [quarterFeasible,quarterProjection,Real.cos_neg,Real.sin_neg] at hGA hBT
  exact ⟨by linarith,by linarith,hAB'⟩

end SignedCycle

namespace AlignedChainBounds

structure Bounds (C : SignedCycle) : Prop where
  span_nonneg : 0≤C.theta H-C.theta D
  span_lt : C.theta H-C.theta D<11/50
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

theorem primary_upper_of_tangent {P : SignedPoint} (hPa : 0<P.a)
    (hPy : 67/200<P.y) (hPc : P.circle≤qCap) : P.a<647/500 := by
  rw [SignedPoint.circle,abs_of_pos (by linarith : 0<P.y)] at hPc
  have hminor := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤167/200)
    (show 167/200≤P.y+1/2 by linarith) 2
  by_contra! hbad
  have hmajor := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤897/500)
    (show 897/500≤P.a+1/2 by linarith) 2
  dsimp [qCap] at hPc
  nlinarith

theorem outer_primary_upper {P : SignedPoint} (hPa : 0<P.a)
    (hPy : 353/500<P.y) (hPc : P.circle≤qCap) : P.a<11/10 := by
  rw [SignedPoint.circle,abs_of_pos (by linarith : 0<P.y)] at hPc
  have hminor := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤6/5)
    (show 6/5≤P.y+1/2 by linarith) 2
  by_contra! hbad
  have hmajor := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤8/5)
    (show 8/5≤P.a+1/2 by linarith) 2
  dsimp [qCap] at hPc
  nlinarith

end AlignedChainBounds

namespace SignedCycle
open AlignedChainBounds

theorem HardInput.aligned_bounds {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A) : Bounds I.cycle := by
  let t := I.cycle.theta H-I.cycle.theta A
  let u := I.cycle.theta A-I.cycle.theta D
  let Hr := I.cycle.point H
  let Ar := I.cycle.point A
  let Br := (I.cycle.point B).reflect
  let Dr := (I.cycle.point D).reflect
  have ht : 0≤t := sub_nonneg.mpr hleft
  have hu : 0≤u := sub_nonneg.mpr hright
  have heq : t+u=I.cycle.theta H-I.cycle.theta D := by dsimp [t,u]; ring
  have hspan : t+u≤7/10 := by
    rw [heq]
    have hh := I.necessary.spread H D
    exact (le_abs_self _).trans hh
  have htwide : t∈Icc 0 (7/10 : ℝ) := ⟨ht,by linarith⟩
  have huwide : u∈Icc 0 (7/10 : ℝ) := ⟨hu,by linarith⟩
  have hHs : Hr.Sorted := I.necessary.sorted H
  have hAs : Ar.Sorted := I.necessary.sorted A
  have hBs : Br.Sorted := by simpa [Br] using I.necessary.sorted B
  have hDs : Dr.Sorted := by simpa [Dr] using I.necessary.sorted D
  have hHcore : Hr.AvoidsCore := I.necessary.core H
  have hAcore : Ar.AvoidsCore := I.necessary.core A
  have hBcore : Br.AvoidsCore := by simpa [Br] using I.necessary.core B
  have hDcore : Dr.AvoidsCore := by simpa [Dr] using I.necessary.core D
  have hHc : Hr.Contained q := I.necessary.contained H
  have hAc : Ar.Contained q := I.necessary.contained A
  have hBc : Br.Contained q := by simpa [Br] using I.necessary.contained B
  have hDc : Dr.Contained q := by simpa [Dr] using I.necessary.contained D
  have hHy : 0≤Hr.y := I.anchors_normal.H_nonneg
  have hAy : 0≤Ar.y := I.anchors_normal.A_nonneg
  have hBy : 0≤Br.y := by dsimp [Br,SignedPoint.reflect]; linarith [I.anchors_normal.B_nonpos]
  have hDy : 0≤Dr.y := by dsimp [Dr,SignedPoint.reflect]; linarith [I.anchors_normal.D_nonpos]
  obtain ⟨hHA0,hBD0,hAB0⟩ := I.aligned_composites hHG hAB hTD
  have hHA : 1+edgeWidth t≤Hr.y+Ar.a*Real.cos t-Ar.y*Real.sin t := hHA0
  have hBD : 1+edgeWidth u≤Dr.y+Br.a*Real.cos u-Br.y*Real.sin u := by
    simpa [Dr,Br,u,SignedPoint.reflect] using hBD0
  have hAB' : 1≤Ar.y+Br.y := by simpa [Ar,Br,SignedPoint.reflect,sub_eq_add_neg] using hAB0
  obtain ⟨hAa,hAyu,hHyl⟩ := single_contact_bounds hq hHs hAs hHcore hAcore
    hHc hAc hHy hAy htwide hHA
  obtain ⟨hBa,hByu,hDyl⟩ := single_contact_bounds hq hDs hBs hDcore hBcore
    hDc hBc hDy hBy huwide hBD
  have hAylo : 67/200<Ar.y := by linarith
  have hBylo : 67/200<Br.y := by linarith
  have hAu := primary_upper_of_tangent hAs.1 hAylo (hAc.trans hq)
  have hBu := primary_upper_of_tangent hBs.1 hBylo (hBc.trans hq)
  have hHyu : Hr.y<9/10 := by
    have hh := (Hr.coordinate_bounds hHs hHcore hHc hq).2.2
    simpa [abs_of_nonneg hHy] using hh
  have hDyu : Dr.y<9/10 := by
    have hh := (Dr.coordinate_bounds hDs hDcore hDc hq).2.2
    simpa [abs_of_nonneg hDy] using hh
  have hHylo : 353/500<Hr.y := by
    have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one t) hAs.1.le
    have hsin := mul_nonneg hAy ((transport_trig htwide).2.2.1)
    have hw := edgeWidth_ge_one t
    linarith
  have hDylo : 353/500<Dr.y := by
    have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one u) hBs.1.le
    have hsin := mul_nonneg hBy ((transport_trig huwide).2.2.1)
    have hw := edgeWidth_ge_one u
    linarith
  have hHu := outer_primary_upper hHs.1 hHylo (hHc.trans hq)
  have hDu := outer_primary_upper hDs.1 hDylo (hDc.trans hq)
  have hmiddle := middle_primary_sum hAs hBs hAy hBy (hAc.trans hq) (hBc.trans hq) hAB'
  have hcharge := charged_outer_tangents htwide huwide
    (by linarith : 1/2≤Ar.a) (by linarith : 1/2≤Br.a)
    hAylo.le hBylo.le hmiddle hHA hBD
  have hsum := outer_primary_sum hHs.1 hDs.1 hHy hDy (hHc.trans hq) (hDc.trans hq)
    ⟨by linarith,hspan⟩ hcharge
  have hshort := short_span hHyu hDyu hAy hBy (hAc.trans hq) (hBc.trans hq)
    ht hu hspan hAB' hHA hBD
  refine {
    span_nonneg := by rw [←heq]; linarith
    span_lt := by rwa [heq] at hshort
    A_primary := ⟨hAa,hAu⟩
    B_primary := ⟨hBa,hBu⟩
    A_tangent := ⟨hAylo,hAyu⟩
    B_tangent := ⟨hBylo,hByu⟩
    H_tangent := ⟨hHylo,hHyu⟩
    D_tangent := ⟨hDylo,hDyu⟩
    H_primary := ⟨SignedPoint.primary_gt_half hHs hHcore,hHu⟩
    D_primary := ⟨SignedPoint.primary_gt_half hDs hDcore,hDu⟩
    primary_sum := ?_ }
  simpa [Hr,Dr,SignedPoint.reflect,heq] using hsum

end SignedCycle
end SquaresInCircles.Eight.TableFree
