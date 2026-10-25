module

public import SquaresInCircles.Eight.Words.Aligned.ChainBounds
public import SquaresInCircles.Eight.Owners.NecessaryCycle

/-!
# Eight squares: quantitative bounds invoked on the actual aligned hard cycle

Original HG/TD witnesses are canceled with the original
GA0/BT2 inequalities.  The resulting estimates use the unchanged H/A/B/D
points and their actual containing circles.  No E frame or owner has yet
been restricted.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
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
  have hnH : next H=G := rfl
  have hnT : next T=D := rfl
  have hnA : next A=B := rfl
  have hnG : next G=A := rfl
  have hnB : next B=T := rfl
  have hHsep : 1≤(I.cycle.point H).y-(I.cycle.point G).y := by
    have hf := I.witnesses.feasible H
    rw [Feasible,slack,edge,ite_eq_left (show Candidate.word H=0 by decide),delta,hnH,hHG,
      sub_self,zeroProjection_aligned,edgeWidth_zero] at hf
    rcases hHowner with hj | hj <;> rw [hj] at hf <;> simpa [sub_nonneg] using hf
  have hTsep : 1≤(I.cycle.point T).y-(I.cycle.point D).y := by
    have hf := I.witnesses.feasible T
    rw [Feasible,slack,edge,ite_eq_left (show Candidate.word T=0 by decide),delta,hnT,hTD,
      sub_self,zeroProjection_aligned,edgeWidth_zero] at hf
    rcases hTowner with hj | hj <;> rw [hj] at hf <;> simpa [sub_nonneg] using hf
  have hAB' : 1≤(I.cycle.point A).y-(I.cycle.point B).y := by
    have hf := I.witnesses.feasible A
    rw [Feasible,slack,edge,ite_eq_left (show Candidate.word A=0 by decide),delta,hnA,hAB,
      sub_self,zeroProjection_aligned,edgeWidth_zero] at hf
    rcases hAowner with hj | hj <;> rw [hj] at hf <;> simpa [sub_nonneg] using hf
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (-(I.cycle.theta H-I.cycle.theta A)) 0 := by
    have hf := I.GA_hard
    rw [Feasible,slack,edge,ite_eq_right (show Candidate.word G≠0 by decide),delta,hnG,hHG,
      show I.cycle.theta A-I.cycle.theta H=-(I.cycle.theta H-I.cycle.theta A) by ring] at hf
    exact sub_nonneg.mp hf
  have hBT : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-(I.cycle.theta A-I.cycle.theta D)) 2 := by
    have hf := I.BT_hard
    rw [Feasible,slack,edge,ite_eq_right (show Candidate.word B≠0 by decide),delta,hnB,hTD,←hAB,
      show I.cycle.theta D-I.cycle.theta A=-(I.cycle.theta A-I.cycle.theta D) by ring] at hf
    exact sub_nonneg.mp hf
  simp only [quarterFeasible,quarterProjection,Real.cos_neg,Real.sin_neg,edgeWidth_neg,
    Matrix.cons_val_zero,Matrix.cons_val_two,Matrix.head_cons,
    Matrix.tail_cons] at hGA hBT
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

theorem primary_upper_of_tangent {P : SignedPoint} (_hPa : 0<P.a)
    (hPy : 67/200<P.y) (hPc : P.circle≤qCap) : P.a<647/500 := by
  rw [SignedPoint.circle,abs_of_pos (by linarith : 0<P.y)] at hPc
  have hminor := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤167/200)
    (show 167/200≤P.y+1/2 by linarith) 2
  by_contra! hbad
  have hmajor := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤897/500)
    (show 897/500≤P.a+1/2 by linarith) 2
  dsimp [qCap] at hPc
  nlinarith

theorem outer_primary_upper {P : SignedPoint} (_hPa : 0<P.a)
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
    simp only [Dr,Br,u,SignedPoint.reflect]
    linarith
  have hAB' : 1≤Ar.y+Br.y := by
    simp only [Ar,Br,SignedPoint.reflect]
    linarith
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
    rwa [abs_of_nonneg hHy] at hh
  have hDyu : Dr.y<9/10 := by
    have hh := (Dr.coordinate_bounds hDs hDcore hDc hq).2.2
    rwa [abs_of_nonneg hDy] at hh
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
  have hHhalf : 1/2<Hr.a := SignedPoint.primary_gt_half hHs hHcore
  have hDhalf : 1/2<Dr.a := SignedPoint.primary_gt_half hDs hDcore
  refine {
    span_nonneg := by rw [←heq]; linarith
    span_lt := by rwa [heq] at hshort
    A_primary := ⟨hAa,hAu⟩
    B_primary := ⟨hBa,hBu⟩
    A_tangent := ⟨hAylo,hAyu⟩
    B_tangent := ⟨hBylo,hByu⟩
    H_tangent := ⟨hHylo,hHyu⟩
    D_tangent := ⟨hDylo,hDyu⟩
    H_primary := ⟨hHhalf,hHu⟩
    D_primary := ⟨hDhalf,hDu⟩
    primary_sum := ?_ }
  rw [heq] at hsum
  exact hsum

end SignedCycle
end SquaresInCircles.Eight
