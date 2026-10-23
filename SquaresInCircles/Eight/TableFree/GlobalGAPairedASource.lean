module

public import SquaresInCircles.Eight.TableFree.GlobalGAPairedAComparison

/-!
# Nonnegative signed A-primary total on the original cycle

Uncompiled source join of all three TD alternatives in Section 3 of
the paired-A hand proof. Both original A primaries may have either sign;
only their signed sum is required to be nonnegative. TD0 is unrestricted,
and the two TD2 signs use their respective completed stress inequalities.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PairedA
open Candidate Secondary

theorem actual_false {q : ℝ} {C : SignedCycle}
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcoreT : (C.point T).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤total C)
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G 3) (hAB : C.Feasible A 2) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 0 ∨ C.Feasible T 2)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0 ∨ hg=2) ∧ C.Feasible H hg := by
    rcases hHG with hh | hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  have hs' := comparison_sorted hs
  have hc' := comparison_contained hc
  have hvar' := (comparison_variations C).1.trans hvar
  have ha' : 0≤TwoPositive.Source.aError (comparison C) true := by simpa using ha
  have hH : (comparison C).point H=C.point H := comparison_points C H (by decide)
  have hG : (comparison C).point G=C.point G := comparison_points C G (by decide)
  have hB : (comparison C).point B=C.point B := comparison_points C B (by decide)
  have hD : (comparison C).point D=C.point D := comparison_points C D (by decide)
  have hT : (comparison C).point T=C.point T := comparison_points C T (by decide)
  have hHy' : 0≤((comparison C).point H).y := by simpa [hH] using hHy
  have hGy' : ((comparison C).point G).y≤0 := by simpa [hG] using hGy
  have hBy' : ((comparison C).point B).y≤0 := by simpa [hB] using hBy
  have hDy' : ((comparison C).point D).y≤0 := by simpa [hD] using hDy
  rcases hTD with hTD | hTD
  · obtain ⟨k,l,c,hk,hl,hc0,hpos⟩ := PositiveATD0.Source.exists_positive_stress true
      hs' hc' hq hHy' hGy' hBy' hDy' hvar' ha' hhg
    have hu := comparison_stress_nonpos (k:=k) (l:=l) (b:=c) (t:=c)
      (hs A) (hc A) hq hvar ha hhg (Or.inl rfl) hk hl hc0 hc0
      hHG hGA hAB hBT hTD hDE hEH
    have hp : 0<stress (comparison C) (comparisonOwners hg 0) (weights k l c c) := by
      simpa only [PositiveATD0.Source.actualStress,PositiveATD0.Source.owners,
        PositiveATD0.Source.weights,stress,comparisonOwners,weights,if_true] using hpos
    linarith
  · rcases le_total 0 (delta C.theta T) with hz | hz
    · have hz' : 0≤delta (comparison C).theta T := by simpa using hz
      obtain ⟨k,l,c,hk,hl,hc0,hpos⟩ := TwoPositive.Source.exists_positive_stress true
        hs' hc' hq hHy' hGy' hBy' hDy' hvar' ha' hz' hhg
      have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
      have hzcap : delta C.theta T∈Icc 0 frameCap :=
        ⟨hz,(le_abs_self _).trans (original_error_bound hvar hn T)⟩
      have hu := comparison_stress_nonpos (k:=k) (l:=l)
        (b:=PositiveTD.tilted c (delta C.theta T)) (t:=c)
        (hs A) (hc A) hq hvar ha hhg (Or.inr rfl) hk hl
        (PositiveTD.tilted_pos hc0 hzcap).le hc0.le hHG hGA hAB hBT hTD hDE hEH
      have hp : 0<stress (comparison C) (comparisonOwners hg 2)
          (weights k l (PositiveTD.tilted c (delta C.theta T)) c) := by
        simpa only [TwoPositive.Source.actualStress,TwoPositive.Source.owners,PositiveTD.weights,
          stress,comparisonOwners,weights,if_true,comparison_T] using hpos
      linarith
    · have hz' : delta (comparison C).theta T≤0 := by simpa using hz
      have hcoreT' : ((comparison C).point T).AvoidsCore := by simpa [hT] using hcoreT
      obtain ⟨k,l,c,hk,hl,hc0,hpos⟩ := PositiveANegativeTD.Source.exists_positive_stress true
        hs' hc' hcoreT' hq hHy' hGy' hBy' hDy' hvar' ha' hz' hhg
      have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
      have hcos : 0<Real.cos (-delta C.theta T) := by
        simpa using transport_cos_pos (original_error_bound hvar hn T)
      have hu := comparison_stress_nonpos (k:=k) (l:=l)
        (b:=c) (t:=c/Real.cos (-delta C.theta T))
        (hs A) (hc A) hq hvar ha hhg (Or.inr rfl) hk hl hc0
        (div_nonneg hc0 hcos.le) hHG hGA hAB hBT hTD hDE hEH
      have hp : 0<stress (comparison C) (comparisonOwners hg 2)
          (weights k l c (c/Real.cos (-delta C.theta T))) := by
        simpa only [PositiveANegativeTD.Source.actualStress,PositiveANegativeTD.Source.owners,
          PositiveANegativeTD.Source.weights,PositiveANegativeTD.Source.sError,
          stress,comparisonOwners,weights,if_true,comparison_T] using hpos
      linarith

/-- The original-radius paired-A row, including all mixed-sign allocations
with nonnegative total and every retained TD owner. -/
theorem frame_nonnegative_total_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (hGA : (forwardAxis 3).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis 2).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 2).Feasible (C.square B) (C.square T))
    (hDE : (forwardAxis 2).Feasible (C.square D) (C.square E))
    (hEH : (forwardAxis 0).Feasible (C.square E) (C.square H))
    (ha : 0≤delta F.theta G+delta F.theta A) : False := by
  have hn := SignedCycle.atFrame_necessary F
  have hanchors := GlobalOriginalOwners.atFrame_anchors F hq hE
  have hG := GlobalQuarterOuter.frame_high_anchor F hq G (by norm_num [word,G])
    3 (Or.inr rfl) (by simpa [G,A,next] using hGA)
  have hzero (i : Vertex) (hi : word i=0) :
      (SignedCycle.atFrame F).Feasible i 0 ∨ (SignedCycle.atFrame F).Feasible i 2 := by
    let j := SignedCycle.retainedOwner F i
    have hf := SignedCycle.retainedOwner_feasible F i
    have hactual := (SignedCycle.atFrame_feasible F i j).1 hf
    rcases GlobalZeroSign.of_frame F hq i hi j hactual with hh | hh
    · exact Or.inl (by simpa [hh.1] using hf)
    · exact Or.inr (by simpa [hh.1] using hf)
  apply actual_false hn.sorted hn.contained (hn.core T) hq.2
    hanchors.2.1.le ((SignedCycle.atFrame_y_neg_iff F G).2 hG.2).le
    hanchors.2.2.2.1.le hanchors.2.2.2.2.2.le
    (FramePhysicalTransport.candidate_variations F hq).1.le
    (by simpa [total,SignedCycle.atFrame] using ha)
    (hzero H (by norm_num [word,H]))
  · exact (SignedCycle.atFrame_feasible F G 3).2 (by simpa [G,A,next] using hGA)
  · exact (SignedCycle.atFrame_feasible F A 2).2 (by simpa [A,B,next] using hAB)
  · exact (SignedCycle.atFrame_feasible F B 2).2 (by simpa [B,T,next] using hBT)
  · exact hzero T (by norm_num [word,T])
  · exact (SignedCycle.atFrame_feasible F D 2).2 (by simpa [D,E,next] using hDE)
  · exact (SignedCycle.atFrame_feasible F E 0).2 (by simpa [E,H,next] using hEH)

end SquaresInCircles.Eight.TableFree.GlobalGA.PairedA
