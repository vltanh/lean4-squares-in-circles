module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3Prepared

/-!
# Every A normal form with sole nonnegative BT3

Uncompiled finite A dispatch. The actual GA2 secondary is tried before
using a negative-GA tangent cut. If it is absent, that cut is derived
again from the current necessary system, not transported as an
unproved premise. The only transport used here changes A; the E cuts
were already derived while the physical source domain was available.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Complete
open Candidate Secondary SignedCycle PairedE

theorem normal_A_false {Q : ℝ} {C : SignedCycle} {hg : Fin 4} (ga ab de eh : Bool)
    (hn : C.Necessary Q) (hQ : Q≤qCap) (hAr : (C.point A).Boundary Q)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hred : NegativeANormalForm.Reduced (C.point A) ga ab (delta C.theta G) (delta C.theta A))
    (hz : 0≤delta C.theta B) (hreg : ERegime C de eh)
    (hhg : hg=0∨hg=2) (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  rcases hred with ha|⟨hga,hab,hflat,hAy,hu⟩|⟨hga,hab,hflat,hAy,hv⟩
  · exact nonnegative_A_false ga ab de eh hn hQ hHy hGy hBy hDy hvar
      ha hz hreg hhg hHG hGA hAB hBT hTD hDE hEH
  · subst ga
    subst ab
    have hGA3 : C.Feasible G 3 := hGA
    have hAB0 : C.Feasible A 0 := hAB
    by_cases hGA2 : C.Feasible G 2
    · exact nonnegative_A_false false false de eh hn hQ hHy hGy hBy hDy hvar
        (by simp [Source.aTotal,PairedE.total,PairedE.selected]) hz hreg hhg
        hHG hGA2 hAB0 hBT hTD hDE hEH
    · have hs : -delta C.theta G∈Ioc 0 frameCap :=
        ⟨neg_pos.mpr hu.2,by norm_num [frameCap]; linarith [hu.1]⟩
      have hlocal : quarterFeasible (C.point G) (C.point A) (-(-delta C.theta G)) 3 := by
        simpa [Feasible,slack,edge,word,next,G,A,quarterFeasible,sub_nonneg] using hGA3
      have hentry := NegativeA.GA_entry (hn.sorted G) (hn.contained G)
        (hn.sorted A) hAr hQ hGy (fun h => (not_le_of_gt hAy.1 h).elim) hs hlocal
      rcases hentry with hsecondary|⟨_,_,hcut,_⟩
      · apply hGA2
        simpa [Feasible,slack,edge,word,next,G,A,quarterFeasible,sub_nonneg] using hsecondary
      · apply negative_A_false true de eh hn hQ hHy hGy hBy hDy hvar
          (r:=-delta C.theta G)
        · change -delta C.theta G∈Icc (0:ℝ) (1/4)
          exact ⟨hs.1.le,by linarith [hu.1]⟩
        · change delta C.theta G= -(-delta C.theta G)
          ring
        · exact hflat
        · exact hAy.1.le
        · exact hcut.le
        · exact hz
        · exact hreg
        · exact hhg
        · exact hHG
        · exact hGA3
        · exact hAB0
        · exact hBT
        · exact hTD
        · exact hDE
        · exact hEH
  · subst ga
    subst ab
    apply negative_A_false false de eh hn hQ hHy hGy hBy hDy hvar
      (r:=-delta C.theta A)
    · change -delta C.theta A∈Icc (0:ℝ) (19/50)
      exact ⟨(neg_pos.mpr hv.2).le,by linarith [hv.1]⟩
    · change delta C.theta A= -(-delta C.theta A)
      ring
    · exact hflat
    · exact hAy.1.le
    · exact hAy.2.le
    · exact hz
    · exact hreg
    · exact hhg
    · exact hHG
    · exact hGA
    · exact hAB
    · exact hBT
    · exact hTD
    · exact hDE
    · exact hEH

/-- Normalize A only after the source E regime has been established.
The descendant is consumed only by necessary-system source stresses. -/
theorem prepared_false {Q : ℝ} {C : SignedCycle} (I : SourceDomain Q C)
    (hQL : qLow≤Q) (hQU : Q≤qCap) (de eh : Bool)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) (hreg : ERegime C de eh)
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0) (hz : 0≤delta C.theta B) : False := by
  obtain ⟨ga,hga⟩ : ∃ga : Bool,I.owner G=(if ga then 3 else 2) := by
    have ho : I.owner G=2∨I.owner G=3 := by simpa [highGAOwners,G] using I.allowed G
    rcases ho with ho|ho
    · exact ⟨false,ho⟩
    · exact ⟨true,ho⟩
  obtain ⟨ab,hab⟩ : ∃ab : Bool,I.owner A=(if ab then 2 else 0) := by
    have ho : I.owner A=0∨I.owner A=2 := by simpa [highGAOwners,A] using I.allowed A
    rcases ho with ho|ho
    · exact ⟨false,ho⟩
    · exact ⟨true,ho⟩
  have hGA : C.Feasible G (if ga then 3 else 2) := by simpa [hga] using I.feasible G
  have hAB : C.Feasible A (if ab then 2 else 0) := by simpa [hab] using I.feasible A
  obtain ⟨O⟩ := NegativeANormalForm.cycle_reduce ga ab
    (by norm_num [qLow] at hQL ⊢; linarith) hQU I.necessary I.radial I.G_negative.le
    (I.outer B (by simp [H,G,B,D])) I.B_negative.le I.A_upper I.A_nonpos_outer
    I.strict_spread hGA hAB
  have hH := O.point_other H (by norm_num [H,A])
  have hG := O.point_other G (by norm_num [G,A])
  have hB := O.point_other B (by norm_num [B,A])
  have hD := O.point_other D (by norm_num [D,A])
  have hE := O.point_other E (by norm_num [E,A])
  have hδB := O.other_delta B (by norm_num [B,G]) (by norm_num [B,A])
  have hδD := O.other_delta D (by norm_num [D,G]) (by norm_num [D,A])
  have hδE := O.other_delta E (by norm_num [E,G]) (by norm_num [E,A])
  have hHy : 0≤(O.cycle.point H).y := by rw [hH]; exact I.H_positive.le
  have hGy : (O.cycle.point G).y≤0 := by rw [hG]; exact I.G_negative.le
  have hBy : (O.cycle.point B).y≤0 := by rw [hB]; exact I.B_negative.le
  have hDy : (O.cycle.point D).y≤0 := by rw [hD]; exact I.D_negative.le
  have hvar := O.variation.trans I.positive_variation.le
  have hhg : I.owner H=0∨I.owner H=2 := by simpa [highGAOwners,H] using I.allowed H
  have hHG := (O.other_edges H (by norm_num [H,G,A]) (I.owner H)).2 (I.feasible H)
  have hreg' : ERegime O.cycle de eh := by
    simpa only [ERegime,cycleTotal,total,hδD,hδE,hE] using hreg
  exact normal_A_false O.ga O.ab de eh O.necessary hQU (O.radial A)
    hHy hGy hBy hDy hvar O.reduced (by rw [hδB]; exact hz) hreg' hhg hHG O.GA O.AB
    ((O.other_edges B (by norm_num [B,G,A]) 3).2 hBT)
    ((O.other_edges T (by norm_num [T,G,A]) 0).2 hTD)
    ((O.other_edges D (by norm_num [D,G,A]) _).2 hDE)
    ((O.other_edges E (by norm_num [E,G,A]) _).2 hEH)

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Complete
