module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativePrimaryReserve

/-!
# All simultaneous nonpositive intermediate primary owners are excluded

GA3, AB2 and TD2 may occur together, including weak zero-error ties.
The other permitted owner on each edge retains its arbitrary signed
error.  A, T and E keep their original transverse signs and radial
kinds.  The theorem uses the actual weak inequalities and the full
signed variation budget.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativePrimary

open Candidate Secondary

theorem gains_nonneg {q : ℝ} {C : SignedCycle} (ga ab td : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcore : ∀i,(C.point i).AvoidsCore) (hq : q≤qCap)
    (hsmall : ∀i,|delta C.theta i|≤frameCap)
    (hga : ga=true → delta C.theta G≤0)
    (hab : ab=true → delta C.theta A≤0)
    (htd : td=true → delta C.theta T≤0) : 0≤gains ga ab td C := by
  have hA := SignedPoint.coordinate_bounds (hs A) (hcore A) (hc A) hq
  have hG := SignedPoint.coordinate_bounds (hs G) (hcore G) (hc G) hq
  have hB := SignedPoint.coordinate_bounds (hs B) (hcore B) (hc B) hq
  have hBupper : -(C.point B).y≤283/200 := by
    have hh := neg_le_abs (C.point B).y
    linarith [hB.2.2]
  have hgainG : 0≤
      (if ga then primaryIncrement (delta C.theta G) (C.point A).a (C.point G).a else 0) := by
    cases hh : ga
    · simp
    · exact gain_nonneg (hga hh) (hsmall G) hA.1.le hG.2.1.le
  have hgainA : 0≤
      (if ab then primaryIncrement (delta C.theta A) (C.point A).a (-(C.point B).y) else 0) := by
    cases hh : ab
    · simp
    · exact gain_nonneg (hab hh) (hsmall A) hA.1.le hBupper
  have hgainT : 0≤(if td then tdIncrement (delta C.theta T) (C.point T) else 0) := by
    cases hh : td
    · simp
    · exact nonpositive_td_gain (hs T) (hcore T) (htd hh) (hsmall T)
  unfold gains
  linarith

/-- Complete fixed-stress family, with the three alternative owner
flags independent.  No zero-error physical separator is assumed. -/
theorem actual_false {q : ℝ} {C : SignedCycle} (ga ab td : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcore : ∀i,(C.point i).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T (if td then 2 else 0))
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0)
    (hga : ga=true → delta C.theta G≤0)
    (hab : ab=true → delta C.theta A≤0)
    (htd : td=true → delta C.theta T≤0) : False := by
  have hn : negativeVariation C.theta≤frameCap := by
    rw [← variations_equal]
    exact hvar
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hGcos := ne_of_gt (cos_pos (hsmall G))
  have hAcos := ne_of_gt (cos_pos (hsmall A))
  have hgain := gains_nonneg ga ab td hs hc hcore hq hsmall hga hab htd
  have hf (hg : Fin 4) (hhg : C.Feasible H hg) :
      ∀i,C.Feasible i (owners hg ga ab td i) := by
    intro i
    fin_cases i
    · simpa [owners,H] using hhg
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  rcases hHG with hHG | hHG
  · have hu := stress_nonpos hsmall (hf 0 hHG)
    have hl := zero_reference_reserve ga ab td hs hc hq hHy hGy hBy hDy hvar
    rw [zero_decomposition ga ab td C hGcos hAcos] at hu
    linarith
  · have hu := stress_nonpos hsmall (hf 2 hHG)
    have hl := two_reference_reserve ga ab td hs hc hq hHy hGy hBy hDy hvar
    rw [two_decomposition ga ab td C hGcos hAcos] at hu
    linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativePrimary
