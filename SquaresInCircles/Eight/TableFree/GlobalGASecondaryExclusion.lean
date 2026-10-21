module

public import SquaresInCircles.Eight.TableFree.GlobalGASecondaryStress

/-!
# Full-variation exclusion of the actual secondary-owner high-GA chain

Uncompiled source.  This is the original seven-point theorem for the owner
tuple HG0/2, GA2, AB0, BT2, TD0, DE2, EH0.  It uses the complete signed
variation bound and all original weak separators.  Containment suffices;
no point is expanded to a circle, and no boundary owner is replaced.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
open Candidate

theorem zero_stress_reserve {q : ℝ} {C : SignedCycle}
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) :
    (7/10000:ℝ)<actualSecondaryStress 0 C := by
  have hn : negativeVariation C.theta≤frameCap := by
    rw [← variations_equal]
    exact hvar
  have hH := actual_H_one (x:=delta C.theta E) hHy (hc H) hq
    (original_error_bound hvar hn E)
  have hgb := original_pair_budgets (i:=H) (j:=G) hvar hn (by norm_num [H,G])
  have hG := actual_G_pair (P:=(C.point G).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
    (by simpa using hc G) hq hgb.1 hgb.2
  have hbb := original_pair_budgets (i:=A) (j:=B) hvar hn (by norm_num [A,B])
  have hB := actual_B_pair (P:=(C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    (by simpa using hc B) hq hbb.1 hbb.2
  have hdb := original_pair_budgets (i:=T) (j:=D) hvar hn (by norm_num [T,D])
  have hde := pair_error_bounds hdb.1 hdb.2
  have hD := actual_dIncrement_nonneg (P:=(C.point D).reflect)
    (z:=delta C.theta T) (d:=delta C.theta D)
    (by simpa using hs D)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa using hc D) hq hde.1 hde.2.1 hde.2.2
  rw [zero_stress_decomposition]
  linarith [baseStress_reserve]

theorem two_stress_reserve {q : ℝ} {C : SignedCycle}
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) :
    (561/10000:ℝ)<actualSecondaryStress 2 C := by
  have hn : negativeVariation C.theta≤frameCap := by
    rw [← variations_equal]
    exact hvar
  have hhb := original_pair_budgets (i:=H) (j:=E) hvar hn (by norm_num [H,E])
  have hH := actual_H_pair hHy (hc H) hq hhb.1 hhb.2
  have hG := actual_G_one (P:=(C.point G).reflect) (x:=delta C.theta G)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
    (by simpa using hc G) hq (original_error_bound hvar hn G)
  have hbb := original_pair_budgets (i:=A) (j:=B) hvar hn (by norm_num [A,B])
  have hB := actual_B_pair (P:=(C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    (by simpa using hc B) hq hbb.1 hbb.2
  have hdb := original_pair_budgets (i:=T) (j:=D) hvar hn (by norm_num [T,D])
  have hde := pair_error_bounds hdb.1 hdb.2
  have hD := actual_dIncrement_nonneg (P:=(C.point D).reflect)
    (z:=delta C.theta T) (d:=delta C.theta D)
    (by simpa using hs D)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa using hc D) hq hde.1 hde.2.1 hde.2.2
  rw [two_stress_decomposition]
  linarith [baseStress_reserve]

/-- A full-variation obstruction on the unchanged necessary cycle.
The HG disjunction consists of the two actual weak axes; ties are allowed. -/
theorem actual_secondary_owner_false {q : ℝ} {C : SignedCycle}
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G 2) (hAB : C.Feasible A 0) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 0) (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) : False := by
  rcases hHG with hHG | hHG
  · have hupper := secondary_stress_nonpos hHG hGA hAB hBT hTD hDE hEH
    have hlower := zero_stress_reserve hs hc hq hHy hGy hBy hDy hvar
    linarith
  · have hupper := secondary_stress_nonpos hHG hGA hAB hBT hTD hDE hEH
    have hlower := two_stress_reserve hs hc hq hHy hGy hBy hDy hvar
    linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
