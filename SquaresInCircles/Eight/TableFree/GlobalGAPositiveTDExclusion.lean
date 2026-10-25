module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDLowTransfer
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDUpperTransfer

/-!
# The original high-GA secondary-owner row for both TD witnesses

Uncompiled source.  The explicit continuous weight families give strict
positivity for every intrinsic concentration alternative over the whole
positive TD interval.  Joining the original nonpositive-TD and TD0
arguments excludes both weak TD witnesses without a frame-order premise.
Every point, radius, signed error, and separator in the conclusion is
the original one.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD
open Candidate Secondary Certificate

/-- The stress coefficients are constructed from the actual TD error.
There are no scalar inequalities left as hypotheses. -/
theorem explicit_positive_weights {z : ℝ} (hz : z∈Icc 0 frameCap) :
    ∃ k l c : ℝ,k∈Icc (1/2:ℝ) (17/20) ∧ l∈Icc k (2*k) ∧ c∈Icc k 2 ∧
      (l≤2*tilted c z ∧ tilted c z≤2*l) ∧
      ∀ i j : Fin 4,0<baseline k l c z+endpoint k l c z i j := by
  by_cases hlo : z≤1/6
  · have hzlo : z∈Icc 0 (1/6:ℝ) := ⟨hz.1,hlo⟩
    have hd := Explicit.low_domain hzlo
    exact ⟨Explicit.lowK z,Explicit.lowL z,Explicit.lowC z,
      hd.1,hd.2.1,hd.2.2.1,hd.2.2.2,low_endpoint_positive hzlo⟩
  · by_cases hclamp : z≤37/80
    · have hzupper : z∈Icc (Explicit.left .varying:ℝ) (Explicit.right .varying:ℝ) := by
        norm_num [Explicit.left,Explicit.right]
        exact ⟨le_of_lt (lt_of_not_ge hlo),hclamp⟩
      have hd := Explicit.upper_domain .varying hzupper
      exact ⟨Explicit.upperK .varying z,1,Explicit.upperC .varying z,
        hd.1,hd.2.1,hd.2.2.1,by rw [mul_one]; exact hd.2.2.2,upper_endpoint_positive .varying hzupper⟩
    · have hzupper : z∈Icc (Explicit.left .clamped:ℝ) (Explicit.right .clamped:ℝ) := by
        norm_num [Explicit.left,Explicit.right]
        exact ⟨le_of_lt (lt_of_not_ge hclamp),by simpa [frameCap] using hz.2⟩
      have hd := Explicit.upper_domain .clamped hzupper
      exact ⟨Explicit.upperK .clamped z,1,Explicit.upperC .clamped z,
        hd.1,hd.2.1,hd.2.2.1,by rw [mul_one]; exact hd.2.2.2,upper_endpoint_positive .clamped hzupper⟩

theorem actual_nonnegative_TD_false {q : ℝ} {C : SignedCycle} {hg : Fin 4}
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta T)
    (hhg : hg=0 ∨ hg=2)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G 2)
    (hAB : C.Feasible A 0) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) : False := by
  have hz' := (original_budgets hg 1 1 1 hvar hz).1
  obtain ⟨k,l,c,hk,hl,hcoef,hratio,hpositive⟩ := explicit_positive_weights hz'
  obtain ⟨i,j,hnecessary⟩ := original_concentration hs hc hq hHy hGy hBy hDy hvar hz hhg
    hHG hGA hAB hBT hTD hDE hEH hk hl hcoef hratio
  exact (not_lt_of_ge hnecessary) (hpositive i j)

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD

namespace SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
open Candidate

/-- The high-GA secondary A/E row excludes TD2 for every original signed
TD error.  A, T, and E are allowed either transverse sign. -/
theorem actual_TD2_false {q : ℝ} {C : SignedCycle}
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained q)
    (hcoreT : (C.point T).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G 2) (hAB : C.Feasible A 0) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) : False := by
  have hz := actual_TD2_positive hs hc hcoreT hq hHy hGy hBy hDy hvar
    hHG hGA hAB hBT hTD hDE hEH
  rcases hHG with hHG | hHG
  · exact PositiveTD.actual_nonnegative_TD_false hs hc hq hHy hGy hBy hDy hvar hz.le
      (Or.inl rfl) hHG hGA hAB hBT hTD hDE hEH
  · exact PositiveTD.actual_nonnegative_TD_false hs hc hq hHy hGy hBy hDy hvar hz.le
      (Or.inr rfl) hHG hGA hAB hBT hTD hDE hEH

/-- Both original weak TD owners are excluded in one full-variation
statement.  No aligned proxy replaces either TD separator. -/
theorem actual_secondary_either_TD_false {q : ℝ} {C : SignedCycle}
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained q)
    (hcoreT : (C.point T).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G 2) (hAB : C.Feasible A 0) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 0 ∨ C.Feasible T 2)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) : False := by
  rcases hTD with hTD | hTD
  · exact actual_secondary_owner_false hs hc hq hHy hGy hBy hDy hvar
      hHG hGA hAB hBT hTD hDE hEH
  · exact actual_TD2_false hs hc hcoreT hq hHy hGy hBy hDy hvar
      hHG hGA hAB hBT hTD hDE hEH

end SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
