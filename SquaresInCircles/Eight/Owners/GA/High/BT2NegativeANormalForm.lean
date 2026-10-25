module

public import SquaresInCircles.Eight.Owners.GA.High.BT2NonnegativeTotals
public import SquaresInCircles.Eight.Owners.GA.Negative.ACycle

/-!
# Eight squares: the normalization of the A primaries in a high-GA source domain

`A_normalize` is the only move of A in the negative-A BT2 case. At the radius of the source
domain, `NegativeANormalForm.cycle_reduce` gives either a nonnegative selected A total or one
negative primary on a flat-core A with positive `y`. A itself moves, so the result is a signed
cycle that satisfies the necessary conditions; it need not be a packing, be ordered or be a source
domain. Every other square and the five witnesses on the edges away from A are unchanged.

The BT2, TD, HG, DE and EH witnesses of the source domain stay feasible (`ATransport`), by the
equivalences on the unchanged edges, and so do the T, D and E errors and the points of E, H, G, B
and D.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle

variable {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C)

include I in
theorem A_normalize (hqL : qLow≤q) (hqU : q≤qCap) :
    Nonempty (GlobalGA.NegativeANormalForm.CycleResult q C) := by
  have hQL : (5/2:ℝ)≤q := by
    have hlow : (5/2:ℝ)≤qLow := by norm_num [qLow]
    exact hlow.trans hqL
  have hGA : C.Feasible G (if gaFlag I then 3 else 2) := by
    rw [←ga_owner I]
    exact I.feasible G
  have hAB : C.Feasible A (if abFlag I then 2 else 0) := by
    rw [←ab_owner I]
    exact I.feasible A
  exact GlobalGA.NegativeANormalForm.cycle_reduce
    (gaFlag I) (abFlag I) hQL hqU I.necessary I.radial
    I.G_negative.le (I.outer B (by simp [H,G,B,D]))
    I.B_negative.le I.A_upper I.A_nonpos_outer I.strict_spread hGA hAB

namespace ATransport
open GlobalGA.NegativeANormalForm
variable {q : ℝ} {C : SignedCycle} (O : CycleResult q C)

/-- A BT2 witness stays feasible when A moves. -/
theorem BT2 (hBT : C.Feasible B 2) : O.cycle.Feasible B 2 :=
  (O.other_edges B (by norm_num [B,G,A]) 2).2 hBT

/-- A TD witness stays feasible when A moves. -/
theorem TD (j : Fin 4) (hTD : C.Feasible T j) : O.cycle.Feasible T j :=
  (O.other_edges T (by norm_num [T,G,A]) j).2 hTD

theorem HG (j : Fin 4) (hHG : C.Feasible H j) : O.cycle.Feasible H j :=
  (O.other_edges H (by norm_num [H,G,A]) j).2 hHG

theorem DE (j : Fin 4) (hDE : C.Feasible D j) : O.cycle.Feasible D j :=
  (O.other_edges D (by norm_num [D,G,A]) j).2 hDE

theorem EH (j : Fin 4) (hEH : C.Feasible E j) : O.cycle.Feasible E j :=
  (O.other_edges E (by norm_num [E,G,A]) j).2 hEH

theorem original_T_error :
    delta O.cycle.theta T=delta C.theta T := by
  have h4 : O.cycle.theta 4=C.theta 4 := O.theta_other T (by decide)
  have h5 : O.cycle.theta 5=C.theta 5 := O.theta_other D (by decide)
  simp [delta,next,T,h4,h5]

theorem original_D_error :
    delta O.cycle.theta D=delta C.theta D := by
  have h5 : O.cycle.theta 5=C.theta 5 := O.theta_other D (by decide)
  have h6 : O.cycle.theta 6=C.theta 6 := O.theta_other E (by decide)
  simp [delta,next,D,h5,h6]

theorem original_E_error :
    delta O.cycle.theta E=delta C.theta E := by
  have h6 : O.cycle.theta 6=C.theta 6 := O.theta_other E (by decide)
  have h0 : O.cycle.theta 0=C.theta 0 := O.theta_other H (by decide)
  simp [delta,next,E,h6,h0]

theorem E_point : O.cycle.point E=C.point E :=
  O.point_other E (by norm_num [E,A])

theorem H_point : O.cycle.point H=C.point H :=
  O.point_other H (by norm_num [H,A])

theorem G_point : O.cycle.point G=C.point G :=
  O.point_other G (by norm_num [G,A])

theorem B_point : O.cycle.point B=C.point B :=
  O.point_other B (by norm_num [B,A])

theorem D_point : O.cycle.point D=C.point D :=
  O.point_other D (by norm_num [D,A])

end ATransport
end SquaresInCircles.Eight.HighGABT2
