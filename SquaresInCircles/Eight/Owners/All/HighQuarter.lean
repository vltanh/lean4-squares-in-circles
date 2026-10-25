module

public import SquaresInCircles.Eight.Owners.All.HighNegativeCore
public import SquaresInCircles.Eight.Owners.All.HighNegativeOuter
public import SquaresInCircles.Eight.Owners.All.HighPositiveTransfer

/-!
# Eight squares: the complete common charge of every original high quarter

Both original high owners, every original error sign, every outer
target, and both positive-core target pieces are covered.  Equality
recovers zero error, the original high marker, and the original tight
axis projection.  No charge bound on another edge is assumed.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh

open FramePair GlobalOuterAnchor

theorem primary_charge (s t : State) (hs : s.branch.type≠0)
    (ht : t.branch.type≠0 ∨ 0<transverse t) {d : ℝ}
    (hd : |d|≤frameCap)
    (hm : GlobalOuterAnchor.width d≤ s.a+t.a*Real.sin d-transverse t*Real.cos d) :
    kappa≤quarterCharge s (transverse t) d ∧
      (d≠0 → kappa<quarterCharge s (transverse t) d) := by
  by_cases hd0 : 0≤d
  · have hp := positive_primary_charge s t hs
      ⟨hd0,(le_abs_self d).trans hd⟩ hm
    exact ⟨hp.1,fun hne => hp.2 (lt_of_le_of_ne hd0 (Ne.symm hne))⟩
  · have hz : -d∈Ioc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    have hm' : GlobalOuterAnchor.width (-(-d))≤ s.a+t.a*Real.sin (-(-d))-
        transverse t*Real.cos (-(-d)) := by simpa only [neg_neg] using hm
    have hstrict : kappa<quarterCharge s (transverse t) d := by
      by_cases htCore : t.branch.type=0
      · have htpos : 0<transverse t := ht.resolve_left (fun hne => hne htCore)
        simpa only [neg_neg] using negative_primary_core s t hs htCore htpos hz hm'
      · simpa only [neg_neg] using negative_primary_outer s t hs htCore hz hm'
    exact ⟨hstrict.le,fun _ => hstrict⟩

/-- A high original owner has the common augmented primary charge.
The target disjunction is exactly what the all-high radial classifier
provides at H, A, and T. -/
theorem high_quarter_charge (s t : State) (hs : s.branch.type≠0)
    (hsy : transverse s≤0) (ht : t.branch.type≠0 ∨ 0<transverse t)
    {j : Fin 4} {d : ℝ} (hj : j=2 ∨ j=3) (hd : |d|≤frameCap)
    (hm : s.Feasible t j (Real.pi/2+d)) :
    kappa≤quarterCharge s (transverse t) d ∧
      (d≠0 → kappa<quarterCharge s (transverse t) d) := by
  rcases hj with rfl | rfl
  · have hmargin := (right_margin s t false hd hsy).1 (by
      simpa only [rightOwner,Bool.false_eq_true,ite_false] using hm)
    change GlobalOuterAnchor.width d≤ s.a*Real.cos d+s.b*Real.sin d-transverse t at hmargin
    exact secondary_charge s hs hd hmargin
  · have hmargin := (right_margin s t true hd hsy).1 (by
      simpa only [rightOwner,ite_true] using hm)
    change GlobalOuterAnchor.width d≤ s.a+t.a*Real.sin d-transverse t*Real.cos d at hmargin
    exact primary_charge s t hs ht hd hmargin

end SquaresInCircles.Eight.GlobalAllHigh
