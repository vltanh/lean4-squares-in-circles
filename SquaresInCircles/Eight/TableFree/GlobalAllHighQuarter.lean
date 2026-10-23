module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighNegativeCore

/-!
# The complete common charge of every original high quarter

Both original high owners, every original error sign, every outer
target, and both positive-core target pieces are covered.  Equality
recovers zero error, the original high marker, and the original tight
axis projection.  No charge bound on another edge is assumed.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh

open FramePair GlobalOuterAnchor

theorem primary_charge (s t : State) (hs : s.branch.type≠0)
    (ht : t.branch.type≠0 ∨ 0<transverse t) {d : ℝ}
    (hd : |d|≤frameCap)
    (hm : width d≤s.a+t.a*Real.sin d-transverse t*Real.cos d) :
    kappa≤quarterCharge s (transverse t) d ∧
      (d≠0 → kappa<quarterCharge s (transverse t) d) := by
  by_cases hd0 : 0≤d
  · have hp := positive_primary_charge s t hs
      ⟨hd0,(le_abs_self d).trans hd⟩ hm
    exact ⟨hp.1,fun hne => hp.2 (lt_of_le_of_ne hd0 (Ne.symm hne))⟩
  · have hz : -d∈Ioc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    have hm' : width (-(-d))≤s.a+t.a*Real.sin (-(-d))-
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
      simpa only [rightOwner,Bool.false_eq_true,if_false] using hm)
    change width d≤s.a*Real.cos d+s.b*Real.sin d-transverse t at hmargin
    exact secondary_charge s hs hd hmargin
  · have hmargin := (right_margin s t true hd hsy).1 (by
      simpa only [rightOwner,if_true] using hm)
    change width d≤s.a+t.a*Real.sin d-transverse t*Real.cos d at hmargin
    exact primary_charge s t hs ht hd hmargin

theorem quarter_zero_equality (s : State) (hs : s.branch.type≠0) {Y : ℝ}
    (hm : 1≤s.a-Y) :
    quarterCharge s Y 0=kappa ↔ s.branch=.high ∧ s.a-Y=1 := by
  have hJ := J_nonnegative s hs
  constructor
  · intro he
    have hJzero : J s=0 := by
      dsimp [quarterCharge,potential,kappa,rho] at he
      linarith
    refine ⟨(J_eq_zero_iff s hs).1 hJzero,?_⟩
    dsimp [quarterCharge,potential,kappa,rho] at he
    rw [hJzero] at he
    linarith
  · rintro ⟨hhigh,hprojection⟩
    rw [quarterCharge,potential,J_high s hhigh]
    dsimp [kappa,rho]
    linarith

/-- Equality recovers the actual marker and the tight original axis;
it never changes a marker choice at a weak chart junction. -/
theorem high_quarter_equality (s t : State) (hs : s.branch.type≠0)
    (hsy : transverse s≤0) (ht : t.branch.type≠0 ∨ 0<transverse t)
    {j : Fin 4} {d : ℝ} (hj : j=2 ∨ j=3) (hd : |d|≤frameCap)
    (hm : s.Feasible t j (Real.pi/2+d)) :
    quarterCharge s (transverse t) d=kappa ↔
      d=0 ∧ s.branch=.high ∧ s.a-transverse t=1 := by
  have hc := high_quarter_charge s t hs hsy ht hj hd hm
  constructor
  · intro he
    have hd0 : d=0 := by
      by_contra hn
      linarith [hc.2 hn]
    subst d
    have hp : 1≤s.a-transverse t := by
      rcases hj with rfl | rfl
      · have hh := (right_margin s t false hd hsy).1 (by
          simpa only [rightOwner,Bool.false_eq_true,if_false] using hm)
        simpa [rightProjection,width] using hh
      · have hh := (right_margin s t true hd hsy).1 (by
          simpa only [rightOwner,if_true] using hm)
        simpa [rightProjection,width] using hh
    exact ⟨rfl,(quarter_zero_equality s hs hp).1 he⟩
  · rintro ⟨rfl,hhigh,hprojection⟩
    exact (quarter_zero_equality s hs hprojection.ge).2 ⟨hhigh,hprojection⟩

end SquaresInCircles.Eight.TableFree.GlobalAllHigh
