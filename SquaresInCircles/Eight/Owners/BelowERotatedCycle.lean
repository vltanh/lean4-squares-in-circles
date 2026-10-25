module

public import SquaresInCircles.Eight.Owners.Nonpositive.EReplacement

/-!
# Eight squares: inserting E along a rotated DE2 contact

`HardInput.fromBelowERotated` replaces E by a sorted point `p` in the circle, off the core, with
`p.y ≤ 0` and frame `θ` between the frames of E and D, when DE has the rotated owner `2` and EH
the primary owner `1` at `p`. The other owners stay (`Witnesses.belowERotated`), and the radial
alternative of E is the coordinate inequality `max |H.y| |D.y| ≤ p.a`. This is the DE2
counterpart of the primary outside-E insertion.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCycle
open Candidate

theorem belowEPrimaryCycle_DE2 (C : SignedCycle) (p : SignedPoint) (θ : ℝ) :
    (belowEPrimaryCycle C p θ).Feasible D 2 ↔
      quarterFeasible (C.point D) p (θ-C.theta D) 2 := by
  simp [belowEPrimaryCycle,replacePoint,Feasible,slack,edge,word,delta,next,D,E,
    quarterFeasible,sub_nonneg]

def Witnesses.belowERotated {C : SignedCycle} (w : C.Witnesses)
    {p : SignedPoint} {θ : ℝ}
    (hDE : quarterFeasible (C.point D) p (θ-C.theta D) 2)
    (hEH : quarterFeasible p (C.point H) (C.theta H-θ) 1) :
    (belowEPrimaryCycle C p θ).Witnesses where
  owner i := if i=D then 2 else if i=E then 1 else w.owner i
  feasible := by
    intro i
    by_cases hiD : i=D
    · subst i
      simpa [D,E] using (belowEPrimaryCycle_DE2 C p θ).2 hDE
    by_cases hiE : i=E
    · subst i
      simpa [D,E] using (belowEPrimaryCycle_EH C p θ).2 hEH
    have hn : next i≠E := by
      have key : ∀ j : Vertex, j≠D → next j≠E := by decide
      exact key i hiD
    simpa [hiD,hiE,belowEPrimaryCycle] using
      (replacePoint_other_feasible (p := p) (t := θ) hiE hn).2 (w.feasible i)
  allowed := by
    intro i
    by_cases hiD : i=D
    · subst i; norm_num [normalOwners,D,E]
    by_cases hiE : i=E
    · subst i; norm_num [normalOwners,D,E]
    · simpa [hiD,hiE] using w.allowed i

def HardInput.fromBelowERotated {q : ℝ} (I : HardInput q)
    {p : SignedPoint} {θ : ℝ}
    (hs : p.Sorted) (hc : p.Contained q) (hcore : p.AvoidsCore) (hy : p.y≤0)
    (hrad : max |(I.cycle.point H).y| |(I.cycle.point D).y|≤p.a)
    (hθ : θ∈Icc (I.cycle.theta E) (I.cycle.theta D))
    (hDE : quarterFeasible (I.cycle.point D) p (θ-I.cycle.theta D) 2)
    (hEH : quarterFeasible p (I.cycle.point H) (I.cycle.theta H-θ) 1) : HardInput q where
  cycle := belowEPrimaryCycle I.cycle p θ
  necessary := by
    apply necessary_replace_clamped (v := E) (a := E) (b := D)
      I.necessary hs hc hcore
    right
    rw [min_eq_left (hθ.1.trans hθ.2),max_eq_right (hθ.1.trans hθ.2)]
    exact hθ
  anchors_normal := {
    H_nonneg := by simpa [belowEPrimaryCycle,replacePoint,H,E] using I.anchors_normal.H_nonneg
    A_nonneg := by simpa [belowEPrimaryCycle,replacePoint,A,E] using I.anchors_normal.A_nonneg
    B_nonpos := by simpa [belowEPrimaryCycle,replacePoint,B,E] using I.anchors_normal.B_nonpos
    D_nonpos := by simpa [belowEPrimaryCycle,replacePoint,D,E] using I.anchors_normal.D_nonpos }
  E_nonpos := by simpa [belowEPrimaryCycle,replacePoint] using hy
  witnesses := I.witnesses.belowERotated hDE hEH
  GA_hard := (replacePoint_other_feasible (v := E) (by decide : G≠E)
    (by decide : next G≠E)).2 I.GA_hard
  BT_hard := (replacePoint_other_feasible (v := E) (by decide : B≠E)
    (by decide : next B≠E)).2 I.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hj
      have hh : I.witnesses.owner H=2 := by
        simpa [Witnesses.belowERotated,H,D,E] using hj
      simpa [belowEPrimaryCycle,replacePoint,G,E] using I.zero_signs.HG_canceling hh
    TD_canceling := by
      intro hj
      have hh : I.witnesses.owner T=0 := by
        simpa [Witnesses.belowERotated,T,D,E] using hj
      simpa [belowEPrimaryCycle,replacePoint,T,E] using I.zero_signs.TD_canceling hh }
  E_radial := by
    right
    simpa [belowEPrimaryCycle,replacePoint,H,D,E] using hrad

end SquaresInCircles.Eight.SignedCycle
