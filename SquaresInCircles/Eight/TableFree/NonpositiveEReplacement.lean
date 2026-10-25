module

public import SquaresInCircles.Eight.TableFree.HardZeroEReflection
public import SquaresInCircles.Eight.TableFree.PairTransportAssembly

/-!
# Actual primary E replacements between its original frame and D

Uncompiled reconstruction.  The supplied point has its own proved
geometry and the two actual primary projections.  Its frame stays on
the original E--D interval; the other six points, frames, and five
unaffected selected owners remain literal.  No radial label is inferred
from a changed circle ceiling.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SignedCycle
open Candidate

def belowEPrimaryCycle (C : SignedCycle) (p : SignedPoint) (θ : ℝ) : SignedCycle :=
  replacePoint C E p θ

theorem belowEPrimaryCycle_unchanged (C : SignedCycle) (p : SignedPoint) (θ : ℝ)
    (i : Vertex) (hi : i≠E) :
    (belowEPrimaryCycle C p θ).point i=C.point i ∧
      (belowEPrimaryCycle C p θ).theta i=C.theta i := by
  simp [belowEPrimaryCycle,replacePoint,hi]

theorem belowEPrimaryCycle_DE (C : SignedCycle) (p : SignedPoint) (θ : ℝ) :
    (belowEPrimaryCycle C p θ).Feasible D 3 ↔
      quarterFeasible (C.point D) p (θ-C.theta D) 3 := by
  simp [belowEPrimaryCycle,replacePoint,Feasible,slack,edge,word,delta,next,D,E,
    quarterFeasible,sub_nonneg]

theorem belowEPrimaryCycle_EH (C : SignedCycle) (p : SignedPoint) (θ : ℝ) :
    (belowEPrimaryCycle C p θ).Feasible E 1 ↔
      quarterFeasible p (C.point H) (C.theta H-θ) 1 := by
  simp [belowEPrimaryCycle,replacePoint,Feasible,slack,edge,word,delta,next,E,H,
    quarterFeasible,sub_nonneg]

def Witnesses.belowEPrimary {C : SignedCycle} (w : C.Witnesses)
    {p : SignedPoint} {θ : ℝ}
    (hDE : quarterFeasible (C.point D) p (θ-C.theta D) 3)
    (hEH : quarterFeasible p (C.point H) (C.theta H-θ) 1) :
    (belowEPrimaryCycle C p θ).Witnesses where
  owner i := if i=D then 3 else if i=E then 1 else w.owner i
  feasible := by
    intro i
    by_cases hiD : i=D
    · subst i
      simpa [D,E] using (belowEPrimaryCycle_DE C p θ).2 hDE
    by_cases hiE : i=E
    · subst i
      simpa [D,E] using (belowEPrimaryCycle_EH C p θ).2 hEH
    have hn : next i≠E := by revert i; decide
    simpa [hiD,hiE,belowEPrimaryCycle] using
      (replacePoint_other_feasible (p := p) (t := θ) hiE hn).2 (w.feasible i)
  allowed := by
    intro i
    by_cases hiD : i=D
    · subst i; norm_num [normalOwners,D,E]
    by_cases hiE : i=E
    · subst i; norm_num [normalOwners,D,E]
    · simpa [hiD,hiE] using w.allowed i

def HardInput.fromBelowEPrimary {q : ℝ} (I : HardInput q)
    {p : SignedPoint} {θ : ℝ}
    (hs : p.Sorted) (hc : p.Contained q) (hcore : p.AvoidsCore) (hy : p.y≤0)
    (hrad : max |(I.cycle.point H).y| |(I.cycle.point D).y|≤p.a)
    (hθ : θ∈Icc (I.cycle.theta E) (I.cycle.theta D))
    (hDE : quarterFeasible (I.cycle.point D) p (θ-I.cycle.theta D) 3)
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
  witnesses := I.witnesses.belowEPrimary hDE hEH
  GA_hard := (replacePoint_other_feasible (v := E) (by decide : G≠E)
    (by decide : next G≠E)).2 I.GA_hard
  BT_hard := (replacePoint_other_feasible (v := E) (by decide : B≠E)
    (by decide : next B≠E)).2 I.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hj
      have hh : I.witnesses.owner H=2 := by
        simpa [Witnesses.belowEPrimary,H,D,E] using hj
      simpa [belowEPrimaryCycle,replacePoint,G,E] using I.zero_signs.HG_canceling hh
    TD_canceling := by
      intro hj
      have hh : I.witnesses.owner T=0 := by
        simpa [Witnesses.belowEPrimary,T,D,E] using hj
      simpa [belowEPrimaryCycle,replacePoint,T,E] using I.zero_signs.TD_canceling hh }
  E_radial := by
    right
    simpa [belowEPrimaryCycle,replacePoint,H,D,E] using hrad

theorem belowEPrimaryCycle_anchor_nonincrease {C : SignedCycle} {p : SignedPoint} {θ : ℝ}
    (hp : p.circle≤(C.point E).circle) : AnchorNonincrease C (belowEPrimaryCycle C p θ) := by
  intro i hi
  by_cases hiE : i=E
  · subst i; simpa [belowEPrimaryCycle,replacePoint] using hp
  · rw [(belowEPrimaryCycle_unchanged C p θ i hiE).1]

theorem belowEPrimaryCycle_strict_loss {C : SignedCycle} {p : SignedPoint} {θ : ℝ}
    (hp : p.circle<(C.point E).circle) : StrictAnchorLoss C (belowEPrimaryCycle C p θ) := by
  refine ⟨E,by norm_num [anchorVertices,E],?_⟩
  simpa [belowEPrimaryCycle,replacePoint] using hp

end SquaresInCircles.Eight.TableFree.SignedCycle
