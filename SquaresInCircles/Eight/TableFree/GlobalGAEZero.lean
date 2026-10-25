module

public import SquaresInCircles.Eight.TableFree.BoundaryRealization
public import SquaresInCircles.Eight.TableFree.GlobalBTExclusion
public import SquaresInCircles.Eight.TableFree.GlobalGASourceDomain

/-!+# The zero-E boundary is impossible in the actual high-GA domain

Uncompiled transcription of the boundary-neighbor transport hand proof.
Reflection and reversal send each original high GA separator to an actual
low BT separator.  At E=0 the reflected E chart is still nonpositive, so
the already proved complete BT exclusion applies to a realization of the
same signed boundary-neighbor system.  No nonneighbor separator and no
normal-source owner assumption is introduced.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA
open Candidate SignedCycle

/-- This statement applies to actual transported boundary neighbors as
well as to the original cycle.  The reflected A frame is identically zero,
so realization preserves the reflected real frames exactly. -/
theorem zero_E_false {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (ho : C.Ordered) (hs : C.StrictSpread)
    (hr : ∀i,(C.point i).Boundary q)
    (owner : Vertex → Fin 4) (hf : ∀i,C.Feasible i (owner i))
    (hq : q∈Icc (5/2:ℝ) Q0) (hE : (C.point E).y=0)
    (j : Fin 4) (hj : j=2 ∨ j=3) (hGA : C.Feasible G j) : False := by
  let owner' : Vertex → Fin 4 := fun i => reflectedOwner (owner (reflectedIndex (next i)))
  have hf' (i : Vertex) : C.reflected.Feasible i (owner' i) :=
    (reflected_feasible C i _).2 (hf _)
  have hr' (i : Vertex) : (C.reflected.point i).Boundary q := by
    simpa [reflected] using hr (reflectedIndex i)
  have hs' : C.reflected.StrictSpread := by
    intro i k
    have hh := hs (reflectedIndex k) (reflectedIndex i)
    simpa [reflected,show C.theta B-C.theta (reflectedIndex i)-
      (C.theta B-C.theta (reflectedIndex k))=
      C.theta (reflectedIndex k)-C.theta (reflectedIndex i) by ring] using hh
  have hA' : C.reflected.theta A=0 := by simp [reflected,reflectedIndex,A,B]
  let K := C.reflected.realizeBoundary hn.reflected ho.reflected hr' owner' hf'
  let F : Candidate.Frame K := C.reflected.realizedFrame hn.reflected ho.reflected
    hr' owner' hf' hq.2 hs' hA'
  have hE6 : (C.point 6).y=0 := hE
  have hE' : K.tangent E≤0 := by
    simp [K,BoundaryCycle.tangent,realizeBoundary,reflected,reflectedIndex,E,
      SignedPoint.reflect,hE6]
  have hBT : C.reflected.Feasible B (reflectedOwner j) := by
    have hh := (reflected_feasible C B j).2
      (by simpa [reflectedIndex,next,B,T,G] using hGA)
    exact hh
  have hBT' : (forwardAxis (reflectedOwner j)).Feasible (K.square B) (K.square T) := by
    have hh := (C.reflected.realizeBoundary_feasible_iff hn.reflected ho.reflected
      hr' owner' hf' B (reflectedOwner j)).2 hBT
    simpa [K,next,B,T] using hh
  have hclass := GlobalBT.frame_BT_high F hq hE' (reflectedOwner j) hBT'
  rcases hj with rfl | rfl <;> norm_num [reflectedOwner] at hclass

theorem SourceDomain.E_negative {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hq : q∈Icc (5/2:ℝ) Q0) : (C.point E).y<0 := by
  apply lt_of_le_of_ne I.E_nonpos
  intro he
  have hj : I.owner G=2 ∨ I.owner G=3 := by
    simpa [highGAOwners,G] using I.allowed G
  exact zero_E_false I.necessary I.ordered I.strict_spread I.radial I.owner I.feasible
    hq he (I.owner G) hj (I.feasible G)

end SquaresInCircles.Eight.TableFree.GlobalGA
