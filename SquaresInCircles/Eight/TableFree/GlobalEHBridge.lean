module

public import SquaresInCircles.Eight.TableFree.GlobalEHCycle

/-!
# Original signed-source adapters for the conditional EH restriction

A single actual low GA witness excludes each original high EH witness,
including a high member of a weak tie.  The realization is used only to
transport the original axes into the physical boundary-cycle theorem;
neither witness is replaced by a certificate axis.  No other quarter
owner, endpoint sign, radial kind or frame order is assumed. Uncompiled
source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SignedCycle

open Candidate

theorem high_EH_low_GA_false {q : ℝ} (C : SignedCycle)
    (hq : q∈Icc (5/2:ℝ) qCap) (hn : C.Necessary q) (ho : C.Ordered)
    (hs : C.StrictSpread) (hr : ∀i,(C.point i).Boundary q)
    (owner : Vertex→Fin 4) (hf : ∀i,C.Feasible i (owner i))
    (jE jG : Fin 4) (hEowner : jE=2 ∨ jE=3) (hGowner : jG=0 ∨ jG=1)
    (hEH : C.Feasible E jE) (hGA : C.Feasible G jG) : False := by
  let K := C.realizeBoundary hn ho hr owner hf
  obtain ⟨F,hFtheta,hFquarter⟩ := EDiagonalExclusion.offsetLift_exists K C.theta
    (by simpa only [StrictSpread,frameCap] using hs)
    (by
      intro k
      change (C.realizeBoundary hn ho hr owner hf).canonicalAngle k=_
      simpa only [actualAngle,mul_div_assoc] using
        C.realizeBoundary_canonicalAngle hn ho hr owner hf k)
  have hEaxis : (forwardAxis jE).Feasible (K.square E) (K.square H) := by
    have hh := (C.realizeBoundary_feasible_iff hn ho hr owner hf E jE).2 hEH
    simpa [E,H,next] using hh
  have hGaxis : (forwardAxis jG).Feasible (K.square G) (K.square A) := by
    have hh := (C.realizeBoundary_feasible_iff hn ho hr owner hf G jG).2 hGA
    simpa [G,A,next] using hh
  exact GlobalEH.original_high_low_false K (by simpa only [qCap,Q0] using hq)
    F hFquarter jE jG hEowner hGowner hEaxis hGaxis

/-- One actual low GA witness controls every original EH witness. -/
theorem EH_low_of_GA_low {q : ℝ} (C : SignedCycle)
    (hq : q∈Icc (5/2:ℝ) qCap) (hn : C.Necessary q) (ho : C.Ordered)
    (hs : C.StrictSpread) (hr : ∀i,(C.point i).Boundary q)
    (owner : Vertex→Fin 4) (hf : ∀i,C.Feasible i (owner i))
    (jG : Fin 4) (hGowner : jG=0 ∨ jG=1) (hGA : C.Feasible G jG)
    (jE : Fin 4) (hEH : C.Feasible E jE) : jE=0 ∨ jE=1 := by
  by_contra hbad
  have hEowner : jE=2 ∨ jE=3 := by fin_cases jE <;> simp_all
  exact C.high_EH_low_GA_false hq hn ho hs hr owner hf
    jE jG hEowner hGowner hEH hGA

/-- The converse dispatch retains the supplied high EH axis and
classifies every original GA axis separately. -/
theorem GA_high_of_EH_high {q : ℝ} (C : SignedCycle)
    (hq : q∈Icc (5/2:ℝ) qCap) (hn : C.Necessary q) (ho : C.Ordered)
    (hs : C.StrictSpread) (hr : ∀i,(C.point i).Boundary q)
    (owner : Vertex→Fin 4) (hf : ∀i,C.Feasible i (owner i))
    (jE : Fin 4) (hEowner : jE=2 ∨ jE=3) (hEH : C.Feasible E jE)
    (jG : Fin 4) (hGA : C.Feasible G jG) : jG=2 ∨ jG=3 := by
  by_contra hbad
  have hGowner : jG=0 ∨ jG=1 := by fin_cases jG <;> simp_all
  exact C.high_EH_low_GA_false hq hn ho hs hr owner hf
    jE jG hEowner hGowner hEH hGA

end SquaresInCircles.Eight.TableFree.SignedCycle
