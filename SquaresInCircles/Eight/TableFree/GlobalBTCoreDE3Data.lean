module

public import SquaresInCircles.Eight.TableFree.GlobalBTTailConcentration

/-!
# Explicit scalar data for the core-E negative-DE3 tail

The coefficient is selected by the actual DE error.  The prefix
coefficient depends only on its retained total and is held fixed
during the concentration comparison.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3

open FrameCircleArc

def m : ℝ := 269343/250000
def slope : ℝ := 2/5
def weight (p : ℝ) : ℝ := 3/5+slope*p
def endpointWeight (t : ℝ) : ℝ := if t≤1/5 then kappa else m/Real.cos t

def first (p t e : ℝ) : ℝ :=
  Real.pi-p-t+(3/2)*kappa+2*weight p+e+kappa*Real.cos p+
    (e/2)*Real.cos t+e*(13/12)*Real.sin t-
      R*(tailNorm kappa (weight p) p+tailNorm e (weight p) 0)

def last (p t e : ℝ) : ℝ :=
  Real.pi-p-t+(5/2)*kappa+weight p+e+weight p*Real.cos p+
    (e/2)*Real.cos t+e*(13/12)*Real.sin t-
      R*(tailNorm kappa (weight p) 0+tailNorm e (weight p) p)

def base (t e : ℝ) : ℝ :=
  Real.pi-t+(5/2)*kappa+6/5+e*(1+(1/2)*Real.cos t+(13/12)*Real.sin t)-
    R*(tailNorm kappa (3/5) 0+tailNorm e (3/5) 0)

def «prefix» (p : ℝ) : ℝ :=
  Real.pi-p+3*kappa+2*weight p+kappa*Real.cos p-
    R*(tailNorm kappa (weight p) p+tailNorm kappa (weight p) 0)

theorem weight_bounds {p : ℝ} (hp : p∈Icc 0 frameCap) :
    (3/5:ℝ)≤weight p ∧ weight p≤22/25 ∧ weight p≤kappa := by
  dsimp [weight,slope,kappa,frameCap] at *
  constructor
  · linarith [hp.1]
  · constructor <;> linarith [hp.2]

theorem weight_pos {p : ℝ} (hp : p∈Icc 0 frameCap) : 0<weight p := by
  linarith [(weight_bounds hp).1]

theorem first_zero (t e : ℝ) : first 0 t e=base t e := by
  simp [first,base,weight] <;> ring

theorem last_zero (t e : ℝ) : last 0 t e=base t e := by
  simp [last,base,weight] <;> ring

end SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3
