module

public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2Weights
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeADCorrection

/-!
# Eight squares: negative EH1 with nonnegative A total and positive TD2

The small-E stress uses the two negative-DE coefficient families. The far-E stress uses its own
continuous linear family and the constant EH multiplier `201/200` (`ehWeight`). Coefficients are
held fixed when either the E magnitude or the A/TD split varies.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

inductive Regime where | small | far
  deriving DecidableEq

instance : Fintype Regime where
  elems := {.small, .far}
  complete x := by cases x <;> decide
abbrev Family := NegativeDEPositiveTD.Family
abbrev Split := NegativeDEPositiveTD.Split

namespace Explicit

abbrev v : ℝ := 1/10
abbrev u : ℝ := 1/4
abbrev L : ℝ := 1/6
abbrev eta := NegativeDEPositiveTD.Explicit.eta
abbrev sigma := NegativeDEPositiveTD.Explicit.sigma
abbrev splitA := NegativeDEPositiveTD.Explicit.splitA
abbrev splitT := NegativeDEPositiveTD.Explicit.splitT

def left : Regime→Family→ℝ
  | .small,.low => 0 | .small,.high => L
  | .far,.low => 0 | .far,.high => u
def right : Regime→Family→ℝ
  | .small,.low => L | .far,.low => u | _,.high => frameCap
def eLeft : Regime→ℝ | .small => 0 | .far => v
def eRight : Regime→ℝ | .small => v | .far => u
def k : Regime→Family→ℝ→ℝ
  | .small,f,θ => NegativeDEPositiveTD.Explicit.k f θ
  | .far,.low,_ => 121/200
  | .far,.high,θ => 101/200+(2/5)*θ
def l : Regime→Family→ℝ→ℝ
  | .small,f,θ => NegativeDEPositiveTD.Explicit.l f θ
  | .far,.low,θ => 1-(9/25)*θ
  | .far,.high,θ => 381/400-(17/100)*θ
def c : Regime→Family→ℝ→ℝ
  | .small,f,θ => NegativeDEPositiveTD.Explicit.c f θ
  | .far,.low,θ => 111/100-(77/100)*θ
  | .far,.high,θ => 1929/2000-(47/250)*θ
def m (r : Regime) (f : Family) (θ z : ℝ) : ℝ := c r f θ*(Real.cos z+eta*Real.sin z)
def splitM (r : Regime) (f : Family) (e : Split) (θ : ℝ) : ℝ := m r f θ (splitT e θ)
def ehWeight : Regime→ℝ | .small => 1 | .far => NegativeEH.p
def errorCharge : Regime→ℝ | .small => 0 | .far => NegativeEH.epsilon
def gain : Regime→ℝ→ℝ | .small => NegativeEH.g | .far => NegativeEH.G
def sortedD : Regime→Family→Bool | .small,.low => true | _,_ => false

def p (r : Regime) (f : Family) (θ z : ℝ) : Fin 3→ℝ :=
  ![k r f θ,k r f θ,min (l r f θ) (m r f θ z)]
def q (r : Regime) (f : Family) (θ z : ℝ) : Fin 3→ℝ :=
  ![1,l r f θ,max (l r f θ) (m r f θ z)]

def baseline (r : Regime) (f : Family) (a z : ℝ) : ℝ :=
  let θ := a+z
  k r f θ+2*l r f θ+m r f θ z+c r f θ*edgeWidth z+2-
    c r f θ*sigma*Real.sin z+l r f θ*TwoPositive.ASupport.charge a-
    fullSupport 1 (k r f θ)-fullSupport (l r f θ) (k r f θ)-
    fullSupport (m r f θ z) (l r f θ)-
    (if sortedD r f then clippedSupport 1 (c r f θ) else fullSupport 1 (c r f θ))

def stressBase (r : Regime) (f : Family) (a z s : ℝ) : ℝ := baseline r f a z+gain r s
def U (r : Regime) (f : Family) (θ z : ℝ) (i : Fin 3) (x : ℝ) : ℝ :=
  OrdinaryAngleConcavity.U R (p r f θ z i) (q r f θ z i) x
def V (r : Regime) (f : Family) (θ z : ℝ) (i : Fin 3) (x : ℝ) : ℝ :=
  OrdinaryAngleConcavity.V R (p r f θ z i) (q r f θ z i) x

theorem family_frame_domain (r : Regime) (f : Family) {θ : ℝ}
    (hθ : θ∈Icc (left r f) (right r f)) : θ∈Icc 0 frameCap := by
  cases r <;> cases f <;> norm_num [left,right,L,u,frameCap] at hθ ⊢ <;>
    constructor <;> linarith [hθ.1,hθ.2]

theorem e_frame_domain (r : Regime) {s : ℝ} (hs : s∈Icc (eLeft r) (eRight r)) :
    s∈Icc 0 frameCap := by
  cases r <;> norm_num [eLeft,eRight,v,u,frameCap] at hs ⊢ <;>
    constructor <;> linarith [hs.1,hs.2]

end Explicit
end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD
