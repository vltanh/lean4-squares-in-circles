module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeELargeAScalars
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDPolynomialData

/-!
# The two continuous negative-DE / positive-TD2 stresses

Uncompiled transcription of Sections 1--3 of
HAND_G3_CORE_E_NEGATIVE_DE3_POSITIVE_TD2_COMPLETE_SCALAR_EXCLUSION.md.
The weights depend on the total positive A/TD angle.  The low and high
families are independent stresses at their common endpoint 1/6.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

inductive Family where | low | high
  deriving DecidableEq, Fintype

inductive Split where | atT | atA
  deriving DecidableEq, Fintype

namespace Explicit

def L : ℝ := 1/6
def eta : ℝ := 293/1000
def K : ℝ := 13/12
def left : Family → ℝ | .low => 0 | .high => L
def right : Family → ℝ | .low => L | .high => frameCap
def t (θ : ℝ) : ℝ := 15/8*(θ-L)

def k : Family → ℝ → ℝ
  | .low,θ => 6708/10000+3/20*(θ-L)+4*(θ-L)^2
  | .high,θ => 670158/1000000+113718/1000000*t θ+
      6506/1000000*(t θ)^2+9026/1000000*(t θ)^3+1/1000*(t θ)^4
def l : Family → ℝ → ℝ
  | .low,θ => 10073/10000-17/10*(θ-L)+11/5*(θ-L)^2
  | .high,θ => 1005069/1000000-146411/1000000*t θ-
      157739/1000000*(t θ)^2+162815/1000000*(t θ)^3
def c : Family → ℝ → ℝ
  | .low,θ => 10389/10000-69/20*(θ-L)+9*(θ-L)^2
  | .high,θ => 1021248/1000000-168873/1000000*t θ-
      165381/1000000*(t θ)^2+175944/1000000*(t θ)^3

def m (f : Family) (θ z : ℝ) : ℝ := c f θ*(Real.cos z+eta*Real.sin z)
def splitA : Split → ℝ → ℝ | .atT,_ => 0 | .atA,θ => θ
def splitT : Split → ℝ → ℝ | .atT,θ => θ | .atA,_ => 0
def splitM (f : Family) (e : Split) (θ : ℝ) : ℝ := m f θ (splitT e θ)
def secant (s : ℝ) : ℝ := 1/Real.cos s
def sigma : ℝ := fullSupport 1 eta

def p (f : Family) (θ z : ℝ) : Fin 3 → ℝ :=
  ![k f θ,k f θ,min (l f θ) (m f θ z)]
def q (f : Family) (θ z : ℝ) : Fin 3 → ℝ :=
  ![1,l f θ,max (l f θ) (m f θ z)]

/-- The exact source baseline, with the sorted D support retained. -/
def baseline (f : Family) (a z s : ℝ) : ℝ :=
  let θ := a+z
  k f θ+2*l f θ+m f θ z+c f θ*edgeWidth z+secant s+1-
    c f θ*sigma*Real.sin z+l f θ*TwoPositive.ASupport.charge a-
    fullSupport 1 (k f θ)-fullSupport (l f θ) (k f θ)-
    fullSupport (m f θ z) (l f θ)-clippedSupport (secant s) (c f θ)+
    K*Real.tan s-(secant s-1)/2

/-- The full-D lower baseline used by the high family. -/
def fullBaseline (f : Family) (a z s : ℝ) : ℝ :=
  baseline f a z s+clippedSupport (secant s) (c f (a+z))-
    fullSupport (secant s) (c f (a+z))

def U (f : Family) (θ z : ℝ) (i : Fin 3) (x : ℝ) : ℝ :=
  OrdinaryAngleConcavity.U R (p f θ z i) (q f θ z i) x
def V (f : Family) (θ z : ℝ) (i : Fin 3) (x : ℝ) : ℝ :=
  OrdinaryAngleConcavity.V R (p f θ z i) (q f θ z i) x

theorem family_frame_domain (f : Family) {θ : ℝ}
    (hθ : θ∈Icc (left f) (right f)) : θ∈Icc 0 frameCap := by
  cases f <;> norm_num [left,right,L,frameCap] at hθ ⊢ <;>
    constructor <;> linarith [hθ.1,hθ.2]

end Explicit
end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD
