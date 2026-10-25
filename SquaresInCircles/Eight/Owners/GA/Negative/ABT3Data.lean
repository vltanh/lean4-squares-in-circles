module

public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowNegativeComparison
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3Data

/-!
# Eight squares: the two reference families for a negative A primary with BT3

The three positive base weights are
fixed at z. Only the A multiplier uses sec(s), and only the TD0
multiplier rotates with the actual BT3 error. The algebraic baseline
retains the exact sorted-D diagonal support on the low family and
the complete-circle support on the high family.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

namespace Certificate
abbrev Family := NegativeAPositiveTD.Certificate.Family
abbrev split : ℚ := 1/4
def left : Family→ℚ | .low => 0 | .high => split
def right : Family→ℚ | .low => split | .high => 7/10
def k : Family→ℚ[X]
  | .low => C (2/3)+C (1/20)*X
  | .high => C (169/250)+C (1/5)*(X-C (1/5))+
      C (9/10)*(X-C (1/5))^2-C (13/10)*(X-C (1/5))^3
def l : Family→ℚ[X]
  | .low => C (533/500)-C (4/25)*X
  | .high => C (41/40)+C (11/50)*(X-C (1/5))-C (3/10)*(X-C (1/5))^2
def m : Family→ℚ[X]
  | .low => C (59/50)+C (1/10)*X-C (769/200)*X^2
  | .high => C (24/25)-C (7/10)*(X-C (1/4))+C (6/5)*(X-C (1/4))^2
end Certificate

namespace Explicit
open Certificate (Family)
def k : Family→ℝ→ℝ
  | .low,z => 2/3+z/20
  | .high,z => 169/250+(z-1/5)/5+(9/10)*(z-1/5)^2-(13/10)*(z-1/5)^3
def l : Family→ℝ→ℝ
  | .low,z => 533/500-(4/25)*z
  | .high,z => 41/40+(11/50)*(z-1/5)-(3/10)*(z-1/5)^2
def m : Family→ℝ→ℝ
  | .low,z => 59/50+z/10-(769/200)*z^2
  | .high,z => 24/25-(7/10)*(z-1/4)+(6/5)*(z-1/4)^2
def c (f : Family) (z : ℝ) : ℝ := PositiveBT3.tilted (m f z) z
abbrev angleCut := NegativeAPositiveTD.Explicit.angleCut
abbrev angle_domain := @NegativeAPositiveTD.Explicit.angle_domain

@[simp] theorem k_eval (f : Family) (z : ℝ) : aeval z (Certificate.k f)=k f z := by
  cases f <;> norm_num [Certificate.k,k] <;> ring
@[simp] theorem l_eval (f : Family) (z : ℝ) : aeval z (Certificate.l f)=l f z := by
  cases f <;> norm_num [Certificate.l,l]
@[simp] theorem m_eval (f : Family) (z : ℝ) : aeval z (Certificate.m f)=m f z := by
  cases f <;> norm_num [Certificate.m,m]
  ring

theorem frame_domain (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) : z∈Icc 0 frameCap := by
  cases f <;> norm_num [Certificate.left,Certificate.right,Certificate.split,frameCap] at hz ⊢ <;>
    constructor <;> linarith [hz.1,hz.2]
end Explicit

abbrev secant := NegativeAPositiveTD.secant
abbrev lambdaG := NegativeAPositiveTD.lambdaG
abbrev lambdaB := NegativeAPositiveTD.lambdaB
abbrev mixedG := NegativeAPositiveTD.mixedG

def baseline (atG : Bool) (k l m s z : ℝ) : ℝ :=
  k+lambdaG atG l s+lambdaB atG l s+m*edgeWidth z+PositiveBT3.tilted m z+2-
    m*PositiveTD.sigma*Real.sin z-fullSupport 1 k-fullSupport (lambdaG atG l s) k-
    fullSupport (lambdaB atG l s) m-clippedSupport 1 (PositiveBT3.tilted m z)+
    secant l s*(edgeWidth s-1)+(7/12)*l*Real.tan s
def baselineZero (k l m z : ℝ) : ℝ := baseline true k l m 0 z
def norms (atG : Bool) (k l m s z : ℝ) : Fin 4→ℝ :=
  ![pairNorm k 1 0,pairNorm k (lambdaG atG l s) 0,
    pairNorm m (lambdaB atG l s) 0,pairNorm 1 (PositiveBT3.tilted m z) 0]
abbrev normSum := NegativeAPositiveTD.normSum
def reducedBaseline (f : Certificate.Family) (atG : Bool) (s z : ℝ) : ℝ :=
  baseline atG (Explicit.k f z) (Explicit.l f z) (Explicit.m f z) s z+
    if f=.low then 0 else clippedSupport 1 (Explicit.c f z)-fullSupport 1 (Explicit.c f z)

theorem baseline_zero (atG : Bool) (k l m z : ℝ) : baseline atG k l m 0 z=baselineZero k l m z := by
  cases atG <;> simp [baselineZero,baseline,NegativeAPositiveTD.lambdaG,
    NegativeAPositiveTD.lambdaB,NegativeAPositiveTD.secant]

theorem reduced_le_baseline (f : Certificate.Family) (atG : Bool) (s z : ℝ) :
    reducedBaseline f atG s z≤baseline atG (Explicit.k f z) (Explicit.l f z) (Explicit.m f z) s z := by
  have hh := PositiveTD.Certificate.clippedSupport_le_fullSupport 1 (Explicit.c f z)
  cases f <;> simp only [reducedBaseline,↓reduceIte,reduceCtorEq,add_zero,le_refl]
  linarith

def pWeights (f : Certificate.Family) (atG : Bool) (k l m c s : ℝ) : Fin 4→ℝ :=
  ![k,k,min (lambdaB atG l s) m,if f=.low then k else min 1 c]
def qWeights (f : Certificate.Family) (atG : Bool) (_k l m c s : ℝ) : Fin 4→ℝ :=
  ![1,lambdaG atG l s,max (lambdaB atG l s) m,if f=.low then 1 else max 1 c]

end SquaresInCircles.Eight.GlobalGA.NegativeABT3
