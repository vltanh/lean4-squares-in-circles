module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3LowPolynomial
public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsEndpoints

/-!
# The actual small and large BT3 scalar expressions

Uncompiled equations (15), (21)--(22), and (27)--(36). The varying
argument is the A total a, with u=theta-a. The D multiplier rotates
with u, while all three negative alternatives have fixed coefficients.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Analytic
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open NonnegativeTotals

def lowBaseline (k m u : ℝ) : ℝ :=
  k+2+m*edgeWidth u+tilted m u+2-m*PositiveTD.sigma*Real.sin u-
    2*fullSupport k 1-fullSupport 1 m-(1+tilted m u)*GlobalGA.Secondary.diagonal

def lowScalar (t a : ℝ) : ℝ :=
  lowBaseline (lowK t) (lowM t) (t-a)+TwoPositive.ASupport.charge a+V R (lowK t) 1 t

def fullBaseline (k l m u : ℝ) : ℝ :=
  k+2*l+m*edgeWidth u+tilted m u+2-m*PositiveTD.sigma*Real.sin u-
    fullSupport 1 k-fullSupport l k-fullSupport m l-fullSupport 1 (tilted m u)

abbrev negative := NonnegativeTotals.Analytic.negative

def largeScalar (k l m theta e a : ℝ) (i : Fin 3) : ℝ :=
  fullBaseline k l m (theta-a)+l*TwoPositive.ASupport.charge a+
    TwoPositive.ASupport.charge e+negative k l m (theta+e) i

def largeEndpoint (r : Region) (ep : Endpoint) (i : Fin 3) (x y : ℝ) : ℝ :=
  largeScalar (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
    (Explicit.theta r x y) (Explicit.e r x y)
    (NonnegativeTotals.Analytic.aAt ep (Explicit.theta r x y)) i

def normAt (r : Region) (i : Fin 3) (j : Fin 4) (x y : ℝ) : ℝ :=
  pairNorm (![Explicit.k r x y,Explicit.k r x y,Explicit.l r x y,1] j)
    (![1,Explicit.l r x y,Explicit.c r x y,
      tilted (Explicit.c r x y) (Explicit.theta r x y)] j)
    (if j.val=i.val then -Explicit.delta r x y else 0)

def largeCoefficient (r : Region) (x y : ℝ) : Fin 3 → ℝ :=
  ![1,Explicit.l r x y,max (Explicit.l r x y) (Explicit.c r x y)]

def nonradical (r : Region) (i : Fin 3) (x y : ℝ) : ℝ :=
  NonnegativeTotals.Analytic.nonradicalBase r .atT x y+
    largeCoefficient r x y i*(Real.cos (Explicit.delta r x y)-1)

theorem tilted_eq (m u : ℝ) : tilted m u=PositiveTD.tilted m u := rfl

theorem fullBaseline_zero (k l m : ℝ) :
    fullBaseline k l m 0=NonnegativeTotals.Analytic.fullBaseline k l m 0 := by
  simp only [fullBaseline,NonnegativeTotals.Analytic.fullBaseline,
    tilted,PositiveTD.tilted,Real.cos_zero,Real.sin_zero,mul_zero,add_zero,mul_one]
  ring

theorem A_endpoint_positive (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) : 0<largeEndpoint r .atA i x y := by
  have hh := NonnegativeTotals.Analytic.endpoint_positive r .atA i hd
  simpa only [largeEndpoint,largeScalar,NonnegativeTotals.Analytic.endpoint,
    NonnegativeTotals.Analytic.largeScalar,NonnegativeTotals.Analytic.aAt,
    sub_self,fullBaseline_zero,PositiveTD.tilted,Real.cos_zero,Real.sin_zero,
    mul_zero,add_zero,mul_one] using hh

theorem fullBaseline_norms (k l m u : ℝ) :
    fullBaseline k l m u=2*k+3*l+(3/2)*tilted m u+m*(edgeWidth u+1/2)+3-
      m*PositiveTD.sigma*Real.sin u-
        R*(pairNorm k 1 0+pairNorm k l 0+pairNorm l m 0+pairNorm 1 (tilted m u) 0) := by
  rw [fullBaseline,fullSupport_pair k 1,fullSupport_pair k l,
    fullSupport_pair l m,fullSupport_pair (tilted m u) 1]
  rw [pairNorm_symm (tilted m u) 1]
  ring

theorem T_endpoint_identity (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) :
    largeEndpoint r .atT i x y=nonradical r i x y-
      R*(normAt r i 0 x y+normAt r i 1 x y+normAt r i 2 x y+normAt r i 3 x y) := by
  have hθ := (Explicit.domains hd).1
  unfold largeEndpoint largeScalar
  simp only [NonnegativeTotals.Analytic.aAt,sub_zero,TwoPositive.ASupport.charge_zero,mul_zero,add_zero]
  rw [fullBaseline_norms]
  simp only [negative]
  rw [NonnegativeTotals.Analytic.negative_identity]
  fin_cases i <;>
    simp only [nonradical,NonnegativeTotals.Analytic.nonradicalBase,largeCoefficient,
      normAt,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceFinMk,
      ite_true,ite_false,tilted]
  all_goals
    rw [edgeWidth_positive_formula hθ]
    dsimp [Explicit.delta]
    ring

theorem norm_nonnegative (r : Region) (i : Fin 3) (j : Fin 4) (x y : ℝ) :
    0≤normAt r i j x y := Real.sqrt_nonneg _

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Analytic
