module

public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2Weights
public import SquaresInCircles.Eight.Owners.GA.Positive.TDScalarBounds

/-!
# Eight squares: the exact negative-flat-A / TD2 scalar baseline

The original GA and AB alternatives keep their separate secant weights.
Only the high family's D support is enlarged to its full-circle bound
inside the analytic lower estimate.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open Certificate (Family)

def secant (l s : ℝ) : ℝ := l/Real.cos s
def lambdaG (atG : Bool) (l s : ℝ) : ℝ := if atG then secant l s else l
def lambdaB (atG : Bool) (l s : ℝ) : ℝ := if atG then l else secant l s

def baseline (atG : Bool) (k l c s z : ℝ) : ℝ :=
  k+lambdaG atG l s+lambdaB atG l s+PositiveTD.tilted c z+c*edgeWidth z+2-
    c*PositiveTD.sigma*Real.sin z-fullSupport 1 k-fullSupport (lambdaG atG l s) k-
    fullSupport (PositiveTD.tilted c z) (lambdaB atG l s)-clippedSupport 1 c+
    secant l s*(edgeWidth s-1)+(7/12)*l*Real.tan s

def nonradical (f : Family) (z : ℝ) : ℝ :=
  2*Explicit.k f z+3*Explicit.l f z+(3/2)*Explicit.m f z+
    Explicit.c f z*edgeWidth z+5/2-Explicit.c f z*PositiveTD.sigma*Real.sin z+
    if f=.low then -(1+Explicit.c f z)*GlobalGA.Secondary.diagonal else (1+Explicit.c f z)/2

def reducedBaseline (f : Family) (atG : Bool) (s z : ℝ) : ℝ :=
  baseline atG (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) s z+
    if f=.low then 0 else clippedSupport 1 (Explicit.c f z)-fullSupport 1 (Explicit.c f z)

def norms (atG : Bool) (k l c s z : ℝ) : Fin 4→ℝ :=
  ![pairNorm k 1 0,pairNorm k (lambdaG atG l s) 0,
    pairNorm (lambdaB atG l s) (PositiveTD.tilted c z) 0,pairNorm c 1 0]
def normSum (f : Family) (n : Fin 4→ℝ) : ℝ :=
  if f=.low then n 0+n 1+n 2 else n 0+n 1+n 2+n 3
def scaledNorms (f : Family) (atG : Bool) (s z : ℝ) (i : Fin 4) : ℝ :=
  Real.cos s*norms atG (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) s z i

theorem baseline_zero (atG : Bool) (k l c z : ℝ) :
    baseline atG k l c 0 z=PositiveTD.baseline k l c z := by
  cases atG <;> simp [baseline,lambdaG,lambdaB,secant,PositiveTD.baseline,edgeWidth_zero] <;> ring

theorem reduced_le_baseline (f : Family) (atG : Bool) (s z : ℝ) :
    reducedBaseline f atG s z≤
      baseline atG (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) s z := by
  have hD := PositiveTD.Certificate.clippedSupport_le_fullSupport 1 (Explicit.c f z)
  cases f <;> simp only [reducedBaseline,↓reduceIte,add_zero,reduceCtorEq] <;> linarith

theorem secant_width_identity {l s : ℝ} (hs : s∈Icc 0 frameCap) :
    (3/2)*(secant l s-l)+secant l s*(edgeWidth s-1)+(7/12)*l*Real.tan s=
      secant l s-l+(13/12)*l*Real.tan s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  rw [edgeWidth_positive_formula hs,Real.tan_eq_sin_div_cos]
  dsimp [secant]
  field_simp [hc.ne']
  ring

theorem reduced_identity (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 frameCap) :
    reducedBaseline f atG s z=
      nonradical f z+secant (Explicit.l f z) s-Explicit.l f z+
        (13/12)*Explicit.l f z*Real.tan s-
        R*normSum f (norms atG (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) s z) := by
  have hwidth := secant_width_identity (l:=Explicit.l f z) hs
  cases f
  · have hz' : z∈Icc 0 (1/5:ℝ) := by
      norm_num [Certificate.left,Certificate.right,Certificate.split] at hz
      exact ⟨hz.1,by linarith [hz.2]⟩
    have hc := (Explicit.low_ranges hz').2.2.2.2.1
    cases atG <;>
      simp only [reducedBaseline,baseline,nonradical,normSum,norms,
        lambdaG,lambdaB,↓reduceIte,Bool.false_eq_true,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one,
        fullSupport_pair,clippedSupport,hc,diagonalSupport,Explicit.m] at ⊢
      <;> linarith only [hwidth]
  · cases atG <;>
      simp only [reducedBaseline,baseline,nonradical,normSum,norms,
        lambdaG,lambdaB,↓reduceIte,Bool.false_eq_true,reduceCtorEq,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one,
        Fin.succ_one_eq_two,fullSupport_pair,Explicit.m] at ⊢
      <;> linarith only [hwidth]

theorem scaled_identity (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 frameCap) :
    Real.cos s*reducedBaseline f atG s z=
      Real.cos s*(nonradical f z-Explicit.l f z)+Explicit.l f z+
        (13/12)*Explicit.l f z*Real.sin s-
        R*normSum f (scaledNorms f atG s z) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  rw [reduced_identity f atG hz hs,Real.tan_eq_sin_div_cos]
  dsimp [secant,scaledNorms,normSum]
  split_ifs <;> field_simp [hc.ne'] <;> ring

theorem norms_nonnegative (atG : Bool) (k l c s z : ℝ) (i : Fin 4) :
    0≤norms atG k l c s z i := by
  fin_cases i <;> simp only [norms] <;>
    exact Real.sqrt_nonneg _

theorem scaled_norms_nonnegative (f : Family) (atG : Bool) {s z : ℝ}
    (hs : s∈Icc 0 frameCap) (i : Fin 4) : 0≤ scaledNorms f atG s z i := by
  have hc : 0≤Real.cos s := by linarith [(transport_trig hs).1]
  exact mul_nonneg hc (norms_nonnegative atG _ _ _ s z i)

def mixedG (k l z : ℝ) : ℝ :=
  k*(PositiveAngularEnvelope.phi (frameCap-z)-1)+l*(Real.cos frameCap-1)-
    R*(pairNorm k l (-z)-pairNorm k l 0)

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD
