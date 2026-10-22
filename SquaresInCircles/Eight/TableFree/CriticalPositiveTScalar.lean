module

public import SquaresInCircles.Eight.TableFree.CriticalPositiveTCoefficients
public import SquaresInCircles.Eight.TableFree.CriticalPositiveTModel
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The differentiated adapted ET scalar

Uncompiled transcription of equations (32), (35) and (36). The original
supporting dual is held fixed while z varies. Positivity of all four norm
radicands follows from the proved coefficient ranges. This file computes
the derivative by the ordinary product and square-root rules and connects
it to the one whole-triangle rational model.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalPositiveTScalar
open CriticalPositiveTCoefficients ExceptionalContactStress ExceptionalContactSupport

def p (eta t z : ℝ) : ℝ := tilt eta (t-z)
def pDerivative (eta t z : ℝ) : ℝ := Real.sin (t-z)-eta*Real.cos (t-z)
def contactDerivative (R eta s : ℝ) : ℝ :=
  -2*Real.sin s+(1+2*eta-R*Real.sqrt (1+eta^2))*Real.cos s
def hSquare (K eta t z : ℝ) : ℝ := p eta t z^2+adaptedK K z^2
def aSquare (K L z : ℝ) : ℝ := adaptedK K z^2+adaptedL L z^2
def bSquare (L C eta t z : ℝ) : ℝ :=
  adaptedL L z^2+adaptedM C eta z^2-2*adaptedL L z*adaptedM C eta z*Real.sin t
def dSquare (C z : ℝ) : ℝ := 1+adaptedC C z^2
def hNumerator (K eta t z : ℝ) : ℝ := p eta t z*pDerivative eta t z+adaptedK K z*(3/50)
def aNumerator (K L z : ℝ) : ℝ := adaptedK K z*(3/50)+adaptedL L z*(-23/100)
def bNumerator (L C eta t z : ℝ) : ℝ :=
  adaptedL L z*(-23/100)+adaptedM C eta z*mDerivative C eta z-
    ((-23/100)*adaptedM C eta z+adaptedL L z*mDerivative C eta z)*Real.sin t
def dNumerator (C z : ℝ) : ℝ := adaptedC C z*(-53/100)

def scalar (R K L C eta t z : ℝ) : ℝ :=
  3*adaptedK K z+2*adaptedL L z+adaptedC C z*contactScalar R eta z+
    contactScalar R eta (t-z)+adaptedM C eta z*(Real.cos t-1)-
    R*(Real.sqrt (hSquare K eta t z)+Real.sqrt (aSquare K L z)+
      Real.sqrt (bSquare L C eta t z)+Real.sqrt (dSquare C z))

def slope (R K L C eta t z : ℝ) : ℝ :=
  3*(3/50)+2*(-23/100)+(-53/100)*contactScalar R eta z+
    adaptedC C z*contactDerivative R eta z-contactDerivative R eta (t-z)+
    mDerivative C eta z*(Real.cos t-1)-R*(
      hNumerator K eta t z/Real.sqrt (hSquare K eta t z)+
      aNumerator K L z/Real.sqrt (aSquare K L z)+
      bNumerator L C eta t z/Real.sqrt (bSquare L C eta t z)+
      dNumerator C z/Real.sqrt (dSquare C z))

theorem radicands_positive {K L C eta t z : ℝ}
    (h : CriticalECoefficients.Bounds t K L C eta) (hz : z∈Icc 0 t) :
    0<hSquare K eta t z ∧ 0<aSquare K L z ∧
      0<bSquare L C eta t z ∧ 0<dSquare C z := by
  have hb := adapted_bounds h hz
  have hk : 0<adaptedK K z := by linarith [hb.k_lower]
  have hm : 0<adaptedM C eta z := by linarith [hb.c_lower,hb.c_le_m]
  have hs : Real.sin t<1 := by linarith [(transport_trig hb.angle).2.2.2.1]
  have hprod := mul_pos (mul_pos hb.ell_pos hm) (sub_pos.mpr hs)
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [hSquare]
    nlinarith [sq_nonneg (p eta t z),sq_pos_of_pos hk]
  · dsimp [aSquare]
    nlinarith [sq_nonneg (adaptedL L z),sq_pos_of_pos hk]
  · dsimp [bSquare]
    nlinarith [sq_nonneg (adaptedL L z-adaptedM C eta z)]
  · dsimp [dSquare]
    positivity

theorem k_hasDerivAt (K z : ℝ) : HasDerivAt (adaptedK K) (3/50) z := by
  convert ((hasDerivAt_id z).const_mul (3/50)).const_add K using 1 <;>
    dsimp [adaptedK] <;> ring
theorem ell_hasDerivAt (L z : ℝ) : HasDerivAt (adaptedL L) (-23/100) z := by
  convert (hasDerivAt_const z L).sub ((hasDerivAt_id z).const_mul (23/100)) using 1 <;>
    dsimp [adaptedL] <;> ring
theorem c_hasDerivAt (C z : ℝ) : HasDerivAt (adaptedC C) (-53/100) z := by
  convert (hasDerivAt_const z C).sub ((hasDerivAt_id z).const_mul (53/100)) using 1 <;>
    dsimp [adaptedC] <;> ring
theorem p_hasDerivAt (eta t z : ℝ) : HasDerivAt (p eta t) (pDerivative eta t z) z := by
  have hr : HasDerivAt (fun s : ℝ => t-s) (-1) z := by
    convert (hasDerivAt_const z t).sub (hasDerivAt_id z) using 1 <;> ring
  convert ((Real.hasDerivAt_cos (t-z)).comp z hr).add
    (((Real.hasDerivAt_sin (t-z)).comp z hr).const_mul eta) using 1 <;>
    dsimp [p,pDerivative,tilt] <;> ring
theorem contact_hasDerivAt (R eta z : ℝ) :
    HasDerivAt (contactScalar R eta) (contactDerivative R eta z) z := by
  convert (((Real.hasDerivAt_cos z).const_mul 2).const_add 1).add
    ((Real.hasDerivAt_sin z).const_mul (1+2*eta-R*Real.sqrt (1+eta^2))) using 1 <;>
    dsimp [contactScalar,contactDerivative] <;> ring

theorem hSquare_hasDerivAt (K eta t z : ℝ) :
    HasDerivAt (hSquare K eta t) (2*hNumerator K eta t z) z := by
  convert ((p_hasDerivAt eta t z).pow 2).add ((k_hasDerivAt K z).pow 2) using 1 <;>
    dsimp [hSquare,hNumerator] <;> ring
theorem aSquare_hasDerivAt (K L z : ℝ) :
    HasDerivAt (aSquare K L) (2*aNumerator K L z) z := by
  convert ((k_hasDerivAt K z).pow 2).add ((ell_hasDerivAt L z).pow 2) using 1 <;>
    dsimp [aSquare,aNumerator] <;> ring
theorem bSquare_hasDerivAt (L C eta t z : ℝ) :
    HasDerivAt (bSquare L C eta t) (2*bNumerator L C eta t z) z := by
  convert (((ell_hasDerivAt L z).pow 2).add ((m_hasDerivAt C eta z).pow 2)).sub
    ((((ell_hasDerivAt L z).const_mul 2).mul (m_hasDerivAt C eta z)).mul_const (Real.sin t)) using 1 <;>
    dsimp [bSquare,bNumerator] <;> ring
theorem dSquare_hasDerivAt (C z : ℝ) :
    HasDerivAt (dSquare C) (2*dNumerator C z) z := by
  convert ((c_hasDerivAt C z).pow 2).const_add 1 using 1 <;>
    dsimp [dSquare,dNumerator] <;> ring

theorem hasDerivAt_scalar {R K L C eta t z : ℝ}
    (h : CriticalECoefficients.Bounds t K L C eta) (hz : z∈Icc 0 t) :
    HasDerivAt (scalar R K L C eta t) (slope R K L C eta t z) z := by
  obtain ⟨hH,hA,hB,hD⟩ := radicands_positive h hz
  have dH : HasDerivAt (fun s => Real.sqrt (hSquare K eta t s))
      (hNumerator K eta t z/Real.sqrt (hSquare K eta t z)) z := by
    convert (hSquare_hasDerivAt K eta t z).sqrt hH.ne' using 1 <;> ring
  have dA : HasDerivAt (fun s => Real.sqrt (aSquare K L s))
      (aNumerator K L z/Real.sqrt (aSquare K L z)) z := by
    convert (aSquare_hasDerivAt K L z).sqrt hA.ne' using 1 <;> ring
  have dB : HasDerivAt (fun s => Real.sqrt (bSquare L C eta t s))
      (bNumerator L C eta t z/Real.sqrt (bSquare L C eta t z)) z := by
    convert (bSquare_hasDerivAt L C eta t z).sqrt hB.ne' using 1 <;> ring
  have dD : HasDerivAt (fun s => Real.sqrt (dSquare C s))
      (dNumerator C z/Real.sqrt (dSquare C z)) z := by
    convert (dSquare_hasDerivAt C z).sqrt hD.ne' using 1 <;> ring
  have hr : HasDerivAt (fun s : ℝ => t-s) (-1) z := by
    convert (hasDerivAt_const z t).sub (hasDerivAt_id z) using 1 <;> ring
  have dE := (contact_hasDerivAt R eta (t-z)).comp z hr
  have hlinear := (((((k_hasDerivAt K z).const_mul 3).add ((ell_hasDerivAt L z).const_mul 2)).add
    ((c_hasDerivAt C z).mul (contact_hasDerivAt R eta z))).add dE).add
      ((m_hasDerivAt C eta z).mul_const (Real.cos t-1))
  have hnorm := (((dH.add dA).add dB).add dD).const_mul R
  convert hlinear.sub hnorm using 1 <;>
    dsimp [scalar,slope] <;> ring

/-- The rational expression evaluates to the direct derivative of the
same successive circle roots and the same adapted coefficients. -/
theorem model_value (q u t z : ℝ) :
    CriticalPositiveTModel.derivative.value (CriticalPositiveTModel.values q u t z)=
      slope (Real.sqrt q) (CriticalEFamily.k q t u) (CriticalEFamily.ell q t u)
        (CriticalEFamily.c q t u) (CriticalEFamily.eta q u) t z := by
  simp only [CriticalPositiveTModel.derivative,CriticalPositiveTModel.numeratorH,
    CriticalPositiveTModel.numeratorA,CriticalPositiveTModel.numeratorB,CriticalPositiveTModel.numeratorD,
    CriticalPositiveTModel.normH2,CriticalPositiveTModel.normA2,CriticalPositiveTModel.normB2,
    CriticalPositiveTModel.normD2,CriticalPositiveTModel.contactZ,CriticalPositiveTModel.contactDerivZ,
    CriticalPositiveTModel.contactDerivRest,CriticalPositiveTModel.contactA,CriticalPositiveTModel.radius,
    CriticalPositiveTModel.pDeriv,CriticalPositiveTModel.mDeriv,CriticalPositiveTModel.p,
    CriticalPositiveTModel.m,CriticalPositiveTModel.fZ,CriticalPositiveTModel.k,
    CriticalPositiveTModel.ell,CriticalPositiveTModel.c,CriticalPositiveTModel.ak,
    CriticalPositiveTModel.al,CriticalPositiveTModel.ac,CriticalPositiveTModel.k0,
    CriticalPositiveTModel.ell0,CriticalPositiveTModel.c0,CriticalPositiveTModel.lambda,
    CriticalPositiveTModel.eta,CriticalPositiveTModel.first,CriticalPositiveTModel.second,
    CriticalPositiveTModel.r,CriticalPositiveTModel.upperRight,CriticalPositiveTModel.upperLeft,
    CriticalPositiveTModel.upperHeight,CriticalPositiveTModel.lowerHeight,CriticalPositiveTModel.lowerLeft,
    CriticalPositiveTModel.root,CriticalPositiveTModel.inverseRoot,CriticalPositiveTModel.lit,
    CriticalPositiveTModel.q,CriticalPositiveTModel.u,CriticalPositiveTModel.z,
    CriticalPositiveTModel.sinT,CriticalPositiveTModel.cosT,CriticalPositiveTModel.sinZ,
    CriticalPositiveTModel.cosZ,CriticalPositiveTModel.sinRest,CriticalPositiveTModel.cosRest,
    RoundedRadicalExpression.Expression.value,RoundedBinomialEnclosure.value,CriticalPositiveTModel.values]
  norm_num
  dsimp [slope,hNumerator,aNumerator,bNumerator,dNumerator,hSquare,aSquare,bSquare,dSquare,
    p,pDerivative,contactDerivative,adaptedK,adaptedL,adaptedC,adaptedM,mDerivative,
    contactScalar,tilt,CriticalEFamily.k,CriticalEFamily.ell,CriticalEFamily.c,
    CriticalEFamily.eta,CriticalEFamily.lam,
    ExactFamily.FiveCornerGeometry.firstComponent,ExactFamily.FiveCornerGeometry.secondComponent,
    ExactFamily.FiveCornerGeometry.lowerRight,ExactFamily.FiveCornerGeometry.topRight,
    ExactFamily.FiveCornerGeometry.topLeft,ExactFamily.FiveCornerGeometry.topHeight,
    ExactFamily.FiveCornerGeometry.lowerHeight,ExactFamily.FiveCornerGeometry.lowerLeft,
    ExactFamily.FiveCornerGeometry.upper]
  simp only [div_eq_mul_inv,one_mul]
  ring

end SquaresInCircles.Eight.TableFree.CriticalPositiveTScalar
