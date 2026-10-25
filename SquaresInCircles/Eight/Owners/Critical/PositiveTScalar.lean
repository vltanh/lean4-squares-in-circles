module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import SquaresInCircles.Eight.Owners.Critical.EWeightBounds
public import SquaresInCircles.Eight.Owners.Critical.PositiveTModel

/-!
# Eight squares: the differentiated adapted ET scalar

The original
supporting dual is held fixed while z varies. Positivity of all four norm
radicands follows from the proved coefficient ranges. This file computes
the derivative by the ordinary product and square-root rules and connects
it to the one whole-triangle rational model.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalPositiveTScalar
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
  have h : HasDerivAt (fun x : ℝ => K+3/50*x) (3/50) z := by
    simpa using ((hasDerivAt_id z).const_mul (3/50:ℝ)).const_add K
  exact h
theorem ell_hasDerivAt (L z : ℝ) : HasDerivAt (adaptedL L) (-23/100) z := by
  have h : HasDerivAt (fun x : ℝ => L-23/100*x) (-23/100) z :=
    (((hasDerivAt_id z).const_mul (23/100:ℝ)).const_sub L).congr_deriv (by norm_num)
  exact h
theorem c_hasDerivAt (C z : ℝ) : HasDerivAt (adaptedC C) (-53/100) z := by
  have h : HasDerivAt (fun x : ℝ => C-53/100*x) (-53/100) z :=
    (((hasDerivAt_id z).const_mul (53/100:ℝ)).const_sub C).congr_deriv (by norm_num)
  exact h
private theorem r52_sub_hasDerivAt (t z : ℝ) : HasDerivAt (fun s : ℝ => t-s) (-1) z := by
  simpa using (hasDerivAt_id z).const_sub t
theorem p_hasDerivAt (eta t z : ℝ) : HasDerivAt (p eta t) (pDerivative eta t z) z := by
  have hr := r52_sub_hasDerivAt t z
  have h1 : HasDerivAt (fun s => Real.cos (t-s)) (-Real.sin (t-z)*(-1)) z :=
    (Real.hasDerivAt_cos (t-z)).comp z hr
  have h2 : HasDerivAt (fun s => Real.sin (t-s)) (Real.cos (t-z)*(-1)) z :=
    (Real.hasDerivAt_sin (t-z)).comp z hr
  have h : HasDerivAt (fun s => Real.cos (t-s)+eta*Real.sin (t-s)) (pDerivative eta t z) z :=
    (h1.add (h2.const_mul eta)).congr_deriv (by simp only [pDerivative]; ring)
  exact h
theorem contact_hasDerivAt (R eta z : ℝ) :
    HasDerivAt (contactScalar R eta) (contactDerivative R eta z) z := by
  have h1 : HasDerivAt (fun s => 1+2*Real.cos s) (2*(-Real.sin z)) z :=
    ((Real.hasDerivAt_cos z).const_mul 2).const_add 1
  have h2 : HasDerivAt (fun s => (1+2*eta-R*Real.sqrt (1+eta^2))*Real.sin s)
      ((1+2*eta-R*Real.sqrt (1+eta^2))*Real.cos z) z :=
    (Real.hasDerivAt_sin z).const_mul _
  have h : HasDerivAt (fun s => 1+2*Real.cos s+(1+2*eta-R*Real.sqrt (1+eta^2))*Real.sin s)
      (contactDerivative R eta z) z :=
    (h1.add h2).congr_deriv (by simp only [contactDerivative]; ring)
  exact h

theorem hSquare_hasDerivAt (K eta t z : ℝ) :
    HasDerivAt (hSquare K eta t) (2*hNumerator K eta t z) z := by
  have h1 : HasDerivAt (fun s => p eta t s^2) (2*p eta t z^(2-1)*pDerivative eta t z) z :=
    (p_hasDerivAt eta t z).pow 2
  have h2 : HasDerivAt (fun s => adaptedK K s^2) (2*adaptedK K z^(2-1)*(3/50)) z :=
    (k_hasDerivAt K z).pow 2
  have h : HasDerivAt (fun s => p eta t s^2+adaptedK K s^2) (2*hNumerator K eta t z) z :=
    (h1.add h2).congr_deriv (by simp only [hNumerator]; ring)
  exact h
theorem aSquare_hasDerivAt (K L z : ℝ) :
    HasDerivAt (aSquare K L) (2*aNumerator K L z) z := by
  have h1 : HasDerivAt (fun s => adaptedK K s^2) (2*adaptedK K z^(2-1)*(3/50)) z :=
    (k_hasDerivAt K z).pow 2
  have h2 : HasDerivAt (fun s => adaptedL L s^2) (2*adaptedL L z^(2-1)*(-23/100)) z :=
    (ell_hasDerivAt L z).pow 2
  have h : HasDerivAt (fun s => adaptedK K s^2+adaptedL L s^2) (2*aNumerator K L z) z :=
    (h1.add h2).congr_deriv (by simp only [aNumerator]; ring)
  exact h
theorem bSquare_hasDerivAt (L C eta t z : ℝ) :
    HasDerivAt (bSquare L C eta t) (2*bNumerator L C eta t z) z := by
  have hl := ell_hasDerivAt L z
  have hm := m_hasDerivAt C eta z
  have h1 : HasDerivAt (fun s => adaptedL L s^2) (2*adaptedL L z^(2-1)*(-23/100)) z := hl.pow 2
  have h2 : HasDerivAt (fun s => adaptedM C eta s^2)
      (2*adaptedM C eta z^(2-1)*mDerivative C eta z) z := hm.pow 2
  have h3 : HasDerivAt (fun s => 2*adaptedL L s*adaptedM C eta s*Real.sin t)
      ((2*(-23/100)*adaptedM C eta z+2*adaptedL L z*mDerivative C eta z)*Real.sin t) z :=
    ((hl.const_mul 2).mul hm).mul_const (Real.sin t)
  have h : HasDerivAt (fun s => adaptedL L s^2+adaptedM C eta s^2-
      2*adaptedL L s*adaptedM C eta s*Real.sin t) (2*bNumerator L C eta t z) z :=
    ((h1.add h2).sub h3).congr_deriv (by simp only [bNumerator]; ring)
  exact h
theorem dSquare_hasDerivAt (C z : ℝ) :
    HasDerivAt (dSquare C) (2*dNumerator C z) z := by
  have h1 : HasDerivAt (fun s => adaptedC C s^2) (2*adaptedC C z^(2-1)*(-53/100)) z :=
    (c_hasDerivAt C z).pow 2
  have h : HasDerivAt (fun s => 1+adaptedC C s^2) (2*dNumerator C z) z :=
    (h1.const_add 1).congr_deriv (by simp only [dNumerator]; ring)
  exact h

theorem hasDerivAt_scalar {R K L C eta t z : ℝ}
    (h : CriticalECoefficients.Bounds t K L C eta) (hz : z∈Icc 0 t) :
    HasDerivAt (scalar R K L C eta t) (slope R K L C eta t z) z := by
  obtain ⟨hH,hA,hB,hD⟩ := radicands_positive h hz
  have dH : HasDerivAt (fun s => Real.sqrt (hSquare K eta t s))
      (2*hNumerator K eta t z/(2*Real.sqrt (hSquare K eta t z))) z :=
    (hSquare_hasDerivAt K eta t z).sqrt hH.ne'
  have dA : HasDerivAt (fun s => Real.sqrt (aSquare K L s))
      (2*aNumerator K L z/(2*Real.sqrt (aSquare K L z))) z :=
    (aSquare_hasDerivAt K L z).sqrt hA.ne'
  have dB : HasDerivAt (fun s => Real.sqrt (bSquare L C eta t s))
      (2*bNumerator L C eta t z/(2*Real.sqrt (bSquare L C eta t z))) z :=
    (bSquare_hasDerivAt L C eta t z).sqrt hB.ne'
  have dD : HasDerivAt (fun s => Real.sqrt (dSquare C s))
      (2*dNumerator C z/(2*Real.sqrt (dSquare C z))) z :=
    (dSquare_hasDerivAt C z).sqrt hD.ne'
  have dE : HasDerivAt (fun s => contactScalar R eta (t-s))
      (contactDerivative R eta (t-z)*(-1)) z :=
    (contact_hasDerivAt R eta (t-z)).comp z (r52_sub_hasDerivAt t z)
  have dK : HasDerivAt (fun s => 3*adaptedK K s) (3*(3/50)) z := (k_hasDerivAt K z).const_mul 3
  have dL : HasDerivAt (fun s => 2*adaptedL L s) (2*(-23/100)) z :=
    (ell_hasDerivAt L z).const_mul 2
  have dC : HasDerivAt (fun s => adaptedC C s*contactScalar R eta s)
      ((-53/100)*contactScalar R eta z+adaptedC C z*contactDerivative R eta z) z :=
    (c_hasDerivAt C z).mul (contact_hasDerivAt R eta z)
  have dM : HasDerivAt (fun s => adaptedM C eta s*(Real.cos t-1))
      (mDerivative C eta z*(Real.cos t-1)) z := (m_hasDerivAt C eta z).mul_const _
  have dN : HasDerivAt (fun s => R*(Real.sqrt (hSquare K eta t s)+Real.sqrt (aSquare K L s)+
      Real.sqrt (bSquare L C eta t s)+Real.sqrt (dSquare C s)))
      (R*(2*hNumerator K eta t z/(2*Real.sqrt (hSquare K eta t z))+
        2*aNumerator K L z/(2*Real.sqrt (aSquare K L z))+
        2*bNumerator L C eta t z/(2*Real.sqrt (bSquare L C eta t z))+
        2*dNumerator C z/(2*Real.sqrt (dSquare C z)))) z :=
    (((dH.add dA).add dB).add dD).const_mul R
  have hall : HasDerivAt (fun s => 3*adaptedK K s+2*adaptedL L s+
      adaptedC C s*contactScalar R eta s+contactScalar R eta (t-s)+
      adaptedM C eta s*(Real.cos t-1)-
      R*(Real.sqrt (hSquare K eta t s)+Real.sqrt (aSquare K L s)+
        Real.sqrt (bSquare L C eta t s)+Real.sqrt (dSquare C s)))
      (slope R K L C eta t z) z :=
    (((((dK.add dL).add dC).add dE).add dM).sub dN).congr_deriv (by simp only [slope]; ring)
  exact hall

section r52_value
open RoundedRadicalExpression
variable {ι : Type*} (v : ι→ℝ)
private theorem r52_value_add (a b : Expression ι) :
    (a+b).value v=a.value v+b.value v := rfl
private theorem r52_value_neg (a : Expression ι) : (-a).value v= -a.value v := rfl
private theorem r52_value_sub (a b : Expression ι) :
    (a-b).value v=a.value v-b.value v := by
  change a.value v+ -b.value v=_
  ring
private theorem r52_value_mul (a b : Expression ι) :
    (a*b).value v=a.value v*b.value v := rfl
private theorem r52_value_pow (a : Expression ι) (n : ℕ) :
    (a^n).value v=a.value v^n := rfl
private theorem r52_value_div (a b : Expression ι) :
    (a/b).value v=a.value v*(1/b.value v) := rfl
private theorem r52_value_two : (2 : Expression ι).value v=2 := by
  change (((2:ℕ):ℚ):ℝ)=_
  norm_num
private theorem r52_value_three : (3 : Expression ι).value v=3 := by
  change (((3:ℕ):ℚ):ℝ)=_
  norm_num
private theorem r52_value_one : (1 : Expression ι).value v=1 := by
  change (((1:ℕ):ℚ):ℝ)=_
  simp
private theorem r52_value_binomial (e : RoundedBinomialEnclosure.Exponent) (a : Expression ι) :
    (Expression.binomial e a).value v=RoundedBinomialEnclosure.value e (a.value v) := rfl
end r52_value

/-- The rational expression evaluates to the direct derivative of the
same successive circle roots and the same adapted coefficients. -/
theorem model_value (q u t z : ℝ) :
    CriticalPositiveTModel.derivative.value (CriticalPositiveTModel.values q u t z)=
      slope (Real.sqrt q) (CriticalEFamily.k q t u) (CriticalEFamily.ell q t u)
        (CriticalEFamily.c q t u) (CriticalEFamily.eta q u) t z := by
  set V := CriticalPositiveTModel.values q u t z with hV
  set E := CriticalEFamily.eta q u with hE
  set K := CriticalEFamily.k q t u with hK
  set L := CriticalEFamily.ell q t u with hL
  set C := CriticalEFamily.c q t u with hC
  have vq : CriticalPositiveTModel.q.value V=q := rfl
  have vu : CriticalPositiveTModel.u.value V=u := rfl
  have vz : CriticalPositiveTModel.z.value V=z := rfl
  have vsT : CriticalPositiveTModel.sinT.value V=Real.sin t := rfl
  have vcT : CriticalPositiveTModel.cosT.value V=Real.cos t := rfl
  have vsZ : CriticalPositiveTModel.sinZ.value V=Real.sin z := rfl
  have vcZ : CriticalPositiveTModel.cosZ.value V=Real.cos z := rfl
  have vsR : CriticalPositiveTModel.sinRest.value V=Real.sin (t-z) := rfl
  have vcR : CriticalPositiveTModel.cosRest.value V=Real.cos (t-z) := rfl
  have v1 := r52_value_one (ι := CriticalPositiveTModel.Input) V
  have v2 := r52_value_two (ι := CriticalPositiveTModel.Input) V
  have v3 := r52_value_three (ι := CriticalPositiveTModel.Input) V
  have vak : CriticalPositiveTModel.ak.value V=3/50 := by
    change ((3/50:ℚ):ℝ)=_
    push_cast; ring
  have val : CriticalPositiveTModel.al.value V=-23/100 := by
    change ((-23/100:ℚ):ℝ)=_
    push_cast; ring
  have vac : CriticalPositiveTModel.ac.value V=-53/100 := by
    change ((-53/100:ℚ):ℝ)=_
    push_cast; ring
  have vr : CriticalPositiveTModel.r.value V=Stationary.FiveCornerGeometry.lowerRight q u := by
    simp only [CriticalPositiveTModel.r,CriticalPositiveTModel.root,r52_value_binomial,
      r52_value_sub,r52_value_pow,vq,vu,RoundedBinomialEnclosure.value,
      Stationary.FiveCornerGeometry.lowerRight,Stationary.FiveCornerGeometry.upper]
  have vuR : CriticalPositiveTModel.upperRight.value V=
      Stationary.FiveCornerGeometry.topRight q u := by
    simp only [CriticalPositiveTModel.upperRight,CriticalPositiveTModel.root,r52_value_binomial,
      r52_value_sub,r52_value_pow,vq,vu,v2,RoundedBinomialEnclosure.value,
      Stationary.FiveCornerGeometry.topRight,Stationary.FiveCornerGeometry.upper]
  have vuL : CriticalPositiveTModel.upperLeft.value V=
      Stationary.FiveCornerGeometry.topLeft q u := by
    simp only [CriticalPositiveTModel.upperLeft,r52_value_sub,v3,vuR,
      Stationary.FiveCornerGeometry.topLeft]
  have vuH : CriticalPositiveTModel.upperHeight.value V=
      Stationary.FiveCornerGeometry.topHeight q u := by
    simp only [CriticalPositiveTModel.upperHeight,CriticalPositiveTModel.root,r52_value_binomial,
      r52_value_sub,r52_value_pow,vq,vuL,RoundedBinomialEnclosure.value,
      Stationary.FiveCornerGeometry.topHeight,Stationary.FiveCornerGeometry.upper]
  have vlH : CriticalPositiveTModel.lowerHeight.value V=
      Stationary.FiveCornerGeometry.lowerHeight q u := by
    simp only [CriticalPositiveTModel.lowerHeight,r52_value_sub,v2,vuH,
      Stationary.FiveCornerGeometry.lowerHeight]
  have vlL : CriticalPositiveTModel.lowerLeft.value V=
      Stationary.FiveCornerGeometry.lowerLeft q u := by
    simp only [CriticalPositiveTModel.lowerLeft,CriticalPositiveTModel.root,r52_value_binomial,
      r52_value_sub,r52_value_pow,vq,vlH,RoundedBinomialEnclosure.value,
      Stationary.FiveCornerGeometry.lowerLeft,Stationary.FiveCornerGeometry.upper]
  have veta : CriticalPositiveTModel.eta.value V=E := by
    simp only [CriticalPositiveTModel.eta,r52_value_div,vlH,vlL,
      hE,CriticalEFamily.eta]
    ring
  have vk0 : CriticalPositiveTModel.k0.value V=K := by
    simp only [CriticalPositiveTModel.k0,CriticalPositiveTModel.lambda,r52_value_div,
      r52_value_add,r52_value_mul,vcT,vsT,veta,vuL,vuH,
      hK,CriticalEFamily.k,CriticalEFamily.lam]
    ring
  have vell0 : CriticalPositiveTModel.ell0.value V=L := by
    simp only [CriticalPositiveTModel.ell0,r52_value_div,r52_value_sub,
      r52_value_mul,vk0,v2,vu,vuR,hL,CriticalEFamily.ell]
    ring
  have vc0 : CriticalPositiveTModel.c0.value V=C := by
    simp only [CriticalPositiveTModel.c0,CriticalPositiveTModel.first,CriticalPositiveTModel.second,
      r52_value_div,r52_value_sub,r52_value_add,r52_value_mul,
      v1,v2,vu,vcT,vsT,vr,vlH,vlL,hC,CriticalEFamily.c,
      Stationary.FiveCornerGeometry.firstComponent,Stationary.FiveCornerGeometry.secondComponent]
    ring
  have vk : CriticalPositiveTModel.k.value V=adaptedK K z := by
    simp only [CriticalPositiveTModel.k,r52_value_add,r52_value_mul,vk0,vak,vz,adaptedK]
  have vell : CriticalPositiveTModel.ell.value V=adaptedL L z := by
    simp only [CriticalPositiveTModel.ell,r52_value_add,r52_value_mul,vell0,val,vz,adaptedL]
    ring
  have vc : CriticalPositiveTModel.c.value V=adaptedC C z := by
    simp only [CriticalPositiveTModel.c,r52_value_add,r52_value_mul,vc0,vac,vz,adaptedC]
    ring
  have vfZ : CriticalPositiveTModel.fZ.value V=tilt E z := by
    simp only [CriticalPositiveTModel.fZ,r52_value_add,r52_value_mul,vcZ,vsZ,veta,tilt]
  have vp : CriticalPositiveTModel.p.value V=p E t z := by
    simp only [CriticalPositiveTModel.p,r52_value_add,r52_value_mul,vcR,vsR,veta,p,tilt]
  have vm : CriticalPositiveTModel.m.value V=adaptedM C E z := by
    simp only [CriticalPositiveTModel.m,r52_value_mul,vc,vfZ,adaptedM]
  have vpD : CriticalPositiveTModel.pDeriv.value V=pDerivative E t z := by
    simp only [CriticalPositiveTModel.pDeriv,r52_value_sub,r52_value_mul,vcR,vsR,veta,pDerivative]
  have vmD : CriticalPositiveTModel.mDeriv.value V=mDerivative C E z := by
    simp only [CriticalPositiveTModel.mDeriv,r52_value_add,r52_value_neg,r52_value_mul,vac,vfZ,vc,
      vsZ,vcZ,veta,mDerivative]
    ring
  have vrad : CriticalPositiveTModel.radius.value V=Real.sqrt q := by
    simp only [CriticalPositiveTModel.radius,CriticalPositiveTModel.root,r52_value_binomial,vq,
      RoundedBinomialEnclosure.value]
  have vcA : CriticalPositiveTModel.contactA.value V=1+2*E-Real.sqrt q*Real.sqrt (1+E^2) := by
    simp only [CriticalPositiveTModel.contactA,CriticalPositiveTModel.root,r52_value_binomial,
      r52_value_sub,r52_value_add,r52_value_mul,r52_value_pow,v1,v2,veta,vrad,
      RoundedBinomialEnclosure.value]
  have vcZz : CriticalPositiveTModel.contactZ.value V=contactScalar (Real.sqrt q) E z := by
    simp only [CriticalPositiveTModel.contactZ,r52_value_add,r52_value_mul,v1,v2,vcZ,vsZ,vcA,
      contactScalar]
  have vcDZ : CriticalPositiveTModel.contactDerivZ.value V=
      contactDerivative (Real.sqrt q) E z := by
    simp only [CriticalPositiveTModel.contactDerivZ,r52_value_add,r52_value_neg,r52_value_mul,v2,
      vcZ,vsZ,vcA,contactDerivative]
  have vcDR : CriticalPositiveTModel.contactDerivRest.value V=
      contactDerivative (Real.sqrt q) E (t-z) := by
    simp only [CriticalPositiveTModel.contactDerivRest,r52_value_add,r52_value_neg,r52_value_mul,
      v2,vcR,vsR,vcA,contactDerivative]
  have vH2 : CriticalPositiveTModel.normH2.value V=hSquare K E t z := by
    simp only [CriticalPositiveTModel.normH2,r52_value_add,r52_value_pow,vp,vk,hSquare]
  have vA2 : CriticalPositiveTModel.normA2.value V=aSquare K L z := by
    simp only [CriticalPositiveTModel.normA2,r52_value_add,r52_value_pow,vk,vell,aSquare]
  have vB2 : CriticalPositiveTModel.normB2.value V=bSquare L C E t z := by
    simp only [CriticalPositiveTModel.normB2,r52_value_sub,r52_value_add,r52_value_mul,
      r52_value_pow,v2,vell,vm,vsT,bSquare]
  have vD2 : CriticalPositiveTModel.normD2.value V=dSquare C z := by
    simp only [CriticalPositiveTModel.normD2,r52_value_add,r52_value_pow,v1,vc,dSquare]
  have vnH : CriticalPositiveTModel.numeratorH.value V=hNumerator K E t z := by
    simp only [CriticalPositiveTModel.numeratorH,r52_value_add,r52_value_mul,vp,vpD,vk,vak,
      hNumerator]
  have vnA : CriticalPositiveTModel.numeratorA.value V=aNumerator K L z := by
    simp only [CriticalPositiveTModel.numeratorA,r52_value_add,r52_value_mul,vk,vak,vell,val,
      aNumerator]
  have vnB : CriticalPositiveTModel.numeratorB.value V=bNumerator L C E t z := by
    simp only [CriticalPositiveTModel.numeratorB,r52_value_sub,r52_value_add,r52_value_mul,
      vell,val,vm,vmD,vsT,bNumerator]
  have vnD : CriticalPositiveTModel.numeratorD.value V=dNumerator C z := by
    simp only [CriticalPositiveTModel.numeratorD,r52_value_mul,vc,vac,dNumerator]
  simp only [CriticalPositiveTModel.derivative,CriticalPositiveTModel.inverseRoot,r52_value_sub,
    r52_value_add,r52_value_mul,r52_value_binomial,v2,v3,vak,val,vac,vcZz,vc,vcDZ,vcDR,vmD,vcT,v1,
    vrad,vnH,vnA,vnB,vnD,vH2,vA2,vB2,vD2,RoundedBinomialEnclosure.value,slope]
  ring

end SquaresInCircles.Eight.CriticalPositiveTScalar
