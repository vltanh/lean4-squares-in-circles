module

public import SquaresInCircles.Eight.TableFree.RoundedRadicalExpression
public import SquaresInCircles.Eight.TableFree.CriticalEExclusion

/-!
# The single whole-triangle positive-T derivative model

Uncompiled transcription of equations (35)--(44) in
`HAND_G5_EXCEPTIONAL_E_ALIGNED_POSITIVE_T_CRITICAL_STRIP.md`.
The expression below is the displayed chain and its displayed derivative,
in their original order. Every radical and reciprocal uses the rounded
degree-twelve binomial rule. The polynomial has total degree at most ten;
there is no angular subdivision or inventory of precomputed coefficients.

The exact rational checks are left as ordinary kernel `decide` proofs.
No certificate has been evaluated during this drafting stage.
-/

@[expose] public section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalPositiveTModel
open RoundedTensorEnclosure RoundedRadicalExpression

inductive Input where
  | q | u | t | z | sinT | cosT | sinZ | cosZ | sinRest | cosRest
  deriving DecidableEq, Fintype

abbrev Expr := Expression Input
def lit (a : ℚ) : Expr := .literal a
def root (a : Expr) : Expr := .binomial .root a
def inverseRoot (a : Expr) : Expr := .binomial .inverseRoot a
def q : Expr := .variable .q
def u : Expr := .variable .u
def t : Expr := .variable .t
def z : Expr := .variable .z
def sinT : Expr := .variable .sinT
def cosT : Expr := .variable .cosT
def sinZ : Expr := .variable .sinZ
def cosZ : Expr := .variable .cosZ
def sinRest : Expr := .variable .sinRest
def cosRest : Expr := .variable .cosRest

/- The successive circle roots in (6). -/
def r : Expr := root (q-u^2)
def upperRight : Expr := root (q-(2-u)^2)
def upperLeft : Expr := 3-upperRight
def upperHeight : Expr := root (q-upperLeft^2)
def lowerHeight : Expr := 2-upperHeight
def lowerLeft : Expr := root (q-lowerHeight^2)
def first : Expr := 2-cosT*(r-1)+sinT*u
def second : Expr := 1+cosT*lowerHeight-sinT*(lowerLeft-1)
def eta : Expr := lowerHeight/lowerLeft
def lambda : Expr := cosT+eta*sinT
def k0 : Expr := lambda*upperLeft/upperHeight
def ell0 : Expr := k0*(2-u)/upperRight
def c0 : Expr := first/second

/- The adaptation and the four differentiated norm numerators. -/
def ak : Expr := lit (3/50)
def al : Expr := lit (-23/100)
def ac : Expr := lit (-53/100)
def k : Expr := k0+ak*z
def ell : Expr := ell0+al*z
def c : Expr := c0+ac*z
def fZ : Expr := cosZ+eta*sinZ
def p : Expr := cosRest+eta*sinRest
def m : Expr := c*fZ
def pDeriv : Expr := sinRest-eta*cosRest
def mDeriv : Expr := ac*fZ+c*(-sinZ+eta*cosZ)
def radius : Expr := root q
def contactA : Expr := 1+2*eta-radius*root (1+eta^2)
def contactZ : Expr := 1+2*cosZ+contactA*sinZ
def contactDerivZ : Expr := -2*sinZ+contactA*cosZ
def contactDerivRest : Expr := -2*sinRest+contactA*cosRest
def normH2 : Expr := p^2+k^2
def normA2 : Expr := k^2+ell^2
def normB2 : Expr := ell^2+m^2-2*ell*m*sinT
def normD2 : Expr := 1+c^2
def numeratorH : Expr := p*pDeriv+k*ak
def numeratorA : Expr := k*ak+ell*al
def numeratorB : Expr := ell*al+m*mDeriv-(al*m+ell*mDeriv)*sinT
def numeratorD : Expr := c*ac

/-- Exactly the differentiated expression (36). Reciprocal norms use
exponent -1/2 directly, as specified in the polynomial builder. -/
def derivative : Expr :=
  3*ak+2*al+ac*contactZ+c*contactDerivZ-contactDerivRest+
    mDeriv*(cosT-1)-radius*(
      numeratorH*inverseRoot normH2+numeratorA*inverseRoot normA2+
      numeratorB*inverseRoot normB2+numeratorD*inverseRoot normD2)

def qMid : ℚ := ((19577/5000)+(1957767069/500000000))/2
def qWidth : ℚ := ((1957767069/500000000)-(19577/5000))/2
def qModel : Enclosure :=
  round ⟨TensorWholeIntervalPolynomial.scalar qMid,qWidth⟩
def tModel : Enclosure := add (constant (13/100)) (scale (3/100) outerVariable)
def zModel : Enclosure := scale (1/2) (mul tModel (add (constant 1) innerVariable))
def uModel : Enclosure := widen (sub (constant 1) (scale (51/80) tModel)) (7/4000)
def restModel : Enclosure := sub tModel zModel
def models : Input→Enclosure
  | .q => qModel
  | .u => uModel
  | .t => tModel
  | .z => zModel
  | .sinT => sine tModel
  | .cosT => cosine tModel
  | .sinZ => sine zModel
  | .cosZ => cosine zModel
  | .sinRest => sine restModel
  | .cosRest => cosine restModel
def enclosure : Enclosure := derivative.model models

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem all_binomial_arguments : derivative.safe models=true := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem constant_coefficient : (4183/100000:ℚ)<center enclosure := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem remaining_coefficients :
    norm (enclosure.polynomial-TensorWholeIntervalPolynomial.scalar (center enclosure))<
      (973/50000:ℚ) := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem error_bound : enclosure.error<(2053/100000:ℚ) := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem uniform_reserve : (9/5000:ℚ)<RoundedTensorEnclosure.floor enclosure := by decide

noncomputable section

def values (Q U T Z : ℝ) : Input→ℝ
  | .q => Q
  | .u => U
  | .t => T
  | .z => Z
  | .sinT => Real.sin T
  | .cosT => Real.cos T
  | .sinZ => Real.sin Z
  | .cosZ => Real.cos Z
  | .sinRest => Real.sin (T-Z)
  | .cosRest => Real.cos (T-Z)

def outerCoordinate (T : ℝ) : ℝ := (T-13/100)/(3/100)
def innerCoordinate (T Z : ℝ) : ℝ := 2*Z/T-1

theorem coordinates_mem {T Z : ℝ} (hT : T∈Icc (1/10:ℝ) (4/25))
    (hZ : Z∈Icc 0 T) :
    |outerCoordinate T|≤1 ∧ |innerCoordinate T Z|≤1 := by
  have hT0 : 0<T := by linarith [hT.1]
  constructor
  · rw [abs_le]
    dsimp [outerCoordinate]
    constructor <;> norm_num <;> linarith [hT.1,hT.2]
  · rw [abs_le]
    dsimp [innerCoordinate]
    constructor
    · have h := div_nonneg (show 0≤2*Z by linarith [hZ.1]) hT0.le
      linarith
    · have h : 2*Z/T≤2 := (div_le_iff₀ hT0).2 (by linarith [hZ.2])
      linarith

theorem position_error {T U : ℝ} (hT : T∈Icc (1/10:ℝ) (4/25))
    (hU : 499/500-127/200*T<U ∧ U<501/500-16/25*T) :
    |U-(1-51/80*T)|≤7/4000 := by
  rw [abs_le]
  constructor <;> linarith [hU.1,hU.2,hT.1]

theorem input_contains {Q U T Z : ℝ} (hQ : Q∈Icc qLow qTrial)
    (hT : T∈Icc (1/10:ℝ) (4/25)) (hZ : Z∈Icc 0 T)
    (hU : 499/500-127/200*T<U ∧ U<501/500-16/25*T) :
    ∀i,Contains (models i) (outerCoordinate T) (innerCoordinate T Z) (values Q U T Z i) := by
  obtain ⟨hX,hY⟩ := coordinates_mem hT hZ
  have hT0 : 0<T := by linarith [hT.1]
  have hTm : Contains tModel (outerCoordinate T) (innerCoordinate T Z) T := by
    have h := contains_add (contains_constant (13/100) hX hY)
      (contains_scale (contains_outer hX hY) (3/100) hX hY) hX hY
    convert h using 1 <;> norm_num [tModel,outerCoordinate] <;> ring
  have hZm : Contains zModel (outerCoordinate T) (innerCoordinate T Z) Z := by
    have h := contains_scale (contains_mul hTm
      (contains_add (contains_constant 1 hX hY) (contains_inner hX hY) hX hY) hX hY)
      (1/2) hX hY
    convert h using 1
    dsimp [innerCoordinate]
    field_simp [hT0.ne']
    ring
  have hUm : Contains uModel (outerCoordinate T) (innerCoordinate T Z) U := by
    apply contains_widen
      (contains_sub (contains_constant 1 hX hY) (contains_scale hTm (51/80) hX hY) hX hY)
      (by norm_num) ?_ hX hY
    norm_num
    exact position_error hT hU
  have hQm : Contains qModel (outerCoordinate T) (innerCoordinate T Z) Q := by
    apply contains_round ?_ hX hY
    refine ⟨by norm_num [qWidth],?_⟩
    simp only [TensorWholeIntervalPolynomial.evaluate_scalar]
    rw [abs_le]
    norm_num [qMid,qWidth,qLow,qTrial] at hQ ⊢
    constructor <;> linarith [hQ.1,hQ.2]
  have hRm := contains_sub hTm hZm hX hY
  have hTF : T∈Icc 0 frameCap := ⟨by linarith [hT.1],by norm_num [frameCap]; linarith [hT.2]⟩
  have hZF : Z∈Icc 0 frameCap := ⟨hZ.1,hZ.2.trans hTF.2⟩
  have hRF : T-Z∈Icc 0 frameCap := ⟨by linarith [hZ.2],by linarith [hZ.1,hTF.2]⟩
  intro i
  cases i
  · exact hQm
  · exact hUm
  · exact hTm
  · exact hZm
  · exact contains_sine hTm hX hY hTF
  · exact contains_cosine hTm hX hY hTF
  · exact contains_sine hZm hX hY hZF
  · exact contains_cosine hZm hX hY hZF
  · exact contains_sine hRm hX hY hRF
  · exact contains_cosine hRm hX hY hRF

/-- The model encloses the explicit real expression for every q,u in
the printed strips independently, before choosing the exact minimizer. -/
theorem derivative_lower {Q U T Z : ℝ} (hQ : Q∈Icc qLow qTrial)
    (hT : T∈Icc (1/10:ℝ) (4/25)) (hZ : Z∈Icc 0 T)
    (hU : 499/500-127/200*T<U ∧ U<501/500-16/25*T) :
    9/5000<derivative.value (values Q U T Z) := by
  obtain ⟨hX,hY⟩ := coordinates_mem hT hZ
  have hc := derivative.contains (input_contains hQ hT hZ hU) hX hY all_binomial_arguments
  have hl := RoundedTensorEnclosure.lower hc hX hY
  have hr : (9/5000:ℝ)<(RoundedTensorEnclosure.floor enclosure:ℝ) := by
    exact_mod_cast uniform_reserve
  exact hr.trans_le hl

theorem minimizing_derivative_lower {Q T Z : ℝ} (hQ : Q∈Icc qLow qTrial)
    (hT : T∈Icc (1/10:ℝ) (4/25)) (hZ : Z∈Icc 0 T) :
    9/5000<derivative.value
      (values Q (ExactFamily.FiveCornerGeometry.minimizingPosition Q T) T Z) := by
  apply derivative_lower hQ hT hZ
  exact CriticalEPosition.minimizingPosition_strip
    (by simpa [CriticalEPolynomials.qLower,CriticalEPolynomials.qUpper,qLow,qTrial] using hQ) hT

end
end SquaresInCircles.Eight.TableFree.CriticalPositiveTModel
