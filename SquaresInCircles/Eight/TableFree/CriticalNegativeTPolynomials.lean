module

public import SquaresInCircles.Eight.TableFree.TensorRadicalExpression
public import SquaresInCircles.Eight.TableFree.CriticalEWeightBounds

/-!
# Two whole-strip rationalized negative-T gain certificates

Uncompiled source. The full critical strip is one tensor square:
t=.13+.03X and u=1-.6375t+.00175Y. The original sharp radius
lies in its fixed rational interval and is carried as a remainder.
Both gain formulas retain their rationalized norm differences. Every
root and inverse domain, and the final coefficient bounds, are exact
rational arithmetic obligations; they have not been executed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalNegativeTPolynomials
open TensorPolynomialEnclosure TensorResidualEnclosure TensorRadicalExpression
open Candidate ExactFamily.FiveCornerGeometry

def jD (R l c t : ℝ) : ℝ :=
  (Real.sin t+13/12)/Real.cos t-R*
    (c*Real.sin t/(Real.cos t^2*(Real.sqrt (1+c^2/Real.cos t^2)+Real.sqrt (1+c^2)))+
      2*l/(Real.sqrt (l^2+c^2)+Real.sqrt (l^2+c^2-2*l*c*Real.sin t)))

def shortAngle : ℝ := 9/100

def jB (R l c t : ℝ) : ℝ :=
  let b := shortAngle
  let a := Real.sin b/(1+Real.cos b)
  a*(1/Real.cos b-Real.cos t)+(13/12)/Real.cos b+Real.sin t-R*
    (c*Real.sin b/(Real.cos b^2*(Real.sqrt (l^2+c^2/Real.cos b^2)+Real.sqrt (l^2+c^2)))+
      2*l*(Real.cos t+Real.sin t*a)/
        (Real.sqrt (l^2+c^2-2*l*c*Real.sin (t-b))+
          Real.sqrt (l^2+c^2-2*l*c*Real.sin t)))

abbrev E := Expr (Fin 3)
def timeE : E := .variable 0
def radiusE : E := .variable 1
def positionE : E := .variable 2
def sineE : E := .sine timeE
def cosineE : E := .cosine timeE
def rE : E := .root (radiusE-positionE^2)
def UE : E := .root (radiusE-(2-positionE)^2)
def VE : E := 3-UE
def YE : E := .root (radiusE-VE^2)
def vE : E := 2-YE
def wE : E := .root (radiusE-vE^2)
def firstE : E := 2-cosineE*(rE-1)+sineE*positionE
def secondE : E := 1+cosineE*vE-sineE*(wE-1)
def etaE : E := vE/wE
def lambdaE : E := cosineE+etaE*sineE
def kE : E := lambdaE*VE/YE
def ellE : E := kE*(2-positionE)/UE
def cE : E := firstE/secondE

def normZeroE : E := .root (ellE^2+cE^2)
def normAtE (a : E) : E := .root (ellE^2+cE^2-2*ellE*cE*(.sine a))

def jDE : E :=
  (sineE+.literal (13/12))/cosineE-(.root radiusE)*
    (cE*sineE/(cosineE^2*((.root (1+cE^2/cosineE^2))+(.root (1+cE^2))))+
      2*ellE/(normZeroE+normAtE timeE))

def bE : E := .literal (9/100)
def sinBE : E := .sine bE
def cosBE : E := .cosine bE
def tanHalfBE : E := sinBE/(1+cosBE)
def jBE : E :=
  tanHalfBE*(1/cosBE-cosineE)+(.literal (13/12))/cosBE+sineE-(.root radiusE)*
    (cE*sinBE/(cosBE^2*((.root (ellE^2+cE^2/cosBE^2))+normZeroE))+
      2*ellE*(cosineE+sineE*tanHalfBE)/(normAtE (timeE-bE)+normAtE timeE))

def timeModel : Enclosure := add (constant (13/100)) (mul (constant (3/100)) outerVariable)
def radiusModel : Enclosure :=
  widen (constant ((CriticalEPolynomials.qLower+CriticalEPolynomials.qUpper)/2))
    ((CriticalEPolynomials.qUpper-CriticalEPolynomials.qLower)/2)
def positionModel : Enclosure :=
  add (sub (constant 1) (mul (constant (51/80)) timeModel))
    (mul (constant (7/4000)) innerVariable)
def models : Fin 3 → Enclosure := ![timeModel,radiusModel,positionModel]
def values (q t u : ℝ) : Fin 3 → ℝ := ![t,q,u]

theorem expression_weights (q t u : ℝ) :
    Expr.value (values q t u) ellE=CriticalEFamily.ell q t u ∧
      Expr.value (values q t u) cE=CriticalEFamily.c q t u := by
  simp [ellE,kE,lambdaE,etaE,cE,firstE,secondE,rE,UE,VE,YE,vE,wE,
    timeE,radiusE,positionE,sineE,cosineE,Expr.value,values,
    CriticalEFamily.ell,CriticalEFamily.k,CriticalEFamily.lam,CriticalEFamily.eta,
    CriticalEFamily.c,lowerRight,topRight,topLeft,topHeight,lowerHeight,lowerLeft,
    firstComponent,secondComponent,div_eq_mul_inv]

theorem expression_values (q t u : ℝ) :
    Expr.value (values q t u) jDE=jD (Real.sqrt q) (CriticalEFamily.ell q t u) (CriticalEFamily.c q t u) t ∧
    Expr.value (values q t u) jBE=jB (Real.sqrt q) (CriticalEFamily.ell q t u) (CriticalEFamily.c q t u) t := by
  obtain ⟨hl,hc⟩ := expression_weights q t u
  simp [jDE,jBE,normZeroE,normAtE,bE,sinBE,cosBE,tanHalfBE,timeE,radiusE,
    sineE,cosineE,Expr.value,values,hl,hc,jD,jB,shortAngle,div_eq_mul_inv]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem domains : Expr.Valid models jDE ∧ Expr.Valid models jBE := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem reserves : 0<floor (Expr.enclose models jDE) ∧
    (7/500:ℚ)<floor (Expr.enclose models jBE) := by decide

theorem model_inputs {q t u x y : ℝ}
    (hq : q∈Icc (CriticalEPolynomials.qLower:ℝ) (CriticalEPolynomials.qUpper:ℝ))
    (hx : |x|≤1) (hy : |y|≤1)
    (ht : t=13/100+(3/100)*x) (hu : u=1-(51/80)*t+(7/4000)*y) :
    ∀ i,Contains (models i) x y (values q t u i) := by
  have hc (a : ℚ) := contains_constant a x y
  have htime : Contains timeModel x y t := by
    rw [ht]
    exact (hc (13/100)).add ((hc (3/100)).mul (contains_outer x y) hx hy)
  have hrad : Contains radiusModel x y q := by
    apply (hc ((CriticalEPolynomials.qLower+CriticalEPolynomials.qUpper)/2)).widen
      (by norm_num [CriticalEPolynomials.qLower,CriticalEPolynomials.qUpper])
    rw [abs_le]
    push_cast
    constructor <;> linarith [hq.1,hq.2]
  have hpos : Contains positionModel x y u := by
    rw [hu]
    exact ((hc 1).sub ((hc (51/80)).mul htime hx hy)).add
      ((hc (7/4000)).mul (contains_inner x y) hx hy)
  intro i
  fin_cases i
  · exact htime
  · exact hrad
  · exact hpos

theorem whole_strip {q t u : ℝ}
    (hq : q∈Icc (CriticalEPolynomials.qLower:ℝ) (CriticalEPolynomials.qUpper:ℝ))
    (ht : t∈Icc (1/10:ℝ) (4/25))
    (hu : u∈Icc (499/500-(127/200)*t) (501/500-(16/25)*t)) :
    0<jD (Real.sqrt q) (CriticalEFamily.ell q t u) (CriticalEFamily.c q t u) t ∧
    (7/500:ℝ)<jB (Real.sqrt q) (CriticalEFamily.ell q t u) (CriticalEFamily.c q t u) t := by
  let x : ℝ := (t-13/100)/(3/100)
  let y : ℝ := (u-(1-(51/80)*t))/(7/4000)
  have hx : |x|≤1 := by rw [abs_le]; dsimp [x]; constructor <;> linarith [ht.1,ht.2]
  have hy : |y|≤1 := by rw [abs_le]; dsimp [y]; constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
  have htime : t=13/100+(3/100)*x := by dsimp [x]; ring
  have hpos : u=1-(51/80)*t+(7/4000)*y := by dsimp [y]; ring
  have hi := model_inputs hq hx hy htime hpos
  have hD := (Expr.contains jDE hi hx hy domains.1).lower hx hy
  have hB := (Expr.contains jBE hi hx hy domains.2).lower hx hy
  obtain ⟨heD,heB⟩ := expression_values q t u
  rw [heD] at hD
  rw [heB] at hB
  have hrD : (0:ℝ)<(floor (Expr.enclose models jDE):ℝ) := by exact_mod_cast reserves.1
  have hrB : (7/500:ℝ)<(floor (Expr.enclose models jBE):ℝ) := by exact_mod_cast reserves.2
  exact ⟨hrD.trans_le hD,hrB.trans_le hB⟩

theorem minimizing_strip {q t : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    0<jD (Real.sqrt q) (CriticalEFamily.ell q t (minimizingPosition q t))
      (CriticalEFamily.c q t (minimizingPosition q t)) t ∧
    (7/500:ℝ)<jB (Real.sqrt q) (CriticalEFamily.ell q t (minimizingPosition q t))
      (CriticalEFamily.c q t (minimizingPosition q t)) t := by
  have hq' : q∈Icc (CriticalEPolynomials.qLower:ℝ) (CriticalEPolynomials.qUpper:ℝ) := by
    simpa [CriticalEPolynomials.qLower,CriticalEPolynomials.qUpper,qLow,qTrial] using hq
  have hu := CriticalEPosition.minimizingPosition_strip hq' ht
  exact whole_strip hq' ht ⟨hu.1.le,hu.2.le⟩

end SquaresInCircles.Eight.TableFree.CriticalNegativeTPolynomials
