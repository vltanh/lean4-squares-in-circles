module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDData

/-!
# The eight negative-TD2 endpoint numerators on the whole trapezoid

Uncompiled transcription of equations (28)--(36) of the negative-TD2
nonnegative-total note. Native coordinates are (t,e), with delta=L+t
and a=L+t-e. All masses are exactly the stated cubic polynomials in
these native coordinates, before the one whole-domain substitution.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD.Certificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial

inductive Kind where
  | negative (i : Fin 3)
  | equal
  | positive (i : Fin 3)
  | diagonal
  deriving DecidableEq

instance : Fintype Kind where
  elems := {.equal, .diagonal} ∪
    Finset.univ.image Kind.negative ∪
    Finset.univ.image Kind.positive
  complete x := by cases x <;> simp

abbrev L : ℚ := 1/6
abbrev h : ℚ := 7/10
abbrev d : ℚ := 8/15
abbrev c : ℚ := 27/20
abbrev gamma : ℚ := 18247/20000
abbrev Rbar : ℚ := 494696877/250000000
abbrev abar : ℚ := 176821959/125000000
abbrev cbar : ℚ := 449607033/500000000

def e : Bivar := C X
def delta : Bivar := TensorWholeIntervalPolynomial.scalar L+X
def a : Bivar := delta-e
def b : Bivar := TensorWholeIntervalPolynomial.scalar h-delta
def k : Bivar := TensorWholeIntervalPolynomial.scalar (3/4)+TensorWholeIntervalPolynomial.scalar (7/50)*e
def l : Bivar := TensorWholeIntervalPolynomial.scalar (19/20)+TensorWholeIntervalPolynomial.scalar (9/20)*e
def p : Fin 3→Bivar := ![k,k,l]
def q : Fin 3→Bivar := ![1,l,TensorWholeIntervalPolynomial.scalar c]

def J (u : Bivar) : Bivar :=
  TensorWholeIntervalPolynomial.scalar (1/2)*(lift u PositiveTD.Certificate.C10-1)+
    TensorWholeIntervalPolynomial.scalar (1/2-abar)*lift u PositiveTD.Certificate.S9-TensorWholeIntervalPolynomial.scalar (29/1000)*u^4

def A0 : Bivar := TensorWholeIntervalPolynomial.scalar 2*k+TensorWholeIntervalPolynomial.scalar 3*l+TensorWholeIntervalPolynomial.scalar ((5/2)*c+5/2-(1+c)*cbar)+l*J a+J e

def A : Kind→Bivar
  | .negative i => A0+q i*(lift delta PositiveTD.Certificate.C10-1)
  | .equal => A0+TensorWholeIntervalPolynomial.scalar (gamma*c)*delta
  | .positive i => A0+TensorWholeIntervalPolynomial.scalar (gamma*c*h)+p i*
      (lift b PositiveTD.Certificate.C10+lift b PositiveTD.Certificate.S11-1)
  | .diagonal => A0+TensorWholeIntervalPolynomial.scalar (gamma*c*h)-TensorWholeIntervalPolynomial.scalar (cbar-1/2)*b

def P0 (j : Fin 3) : Bivar := (p j)^2+(q j)^2

def P : Kind→Fin 3→Bivar
  | .negative i,j => P0 j-if i=j then TensorWholeIntervalPolynomial.scalar 2*p j*q j*lift delta PositiveTD.Certificate.S11 else 0
  | .positive i,j => P0 j+if i=j then TensorWholeIntervalPolynomial.scalar 2*p j*q j*lift b PositiveTD.Certificate.S9 else 0
  | _,j => P0 j

def rhoBase : Fin 3→ℚ := ![5/4,302592961/250000000,825378701/500000000]
def rhoNegative : Fin 3→ℚ := ![573074123/500000000,221684281/200000000,75820123/50000000]
def rhoPositive : Fin 3→ℚ := ![1524831081/1000000000,369922233/250000000,2007252551/1000000000]
def rho : Kind→Fin 3→ℚ
  | .negative i,j => if i=j then rhoNegative j else rhoBase j
  | .positive i,j => if i=j then rhoPositive j else rhoBase j
  | _,j => rhoBase j

def mass (f : Kind) (j : Fin 3) : Bivar := cubicMass (rho f j) (P f j)

def numerator (f : Kind) : Bivar :=
  let r := mass f
  TensorWholeIntervalPolynomial.scalar 2*A f*r 0*r 1*r 2-TensorWholeIntervalPolynomial.scalar Rbar*
    ((P f 0+(r 0)^2)*r 1*r 2+(P f 1+(r 1)^2)*r 0*r 2+(P f 2+(r 2)^2)*r 0*r 1)

def degree : Kind→ℕ | .positive _ => 21 | _ => 20
def transform (p : Bivar) : Bivar := trapezoid L d p
def lowerOn (D : ℕ) (p : Bivar) : ℚ := lower D (coefficient D (transform p))
def upperOn (D : ℕ) (p : Bivar) : ℚ := TwoVariablePolynomial.upper D (coefficient D (transform p))
def Domain (t E : ℝ) : Prop := t∈Icc 0 (d:ℝ) ∧ E∈Icc 0 ((L:ℝ)+t)

def wholeReserve : Kind→ℚ
  | .equal => 7/250
  | .positive i => ![21/40,5/8,587/1000] i
  | .diagonal => 553/1000
  | .negative _ => 0

def Whole (f : Kind) : Prop := match f with | .negative _ => False | _ => True

inductive Boundary where | low | equal | high
  deriving DecidableEq

instance : Fintype Boundary where
  elems := {.low, .equal, .high}
  complete x := by cases x <;> decide

def boundaryLength : Boundary→ℚ | .low => L | .equal => d | .high => h
def boundary (j : Boundary) (p : Bivar) : ℚ[X] :=
  match j with
  | .low => restrict p 0 X
  | .equal => restrict p X (C L+X)
  | .high => restrict p (C d) X

def boundaryReserve : Boundary→Fin 3→ℚ
  | .low => ![101/1250,667/10000,3357/10000]
  | .equal => ![609/5000,123/1000,2207/5000]
  | .high => ![117/5000,179/10000,51/100]

def highCentered (i : Fin 3) : ℚ[X] := (boundary .high (numerator (.negative i))).comp (C (7/20)+X)
def highCoefficient (i : Fin 3) (j : ℕ) : ℚ := (highCentered i).coeff j
def highTail (i : Fin 3) : ℚ :=
  ∑j : Fin 18,|highCoefficient i (j.val+3)| *(7/20)^(j.val+1)
def highCurvature (i : Fin 3) : ℚ := highCoefficient i 2-highTail i

def C6 : ℚ[X] := 1-C (1/2)*X^2+C (1/24)*X^4-C (1/720)*X^6
def slopeK : ℚ[X] := C (3/4)+C (7/50)*X
def slopeL : ℚ[X] := C (19/20)+C (9/20)*X
def slopePolynomial : ℚ[X] :=
  C (9789/2500)*(slopeK)^2*(slopeL)^2*C ((C6.eval h)^2)-
    (C (4/5)+slopeL*C (PositiveTD.Certificate.S9.eval h))^2*
      (slopeK^2+slopeL^2-C (2*PositiveTD.Certificate.S11.eval h)*slopeK*slopeL)

theorem domain_angles {t E : ℝ} (hd : Domain t E) :
    NegativeTD.Domain ((L:ℝ)+t) E := by
  dsimp [Domain,NegativeTD.Domain,NegativeTD.L,frameCap,L,d] at *
  exact ⟨⟨by linarith [hd.1.1],by linarith [hd.1.2]⟩,hd.2⟩

theorem domain_of_angles {t E : ℝ} (hd : NegativeTD.Domain t E) : Domain (t-L) E := by
  dsimp [Domain,NegativeTD.Domain,NegativeTD.L,frameCap,L,d] at *
  exact ⟨⟨by linarith [hd.1.1],by linarith [hd.1.2]⟩,
    ⟨hd.2.1,by linarith [hd.2.2]⟩⟩

@[simp] theorem evaluate_e (t E : ℝ) : evaluate t E e=E := by simp [e]
@[simp] theorem evaluate_delta (t E : ℝ) : evaluate t E delta=(L:ℝ)+t := by simp [delta]
@[simp] theorem evaluate_a (t E : ℝ) : evaluate t E a=(L:ℝ)+t-E := by simp [a]
@[simp] theorem evaluate_b (t E : ℝ) : evaluate t E b=(h:ℝ)-((L:ℝ)+t) := by simp [b]
@[simp] theorem evaluate_k (t E : ℝ) : evaluate t E k=NegativeTD.k E := by simp [k,NegativeTD.k]
@[simp] theorem evaluate_l (t E : ℝ) : evaluate t E l=NegativeTD.l E := by simp [l,NegativeTD.l]
@[simp] theorem evaluate_p (t E : ℝ) (i : Fin 3) : evaluate t E (p i)=NegativeTD.p E i.castSucc := by
  fin_cases i <;> simp [p,NegativeTD.p]
@[simp] theorem evaluate_q (t E : ℝ) (i : Fin 3) : evaluate t E (q i)=NegativeTD.q E i.castSucc := by
  fin_cases i <;> simp [q,NegativeTD.q,NegativeTD.c,c]

theorem bounds {D : ℕ} {p : Bivar} (hid : transform p=expansion D (transform p))
    {t E : ℝ} (hd : Domain t E) :
    (lowerOn D p:ℝ)≤evaluate t E p ∧ evaluate t E p≤(upperOn D p:ℝ) :=
  trapezoid_bounds (by norm_num [L]) (by norm_num [d]) hid hd.1 hd.2

theorem positive_on_domain {D : ℕ} {p : Bivar} {v : ℚ}
    (hid : transform p=expansion D (transform p)) (hv : v<lowerOn D p)
    {t E : ℝ} (hd : Domain t E) : (v:ℝ)<evaluate t E p := by
  have hh : (v:ℝ)<(lowerOn D p:ℝ) := by exact_mod_cast hv
  exact hh.trans_le (bounds hid hd).1

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD.Certificate
