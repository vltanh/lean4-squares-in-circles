module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDCertificates

/-!
# The eight paired nonpositive-T endpoint numerators

Uncompiled transcription of Sections 8--9 of the nonpositive signed
T-total note.  The five low endpoints use the entire native trapezoid
L≤delta≤M.  The three shifted V endpoints use M≤delta≤h, retaining
their three original boundary curves for the subsequent concavity
argument.  Every mass is the literal cubic formula in the note.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired.Certificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial

inductive Kind where
  | equal
  | positive (i : Fin 3)
  | diagonal
  | negative (i : Fin 3)
  deriving DecidableEq,Fintype

abbrev L : ℚ := 1/6
abbrev M : ℚ := 41/100
abbrev h : ℚ := 7/10
abbrev c : ℚ := 27/20
abbrev kappa : ℚ := 847/800
abbrev Rbar := NonnegativeTotals.NegativeTD.Certificate.Rbar
abbrev abar := NonnegativeTotals.NegativeTD.Certificate.abar
abbrev cbar := NonnegativeTotals.NegativeTD.Certificate.cbar

def origin : Kind → ℚ | .negative _ => M | _ => L
def length : Kind → ℚ | .negative _ => h-M | _ => M-L
def e : Bivar := C X
def delta (f : Kind) : Bivar := scalar (origin f)+X
def k : Bivar := scalar (3/4)+scalar (7/50)*e
def l : Bivar := scalar (19/20)+scalar (9/20)*e
def p : Fin 3 → Bivar := ![k,k,l]
def q : Fin 3 → Bivar := ![1,l,scalar c]
abbrev J := NonnegativeTotals.NegativeTD.Certificate.J

def gain (u : Bivar) : Bivar :=
  scalar (c*kappa)*(lift u PositiveTD.Certificate.C10+
    lift u PositiveTD.Certificate.S11-1)
def A0 (f : Kind) : Bivar :=
  scalar 2*k+scalar 3*l+scalar ((5/2)*c+5/2-(1+c)*cbar)+l*J (delta f-e)+J e
def A : Kind → Bivar
  | .equal => A0 .equal+gain (delta .equal)
  | .positive i => A0 (.positive i)+gain (scalar M)+p i*
      (lift (scalar M-delta (.positive i)) PositiveTD.Certificate.C10+
        lift (scalar M-delta (.positive i)) PositiveTD.Certificate.S11-1)
  | .diagonal => A0 .diagonal+gain (scalar M)-
      scalar (cbar-1/2)*(scalar M-delta .diagonal)
  | .negative i => A0 (.negative i)+gain (scalar M)+q i*
      (lift (delta (.negative i)-scalar M) PositiveTD.Certificate.C10-1)

def P0 (j : Fin 3) : Bivar := (p j)^2+(q j)^2
def P : Kind → Fin 3 → Bivar
  | .positive i,j => P0 j+if i=j then scalar 2*p j*q j*
      lift (scalar M-delta (.positive i)) PositiveTD.Certificate.S9 else 0
  | .negative i,j => P0 j-if i=j then scalar 2*p j*q j*
      lift (delta (.negative i)-scalar M) PositiveTD.Certificate.S11 else 0
  | _,j => P0 j
def rhoBase : Fin 3 → ℚ := ![5/4,302592961/250000000,825378701/500000000]
def rhoPositive : Fin 3 → ℚ := ![693525169/500000000,1344744663/1000000000,1828389667/1000000000]
def rho : Kind → Fin 3 → ℚ
  | .positive i,j => if i=j then rhoPositive j else rhoBase j
  | _,j => rhoBase j
def mass (f : Kind) (j : Fin 3) : Bivar := cubicMass (rho f j) (P f j)
def numerator (f : Kind) : Bivar :=
  let r := mass f
  scalar 2*A f*r 0*r 1*r 2-scalar Rbar*
    ((P f 0+(r 0)^2)*r 1*r 2+(P f 1+(r 1)^2)*r 0*r 2+(P f 2+(r 2)^2)*r 0*r 1)
def degree : Kind → ℕ | .positive _ => 21 | _ => 20
def transform (f : Kind) (P : Bivar) : Bivar := trapezoid (origin f) (length f) P
def lowerOn (f : Kind) (D : ℕ) (P : Bivar) : ℚ :=
  lower D (coefficient D (transform f P))
def Domain (f : Kind) (x E : ℝ) : Prop :=
  x∈Icc 0 (length f:ℝ) ∧ E∈Icc 0 ((origin f:ℝ)+x)
def Whole : Kind → Prop | .negative _ => False | _ => True
def wholeReserve : Kind → ℚ
  | .equal => 183/1000
  | .positive i => ![139/1000,17/100,157/1000] i
  | .diagonal => 141/1000
  | .negative _ => 0

inductive Boundary where | low | equal | high
  deriving DecidableEq,Fintype
def boundaryLength : Boundary → ℚ | .low => M | .equal => h-M | .high => h
def boundary (b : Boundary) (P : Bivar) : ℚ[X] :=
  match b with
  | .low => restrict P 0 X
  | .equal => restrict P X (C M+X)
  | .high => restrict P (C (h-M)) X
def boundaryReserve : Boundary → Fin 3 → ℚ
  | .low => ![101/500,101/500,101/500]
  | .equal => ![23/100,57/250,57/250]
  | .high => ![11/50,187/1000,119/200]

abbrev C6 := NonnegativeTotals.NegativeTD.Certificate.C6
abbrev slopeK := NonnegativeTotals.NegativeTD.Certificate.slopeK
abbrev slopeL := NonnegativeTotals.NegativeTD.Certificate.slopeL
def slopePolynomial : ℚ[X] :=
  C (9789/2500)*slopeK^2*slopeL^2*C ((C6.eval h)^2)-
    (C (41/50)+slopeL*C (PositiveTD.Certificate.S9.eval h))^2*
      (slopeK^2+slopeL^2-C (2*PositiveTD.Certificate.S11.eval h)*slopeK*slopeL)

@[simp] theorem evaluate_e (x E : ℝ) : evaluate x E e=E := by simp [e]
@[simp] theorem evaluate_delta (f : Kind) (x E : ℝ) :
    evaluate x E (delta f)=(origin f:ℝ)+x := by simp [delta]
@[simp] theorem evaluate_k (x E : ℝ) : evaluate x E k=NonnegativeTotals.NegativeTD.k E := by
  simp [k,NonnegativeTotals.NegativeTD.k]
@[simp] theorem evaluate_l (x E : ℝ) : evaluate x E l=NonnegativeTotals.NegativeTD.l E := by
  simp [l,NonnegativeTotals.NegativeTD.l]
@[simp] theorem evaluate_p (x E : ℝ) (i : Fin 3) :
    evaluate x E (p i)=NonnegativeTotals.NegativeTD.p E i.castSucc := by
  fin_cases i <;> simp [p,NonnegativeTotals.NegativeTD.p]
@[simp] theorem evaluate_q (x E : ℝ) (i : Fin 3) :
    evaluate x E (q i)=NonnegativeTotals.NegativeTD.q E i.castSucc := by
  fin_cases i <;> simp [q,NonnegativeTotals.NegativeTD.q,NonnegativeTotals.NegativeTD.c,c]

theorem bounds {f : Kind} {D : ℕ} {P : Bivar}
    (hid : transform f P=expansion D (transform f P))
    {x E : ℝ} (hd : Domain f x E) : (lowerOn f D P:ℝ)≤evaluate x E P :=
  (trapezoid_bounds (by cases f <;> norm_num [origin,L,M])
    (by cases f <;> norm_num [length,L,M,h]) hid hd.1 hd.2).1

theorem positive_on_domain {f : Kind} {D : ℕ} {P : Bivar} {v : ℚ}
    (hid : transform f P=expansion D (transform f P)) (hv : v<lowerOn f D P)
    {x E : ℝ} (hd : Domain f x E) : (v:ℝ)<evaluate x E P := by
  have hh : (v:ℝ)<(lowerOn f D P:ℝ) := by exact_mod_cast hv
  exact hh.trans_le (bounds hid hd)

end SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired.Certificate
