module

public import SquaresInCircles.Eight.Owners.GA.Negative.ALongEData

/-!
# Eight squares: the twelve longer-E endpoints with positive BT3

The four native domains and the common gain are those of the longer-E case `NegativeA.LongE`.
Here the rotating coefficient belongs to D; the negative B norm uses the fixed coefficient `m`.
The opposite cubic mass corrections are kept on both triangle G curves.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE
open NegativeA.LongE (Region)
open TensorWholeIntervalPolynomial TwoVariablePolynomial

namespace Explicit
abbrev Domain := NegativeA.LongE.Explicit.Domain
abbrev baseRegion := NegativeA.LongE.Explicit.baseRegion
abbrev baseY := NegativeA.LongE.Explicit.baseY
abbrev z := NegativeA.LongE.Explicit.z
abbrev e := NegativeA.LongE.Explicit.e
abbrev s := NegativeA.LongE.Explicit.s
abbrev delta := NegativeA.LongE.Explicit.delta
abbrev k := NegativeA.LongE.Explicit.k
abbrev l := NegativeA.LongE.Explicit.l
abbrev m := NegativeA.LongE.Explicit.c
abbrev base_domain := @NegativeA.LongE.Explicit.base_domain
abbrev domains := @NegativeA.LongE.Explicit.domains
abbrev coordinates := @NegativeA.LongE.Explicit.coordinates
end Explicit

namespace Certificate
abbrev z := NegativeA.LongE.Certificate.z
abbrev e := NegativeA.LongE.Certificate.e
abbrev s := NegativeA.LongE.Certificate.s
abbrev delta := NegativeA.LongE.Certificate.delta
abbrev k := NegativeA.LongE.Certificate.k
abbrev l := NegativeA.LongE.Certificate.l
abbrev m := NegativeA.LongE.Certificate.c
abbrev gain := NegativeA.LongE.Certificate.gain
abbrev jE := NegativeA.LongE.Certificate.jE
abbrev rotation := NegativeA.LongE.Certificate.M
abbrev ABase := NegativeA.LongE.Certificate.ABase
abbrev transform := NegativeA.LongE.Certificate.transform
abbrev lowerOn := NegativeA.LongE.Certificate.lowerOn
abbrev upperOn := NegativeA.LongE.Certificate.upperOn
abbrev domain_bounds := @NegativeA.LongE.Certificate.domain_bounds
abbrev positive_on_domain := @NegativeA.LongE.Certificate.positive_on_domain
abbrev upper_on_domain := @NegativeA.LongE.Certificate.upper_on_domain

def qB : Region → Bivar
  | .TE => l .TE+scalar (3/20)*(scalar (8/15)-X)
  | .TC => l .TC+scalar (3/20)*(scalar (8/15)-X)
  | .RE => m .RE
  | .RC => m .RC
def A (r : Region) (i : Fin 3) : Bivar :=
  ABase r+(![1,l r,qB r] i)*(lift (delta r) PositiveTD.Certificate.C10-1)
def baseNorm (r : Region) : Fin 4 → Bivar :=
  ![1+(k r)^2,(k r)^2+(l r)^2,(l r)^2+(m r)^2,1+(rotation r)^2]
def P (r : Region) (i : Fin 3) (j : Fin 4) : Bivar :=
  baseNorm r j-if j.val=i.val then
    scalar 2*(![k r,k r*l r,l r*m r,0] j)*lift (delta r) PositiveTD.Certificate.S11 else 0
def rho (r : Region) (i : Fin 3) (j : Fin 4) : ℚ :=
  match r with
  | .TE | .RE =>
    if j.val=i.val then
      if j=2 then 1302177104/1000000000 else 1107155480/1000000000
    else ![1203257512/1000000000,1203257512/1000000000,
      1425785990/1000000000,1451171531/1000000000] j
  | .TC | .RC =>
    if j.val=i.val then
      ![1159403846/1000000000,1232394077/1000000000,1424873143/1000000000,0] j
    else ![1265525725/1000000000,1341857056/1000000000,
      1560132267/1000000000,1523913613/1000000000] j
def mass (r : Region) (i : Fin 3) (j : Fin 4) : Bivar :=
  cubicMass (rho r i j) (P r i j)+
    if (r=.TE∨r=.TC) ∧ i=1 then
      if j=1 then -scalar (1/4)*X^3
      else if j=3 then scalar (1/4)*X^3 else 0
    else 0
def numerator (r : Region) (i : Fin 3) : Bivar :=
  let w := mass r i
  scalar 2*A r i*w 0*w 1*w 2*w 3-scalar NonnegativeTotals.Certificate.Rbar*
    ((P r i 0+(w 0)^2)*w 1*w 2*w 3+(P r i 1+(w 1)^2)*w 0*w 2*w 3+
      (P r i 2+(w 2)^2)*w 0*w 1*w 3+(P r i 3+(w 3)^2)*w 0*w 1*w 2)

@[simp] theorem evaluate_z (r : Region) (x y : ℝ) : evaluate x y (z r)=Explicit.z r x y :=
  NegativeA.LongE.Certificate.evaluate_z r x y
@[simp] theorem evaluate_e (r : Region) (x y : ℝ) : evaluate x y (e r)=Explicit.e r x y :=
  NegativeA.LongE.Certificate.evaluate_e r x y
@[simp] theorem evaluate_s (r : Region) (x y : ℝ) : evaluate x y (s r)=Explicit.s r x y :=
  NegativeA.LongE.Certificate.evaluate_s r x y
@[simp] theorem evaluate_delta (r : Region) (x y : ℝ) : evaluate x y (delta r)=Explicit.delta r x y :=
  NegativeA.LongE.Certificate.evaluate_delta r x y
@[simp] theorem evaluate_k (r : Region) (x y : ℝ) : evaluate x y (k r)=Explicit.k r x y :=
  NegativeA.LongE.Certificate.evaluate_k r x y
@[simp] theorem evaluate_l (r : Region) (x y : ℝ) : evaluate x y (l r)=Explicit.l r x y :=
  NegativeA.LongE.Certificate.evaluate_l r x y
@[simp] theorem evaluate_m (r : Region) (x y : ℝ) : evaluate x y (m r)=Explicit.m r x y :=
  NegativeA.LongE.Certificate.evaluate_c r x y

end Certificate
end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE
