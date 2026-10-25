module

public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds

/-!
# Eight squares: the six continuous negative-DE endpoint polynomials

The two choices below are cubic weight formulas on complete sine
intervals.  Each formula is held fixed at all three vertices of the
original angular simplex.  The endpoint masses enter only after that
exact-norm reduction.  Every arithmetic comparison is an explicit
rational coefficient sum of the displayed polynomials.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.NegativeLargeDEPolynomials
open CenteredMonomialBounds


inductive Band where
  | low | high
  deriving DecidableEq

instance : Fintype Band where
  elems := {.low, .high}
  complete x := by cases x <;> decide

def lo : Band → ℚ | .low => 0 | .high => 4/25
def hi : Band → ℚ | .low => 4/25 | .high => 27/100
def mid : Band → ℚ | .low => 2/25 | .high => 43/200
def rad : Band → ℚ | .low => 2/25 | .high => 11/200
def domain (b : Band) : Set ℝ := Icc (lo b:ℝ) (hi b:ℝ)

def cubic (a b c d : ℚ) : ℚ[X] := C a+C b*X+C c*X^2+C d*X^3

def weight : Band → Fin 3 → ℚ[X]
  | .low => ![
      cubic (5882364/10000000) (4934062/10000000) (1427643/10000000) (-5188337/10000000),
      cubic (10080571/10000000) (1130618/10000000) (-9739332/10000000) (26675520/10000000),
      cubic (11668343/10000000) (-9213978/10000000) (709186/10000000) (11644648/10000000)]
  | .high => ![
      cubic (6633158/10000000) (-399489/10000000) (4780194/10000000) (-1700769/10000000),
      cubic (9663412/10000000) (3388059/10000000) (2953896/10000000) (-40769811/10000000),
      cubic (11418718/10000000) (-8017237/10000000) (8506823/10000000) (-23797095/10000000)]

def aP (b : Band) : ℚ[X] := weight b 0
def betaP (b : Band) : ℚ[X] := weight b 1
def epsilonP (b : Band) : ℚ[X] := weight b 2
def a (b : Band) (s : ℝ) : ℝ := aeval s (aP b)
def beta (b : Band) (s : ℝ) : ℝ := aeval s (betaP b)
def epsilon (b : Band) (s : ℝ) : ℝ := aeval s (epsilonP b)

def massARot : Band → ℚ[X]
  | .low => cubic (29347657/100000000) (-6503767/100000000)
      (-7091341/100000000) (-8897024/100000000)
  | .high => cubic (30357263/100000000) (-14570632/100000000)
      (4070833/100000000) (-10732173/100000000)
def massAFixed : Band → ℚ[X]
  | .low => cubic (29348151/100000000) (6325141/100000000)
      (4054196/100000000) (-7689433/100000000)
  | .high => cubic (30355109/100000000) (-526874/100000000)
      (6446582/100000000) (-1674049/100000000)
def massBFixed : Band → ℚ[X]
  | .low => cubic (29492831/100000000) (8686475/100000000)
      (-16973016/100000000) (49966604/100000000)
  | .high => cubic (29572699/100000000) (7226100/100000000)
      (9419652/100000000) (-82051441/100000000)
def massBRot : Band → ℚ[X]
  | .low => cubic (29493219/100000000) (-4166049/100000000)
      (-27993159/100000000) (48192325/100000000)
  | .high => cubic (29526357/100000000) (-5762896/100000000)
      (-160373/100000000) (-75838043/100000000)
def massD : Band → ℚ[X]
  | .low => cubic (38962916/100000000) (-9878934/100000000)
      (-24001063/100000000) (73320919/100000000)
  | .high => cubic (37791971/100000000) (-3967690/100000000)
      (13681627/100000000) (-111961265/100000000)
def massHFixed : Band → ℚ[X]
  | .low => cubic (38830893/100000000) (-17713048/100000000)
      (4857227/100000000) (19769415/100000000)
  | .high => cubic (38317300/100000000) (-14574793/100000000)
      (14011328/100000000) (-36291958/100000000)
def massHSec : Band → ℚ[X]
  | .low => cubic (38830222/100000000) (-17682548/100000000)
      (12596229/100000000) (26750787/100000000)
  | .high => cubic (38277232/100000000) (-13854359/100000000)
      (17734792/100000000) (-21542959/100000000)
def massE : Band → ℚ[X]
  | .low => cubic (30487404/100000000) (-22523113/100000000)
      (2419395/100000000) (28112053/100000000)
  | .high => cubic (29868446/100000000) (-19396183/100000000)
      (20127830/100000000) (-55787176/100000000)

/-- The last entry is M_E; the actual E circle mass is s*M_E. -/
def mass (b : Band) (j : Fin 3) : Fin 5 → ℚ[X] := ![
  if j=0 then massARot b else massAFixed b,
  if j=1 then massBRot b else massBFixed b,
  massD b,
  if j=2 then massHSec b else massHFixed b,
  massE b]

def otherA (b : Band) (j : Fin 3) : ℚ[X] :=
  mass b j 1*mass b j 2*mass b j 3*mass b j 4
def otherB (b : Band) (j : Fin 3) : ℚ[X] :=
  mass b j 0*mass b j 2*mass b j 3*mass b j 4
def otherD (b : Band) (j : Fin 3) : ℚ[X] :=
  mass b j 0*mass b j 1*mass b j 3*mass b j 4
def otherH (b : Band) (j : Fin 3) : ℚ[X] :=
  mass b j 0*mass b j 1*mass b j 2*mass b j 4
def otherE (b : Band) (j : Fin 3) : ℚ[X] :=
  mass b j 0*mass b j 1*mass b j 2*mass b j 3
def denominator (b : Band) (j : Fin 3) : ℚ[X] :=
  C 4*mass b j 0*mass b j 1*mass b j 2*mass b j 3*mass b j 4

def Q : ℚ := 1957767069/500000000
def eta : ℚ := 1/400
def k : ℚ := 307/1000
def K : ℚ := 13/12
def scale (j : Fin 3) : ℚ[X] := if j=2 then 1-X^2 else 1
def totalMass (b : Band) (j : Fin 3) : ℚ[X] :=
  mass b j 0+mass b j 1+mass b j 2+mass b j 3+X*mass b j 4

def base (b : Band) (j : Fin 3) : ℚ[X] :=
  C (if j=1 then 3 else 2)+C 2*aP b+C eta+
    C (if j=1 then 2 else 3)*betaP b+C (2*k)*X+
    epsilonP b+epsilonP b*X-C Q*totalMass b j

/-- The cosine-free part after multiplication by D_j*v_j². -/
def constantNumerator (b : Band) (j : Fin 3) : ℚ[X] :=
  denominator b j*scale j*base b j-
    otherA b j*scale j*(1+(aP b+C eta)^2-
      if j=0 then C 2*(aP b+C eta)*X else 0)-
    otherB b j*scale j*((betaP b)^2+(aP b)^2-
      if j=1 then C 2*aP b*betaP b*X else 0)-
    otherD b j*scale j*((epsilonP b)^2*(1-X^2)+C (k^2)*X^2+(betaP b)^2)-
    otherH b j*((epsilonP b)^2*scale j+1)-
    otherE b j*scale j*X*((epsilonP b)^2+C (k^2))

/-- The remaining coefficient of c, using c²=1-s² exactly. -/
def cosineNumerator (b : Band) (j : Fin 3) : ℚ[X] :=
  denominator b j*(scale j*(C 2*epsilonP b+
      if j=0 then 1 else if j=1 then betaP b else 0)+
      if j=2 then 1+C K*X else 0)-
    otherD b j*scale j*C (2*k)*epsilonP b*X

def cosineSix : ℚ[X] := 1-C (1/2)*X^2-C (1/8)*X^4-C (1/16)*X^6
def cosineReserve : Band → ℚ | .low => 3/50 | .high => 9/200
def P (b : Band) (j : Fin 3) : ℚ[X] :=
  constantNumerator b j+cosineNumerator b j*cosineSix-
    C (cosineReserve b/20)*X^8

def weightLower : Fin 3 → ℚ := ![58/100,99/100,93/100]
def weightUpper : Fin 3 → ℚ := ![69/100,103/100,117/100]

/-! ### Exact coefficient lists

A list of rationals, lowest degree first, names a polynomial. Sums,
products, powers, compositions and derivatives of such lists are exact
rational computations, which the kernel carries out. -/

private def toPoly : List ℚ → ℚ[X]
  | [] => 0
  | a :: l => C a+X*toPoly l

private def ladd : List ℚ → List ℚ → List ℚ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a+b) :: ladd l m

private def lsmul (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: l => (c*a) :: lsmul c l

private def lneg : List ℚ → List ℚ
  | [] => []
  | a :: l => (-a) :: lneg l

private def lmul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | _ :: _, [] => []
  | a :: l, b :: m => ladd (lsmul a (b :: m)) (0 :: lmul l (b :: m))

private def lpow (l : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n+1 => lmul (lpow l n) l

private def lcomp : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: l, m => ladd [a] (lmul m (lcomp l m))

private def lderivAux (k : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: l => (k*a) :: lderivAux (k+1) l

private def lderiv : List ℚ → List ℚ
  | [] => []
  | _ :: l => lderivAux 1 l

private def leval : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: l, r => a+r*leval l r

private theorem toPoly_add : ∀ l m : List ℚ, toPoly (ladd l m)=toPoly l+toPoly m
  | [], m => by simp [ladd,toPoly]
  | a :: l, [] => by simp [ladd,toPoly]
  | a :: l, b :: m => by
    simp only [ladd,toPoly,toPoly_add l m,C_add]
    ring

private theorem toPoly_smul (c : ℚ) : ∀ l : List ℚ, toPoly (lsmul c l)=C c*toPoly l
  | [] => by simp [lsmul,toPoly]
  | a :: l => by
    simp only [lsmul,toPoly,toPoly_smul c l,C_mul]
    ring

private theorem toPoly_neg : ∀ l : List ℚ, toPoly (lneg l)=-toPoly l
  | [] => by simp [lneg,toPoly]
  | a :: l => by
    simp only [lneg,toPoly,toPoly_neg l,C_neg]
    ring

private theorem toPoly_mul : ∀ l m : List ℚ, toPoly (lmul l m)=toPoly l*toPoly m
  | [], m => by simp [lmul,toPoly]
  | _ :: _, [] => by simp [lmul,toPoly]
  | a :: l, b :: m => by
    rw [lmul,toPoly_add,toPoly_smul]
    simp only [toPoly,toPoly_mul l (b :: m),C_0]
    ring

private theorem toPoly_pow (l : List ℚ) : ∀ n : ℕ, toPoly (lpow l n)=toPoly l^n
  | 0 => by simp [lpow,toPoly]
  | n+1 => by rw [lpow,toPoly_mul,toPoly_pow l n,pow_succ]

private theorem toPoly_comp : ∀ l m : List ℚ, toPoly (lcomp l m)=(toPoly l).comp (toPoly m)
  | [], m => by simp [lcomp,toPoly]
  | a :: l, m => by
    rw [lcomp,toPoly_add,toPoly_mul,toPoly_comp l m]
    simp only [toPoly,add_comp,mul_comp,C_comp,X_comp,mul_zero,add_zero]

private theorem toPoly_derivAux : ∀ (k : ℚ) (l : List ℚ),
    toPoly (lderivAux k l)=C k*toPoly l+X*derivative (toPoly l)
  | k, [] => by simp [lderivAux,toPoly]
  | k, a :: l => by
    rw [lderivAux,toPoly,toPoly_derivAux (k+1) l,toPoly,derivative_add,derivative_C,
      derivative_mul,derivative_X,C_mul,C_add,C_1]
    ring

private theorem toPoly_deriv : ∀ l : List ℚ, derivative (toPoly l)=toPoly (lderiv l)
  | [] => by simp [lderiv,toPoly]
  | a :: l => by
    rw [lderiv,toPoly_derivAux,toPoly,derivative_add,derivative_C,derivative_mul,
      derivative_X,C_1]
    ring

private theorem eval_toPoly (r : ℚ) : ∀ l : List ℚ, (toPoly l).eval r=leval l r
  | [] => by simp [toPoly,leval]
  | a :: l => by simp [toPoly,leval,eval_toPoly r l]

private theorem coeff_toPoly : ∀ (l : List ℚ) (i : ℕ), (toPoly l).coeff i=l.getD i 0
  | [], i => by simp [toPoly]
  | a :: l, 0 => by simp [toPoly]
  | a :: l, i+1 => by simp [toPoly,coeff_toPoly l i]

private theorem getD_large : ∀ (l : List ℚ) (N : ℕ), l.length ≤ N → l.getD N 0=0
  | [], _, _ => rfl
  | a :: l, 0, h => by simp at h
  | a :: l, N+1, h => by
    rw [List.getD_cons_succ]
    exact getD_large l N (by simp at h; omega)

private theorem natDegree_toPoly (l : List ℚ) : (toPoly l).natDegree ≤ l.length-1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_toPoly]
  exact getD_large l N (by omega)

private theorem reify_C (a : ℚ) : C a=toPoly [a] := by simp [toPoly]
private theorem reify_X : (X : ℚ[X])=toPoly [0,1] := by simp [toPoly]
private theorem reify_one : (1 : ℚ[X])=toPoly [1] := by simp [toPoly]
private theorem reify_zero : (0 : ℚ[X])=toPoly [] := rfl
private theorem reify_add (l m : List ℚ) : toPoly l+toPoly m=toPoly (ladd l m) :=
  (toPoly_add l m).symm
private theorem reify_sub (l m : List ℚ) :
    toPoly l-toPoly m=toPoly (ladd l (lneg m)) := by
  rw [toPoly_add,toPoly_neg,sub_eq_add_neg]
private theorem reify_neg (l : List ℚ) : -toPoly l=toPoly (lneg l) :=
  (toPoly_neg l).symm
private theorem reify_mul (l m : List ℚ) : toPoly l*toPoly m=toPoly (lmul l m) :=
  (toPoly_mul l m).symm
private theorem reify_pow (l : List ℚ) (n : ℕ) : toPoly l^n=toPoly (lpow l n) :=
  (toPoly_pow l n).symm
private theorem reify_deriv (l : List ℚ) : derivative (toPoly l)=toPoly (lderiv l) :=
  toPoly_deriv l

private theorem translated_toPoly (m : ℚ) (l : List ℚ) :
    translated m (toPoly l)=toPoly (lcomp l [m,1]) := by
  rw [translated,toPoly_comp]
  simp [toPoly]

private theorem series_self {n : ℕ} {q : ℚ[X]} (hq : q.natDegree ≤ n) : q=series n q := by
  conv_lhs => rw [as_sum_range_C_mul_X_pow' q (n := n+1) (by omega)]
  rw [series,Finset.sum_range_succ',add_comm]
  congr 1
  · simp
  · exact (Fin.sum_univ_eq_sum_range (fun j => C (q.coeff (j+1))*X^(j+1)) n).symm

/-- A translated degree identity from a coefficient list of bounded length. -/
private theorem series_toPoly {n : ℕ} {m : ℚ} {l : List ℚ}
    (hl : (lcomp l [m,1]).length ≤ n+1) :
    translated m (toPoly l)=series n (translated m (toPoly l)) := by
  apply series_self
  rw [translated_toPoly]
  exact (natDegree_toPoly _).trans (by omega)

private def lowerL (n : ℕ) (r : ℚ) (L : List ℚ) : ℚ :=
  L.getD 0 0+∑ j : Fin n,lowerTerm (L.getD (j.val+1) 0) r (j.val+1)

private def upperL (n : ℕ) (r : ℚ) (L : List ℚ) : ℚ :=
  L.getD 0 0+∑ j : Fin n,max (L.getD (j.val+1) 0) 0*r^(j.val+1)

private theorem lowerOn_toPoly (n : ℕ) (m r : ℚ) (l : List ℚ) :
    lowerOn n m r (toPoly l)=lowerL n r (lcomp l [m,1]) := by
  simp only [lowerOn,lower,lowerL,translated_toPoly,coeff_toPoly]

private theorem upperOn_toPoly (n : ℕ) (a b : ℚ) (l : List ℚ) :
    upperOn n a b (toPoly l)=upperL n (b-a) (lcomp l [a,1]) := by
  simp only [upperOn,upper,upperL,translated_toPoly,coeff_toPoly]

/-- Unfold the polynomials of this file into coefficient lists. -/
local macro "reify" : tactic => `(tactic| simp only [P,constantNumerator,cosineNumerator,
  cosineSix,otherA,otherB,otherD,otherH,otherE,denominator,totalMass,scale,base,mass,aP,
  betaP,epsilonP,weight,cubic,massARot,massAFixed,massBFixed,massBRot,massD,massHFixed,
  massHSec,massE,Fin.isValue,Fin.reduceFinMk,Fin.reduceEq,Matrix.cons_val_zero,
  Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
  Matrix.head_cons,Matrix.tail_cons,eq_self_iff_true,true_or,or_true,false_or,or_false,
  Bool.false_eq_true,↓reduceIte,reify_C,reify_X,reify_one,reify_zero,reify_add,reify_sub,
  reify_neg,reify_mul,reify_pow])

/-! ### One kernel evaluation per band and vertex

Each certificate below evaluates the cleared polynomial of one band and one
vertex once, and checks every finite fact used about it: the degree bounds,
the cosine coefficient bound and the band's own reserves. -/

private abbrev Shape (m lo' hi' res : ℚ) (L Lc : List ℚ) : Prop :=
  (lcomp (lderiv L) [m,1]).length ≤ 27 ∧ (lcomp (lderiv (lderiv L)) [m,1]).length ≤ 27 ∧
    (lcomp (lneg (lderiv (lderiv L))) [m,1]).length ≤ 27 ∧ (lcomp Lc [lo',1]).length ≤ 27 ∧
    upperL 26 (hi'-lo') (lcomp Lc [lo',1])<res

private abbrev LowOrd (L : List ℚ) : Prop :=
  (1/250:ℚ)<lowerL 26 (2/25) (lcomp (lderiv (lderiv L)) [2/25,1]) ∧
    (1/2500000:ℚ)<leval L (123/1000) ∧ |leval (lderiv L) (123/1000)|<1/1000000

private abbrev LowSec (L : List ℚ) : Prop :=
  (1/400:ℚ)<lowerL 26 (2/25) (lcomp (lneg (lderiv (lderiv L))) [2/25,1]) ∧
    (1/250000:ℚ)<leval L 0 ∧ (1/250000:ℚ)<leval L (4/25)

private abbrev HighOrd (L : List ℚ) : Prop :=
  (1/12500:ℚ)<lowerL 26 (11/200) (lcomp (lderiv L) [43/200,1]) ∧
    (1/250000:ℚ)<leval L (4/25)

private theorem cert_low0 : ∃ L Lc : List ℚ, P .low 0=toPoly L ∧
    cosineNumerator .low 0=toPoly Lc ∧
    Shape (mid .low) (lo .low) (hi .low) (cosineReserve .low) L Lc ∧ LowOrd L := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_low1 : ∃ L Lc : List ℚ, P .low 1=toPoly L ∧
    cosineNumerator .low 1=toPoly Lc ∧
    Shape (mid .low) (lo .low) (hi .low) (cosineReserve .low) L Lc ∧ LowOrd L := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_low2 : ∃ L Lc : List ℚ, P .low 2=toPoly L ∧
    cosineNumerator .low 2=toPoly Lc ∧
    Shape (mid .low) (lo .low) (hi .low) (cosineReserve .low) L Lc ∧ LowSec L := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_high0 : ∃ L Lc : List ℚ, P .high 0=toPoly L ∧
    cosineNumerator .high 0=toPoly Lc ∧
    Shape (mid .high) (lo .high) (hi .high) (cosineReserve .high) L Lc ∧ HighOrd L := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_high1 : ∃ L Lc : List ℚ, P .high 1=toPoly L ∧
    cosineNumerator .high 1=toPoly Lc ∧
    Shape (mid .high) (lo .high) (hi .high) (cosineReserve .high) L Lc ∧ HighOrd L := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_high2 : ∃ L Lc : List ℚ, P .high 2=toPoly L ∧
    cosineNumerator .high 2=toPoly Lc ∧
    Shape (mid .high) (lo .high) (hi .high) (cosineReserve .high) L Lc ∧ HighOrd L := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem shape (b : Band) (j : Fin 3) : ∃ L Lc : List ℚ, P b j=toPoly L ∧
    cosineNumerator b j=toPoly Lc ∧ Shape (mid b) (lo b) (hi b) (cosineReserve b) L Lc := by
  cases b <;> fin_cases j
  · obtain ⟨L,Lc,h1,h2,h3,-⟩ := cert_low0; exact ⟨L,Lc,h1,h2,h3⟩
  · obtain ⟨L,Lc,h1,h2,h3,-⟩ := cert_low1; exact ⟨L,Lc,h1,h2,h3⟩
  · obtain ⟨L,Lc,h1,h2,h3,-⟩ := cert_low2; exact ⟨L,Lc,h1,h2,h3⟩
  · obtain ⟨L,Lc,h1,h2,h3,-⟩ := cert_high0; exact ⟨L,Lc,h1,h2,h3⟩
  · obtain ⟨L,Lc,h1,h2,h3,-⟩ := cert_high1; exact ⟨L,Lc,h1,h2,h3⟩
  · obtain ⟨L,Lc,h1,h2,h3,-⟩ := cert_high2; exact ⟨L,Lc,h1,h2,h3⟩

private theorem fin3_cases (j : Fin 3) : j=0 ∨ j=1 ∨ j=2 := by
  fin_cases j <;> simp

private theorem r34_domain_low : domain .low=Icc (0:ℝ) (4/25) := by
  simp only [domain,lo,hi]
  norm_num

private theorem r34_domain_high : domain .high=Icc (4/25:ℝ) (27/100) := by
  simp only [domain,lo,hi]
  norm_num


theorem domain_centered {b : Band} {s : ℝ} (hs : s∈domain b) :
    |s-(mid b:ℝ)|≤(rad b:ℝ) := by
  cases b
  · rw [r34_domain_low] at hs
    rw [abs_le]
    simp only [mid,rad]
    push_cast
    constructor <;> linarith [hs.1,hs.2]
  · rw [r34_domain_high] at hs
    rw [abs_le]
    simp only [mid,rad]
    push_cast
    constructor <;> linarith [hs.1,hs.2]

theorem domain_full {b : Band} {s : ℝ} (hs : s∈domain b) :
    s∈Icc 0 (27/100 : ℝ) := by
  cases b
  · rw [r34_domain_low] at hs
    constructor <;> linarith [hs.1,hs.2]
  · rw [r34_domain_high] at hs
    constructor <;> linarith [hs.1,hs.2]

theorem weight_series : ∀b i,
    translated (mid b) (weight b i)=series 3 (translated (mid b) (weight b i)) ∧
    translated (mid b) (-weight b i)=series 3 (translated (mid b) (-weight b i)) := by
  intro b i
  cases b <;> fin_cases i <;> reify <;>
    exact ⟨series_toPoly (by decide +kernel),series_toPoly (by decide +kernel)⟩

theorem weight_coefficients : ∀b i,
    weightLower i<lowerOn 3 (mid b) (rad b) (weight b i) ∧
    -weightUpper i<lowerOn 3 (mid b) (rad b) (-weight b i) := by
  intro b i
  cases b <;> fin_cases i <;> reify <;> rw [lowerOn_toPoly,lowerOn_toPoly] <;> decide +kernel

theorem mass_series : ∀b j i,
    translated (mid b) (mass b j i)=series 3 (translated (mid b) (mass b j i)) := by
  intro b j i
  cases b <;> fin_cases j <;> fin_cases i <;> reify <;> exact series_toPoly (by decide +kernel)

theorem mass_coefficients : ∀b j i,
    (23/100:ℚ)<lowerOn 3 (mid b) (rad b) (mass b j i) := by
  intro b j i
  cases b <;> fin_cases j <;> fin_cases i <;> reify <;> rw [lowerOn_toPoly] <;> decide +kernel

theorem weight_bounds {b : Band} {s : ℝ} (hs : s∈domain b) (i : Fin 3) :
    (weightLower i:ℝ)<aeval s (weight b i) ∧
      aeval s (weight b i)<(weightUpper i:ℝ) := by
  have hr : 0≤rad b := by cases b <;> norm_num [rad]
  have hlo := interval_lower (weight_series b i).1 hr (domain_centered hs)
  have hhi := interval_lower (weight_series b i).2 hr (domain_centered hs)
  have hnumlo : (weightLower i:ℝ)<(lowerOn 3 (mid b) (rad b) (weight b i):ℝ) := by
    exact_mod_cast (weight_coefficients b i).1
  have hnumhi : -(weightUpper i:ℝ)<(lowerOn 3 (mid b) (rad b) (-weight b i):ℝ) := by
    exact_mod_cast (weight_coefficients b i).2
  rw [map_neg] at hhi
  exact ⟨hnumlo.trans_le hlo,by linarith⟩

theorem actual_weight_bounds {b : Band} {s : ℝ} (hs : s∈domain b) :
    58/100<a b s ∧ a b s<69/100 ∧
    99/100<beta b s ∧ beta b s<103/100 ∧
    93/100<epsilon b s ∧ epsilon b s<117/100 := by
  have h0 := weight_bounds hs 0
  have h1 := weight_bounds hs 1
  have h2 := weight_bounds hs 2
  simpa [a,beta,epsilon,aP,betaP,epsilonP,weightLower,weightUpper] using
    And.intro h0.1 (And.intro h0.2 (And.intro h1.1 (And.intro h1.2 h2)))

theorem mass_positive {b : Band} {s : ℝ} (hs : s∈domain b) (j : Fin 3) (i : Fin 5) :
    0<aeval s (mass b j i) := by
  have hr : 0≤rad b := by cases b <;> norm_num [rad]
  have hh := interval_lower (mass_series b j i) hr (domain_centered hs)
  have hn := (Rat.cast_lt (K := ℝ)).mpr (mass_coefficients b j i)
  rw [show ((23/100:ℚ):ℝ)=23/100 by norm_num] at hn
  linarith

theorem cosine_series : ∀b j,
    translated (lo b) (cosineNumerator b j)=
      series 26 (translated (lo b) (cosineNumerator b j)) := by
  intro b j
  obtain ⟨L,Lc,-,hc,hs⟩ := shape b j
  rw [hc]
  exact series_toPoly hs.2.2.2.1

theorem cosine_coefficients : ∀b j,
    upperOn 26 (lo b) (hi b) (cosineNumerator b j)<cosineReserve b := by
  intro b j
  obtain ⟨L,Lc,-,hc,hs⟩ := shape b j
  rw [hc,upperOn_toPoly]
  exact hs.2.2.2.2

theorem cosine_upper {b : Band} {s : ℝ} (hs : s∈domain b) (j : Fin 3) :
    aeval s (cosineNumerator b j)<(cosineReserve b:ℝ) := by
  have hb := interval_upper (cosine_series b j) hs
  have hn : (upperOn 26 (lo b) (hi b) (cosineNumerator b j):ℝ)<(cosineReserve b:ℝ) := by
    exact_mod_cast cosine_coefficients b j
  exact hb.trans_lt hn

theorem derivative_series : ∀b j,
    translated (mid b) (P b j).derivative=
      series 26 (translated (mid b) (P b j).derivative) ∧
    translated (mid b) (P b j).derivative.derivative=
      series 26 (translated (mid b) (P b j).derivative.derivative) ∧
    translated (mid b) (-(P b j).derivative.derivative)=
      series 26 (translated (mid b) (-(P b j).derivative.derivative)) := by
  intro b j
  obtain ⟨L,Lc,hL,-,hs⟩ := shape b j
  rw [hL,reify_deriv,reify_deriv,reify_neg]
  exact ⟨series_toPoly hs.1,series_toPoly hs.2.1,series_toPoly hs.2.2.1⟩

theorem low_curvature_coefficients :
    (1/250:ℚ)<lowerOn 26 (2/25) (2/25) (P .low 0).derivative.derivative ∧
    (1/250:ℚ)<lowerOn 26 (2/25) (2/25) (P .low 1).derivative.derivative ∧
    (1/400:ℚ)<lowerOn 26 (2/25) (2/25) (-(P .low 2).derivative.derivative) := by
  refine ⟨?_,?_,?_⟩
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_low0
    rw [hL,reify_deriv,reify_deriv,lowerOn_toPoly]
    exact h.1
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_low1
    rw [hL,reify_deriv,reify_deriv,lowerOn_toPoly]
    exact h.1
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_low2
    rw [hL,reify_deriv,reify_deriv,reify_neg,lowerOn_toPoly]
    exact h.1

theorem high_growth_coefficients : ∀j,
    (1/12500:ℚ)<lowerOn 26 (43/200) (11/200) (P .high j).derivative := by
  intro j
  obtain rfl | rfl | rfl := fin3_cases j
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_high0
    rw [hL,reify_deriv,lowerOn_toPoly]
    exact h.1
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_high1
    rw [hL,reify_deriv,lowerOn_toPoly]
    exact h.1
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_high2
    rw [hL,reify_deriv,lowerOn_toPoly]
    exact h.1

theorem low_tangent_values : ∀j : Fin 2,
    (1/2500000:ℚ)<(P .low j.castSucc).eval (123/1000) ∧
    |(P .low j.castSucc).derivative.eval (123/1000)|<1/1000000 := by
  intro j
  obtain rfl | rfl : j=0 ∨ j=1 := by fin_cases j <;> simp
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_low0
    rw [Fin.castSucc_zero,hL,reify_deriv,eval_toPoly,eval_toPoly]
    exact h.2
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_low1
    rw [Fin.castSucc_one,hL,reify_deriv,eval_toPoly,eval_toPoly]
    exact h.2

theorem low_secant_endpoints :
    (1/250000:ℚ)<(P .low 2).eval 0 ∧
    (1/250000:ℚ)<(P .low 2).eval (4/25) := by
  obtain ⟨L,Lc,hL,-,-,h⟩ := cert_low2
  rw [hL,eval_toPoly,eval_toPoly]
  exact h.2

theorem high_start_values : ∀j,
    (1/250000:ℚ)<(P .high j).eval (4/25) := by
  intro j
  obtain rfl | rfl | rfl := fin3_cases j
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_high0
    rw [hL,eval_toPoly]
    exact h.2
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_high1
    rw [hL,eval_toPoly]
    exact h.2
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_high2
    rw [hL,eval_toPoly]
    exact h.2

theorem rational_eval (p : ℚ[X]) (r : ℚ) :
    aeval (r:ℝ) p=((p.eval r:ℚ):ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n c => simp [Polynomial.aeval_monomial,Polynomial.eval_monomial]

theorem low_curvature {s : ℝ} (hs : s∈domain .low) (j : Fin 2) :
    (1/250:ℝ)<aeval s (P .low j.castSucc).derivative.derivative := by
  have hb := interval_lower (derivative_series .low j.castSucc).2.1
    (by norm_num [rad] : 0≤rad Band.low) (domain_centered hs)
  have hc : (1/250:ℚ)<
      lowerOn 26 (mid .low) (rad .low) (P .low j.castSucc).derivative.derivative := by
    fin_cases j
    · exact low_curvature_coefficients.1
    · exact low_curvature_coefficients.2.1
  have hc' := (Rat.cast_lt (K := ℝ)).mpr hc
  rw [show ((1/250:ℚ):ℝ)=1/250 by norm_num] at hc'
  exact hc'.trans_le hb

theorem low_secant_curvature {s : ℝ} (hs : s∈domain .low) :
    aeval s (P .low 2).derivative.derivative< -(1/400:ℝ) := by
  have hb := interval_lower (derivative_series .low 2).2.2
    (by norm_num [rad] : 0≤rad Band.low) (domain_centered hs)
  have hc := (Rat.cast_lt (K := ℝ)).mpr low_curvature_coefficients.2.2
  rw [show ((1/400:ℚ):ℝ)=1/400 by norm_num] at hc
  rw [map_neg] at hb
  have hc' : (1/400:ℝ)<(lowerOn 26 (mid .low) (rad .low) (-(P .low 2).derivative.derivative):ℝ) :=
    hc
  linarith

theorem high_growth {s : ℝ} (hs : s∈domain .high) (j : Fin 3) :
    (1/12500:ℝ)<aeval s (P .high j).derivative := by
  have hb := interval_lower (derivative_series .high j).1
    (by norm_num [rad] : 0≤rad Band.high) (domain_centered hs)
  have hc := (Rat.cast_lt (K := ℝ)).mpr (high_growth_coefficients j)
  rw [show ((1/12500:ℚ):ℝ)=1/12500 by norm_num] at hc
  exact hc.trans_le hb

/-- The first two low-band polynomials retain their actual tangent at
.123 and the whole-interval curvature reserve. -/
theorem low_ordinary_positive {s : ℝ} (hs : s∈domain .low) (j : Fin 2) :
    0<aeval s (P .low j.castSucc) := by
  rw [r34_domain_low] at hs
  have hh := second_derivative_tangent_lower
    (f := fun x : ℝ => aeval x (P .low j.castSucc))
    (df := fun x : ℝ => aeval x (P .low j.castSucc).derivative)
    (ddf := fun x : ℝ => aeval x (P .low j.castSucc).derivative.derivative)
    (l := 0) (h := 4/25) (x₀ := 123/1000) (x := s) (κ := 1/250)
    (fun x _ => aeval_hasDerivAt _ x) (fun x _ => aeval_hasDerivAt _ x)
    (fun x hx => (low_curvature (by rw [r34_domain_low]; exact hx) j).le) (by norm_num) hs
  have hv : (1/2500000:ℝ)<aeval (123/1000:ℝ) (P .low j.castSucc) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (low_tangent_values j).1
    rw [show (123/1000:ℝ)=((123/1000:ℚ):ℝ) by norm_num,rational_eval]
    push_cast at h
    exact h
  have hd : |aeval (123/1000:ℝ) (P .low j.castSucc).derivative|<1/1000000 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (low_tangent_values j).2
    rw [show (123/1000:ℝ)=((123/1000:ℚ):ℝ) by norm_num,rational_eval]
    push_cast at h
    exact h
  have hd2 : (aeval (123/1000:ℝ) (P .low j.castSucc).derivative)^2<1/1000000000000 := by
    obtain ⟨hl,hu⟩ := abs_lt.mp hd
    nlinarith
  have hsq := sq_nonneg
    (s-123/1000+250*aeval (123/1000:ℝ) (P .low j.castSucc).derivative)
  nlinarith

theorem low_secant_positive {s : ℝ} (hs : s∈domain .low) :
    0<aeval s (P .low 2) := by
  rw [r34_domain_low] at hs
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (4/25)) (fun x : ℝ => aeval x (P .low 2)) := by
    apply concave_of_deriv2
      (f' := fun x => aeval x (P .low 2).derivative)
      (f'' := fun x => aeval x (P .low 2).derivative.derivative)
    · exact fun x _ => aeval_hasDerivAt _ x
    · exact fun x _ => aeval_hasDerivAt _ x
    · intro x hx
      linarith [low_secant_curvature (by rw [r34_domain_low]; exact hx)]
  have hh := concave_endpoint_reserve (f := fun x : ℝ => aeval x (P .low 2))
    (k := (0:ℝ)) (by norm_num) hs (by simpa using hc)
  have hl : (0:ℝ)<aeval 0 (P .low 2) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (lt_trans (by norm_num : (0:ℚ)<1/250000) low_secant_endpoints.1)
    rw [show (0:ℝ)=((0:ℚ):ℝ) by norm_num,rational_eval]
    exact h
  have hu : (0:ℝ)<aeval (4/25:ℝ) (P .low 2) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (lt_trans (by norm_num : (0:ℚ)<1/250000) low_secant_endpoints.2)
    rw [show (4/25:ℝ)=((4/25:ℚ):ℝ) by norm_num,rational_eval]
    push_cast at h
    exact h
  have hm := lt_min hl hu
  simp only [zero_div,zero_mul,add_zero] at hh
  exact hm.trans_le hh

theorem high_positive {s : ℝ} (hs : s∈domain .high) (j : Fin 3) :
    0<aeval s (P .high j) := by
  rw [r34_domain_high] at hs
  have hh := derivative_reserve
    (f := fun x : ℝ => aeval x (P .high j))
    (df := fun x : ℝ => aeval x (P .high j).derivative)
    (l := (4/25:ℝ)) (u := 27/100) (x := 4/25) (y := s) (k := 0)
    (fun x _ => (aeval_hasDerivAt _ x).continuousAt.continuousWithinAt)
    (fun x _ => aeval_hasDerivAt _ x)
    (fun x hx => by
      linarith [high_growth (by rw [r34_domain_high]; exact Ioo_subset_Icc_self hx) j])
    (by norm_num) hs hs.1
  have hv : (0:ℝ)<aeval (4/25:ℝ) (P .high j) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (lt_trans (by norm_num : (0:ℚ)<1/250000) (high_start_values j))
    rw [show (4/25:ℝ)=((4/25:ℚ):ℝ) by norm_num,rational_eval]
    push_cast at h
    exact h
  simp only [zero_mul] at hh
  linarith

/-- Every actual sine in either complete interval has a positive cleared
endpoint polynomial; all three geometric simplex vertices are included. -/
theorem polynomial_positive {b : Band} {s : ℝ} (hs : s∈domain b) (j : Fin 3) :
    0<aeval s (P b j) := by
  cases b
  · fin_cases j
    · exact low_ordinary_positive hs 0
    · exact low_ordinary_positive hs 1
    · exact low_secant_positive hs
  · exact high_positive hs j

end SquaresInCircles.Eight.NegativeLargeDEPolynomials
