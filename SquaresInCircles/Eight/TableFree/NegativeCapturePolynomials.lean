module

public import SquaresInCircles.Eight.TableFree.NegativeCaptureData

/-!
# The eight exact cleared polynomials for canonical negative capture

Uncompiled reconstruction of sections 6--7 of
HAND_G5_NEGATIVE_CANONICAL_SMALL_ERROR_CAPTURE.md.

All operations below are ordinary rational polynomial operations.  The
two approximate short-angle constants remain separate: their squared
sum is never replaced by one.  The secant endpoint is cleared by the
actual factor 1-s².  Whole-polynomial coefficient sums, followed by
finite derivative integration, give positivity on both full bands.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.NegativeCapturePolynomials
open CenteredMonomialBounds NegativeCaptureData


def otherA (b : Band) (j : Fin 4) : ℚ[X] :=
  mass b j 1*mass b j 2*mass b j 3*mass b j 4
def otherB (b : Band) (j : Fin 4) : ℚ[X] :=
  mass b j 0*mass b j 2*mass b j 3*mass b j 4
def otherD (b : Band) (j : Fin 4) : ℚ[X] :=
  mass b j 0*mass b j 1*mass b j 3*mass b j 4
def otherH (b : Band) (j : Fin 4) : ℚ[X] :=
  mass b j 0*mass b j 1*mass b j 2*mass b j 4
def otherE (b : Band) (j : Fin 4) : ℚ[X] :=
  mass b j 0*mass b j 1*mass b j 2*mass b j 3
def denominator (b : Band) (j : Fin 4) : ℚ[X] :=
  C 4*mass b j 0*mass b j 1*mass b j 2*mass b j 3*mass b j 4
def totalMass (b : Band) (j : Fin 4) : ℚ[X] :=
  mass b j 0+mass b j 1+mass b j 2+mass b j 3+X*mass b j 4
def scale (j : Fin 4) : ℚ[X] := if j=1 then 1-X^2 else 1

def endpointConstant (j : Fin 4) : ℚ[X] :=
  if j=0 ∨ j=1 then C 2 else if j=2 then
    C (chi+1)+C sigma*X else C (1+(1+K*sigma)/chi)+C sigma*X
def endpointCosine (j : Fin 4) : ℚ[X] :=
  if j=0 then 1 else if j=1 then 0 else C chi
def secantSquare (j : Fin 4) : ℚ[X] := if j=3 then C (1/chi^2) else 1

def base (b : Band) (j : Fin 4) : ℚ[X] :=
  C 3+C 2*aP b+C eta+fP b+C (2*k)*X+fP b*X-
    C Q*totalMass b j-C (delta j)+endpointConstant j
def normA (b : Band) (j : Fin 4) : ℚ[X] :=
  if j=0 then 1+(aP b+C eta)^2-C 2*(aP b+C eta)*X
  else if j=2 then C (chi^2+sigma^2)+(aP b+C eta)^2-
    C (2*sigma)*(aP b+C eta)
  else 1+(aP b+C eta)^2
def normB (b : Band) (j : Fin 4) : ℚ[X] :=
  if j=0 ∨ j=1 then 1+(aP b)^2
  else C (chi^2+sigma^2)+(aP b)^2-C (2*chi)*aP b*X
def normBCosine (b : Band) (j : Fin 4) : ℚ[X] :=
  if j=0 ∨ j=1 then 0 else C (2*sigma)*aP b

/-- Constant term in the exact quotient c²=1-s².  Every mass quotient
has already been written as the product of the other four masses. -/
def constantNumerator (b : Band) (j : Fin 4) : ℚ[X] :=
  denominator b j*scale j*base b j-
    otherA b j*scale j*normA b j-
    otherB b j*scale j*normB b j-
    otherD b j*scale j*((fP b)^2+1)-
    otherH b j*(scale j*((fP b)^2*(1-X^2)+C (k^2)*X^2)+secantSquare j)-
    otherE b j*scale j*X*((fP b)^2+C (k^2))

/-- Coefficient of the original cosine after clearing the secant. -/
def cosineNumerator (b : Band) (j : Fin 4) : ℚ[X] :=
  denominator b j*(scale j*(C 2*fP b+endpointCosine j)+
    if j=1 then 1+C K*X else 0)-
    otherB b j*scale j*normBCosine b j-
    otherH b j*scale j*C (2*k)*fP b*X

def cosineSix : ℚ[X] := 1-C (1/2)*X^2-C (1/8)*X^4-C (1/16)*X^6
def cosineReserve : Band → ℚ | .low => 3/50 | .high => 1/20
def P (b : Band) (j : Fin 4) : ℚ[X] :=
  constantNumerator b j+cosineNumerator b j*cosineSix-
    C (cosineReserve b/20)*X^8

def pivot (j : Fin 4) : ℚ := ![47/400,1/10,233/2000,67/500] j

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
  cosineSix,otherA,otherB,otherD,otherH,otherE,denominator,totalMass,scale,endpointConstant,
  endpointCosine,secantSquare,base,normA,normB,normBCosine,mass,aP,fP,weight,cubic,massARot,
  massAFixed,massAShort,massBFixed,massBShift,massD,massHFixed,massHSec,massHShort,massE,
  Fin.isValue,Fin.reduceFinMk,Fin.reduceEq,Matrix.cons_val_zero,Matrix.cons_val_one,
  Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,
  Matrix.tail_cons,eq_self_iff_true,true_or,or_true,false_or,or_false,Bool.false_eq_true,
  ↓reduceIte,reify_C,reify_X,reify_one,reify_zero,reify_add,reify_sub,reify_neg,reify_mul,
  reify_pow])

/-! ### One kernel evaluation per band and vertex

Each certificate below evaluates the cleared polynomial of one band and one
vertex once, and checks every finite fact used about it: the degree bounds,
the cosine coefficient bound and the band's own reserves. -/

private abbrev Shape (m lo' hi' res : ℚ) (L Lc : List ℚ) : Prop :=
  (lcomp L [m,1]).length ≤ 27 ∧ (lcomp (lderiv L) [m,1]).length ≤ 27 ∧
    (lcomp (lderiv (lderiv L)) [m,1]).length ≤ 27 ∧ (lcomp Lc [lo',1]).length ≤ 27 ∧
    upperL 26 (hi'-lo') (lcomp Lc [lo',1])<res

private abbrev LowOrd (p : ℚ) (L : List ℚ) : Prop :=
  (1/200:ℚ)<lowerL 26 (rad .low) (lcomp (lderiv (lderiv L)) [mid .low,1]) ∧
    (1/200000:ℚ)<leval L p ∧ |leval (lderiv L) p|<1/100000

private abbrev LowSec (L : List ℚ) : Prop :=
  (1/40000:ℚ)<lowerL 26 (rad .low) (lcomp L [mid .low,1])

private abbrev HighOrd (L : List ℚ) : Prop :=
  (-1/250000:ℚ)<lowerL 26 (rad .high) (lcomp (lderiv L) [mid .high,1]) ∧
    (3/500000:ℚ)<leval L (7/50)

private abbrev HighSec (L : List ℚ) : Prop :=
  (1/100000:ℚ)<lowerL 26 (rad .high) (lcomp L [mid .high,1])

private theorem cert_low0 : ∃ L Lc : List ℚ, P .low 0=toPoly L ∧
    cosineNumerator .low 0=toPoly Lc ∧
    Shape (mid .low) (lo .low) (hi .low) (cosineReserve .low) L Lc ∧ LowOrd (pivot 0) L := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_low1 : ∃ L Lc : List ℚ, P .low 1=toPoly L ∧
    cosineNumerator .low 1=toPoly Lc ∧
    Shape (mid .low) (lo .low) (hi .low) (cosineReserve .low) L Lc ∧ LowSec L := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_low2 : ∃ L Lc : List ℚ, P .low 2=toPoly L ∧
    cosineNumerator .low 2=toPoly Lc ∧
    Shape (mid .low) (lo .low) (hi .low) (cosineReserve .low) L Lc ∧ LowOrd (pivot 2) L := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_low3 : ∃ L Lc : List ℚ, P .low 3=toPoly L ∧
    cosineNumerator .low 3=toPoly Lc ∧
    Shape (mid .low) (lo .low) (hi .low) (cosineReserve .low) L Lc ∧ LowOrd (pivot 3) L := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_high0 : ∃ L Lc : List ℚ, P .high 0=toPoly L ∧
    cosineNumerator .high 0=toPoly Lc ∧
    Shape (mid .high) (lo .high) (hi .high) (cosineReserve .high) L Lc ∧ HighOrd L := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_high1 : ∃ L Lc : List ℚ, P .high 1=toPoly L ∧
    cosineNumerator .high 1=toPoly Lc ∧
    Shape (mid .high) (lo .high) (hi .high) (cosineReserve .high) L Lc ∧ HighSec L := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_high2 : ∃ L Lc : List ℚ, P .high 2=toPoly L ∧
    cosineNumerator .high 2=toPoly Lc ∧
    Shape (mid .high) (lo .high) (hi .high) (cosineReserve .high) L Lc ∧ HighOrd L := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_high3 : ∃ L Lc : List ℚ, P .high 3=toPoly L ∧
    cosineNumerator .high 3=toPoly Lc ∧
    Shape (mid .high) (lo .high) (hi .high) (cosineReserve .high) L Lc ∧ HighOrd L := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem shape (b : Band) (j : Fin 4) : ∃ L Lc : List ℚ, P b j=toPoly L ∧
    cosineNumerator b j=toPoly Lc ∧ Shape (mid b) (lo b) (hi b) (cosineReserve b) L Lc := by
  cases b <;> fin_cases j
  · obtain ⟨L,Lc,h1,h2,h3,-⟩ := cert_low0; exact ⟨L,Lc,h1,h2,h3⟩
  · obtain ⟨L,Lc,h1,h2,h3,-⟩ := cert_low1; exact ⟨L,Lc,h1,h2,h3⟩
  · obtain ⟨L,Lc,h1,h2,h3,-⟩ := cert_low2; exact ⟨L,Lc,h1,h2,h3⟩
  · obtain ⟨L,Lc,h1,h2,h3,-⟩ := cert_low3; exact ⟨L,Lc,h1,h2,h3⟩
  · obtain ⟨L,Lc,h1,h2,h3,-⟩ := cert_high0; exact ⟨L,Lc,h1,h2,h3⟩
  · obtain ⟨L,Lc,h1,h2,h3,-⟩ := cert_high1; exact ⟨L,Lc,h1,h2,h3⟩
  · obtain ⟨L,Lc,h1,h2,h3,-⟩ := cert_high2; exact ⟨L,Lc,h1,h2,h3⟩
  · obtain ⟨L,Lc,h1,h2,h3,-⟩ := cert_high3; exact ⟨L,Lc,h1,h2,h3⟩

private theorem fin4_cases (j : Fin 4) : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by
  fin_cases j <;> simp

private theorem r34_domain_low : domain .low=Icc (1499/100000:ℝ) (7/50) := by
  simp only [domain,lo,hi]
  norm_num

private theorem r34_domain_high : domain .high=Icc (7/50:ℝ) (27/100) := by
  simp only [domain,lo,hi]
  norm_num


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

theorem polynomial_series : ∀b j,
    translated (mid b) (P b j)=series 26 (translated (mid b) (P b j)) ∧
    translated (mid b) (P b j).derivative=
      series 26 (translated (mid b) (P b j).derivative) ∧
    translated (mid b) (P b j).derivative.derivative=
      series 26 (translated (mid b) (P b j).derivative.derivative) := by
  intro b j
  obtain ⟨L,Lc,hL,-,hs⟩ := shape b j
  rw [hL,reify_deriv,reify_deriv]
  exact ⟨series_toPoly hs.1,series_toPoly hs.2.1,series_toPoly hs.2.2.1⟩

theorem low_curvature_coefficients : ∀j : Fin 4, j≠1 →
    (1/200:ℚ)<lowerOn 26 (mid .low) (rad .low) (P .low j).derivative.derivative := by
  intro j hj
  obtain rfl | rfl | rfl | rfl := fin4_cases j
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_low0
    rw [hL,reify_deriv,reify_deriv,lowerOn_toPoly]
    exact h.1
  · exact absurd rfl hj
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_low2
    rw [hL,reify_deriv,reify_deriv,lowerOn_toPoly]
    exact h.1
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_low3
    rw [hL,reify_deriv,reify_deriv,lowerOn_toPoly]
    exact h.1

theorem low_tangent_values : ∀j : Fin 4, j≠1 →
    (1/200000:ℚ)<(P .low j).eval (pivot j) ∧
      |(P .low j).derivative.eval (pivot j)|<1/100000 := by
  intro j hj
  obtain rfl | rfl | rfl | rfl := fin4_cases j
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_low0
    rw [hL,reify_deriv,eval_toPoly,eval_toPoly]
    exact h.2
  · exact absurd rfl hj
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_low2
    rw [hL,reify_deriv,eval_toPoly,eval_toPoly]
    exact h.2
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_low3
    rw [hL,reify_deriv,eval_toPoly,eval_toPoly]
    exact h.2

theorem low_secant_coefficients :
    (1/40000:ℚ)<lowerOn 26 (mid .low) (rad .low) (P .low 1) := by
  obtain ⟨L,Lc,hL,-,-,h⟩ := cert_low1
  rw [hL,lowerOn_toPoly]
  exact h

theorem high_growth_coefficients : ∀j : Fin 4, j≠1 →
    (-1/250000:ℚ)<lowerOn 26 (mid .high) (rad .high) (P .high j).derivative := by
  intro j hj
  obtain rfl | rfl | rfl | rfl := fin4_cases j
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_high0
    rw [hL,reify_deriv,lowerOn_toPoly]
    exact h.1
  · exact absurd rfl hj
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_high2
    rw [hL,reify_deriv,lowerOn_toPoly]
    exact h.1
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_high3
    rw [hL,reify_deriv,lowerOn_toPoly]
    exact h.1

theorem high_start_values : ∀j : Fin 4, j≠1 →
    (3/500000:ℚ)<(P .high j).eval (7/50) := by
  intro j hj
  obtain rfl | rfl | rfl | rfl := fin4_cases j
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_high0
    rw [hL,eval_toPoly]
    exact h.2
  · exact absurd rfl hj
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_high2
    rw [hL,eval_toPoly]
    exact h.2
  · obtain ⟨L,Lc,hL,-,-,h⟩ := cert_high3
    rw [hL,eval_toPoly]
    exact h.2

theorem high_secant_coefficients :
    (1/100000:ℚ)<lowerOn 26 (mid .high) (rad .high) (P .high 1) := by
  obtain ⟨L,Lc,hL,-,-,h⟩ := cert_high1
  rw [hL,lowerOn_toPoly]
  exact h

theorem rational_eval (p : ℚ[X]) (r : ℚ) :
    aeval (r:ℝ) p=((p.eval r:ℚ):ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n c => simp [Polynomial.aeval_monomial,Polynomial.eval_monomial]

theorem cosine_upper {b : Band} {s : ℝ} (hs : s∈domain b) (j : Fin 4) :
    aeval s (cosineNumerator b j)<(cosineReserve b:ℝ) := by
  have hb := interval_upper (cosine_series b j) hs
  have hn : (upperOn 26 (lo b) (hi b) (cosineNumerator b j):ℝ)<(cosineReserve b:ℝ) := by
    exact_mod_cast cosine_coefficients b j
  exact hb.trans_lt hn

theorem low_curvature {s : ℝ} (hs : s∈domain .low) {j : Fin 4} (hj : j≠1) :
    (1/200:ℝ)<aeval s (P .low j).derivative.derivative := by
  have hb := interval_lower (polynomial_series .low j).2.2
    (by norm_num [rad] : 0≤rad Band.low) (domain_centered hs)
  have hc := (Rat.cast_lt (K := ℝ)).mpr (low_curvature_coefficients j hj)
  rw [show ((1/200:ℚ):ℝ)=1/200 by norm_num] at hc
  exact hc.trans_le hb

/-- A complete-square tangent bound on the full first sine interval. -/
theorem low_ordinary_positive {s : ℝ} (hs : s∈domain .low) {j : Fin 4} (hj : j≠1) :
    (499/100000000:ℝ)<aeval s (P .low j) := by
  have hp : (pivot j:ℝ)∈Icc (1499/100000:ℝ) (7/50) := by
    fin_cases j <;> norm_num [pivot]
  rw [r34_domain_low] at hs
  have hh := second_derivative_tangent_lower
    (f := fun x : ℝ => aeval x (P .low j))
    (df := fun x : ℝ => aeval x (P .low j).derivative)
    (ddf := fun x : ℝ => aeval x (P .low j).derivative.derivative)
    (l := 1499/100000) (h := 7/50) (x₀ := (pivot j:ℝ)) (x := s) (κ := 1/200)
    (fun x _ => aeval_hasDerivAt _ x) (fun x _ => aeval_hasDerivAt _ x)
    (fun x hx => (low_curvature (by rw [r34_domain_low]; exact hx) hj).le) hp hs
  have hv : (1/200000:ℝ)<aeval (pivot j:ℝ) (P .low j) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (low_tangent_values j hj).1
    rw [rational_eval]
    push_cast at h
    exact h
  have hd : |aeval (pivot j:ℝ) (P .low j).derivative|<1/100000 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (low_tangent_values j hj).2
    rw [rational_eval]
    push_cast at h
    exact h
  have hd2 : (aeval (pivot j:ℝ) (P .low j).derivative)^2<1/10000000000 := by
    obtain ⟨hl,hu⟩ := abs_lt.mp hd
    nlinarith
  have hsq := sq_nonneg
    (s-(pivot j:ℝ)+200*aeval (pivot j:ℝ) (P .low j).derivative)
  nlinarith

theorem low_secant_positive {s : ℝ} (hs : s∈domain .low) :
    (1/40000:ℝ)<aeval s (P .low 1) := by
  have hb := interval_lower (polynomial_series .low 1).1
    (by norm_num [rad] : 0≤rad Band.low) (domain_centered hs)
  have hn := (Rat.cast_lt (K := ℝ)).mpr low_secant_coefficients
  rw [show ((1/40000:ℚ):ℝ)=1/40000 by norm_num] at hn
  exact hn.trans_le hb

theorem high_growth {s : ℝ} (hs : s∈domain .high) {j : Fin 4} (hj : j≠1) :
    (-1/250000:ℝ)<aeval s (P .high j).derivative := by
  have hb := interval_lower (polynomial_series .high j).2.1
    (by norm_num [rad] : 0≤rad Band.high) (domain_centered hs)
  have hc : (-1/250000:ℝ)<
      (lowerOn 26 (mid .high) (rad .high) (P .high j).derivative:ℝ) := by
    exact_mod_cast high_growth_coefficients j hj
  exact hc.trans_le hb

theorem high_ordinary_positive {s : ℝ} (hs : s∈domain .high) {j : Fin 4} (hj : j≠1) :
    (137/25000000:ℝ)<aeval s (P .high j) := by
  rw [r34_domain_high] at hs
  have hh := derivative_reserve
    (f := fun x : ℝ => aeval x (P .high j))
    (df := fun x : ℝ => aeval x (P .high j).derivative)
    (l := (7/50:ℝ)) (u := 27/100) (x := 7/50) (y := s) (k := -1/250000)
    (fun x _ => (aeval_hasDerivAt _ x).continuousAt.continuousWithinAt)
    (fun x _ => aeval_hasDerivAt _ x)
    (fun x hx => (high_growth (by rw [r34_domain_high]; exact Ioo_subset_Icc_self hx) hj).le)
    (by norm_num) hs hs.1
  have hv : (3/500000:ℝ)<aeval (7/50:ℝ) (P .high j) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (high_start_values j hj)
    rw [show (7/50:ℝ)=((7/50:ℚ):ℝ) by norm_num,rational_eval]
    push_cast at h
    exact h
  have hs' : s≤27/100 := hs.2
  have hs'' : 7/50≤s := hs.1
  nlinarith

theorem high_secant_positive {s : ℝ} (hs : s∈domain .high) :
    (1/100000:ℝ)<aeval s (P .high 1) := by
  have hb := interval_lower (polynomial_series .high 1).1
    (by norm_num [rad] : 0≤rad Band.high) (domain_centered hs)
  have hn := (Rat.cast_lt (K := ℝ)).mpr high_secant_coefficients
  rw [show ((1/100000:ℚ):ℝ)=1/100000 by norm_num] at hn
  exact hn.trans_le hb

/-- All four geometric vertices are positive on both full sine bands. -/
theorem polynomial_positive {b : Band} {s : ℝ} (hs : s∈domain b) (j : Fin 4) :
    0<aeval s (P b j) := by
  cases b
  · by_cases hj : j=1
    · subst j
      exact lt_trans (by norm_num) (low_secant_positive hs)
    · exact lt_trans (by norm_num) (low_ordinary_positive hs hj)
  · by_cases hj : j=1
    · subst j
      exact lt_trans (by norm_num) (high_secant_positive hs)
    · exact lt_trans (by norm_num) (high_ordinary_positive hs hj)

end SquaresInCircles.Eight.TableFree.NegativeCapturePolynomials
