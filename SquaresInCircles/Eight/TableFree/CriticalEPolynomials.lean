module

public import SquaresInCircles.Eight.TableFree.PositiveScalarPolynomials
public import Mathlib.Data.Nat.Sqrt

/-!
# Whole-strip radical polynomials for the sharp supporting chain

Uncompiled source of the construction in Section 7 of the critical-strip
hand proof. There are three intrinsic chains: the lower comparison,
the upper comparison, and the enclosure between them. A sextic root
polynomial is formed algebraically, then proved to enclose the square
root by its squared residual on the entire interval. The displayed
kernel arithmetic proofs have not been executed or replayed.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.CriticalEPolynomials
open Polynomial WholeIntervalPolynomial

inductive Chain where
  | lower | upper | mixed
  deriving DecidableEq

instance : Fintype Chain where
  elems := {.lower, .upper, .mixed}
  complete x := by cases x <;> decide

def length : ℚ := 3/50
def parameter : ℚ[X] := C (1/10)+X
def uMinus : ℚ[X] := C (499/500)-C (127/200)*parameter
def uPlus : ℚ[X] := C (501/500)-C (16/25)*parameter
def a : Chain → ℚ[X] | .lower | .mixed => uMinus | .upper => uPlus
def b : Chain → ℚ[X] | .upper | .mixed => uPlus | .lower => uMinus
def qLower : ℚ := 19577/5000
def qUpper : ℚ := 1957767069/500000000
def epsilon : ℚ := 1/10000000

def sextic (P : ℚ[X]) : ℚ[X] := ∑n : Fin 7,monomial n.val (P.coeff n.val)
def binomial : Fin 7 → ℚ := ![1,1/2,-1/8,1/16,-5/128,7/256,-21/1024]

/-- Nearest multiple of 10^-12, chosen by a rational square comparison.
Its role is only to construct the polynomial; the root bound below is
proved independently by the full squared residual. -/
def rootSeed (A : ℚ[X]) : ℚ :=
  let v : ℚ := A.coeff 0*(10:ℚ)^24
  let n : ℕ := Nat.sqrt (Int.toNat ⌊v⌋)
  (if v≤((n:ℚ)+1/2)^2 then (n:ℚ) else (n:ℚ)+1)/(10:ℚ)^12

def rootPolynomial (A : ℚ[X]) : ℚ[X] :=
  let d := C (1/A.coeff 0)*(sextic A-C (A.coeff 0))
  sextic (C (rootSeed A)*∑j : Fin 7,C (binomial j)*d^j.val)
def rootLower (A : ℚ[X]) : ℚ[X] := rootPolynomial A-C epsilon
def rootUpper (A : ℚ[X]) : ℚ[X] := rootPolynomial A+C epsilon

def rArgLo (s : Chain) : ℚ[X] := C qLower-(b s)^2
def rArgHi (s : Chain) : ℚ[X] := C qUpper-(a s)^2
def rLo (s : Chain) : ℚ[X] := rootLower (rArgLo s)
def rHi (s : Chain) : ℚ[X] := rootUpper (rArgHi s)
def UArgLo (s : Chain) : ℚ[X] := C qLower-(2-a s)^2
def UArgHi (s : Chain) : ℚ[X] := C qUpper-(2-b s)^2
def ULo (s : Chain) : ℚ[X] := rootLower (UArgLo s)
def UHi (s : Chain) : ℚ[X] := rootUpper (UArgHi s)
def VLo (s : Chain) : ℚ[X] := 3-UHi s
def VHi (s : Chain) : ℚ[X] := 3-ULo s
def YArgLo (s : Chain) : ℚ[X] := C qLower-(VHi s)^2
def YArgHi (s : Chain) : ℚ[X] := C qUpper-(VLo s)^2
def YLo (s : Chain) : ℚ[X] := rootLower (YArgLo s)
def YHi (s : Chain) : ℚ[X] := rootUpper (YArgHi s)
def vLo (s : Chain) : ℚ[X] := 2-YHi s
def vHi (s : Chain) : ℚ[X] := 2-YLo s
def wArgLo (s : Chain) : ℚ[X] := C qLower-(vHi s)^2
def wArgHi (s : Chain) : ℚ[X] := C qUpper-(vLo s)^2
def wLo (s : Chain) : ℚ[X] := rootLower (wArgLo s)
def wHi (s : Chain) : ℚ[X] := rootUpper (wArgHi s)

def rootArgument (s : Chain) : Fin 8 → ℚ[X] :=
  ![rArgLo s,rArgHi s,UArgLo s,UArgHi s,YArgLo s,YArgHi s,wArgLo s,wArgHi s]
def coordinateLower (s : Chain) : Fin 6 → ℚ[X] := ![rLo s,ULo s,VLo s,YLo s,vLo s,wLo s]
def coordinateUpper (s : Chain) : Fin 6 → ℚ[X] := ![rHi s,UHi s,VHi s,YHi s,vHi s,wHi s]

def sineLo : ℚ[X] := PositiveScalarPolynomials.sine.comp parameter
def sineHi : ℚ[X] :=
  (PositiveScalarPolynomials.sine+C (1/1307674368000)*X^15).comp parameter
def cosineLo : ℚ[X] :=
  (PositiveScalarPolynomials.cosine-C (1/20922789888000)*X^16).comp parameter
def cosineHi : ℚ[X] := PositiveScalarPolynomials.cosine.comp parameter

def firstLo (s : Chain) : ℚ[X] := 2-cosineHi*(rHi s-1)+sineLo*a s
def firstHi (s : Chain) : ℚ[X] := 2-cosineLo*(rLo s-1)+sineHi*b s
def secondLo (s : Chain) : ℚ[X] := 1+cosineLo*vLo s-sineHi*(wHi s-1)
def secondHi (s : Chain) : ℚ[X] := 1+cosineHi*vHi s-sineLo*(wLo s-1)

def positionUpperAt (s : Chain) : ℚ[X] :=
  firstHi s*(cosineHi*b s+sineHi*rHi s)*UHi s*YHi s*wHi s-
    secondLo s*(2-b s)*VLo s*(cosineLo*wLo s+sineLo*vLo s)*rLo s

def positionLowerAt (s : Chain) : ℚ[X] :=
  firstLo s*(cosineLo*a s+sineLo*rLo s)*ULo s*YLo s*wLo s-
    secondHi s*(2-a s)*VHi s*(cosineHi*wHi s+sineHi*vHi s)*rHi s

def positionUpper : ℚ[X] := positionUpperAt .lower
def positionLower : ℚ[X] := positionLowerAt .upper

inductive Coefficient where
  | etaLower | etaUpper | kLower | kUpper | ellUpper | ellK
  | cLower | cUpper | ellCLower | ellCUpper | cK
  deriving DecidableEq

instance : Fintype Coefficient where
  elems := {.etaLower, .etaUpper, .kLower, .kUpper, .ellUpper, .ellK, .cLower, .cUpper, .ellCLower, .ellCUpper, .cK}
  complete x := by cases x <;> decide

def cleared : Coefficient → ℚ[X]
  | .etaLower => vLo .mixed-C (27/100)*wHi .mixed
  | .etaUpper => C (31/100)*wLo .mixed-vHi .mixed
  | .kLower => (cosineLo*wLo .mixed+sineLo*vLo .mixed)*VLo .mixed-
      C (37/40)*wHi .mixed*YHi .mixed
  | .kUpper => C (197/200)*wLo .mixed*YLo .mixed-
      (cosineHi*wHi .mixed+sineHi*vHi .mixed)*VHi .mixed
  | .ellUpper => C (67/100)*wLo .mixed*YLo .mixed*ULo .mixed-
      (cosineHi*wHi .mixed+sineHi*vHi .mixed)*VHi .mixed*(2-a .mixed)
  | .ellK => C (27/40)*ULo .mixed-(2-a .mixed)
  | .cLower => firstLo .mixed-C (37/40)*secondHi .mixed
  | .cUpper => secondLo .mixed-firstHi .mixed
  | .ellCLower => sineLo*rLo .mixed+cosineLo*a .mixed-C (63/100)*rHi .mixed
  | .ellCUpper => C (17/25)*rLo .mixed-sineHi*rHi .mixed-cosineHi*b .mixed
  | .cK => C (51/50)*ULo .lower*(sineLo*rLo .lower+cosineLo*a .lower)-
      (2-a .lower)*rHi .lower

/-! ### Exact list arithmetic for the kernel checks

The polynomials above are noncomputable `ℚ[X]` values, so the kernel cannot evaluate them.
Each one is mirrored by a coefficient list (`toPoly` of the list is the polynomial); the
reserves are then decided by the kernel on the lists. The expansion identities need no
computation: an exact Chebyshev expansion holds for every polynomial of degree at most `D`. -/

private def ladd : List ℚ → List ℚ → List ℚ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a+b) :: ladd p q

private def lsmul (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: p => (c*a) :: lsmul c p

private def lneg : List ℚ → List ℚ
  | [] => []
  | a :: p => (-a) :: lneg p

private def lsub : List ℚ → List ℚ → List ℚ
  | [], q => lneg q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a-b) :: lsub p q

/-- Multiplication by `X`, keeping the empty list empty. -/
private def lshift : List ℚ → List ℚ
  | [] => []
  | r => 0 :: r

private def lmul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: p, q => ladd (lsmul a q) (lshift (lmul p q))

private def lpow (p : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n+1 => lmul (lpow p n) p

private def lcomp : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | c :: p, q => ladd [c] (lmul q (lcomp p q))

private noncomputable def toPoly : List ℚ → ℚ[X]
  | [] => 0
  | c :: p => C c+X*toPoly p

@[simp] private theorem toPoly_nil : toPoly []=0 := rfl
@[simp] private theorem toPoly_cons (c : ℚ) (p : List ℚ) :
    toPoly (c :: p)=C c+X*toPoly p := rfl

private theorem toPoly_single (c : ℚ) : toPoly [c]=C c := by simp

private theorem toPoly_add (p q : List ℚ) : toPoly (ladd p q)=toPoly p+toPoly q := by
  induction p generalizing q with
  | nil => simp [ladd]
  | cons a p ih =>
    cases q with
    | nil => simp [ladd]
    | cons b q => simp only [ladd,toPoly_cons,ih,C_add]; ring

private theorem toPoly_smul (c : ℚ) (p : List ℚ) : toPoly (lsmul c p)=C c*toPoly p := by
  induction p with
  | nil => simp [lsmul]
  | cons a p ih => simp only [lsmul,toPoly_cons,ih,C_mul]; ring

private theorem toPoly_neg (p : List ℚ) : toPoly (lneg p)=-toPoly p := by
  induction p with
  | nil => simp [lneg]
  | cons a p ih => simp only [lneg,toPoly_cons,ih,C_neg]; ring

private theorem toPoly_sub (p q : List ℚ) : toPoly (lsub p q)=toPoly p-toPoly q := by
  induction p generalizing q with
  | nil => simp [lsub,toPoly_neg]
  | cons a p ih =>
    cases q with
    | nil => simp [lsub]
    | cons b q => simp only [lsub,toPoly_cons,ih,C_sub]; ring

private theorem toPoly_shift (r : List ℚ) : toPoly (lshift r)=X*toPoly r := by
  cases r <;> simp [lshift]

private theorem toPoly_mul (p q : List ℚ) : toPoly (lmul p q)=toPoly p*toPoly q := by
  induction p with
  | nil => simp [lmul]
  | cons a p ih => simp only [lmul,toPoly_add,toPoly_smul,toPoly_shift,toPoly_cons,ih]; ring

private theorem toPoly_pow (p : List ℚ) (n : ℕ) : toPoly (lpow p n)=toPoly p^n := by
  induction n with
  | zero => simp [lpow]
  | succ n ih => rw [lpow,toPoly_mul,ih,pow_succ]

private theorem toPoly_comp (p q : List ℚ) : toPoly (lcomp p q)=(toPoly p).comp (toPoly q) := by
  induction p with
  | nil => simp [lcomp]
  | cons c p ih =>
    simp only [lcomp,toPoly_add,toPoly_mul,ih,toPoly_cons,toPoly_nil,add_comp,mul_comp,
      C_comp,X_comp]
    ring

private theorem coeff_toPoly (l : List ℚ) (n : ℕ) : (toPoly l).coeff n=l.getD n 0 := by
  induction l generalizing n with
  | nil => simp
  | cons c l ih =>
    cases n with
    | zero => simp
    | succ n => simp [coeff_X_mul,ih]

private theorem natDegree_toPoly_le {l : List ℚ} {n : ℕ} (h : l.length ≤ n+1) :
    (toPoly l).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_toPoly]
  exact List.getD_eq_default _ _ (by omega)

private theorem sextic_toPoly (l : List ℚ) : sextic (toPoly l)=toPoly (l.take 7) := by
  ext m
  rw [coeff_toPoly,sextic,finsetSum_coeff]
  simp only [coeff_monomial,coeff_toPoly,Fin.sum_univ_seven]
  rcases m with _|_|_|_|_|_|_|m <;> simp [List.getD_eq_getElem?_getD]

/-- The seed of a root polynomial, with the integer square root supplied. -/
private def seedOf (A : List ℚ) (n : ℕ) : ℚ :=
  (if A.getD 0 0*(10:ℚ)^24 ≤ ((n:ℚ)+1/2)^2 then (n:ℚ) else (n:ℚ)+1)/(10:ℚ)^12

private def seedOK (A : List ℚ) (n : ℕ) : Bool :=
  let m := Int.toNat ⌊A.getD 0 0*(10:ℚ)^24⌋
  decide (n*n ≤ m) && decide (m < (n+1)*(n+1))

private theorem rootSeed_toPoly {A : List ℚ} {n : ℕ} (h : seedOK A n=true) :
    rootSeed (toPoly A)=seedOf A n := by
  simp only [seedOK,Bool.and_eq_true,decide_eq_true_eq] at h
  have hs : Nat.sqrt (Int.toNat ⌊A.getD 0 0*(10:ℚ)^24⌋)=n := (Nat.eq_sqrt.mpr h).symm
  simp only [rootSeed,seedOf,coeff_toPoly,hs]

private def binSum (d : List ℚ) : List ℚ :=
  ladd (lsmul 1 (lpow d 0)) (ladd (lsmul (1/2) (lpow d 1)) (ladd (lsmul (-1/8) (lpow d 2))
    (ladd (lsmul (1/16) (lpow d 3)) (ladd (lsmul (-5/128) (lpow d 4))
      (ladd (lsmul (7/256) (lpow d 5)) (lsmul (-21/1024) (lpow d 6)))))))

private def rootPolyL (A : List ℚ) (n : ℕ) : List ℚ :=
  (lsmul (seedOf A n) (binSum (lsmul (1/A.getD 0 0) (lsub (A.take 7) [A.getD 0 0])))).take 7

private def rootLowerL (A : List ℚ) (n : ℕ) : List ℚ := lsub (rootPolyL A n) [epsilon]
private def rootUpperL (A : List ℚ) (n : ℕ) : List ℚ := ladd (rootPolyL A n) [epsilon]

private theorem rootPolynomial_toPoly {A : List ℚ} {n : ℕ} (h : seedOK A n=true) :
    rootPolynomial (toPoly A)=toPoly (rootPolyL A n) := by
  rw [rootPolynomial,rootPolyL,← sextic_toPoly,rootSeed_toPoly h]
  congr 1
  simp only [Fin.sum_univ_seven,binSum,toPoly_add,toPoly_smul,toPoly_pow,toPoly_sub,
    sextic_toPoly,coeff_toPoly,toPoly_single,binomial]
  have h3 : ((3:Fin 7):ℕ)=3 := rfl
  have h4 : ((4:Fin 7):ℕ)=4 := rfl
  have h5 : ((5:Fin 7):ℕ)=5 := rfl
  have h6 : ((6:Fin 7):ℕ)=6 := rfl
  simp only [Fin.val_zero,Fin.val_one,Fin.val_two,h3,h4,h5,h6,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val,pow_zero,C_1]
  ring

private theorem rootLower_toPoly {A : List ℚ} {n : ℕ} (h : seedOK A n=true) :
    rootLower (toPoly A)=toPoly (rootLowerL A n) := by
  rw [rootLower,rootLowerL,toPoly_sub,rootPolynomial_toPoly h,toPoly_single]

private theorem rootUpper_toPoly {A : List ℚ} {n : ℕ} (h : seedOK A n=true) :
    rootUpper (toPoly A)=toPoly (rootUpperL A n) := by
  rw [rootUpper,rootUpperL,toPoly_add,rootPolynomial_toPoly h,toPoly_single]

/-! The exact Chebyshev expansion of a monomial -/

private theorem mc_of {i j k : ℕ} (h : i=j+2*k) :
    monomialCoefficient i j=(if j=0 then 1 else 2)*(i.choose k : ℚ)/(2:ℚ)^i := by
  subst h
  have h1 : j+2*k-j=2*k := by omega
  have h2 : 2*k/2=k := by omega
  simp [monomialCoefficient,h1,h2]

private theorem mc_zero {i j : ℕ} (h : ¬(j ≤ i ∧ (i-j)%2=0)) : monomialCoefficient i j=0 := by
  simp only [monomialCoefficient]
  rw [ite_eq_right h]

private theorem mc_gt {i j : ℕ} (h : i < j) : monomialCoefficient i j=0 := mc_zero (by omega)

private theorem mc_rec2 (i j : ℕ) :
    monomialCoefficient (i+1) (j+2)=
      (monomialCoefficient i (j+1)+monomialCoefficient i (j+3))/2 := by
  by_cases h : j+1 ≤ i ∧ (i-(j+1))%2=0
  · obtain ⟨k,hk⟩ : ∃ k, i=j+1+2*k := ⟨(i-(j+1))/2,by omega⟩
    rw [mc_of (k := k) (by omega),mc_of (k := k) hk]
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      rw [mc_zero (by omega)]
      simp [hk,pow_succ]
      ring
    · obtain ⟨k',rfl⟩ : ∃ k', k=k'+1 := ⟨k-1,by omega⟩
      rw [mc_of (k := k') (by omega),hk]
      simp only [Nat.choose_succ_succ,Nat.cast_add,pow_succ]
      simp
      ring
  · rw [mc_zero (by omega),mc_zero (by omega),mc_zero (by omega)]
    simp

private theorem mc_rec1 (i : ℕ) :
    monomialCoefficient (i+1) 1=monomialCoefficient i 0+monomialCoefficient i 2/2 := by
  by_cases h : i%2=0
  · obtain ⟨k,hk⟩ : ∃ k, i=2*k := ⟨i/2,by omega⟩
    rw [mc_of (k := k) (by omega),mc_of (k := k) (by omega)]
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      rw [mc_zero (by omega)]
      simp [hk]
    · obtain ⟨k',rfl⟩ : ∃ k', k=k'+1 := ⟨k-1,by omega⟩
      rw [mc_of (k := k') (by omega),hk]
      simp only [Nat.choose_succ_succ,Nat.cast_add,pow_succ]
      simp
      ring
  · rw [mc_zero (by omega),mc_zero (by omega),mc_zero (by omega)]
    simp

private theorem mc_rec0 (i : ℕ) :
    monomialCoefficient (i+1) 0=monomialCoefficient i 1/2 := by
  by_cases h : i%2=1
  · obtain ⟨k,hk⟩ : ∃ k, i=1+2*k := ⟨i/2,by omega⟩
    rw [mc_of (k := k+1) (by omega),mc_of (k := k) (by omega),hk]
    have hs : (2*k+1).choose (k+1)=(2*k+1).choose k := by
      rw [Nat.choose_symm_of_eq_add]; omega
    rw [show 1+2*k+1=(2*k+1)+1 by ring,Nat.choose_succ_succ,hs,show 1+2*k=2*k+1 by ring]
    simp [pow_succ]
    ring
  · rw [mc_zero (by omega),mc_zero (by omega)]
    simp

private def chebSum (m : ℕ → ℚ) (N : ℕ) : ℚ[X] :=
  ∑ j∈Finset.range N,C (m j)*Polynomial.Chebyshev.T ℚ (j : ℤ)

private theorem chebSum_extend (m : ℕ → ℚ) (N k : ℕ) (h : ∀ j, N ≤ j → m j=0) :
    chebSum m (N+k)=chebSum m N := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc,chebSum,Finset.sum_range_succ,← chebSum,ih,h (N+k) (by omega)]
    simp

private theorem X_mul_T (j : ℕ) :
    X*Polynomial.Chebyshev.T ℚ ((j:ℤ)+1)=
      C (1/2)*(Polynomial.Chebyshev.T ℚ ((j:ℤ)+2)+Polynomial.Chebyshev.T ℚ (j:ℤ)) := by
  rw [Polynomial.Chebyshev.T_add_two]
  have h2 : (C (1/2) : ℚ[X])*2=1 := by rw [← C_ofNat,← C_mul]; norm_num
  linear_combination (-X*Polynomial.Chebyshev.T ℚ ((j:ℤ)+1))*h2

private theorem chebSum_mono (i : ℕ) : ∀ N, i < N → chebSum (monomialCoefficient i) N=X^i := by
  induction i with
  | zero =>
    intro N hN
    obtain ⟨M,rfl⟩ : ∃ M, N=1+M := ⟨N-1,by omega⟩
    rw [chebSum_extend _ 1 M (fun j hj => mc_gt (by omega))]
    simp [chebSum,monomialCoefficient]
  | succ i ih =>
    intro N hN
    rw [← chebSum_extend _ N 4 (fun j hj => mc_gt (by omega))]
    obtain ⟨L,hL⟩ : ∃ L, N+4=L+6 := ⟨N-2,by omega⟩
    rw [hL,pow_succ,← ih (L+5) (by omega)]
    set m := monomialCoefficient i with hm
    have hT (j : ℕ) : Polynomial.Chebyshev.T ℚ ((j+2 : ℕ) : ℤ)=
        Polynomial.Chebyshev.T ℚ ((j:ℤ)+2) := by push_cast; ring_nf
    have hT1 (j : ℕ) : Polynomial.Chebyshev.T ℚ ((j+1 : ℕ) : ℤ)=
        Polynomial.Chebyshev.T ℚ ((j:ℤ)+1) := by push_cast; ring_nf
    have hz5 : m (L+5)=0 := mc_gt (by omega)
    have hz6 : m (L+6)=0 := mc_gt (by omega)
    have hl : chebSum (monomialCoefficient (i+1)) (L+6)=
        ∑ j∈Finset.range (L+4),C ((m (j+1)+m (j+3))/2)*Polynomial.Chebyshev.T ℚ ((j:ℤ)+2)+
          C (m 0+m 2/2)*X+C (m 1/2) := by
      rw [chebSum,Finset.sum_range_succ' _ (L+5),Finset.sum_range_succ' _ (L+4)]
      simp only [hT,mc_rec2,mc_rec0,← hm]
      simp [mc_rec1,← hm]
    have hr : chebSum m (L+5)*X=
        ∑ j∈Finset.range (L+4),C (m (j+1))*(C (1/2)*(Polynomial.Chebyshev.T ℚ ((j:ℤ)+2)+
          Polynomial.Chebyshev.T ℚ (j:ℤ)))+C (m 0)*X := by
      rw [chebSum,Finset.sum_range_succ' _ (L+4),add_mul,Finset.sum_mul]
      simp only [hT1]
      congr 1
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← X_mul_T]; ring
      · simp
    rw [hl,hr]
    set T := fun j : ℤ => Polynomial.Chebyshev.T ℚ j with hTdef
    have e (x : ℚ) : C (x/2)=C x*C (1/2) := by rw [← C_mul]; ring_nf
    have hsum : ∑ j∈Finset.range (L+4),C ((m (j+1)+m (j+3))/2)*T ((j:ℤ)+2)=
        ∑ j∈Finset.range (L+4),C (m (j+1))*(C (1/2)*T ((j:ℤ)+2))+
          ∑ j∈Finset.range (L+4),C (m (j+3))*(C (1/2)*T ((j:ℤ)+2)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [add_div,C_add,e (m (j+1)),e (m (j+3))]; ring
    have hsum2 : ∑ j∈Finset.range (L+4),C (m (j+1))*(C (1/2)*(T ((j:ℤ)+2)+T (j:ℤ)))=
        ∑ j∈Finset.range (L+4),C (m (j+1))*(C (1/2)*T ((j:ℤ)+2))+
          ∑ j∈Finset.range (L+4),C (m (j+1))*(C (1/2)*T (j:ℤ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    have key : ∑ j∈Finset.range (L+4),C (m (j+3))*(C (1/2)*T ((j:ℤ)+2))+C (m 2)*C (1/2)*X+
        C (m 1)*C (1/2)=
        ∑ j∈Finset.range (L+4),C (m (j+1))*(C (1/2)*T (j:ℤ)) := by
      rw [Finset.sum_range_succ' (fun j => C (m (j+1))*(C (1/2)*T (j:ℤ))) (L+3),
        Finset.sum_range_succ' _ (L+2),Finset.sum_range_succ _ (L+3),Finset.sum_range_succ _ (L+2)]
      have h3 : L+2+3=L+5 := by ring
      have h4 : L+3+3=L+6 := by ring
      simp only [h3,h4,hz5,hz6,C_0,zero_mul,add_zero]
      simp only [hTdef]
      push_cast
      simp only [Polynomial.Chebyshev.T_zero,Polynomial.Chebyshev.T_one]
      have hc (j : ℕ) : ((j:ℤ)+1+1)=(j:ℤ)+2 := by ring
      simp only [hc,mul_one]
      ring
    rw [hsum,hsum2,C_add,e (m 2),e (m 1)]
    linear_combination key

private theorem series_eq_chebSum (D : ℕ) (b : ℕ → ℚ) : series D b=chebSum b (D+1) := by
  rw [series,chebSum,Finset.sum_range_succ',
    Fin.sum_univ_eq_sum_range (fun j => C (b (j+1))*Polynomial.Chebyshev.T ℚ ((j:ℤ)+1)) D]
  push_cast
  simp only [Polynomial.Chebyshev.T_zero,mul_one]
  ring

private theorem series_mono {D i : ℕ} (hi : i ≤ D) : series D (monomialCoefficient i)=X^i := by
  rw [series_eq_chebSum]
  exact chebSum_mono i (D+1) (by omega)

private theorem expansion_linear (D : ℕ) (p : ℚ[X]) :
    expansion D p=∑ i∈Finset.range (D+1),C (p.coeff i)*series D (monomialCoefficient i) := by
  simp only [expansion,series,coefficient,map_sum,map_mul,mul_add,Finset.sum_add_distrib,
    Finset.sum_mul,Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  ring

/-- Every polynomial of degree at most `D` equals its degree-`D` Chebyshev expansion. -/
private theorem expansion_self {D : ℕ} (p : ℚ[X]) (hp : p.natDegree ≤ D) : p=expansion D p := by
  rw [expansion_linear]
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (n := D+1) (by omega)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [series_mono (by simp at hi; omega)]

private theorem sum_range_list (f : ℕ → ℚ) (n : ℕ) :
    ∑ i∈Finset.range n,f i=((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,List.range_succ,List.map_append,List.sum_append]; simp

/-! Sparse Chebyshev coefficients with integer rows -/

private def zadd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a+b) :: zadd p q

/-- `2^(i+1)` times the next row of Chebyshev coefficients of the powers of `X`. -/
private def nextRowZ (r : List ℤ) : List ℤ :=
  zadd (zadd (0 :: r) (r.drop 1)) [0,r.getD 0 0]

private def rowsAux : ℕ → List ℤ → List (List ℤ)
  | 0, r => [r]
  | n+1, r => r :: rowsAux n (nextRowZ r)

private def rowZ : ℕ → List ℤ
  | 0 => [1]
  | i+1 => nextRowZ (rowZ i)

private theorem getD_zadd (p q : List ℤ) (j : ℕ) :
    (zadd p q).getD j 0=p.getD j 0+q.getD j 0 := by
  induction p generalizing q j with
  | nil => simp [zadd]
  | cons a p ih =>
    cases q with
    | nil => simp [zadd]
    | cons b q =>
      cases j with
      | zero => simp [zadd]
      | succ j => simp only [zadd,List.getD_cons_succ,ih]

private theorem getD_drop_oneZ (r : List ℤ) (j : ℕ) : (r.drop 1).getD j 0=r.getD (j+1) 0 := by
  cases r <;> simp

private theorem rowZ_getD (i j : ℕ) :
    (((rowZ i).getD j 0 : ℤ) : ℚ)=(2:ℚ)^i*monomialCoefficient i j := by
  induction i generalizing j with
  | zero =>
    rcases j with _|j
    · simp [rowZ,monomialCoefficient]
    · rw [mc_gt (by omega)]; simp [rowZ]
  | succ i ih =>
    simp only [rowZ,nextRowZ,getD_zadd,getD_drop_oneZ]
    match j with
    | 0 =>
      simp only [List.getD_cons_zero,Int.cast_add,Int.cast_zero,ih,mc_rec0]
      ring
    | 1 =>
      simp only [List.getD_cons_zero,List.getD_cons_succ,Int.cast_add,ih,mc_rec1]
      ring
    | j+2 =>
      simp only [List.getD_cons_succ,List.getD_nil,Int.cast_add,Int.cast_zero,ih,mc_rec2]
      rw [show j+2+1=j+3 by ring]
      ring

private theorem rowsAux_getD (n i : ℕ) (r : List ℤ) (hi : i ≤ n) :
    (rowsAux n r).getD i []=Nat.iterate nextRowZ i r := by
  induction n generalizing i r with
  | zero => obtain rfl : i=0 := by omega
            simp [rowsAux]
  | succ n ih =>
    rcases i with _|i
    · simp [rowsAux]
    · simp only [rowsAux,List.getD_cons_succ,ih i _ (by omega),Function.iterate_succ_apply]

private theorem rowZ_eq_iterate (i : ℕ) : rowZ i=Nat.iterate nextRowZ i [1] := by
  induction i with
  | zero => rfl
  | succ i ih => rw [rowZ,ih,Function.iterate_succ_apply']

/-- `L` with its `i`-th coefficient divided by `2^i`. -/
private def halveL : ℕ → List ℚ → List ℚ
  | _, [] => []
  | i, a :: p => a/((2^i : ℕ) : ℚ) :: halveL (i+1) p

private theorem getD_halveL (L : List ℚ) (k i : ℕ) :
    (halveL k L).getD i 0=L.getD i 0/((2^(k+i) : ℕ) : ℚ) := by
  induction L generalizing k i with
  | nil => simp [halveL]
  | cons a p ih =>
    cases i with
    | zero => simp [halveL]
    | succ i => simp only [halveL,List.getD_cons_succ,ih]; ring_nf

/-- The Chebyshev coefficient vector on `[-1,1]` of a coefficient list, keeping only the
terms with `j ≤ i` and `i ≡ j (mod 2)`. -/
private def chebL (D : ℕ) (L : List ℚ) (rows : List (List ℤ)) (j : ℕ) : ℚ :=
  (((List.range (D+1)).filter (fun i => decide (j ≤ i ∧ (i-j)%2=0))).map
    (fun i => (halveL 0 L).getD i 0*(((rows.getD i []).getD j 0 : ℤ) : ℚ))).sum

private theorem list_sum_filter (l : List ℕ) (p : ℕ → Bool) (f : ℕ → ℚ)
    (h : ∀ i, p i=false → f i=0) : (l.map f).sum=((l.filter p).map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : p a=true
    · simp [ha,ih]
    · simp [ha,ih,h a (by simpa using ha)]

private theorem coefficient_toPoly (D : ℕ) (L : List ℚ) (j : ℕ) :
    coefficient D (toPoly L) j=chebL D L (rowsAux D [1]) j := by
  rw [coefficient,sum_range_list,chebL]
  rw [list_sum_filter _ (fun i => decide (j ≤ i ∧ (i-j)%2=0)) _ (by
    intro i hi
    simp only [decide_eq_false_iff_not] at hi
    simp [mc_zero hi])]
  congr 1
  refine List.map_congr_left (fun i hi => ?_)
  have hiD : i ≤ D := by
    have := (List.mem_filter.mp hi).1
    simp at this; omega
  rw [coeff_toPoly,rowsAux_getD D i [1] hiD,← rowZ_eq_iterate,rowZ_getD,getD_halveL,zero_add]
  push_cast
  field_simp

private def lowerL (D : ℕ) (b : ℕ → ℚ) : ℚ := b 0-((List.range D).map (fun j => |b (j+1)|)).sum
private def upperL (D : ℕ) (b : ℕ → ℚ) : ℚ := b 0+((List.range D).map (fun j => |b (j+1)|)).sum

private def lowerOnL (D : ℕ) (L : List ℚ) : ℚ := lowerL D (chebL D L (rowsAux D [1]))
private def upperOnL (D : ℕ) (L : List ℚ) : ℚ := upperL D (chebL D L (rowsAux D [1]))

/-- The centered variable: `X ↦ length/2 + (length/2) X`. -/
private def affL : List ℚ := [(0+length)/2,(length-0)/2]

private theorem centered_eq (p : ℚ[X]) : centered 0 length p=p.comp (toPoly affL) := by
  rw [centered]
  congr 1
  simp [affine,affL]

private theorem lowerOn_of {D : ℕ} {p : ℚ[X]} {L : List ℚ}
    (h : p.comp (toPoly affL)=toPoly L) : lowerOn D 0 length p=lowerOnL D L := by
  simp only [lowerOn,lower,lowerOnL,lowerL,centered_eq,h,coefficient_toPoly,
    Fin.sum_univ_eq_sum_range (fun j => |chebL D L (rowsAux D [1]) (j+1)|) D,sum_range_list]

private theorem upperOn_of {D : ℕ} {p : ℚ[X]} {L : List ℚ}
    (h : p.comp (toPoly affL)=toPoly L) : upperOn D 0 length p=upperOnL D L := by
  simp only [upperOn,upper,upperOnL,upperL,centered_eq,h,coefficient_toPoly,
    Fin.sum_univ_eq_sum_range (fun j => |chebL D L (rowsAux D [1]) (j+1)|) D,sum_range_list]

private theorem identity_of {D : ℕ} {p : ℚ[X]} {L : List ℚ}
    (h : p.comp (toPoly affL)=toPoly L) (hl : L.length ≤ D+1) :
    centered 0 length p=expansion D (centered 0 length p) := by
  rw [centered_eq,h]
  exact expansion_self _ (natDegree_toPoly_le hl)

/-! The sixteen exact roots of the chains

The mixed chain takes its lower roots from the `uMinus` side and its upper roots from the
`uPlus` side, so the three chains use sixteen distinct roots. Each is named once, so that the
kernel computes it once. -/

private def monoC (c : ℚ) (k : ℕ) : List ℚ := List.replicate k 0++[c]

private theorem toPoly_monoC (c : ℚ) (k : ℕ) : toPoly (monoC c k)=C c*X^k := by
  induction k with
  | zero => simp [monoC]
  | succ k ih =>
    simp only [monoC,List.replicate_succ,List.cons_append] at ih ⊢
    rw [toPoly_cons,ih]
    simp [pow_succ]
    ring

private def paramL : List ℚ := [1/10,1]
private def uMinusL : List ℚ := lsub [499/500] (lsmul (127/200) paramL)
private def uPlusL : List ℚ := lsub [501/500] (lsmul (16/25) paramL)

private def argRLo (x : List ℚ) : List ℚ := lsub [qLower] (lpow x 2)
private def argRHi (x : List ℚ) : List ℚ := lsub [qUpper] (lpow x 2)
private def argULo (x : List ℚ) : List ℚ := lsub [qLower] (lpow (lsub [2] x) 2)
private def argUHi (x : List ℚ) : List ℚ := lsub [qUpper] (lpow (lsub [2] x) 2)
private def argYLo (u : List ℚ) : List ℚ := lsub [qLower] (lpow (lsub [3] u) 2)
private def argYHi (u : List ℚ) : List ℚ := lsub [qUpper] (lpow (lsub [3] u) 2)
private def argWLo (y : List ℚ) : List ℚ := lsub [qLower] (lpow (lsub [2] y) 2)
private def argWHi (y : List ℚ) : List ℚ := lsub [qUpper] (lpow (lsub [2] y) 2)

private def rpRLoM : List ℚ := rootPolyL (argRLo uMinusL) 1744164484789
private def rpRLoP : List ℚ := rootPolyL (argRLo uPlusL) 1742284706929
private def rpRHiM : List ℚ := rootPolyL (argRHi uMinusL) 1744202937734
private def rpRHiP : List ℚ := rootPolyL (argRHi uPlusL) 1742323201360
private def rpULoM : List ℚ := rootPolyL (argULo uMinusL) 1667366111566
private def rpULoP : List ℚ := rootPolyL (argULo uPlusL) 1669597556299
private def rpUHiM : List ℚ := rootPolyL (argUHi uMinusL) 1667406335600
private def rpUHiP : List ℚ := rootPolyL (argUHi uPlusL) 1669637726574
private def rpYLoM : List ℚ := rootPolyL (argYLo (lsub rpULoM [epsilon])) 1462698414872
private def rpYLoP : List ℚ := rootPolyL (argYLo (lsub rpULoP [epsilon])) 1464728326930
private def rpYHiM : List ℚ := rootPolyL (argYHi (ladd rpUHiM [epsilon])) 1462781094395
private def rpYHiP : List ℚ := rootPolyL (argYHi (ladd rpUHiP [epsilon])) 1464810781472
private def rpWLoM : List ℚ := rootPolyL (argWLo (lsub rpYLoM [epsilon])) 1904391477390
private def rpWLoP : List ℚ := rootPolyL (argWLo (lsub rpYLoP [epsilon])) 1904963025613
private def rpWHiM : List ℚ := rootPolyL (argWHi (ladd rpYHiM [epsilon])) 1904450076243
private def rpWHiP : List ℚ := rootPolyL (argWHi (ladd rpYHiP [epsilon])) 1905021455367

/-! Centered lists -/

private def cen (L : List ℚ) : List ℚ := lcomp L affL

private def cuM : List ℚ := cen uMinusL
private def cuP : List ℚ := cen uPlusL
private def cRLoM : List ℚ := cen rpRLoM
private def cRLoP : List ℚ := cen rpRLoP
private def cRHiM : List ℚ := cen rpRHiM
private def cRHiP : List ℚ := cen rpRHiP
private def cULoM : List ℚ := cen rpULoM
private def cULoP : List ℚ := cen rpULoP
private def cUHiM : List ℚ := cen rpUHiM
private def cUHiP : List ℚ := cen rpUHiP
private def cYLoM : List ℚ := cen rpYLoM
private def cYLoP : List ℚ := cen rpYLoP
private def cYHiM : List ℚ := cen rpYHiM
private def cYHiP : List ℚ := cen rpYHiP
private def cWLoM : List ℚ := cen rpWLoM
private def cWLoP : List ℚ := cen rpWLoP
private def cWHiM : List ℚ := cen rpWHiM
private def cWHiP : List ℚ := cen rpWHiP

private def lo (L : List ℚ) : List ℚ := lsub L [epsilon]
private def hi (L : List ℚ) : List ℚ := ladd L [epsilon]
private def qsq (q : ℚ) (x : List ℚ) : List ℚ := lsub [q] (lpow x 2)

private def sineL : List ℚ :=
  lsub (ladd (lsub (ladd (lsub (ladd (lsub (monoC 1 1) (monoC (1/6) 3)) (monoC (1/120) 5))
    (monoC (1/5040) 7)) (monoC (1/362880) 9)) (monoC (1/39916800) 11))
    (monoC (1/6227020800) 13)) (monoC (1/1307674368000) 15)
private def cosineL : List ℚ :=
  ladd (lsub (ladd (lsub (ladd (lsub (ladd (lsub [1] (monoC (1/2) 2)) (monoC (1/24) 4))
    (monoC (1/720) 6)) (monoC (1/40320) 8)) (monoC (1/3628800) 10)) (monoC (1/479001600) 12))
    (monoC (1/87178291200) 14)) (monoC (1/20922789888000) 16)
private def cparL : List ℚ := cen paramL
private def csLo : List ℚ := lcomp sineL cparL
private def csHi : List ℚ := lcomp (ladd sineL (monoC (1/1307674368000) 15)) cparL
private def ccLo : List ℚ := lcomp (lsub cosineL (monoC (1/20922789888000) 16)) cparL
private def ccHi : List ℚ := lcomp cosineL cparL

/-- The centered chain of one choice of sides. -/
private structure CQ where
  a : List ℚ
  b : List ℚ
  rLo : List ℚ
  rHi : List ℚ
  ULo : List ℚ
  UHi : List ℚ
  YLo : List ℚ
  YHi : List ℚ
  wLo : List ℚ
  wHi : List ℚ

private def CQ.VLo (c : CQ) : List ℚ := lsub [3] c.UHi
private def CQ.VHi (c : CQ) : List ℚ := lsub [3] c.ULo
private def CQ.vLo (c : CQ) : List ℚ := lsub [2] c.YHi
private def CQ.vHi (c : CQ) : List ℚ := lsub [2] c.YLo

private def cqOf : Chain → CQ
  | .lower => ⟨cuM,cuM,lo cRLoM,hi cRHiM,lo cULoM,hi cUHiM,lo cYLoM,hi cYHiM,lo cWLoM,hi cWHiM⟩
  | .upper => ⟨cuP,cuP,lo cRLoP,hi cRHiP,lo cULoP,hi cUHiP,lo cYLoP,hi cYHiP,lo cWLoP,hi cWHiP⟩
  | .mixed => ⟨cuM,cuP,lo cRLoP,hi cRHiM,lo cULoM,hi cUHiP,lo cYLoM,hi cYHiP,lo cWLoM,hi cWHiP⟩

private def CQ.firstLo (c : CQ) : List ℚ :=
  ladd (lsub [2] (lmul ccHi (lsub c.rHi [1]))) (lmul csLo c.a)
private def CQ.firstHi (c : CQ) : List ℚ :=
  ladd (lsub [2] (lmul ccLo (lsub c.rLo [1]))) (lmul csHi c.b)
private def CQ.secondLo (c : CQ) : List ℚ :=
  lsub (ladd [1] (lmul ccLo c.vLo)) (lmul csHi (lsub c.wHi [1]))
private def CQ.secondHi (c : CQ) : List ℚ :=
  lsub (ladd [1] (lmul ccHi c.vHi)) (lmul csLo (lsub c.wLo [1]))

private def CQ.posUpper (c : CQ) : List ℚ :=
  lsub (lmul (lmul (lmul (lmul c.firstHi (ladd (lmul ccHi c.b) (lmul csHi c.rHi)))
      c.UHi) c.YHi) c.wHi)
    (lmul (lmul (lmul (lmul c.secondLo (lsub [2] c.b)) c.VLo)
      (ladd (lmul ccLo c.wLo) (lmul csLo c.vLo))) c.rLo)
private def CQ.posLower (c : CQ) : List ℚ :=
  lsub (lmul (lmul (lmul (lmul c.firstLo (ladd (lmul ccLo c.a) (lmul csLo c.rLo)))
      c.ULo) c.YLo) c.wLo)
    (lmul (lmul (lmul (lmul c.secondHi (lsub [2] c.a)) c.VHi)
      (ladd (lmul ccHi c.wHi) (lmul csHi c.vHi))) c.rHi)

private def clearedQ : Coefficient → List ℚ
  | .etaLower => lsub (cqOf .mixed).vLo (lsmul (27/100) (cqOf .mixed).wHi)
  | .etaUpper => lsub (lsmul (31/100) (cqOf .mixed).wLo) (cqOf .mixed).vHi
  | .kLower => lsub (lmul (ladd (lmul ccLo (cqOf .mixed).wLo) (lmul csLo (cqOf .mixed).vLo))
      (cqOf .mixed).VLo) (lmul (lsmul (37/40) (cqOf .mixed).wHi) (cqOf .mixed).YHi)
  | .kUpper => lsub (lmul (lsmul (197/200) (cqOf .mixed).wLo) (cqOf .mixed).YLo)
      (lmul (ladd (lmul ccHi (cqOf .mixed).wHi) (lmul csHi (cqOf .mixed).vHi)) (cqOf .mixed).VHi)
  | .ellUpper => lsub (lmul (lmul (lsmul (67/100) (cqOf .mixed).wLo) (cqOf .mixed).YLo)
      (cqOf .mixed).ULo)
      (lmul (lmul (ladd (lmul ccHi (cqOf .mixed).wHi) (lmul csHi (cqOf .mixed).vHi))
        (cqOf .mixed).VHi) (lsub [2] (cqOf .mixed).a))
  | .ellK => lsub (lsmul (27/40) (cqOf .mixed).ULo) (lsub [2] (cqOf .mixed).a)
  | .cLower => lsub (cqOf .mixed).firstLo (lsmul (37/40) (cqOf .mixed).secondHi)
  | .cUpper => lsub (cqOf .mixed).secondLo (cqOf .mixed).firstHi
  | .ellCLower => lsub (ladd (lmul csLo (cqOf .mixed).rLo) (lmul ccLo (cqOf .mixed).a))
      (lsmul (63/100) (cqOf .mixed).rHi)
  | .ellCUpper => lsub (lsub (lsmul (17/25) (cqOf .mixed).rLo) (lmul csHi (cqOf .mixed).rHi))
      (lmul ccHi (cqOf .mixed).b)
  | .cK => lsub (lmul (lsmul (51/50) (cqOf .lower).ULo)
      (ladd (lmul csLo (cqOf .lower).rLo) (lmul ccLo (cqOf .lower).a)))
      (lmul (lsub [2] (cqOf .lower).a) (cqOf .lower).rHi)

/-! The single kernel check of every reserve -/

private def gtB (r : ℚ) (D : ℕ) (L : List ℚ) : Bool := decide (r < lowerOnL D L)
private def ltB (r : ℚ) (D : ℕ) (L : List ℚ) : Bool := decide (upperOnL D L < r)

/-- The seeds are the integer square roots of the scaled constant terms. -/
private def seedsOK : Bool :=
  seedOK (argRLo uMinusL) 1744164484789 && (seedOK (argRLo uPlusL) 1742284706929 &&
  (seedOK (argRHi uMinusL) 1744202937734 && (seedOK (argRHi uPlusL) 1742323201360 &&
  (seedOK (argULo uMinusL) 1667366111566 && (seedOK (argULo uPlusL) 1669597556299 &&
  (seedOK (argUHi uMinusL) 1667406335600 && (seedOK (argUHi uPlusL) 1669637726574 &&
  (seedOK (argYLo (lsub rpULoM [epsilon])) 1462698414872 &&
  (seedOK (argYLo (lsub rpULoP [epsilon])) 1464728326930 &&
  (seedOK (argYHi (ladd rpUHiM [epsilon])) 1462781094395 &&
  (seedOK (argYHi (ladd rpUHiP [epsilon])) 1464810781472 &&
  (seedOK (argWLo (lsub rpYLoM [epsilon])) 1904391477390 &&
  (seedOK (argWLo (lsub rpYLoP [epsilon])) 1904963025613 &&
  (seedOK (argWHi (ladd rpYHiM [epsilon])) 1904450076243 &&
  (seedOK (argWHi (ladd rpYHiP [epsilon])) 1905021455367)))))))))))))))

/-- The three reserves of a root, from its centered argument and centered root polynomial,
with the lengths that bound the degrees. -/
private def rootOK (cA cp : List ℚ) : Bool :=
  gtB (2879/2000) 6 (lo cp) && (gtB (23/80000000) 12 (lsub cA (lpow (lo cp) 2)) &&
  (gtB (9/31250000) 12 (lsub (lpow (hi cp) 2) cA) && (decide ((lo cp).length ≤ 7) &&
  (decide ((lsub cA (lpow (lo cp) 2)).length ≤ 13) &&
  (decide ((lsub (lpow (hi cp) 2) cA).length ≤ 13))))))

private def chainOK (c : CQ) : Bool :=
  gtB (1/2) 6 c.rLo && (gtB (1/2) 6 c.ULo && (gtB (1/2) 6 c.VLo && (gtB (1/2) 6 c.YLo &&
  (gtB (1/2) 6 c.vLo && (gtB (1/2) 6 c.wLo && (ltB 2 6 c.rHi && (ltB 2 6 c.UHi &&
  (ltB 2 6 c.VHi && (ltB 2 6 c.YHi && (ltB 2 6 c.vHi && (ltB 2 6 c.wHi && (gtB 1 6 c.rLo &&
  (gtB 1 6 c.wLo && (gtB 1 22 c.firstLo && (gtB 1 22 c.secondLo &&
  (decide (c.rLo.length ≤ 7) && (decide (c.ULo.length ≤ 7) && (decide (c.VLo.length ≤ 7) &&
  (decide (c.YLo.length ≤ 7) && (decide (c.vLo.length ≤ 7) && (decide (c.wLo.length ≤ 7) &&
  (decide (c.rHi.length ≤ 7) && (decide (c.UHi.length ≤ 7) && (decide (c.VHi.length ≤ 7) &&
  (decide (c.YHi.length ≤ 7) && (decide (c.vHi.length ≤ 7) && (decide (c.wHi.length ≤ 7) &&
  (decide (c.firstLo.length ≤ 23) &&
  (decide (c.secondLo.length ≤ 23))))))))))))))))))))))))))))))

private def clearedOK (i : Coefficient) : Bool :=
  gtB 0 32 (clearedQ i) && decide ((clearedQ i).length ≤ 33)

private def allOK : Bool :=
  seedsOK && (rootOK (qsq qLower cuM) cRLoM && (rootOK (qsq qLower cuP) cRLoP &&
  (rootOK (qsq qUpper cuM) cRHiM && (rootOK (qsq qUpper cuP) cRHiP &&
  (rootOK (qsq qLower (lsub [2] cuM)) cULoM && (rootOK (qsq qLower (lsub [2] cuP)) cULoP &&
  (rootOK (qsq qUpper (lsub [2] cuM)) cUHiM && (rootOK (qsq qUpper (lsub [2] cuP)) cUHiP &&
  (rootOK (qsq qLower (lsub [3] (lo cULoM))) cYLoM &&
  (rootOK (qsq qLower (lsub [3] (lo cULoP))) cYLoP &&
  (rootOK (qsq qUpper (lsub [3] (hi cUHiM))) cYHiM &&
  (rootOK (qsq qUpper (lsub [3] (hi cUHiP))) cYHiP &&
  (rootOK (qsq qLower (lsub [2] (lo cYLoM))) cWLoM &&
  (rootOK (qsq qLower (lsub [2] (lo cYLoP))) cWLoP &&
  (rootOK (qsq qUpper (lsub [2] (hi cYHiM))) cWHiM &&
  (rootOK (qsq qUpper (lsub [2] (hi cYHiP))) cWHiP && (chainOK (cqOf .lower) &&
  (chainOK (cqOf .upper) && (chainOK (cqOf .mixed) &&
  (ltB (-(1/50)) 64 (cqOf .lower).posUpper && (gtB (1/25) 64 (cqOf .upper).posLower &&
  (decide ((cqOf .lower).posUpper.length ≤ 65) &&
  (decide ((cqOf .upper).posLower.length ≤ 65) && (clearedOK .etaLower &&
  (clearedOK .etaUpper && (clearedOK .kLower && (clearedOK .kUpper && (clearedOK .ellUpper &&
  (clearedOK .ellK && (clearedOK .cLower && (clearedOK .cUpper && (clearedOK .ellCLower &&
  (clearedOK .ellCUpper && (clearedOK .cK))))))))))))))))))))))))))))))))))

private theorem allOK_true : allOK=true := by decide +kernel

/-! The polynomials of this file as lists -/

private theorem and_true_left {a b : Bool} (h : (a && b)=true) : a=true := by
  simp only [Bool.and_eq_true] at h; exact h.1
private theorem parameter_eq : parameter=toPoly paramL := by
  simp [parameter,paramL]

private theorem uMinus_eq : uMinus=toPoly uMinusL := by
  simp only [uMinus,uMinusL,toPoly_sub,toPoly_smul,toPoly_single,← parameter_eq]

private theorem uPlus_eq : uPlus=toPoly uPlusL := by
  simp only [uPlus,uPlusL,toPoly_sub,toPoly_smul,toPoly_single,← parameter_eq]

private def aL : Chain → List ℚ | .lower | .mixed => uMinusL | .upper => uPlusL
private def bL : Chain → List ℚ | .upper | .mixed => uPlusL | .lower => uMinusL

private theorem a_eq (s : Chain) : a s=toPoly (aL s) := by
  cases s <;> simp only [a,aL,uMinus_eq,uPlus_eq]

private theorem b_eq (s : Chain) : b s=toPoly (bL s) := by
  cases s <;> simp only [b,bL,uMinus_eq,uPlus_eq]

private theorem two_eq : (2:ℚ[X])=toPoly [2] := by rw [toPoly_single,C_ofNat]
private theorem three_eq : (3:ℚ[X])=toPoly [3] := by rw [toPoly_single,C_ofNat]
private theorem one_eq : (1:ℚ[X])=toPoly [1] := by rw [toPoly_single,C_1]

private theorem comp_aff (L : List ℚ) : (toPoly L).comp (toPoly affL)=toPoly (cen L) := by
  rw [cen,toPoly_comp]

private theorem lo_eq (L : List ℚ) : toPoly (lo L)=toPoly L-C epsilon := by
  rw [lo,toPoly_sub,toPoly_single]
private theorem hi_eq (L : List ℚ) : toPoly (hi L)=toPoly L+C epsilon := by
  rw [hi,toPoly_add,toPoly_single]

private theorem comp_lo (L : List ℚ) : (toPoly (lo L)).comp (toPoly affL)=toPoly (lo (cen L)) := by
  rw [lo_eq,lo_eq,sub_comp,C_comp,comp_aff]
private theorem comp_hi (L : List ℚ) : (toPoly (hi L)).comp (toPoly affL)=toPoly (hi (cen L)) := by
  rw [hi_eq,hi_eq,add_comp,C_comp,comp_aff]

/-- The two root polynomials of an argument, from its list and its seed. -/
private theorem root_lo {Ap : ℚ[X]} {A : List ℚ} {n : ℕ} (hA : Ap=toPoly A) (h : seedOK A n=true) :
    rootLower Ap=toPoly (lo (rootPolyL A n)) := by
  rw [hA,rootLower_toPoly h]; rfl
private theorem root_hi {Ap : ℚ[X]} {A : List ℚ} {n : ℕ} (hA : Ap=toPoly A) (h : seedOK A n=true) :
    rootUpper Ap=toPoly (hi (rootPolyL A n)) := by
  rw [hA,rootUpper_toPoly h]; rfl

private theorem seeds_true : seedsOK=true := and_true_left allOK_true

private theorem s_RLoM : seedOK (argRLo uMinusL) 1744164484789=true := by
  have h := seeds_true; simp only [seedsOK,Bool.and_eq_true] at h; exact h.1
private theorem s_RLoP : seedOK (argRLo uPlusL) 1742284706929=true := by
  have h := seeds_true; simp only [seedsOK,Bool.and_eq_true] at h; exact h.2.1
private theorem s_RHiM : seedOK (argRHi uMinusL) 1744202937734=true := by
  have h := seeds_true; simp only [seedsOK,Bool.and_eq_true] at h; exact h.2.2.1
private theorem s_RHiP : seedOK (argRHi uPlusL) 1742323201360=true := by
  have h := seeds_true; simp only [seedsOK,Bool.and_eq_true] at h; exact h.2.2.2.1
private theorem s_ULoM : seedOK (argULo uMinusL) 1667366111566=true := by
  have h := seeds_true; simp only [seedsOK,Bool.and_eq_true] at h; exact h.2.2.2.2.1
private theorem s_ULoP : seedOK (argULo uPlusL) 1669597556299=true := by
  have h := seeds_true; simp only [seedsOK,Bool.and_eq_true] at h; exact h.2.2.2.2.2.1
private theorem s_UHiM : seedOK (argUHi uMinusL) 1667406335600=true := by
  have h := seeds_true; simp only [seedsOK,Bool.and_eq_true] at h; exact h.2.2.2.2.2.2.1
private theorem s_UHiP : seedOK (argUHi uPlusL) 1669637726574=true := by
  have h := seeds_true; simp only [seedsOK,Bool.and_eq_true] at h; exact h.2.2.2.2.2.2.2.1
private theorem s_YLoM : seedOK (argYLo (lsub rpULoM [epsilon])) 1462698414872=true := by
  have h := seeds_true; simp only [seedsOK,Bool.and_eq_true] at h; exact h.2.2.2.2.2.2.2.2.1
private theorem s_YLoP : seedOK (argYLo (lsub rpULoP [epsilon])) 1464728326930=true := by
  have h := seeds_true; simp only [seedsOK,Bool.and_eq_true] at h; exact h.2.2.2.2.2.2.2.2.2.1
private theorem s_YHiM : seedOK (argYHi (ladd rpUHiM [epsilon])) 1462781094395=true := by
  have h := seeds_true; simp only [seedsOK,Bool.and_eq_true] at h; exact h.2.2.2.2.2.2.2.2.2.2.1
private theorem s_YHiP : seedOK (argYHi (ladd rpUHiP [epsilon])) 1464810781472=true := by
  have h := seeds_true; simp only [seedsOK,Bool.and_eq_true] at h
  exact h.2.2.2.2.2.2.2.2.2.2.2.1
private theorem s_WLoM : seedOK (argWLo (lsub rpYLoM [epsilon])) 1904391477390=true := by
  have h := seeds_true; simp only [seedsOK,Bool.and_eq_true] at h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem s_WLoP : seedOK (argWLo (lsub rpYLoP [epsilon])) 1904963025613=true := by
  have h := seeds_true; simp only [seedsOK,Bool.and_eq_true] at h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem s_WHiM : seedOK (argWHi (ladd rpYHiM [epsilon])) 1904450076243=true := by
  have h := seeds_true; simp only [seedsOK,Bool.and_eq_true] at h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem s_WHiP : seedOK (argWHi (ladd rpYHiP [epsilon])) 1905021455367=true := by
  have h := seeds_true; simp only [seedsOK,Bool.and_eq_true] at h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! Arguments and roots, chain by chain -/

private theorem rArgLo_eq (s : Chain) : rArgLo s=toPoly (argRLo (bL s)) := by
  simp only [rArgLo,argRLo,toPoly_sub,toPoly_pow,toPoly_single,b_eq]
private theorem rArgHi_eq (s : Chain) : rArgHi s=toPoly (argRHi (aL s)) := by
  simp only [rArgHi,argRHi,toPoly_sub,toPoly_pow,toPoly_single,a_eq]
private theorem UArgLo_eq (s : Chain) : UArgLo s=toPoly (argULo (aL s)) := by
  simp only [UArgLo,argULo,toPoly_sub,toPoly_pow,toPoly_single,a_eq,two_eq]
private theorem UArgHi_eq (s : Chain) : UArgHi s=toPoly (argUHi (bL s)) := by
  simp only [UArgHi,argUHi,toPoly_sub,toPoly_pow,toPoly_single,b_eq,two_eq]

private def rpRLo : Chain → List ℚ | .lower => rpRLoM | .upper | .mixed => rpRLoP
private def rpRHi : Chain → List ℚ | .lower | .mixed => rpRHiM | .upper => rpRHiP
private def rpULo : Chain → List ℚ | .lower | .mixed => rpULoM | .upper => rpULoP
private def rpUHi : Chain → List ℚ | .lower => rpUHiM | .upper | .mixed => rpUHiP
private def rpYLo : Chain → List ℚ | .lower | .mixed => rpYLoM | .upper => rpYLoP
private def rpYHi : Chain → List ℚ | .lower => rpYHiM | .upper | .mixed => rpYHiP
private def rpWLo : Chain → List ℚ | .lower | .mixed => rpWLoM | .upper => rpWLoP
private def rpWHi : Chain → List ℚ | .lower => rpWHiM | .upper | .mixed => rpWHiP

private theorem RLo_lo (s : Chain) : rootLower (rArgLo s)=toPoly (lo (rpRLo s)) := by
  cases s
  · exact root_lo (rArgLo_eq _) s_RLoM
  · exact root_lo (rArgLo_eq _) s_RLoP
  · exact root_lo (rArgLo_eq _) s_RLoP
private theorem RLo_hi (s : Chain) : rootUpper (rArgLo s)=toPoly (hi (rpRLo s)) := by
  cases s
  · exact root_hi (rArgLo_eq _) s_RLoM
  · exact root_hi (rArgLo_eq _) s_RLoP
  · exact root_hi (rArgLo_eq _) s_RLoP
private theorem RHi_lo (s : Chain) : rootLower (rArgHi s)=toPoly (lo (rpRHi s)) := by
  cases s
  · exact root_lo (rArgHi_eq _) s_RHiM
  · exact root_lo (rArgHi_eq _) s_RHiP
  · exact root_lo (rArgHi_eq _) s_RHiM
private theorem RHi_hi (s : Chain) : rootUpper (rArgHi s)=toPoly (hi (rpRHi s)) := by
  cases s
  · exact root_hi (rArgHi_eq _) s_RHiM
  · exact root_hi (rArgHi_eq _) s_RHiP
  · exact root_hi (rArgHi_eq _) s_RHiM
private theorem ULo_lo (s : Chain) : rootLower (UArgLo s)=toPoly (lo (rpULo s)) := by
  cases s
  · exact root_lo (UArgLo_eq _) s_ULoM
  · exact root_lo (UArgLo_eq _) s_ULoP
  · exact root_lo (UArgLo_eq _) s_ULoM
private theorem ULo_hi (s : Chain) : rootUpper (UArgLo s)=toPoly (hi (rpULo s)) := by
  cases s
  · exact root_hi (UArgLo_eq _) s_ULoM
  · exact root_hi (UArgLo_eq _) s_ULoP
  · exact root_hi (UArgLo_eq _) s_ULoM
private theorem UHi_lo (s : Chain) : rootLower (UArgHi s)=toPoly (lo (rpUHi s)) := by
  cases s
  · exact root_lo (UArgHi_eq _) s_UHiM
  · exact root_lo (UArgHi_eq _) s_UHiP
  · exact root_lo (UArgHi_eq _) s_UHiP
private theorem UHi_hi (s : Chain) : rootUpper (UArgHi s)=toPoly (hi (rpUHi s)) := by
  cases s
  · exact root_hi (UArgHi_eq _) s_UHiM
  · exact root_hi (UArgHi_eq _) s_UHiP
  · exact root_hi (UArgHi_eq _) s_UHiP

private theorem ULo_eq (s : Chain) : ULo s=toPoly (lo (rpULo s)) := ULo_lo s
private theorem UHi_eq (s : Chain) : UHi s=toPoly (hi (rpUHi s)) := UHi_hi s

private theorem YArgLo_eq (s : Chain) : YArgLo s=toPoly (argYLo (lo (rpULo s))) := by
  simp only [YArgLo,VHi,argYLo,toPoly_sub,toPoly_pow,toPoly_single,ULo_eq,three_eq]
private theorem YArgHi_eq (s : Chain) : YArgHi s=toPoly (argYHi (hi (rpUHi s))) := by
  simp only [YArgHi,VLo,argYHi,toPoly_sub,toPoly_pow,toPoly_single,UHi_eq,three_eq]

private theorem YLo_lo (s : Chain) : rootLower (YArgLo s)=toPoly (lo (rpYLo s)) := by
  cases s
  · exact root_lo (YArgLo_eq _) s_YLoM
  · exact root_lo (YArgLo_eq _) s_YLoP
  · exact root_lo (YArgLo_eq _) s_YLoM
private theorem YLo_hi (s : Chain) : rootUpper (YArgLo s)=toPoly (hi (rpYLo s)) := by
  cases s
  · exact root_hi (YArgLo_eq _) s_YLoM
  · exact root_hi (YArgLo_eq _) s_YLoP
  · exact root_hi (YArgLo_eq _) s_YLoM
private theorem YHi_lo (s : Chain) : rootLower (YArgHi s)=toPoly (lo (rpYHi s)) := by
  cases s
  · exact root_lo (YArgHi_eq _) s_YHiM
  · exact root_lo (YArgHi_eq _) s_YHiP
  · exact root_lo (YArgHi_eq _) s_YHiP
private theorem YHi_hi (s : Chain) : rootUpper (YArgHi s)=toPoly (hi (rpYHi s)) := by
  cases s
  · exact root_hi (YArgHi_eq _) s_YHiM
  · exact root_hi (YArgHi_eq _) s_YHiP
  · exact root_hi (YArgHi_eq _) s_YHiP

private theorem YLo_eq (s : Chain) : YLo s=toPoly (lo (rpYLo s)) := YLo_lo s
private theorem YHi_eq (s : Chain) : YHi s=toPoly (hi (rpYHi s)) := YHi_hi s

private theorem wArgLo_eq (s : Chain) : wArgLo s=toPoly (argWLo (lo (rpYLo s))) := by
  simp only [wArgLo,vHi,argWLo,toPoly_sub,toPoly_pow,toPoly_single,YLo_eq,two_eq]
private theorem wArgHi_eq (s : Chain) : wArgHi s=toPoly (argWHi (hi (rpYHi s))) := by
  simp only [wArgHi,vLo,argWHi,toPoly_sub,toPoly_pow,toPoly_single,YHi_eq,two_eq]

private theorem WLo_lo (s : Chain) : rootLower (wArgLo s)=toPoly (lo (rpWLo s)) := by
  cases s
  · exact root_lo (wArgLo_eq _) s_WLoM
  · exact root_lo (wArgLo_eq _) s_WLoP
  · exact root_lo (wArgLo_eq _) s_WLoM
private theorem WLo_hi (s : Chain) : rootUpper (wArgLo s)=toPoly (hi (rpWLo s)) := by
  cases s
  · exact root_hi (wArgLo_eq _) s_WLoM
  · exact root_hi (wArgLo_eq _) s_WLoP
  · exact root_hi (wArgLo_eq _) s_WLoM
private theorem WHi_lo (s : Chain) : rootLower (wArgHi s)=toPoly (lo (rpWHi s)) := by
  cases s
  · exact root_lo (wArgHi_eq _) s_WHiM
  · exact root_lo (wArgHi_eq _) s_WHiP
  · exact root_lo (wArgHi_eq _) s_WHiP
private theorem WHi_hi (s : Chain) : rootUpper (wArgHi s)=toPoly (hi (rpWHi s)) := by
  cases s
  · exact root_hi (wArgHi_eq _) s_WHiM
  · exact root_hi (wArgHi_eq _) s_WHiP
  · exact root_hi (wArgHi_eq _) s_WHiP

/-! Centered polynomials as lists -/

private theorem aff_lo {p : ℚ[X]} {L : List ℚ} (h : p=toPoly (lo L)) :
    p.comp (toPoly affL)=toPoly (lo (cen L)) := by rw [h,comp_lo]
private theorem aff_hi {p : ℚ[X]} {L : List ℚ} (h : p=toPoly (hi L)) :
    p.comp (toPoly affL)=toPoly (hi (cen L)) := by rw [h,comp_hi]

private theorem a_comp (s : Chain) : (a s).comp (toPoly affL)=toPoly (cqOf s).a := by
  rw [a_eq,comp_aff]; cases s <;> rfl
private theorem b_comp (s : Chain) : (b s).comp (toPoly affL)=toPoly (cqOf s).b := by
  rw [b_eq,comp_aff]; cases s <;> rfl
private theorem rLo_comp (s : Chain) : (rLo s).comp (toPoly affL)=toPoly (cqOf s).rLo := by
  exact (aff_lo (RLo_lo s)).trans (by cases s <;> rfl)
private theorem rHi_comp (s : Chain) : (rHi s).comp (toPoly affL)=toPoly (cqOf s).rHi := by
  exact (aff_hi (RHi_hi s)).trans (by cases s <;> rfl)
private theorem ULo_comp (s : Chain) : (ULo s).comp (toPoly affL)=toPoly (cqOf s).ULo := by
  exact (aff_lo (ULo_lo s)).trans (by cases s <;> rfl)
private theorem UHi_comp (s : Chain) : (UHi s).comp (toPoly affL)=toPoly (cqOf s).UHi := by
  exact (aff_hi (UHi_hi s)).trans (by cases s <;> rfl)
private theorem YLo_comp (s : Chain) : (YLo s).comp (toPoly affL)=toPoly (cqOf s).YLo := by
  exact (aff_lo (YLo_lo s)).trans (by cases s <;> rfl)
private theorem YHi_comp (s : Chain) : (YHi s).comp (toPoly affL)=toPoly (cqOf s).YHi := by
  exact (aff_hi (YHi_hi s)).trans (by cases s <;> rfl)
private theorem wLo_comp (s : Chain) : (wLo s).comp (toPoly affL)=toPoly (cqOf s).wLo := by
  exact (aff_lo (WLo_lo s)).trans (by cases s <;> rfl)
private theorem wHi_comp (s : Chain) : (wHi s).comp (toPoly affL)=toPoly (cqOf s).wHi := by
  exact (aff_hi (WHi_hi s)).trans (by cases s <;> rfl)

private theorem const_comp (c : ℚ) : (toPoly [c]).comp (toPoly affL)=toPoly [c] := by
  rw [toPoly_single,C_comp]

private theorem VLo_comp (s : Chain) : (VLo s).comp (toPoly affL)=toPoly (cqOf s).VLo := by
  rw [VLo,three_eq,sub_comp,const_comp,UHi_comp,CQ.VLo,toPoly_sub]
private theorem VHi_comp (s : Chain) : (VHi s).comp (toPoly affL)=toPoly (cqOf s).VHi := by
  rw [VHi,three_eq,sub_comp,const_comp,ULo_comp,CQ.VHi,toPoly_sub]
private theorem vLo_comp (s : Chain) : (vLo s).comp (toPoly affL)=toPoly (cqOf s).vLo := by
  rw [vLo,two_eq,sub_comp,const_comp,YHi_comp,CQ.vLo,toPoly_sub]
private theorem vHi_comp (s : Chain) : (vHi s).comp (toPoly affL)=toPoly (cqOf s).vHi := by
  rw [vHi,two_eq,sub_comp,const_comp,YLo_comp,CQ.vHi,toPoly_sub]

private theorem sine_eq : PositiveScalarPolynomials.sine=toPoly sineL := by
  simp only [PositiveScalarPolynomials.sine,sineL,toPoly_add,toPoly_sub,toPoly_monoC,C_1,
    one_mul,pow_one]
private theorem cosine_eq : PositiveScalarPolynomials.cosine=toPoly cosineL := by
  simp only [PositiveScalarPolynomials.cosine,cosineL,toPoly_add,toPoly_sub,toPoly_monoC,
    toPoly_single,C_1]

private theorem param_comp (p : ℚ[X]) (L : List ℚ) (h : p=toPoly L) :
    (p.comp parameter).comp (toPoly affL)=toPoly (lcomp L cparL) := by
  rw [comp_assoc,h,parameter_eq,comp_aff,cparL,toPoly_comp]

private theorem sineLo_comp : sineLo.comp (toPoly affL)=toPoly csLo :=
  param_comp _ _ sine_eq
private theorem sineHi_comp : sineHi.comp (toPoly affL)=toPoly csHi :=
  param_comp _ _ (by rw [toPoly_add,toPoly_monoC,sine_eq])
private theorem cosineLo_comp : cosineLo.comp (toPoly affL)=toPoly ccLo :=
  param_comp _ _ (by rw [toPoly_sub,toPoly_monoC,cosine_eq])
private theorem cosineHi_comp : cosineHi.comp (toPoly affL)=toPoly ccHi :=
  param_comp _ _ cosine_eq

private theorem firstLo_comp (s : Chain) :
    (firstLo s).comp (toPoly affL)=toPoly (cqOf s).firstLo := by
  rw [firstLo,two_eq,one_eq]
  simp only [add_comp,sub_comp,mul_comp,const_comp,rHi_comp,a_comp,cosineHi_comp,sineLo_comp,
    CQ.firstLo,toPoly_add,toPoly_sub,toPoly_mul]
private theorem firstHi_comp (s : Chain) :
    (firstHi s).comp (toPoly affL)=toPoly (cqOf s).firstHi := by
  rw [firstHi,two_eq,one_eq]
  simp only [add_comp,sub_comp,mul_comp,const_comp,rLo_comp,b_comp,cosineLo_comp,sineHi_comp,
    CQ.firstHi,toPoly_add,toPoly_sub,toPoly_mul]
private theorem secondLo_comp (s : Chain) :
    (secondLo s).comp (toPoly affL)=toPoly (cqOf s).secondLo := by
  rw [secondLo,one_eq]
  simp only [add_comp,sub_comp,mul_comp,const_comp,vLo_comp,wHi_comp,cosineLo_comp,sineHi_comp,
    CQ.secondLo,toPoly_add,toPoly_sub,toPoly_mul]
private theorem secondHi_comp (s : Chain) :
    (secondHi s).comp (toPoly affL)=toPoly (cqOf s).secondHi := by
  rw [secondHi,one_eq]
  simp only [add_comp,sub_comp,mul_comp,const_comp,vHi_comp,wLo_comp,cosineHi_comp,sineLo_comp,
    CQ.secondHi,toPoly_add,toPoly_sub,toPoly_mul]

private theorem posUpper_comp (s : Chain) :
    (positionUpperAt s).comp (toPoly affL)=toPoly (cqOf s).posUpper := by
  rw [positionUpperAt,two_eq]
  simp only [add_comp,sub_comp,mul_comp,const_comp,firstHi_comp,secondLo_comp,b_comp,rHi_comp,
    rLo_comp,UHi_comp,YHi_comp,wHi_comp,wLo_comp,VLo_comp,vLo_comp,cosineHi_comp,cosineLo_comp,
    sineHi_comp,sineLo_comp,CQ.posUpper,toPoly_add,toPoly_sub,toPoly_mul]
private theorem posLower_comp (s : Chain) :
    (positionLowerAt s).comp (toPoly affL)=toPoly (cqOf s).posLower := by
  rw [positionLowerAt,two_eq]
  simp only [add_comp,sub_comp,mul_comp,const_comp,firstLo_comp,secondHi_comp,a_comp,rHi_comp,
    rLo_comp,ULo_comp,YLo_comp,wLo_comp,wHi_comp,VHi_comp,vHi_comp,cosineHi_comp,cosineLo_comp,
    sineHi_comp,sineLo_comp,CQ.posLower,toPoly_add,toPoly_sub,toPoly_mul]

private theorem cleared_comp (i : Coefficient) :
    (cleared i).comp (toPoly affL)=toPoly (clearedQ i) := by
  cases i <;> simp only [cleared,clearedQ,two_eq,add_comp,sub_comp,mul_comp,C_comp,const_comp,
    firstLo_comp,firstHi_comp,secondLo_comp,secondHi_comp,a_comp,b_comp,rLo_comp,rHi_comp,
    ULo_comp,YLo_comp,YHi_comp,wLo_comp,wHi_comp,VLo_comp,VHi_comp,vLo_comp,vHi_comp,
    cosineHi_comp,cosineLo_comp,sineHi_comp,sineLo_comp,toPoly_add,toPoly_sub,toPoly_mul,
    toPoly_smul]

/-! Facts for the theorems -/

private theorem gt_spec {r : ℚ} {D : ℕ} {L : List ℚ} (h : gtB r D L=true) : r < lowerOnL D L :=
  of_decide_eq_true h
private theorem lt_spec {r : ℚ} {D : ℕ} {L : List ℚ} (h : ltB r D L=true) : upperOnL D L < r :=
  of_decide_eq_true h

private theorem allOK_parts :
    seedsOK=true ∧
    rootOK (qsq qLower cuM) cRLoM=true ∧ rootOK (qsq qLower cuP) cRLoP=true ∧
    rootOK (qsq qUpper cuM) cRHiM=true ∧ rootOK (qsq qUpper cuP) cRHiP=true ∧
    rootOK (qsq qLower (lsub [2] cuM)) cULoM=true ∧ rootOK (qsq qLower (lsub [2] cuP)) cULoP=true ∧
    rootOK (qsq qUpper (lsub [2] cuM)) cUHiM=true ∧ rootOK (qsq qUpper (lsub [2] cuP)) cUHiP=true ∧
    rootOK (qsq qLower (lsub [3] (lo cULoM))) cYLoM=true ∧
    rootOK (qsq qLower (lsub [3] (lo cULoP))) cYLoP=true ∧
    rootOK (qsq qUpper (lsub [3] (hi cUHiM))) cYHiM=true ∧
    rootOK (qsq qUpper (lsub [3] (hi cUHiP))) cYHiP=true ∧
    rootOK (qsq qLower (lsub [2] (lo cYLoM))) cWLoM=true ∧
    rootOK (qsq qLower (lsub [2] (lo cYLoP))) cWLoP=true ∧
    rootOK (qsq qUpper (lsub [2] (hi cYHiM))) cWHiM=true ∧
    rootOK (qsq qUpper (lsub [2] (hi cYHiP))) cWHiP=true ∧
    chainOK (cqOf .lower)=true ∧ chainOK (cqOf .upper)=true ∧ chainOK (cqOf .mixed)=true ∧
    ltB (-(1/50)) 64 (cqOf .lower).posUpper=true ∧ gtB (1/25) 64 (cqOf .upper).posLower=true ∧
    (cqOf .lower).posUpper.length ≤ 65 ∧ (cqOf .upper).posLower.length ≤ 65 ∧
    clearedOK .etaLower=true ∧ clearedOK .etaUpper=true ∧ clearedOK .kLower=true ∧
    clearedOK .kUpper=true ∧ clearedOK .ellUpper=true ∧ clearedOK .ellK=true ∧
    clearedOK .cLower=true ∧ clearedOK .cUpper=true ∧ clearedOK .ellCLower=true ∧
    clearedOK .ellCUpper=true ∧ clearedOK .cK=true := by
  have h := allOK_true
  simp only [allOK,Bool.and_eq_true,decide_eq_true_eq] at h
  exact h

private theorem chainOK_parts (s : Chain) :
    gtB (1/2) 6 (cqOf s).rLo=true ∧ gtB (1/2) 6 (cqOf s).ULo=true ∧
    gtB (1/2) 6 (cqOf s).VLo=true ∧ gtB (1/2) 6 (cqOf s).YLo=true ∧
    gtB (1/2) 6 (cqOf s).vLo=true ∧ gtB (1/2) 6 (cqOf s).wLo=true ∧
    ltB 2 6 (cqOf s).rHi=true ∧ ltB 2 6 (cqOf s).UHi=true ∧ ltB 2 6 (cqOf s).VHi=true ∧
    ltB 2 6 (cqOf s).YHi=true ∧ ltB 2 6 (cqOf s).vHi=true ∧ ltB 2 6 (cqOf s).wHi=true ∧
    gtB 1 6 (cqOf s).rLo=true ∧ gtB 1 6 (cqOf s).wLo=true ∧ gtB 1 22 (cqOf s).firstLo=true ∧
    gtB 1 22 (cqOf s).secondLo=true ∧
    (cqOf s).rLo.length ≤ 7 ∧ (cqOf s).ULo.length ≤ 7 ∧ (cqOf s).VLo.length ≤ 7 ∧
    (cqOf s).YLo.length ≤ 7 ∧ (cqOf s).vLo.length ≤ 7 ∧ (cqOf s).wLo.length ≤ 7 ∧
    (cqOf s).rHi.length ≤ 7 ∧ (cqOf s).UHi.length ≤ 7 ∧ (cqOf s).VHi.length ≤ 7 ∧
    (cqOf s).YHi.length ≤ 7 ∧ (cqOf s).vHi.length ≤ 7 ∧ (cqOf s).wHi.length ≤ 7 ∧
    (cqOf s).firstLo.length ≤ 23 ∧ (cqOf s).secondLo.length ≤ 23 := by
  have h : chainOK (cqOf s)=true := by
    obtain ⟨-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,hl,hu,hm,-⟩ := allOK_parts
    cases s
    · exact hl
    · exact hu
    · exact hm
  simp only [chainOK,Bool.and_eq_true,decide_eq_true_eq] at h
  exact h

private theorem qsq_comp {p : ℚ[X]} {L : List ℚ} (q : ℚ) (h : p.comp (toPoly affL)=toPoly L) :
    (C q-p^2).comp (toPoly affL)=toPoly (qsq q L) := by
  rw [sub_comp,pow_comp,C_comp,h,qsq,toPoly_sub,toPoly_pow,toPoly_single]

private theorem csub_comp {p : ℚ[X]} {L : List ℚ} (c : ℚ) (h : p.comp (toPoly affL)=toPoly L) :
    (toPoly [c]-p).comp (toPoly affL)=toPoly (lsub [c] L) := by
  rw [sub_comp,const_comp,h,toPoly_sub]

private theorem rArgLo_comp (s : Chain) :
    (rArgLo s).comp (toPoly affL)=toPoly (qsq qLower (cen (bL s))) :=
  qsq_comp _ (by rw [b_eq,comp_aff])
private theorem rArgHi_comp (s : Chain) :
    (rArgHi s).comp (toPoly affL)=toPoly (qsq qUpper (cen (aL s))) :=
  qsq_comp _ (by rw [a_eq,comp_aff])
private theorem UArgLo_comp (s : Chain) :
    (UArgLo s).comp (toPoly affL)=toPoly (qsq qLower (lsub [2] (cen (aL s)))) :=
  qsq_comp _ (by rw [two_eq,a_eq]; exact csub_comp 2 (comp_aff _))
private theorem UArgHi_comp (s : Chain) :
    (UArgHi s).comp (toPoly affL)=toPoly (qsq qUpper (lsub [2] (cen (bL s)))) :=
  qsq_comp _ (by rw [two_eq,b_eq]; exact csub_comp 2 (comp_aff _))
private theorem YArgLo_comp (s : Chain) :
    (YArgLo s).comp (toPoly affL)=toPoly (qsq qLower (lsub [3] (lo (cen (rpULo s))))) :=
  qsq_comp _ (by rw [VHi,three_eq,ULo_eq]; exact csub_comp 3 (comp_lo _))
private theorem YArgHi_comp (s : Chain) :
    (YArgHi s).comp (toPoly affL)=toPoly (qsq qUpper (lsub [3] (hi (cen (rpUHi s))))) :=
  qsq_comp _ (by rw [VLo,three_eq,UHi_eq]; exact csub_comp 3 (comp_hi _))
private theorem wArgLo_comp (s : Chain) :
    (wArgLo s).comp (toPoly affL)=toPoly (qsq qLower (lsub [2] (lo (cen (rpYLo s))))) :=
  qsq_comp _ (by rw [vHi,two_eq,YLo_eq]; exact csub_comp 2 (comp_lo _))
private theorem wArgHi_comp (s : Chain) :
    (wArgHi s).comp (toPoly affL)=toPoly (qsq qUpper (lsub [2] (hi (cen (rpYHi s))))) :=
  qsq_comp _ (by rw [vLo,two_eq,YHi_eq]; exact csub_comp 2 (comp_hi _))

private theorem pack {Ap : ℚ[X]} {cA rp : List ℚ}
    (hA : Ap.comp (toPoly affL)=toPoly cA) (hl : rootLower Ap=toPoly (lo rp))
    (hh : rootUpper Ap=toPoly (hi rp)) (hok : rootOK cA (cen rp)=true) : ∃ cA cp : List ℚ,
    Ap.comp (toPoly affL)=toPoly cA ∧ (rootLower Ap).comp (toPoly affL)=toPoly (lo cp) ∧
    (rootUpper Ap).comp (toPoly affL)=toPoly (hi cp) ∧
    rootOK cA cp=true ∧ (lo cp).length ≤ 7 ∧ (lsub cA (lpow (lo cp) 2)).length ≤ 13 ∧
      (lsub (lpow (hi cp) 2) cA).length ≤ 13 := by
  have hk := hok
  simp only [rootOK,Bool.and_eq_true,decide_eq_true_eq] at hk
  exact ⟨cA,cen rp,hA,aff_lo hl,aff_hi hh,hok,hk.2.2.2.1,hk.2.2.2.2.1,hk.2.2.2.2.2⟩

/-- Everything about one root argument, packaged per chain and index. -/
private theorem root_facts (s : Chain) (i : Fin 8) : ∃ cA cp : List ℚ,
    (rootArgument s i).comp (toPoly affL)=toPoly cA ∧
    (rootLower (rootArgument s i)).comp (toPoly affL)=toPoly (lo cp) ∧
    (rootUpper (rootArgument s i)).comp (toPoly affL)=toPoly (hi cp) ∧
    rootOK cA cp=true ∧ (lo cp).length ≤ 7 ∧ (lsub cA (lpow (lo cp) 2)).length ≤ 13 ∧
      (lsub (lpow (hi cp) 2) cA).length ≤ 13 := by
  obtain ⟨-,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,-⟩ := allOK_parts
  fin_cases i
  · cases s
    · exact pack (rArgLo_comp _) (RLo_lo _) (RLo_hi _) h1
    · exact pack (rArgLo_comp _) (RLo_lo _) (RLo_hi _) h2
    · exact pack (rArgLo_comp _) (RLo_lo _) (RLo_hi _) h2
  · cases s
    · exact pack (rArgHi_comp _) (RHi_lo _) (RHi_hi _) h3
    · exact pack (rArgHi_comp _) (RHi_lo _) (RHi_hi _) h4
    · exact pack (rArgHi_comp _) (RHi_lo _) (RHi_hi _) h3
  · cases s
    · exact pack (UArgLo_comp _) (ULo_lo _) (ULo_hi _) h5
    · exact pack (UArgLo_comp _) (ULo_lo _) (ULo_hi _) h6
    · exact pack (UArgLo_comp _) (ULo_lo _) (ULo_hi _) h5
  · cases s
    · exact pack (UArgHi_comp _) (UHi_lo _) (UHi_hi _) h7
    · exact pack (UArgHi_comp _) (UHi_lo _) (UHi_hi _) h8
    · exact pack (UArgHi_comp _) (UHi_lo _) (UHi_hi _) h8
  · cases s
    · exact pack (YArgLo_comp _) (YLo_lo _) (YLo_hi _) h9
    · exact pack (YArgLo_comp _) (YLo_lo _) (YLo_hi _) h10
    · exact pack (YArgLo_comp _) (YLo_lo _) (YLo_hi _) h9
  · cases s
    · exact pack (YArgHi_comp _) (YHi_lo _) (YHi_hi _) h11
    · exact pack (YArgHi_comp _) (YHi_lo _) (YHi_hi _) h12
    · exact pack (YArgHi_comp _) (YHi_lo _) (YHi_hi _) h12
  · cases s
    · exact pack (wArgLo_comp _) (WLo_lo _) (WLo_hi _) h13
    · exact pack (wArgLo_comp _) (WLo_lo _) (WLo_hi _) h14
    · exact pack (wArgLo_comp _) (WLo_lo _) (WLo_hi _) h13
  · cases s
    · exact pack (wArgHi_comp _) (WHi_lo _) (WHi_hi _) h15
    · exact pack (wArgHi_comp _) (WHi_lo _) (WHi_hi _) h16
    · exact pack (wArgHi_comp _) (WHi_lo _) (WHi_hi _) h16

private theorem coord_facts (s : Chain) (i : Fin 6) : ∃ Llo Lhi : List ℚ,
    (coordinateLower s i).comp (toPoly affL)=toPoly Llo ∧
    (coordinateUpper s i).comp (toPoly affL)=toPoly Lhi ∧ Llo.length ≤ 7 ∧ Lhi.length ≤ 7 ∧
    gtB (1/2) 6 Llo=true ∧ ltB 2 6 Lhi=true := by
  obtain ⟨o1,o2,o3,o4,o5,o6,u1,u2,u3,u4,u5,u6,-,-,-,-,l1,l2,l3,l4,l5,l6,k1,k2,k3,k4,k5,k6,-⟩ :=
    chainOK_parts s
  fin_cases i
  · exact ⟨_,_,rLo_comp s,rHi_comp s,l1,k1,o1,u1⟩
  · exact ⟨_,_,ULo_comp s,UHi_comp s,l2,k2,o2,u2⟩
  · exact ⟨_,_,VLo_comp s,VHi_comp s,l3,k3,o3,u3⟩
  · exact ⟨_,_,YLo_comp s,YHi_comp s,l4,k4,o4,u4⟩
  · exact ⟨_,_,vLo_comp s,vHi_comp s,l5,k5,o5,u5⟩
  · exact ⟨_,_,wLo_comp s,wHi_comp s,l6,k6,o6,u6⟩

theorem root_identities (s : Chain) (i : Fin 8) :
    centered 0 length (rootLower (rootArgument s i))=
      expansion 6 (centered 0 length (rootLower (rootArgument s i))) ∧
    centered 0 length (rootArgument s i-rootLower (rootArgument s i)^2)=
      expansion 12 (centered 0 length (rootArgument s i-rootLower (rootArgument s i)^2)) ∧
    centered 0 length (rootUpper (rootArgument s i)^2-rootArgument s i)=
      expansion 12 (centered 0 length (rootUpper (rootArgument s i)^2-rootArgument s i)) := by
  obtain ⟨cA,cp,hA,hl,hh,-,l1,l2,l3⟩ := root_facts s i
  refine ⟨identity_of hl l1,identity_of ?_ l2,identity_of ?_ l3⟩
  · rw [sub_comp,pow_comp,hA,hl,← toPoly_pow,← toPoly_sub]
  · rw [sub_comp,pow_comp,hA,hh,← toPoly_pow,← toPoly_sub]

theorem root_reserves (s : Chain) (i : Fin 8) :
    (2879/2000:ℚ)<lowerOn 6 0 length (rootLower (rootArgument s i)) ∧
    (23/80000000:ℚ)<lowerOn 12 0 length (rootArgument s i-rootLower (rootArgument s i)^2) ∧
    (9/31250000:ℚ)<lowerOn 12 0 length (rootUpper (rootArgument s i)^2-rootArgument s i) := by
  obtain ⟨cA,cp,hA,hl,hh,hok,-,-,-⟩ := root_facts s i
  simp only [rootOK,Bool.and_eq_true] at hok
  obtain ⟨o1,o2,o3,-⟩ := hok
  have e2 : (rootArgument s i-rootLower (rootArgument s i)^2).comp (toPoly affL)=
      toPoly (lsub cA (lpow (lo cp) 2)) := by
    rw [sub_comp,pow_comp,hA,hl,← toPoly_pow,← toPoly_sub]
  have e3 : (rootUpper (rootArgument s i)^2-rootArgument s i).comp (toPoly affL)=
      toPoly (lsub (lpow (hi cp) 2) cA) := by
    rw [sub_comp,pow_comp,hA,hh,← toPoly_pow,← toPoly_sub]
  rw [lowerOn_of hl,lowerOn_of e2,lowerOn_of e3]
  exact ⟨gt_spec o1,gt_spec o2,gt_spec o3⟩

theorem coordinate_identities (s : Chain) (i : Fin 6) :
    centered 0 length (coordinateLower s i)=expansion 6 (centered 0 length (coordinateLower s i)) ∧
    centered 0 length (coordinateUpper s i)=expansion 6 (centered 0 length (coordinateUpper s i)) := by
  obtain ⟨Llo,Lhi,h1,h2,l1,l2,-,-⟩ := coord_facts s i
  exact ⟨identity_of h1 l1,identity_of h2 l2⟩

theorem coordinate_reserves (s : Chain) (i : Fin 6) :
    (1/2:ℚ)<lowerOn 6 0 length (coordinateLower s i) ∧
    upperOn 6 0 length (coordinateUpper s i)<2 := by
  obtain ⟨Llo,Lhi,h1,h2,-,-,o1,o2⟩ := coord_facts s i
  rw [lowerOn_of h1,upperOn_of h2]
  exact ⟨gt_spec o1,lt_spec o2⟩

theorem auxiliary_reserves (s : Chain) :
    (1:ℚ)<lowerOn 6 0 length (rLo s) ∧
    (1:ℚ)<lowerOn 6 0 length (wLo s) ∧
    (1:ℚ)<lowerOn 22 0 length (firstLo s) ∧
    (1:ℚ)<lowerOn 22 0 length (secondLo s) := by
  obtain ⟨-,-,-,-,-,-,-,-,-,-,-,-,o1,o2,o3,o4,-⟩ := chainOK_parts s
  rw [lowerOn_of (rLo_comp s),lowerOn_of (wLo_comp s),lowerOn_of (firstLo_comp s),
    lowerOn_of (secondLo_comp s)]
  exact ⟨gt_spec o1,gt_spec o2,gt_spec o3,gt_spec o4⟩

theorem auxiliary_identities (s : Chain) :
    centered 0 length (firstLo s)=expansion 22 (centered 0 length (firstLo s)) ∧
    centered 0 length (secondLo s)=expansion 22 (centered 0 length (secondLo s)) := by
  obtain ⟨-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,l1,l2⟩ := chainOK_parts s
  exact ⟨identity_of (firstLo_comp s) l1,identity_of (secondLo_comp s) l2⟩

theorem position_identities :
    centered 0 length positionUpper=expansion 64 (centered 0 length positionUpper) ∧
    centered 0 length positionLower=expansion 64 (centered 0 length positionLower) := by
  obtain ⟨-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,l1,l2,-⟩ := allOK_parts
  exact ⟨identity_of (posUpper_comp .lower) l1,identity_of (posLower_comp .upper) l2⟩

theorem position_reserves :
    upperOn 64 0 length positionUpper< -(1/50:ℚ) ∧
    (1/25:ℚ)<lowerOn 64 0 length positionLower := by
  obtain ⟨-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,o1,o2,-⟩ := allOK_parts
  rw [show positionUpper=positionUpperAt .lower from rfl,
    show positionLower=positionLowerAt .upper from rfl,upperOn_of (posUpper_comp .lower),
    lowerOn_of (posLower_comp .upper)]
  exact ⟨lt_spec o1,gt_spec o2⟩

theorem coefficient_identity (i : Coefficient) :
    centered 0 length (cleared i)=expansion 32 (centered 0 length (cleared i)) := by
  obtain ⟨-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11⟩ :=
    allOK_parts
  have h : clearedOK i=true := by
    cases i
    · exact c1
    · exact c2
    · exact c3
    · exact c4
    · exact c5
    · exact c6
    · exact c7
    · exact c8
    · exact c9
    · exact c10
    · exact c11
  simp only [clearedOK,Bool.and_eq_true,decide_eq_true_eq] at h
  exact identity_of (cleared_comp i) h.2

theorem coefficient_reserve (i : Coefficient) : (0:ℚ)<lowerOn 32 0 length (cleared i) := by
  obtain ⟨-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11⟩ :=
    allOK_parts
  have h : clearedOK i=true := by
    cases i
    · exact c1
    · exact c2
    · exact c3
    · exact c4
    · exact c5
    · exact c6
    · exact c7
    · exact c8
    · exact c9
    · exact c10
    · exact c11
  simp only [clearedOK,Bool.and_eq_true] at h
  rw [lowerOn_of (cleared_comp i)]
  exact gt_spec h.1

theorem coefficient_positive (i : Coefficient) {z : ℝ} (hz : z∈Set.Icc 0 (length:ℝ)) :
    0<aeval z (cleared i) := by
  have hz' : z∈Set.Icc ((0:ℚ):ℝ) (length:ℝ) := by rw [Rat.cast_zero]; exact hz
  have h := positive_on_interval (by norm_num [length]) (coefficient_identity i)
    (coefficient_reserve i) hz'
  rwa [Rat.cast_zero] at h

end SquaresInCircles.Eight.TableFree.CriticalEPolynomials
