module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Rat.Star
public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.Positive.ScalarPolynomials
public import SquaresInCircles.Eight.Owners.Stationary.PositionBounds
public import SquaresInCircles.Eight.Owners.Stationary.TerminalWeights
public import SquaresInCircles.Eight.Stationary.CriticalHessian

/-!
# Eight squares: the sharper affine strip for the actual critical position minimum

The comparison signs are obtained from the explicit
whole-interval polynomial enclosures of the original gradient. Strict
position convexity then locates the actual minimizingPosition between
the two affine curves. No root search or localization assumption enters
the theorem, and the tilt varies over the entire critical interval.
-/

section
/-!
## Whole-strip radical polynomials for the sharp supporting chain

There are three intrinsic chains: the lower comparison,
the upper comparison, and the enclosure between them. A sextic root
polynomial is formed algebraically, then proved to enclose the square
root by its squared residual on the entire interval. The displayed
kernel arithmetic proofs have not been executed or replayed.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.CriticalEPolynomials
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


/-! ### Integer arithmetic for the kernel checks

The polynomials above are noncomputable `ℚ[X]` values, so the kernel cannot evaluate them.
Each one is written as a term of `PE`: its meaning `PE.poly` is the polynomial, and its value
`PE.z` is an integer coefficient list with a common denominator
(`WholeIntervalPolynomial.Certificate.Scaled`), which the kernel computes with integer
operations only. The expansion identities need no computation: an exact Chebyshev expansion
holds for every polynomial of degree at most `D`. -/

/-- `C (n/d)`. -/
private theorem rep_frac (n : ℤ) (d : ℕ) (hd : d≠0) :
    (⟨[n],d⟩ : Certificate.Scaled).Rep (C ((n:ℚ)/d)) := by
  unfold Certificate.Scaled.Rep
  have hd' : (d:ℚ)≠0 := by exact_mod_cast hd
  simp only [Certificate.toPoly,mul_zero,add_zero,← map_mul]
  congr 1
  field_simp

private theorem toPoly_mono (n : ℤ) : ∀ k : ℕ,
    Certificate.toPoly (List.replicate k 0++[n])=C (n:ℚ)*X^k
  | 0 => by simp [Certificate.toPoly]
  | k+1 => by
    rw [List.replicate_succ,List.cons_append,Certificate.toPoly,toPoly_mono n k]
    simp only [Int.cast_zero,map_zero,zero_add,pow_succ]
    ring

/-- `C (n/d) * X^k`. -/
private theorem rep_mono (n : ℤ) (d k : ℕ) (hd : d≠0) :
    (⟨List.replicate k 0++[n],d⟩ : Certificate.Scaled).Rep (C ((n:ℚ)/d)*X^k) := by
  unfold Certificate.Scaled.Rep
  have hd' : (d:ℚ)≠0 := by exact_mod_cast hd
  rw [toPoly_mono,← mul_assoc,← map_mul]
  congr 2
  field_simp

/-! Sums over the least common multiple of the two scales -/

private def addZ (a b : Certificate.Scaled) : Certificate.Scaled :=
  ⟨Certificate.add (Certificate.smul ((b.s/Nat.gcd a.s b.s : ℕ) : ℤ) a.l)
    (Certificate.smul ((a.s/Nat.gcd a.s b.s : ℕ) : ℤ) b.l),a.s/Nat.gcd a.s b.s*b.s⟩
private def subZ (a b : Certificate.Scaled) : Certificate.Scaled :=
  ⟨Certificate.add (Certificate.smul ((b.s/Nat.gcd a.s b.s : ℕ) : ℤ) a.l)
    (Certificate.smul (-((a.s/Nat.gcd a.s b.s : ℕ) : ℤ)) b.l),a.s/Nat.gcd a.s b.s*b.s⟩

private theorem gcd_cross (x y : ℕ) : y/Nat.gcd x y*x=x/Nat.gcd x y*y := by
  obtain ⟨k,hk⟩ := Nat.gcd_dvd_left x y
  obtain ⟨m,hm⟩ := Nat.gcd_dvd_right x y
  generalize Nat.gcd x y=g at hk hm ⊢
  subst hk hm
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  · rw [Nat.mul_div_cancel_left _ hg,Nat.mul_div_cancel_left _ hg]
    ring

private theorem C_cross (a b : Certificate.Scaled) :
    C ((b.s/Nat.gcd a.s b.s : ℕ) : ℚ)*C (a.s : ℚ)=C ((a.s/Nat.gcd a.s b.s : ℕ) : ℚ)*C (b.s : ℚ) := by
  rw [← map_mul,← map_mul]
  congr 1
  exact_mod_cast gcd_cross a.s b.s

private theorem rep_addZ {a b : Certificate.Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (addZ a b).Rep (p+q) := by
  unfold Certificate.Scaled.Rep at *
  simp only [addZ,Certificate.toPoly_add,Certificate.toPoly_smul,ha,hb,Int.cast_natCast,
    Nat.cast_mul,map_mul]
  linear_combination p*C_cross a b

private theorem rep_subZ {a b : Certificate.Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (subZ a b).Rep (p-q) := by
  unfold Certificate.Scaled.Rep at *
  simp only [subZ,Certificate.toPoly_add,Certificate.toPoly_smul,ha,hb,Int.cast_neg,
    Int.cast_natCast,Nat.cast_mul,map_mul,map_neg]
  linear_combination p*C_cross a b

/-! Division of a list by the greatest common divisor of its entries and its scale -/

private def contentZ (c : Certificate.Scaled) : ℕ := c.l.foldr (fun x g => Nat.gcd x.natAbs g) c.s
private def reduceZ (c : Certificate.Scaled) : Certificate.Scaled :=
  ⟨c.l.map (fun x => x/(contentZ c : ℤ)),c.s/contentZ c⟩

private theorem content_dvd (s : ℕ) : ∀ l : List ℤ,
    l.foldr (fun x g => Nat.gcd x.natAbs g) s ∣ s ∧
      ∀ x∈l, ((l.foldr (fun x g => Nat.gcd x.natAbs g) s : ℕ) : ℤ) ∣ x
  | [] => ⟨dvd_rfl,by simp⟩
  | y :: l => by
    obtain ⟨h1,h2⟩ := content_dvd s l
    refine ⟨(Nat.gcd_dvd_right _ _).trans h1,fun x hx => ?_⟩
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
    · exact (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)).trans (h2 x hx)

private theorem toPoly_div (g : ℤ) : ∀ l : List ℤ, (∀ x∈l, g ∣ x) →
    C (g:ℚ)*Certificate.toPoly (l.map (fun x => x/g))=Certificate.toPoly l
  | [], _ => by simp [Certificate.toPoly]
  | y :: l, h => by
    have ih := toPoly_div g l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hy : ((y/g : ℤ) : ℚ)*g=y := by exact_mod_cast Int.ediv_mul_cancel (h y List.mem_cons_self)
    have e : C (g:ℚ)*C ((y/g : ℤ) : ℚ)=C (y:ℚ) := by rw [← map_mul,mul_comm,hy]
    simp only [List.map_cons,Certificate.toPoly]
    rw [← ih]
    linear_combination e

private theorem toPoly_map_zero : ∀ l : List ℤ, Certificate.toPoly (l.map (fun x => x/0))=0
  | [] => rfl
  | y :: l => by rw [List.map_cons,Certificate.toPoly,toPoly_map_zero l]; simp

private theorem rep_reduceZ {c : Certificate.Scaled} {p : ℚ[X]} (h : c.Rep p) :
    (reduceZ c).Rep p := by
  obtain ⟨h1,h2⟩ := content_dvd c.s c.l
  unfold Certificate.Scaled.Rep at *
  show Certificate.toPoly (c.l.map (fun x => x/(contentZ c : ℤ)))=C ((c.s/contentZ c : ℕ):ℚ)*p
  rcases Nat.eq_zero_or_pos (contentZ c) with h0 | hpos
  · rw [h0,Nat.cast_zero,toPoly_map_zero,Nat.div_zero,Nat.cast_zero,map_zero,zero_mul]
  · have hg : (contentZ c : ℚ)≠0 := by exact_mod_cast hpos.ne'
    have hd := toPoly_div (contentZ c : ℤ) c.l h2
    rw [Int.cast_natCast,h] at hd
    rw [Nat.cast_div (show contentZ c ∣ c.s from h1) hg]
    apply mul_left_cancel₀ (show C (contentZ c : ℚ)≠0 by simpa using hg)
    rw [hd,← mul_assoc,← map_mul]
    congr 2
    field_simp

/-! The first seven coefficients -/

private theorem sextic_toPoly (l : List ℤ) :
    sextic (Certificate.toPoly l)=Certificate.toPoly (l.take 7) := by
  ext m
  rw [Certificate.coeff_toPoly,sextic,finsetSum_coeff]
  simp only [coeff_monomial,Certificate.coeff_toPoly,Fin.sum_univ_seven]
  rcases m with _|_|_|_|_|_|_|m <;> simp [List.getD_eq_getElem?_getD]

private theorem sextic_C_mul (c : ℚ) (q : ℚ[X]) : sextic (C c*q)=C c*sextic q := by
  simp only [sextic,coeff_C_mul,← C_mul_monomial,← Finset.mul_sum]

private def takeZ (c : Certificate.Scaled) : Certificate.Scaled := ⟨c.l.take 7,c.s⟩

private theorem rep_takeZ {c : Certificate.Scaled} {q : ℚ[X]} (h : c.Rep q) :
    (takeZ c).Rep (sextic q) := by
  unfold Certificate.Scaled.Rep at *
  show Certificate.toPoly (c.l.take 7)=C (c.s:ℚ)*sextic q
  rw [← sextic_toPoly,h,sextic_C_mul]

/-! The root polynomial in integers -/

private def a0Z (A : Certificate.Scaled) : ℤ := A.l.getD 0 0
/-- `⌊A(0) 10^24⌋`. -/
private def mZ (A : Certificate.Scaled) : ℕ := (a0Z A*10^24/(A.s : ℤ)).toNat
/-- `n` is the integer square root of `⌊A(0) 10^24⌋`. -/
private def seedOKZ (A : Certificate.Scaled) (n : ℕ) : Bool :=
  decide (0<a0Z A) && (decide (A.s≠0) && (decide (n*n≤mZ A) && decide (mZ A<(n+1)*(n+1))))
/-- The numerator of `rootSeed` over `10^12`. -/
private def seedNumZ (A : Certificate.Scaled) (n : ℕ) : ℕ :=
  if 4*(a0Z A).toNat*10^24≤(2*n+1)^2*A.s then n else n+1
/-- `(sextic A - A(0)) / A(0)`. -/
private def dZ (A : Certificate.Scaled) : Certificate.Scaled := ⟨0 :: (A.l.drop 1).take 6,(a0Z A).toNat⟩
/-- The binomial sum by Horner's rule; only its first seven coefficients are evaluated. -/
private def hornerZ (d : Certificate.Scaled) : Certificate.Scaled :=
  addZ ⟨[1],1⟩ (d.mul (addZ ⟨[1],2⟩ (d.mul (addZ ⟨[-1],8⟩ (d.mul (addZ ⟨[1],16⟩ (d.mul
    (addZ ⟨[-5],128⟩ (d.mul (addZ ⟨[7],256⟩ (d.mul ⟨[-21],1024⟩)))))))))))
private def rootPolyZ (A : Certificate.Scaled) (n : ℕ) : Certificate.Scaled :=
  reduceZ (takeZ ((⟨[(seedNumZ A n : ℤ)],10^12⟩ : Certificate.Scaled).mul (hornerZ (dZ A))))

private theorem rootSeed_eq {A : Certificate.Scaled} {p : ℚ[X]} (hA : A.Rep p) {n : ℕ}
    (h : seedOKZ A n=true) : rootSeed p=(seedNumZ A n : ℚ)/10^12 := by
  simp only [seedOKZ,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨ha0,hs,h1,h2⟩ := h
  have hc : p.coeff 0=(a0Z A : ℚ)/A.s := hA.coeff hs 0
  have hs' : (0:ℚ)<A.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hfl : ⌊p.coeff 0*(10:ℚ)^24⌋=a0Z A*10^24/(A.s : ℤ) := by
    rw [hc,div_mul_eq_mul_div,show (a0Z A : ℚ)*10^24=((a0Z A*10^24 : ℤ) : ℚ) by push_cast; ring]
    exact Rat.floor_intCast_div_natCast _ _
  have hsq : Nat.sqrt (Int.toNat ⌊p.coeff 0*(10:ℚ)^24⌋)=n := by
    rw [hfl]
    exact (Nat.eq_sqrt.mpr ⟨h1,h2⟩).symm
  have ha : (((a0Z A).toNat : ℕ) : ℚ)=a0Z A := by exact_mod_cast Int.toNat_of_nonneg ha0.le
  have key : p.coeff 0*(10:ℚ)^24≤((n:ℚ)+1/2)^2 ↔ 4*(a0Z A).toNat*10^24≤(2*n+1)^2*A.s := by
    have e : ((4*(a0Z A).toNat*10^24 : ℕ) : ℚ)=4*(a0Z A : ℚ)*10^24 := by
      simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,ha]
    have e' : (((2*n+1)^2*A.s : ℕ) : ℚ)=(2*(n:ℚ)+1)^2*A.s := by push_cast; ring
    rw [← Nat.cast_le (α := ℚ),e,e',hc,div_mul_eq_mul_div,div_le_iff₀ hs']
    constructor <;> intro h <;> linarith
  simp only [rootSeed,hsq,seedNumZ]
  split_ifs with hq hn hn
  · rfl
  · exact absurd (key.mp hq) hn
  · exact absurd (key.mpr hn) hq
  · norm_num

private theorem rep_dZ {A : Certificate.Scaled} {p : ℚ[X]} (hA : A.Rep p) (ha0 : 0<a0Z A)
    (hs : A.s≠0) : (dZ A).Rep (C (1/p.coeff 0)*(sextic p-C (p.coeff 0))) := by
  have hc : p.coeff 0=(a0Z A : ℚ)/A.s := hA.coeff hs 0
  have hs' : (A.s : ℚ)≠0 := by exact_mod_cast hs
  have ha : (((a0Z A).toNat : ℕ) : ℚ)=a0Z A := by exact_mod_cast Int.toNat_of_nonneg ha0.le
  have ht := rep_takeZ hA
  unfold Certificate.Scaled.Rep at ht ⊢
  simp only [dZ,takeZ] at ht ⊢
  rw [ha,hc]
  obtain ⟨l,hl⟩ : ∃ l, A.l=l := ⟨_,rfl⟩
  rw [hl] at ht ⊢
  have hx : a0Z A=l.getD 0 0 := by rw [a0Z,hl]
  rcases l with _|⟨x,l⟩
  · simp at hx; omega
  · simp only [List.getD_cons_zero] at hx
    simp only [List.take_succ_cons,List.drop_succ_cons,List.drop_zero,Certificate.toPoly,
      Int.cast_zero,map_zero,zero_add] at ht ⊢
    rw [hx] at ha0 ⊢
    have hx0 : (x:ℚ)≠0 := by exact_mod_cast ha0.ne'
    have e1 : C (x:ℚ)*C (1/((x:ℚ)/A.s))=C (A.s:ℚ) := by
      rw [← map_mul]; congr 1; field_simp
    have e2 : C (A.s:ℚ)*C ((x:ℚ)/A.s)=C (x:ℚ) := by
      rw [← map_mul]; congr 1; field_simp
    linear_combination (-(sextic p-C ((x:ℚ)/A.s)))*e1+ht+e2

/-- The Horner form of the binomial sum, with the constants as `PE` writes them. -/
private theorem horner_eq (D : ℚ[X]) :
    C (((1:ℤ):ℚ)/(1:ℕ))+D*(C (((1:ℤ):ℚ)/(2:ℕ))+D*(C (((-1:ℤ):ℚ)/(8:ℕ))+D*(C (((1:ℤ):ℚ)/(16:ℕ))+
      D*(C (((-5:ℤ):ℚ)/(128:ℕ))+D*(C (((7:ℤ):ℚ)/(256:ℕ))+D*C (((-21:ℤ):ℚ)/(1024:ℕ)))))))=
      ∑j : Fin 7,C (binomial j)*D^j.val := by
  simp only [Fin.sum_univ_seven,binomial]
  have h3 : ((3:Fin 7):ℕ)=3 := rfl
  have h4 : ((4:Fin 7):ℕ)=4 := rfl
  have h5 : ((5:Fin 7):ℕ)=5 := rfl
  have h6 : ((6:Fin 7):ℕ)=6 := rfl
  simp only [Fin.val_zero,Fin.val_one,Fin.val_two,h3,h4,h5,h6,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val,pow_zero]
  push_cast
  ring_nf

private theorem rep_rootPolyZ {A : Certificate.Scaled} {p : ℚ[X]} (hA : A.Rep p) {n : ℕ}
    (h : seedOKZ A n=true) : (rootPolyZ A n).Rep (rootPolynomial p) := by
  have h' := h
  simp only [seedOKZ,Bool.and_eq_true,decide_eq_true_eq] at h'
  have hd := rep_dZ hA h'.1 h'.2.1
  have hH := rep_addZ (rep_frac 1 1 one_ne_zero) (hd.mul (rep_addZ (rep_frac 1 2 two_ne_zero)
    (hd.mul (rep_addZ (rep_frac (-1) 8 (by norm_num)) (hd.mul (rep_addZ (rep_frac 1 16 (by norm_num))
    (hd.mul (rep_addZ (rep_frac (-5) 128 (by norm_num)) (hd.mul (rep_addZ (rep_frac 7 256 (by norm_num))
    (hd.mul (rep_frac (-21) 1024 (by norm_num)))))))))))))
  have hS := (rep_frac (seedNumZ A n : ℤ) (10^12) (by norm_num)).mul hH
  have hR := rep_reduceZ (rep_takeZ hS)
  rw [horner_eq,Int.cast_natCast,Nat.cast_pow,Nat.cast_ofNat,← rootSeed_eq hA h] at hR
  exact hR

/-! Polynomial expressions -/

private inductive PE where
  | const : ℤ → ℕ → PE
  | mono : ℤ → ℕ → ℕ → PE
  | add : PE → PE → PE
  | sub : PE → PE → PE
  | mul : PE → PE → PE
  | cen : PE → PE
  | trig : PE → PE
  | root : PE → ℕ → PE

private noncomputable def PE.poly : PE → ℚ[X]
  | .const n d => C ((n:ℚ)/d)
  | .mono n d k => C ((n:ℚ)/d)*X^k
  | .add a b => a.poly+b.poly
  | .sub a b => a.poly-b.poly
  | .mul a b => a.poly*b.poly
  | .cen a => centered 0 length a.poly
  | .trig a => centered (1/10) (4/25) a.poly
  | .root a _ => rootPolynomial a.poly

private def PE.z : PE → Certificate.Scaled
  | .const n d => ⟨[n],d⟩
  | .mono n d k => ⟨List.replicate k 0++[n],d⟩
  | .add a b => addZ a.z b.z
  | .sub a b => subZ a.z b.z
  | .mul a b => a.z.mul b.z
  | .cen a => a.z.center 3 100 1 1
  | .trig a => a.z.center 1 100 13 3
  | .root a n => rootPolyZ a.z n

/-- The side conditions: nonzero denominators, and the supplied integer square roots. -/
private def PE.ok : PE → Bool
  | .const _ d => decide (d≠0)
  | .mono _ d _ => decide (d≠0)
  | .add a b => a.ok && b.ok
  | .sub a b => a.ok && b.ok
  | .mul a b => a.ok && b.ok
  | .cen a => a.ok
  | .trig a => a.ok
  | .root a n => a.ok && seedOKZ a.z n

private theorem PE.rep : ∀ e : PE, e.ok=true → e.z.Rep e.poly
  | .const n d, h => rep_frac n d (of_decide_eq_true h)
  | .mono n d k, h => rep_mono n d k (of_decide_eq_true h)
  | .add a b, h => by
    simp only [PE.ok,Bool.and_eq_true] at h
    exact rep_addZ (PE.rep a h.1) (PE.rep b h.2)
  | .sub a b, h => by
    simp only [PE.ok,Bool.and_eq_true] at h
    exact rep_subZ (PE.rep a h.1) (PE.rep b h.2)
  | .mul a b, h => by
    simp only [PE.ok,Bool.and_eq_true] at h
    exact (PE.rep a h.1).mul (PE.rep b h.2)
  | .cen a, h => (PE.rep a h).centered 3 100 1 1 (by norm_num) (by norm_num [length])
      (by norm_num [length])
  | .trig a, h => (PE.rep a h).centered 1 100 13 3 (by norm_num) (by norm_num) (by norm_num)
  | .root a n, h => by
    simp only [PE.ok,Bool.and_eq_true] at h
    exact rep_rootPolyZ (PE.rep a h.1) h.2

/-! Bounds in integers -/

private def lowerZL (D : ℕ) (B : List ℤ) : ℤ :=
  B.getD 0 0-((List.range D).map (fun j => ((B.getD (j+1) 0).natAbs : ℤ))).sum
private def upperZL (D : ℕ) (B : List ℤ) : ℤ :=
  B.getD 0 0+((List.range D).map (fun j => ((B.getD (j+1) 0).natAbs : ℤ))).sum

/-- `rn/rd < lowerOn D 0 length e.poly`, with the degree bound for the expansion. -/
private def gtZ (rn : ℤ) (rd D : ℕ) (e : PE) : Bool :=
  e.ok && (decide (e.z.l.length≤D+1) && (decide (e.z.s≠0) &&
    decide (rn*((e.z.s*2^e.z.l.length : ℕ) : ℤ)<
      lowerZL D (Certificate.chebList e.z.l)*((2*rd : ℕ) : ℤ))))
/-- `upperOn D 0 length e.poly < rn/rd`, with the degree bound for the expansion. -/
private def ltZ (rn : ℤ) (rd D : ℕ) (e : PE) : Bool :=
  e.ok && (decide (e.z.l.length≤D+1) && (decide (e.z.s≠0) &&
    decide (upperZL D (Certificate.chebList e.z.l)*((2*rd : ℕ) : ℤ)<
      rn*((e.z.s*2^e.z.l.length : ℕ) : ℤ))))

private theorem sum_range_list {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i∈Finset.range n,f i=((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,List.range_succ,List.map_append,List.sum_append]; simp

private theorem lowerZ_eq (D : ℕ) (B : List ℤ) :
    Certificate.lowerZ D (fun j => B.getD j 0)=lowerZL D B := by
  simp only [Certificate.lowerZ,lowerZL,
    Fin.sum_univ_eq_sum_range (fun j => |B.getD (j+1) 0|) D,sum_range_list,Int.natCast_natAbs]

private theorem upperZ_eq (D : ℕ) (B : List ℤ) :
    Certificate.upperZ D (fun j => B.getD j 0)=upperZL D B := by
  simp only [Certificate.upperZ,upperZL,
    Fin.sum_univ_eq_sum_range (fun j => |B.getD (j+1) 0|) D,sum_range_list,Int.natCast_natAbs]

private theorem gt_facts {rn : ℤ} {rd D : ℕ} {e : PE} {P : ℚ[X]} {r : ℚ} (h : gtZ rn rd D e=true)
    (hP : centered 0 length P=e.poly) (hr : (rn:ℚ)/rd=r) (hrd : 0<rd) :
    centered 0 length P=expansion D (centered 0 length P) ∧ r<lowerOn D 0 length P := by
  simp only [gtZ,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨hok,hl,hs,hz⟩ := h
  have hrep : e.z.Rep (centered 0 length P) := by rw [hP]; exact e.rep hok
  refine ⟨hrep.eq_expansion hs hl,?_⟩
  rw [Certificate.lowerOn_eq_of_rep hrep hs hl,lowerZ_eq,← hr]
  have hK : (0:ℚ)<e.z.s*2^e.z.l.length :=
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hs) (by positivity)
  have hrd' : (0:ℚ)<rd := by exact_mod_cast hrd
  rw [div_lt_div_iff₀ hrd' (half_pos hK)]
  have hr' := (Int.cast_lt (R := ℚ)).mpr hz
  push_cast at hr'
  linarith

private theorem lt_facts {rn : ℤ} {rd D : ℕ} {e : PE} {P : ℚ[X]} {r : ℚ} (h : ltZ rn rd D e=true)
    (hP : centered 0 length P=e.poly) (hr : (rn:ℚ)/rd=r) (hrd : 0<rd) :
    centered 0 length P=expansion D (centered 0 length P) ∧ upperOn D 0 length P<r := by
  simp only [ltZ,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨hok,hl,hs,hz⟩ := h
  have hrep : e.z.Rep (centered 0 length P) := by rw [hP]; exact e.rep hok
  refine ⟨hrep.eq_expansion hs hl,?_⟩
  rw [Certificate.upperOn_eq_of_rep hrep hs hl,upperZ_eq,← hr]
  have hK : (0:ℚ)<e.z.s*2^e.z.l.length :=
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hs) (by positivity)
  have hrd' : (0:ℚ)<rd := by exact_mod_cast hrd
  rw [div_lt_div_iff₀ (half_pos hK) hrd']
  have hr' := (Int.cast_lt (R := ℚ)).mpr hz
  push_cast at hr'
  linarith

/-! The expressions of this file -/

private def paramE : PE := .add (.const 1 10) (.mono 1 1 1)
private def uMinusE : PE := .sub (.const 499 500) (.mul (.const 127 200) paramE)
private def uPlusE : PE := .sub (.const 501 500) (.mul (.const 16 25) paramE)
private def qL : PE := .const 19577 5000
private def qU : PE := .const 1957767069 500000000
private def two : PE := .const 2 1
private def three : PE := .const 3 1
private def sqE (x : PE) : PE := .mul x x
private def loE (r : PE) : PE := .sub r (.const 1 10000000)
private def hiE (r : PE) : PE := .add r (.const 1 10000000)

private def sineE : PE :=
  .sub (.add (.sub (.add (.sub (.add (.sub (.mono 1 1 1) (.mono 1 6 3)) (.mono 1 120 5))
    (.mono 1 5040 7)) (.mono 1 362880 9)) (.mono 1 39916800 11)) (.mono 1 6227020800 13))
    (.mono 1 1307674368000 15)
private def cosineE : PE :=
  .add (.sub (.add (.sub (.add (.sub (.add (.sub (.const 1 1) (.mono 1 2 2)) (.mono 1 24 4))
    (.mono 1 720 6)) (.mono 1 40320 8)) (.mono 1 3628800 10)) (.mono 1 479001600 12))
    (.mono 1 87178291200 14)) (.mono 1 20922789888000 16)
private def tsLo : PE := .trig sineE
private def tsHi : PE := .trig (.add sineE (.mono 1 1307674368000 15))
private def tcLo : PE := .trig (.sub cosineE (.mono 1 20922789888000 16))
private def tcHi : PE := .trig cosineE

/-! The sixteen roots

The mixed chain takes its lower roots from the `uMinus` side and its upper roots from the
`uPlus` side, so the three chains use sixteen distinct roots. Each is named once, so that the
kernel computes it once. -/

private def argRLoM : PE := .sub qL (sqE uMinusE)
private def argRLoP : PE := .sub qL (sqE uPlusE)
private def argRHiM : PE := .sub qU (sqE uMinusE)
private def argRHiP : PE := .sub qU (sqE uPlusE)
private def argULoM : PE := .sub qL (sqE (.sub two uMinusE))
private def argULoP : PE := .sub qL (sqE (.sub two uPlusE))
private def argUHiM : PE := .sub qU (sqE (.sub two uMinusE))
private def argUHiP : PE := .sub qU (sqE (.sub two uPlusE))
private def rootRLoM : PE := .root argRLoM 1744164484789
private def rootRLoP : PE := .root argRLoP 1742284706929
private def rootRHiM : PE := .root argRHiM 1744202937734
private def rootRHiP : PE := .root argRHiP 1742323201360
private def rootULoM : PE := .root argULoM 1667366111566
private def rootULoP : PE := .root argULoP 1669597556299
private def rootUHiM : PE := .root argUHiM 1667406335600
private def rootUHiP : PE := .root argUHiP 1669637726574
private def argYLoM : PE := .sub qL (sqE (.sub three (loE rootULoM)))
private def argYLoP : PE := .sub qL (sqE (.sub three (loE rootULoP)))
private def argYHiM : PE := .sub qU (sqE (.sub three (hiE rootUHiM)))
private def argYHiP : PE := .sub qU (sqE (.sub three (hiE rootUHiP)))
private def rootYLoM : PE := .root argYLoM 1462698414872
private def rootYLoP : PE := .root argYLoP 1464728326930
private def rootYHiM : PE := .root argYHiM 1462781094395
private def rootYHiP : PE := .root argYHiP 1464810781472
private def argWLoM : PE := .sub qL (sqE (.sub two (loE rootYLoM)))
private def argWLoP : PE := .sub qL (sqE (.sub two (loE rootYLoP)))
private def argWHiM : PE := .sub qU (sqE (.sub two (hiE rootYHiM)))
private def argWHiP : PE := .sub qU (sqE (.sub two (hiE rootYHiP)))
private def rootWLoM : PE := .root argWLoM 1904391477390
private def rootWLoP : PE := .root argWLoP 1904963025613
private def rootWHiM : PE := .root argWHiM 1904450076243
private def rootWHiP : PE := .root argWHiP 1905021455367

/-- The centered chain of one choice of sides. -/
private structure CE where
  a : PE
  b : PE
  rLo : PE
  rHi : PE
  ULo : PE
  UHi : PE
  YLo : PE
  YHi : PE
  wLo : PE
  wHi : PE

private def CE.VLo (c : CE) : PE := .sub three c.UHi
private def CE.VHi (c : CE) : PE := .sub three c.ULo
private def CE.vLo (c : CE) : PE := .sub two c.YHi
private def CE.vHi (c : CE) : PE := .sub two c.YLo

private def ceOf : Chain → CE
  | .lower => ⟨.cen uMinusE,.cen uMinusE,.cen (loE rootRLoM),.cen (hiE rootRHiM),
      .cen (loE rootULoM),.cen (hiE rootUHiM),.cen (loE rootYLoM),.cen (hiE rootYHiM),
      .cen (loE rootWLoM),.cen (hiE rootWHiM)⟩
  | .upper => ⟨.cen uPlusE,.cen uPlusE,.cen (loE rootRLoP),.cen (hiE rootRHiP),
      .cen (loE rootULoP),.cen (hiE rootUHiP),.cen (loE rootYLoP),.cen (hiE rootYHiP),
      .cen (loE rootWLoP),.cen (hiE rootWHiP)⟩
  | .mixed => ⟨.cen uMinusE,.cen uPlusE,.cen (loE rootRLoP),.cen (hiE rootRHiM),
      .cen (loE rootULoM),.cen (hiE rootUHiP),.cen (loE rootYLoM),.cen (hiE rootYHiP),
      .cen (loE rootWLoM),.cen (hiE rootWHiP)⟩

private def CE.firstLo (c : CE) : PE :=
  .add (.sub two (.mul tcHi (.sub c.rHi (.const 1 1)))) (.mul tsLo c.a)
private def CE.firstHi (c : CE) : PE :=
  .add (.sub two (.mul tcLo (.sub c.rLo (.const 1 1)))) (.mul tsHi c.b)
private def CE.secondLo (c : CE) : PE :=
  .sub (.add (.const 1 1) (.mul tcLo c.vLo)) (.mul tsHi (.sub c.wHi (.const 1 1)))
private def CE.secondHi (c : CE) : PE :=
  .sub (.add (.const 1 1) (.mul tcHi c.vHi)) (.mul tsLo (.sub c.wLo (.const 1 1)))

private def CE.posUpper (c : CE) : PE :=
  .sub (.mul (.mul (.mul (.mul c.firstHi (.add (.mul tcHi c.b) (.mul tsHi c.rHi))) c.UHi) c.YHi)
      c.wHi)
    (.mul (.mul (.mul (.mul c.secondLo (.sub two c.b)) c.VLo) (.add (.mul tcLo c.wLo)
      (.mul tsLo c.vLo))) c.rLo)
private def CE.posLower (c : CE) : PE :=
  .sub (.mul (.mul (.mul (.mul c.firstLo (.add (.mul tcLo c.a) (.mul tsLo c.rLo))) c.ULo) c.YLo)
      c.wLo)
    (.mul (.mul (.mul (.mul c.secondHi (.sub two c.a)) c.VHi) (.add (.mul tcHi c.wHi)
      (.mul tsHi c.vHi))) c.rHi)

private def clearedE : Coefficient → PE
  | .etaLower => .sub (ceOf .mixed).vLo (.mul (.const 27 100) (ceOf .mixed).wHi)
  | .etaUpper => .sub (.mul (.const 31 100) (ceOf .mixed).wLo) (ceOf .mixed).vHi
  | .kLower => .sub (.mul (.add (.mul tcLo (ceOf .mixed).wLo) (.mul tsLo (ceOf .mixed).vLo))
      (ceOf .mixed).VLo) (.mul (.mul (.const 37 40) (ceOf .mixed).wHi) (ceOf .mixed).YHi)
  | .kUpper => .sub (.mul (.mul (.const 197 200) (ceOf .mixed).wLo) (ceOf .mixed).YLo)
      (.mul (.add (.mul tcHi (ceOf .mixed).wHi) (.mul tsHi (ceOf .mixed).vHi)) (ceOf .mixed).VHi)
  | .ellUpper => .sub (.mul (.mul (.mul (.const 67 100) (ceOf .mixed).wLo) (ceOf .mixed).YLo)
      (ceOf .mixed).ULo)
      (.mul (.mul (.add (.mul tcHi (ceOf .mixed).wHi) (.mul tsHi (ceOf .mixed).vHi))
        (ceOf .mixed).VHi) (.sub two (ceOf .mixed).a))
  | .ellK => .sub (.mul (.const 27 40) (ceOf .mixed).ULo) (.sub two (ceOf .mixed).a)
  | .cLower => .sub (ceOf .mixed).firstLo (.mul (.const 37 40) (ceOf .mixed).secondHi)
  | .cUpper => .sub (ceOf .mixed).secondLo (ceOf .mixed).firstHi
  | .ellCLower => .sub (.add (.mul tsLo (ceOf .mixed).rLo) (.mul tcLo (ceOf .mixed).a))
      (.mul (.const 63 100) (ceOf .mixed).rHi)
  | .ellCUpper => .sub (.sub (.mul (.const 17 25) (ceOf .mixed).rLo) (.mul tsHi (ceOf .mixed).rHi))
      (.mul tcHi (ceOf .mixed).b)
  | .cK => .sub (.mul (.mul (.const 51 50) (ceOf .lower).ULo) (.add (.mul tsLo (ceOf .lower).rLo)
      (.mul tcLo (ceOf .lower).a))) (.mul (.sub two (ceOf .lower).a) (ceOf .lower).rHi)

/-! The single kernel check of every reserve -/

/-- The three reserves of a root, from its argument `A` and the root `r` of `A`. -/
private def rootOK (A r : PE) : Bool :=
  gtZ 2879 2000 6 (.cen (loE r)) &&
  (gtZ 23 80000000 12 (.sub (.cen A) (sqE (.cen (loE r)))) &&
  gtZ 9 31250000 12 (.sub (sqE (.cen (hiE r))) (.cen A)))

private def chainOK (c : CE) : Bool :=
  gtZ 1 2 6 c.rLo && (gtZ 1 2 6 c.ULo && (gtZ 1 2 6 c.VLo && (gtZ 1 2 6 c.YLo &&
  (gtZ 1 2 6 c.vLo && (gtZ 1 2 6 c.wLo && (ltZ 2 1 6 c.rHi && (ltZ 2 1 6 c.UHi &&
  (ltZ 2 1 6 c.VHi && (ltZ 2 1 6 c.YHi && (ltZ 2 1 6 c.vHi && (ltZ 2 1 6 c.wHi &&
  (gtZ 1 1 6 c.rLo && (gtZ 1 1 6 c.wLo && (gtZ 1 1 22 c.firstLo &&
  gtZ 1 1 22 c.secondLo))))))))))))))

private def clearedOK (i : Coefficient) : Bool := gtZ 0 1 32 (clearedE i)

private def allOK : Bool :=
  rootOK argRLoM rootRLoM && (rootOK argRLoP rootRLoP && (rootOK argRHiM rootRHiM &&
  (rootOK argRHiP rootRHiP && (rootOK argULoM rootULoM && (rootOK argULoP rootULoP &&
  (rootOK argUHiM rootUHiM && (rootOK argUHiP rootUHiP && (rootOK argYLoM rootYLoM &&
  (rootOK argYLoP rootYLoP && (rootOK argYHiM rootYHiM && (rootOK argYHiP rootYHiP &&
  (rootOK argWLoM rootWLoM && (rootOK argWLoP rootWLoP && (rootOK argWHiM rootWHiM &&
  (rootOK argWHiP rootWHiP && (chainOK (ceOf .lower) && (chainOK (ceOf .upper) &&
  (chainOK (ceOf .mixed) && (ltZ (-1) 50 64 (ceOf .lower).posUpper &&
  (gtZ 1 25 64 (ceOf .upper).posLower && (clearedOK .etaLower && (clearedOK .etaUpper &&
  (clearedOK .kLower && (clearedOK .kUpper && (clearedOK .ellUpper && (clearedOK .ellK &&
  (clearedOK .cLower && (clearedOK .cUpper && (clearedOK .ellCLower &&
  (clearedOK .ellCUpper && clearedOK .cK))))))))))))))))))))))))))))))

private theorem allOK_true : allOK=true := by decide +kernel

private theorem allOK_parts :
    rootOK argRLoM rootRLoM=true ∧ rootOK argRLoP rootRLoP=true ∧
    rootOK argRHiM rootRHiM=true ∧ rootOK argRHiP rootRHiP=true ∧
    rootOK argULoM rootULoM=true ∧ rootOK argULoP rootULoP=true ∧
    rootOK argUHiM rootUHiM=true ∧ rootOK argUHiP rootUHiP=true ∧
    rootOK argYLoM rootYLoM=true ∧ rootOK argYLoP rootYLoP=true ∧
    rootOK argYHiM rootYHiM=true ∧ rootOK argYHiP rootYHiP=true ∧
    rootOK argWLoM rootWLoM=true ∧ rootOK argWLoP rootWLoP=true ∧
    rootOK argWHiM rootWHiM=true ∧ rootOK argWHiP rootWHiP=true ∧
    chainOK (ceOf .lower)=true ∧ chainOK (ceOf .upper)=true ∧ chainOK (ceOf .mixed)=true ∧
    ltZ (-1) 50 64 (ceOf .lower).posUpper=true ∧ gtZ 1 25 64 (ceOf .upper).posLower=true ∧
    clearedOK .etaLower=true ∧ clearedOK .etaUpper=true ∧ clearedOK .kLower=true ∧
    clearedOK .kUpper=true ∧ clearedOK .ellUpper=true ∧ clearedOK .ellK=true ∧
    clearedOK .cLower=true ∧ clearedOK .cUpper=true ∧ clearedOK .ellCLower=true ∧
    clearedOK .ellCUpper=true ∧ clearedOK .cK=true := by
  have h := allOK_true
  simp only [allOK,Bool.and_eq_true] at h
  exact h

private theorem chainOK_parts (s : Chain) :
    gtZ 1 2 6 (ceOf s).rLo=true ∧ gtZ 1 2 6 (ceOf s).ULo=true ∧
    gtZ 1 2 6 (ceOf s).VLo=true ∧ gtZ 1 2 6 (ceOf s).YLo=true ∧
    gtZ 1 2 6 (ceOf s).vLo=true ∧ gtZ 1 2 6 (ceOf s).wLo=true ∧
    ltZ 2 1 6 (ceOf s).rHi=true ∧ ltZ 2 1 6 (ceOf s).UHi=true ∧ ltZ 2 1 6 (ceOf s).VHi=true ∧
    ltZ 2 1 6 (ceOf s).YHi=true ∧ ltZ 2 1 6 (ceOf s).vHi=true ∧ ltZ 2 1 6 (ceOf s).wHi=true ∧
    gtZ 1 1 6 (ceOf s).rLo=true ∧ gtZ 1 1 6 (ceOf s).wLo=true ∧
    gtZ 1 1 22 (ceOf s).firstLo=true ∧ gtZ 1 1 22 (ceOf s).secondLo=true := by
  have h : chainOK (ceOf s)=true := by
    obtain ⟨-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,hl,hu,hm,-⟩ := allOK_parts
    cases s
    · exact hl
    · exact hu
    · exact hm
  simp only [chainOK,Bool.and_eq_true] at h
  exact h

/-! The polynomials of this file as expressions -/

private theorem paramE_poly : paramE.poly=parameter := by
  simp only [paramE,PE.poly,parameter]
  norm_num

private theorem uMinusE_poly : uMinusE.poly=uMinus := by
  simp only [uMinusE,PE.poly,paramE_poly,uMinus]
  norm_num

private theorem uPlusE_poly : uPlusE.poly=uPlus := by
  simp only [uPlusE,PE.poly,paramE_poly,uPlus]
  norm_num

private theorem qL_poly : qL.poly=C qLower := by
  simp only [qL,PE.poly,qLower]
  norm_num

private theorem qU_poly : qU.poly=C qUpper := by
  simp only [qU,PE.poly,qUpper]
  norm_num

private theorem two_poly : two.poly=2 := by
  simp only [two,PE.poly]
  norm_num
  exact map_ofNat C 2

private theorem three_poly : three.poly=3 := by
  simp only [three,PE.poly]
  norm_num
  exact map_ofNat C 3

private theorem sqE_poly (x : PE) : (sqE x).poly=x.poly^2 := by
  simp only [sqE,PE.poly,sq]

private theorem loE_poly (r : PE) : (loE r).poly=r.poly-C epsilon := by
  simp only [loE,PE.poly,epsilon]
  norm_num

private theorem hiE_poly (r : PE) : (hiE r).poly=r.poly+C epsilon := by
  simp only [hiE,PE.poly,epsilon]
  norm_num

private def aE : Chain → PE | .lower | .mixed => uMinusE | .upper => uPlusE
private def bE : Chain → PE | .upper | .mixed => uPlusE | .lower => uMinusE

private theorem aE_poly (s : Chain) : (aE s).poly=a s := by
  cases s <;> simp only [aE,a,uMinusE_poly,uPlusE_poly]

private theorem bE_poly (s : Chain) : (bE s).poly=b s := by
  cases s <;> simp only [bE,b,uMinusE_poly,uPlusE_poly]

private def rootRLo : Chain → PE | .lower => rootRLoM | .upper | .mixed => rootRLoP
private def rootRHi : Chain → PE | .lower | .mixed => rootRHiM | .upper => rootRHiP
private def rootULo : Chain → PE | .lower | .mixed => rootULoM | .upper => rootULoP
private def rootUHi : Chain → PE | .lower => rootUHiM | .upper | .mixed => rootUHiP
private def rootYLo : Chain → PE | .lower | .mixed => rootYLoM | .upper => rootYLoP
private def rootYHi : Chain → PE | .lower => rootYHiM | .upper | .mixed => rootYHiP
private def rootWLo : Chain → PE | .lower | .mixed => rootWLoM | .upper => rootWLoP
private def rootWHi : Chain → PE | .lower => rootWHiM | .upper | .mixed => rootWHiP

private theorem argR_poly (q : PE) (x : PE) : (PE.sub q (sqE x)).poly=q.poly-x.poly^2 := by
  rw [PE.poly,sqE_poly]

private theorem rootRLo_poly (s : Chain) : (rootRLo s).poly=rootPolynomial (rArgLo s) := by
  cases s <;> simp only [rootRLo,rootRLoM,rootRLoP,argRLoM,argRLoP,PE.poly,sqE_poly,qL_poly,
    rArgLo,b,uMinusE_poly,uPlusE_poly]

private theorem rootRHi_poly (s : Chain) : (rootRHi s).poly=rootPolynomial (rArgHi s) := by
  cases s <;> simp only [rootRHi,rootRHiM,rootRHiP,argRHiM,argRHiP,PE.poly,sqE_poly,qU_poly,
    rArgHi,a,uMinusE_poly,uPlusE_poly]

private theorem rootULo_poly (s : Chain) : (rootULo s).poly=rootPolynomial (UArgLo s) := by
  cases s <;> simp only [rootULo,rootULoM,rootULoP,argULoM,argULoP,PE.poly,sqE_poly,qL_poly,
    two_poly,UArgLo,a,uMinusE_poly,uPlusE_poly]

private theorem rootUHi_poly (s : Chain) : (rootUHi s).poly=rootPolynomial (UArgHi s) := by
  cases s <;> simp only [rootUHi,rootUHiM,rootUHiP,argUHiM,argUHiP,PE.poly,sqE_poly,qU_poly,
    two_poly,UArgHi,b,uMinusE_poly,uPlusE_poly]

private theorem rLo_eq (s : Chain) : rLo s=(loE (rootRLo s)).poly := by
  rw [loE_poly,rootRLo_poly,rLo,rootLower]
private theorem rHi_eq (s : Chain) : rHi s=(hiE (rootRHi s)).poly := by
  rw [hiE_poly,rootRHi_poly,rHi,rootUpper]
private theorem ULo_eq (s : Chain) : ULo s=(loE (rootULo s)).poly := by
  rw [loE_poly,rootULo_poly,ULo,rootLower]
private theorem UHi_eq (s : Chain) : UHi s=(hiE (rootUHi s)).poly := by
  rw [hiE_poly,rootUHi_poly,UHi,rootUpper]

private theorem rootYLo_poly (s : Chain) : (rootYLo s).poly=rootPolynomial (YArgLo s) := by
  have h := ULo_eq s
  cases s <;> simp only [rootULo] at h <;> simp only [rootYLo,rootYLoM,rootYLoP,argYLoM,argYLoP,
    PE.poly,sqE_poly,qL_poly,YArgLo,VHi,three_poly,h]

private theorem rootYHi_poly (s : Chain) : (rootYHi s).poly=rootPolynomial (YArgHi s) := by
  have h := UHi_eq s
  cases s <;> simp only [rootUHi] at h <;> simp only [rootYHi,rootYHiM,rootYHiP,argYHiM,argYHiP,
    PE.poly,sqE_poly,qU_poly,YArgHi,VLo,three_poly,h]

private theorem YLo_eq (s : Chain) : YLo s=(loE (rootYLo s)).poly := by
  rw [loE_poly,rootYLo_poly,YLo,rootLower]
private theorem YHi_eq (s : Chain) : YHi s=(hiE (rootYHi s)).poly := by
  rw [hiE_poly,rootYHi_poly,YHi,rootUpper]

private theorem rootWLo_poly (s : Chain) : (rootWLo s).poly=rootPolynomial (wArgLo s) := by
  have h := YLo_eq s
  cases s <;> simp only [rootYLo] at h <;> simp only [rootWLo,rootWLoM,rootWLoP,argWLoM,argWLoP,
    PE.poly,sqE_poly,qL_poly,wArgLo,vHi,two_poly,h]

private theorem rootWHi_poly (s : Chain) : (rootWHi s).poly=rootPolynomial (wArgHi s) := by
  have h := YHi_eq s
  cases s <;> simp only [rootYHi] at h <;> simp only [rootWHi,rootWHiM,rootWHiP,argWHiM,argWHiP,
    PE.poly,sqE_poly,qU_poly,wArgHi,vLo,two_poly,h]

private theorem wLo_eq (s : Chain) : wLo s=(loE (rootWLo s)).poly := by
  rw [loE_poly,rootWLo_poly,wLo,rootLower]
private theorem wHi_eq (s : Chain) : wHi s=(hiE (rootWHi s)).poly := by
  rw [hiE_poly,rootWHi_poly,wHi,rootUpper]

/-! Centered polynomials as expressions -/

private theorem cen_add (p q : ℚ[X]) :
    centered 0 length (p+q)=centered 0 length p+centered 0 length q := add_comp
private theorem cen_sub (p q : ℚ[X]) :
    centered 0 length (p-q)=centered 0 length p-centered 0 length q := sub_comp
private theorem cen_mul (p q : ℚ[X]) :
    centered 0 length (p*q)=centered 0 length p*centered 0 length q := mul_comp _ _ _
private theorem cen_sq (p : ℚ[X]) :
    centered 0 length (p^2)=centered 0 length p*centered 0 length p := by
  rw [centered,centered,pow_comp,sq]
private theorem cen_C (c : ℚ) : centered 0 length (C c)=C c := C_comp
private theorem cen_one : centered 0 length 1=(PE.const 1 1).poly := by
  simp only [centered,one_comp,PE.poly]; norm_num
private theorem cen_two : centered 0 length 2=two.poly := by
  simp only [centered,ofNat_comp,two_poly,Nat.cast_ofNat]
private theorem cen_three : centered 0 length 3=three.poly := by
  simp only [centered,ofNat_comp,three_poly,Nat.cast_ofNat]

private theorem a_cen (s : Chain) : centered 0 length (a s)=(ceOf s).a.poly := by
  rw [← aE_poly]; cases s <;> rfl
private theorem b_cen (s : Chain) : centered 0 length (b s)=(ceOf s).b.poly := by
  rw [← bE_poly]; cases s <;> rfl
private theorem rLo_cen (s : Chain) : centered 0 length (rLo s)=(ceOf s).rLo.poly := by
  rw [rLo_eq]; cases s <;> rfl
private theorem rHi_cen (s : Chain) : centered 0 length (rHi s)=(ceOf s).rHi.poly := by
  rw [rHi_eq]; cases s <;> rfl
private theorem ULo_cen (s : Chain) : centered 0 length (ULo s)=(ceOf s).ULo.poly := by
  rw [ULo_eq]; cases s <;> rfl
private theorem UHi_cen (s : Chain) : centered 0 length (UHi s)=(ceOf s).UHi.poly := by
  rw [UHi_eq]; cases s <;> rfl
private theorem YLo_cen (s : Chain) : centered 0 length (YLo s)=(ceOf s).YLo.poly := by
  rw [YLo_eq]; cases s <;> rfl
private theorem YHi_cen (s : Chain) : centered 0 length (YHi s)=(ceOf s).YHi.poly := by
  rw [YHi_eq]; cases s <;> rfl
private theorem wLo_cen (s : Chain) : centered 0 length (wLo s)=(ceOf s).wLo.poly := by
  rw [wLo_eq]; cases s <;> rfl
private theorem wHi_cen (s : Chain) : centered 0 length (wHi s)=(ceOf s).wHi.poly := by
  rw [wHi_eq]; cases s <;> rfl
private theorem VLo_cen (s : Chain) : centered 0 length (VLo s)=(ceOf s).VLo.poly := by
  rw [VLo,cen_sub,UHi_cen,cen_three]; rfl
private theorem VHi_cen (s : Chain) : centered 0 length (VHi s)=(ceOf s).VHi.poly := by
  rw [VHi,cen_sub,ULo_cen,cen_three]; rfl
private theorem vLo_cen (s : Chain) : centered 0 length (vLo s)=(ceOf s).vLo.poly := by
  rw [vLo,cen_sub,YHi_cen,cen_two]; rfl
private theorem vHi_cen (s : Chain) : centered 0 length (vHi s)=(ceOf s).vHi.poly := by
  rw [vHi,cen_sub,YLo_cen,cen_two]; rfl

private theorem param_affine : parameter.comp (affine 0 length)=affine (1/10) (4/25) := by
  simp only [parameter,affine,length,add_comp,C_comp,X_comp]
  rw [← add_assoc,← map_add]
  norm_num

private theorem trig_cen (p : ℚ[X]) (e : PE) (h : e.poly=p) :
    centered 0 length (p.comp parameter)=(PE.trig e).poly := by
  simp only [centered,comp_assoc,param_affine,PE.poly,h]

private theorem sineE_poly : sineE.poly=PositiveScalarPolynomials.sine := by
  simp only [sineE,PE.poly,PositiveScalarPolynomials.sine]
  norm_num

private theorem cosineE_poly : cosineE.poly=PositiveScalarPolynomials.cosine := by
  simp only [cosineE,PE.poly,PositiveScalarPolynomials.cosine]
  norm_num

private theorem sineLo_cen : centered 0 length sineLo=tsLo.poly := trig_cen _ _ sineE_poly
private theorem sineHi_cen : centered 0 length sineHi=tsHi.poly :=
  trig_cen _ _ (by simp only [PE.poly,sineE_poly]; norm_num)
private theorem cosineLo_cen : centered 0 length cosineLo=tcLo.poly :=
  trig_cen _ _ (by simp only [PE.poly,cosineE_poly]; norm_num)
private theorem cosineHi_cen : centered 0 length cosineHi=tcHi.poly := trig_cen _ _ cosineE_poly

private theorem firstLo_cen (s : Chain) : centered 0 length (firstLo s)=(ceOf s).firstLo.poly := by
  simp only [firstLo,cen_add,cen_sub,cen_mul,cen_one,cen_two,a_cen,rHi_cen,cosineHi_cen,
    sineLo_cen,CE.firstLo,PE.poly]
private theorem firstHi_cen (s : Chain) : centered 0 length (firstHi s)=(ceOf s).firstHi.poly := by
  simp only [firstHi,cen_add,cen_sub,cen_mul,cen_one,cen_two,b_cen,rLo_cen,cosineLo_cen,
    sineHi_cen,CE.firstHi,PE.poly]
private theorem secondLo_cen (s : Chain) :
    centered 0 length (secondLo s)=(ceOf s).secondLo.poly := by
  simp only [secondLo,cen_add,cen_sub,cen_mul,cen_one,vLo_cen,wHi_cen,cosineLo_cen,sineHi_cen,
    CE.secondLo,PE.poly]
private theorem secondHi_cen (s : Chain) :
    centered 0 length (secondHi s)=(ceOf s).secondHi.poly := by
  simp only [secondHi,cen_add,cen_sub,cen_mul,cen_one,vHi_cen,wLo_cen,cosineHi_cen,sineLo_cen,
    CE.secondHi,PE.poly]

private theorem posUpper_cen (s : Chain) :
    centered 0 length (positionUpperAt s)=(ceOf s).posUpper.poly := by
  simp only [positionUpperAt,cen_add,cen_sub,cen_mul,cen_two,firstHi_cen,secondLo_cen,b_cen,
    rHi_cen,rLo_cen,UHi_cen,YHi_cen,wHi_cen,wLo_cen,VLo_cen,vLo_cen,cosineHi_cen,cosineLo_cen,
    sineHi_cen,sineLo_cen,CE.posUpper,PE.poly]
private theorem posLower_cen (s : Chain) :
    centered 0 length (positionLowerAt s)=(ceOf s).posLower.poly := by
  simp only [positionLowerAt,cen_add,cen_sub,cen_mul,cen_two,firstLo_cen,secondHi_cen,a_cen,
    rHi_cen,rLo_cen,ULo_cen,YLo_cen,wLo_cen,wHi_cen,VHi_cen,vHi_cen,cosineHi_cen,cosineLo_cen,
    sineHi_cen,sineLo_cen,CE.posLower,PE.poly]

private theorem cleared_cen (i : Coefficient) : centered 0 length (cleared i)=(clearedE i).poly := by
  cases i <;> simp only [cleared,clearedE,cen_add,cen_sub,cen_mul,cen_C,cen_two,firstLo_cen,
    firstHi_cen,secondLo_cen,secondHi_cen,a_cen,b_cen,rLo_cen,rHi_cen,ULo_cen,YLo_cen,YHi_cen,
    wLo_cen,wHi_cen,VLo_cen,VHi_cen,vLo_cen,vHi_cen,cosineHi_cen,cosineLo_cen,sineHi_cen,
    sineLo_cen,PE.poly,Int.cast_ofNat,Nat.cast_ofNat]

/-! Facts for the theorems -/

/-- Everything about one root argument. -/
private theorem pack {Ap : ℚ[X]} {A : PE} {n : ℕ} (hA : A.poly=Ap)
    (hok : rootOK A (.root A n)=true) :
    (centered 0 length (rootLower Ap)=expansion 6 (centered 0 length (rootLower Ap)) ∧
      (2879/2000:ℚ)<lowerOn 6 0 length (rootLower Ap)) ∧
    (centered 0 length (Ap-rootLower Ap^2)=expansion 12 (centered 0 length (Ap-rootLower Ap^2)) ∧
      (23/80000000:ℚ)<lowerOn 12 0 length (Ap-rootLower Ap^2)) ∧
    (centered 0 length (rootUpper Ap^2-Ap)=expansion 12 (centered 0 length (rootUpper Ap^2-Ap)) ∧
      (9/31250000:ℚ)<lowerOn 12 0 length (rootUpper Ap^2-Ap)) := by
  simp only [rootOK,Bool.and_eq_true] at hok
  obtain ⟨h1,h2,h3⟩ := hok
  have e1 : centered 0 length (rootLower Ap)=(PE.cen (loE (.root A n))).poly := by
    simp only [PE.poly,loE_poly,hA,rootLower]
  have e3 : centered 0 length (rootUpper Ap)=(PE.cen (hiE (.root A n))).poly := by
    simp only [PE.poly,hiE_poly,hA,rootUpper]
  have eA : centered 0 length Ap=(PE.cen A).poly := by simp only [PE.poly,hA]
  refine ⟨gt_facts h1 e1 (by norm_num) (by norm_num),gt_facts h2 ?_ (by norm_num) (by norm_num),
    gt_facts h3 ?_ (by norm_num) (by norm_num)⟩
  · rw [cen_sub,cen_sq,eA,e1]; simp only [PE.poly,sqE]
  · rw [cen_sub,cen_sq,eA,e3]; simp only [PE.poly,sqE]

private theorem argRLo_poly (s : Chain) : (PE.sub qL (sqE (bE s))).poly=rArgLo s := by
  rw [argR_poly,qL_poly,bE_poly,rArgLo]
private theorem argRHi_poly (s : Chain) : (PE.sub qU (sqE (aE s))).poly=rArgHi s := by
  rw [argR_poly,qU_poly,aE_poly,rArgHi]
private theorem argULo_poly (s : Chain) : (PE.sub qL (sqE (.sub two (aE s)))).poly=UArgLo s := by
  rw [argR_poly,qL_poly,PE.poly,two_poly,aE_poly,UArgLo]
private theorem argUHi_poly (s : Chain) : (PE.sub qU (sqE (.sub two (bE s)))).poly=UArgHi s := by
  rw [argR_poly,qU_poly,PE.poly,two_poly,bE_poly,UArgHi]
private theorem argYLo_poly (s : Chain) :
    (PE.sub qL (sqE (.sub three (loE (rootULo s))))).poly=YArgLo s := by
  rw [argR_poly,qL_poly,PE.poly,three_poly,← ULo_eq,YArgLo,VHi]
private theorem argYHi_poly (s : Chain) :
    (PE.sub qU (sqE (.sub three (hiE (rootUHi s))))).poly=YArgHi s := by
  rw [argR_poly,qU_poly,PE.poly,three_poly,← UHi_eq,YArgHi,VLo]
private theorem argWLo_poly (s : Chain) :
    (PE.sub qL (sqE (.sub two (loE (rootYLo s))))).poly=wArgLo s := by
  rw [argR_poly,qL_poly,PE.poly,two_poly,← YLo_eq,wArgLo,vHi]
private theorem argWHi_poly (s : Chain) :
    (PE.sub qU (sqE (.sub two (hiE (rootYHi s))))).poly=wArgHi s := by
  rw [argR_poly,qU_poly,PE.poly,two_poly,← YHi_eq,wArgHi,vLo]

private theorem root_facts (s : Chain) (i : Fin 8) :
    (centered 0 length (rootLower (rootArgument s i))=
        expansion 6 (centered 0 length (rootLower (rootArgument s i))) ∧
      (2879/2000:ℚ)<lowerOn 6 0 length (rootLower (rootArgument s i))) ∧
    (centered 0 length (rootArgument s i-rootLower (rootArgument s i)^2)=
        expansion 12 (centered 0 length (rootArgument s i-rootLower (rootArgument s i)^2)) ∧
      (23/80000000:ℚ)<lowerOn 12 0 length (rootArgument s i-rootLower (rootArgument s i)^2)) ∧
    (centered 0 length (rootUpper (rootArgument s i)^2-rootArgument s i)=
        expansion 12 (centered 0 length (rootUpper (rootArgument s i)^2-rootArgument s i)) ∧
      (9/31250000:ℚ)<lowerOn 12 0 length (rootUpper (rootArgument s i)^2-rootArgument s i)) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,-⟩ := allOK_parts
  fin_cases i
  · cases s
    · exact pack (argRLo_poly .lower) h1
    · exact pack (argRLo_poly .upper) h2
    · exact pack (argRLo_poly .mixed) h2
  · cases s
    · exact pack (argRHi_poly .lower) h3
    · exact pack (argRHi_poly .upper) h4
    · exact pack (argRHi_poly .mixed) h3
  · cases s
    · exact pack (argULo_poly .lower) h5
    · exact pack (argULo_poly .upper) h6
    · exact pack (argULo_poly .mixed) h5
  · cases s
    · exact pack (argUHi_poly .lower) h7
    · exact pack (argUHi_poly .upper) h8
    · exact pack (argUHi_poly .mixed) h8
  · cases s
    · exact pack (argYLo_poly .lower) h9
    · exact pack (argYLo_poly .upper) h10
    · exact pack (argYLo_poly .mixed) h9
  · cases s
    · exact pack (argYHi_poly .lower) h11
    · exact pack (argYHi_poly .upper) h12
    · exact pack (argYHi_poly .mixed) h12
  · cases s
    · exact pack (argWLo_poly .lower) h13
    · exact pack (argWLo_poly .upper) h14
    · exact pack (argWLo_poly .mixed) h13
  · cases s
    · exact pack (argWHi_poly .lower) h15
    · exact pack (argWHi_poly .upper) h16
    · exact pack (argWHi_poly .mixed) h16

private theorem coord_facts (s : Chain) (i : Fin 6) :
    (centered 0 length (coordinateLower s i)=
        expansion 6 (centered 0 length (coordinateLower s i)) ∧
      (1/2:ℚ)<lowerOn 6 0 length (coordinateLower s i)) ∧
    (centered 0 length (coordinateUpper s i)=
        expansion 6 (centered 0 length (coordinateUpper s i)) ∧
      upperOn 6 0 length (coordinateUpper s i)<2) := by
  obtain ⟨o1,o2,o3,o4,o5,o6,u1,u2,u3,u4,u5,u6,-⟩ := chainOK_parts s
  have key : ∀ {e e' : PE} {P P' : ℚ[X]}, gtZ 1 2 6 e=true → centered 0 length P=e.poly →
      ltZ 2 1 6 e'=true → centered 0 length P'=e'.poly →
      (centered 0 length P=expansion 6 (centered 0 length P) ∧ (1/2:ℚ)<lowerOn 6 0 length P) ∧
      (centered 0 length P'=expansion 6 (centered 0 length P') ∧ upperOn 6 0 length P'<2) :=
    fun h hP h' hP' => ⟨gt_facts h hP (by norm_num) (by norm_num),
      lt_facts h' hP' (by norm_num) (by norm_num)⟩
  fin_cases i
  · exact key o1 (rLo_cen s) u1 (rHi_cen s)
  · exact key o2 (ULo_cen s) u2 (UHi_cen s)
  · exact key o3 (VLo_cen s) u3 (VHi_cen s)
  · exact key o4 (YLo_cen s) u4 (YHi_cen s)
  · exact key o5 (vLo_cen s) u5 (vHi_cen s)
  · exact key o6 (wLo_cen s) u6 (wHi_cen s)

theorem root_identities (s : Chain) (i : Fin 8) :
    centered 0 length (rootLower (rootArgument s i))=
      expansion 6 (centered 0 length (rootLower (rootArgument s i))) ∧
    centered 0 length (rootArgument s i-rootLower (rootArgument s i)^2)=
      expansion 12 (centered 0 length (rootArgument s i-rootLower (rootArgument s i)^2)) ∧
    centered 0 length (rootUpper (rootArgument s i)^2-rootArgument s i)=
      expansion 12 (centered 0 length (rootUpper (rootArgument s i)^2-rootArgument s i)) := by
  obtain ⟨⟨i1,-⟩,⟨i2,-⟩,⟨i3,-⟩⟩ := root_facts s i
  exact ⟨i1,i2,i3⟩

theorem root_reserves (s : Chain) (i : Fin 8) :
    (2879/2000:ℚ)<lowerOn 6 0 length (rootLower (rootArgument s i)) ∧
    (23/80000000:ℚ)<lowerOn 12 0 length (rootArgument s i-rootLower (rootArgument s i)^2) ∧
    (9/31250000:ℚ)<lowerOn 12 0 length (rootUpper (rootArgument s i)^2-rootArgument s i) := by
  obtain ⟨⟨-,r1⟩,⟨-,r2⟩,⟨-,r3⟩⟩ := root_facts s i
  exact ⟨r1,r2,r3⟩

theorem coordinate_identities (s : Chain) (i : Fin 6) :
    centered 0 length (coordinateLower s i)=expansion 6 (centered 0 length (coordinateLower s i)) ∧
    centered 0 length (coordinateUpper s i)=expansion 6 (centered 0 length (coordinateUpper s i)) := by
  obtain ⟨⟨i1,-⟩,⟨i2,-⟩⟩ := coord_facts s i
  exact ⟨i1,i2⟩

theorem coordinate_reserves (s : Chain) (i : Fin 6) :
    (1/2:ℚ)<lowerOn 6 0 length (coordinateLower s i) ∧
    upperOn 6 0 length (coordinateUpper s i)<2 := by
  obtain ⟨⟨-,r1⟩,⟨-,r2⟩⟩ := coord_facts s i
  exact ⟨r1,r2⟩

private theorem auxiliary_facts (s : Chain) :
    (centered 0 length (rLo s)=expansion 6 (centered 0 length (rLo s)) ∧
      (1:ℚ)<lowerOn 6 0 length (rLo s)) ∧
    (centered 0 length (wLo s)=expansion 6 (centered 0 length (wLo s)) ∧
      (1:ℚ)<lowerOn 6 0 length (wLo s)) ∧
    (centered 0 length (firstLo s)=expansion 22 (centered 0 length (firstLo s)) ∧
      (1:ℚ)<lowerOn 22 0 length (firstLo s)) ∧
    (centered 0 length (secondLo s)=expansion 22 (centered 0 length (secondLo s)) ∧
      (1:ℚ)<lowerOn 22 0 length (secondLo s)) := by
  obtain ⟨-,-,-,-,-,-,-,-,-,-,-,-,o1,o2,o3,o4⟩ := chainOK_parts s
  exact ⟨gt_facts o1 (rLo_cen s) (by norm_num) (by norm_num),
    gt_facts o2 (wLo_cen s) (by norm_num) (by norm_num),
    gt_facts o3 (firstLo_cen s) (by norm_num) (by norm_num),
    gt_facts o4 (secondLo_cen s) (by norm_num) (by norm_num)⟩

theorem auxiliary_reserves (s : Chain) :
    (1:ℚ)<lowerOn 6 0 length (rLo s) ∧
    (1:ℚ)<lowerOn 6 0 length (wLo s) ∧
    (1:ℚ)<lowerOn 22 0 length (firstLo s) ∧
    (1:ℚ)<lowerOn 22 0 length (secondLo s) := by
  obtain ⟨⟨-,r1⟩,⟨-,r2⟩,⟨-,r3⟩,⟨-,r4⟩⟩ := auxiliary_facts s
  exact ⟨r1,r2,r3,r4⟩

theorem auxiliary_identities (s : Chain) :
    centered 0 length (firstLo s)=expansion 22 (centered 0 length (firstLo s)) ∧
    centered 0 length (secondLo s)=expansion 22 (centered 0 length (secondLo s)) := by
  obtain ⟨-,-,⟨i3,-⟩,⟨i4,-⟩⟩ := auxiliary_facts s
  exact ⟨i3,i4⟩

private theorem position_facts :
    (centered 0 length positionUpper=expansion 64 (centered 0 length positionUpper) ∧
      upperOn 64 0 length positionUpper< -(1/50:ℚ)) ∧
    (centered 0 length positionLower=expansion 64 (centered 0 length positionLower) ∧
      (1/25:ℚ)<lowerOn 64 0 length positionLower) := by
  obtain ⟨-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,o1,o2,-⟩ := allOK_parts
  exact ⟨lt_facts o1 (posUpper_cen .lower) (by norm_num) (by norm_num),
    gt_facts o2 (posLower_cen .upper) (by norm_num) (by norm_num)⟩

theorem position_identities :
    centered 0 length positionUpper=expansion 64 (centered 0 length positionUpper) ∧
    centered 0 length positionLower=expansion 64 (centered 0 length positionLower) :=
  ⟨position_facts.1.1,position_facts.2.1⟩

theorem position_reserves :
    upperOn 64 0 length positionUpper< -(1/50:ℚ) ∧
    (1/25:ℚ)<lowerOn 64 0 length positionLower :=
  ⟨position_facts.1.2,position_facts.2.2⟩

private theorem coefficient_facts (i : Coefficient) :
    centered 0 length (cleared i)=expansion 32 (centered 0 length (cleared i)) ∧
      (0:ℚ)<lowerOn 32 0 length (cleared i) := by
  obtain ⟨-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11⟩ :=
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
  exact gt_facts h (cleared_cen i) (by norm_num) (by norm_num)

theorem coefficient_identity (i : Coefficient) :
    centered 0 length (cleared i)=expansion 32 (centered 0 length (cleared i)) :=
  (coefficient_facts i).1

theorem coefficient_reserve (i : Coefficient) : (0:ℚ)<lowerOn 32 0 length (cleared i) :=
  (coefficient_facts i).2

theorem coefficient_positive (i : Coefficient) {z : ℝ} (hz : z∈Set.Icc 0 (length:ℝ)) :
    0<aeval z (cleared i) := by
  have hz' : z∈Set.Icc ((0:ℚ):ℝ) (length:ℝ) := by rw [Rat.cast_zero]; exact hz
  have h := positive_on_interval (by norm_num [length]) (coefficient_identity i)
    (coefficient_reserve i) hz'
  rwa [Rat.cast_zero] at h

end SquaresInCircles.Eight.CriticalEPolynomials
end
end
end

section
/-!
## Transfer of the sextic enclosures to the actual circle roots

Each step uses the same original q and u. Squaring
and monotonicity transfer the polynomial residuals successively through
r, U, V, Y, v and w. No independent root choices or altered radii enter
the chain, and no comparison-position premise is hidden in the result.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalERadicals
open Polynomial WholeIntervalPolynomial CriticalEPolynomials
open Stationary.FiveCornerGeometry

def ev (t : ℝ) (P : ℚ[X]) : ℝ := aeval (t-1/10) P

@[simp] theorem ev_add (t : ℝ) (P Q : ℚ[X]) : ev t (P+Q)=ev t P+ev t Q := by simp [ev]
@[simp] theorem ev_sub (t : ℝ) (P Q : ℚ[X]) : ev t (P-Q)=ev t P-ev t Q := by simp [ev]
@[simp] theorem ev_mul (t : ℝ) (P Q : ℚ[X]) : ev t (P*Q)=ev t P*ev t Q := by simp [ev]
@[simp] theorem ev_pow (t : ℝ) (P : ℚ[X]) (n : ℕ) : ev t (P^n)=ev t P^n := by simp [ev]
@[simp] theorem ev_C (t : ℝ) (r : ℚ) : ev t (C r)=(r:ℝ) := by simp [ev]
@[simp] theorem ev_nat (t : ℝ) (n : ℕ) : ev t (n:ℚ[X])=n := by simp [ev]
@[simp] theorem ev_parameter (t : ℝ) : ev t parameter=t := by simp [ev,parameter]
@[simp] theorem ev_minus (t : ℝ) : ev t uMinus=499/500-(127/200)*t := by simp [uMinus]
@[simp] theorem ev_plus (t : ℝ) : ev t uPlus=501/500-(16/25)*t := by simp [uPlus]

private theorem ev_two (t : ℝ) : ev t (2 : ℚ[X])=2 := by
  rw [ev]
  exact map_ofNat _ 2

private theorem ev_three (t : ℝ) : ev t (3 : ℚ[X])=3 := by
  rw [ev]
  exact map_ofNat _ 3

theorem local_parameter {t : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25)) :
    t-1/10∈Icc 0 (length:ℝ) := by
  norm_num [length]
  constructor <;> linarith [ht.1,ht.2]

theorem endpoints {t : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25)) (s : Chain) :
    (89/100:ℝ)<ev t (a s) ∧ ev t (a s)≤ev t (b s) ∧ ev t (b s)<19/20 := by
  cases s <;> simp only [a,b,ev_minus,ev_plus] <;>
    exact ⟨by linarith [ht.1,ht.2],by linarith [ht.1,ht.2],by linarith [ht.1,ht.2]⟩

theorem root_squares (s : Chain) (i : Fin 8) {t : ℝ}
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    0<ev t (rootLower (rootArgument s i)) ∧
    ev t (rootLower (rootArgument s i))^2<ev t (rootArgument s i) ∧
    ev t (rootArgument s i)<ev t (rootUpper (rootArgument s i))^2 ∧
    0<ev t (rootUpper (rootArgument s i)) := by
  have hz : t-1/10∈Icc ((0:ℚ):ℝ) (length:ℝ) := by
    rw [Rat.cast_zero]; exact local_parameter ht
  have h0 := positive_on_interval (by norm_num [length])
    (root_identities s i).1 (root_reserves s i).1 hz
  have h1 := positive_on_interval (by norm_num [length])
    (root_identities s i).2.1 (root_reserves s i).2.1 hz
  have h2 := positive_on_interval (by norm_num [length])
    (root_identities s i).2.2 (root_reserves s i).2.2 hz
  have h0' : (2879/2000:ℝ)<ev t (rootLower (rootArgument s i)) :=
    (by norm_num : (2879/2000:ℝ)=((2879/2000:ℚ):ℝ)).trans_lt h0
  have h1' : (23/80000000:ℝ)<ev t (rootArgument s i-rootLower (rootArgument s i)^2) :=
    (by norm_num : (23/80000000:ℝ)=((23/80000000:ℚ):ℝ)).trans_lt h1
  have h2' : (9/31250000:ℝ)<ev t (rootUpper (rootArgument s i)^2-rootArgument s i) :=
    (by norm_num : (9/31250000:ℝ)=((9/31250000:ℚ):ℝ)).trans_lt h2
  simp only [ev_sub,ev_pow] at h1' h2'
  have hdiff : ev t (rootUpper (rootArgument s i))-ev t (rootLower (rootArgument s i))=
      2/10000000 := by
    simp only [rootUpper,rootLower,ev_add,ev_sub,ev_C,epsilon]
    push_cast
    ring
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem root_between (s : Chain) (i j : Fin 8) {t z : ℝ}
    (ht : t∈Icc (1/10:ℝ) (4/25))
    (hz : z∈Icc (ev t (rootArgument s i)) (ev t (rootArgument s j))) :
    ev t (rootLower (rootArgument s i))<Real.sqrt z ∧
    Real.sqrt z<ev t (rootUpper (rootArgument s j)) := by
  have hi := root_squares s i ht
  have hj := root_squares s j ht
  have hz0 : 0≤z := by nlinarith [hi.2.1,hz.1,sq_nonneg (ev t (rootLower (rootArgument s i)))]
  have hs0 := Real.sqrt_nonneg z
  have hs2 := Real.sq_sqrt hz0
  constructor <;> nlinarith [hi.1,hi.2.1,hj.2.2.1,hj.2.2.2,hz.1,hz.2]

theorem polynomial_coordinates (s : Chain) (i : Fin 6) {t : ℝ}
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    1/2<ev t (coordinateLower s i) ∧ ev t (coordinateUpper s i)<2 := by
  have hz : t-1/10∈Icc ((0:ℚ):ℝ) (length:ℝ) := by
    rw [Rat.cast_zero]; exact local_parameter ht
  have hh := positive_on_interval (by norm_num [length])
    (coordinate_identities s i).1 (coordinate_reserves s i).1 hz
  have hu := (interval_bounds (by norm_num [length])
    (coordinate_identities s i).2 hz).2
  have hc : (upperOn 6 0 length (coordinateUpper s i):ℝ)<2 := by
    exact_mod_cast (coordinate_reserves s i).2
  have hh' : (1/2:ℝ)<ev t (coordinateLower s i) :=
    (by norm_num : (1/2:ℝ)=((1/2:ℚ):ℝ)).trans_lt hh
  exact ⟨hh',hu.trans_lt hc⟩

structure RadicalBounds (s : Chain) (q t u : ℝ) : Prop where
  r : lowerRight q u∈Icc (ev t (rLo s)) (ev t (rHi s))
  U : topRight q u∈Icc (ev t (ULo s)) (ev t (UHi s))
  V : topLeft q u∈Icc (ev t (VLo s)) (ev t (VHi s))
  Y : topHeight q u∈Icc (ev t (YLo s)) (ev t (YHi s))
  v : lowerHeight q u∈Icc (ev t (vLo s)) (ev t (vHi s))
  w : lowerLeft q u∈Icc (ev t (wLo s)) (ev t (wHi s))

theorem actual_radicals (s : Chain) {q t u : ℝ}
    (hq : q∈Icc (qLower:ℝ) (qUpper:ℝ)) (ht : t∈Icc (1/10:ℝ) (4/25))
    (hu : u∈Icc (ev t (a s)) (ev t (b s))) : RadicalBounds s q t u := by
  have hab := endpoints ht s
  have ha : 0≤ev t (a s) := by linarith [hab.1]
  have hu0 : 0≤u := ha.trans hu.1
  have hrarg : q-u^2∈Icc (ev t (rootArgument s 0)) (ev t (rootArgument s 1)) := by
    have hl := square_mono_nonneg ha hu.1
    have hh := square_mono_nonneg hu0 hu.2
    simp only [rootArgument,Matrix.cons_val_zero,Matrix.cons_val_one,rArgLo,rArgHi,
      ev_sub,ev_C,ev_pow]
    constructor <;> linarith [hq.1,hq.2]
  obtain ⟨hrlo,hrhi⟩ := root_between s 0 1 ht hrarg
  have hr : lowerRight q u∈Icc (ev t (rLo s)) (ev t (rHi s)) := ⟨hrlo.le,hrhi.le⟩
  have hUarg : q-(2-u)^2∈Icc (ev t (rootArgument s 2)) (ev t (rootArgument s 3)) := by
    have hb : 0≤2-ev t (b s) := by linarith [hab.2.2]
    have hlow := square_mono_nonneg hb (show 2-ev t (b s)≤2-u by linarith [hu.2])
    have hhigh := square_mono_nonneg (show 0≤2-u by linarith [hu.2,hab.2.2])
      (show 2-u≤2-ev t (a s) by linarith [hu.1])
    have e2 : ev t (rootArgument s 2)=qLower-(2-ev t (a s))^2 := by
      simp [rootArgument,UArgLo,ev_two]
    have e3 : ev t (rootArgument s 3)=qUpper-(2-ev t (b s))^2 := by
      simp [rootArgument,UArgHi,ev_two]
    rw [e2,e3]
    constructor <;> linarith [hq.1,hq.2]
  obtain ⟨hUlo,hUhi⟩ := root_between s 2 3 ht hUarg
  have hU : topRight q u∈Icc (ev t (ULo s)) (ev t (UHi s)) := ⟨hUlo.le,hUhi.le⟩
  have hV : topLeft q u∈Icc (ev t (VLo s)) (ev t (VHi s)) := by
    simp only [topLeft,VLo,VHi,ev_sub,ev_three]
    exact ⟨by linarith [hU.2],by linarith [hU.1]⟩
  have hV0 : 0≤ev t (VLo s) := by
    have h2 : 1/2<ev t (VLo s) := (polynomial_coordinates s 2 ht).1
    linarith
  have hYarg : q-topLeft q u^2∈Icc (ev t (rootArgument s 4)) (ev t (rootArgument s 5)) := by
    have hlo := square_mono_nonneg hV0 hV.1
    have hhi := square_mono_nonneg (hV0.trans hV.1) hV.2
    have e4 : ev t (rootArgument s 4)=qLower-(ev t (VHi s))^2 := by
      simp [rootArgument,YArgLo]
    have e5 : ev t (rootArgument s 5)=qUpper-(ev t (VLo s))^2 := by
      simp [rootArgument,YArgHi]
    rw [e4,e5]
    constructor <;> linarith [hq.1,hq.2]
  obtain ⟨hYlo,hYhi⟩ := root_between s 4 5 ht hYarg
  have hY : topHeight q u∈Icc (ev t (YLo s)) (ev t (YHi s)) := ⟨hYlo.le,hYhi.le⟩
  have hv : lowerHeight q u∈Icc (ev t (vLo s)) (ev t (vHi s)) := by
    simp only [lowerHeight,vLo,vHi,ev_sub,ev_two]
    exact ⟨by linarith [hY.2],by linarith [hY.1]⟩
  have hv0 : 0≤ev t (vLo s) := by
    have h4 : 1/2<ev t (vLo s) := (polynomial_coordinates s 4 ht).1
    linarith
  have hwarg : q-lowerHeight q u^2∈Icc (ev t (rootArgument s 6)) (ev t (rootArgument s 7)) := by
    have hlo := square_mono_nonneg hv0 hv.1
    have hhi := square_mono_nonneg (hv0.trans hv.1) hv.2
    have e6 : ev t (rootArgument s 6)=qLower-(ev t (vHi s))^2 := by
      simp [rootArgument,wArgLo]
    have e7 : ev t (rootArgument s 7)=qUpper-(ev t (vLo s))^2 := by
      simp [rootArgument,wArgHi]
    rw [e6,e7]
    constructor <;> linarith [hq.1,hq.2]
  obtain ⟨hwlo,hwhi⟩ := root_between s 6 7 ht hwarg
  exact ⟨hr,hU,hV,hY,hv,hwlo.le,hwhi.le⟩

theorem RadicalBounds.smoothDomain {s : Chain} {q t u : ℝ}
    (h : RadicalBounds s q t u) (ht : t∈Icc (1/10:ℝ) (4/25))
    (hu : 0≤u) (hq : q<4) : SmoothDomain q u := by
  have h0 : 1/2<ev t (rLo s) := (polynomial_coordinates s 0 ht).1
  have h1 : 1/2<ev t (ULo s) := (polynomial_coordinates s 1 ht).1
  have h3 : 1/2<ev t (YLo s) := (polynomial_coordinates s 3 ht).1
  have h5 : 1/2<ev t (wLo s) := (polynomial_coordinates s 5 ht).1
  have hr : 0<lowerRight q u := by linarith [h.r.1]
  have hU : 0<topRight q u := by linarith [h.U.1]
  have hY : 0<topHeight q u := by linarith [h.Y.1]
  have hw : 0<lowerLeft q u := by linarith [h.w.1]
  exact ⟨⟨hu,by linarith [Real.sqrt_pos.mp hr],by linarith [Real.sqrt_pos.mp hU],
    by linarith [Real.sqrt_pos.mp hY],by linarith [Real.sqrt_pos.mp hw]⟩,hq,hr,hU,hY,hw⟩

end SquaresInCircles.Eight.CriticalERadicals
end
end
end

section
/-!
## Positive substitution into the actual cleared position equation

Bounds are attached to the actual trigonometric
and radical expressions. Their products have the displayed polynomial
endpoints, so the full-interval signs apply to the real position
gradient after clearing only its proved positive denominator.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalESubstitution
open Polynomial CriticalEPolynomials CriticalERadicals WholeIntervalPolynomial
open Stationary.FiveCornerGeometry HighOrderTaylor

theorem trig_evaluations (t : ℝ) :
    ev t sineLo=S15 t ∧ ev t sineHi=S13 t ∧
    ev t cosineLo=C14 t ∧ ev t cosineHi=C16 t := by
  have hp : aeval (t-1/10) parameter=t := by
    simp only [parameter,map_add,aeval_C,aeval_X,eq_ratCast]
    push_cast
    ring
  refine ⟨?_,?_,?_,?_⟩ <;>
    simp only [ev,sineLo,sineHi,cosineLo,cosineHi,aeval_comp,hp,map_add,map_sub,map_mul,
      map_pow,aeval_C,aeval_X,eq_ratCast,PositiveScalarPolynomials.sine_eval,
      PositiveScalarPolynomials.cosine_eval]
  · simp only [S15]
    push_cast
    ring
  · simp only [C16]
    push_cast
    ring

theorem trig_bounds {t : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25)) :
    Real.sin t∈Icc (ev t sineLo) (ev t sineHi) ∧
    Real.cos t∈Icc (ev t cosineLo) (ev t cosineHi) ∧
    0≤ev t sineLo ∧ 0<ev t cosineLo := by
  have ht0 : 0≤t := by linarith [ht.1]
  have ht' : t∈Icc 0 frameCap := ⟨ht0,by dsimp [frameCap]; linarith [ht.2]⟩
  obtain ⟨hs,hs',hc,hc'⟩ := trig_evaluations t
  rw [hs,hs',hc,hc']
  exact ⟨⟨S15_le_sin ht0,sin_le_S13 ht0⟩,⟨C14_le_cos ht0,cos_le_C16 ht0⟩,
    S15_nonneg ht',C14_pos ht'⟩

theorem auxiliary_bounds (s : Chain) {t : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25)) :
    1<ev t (rLo s) ∧ 1<ev t (wLo s) ∧
    1<ev t (firstLo s) ∧ 1<ev t (secondLo s) := by
  have hz : t-1/10∈Icc ((0:ℚ):ℝ) (length:ℝ) := by
    rw [Rat.cast_zero]
    exact local_parameter ht
  have h0 := positive_on_interval (by norm_num [length]) (coordinate_identities s 0).1
    (auxiliary_reserves s).1 hz
  have h1 := positive_on_interval (by norm_num [length]) (coordinate_identities s 5).1
    (auxiliary_reserves s).2.1 hz
  have h2 := positive_on_interval (by norm_num [length]) (auxiliary_identities s).1
    (auxiliary_reserves s).2.2.1 hz
  have h3 := positive_on_interval (by norm_num [length]) (auxiliary_identities s).2
    (auxiliary_reserves s).2.2.2 hz
  rw [Rat.cast_one] at h0 h1 h2 h3
  exact ⟨h0,h1,h2,h3⟩

theorem component_bounds {s : Chain} {q t u : ℝ}
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hu : u∈Icc (ev t (a s)) (ev t (b s)))
    (h : RadicalBounds s q t u) :
    firstComponent q (Real.cos t) (Real.sin t) u∈Icc (ev t (firstLo s)) (ev t (firstHi s)) ∧
    secondComponent q (Real.cos t) (Real.sin t) u∈Icc (ev t (secondLo s)) (ev t (secondHi s)) := by
  obtain ⟨hs,hc,hs0,hc0⟩ := trig_bounds ht
  obtain ⟨hr,hw,_,_⟩ := auxiliary_bounds s ht
  have hv4 : 1/2<ev t (vLo s) := (polynomial_coordinates s 4 ht).1
  have hcr := StationaryPrimitives.product_bounds hc
    (show lowerRight q u-1∈Icc (ev t (rLo s)-1) (ev t (rHi s)-1) by
      constructor <;> linarith [h.r.1,h.r.2]) hc0.le (by linarith)
  have hsu := StationaryPrimitives.product_bounds hs hu hs0
    (by have h' := (endpoints ht s).1; linarith)
  have hcv := StationaryPrimitives.product_bounds hc h.v hc0.le (by linarith)
  have hsw := StationaryPrimitives.product_bounds hs
    (show lowerLeft q u-1∈Icc (ev t (wLo s)-1) (ev t (wHi s)-1) by
      constructor <;> linarith [h.w.1,h.w.2]) hs0 (by linarith)
  have e1 : ev t (1:ℚ[X])=1 := by simp [ev]
  have e2 : ev t (2:ℚ[X])=2 := by rw [ev]; exact map_ofNat _ 2
  simp only [firstComponent,secondComponent,firstLo,firstHi,secondLo,secondHi,
    ev_sub,ev_add,ev_mul,e1,e2]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> linarith [hcr.1,hcr.2,hsu.1,hsu.2,hcv.1,hcv.2,hsw.1,hsw.2]

/-- Elementary positive interval multiplication, without a state grid. -/
structure PositiveInterval (x : ℝ) where
  lo : ℝ
  hi : ℝ
  mem : x∈Icc lo hi
  lo_nonneg : 0≤lo

namespace PositiveInterval

def of_bounds {x a b : ℝ} (h : x∈Icc a b) (ha : 0≤a) : PositiveInterval x := ⟨a,b,h,ha⟩
def add {x y : ℝ} (X : PositiveInterval x) (Y : PositiveInterval y) : PositiveInterval (x+y) :=
  ⟨X.lo+Y.lo,X.hi+Y.hi,⟨add_le_add X.mem.1 Y.mem.1,add_le_add X.mem.2 Y.mem.2⟩,
    add_nonneg X.lo_nonneg Y.lo_nonneg⟩
def mul {x y : ℝ} (X : PositiveInterval x) (Y : PositiveInterval y) : PositiveInterval (x*y) :=
  ⟨X.lo*Y.lo,X.hi*Y.hi,StationaryPrimitives.product_bounds X.mem Y.mem X.lo_nonneg Y.lo_nonneg,
    mul_nonneg X.lo_nonneg Y.lo_nonneg⟩

theorem lower_ratio {x y r : ℝ} (X : PositiveInterval x) (Y : PositiveInterval y)
    (hy : 0<Y.lo) (hr : 0≤r) (h : r*Y.hi<X.lo) : r<x/y := by
  have hyp : 0<y := hy.trans_le Y.mem.1
  apply (lt_div_iff₀ hyp).2
  have hm := mul_le_mul_of_nonneg_left Y.mem.2 hr
  linarith [X.mem.1]

theorem upper_ratio {x y r : ℝ} (X : PositiveInterval x) (Y : PositiveInterval y)
    (hy : 0<Y.lo) (hr : 0≤r) (h : X.hi<r*Y.lo) : x/y<r := by
  have hyp : 0<y := hy.trans_le Y.mem.1
  apply (div_lt_iff₀ hyp).2
  have hm := mul_le_mul_of_nonneg_left Y.mem.1 hr
  linarith [X.mem.2]

end PositiveInterval

structure Boxes (s : Chain) (q t u : ℝ) where
  height : PositiveInterval u
  height_lo : height.lo=ev t (a s)
  height_hi : height.hi=ev t (b s)
  other : PositiveInterval (2-u)
  other_lo : other.lo=2-ev t (b s)
  other_hi : other.hi=2-ev t (a s)
  r : PositiveInterval (lowerRight q u)
  r_lo : r.lo=ev t (rLo s)
  r_hi : r.hi=ev t (rHi s)
  U : PositiveInterval (topRight q u)
  U_lo : U.lo=ev t (ULo s)
  U_hi : U.hi=ev t (UHi s)
  V : PositiveInterval (topLeft q u)
  V_lo : V.lo=ev t (VLo s)
  V_hi : V.hi=ev t (VHi s)
  Y : PositiveInterval (topHeight q u)
  Y_lo : Y.lo=ev t (YLo s)
  Y_hi : Y.hi=ev t (YHi s)
  v : PositiveInterval (lowerHeight q u)
  v_lo : v.lo=ev t (vLo s)
  v_hi : v.hi=ev t (vHi s)
  w : PositiveInterval (lowerLeft q u)
  w_lo : w.lo=ev t (wLo s)
  w_hi : w.hi=ev t (wHi s)
  sine : PositiveInterval (Real.sin t)
  sine_lo : sine.lo=ev t sineLo
  sine_hi : sine.hi=ev t sineHi
  cosine : PositiveInterval (Real.cos t)
  cosine_lo : cosine.lo=ev t cosineLo
  cosine_hi : cosine.hi=ev t cosineHi
  first : PositiveInterval (firstComponent q (Real.cos t) (Real.sin t) u)
  first_lo : first.lo=ev t (firstLo s)
  first_hi : first.hi=ev t (firstHi s)
  second : PositiveInterval (secondComponent q (Real.cos t) (Real.sin t) u)
  second_lo : second.lo=ev t (secondLo s)
  second_hi : second.hi=ev t (secondHi s)

def boxes {s : Chain} {q t u : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25))
    (hu : u∈Icc (ev t (a s)) (ev t (b s))) (h : RadicalBounds s q t u) : Boxes s q t u := by
  have hp (i : Fin 6) : 0≤ev t (coordinateLower s i) := by linarith [(polynomial_coordinates s i ht).1]
  have hb := endpoints ht s
  have ht' := trig_bounds ht
  have hf := component_bounds ht hu h
  have ha := auxiliary_bounds s ht
  refine ⟨PositiveInterval.of_bounds hu (by linarith [hb.1]),rfl,rfl,
    PositiveInterval.of_bounds ⟨by linarith [hu.2],by linarith [hu.1]⟩ (by linarith [hb.2.2]),rfl,rfl,
    PositiveInterval.of_bounds h.r (hp 0),rfl,rfl,
    PositiveInterval.of_bounds h.U (hp 1),rfl,rfl,
    PositiveInterval.of_bounds h.V (hp 2),rfl,rfl,
    PositiveInterval.of_bounds h.Y (hp 3),rfl,rfl,
    PositiveInterval.of_bounds h.v (hp 4),rfl,rfl,
    PositiveInterval.of_bounds h.w (hp 5),rfl,rfl,
    PositiveInterval.of_bounds ht'.1 ht'.2.2.1,rfl,rfl,
    PositiveInterval.of_bounds ht'.2.1 ht'.2.2.2.le,rfl,rfl,
    PositiveInterval.of_bounds hf.1 (by linarith [ha.2.2.1]),rfl,rfl,
    PositiveInterval.of_bounds hf.2 (by linarith [ha.2.2.2]),rfl,rfl⟩

def clearedPosition (q t u : ℝ) : ℝ :=
  firstComponent q (Real.cos t) (Real.sin t) u*(Real.cos t*u+Real.sin t*lowerRight q u)*
    topRight q u*topHeight q u*lowerLeft q u-
  secondComponent q (Real.cos t) (Real.sin t) u*(2-u)*topLeft q u*
    (Real.cos t*lowerLeft q u+Real.sin t*lowerHeight q u)*lowerRight q u

theorem clearedPosition_identity {q t u : ℝ} (h : SmoothDomain q u) :
    clearedPosition q t u=positionHalf q (Real.cos t) (Real.sin t) u*
      (lowerRight q u*topRight q u*topHeight q u*lowerLeft q u) := by
  dsimp [clearedPosition,positionHalf,slopeRatio]
  field_simp [h.r_pos.ne',h.U_pos.ne',h.Y_pos.ne',h.w_pos.ne']
  ring

theorem position_bounds {s : Chain} {q t u : ℝ}
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hu : u∈Icc (ev t (a s)) (ev t (b s)))
    (h : RadicalBounds s q t u) :
    clearedPosition q t u∈Icc (ev t (positionLowerAt s)) (ev t (positionUpperAt s)) := by
  let B := boxes ht hu h
  let X := (((B.first.mul ((B.cosine.mul B.height).add (B.sine.mul B.r))).mul B.U).mul B.Y).mul
    B.w
  let Y := (((B.second.mul B.other).mul B.V).mul ((B.cosine.mul B.w).add (B.sine.mul B.v))).mul
    B.r
  have e2 : ev t (2:ℚ[X])=2 := by rw [ev]; exact map_ofNat _ 2
  have hlo : ev t (positionLowerAt s)=X.lo-Y.hi := by
    show _=B.first.lo*(B.cosine.lo*B.height.lo+B.sine.lo*B.r.lo)*B.U.lo*B.Y.lo*B.w.lo-
      B.second.hi*B.other.hi*B.V.hi*(B.cosine.hi*B.w.hi+B.sine.hi*B.v.hi)*B.r.hi
    rw [B.first_lo,B.cosine_lo,B.height_lo,B.sine_lo,B.r_lo,B.U_lo,B.Y_lo,B.w_lo,
      B.second_hi,B.other_hi,B.V_hi,B.cosine_hi,B.w_hi,B.sine_hi,B.v_hi,B.r_hi]
    simp only [positionLowerAt,ev_sub,ev_mul,ev_add,e2]
  have hhi : ev t (positionUpperAt s)=X.hi-Y.lo := by
    show _=B.first.hi*(B.cosine.hi*B.height.hi+B.sine.hi*B.r.hi)*B.U.hi*B.Y.hi*B.w.hi-
      B.second.lo*B.other.lo*B.V.lo*(B.cosine.lo*B.w.lo+B.sine.lo*B.v.lo)*B.r.lo
    rw [B.first_hi,B.cosine_hi,B.height_hi,B.sine_hi,B.r_hi,B.U_hi,B.Y_hi,B.w_hi,
      B.second_lo,B.other_lo,B.V_lo,B.cosine_lo,B.w_lo,B.sine_lo,B.v_lo,B.r_lo]
    simp only [positionUpperAt,ev_sub,ev_mul,ev_add,e2]
  rw [hlo,hhi]
  exact ⟨sub_le_sub X.mem.1 Y.mem.2,sub_le_sub X.mem.2 Y.mem.1⟩

end SquaresInCircles.Eight.CriticalESubstitution
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalEPosition
open Polynomial CriticalEPolynomials CriticalERadicals CriticalESubstitution
open WholeIntervalPolynomial Stationary.FiveCornerGeometry

theorem angle_mem {t : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25)) : t∈tiltInterval := by
  obtain ⟨hh,he⟩ := StationaryPrimitives.terminal_tangent ht
  rw [← he]
  exact StationaryPrimitives.arctan_mem_tiltInterval hh

theorem comparison_signs {q t : ℝ}
    (hq : q∈Icc (qLower:ℝ) (qUpper:ℝ)) (ht : t∈Icc (1/10:ℝ) (4/25)) :
    positionHalf q (Real.cos t) (Real.sin t) (ev t uMinus)<0 ∧
    0<positionHalf q (Real.cos t) (Real.sin t) (ev t uPlus) := by
  have hl : ev t uMinus∈Icc (ev t (a .lower)) (ev t (b .lower)) := ⟨le_rfl,le_rfl⟩
  have hu : ev t uPlus∈Icc (ev t (a .upper)) (ev t (b .upper)) := ⟨le_rfl,le_rfl⟩
  have hrl := actual_radicals .lower hq ht hl
  have hru := actual_radicals .upper hq ht hu
  have hqlt : q<4 := by norm_num [qUpper] at hq; linarith [hq.2]
  have hdl := hrl.smoothDomain ht (by rw [ev_minus]; linarith [ht.2]) hqlt
  have hdu := hru.smoothDomain ht (by rw [ev_plus]; linarith [ht.2]) hqlt
  have hJl := (position_bounds ht hl hrl).2
  have hJu := (position_bounds ht hu hru).1
  have hloc : t-1/10∈Icc ((0:ℚ):ℝ) (length:ℝ) := by
    rw [Rat.cast_zero]
    exact local_parameter ht
  have hpL := (interval_bounds (by norm_num [length]) position_identities.1 hloc).2
  have hpU := positive_on_interval (by norm_num [length]) position_identities.2
    position_reserves.2 hloc
  have hresL : (upperOn 64 0 length positionUpper:ℝ) < -1/50 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr position_reserves.1
    push_cast at h
    linarith
  have hneg : clearedPosition q t (ev t uMinus)<0 := by
    change ev t positionUpper≤(upperOn 64 0 length positionUpper:ℝ) at hpL
    change clearedPosition q t (ev t uMinus)≤ev t positionUpper at hJl
    linarith
  have hpos : 0<clearedPosition q t (ev t uPlus) := by
    have h : (1/25:ℝ)<ev t positionLower := by
      have h' := hpU
      push_cast at h'
      exact h'
    change ev t positionLower≤clearedPosition q t (ev t uPlus) at hJu
    linarith
  have hdenL := mul_pos (mul_pos (mul_pos hdl.r_pos hdl.U_pos) hdl.Y_pos) hdl.w_pos
  have hdenU := mul_pos (mul_pos (mul_pos hdu.r_pos hdu.U_pos) hdu.Y_pos) hdu.w_pos
  rw [clearedPosition_identity hdl] at hneg
  rw [clearedPosition_identity hdu] at hpos
  constructor <;> nlinarith

theorem minimizingPosition_strip {q t : ℝ}
    (hq : q∈Icc (qLower:ℝ) (qUpper:ℝ)) (ht : t∈Icc (1/10:ℝ) (4/25)) :
    499/500-(127/200)*t< minimizingPosition q t ∧
    minimizingPosition q t<501/500-(16/25)*t := by
  have hql : (79/40:ℝ)^2≤q := by norm_num [qLower] at hq; nlinarith [hq.1]
  have hqu : q≤9789/2500 := by norm_num [qUpper] at hq; linarith [hq.2]
  obtain ⟨hc,hs,_⟩ := tiltInterval_bounds (angle_mem ht)
  have hm := StationaryPrimitives.position_gradient_strictMono hql hqu hc hs.le
    (Real.cos_sq_add_sin_sq t)
  have hu := windowMinimizer_mem q (Real.cos t) (Real.sin t)
  change minimizingPosition q t∈positionWindow at hu
  have hz := minimizingPosition_root hql hqu (angle_mem ht)
  change 2*positionHalf q (Real.cos t) (Real.sin t) (minimizingPosition q t)=0 at hz
  have hL : ev t uMinus∈positionWindow := by
    simp only [ev_minus,positionWindow]
    constructor <;> linarith [ht.1,ht.2]
  have hU : ev t uPlus∈positionWindow := by
    simp only [ev_plus,positionWindow]
    constructor <;> linarith [ht.1,ht.2]
  have hsign := comparison_signs hq ht
  have hl : ev t uMinus< minimizingPosition q t := by
    by_contra! hbad
    have he := hm.monotoneOn hu hL hbad
    linarith [hsign.1]
  have hh : minimizingPosition q t<ev t uPlus := by
    by_contra! hbad
    have he := hm.monotoneOn hU hu hbad
    linarith [hsign.2]
  rw [ev_minus] at hl
  rw [ev_plus] at hh
  exact ⟨hl,hh⟩

end SquaresInCircles.Eight.CriticalEPosition
end
end
end
