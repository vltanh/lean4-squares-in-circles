module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Data.Int.Star
public import SquaresInCircles.Eight.Arithmetic.FastPolynomials
public import SquaresInCircles.Eight.Owners.Positive.ScalarPolynomials
public import SquaresInCircles.Eight.Owners.Sole.ECoefficients
public import SquaresInCircles.Eight.Owners.WholeIntervalBernstein

/-!
# Eight squares: explicit whole-interval polynomials for the sole-E endpoints

These are the eighteen sole-EH scalars and the six
additional sole-DE scalars in the two hand proofs. The masses are built
by three rational Newton steps at the left endpoint, followed by cubic
truncation. Every identity and reserve is a kernel arithmetic proof
which has not been run. No numerical samples or external replay occur.

The polynomial bounds are kept separate from their trigonometric and
radical transfer. Their presence alone is not a geometric exclusion.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleScalarPolynomials
open Polynomial WholeIntervalPolynomial SoleECoefficients

inductive ScalarCase where
  | lowE | lowG
  | middleE (i : Fin 4) | middleG (i : Fin 4)
  | highE (i : Fin 4) | highG (i : Fin 4)
  | lowDE | middleDE (i : Fin 4) | highDEH
  deriving DecidableEq

instance : Fintype ScalarCase where
  elems := {.lowE, .lowG, .lowDE, .highDEH} ∪
    Finset.univ.image ScalarCase.middleE ∪
    Finset.univ.image ScalarCase.middleG ∪
    Finset.univ.image ScalarCase.highE ∪
    Finset.univ.image ScalarCase.highG ∪
    Finset.univ.image ScalarCase.middleDE
  complete x := by cases x <;> simp

def band : ScalarCase → Band
  | .lowE | .lowG | .lowDE => .low
  | .middleE _ | .middleG _ | .middleDE _ => .middle
  | _ => .high

def origin : Band → ℚ
  | .low => 0 | .middle => 1/5 | .high => 7/20

def length : Band → ℚ
  | .low => 1/5 | .middle => 3/20 | .high => 7/20

def negativeIndex : ScalarCase → Fin 4
  | .lowE | .lowG | .lowDE => 2
  | .middleE i | .middleG i | .highE i | .highG i | .middleDE i => i
  | .highDEH => 0

def atG : ScalarCase → Bool
  | .lowG | .middleG _ | .highG _ | .highDEH => true
  | _ => false

def isDE : ScalarCase → Bool
  | .lowDE | .middleDE _ => true
  | _ => false

def radiusUpper : ℚ := 989385433/500000000
def axisUpper : ℚ := 1414558471/1000000000
def margin : ℚ := 1/100000000

def parameter (b : Band) : ℚ[X] := C (origin b)+X
def sine (b : Band) : ℚ[X] := PositiveScalarPolynomials.sine.comp (parameter b)
def cosine (b : Band) : ℚ[X] := PositiveScalarPolynomials.cosine.comp (parameter b)
def halfSine (b : Band) : ℚ[X] :=
  PositiveScalarPolynomials.sine.comp (C (1/2)*parameter b)

def k : Band → ℚ[X]
  | .low => C (17253/20000)+C (11/20)*X+C (3/10)*X^2
  | .middle => C (983/1000)+C (1/10)*X-C (3/10)*X^2
  | .high => C (1017/1000)-C (1/50)*parameter .high

def c : Band → ℚ[X]
  | .low => k .low+C (3/10)*X
  | .middle => C (209/200)+C (13/20)*X-C (3/2)*X^2
  | .high => C (113/100)

def ell : Band → ℚ[X]
  | .low => C (50521/100000)+C (823/1000)*X+C (7/10)*X^2
  | .middle => C (349/500)+C (9/10)*X-X^2
  | .high => C (7/10)+C (9/25)*parameter .high

def g : Band → ℚ[X]
  | .low => C (8/25)
  | .middle => C (31/100)
  | .high => C (27/100)+C (2/25)*parameter .high

def eta : Band → ℚ[X]
  | .low => C (131/500)+C (267/1000)*X+C (1/10)*X^2
  | .middle => C (319/1000)+C (1/5)*X
  | .high => C (7/20)

def n (b : Band) : ℚ[X] := k b*(cosine b+g b*sine b)
def p (b : Band) : ℚ[X] := if b=.high then 1 else cosine b+eta b*sine b
def r (b : Band) : ℚ[X] := cosine b+C (7/10)*sine b

def first (s : ScalarCase) : Fin 4 → ℚ[X] :=
  let b := band s
  if atG s then ![1,k b,ell b,1]
  else if isDE s then ![r b,k b,ell b,1]
  else ![1,k b,ell b,p b]

def second (s : ScalarCase) : Fin 4 → ℚ[X] :=
  let b := band s
  ![if atG s then n b else k b,ell b,c b,c b]

def nu (s : ScalarCase) : ℚ[X] :=
  let b := band s
  if s=.highDEH then C (53/50)
  else ![if atG s then n b else if isDE s then r b else k b,ell b,c b,c b]
    (negativeIndex s)

def outside (s : ScalarCase) : ℚ[X] :=
  let b := band s
  (if atG s then
      3+2*ell b+3*c b+k b*(1+2*cosine b+(1+2*g b)*sine b)
    else if isDE s then
      3*k b+2*ell b+3*c b+1+C (1/2)*cosine b+
        C (1/2-axisUpper)*sine b+C (3/2)*r b
    else if b=.high then
      3+sine b-C (2*radiusUpper)*halfSine b+3*k b+2*ell b+3*c b
    else
      3*k b+2*ell b+3*c b+1+2*cosine b+(1+2*eta b)*sine b)+
    nu s*(cosine b-1)

def squaredNorm (s : ScalarCase) (i : Fin 4) : ℚ[X] :=
  (first s i)^2+(second s i)^2-
    (if i=negativeIndex s then 2*first s i*second s i*sine (band s) else 0)

def rowSquare (s : ScalarCase) (i : Fin 5) : ℚ[X] :=
  if hi : i.val<4 then squaredNorm s ⟨i.val,hi⟩
  else if atG s then 1+(g (band s))^2
  else if isDE s=true ∨ band s=.high then 1 else 1+(eta (band s))^2

def rowWeight (s : ScalarCase) (i : Fin 5) : ℚ[X] :=
  if i.val<4 then 1 else if atG s then k (band s)*sine (band s)
  else if isDE s=true ∨ band s=.high then 0 else sine (band s)

def truncateThree (v : ℚ[X]) : ℚ[X] :=
  C (v.coeff 0)+C (v.coeff 1)*X+C (v.coeff 2)*X^2+C (v.coeff 3)*X^3

def newton (v : ℚ) : ℕ → ℚ
  | 0 => 1
  | j+1 => (newton v j+v/newton v j)/2

def newtonMass (v : ℚ[X]) : ℚ[X] :=
  let v0 := v.coeff 0
  let w := C (1/v0)*(truncateThree v-C v0)
  truncateThree (C (newton v0 3)*(1+C (1/2)*w-C (1/8)*w^2+C (1/16)*w^3))

def massAt (s : ScalarCase) (i : Fin 5) : ℚ[X] :=
  if i.val=4 ∧ (isDE s=true ∨ band s=.high) ∧ atG s=false then 1
  else newtonMass (rowSquare s i)

def mass (s : ScalarCase) : ℚ[X] := ∏i : Fin 5,massAt s i
def massExcept (s : ScalarCase) (i : Fin 5) : ℚ[X] :=
  ∏j : Fin 5,if j=i then 1 else massAt s j

def certificate (s : ScalarCase) : ℚ[X] :=
  2*(outside s-C margin)*mass s-C radiusUpper*
    ∑i : Fin 5,rowWeight s i*(rowSquare s i+(massAt s i)^2)*massExcept s i

def degree : ScalarCase → ℕ
  | .lowDE => 41
  | _ => 46

theorem length_pos (b : Band) : 0<length b := by cases b <;> norm_num [length]

theorem local_parameter {b : Band} {t : ℝ} (ht : t∈domain b) :
    t-(origin b:ℝ)∈Set.Icc 0 (length b:ℝ) := by
  cases b <;> norm_num [domain,origin,length,frameCap] at ht ⊢ <;>
    constructor <;> linarith [ht.1,ht.2]

/-! ### Kernel certificates

Each polynomial of this file is mirrored by a scaled integer coefficient list
(`PolynomialCertificates`, `FastPolynomials`). The band polynomials, the rows and the
masses are divided by the gcd of their entries after every composite step, which keeps
the integers short. The products of the masses, the certificate and the centered lists
are not: their entries have thousands of bits, and a gcd of such numbers costs the
kernels outside Lean far more than the products it would shorten. The Newton steps of
`newtonMass` are carried out on integer numerators and denominators. -/

section Certificates
open WholeIntervalPolynomial.Certificate

/-! #### Coefficients of a represented polynomial -/

private theorem rep_coeff_mul {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) (j : ℕ) :
    (a.s:ℚ)*p.coeff j=(a.l.getD j 0:ℚ) := by
  have h := congrArg (fun q : ℚ[X] => q.coeff j) ha
  simp only [coeff_toPoly,coeff_C_mul] at h
  exact h.symm

/-- `truncateThree`: the first four coefficients. -/
private def trunc4 (a : Scaled) : Scaled :=
  ⟨[a.l.getD 0 0,a.l.getD 1 0,a.l.getD 2 0,a.l.getD 3 0],a.s⟩

private theorem rep_trunc4 {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) :
    (trunc4 a).Rep (truncateThree p) := by
  unfold Scaled.Rep trunc4 truncateThree
  simp only [toPoly]
  rw [← rep_coeff_mul ha 0,← rep_coeff_mul ha 1,← rep_coeff_mul ha 2,← rep_coeff_mul ha 3]
  simp only [C_mul,mul_zero,add_zero]
  ring

/-- `C (p.coeff 0)`. -/
private def const0 (a : Scaled) : Scaled := ⟨[a.l.getD 0 0],a.s⟩

private theorem rep_const0 {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) :
    (const0 a).Rep (C (p.coeff 0)) := by
  unfold Scaled.Rep const0
  simp only [toPoly,mul_zero,add_zero]
  rw [← rep_coeff_mul ha 0,C_mul]

/-- `C (1/p.coeff 0)`, when the constant coefficient is positive. -/
private def inv0 (a : Scaled) : Scaled := ⟨[(a.s:ℤ)],(a.l.getD 0 0).toNat⟩

private theorem rep_inv0 {a : Scaled} {p : ℚ[X]} (ha : a.Rep p)
    (hl : 0<a.l.getD 0 0) (hs : a.s≠0) : (inv0 a).Rep (C (1/p.coeff 0)) := by
  unfold Scaled.Rep inv0
  have h := rep_coeff_mul ha 0
  have hs' : (a.s:ℚ)≠0 := by exact_mod_cast hs
  have hl' : ((a.l.getD 0 0).toNat:ℚ)=(a.l.getD 0 0:ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hl.le
  have hp : p.coeff 0=(a.l.getD 0 0:ℚ)/a.s := by field_simp; linarith
  have hl0 : (a.l.getD 0 0:ℚ)≠0 := by exact_mod_cast hl.ne'
  simp only [toPoly,mul_zero,add_zero,Int.cast_natCast]
  rw [← C_mul,hl',hp]
  congr 1
  field_simp

/-- Integer numerator and denominator of the Newton iterates for `l0/s`. -/
private def newtonPair (l0 : ℤ) (s : ℕ) : ℕ → ℤ × ℕ
  | 0 => (1,1)
  | j+1 =>
    let x := newtonPair l0 s j
    (x.1^2*s+l0*x.2^2,2*x.1.toNat*x.2*s)

private theorem newtonPair_spec {l0 : ℤ} {s : ℕ} (hl : 0<l0) (hs : 0<s) :
    ∀ j,0<(newtonPair l0 s j).1 ∧ 0<(newtonPair l0 s j).2 ∧
      newton ((l0:ℚ)/s) j=((newtonPair l0 s j).1:ℚ)/(newtonPair l0 s j).2
  | 0 => by simp [newtonPair,newton]
  | j+1 => by
    obtain ⟨h1,h2,h3⟩ := newtonPair_spec hl hs j
    simp only [newtonPair,newton]
    generalize newtonPair l0 s j=x at h1 h2 h3 ⊢
    obtain ⟨P,Q⟩ := x
    simp only at h1 h2 h3 ⊢
    have hP : ((P.toNat:ℕ):ℚ)=(P:ℚ) := by exact_mod_cast Int.toNat_of_nonneg h1.le
    have hPn : 0<P.toNat := by omega
    have hQz : (0:ℤ)<(Q:ℤ) := by exact_mod_cast h2
    refine ⟨add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg _) (Int.natCast_nonneg _))
      (mul_pos hl (pow_pos hQz 2)),Nat.mul_pos (Nat.mul_pos (Nat.mul_pos two_pos hPn) h2) hs,?_⟩
    rw [h3]
    push_cast
    rw [hP]
    have hP0 : (P:ℚ)≠0 := by exact_mod_cast h1.ne'
    have hQ0 : (Q:ℚ)≠0 := by exact_mod_cast h2.ne'
    have hs0 : (s:ℚ)≠0 := by exact_mod_cast hs.ne'
    field_simp

/-- `C (newton (p.coeff 0) 3)`. -/
private def newton3 (a : Scaled) : Scaled :=
  ⟨[(newtonPair (a.l.getD 0 0) a.s 3).1],(newtonPair (a.l.getD 0 0) a.s 3).2⟩

private theorem rep_newton3 {a : Scaled} {p : ℚ[X]} (ha : a.Rep p)
    (hl : 0<a.l.getD 0 0) (hs : a.s≠0) : (newton3 a).Rep (C (newton (p.coeff 0) 3)) := by
  unfold Scaled.Rep newton3
  have h := rep_coeff_mul ha 0
  have hs' : (a.s:ℚ)≠0 := by exact_mod_cast hs
  have hp : p.coeff 0=(a.l.getD 0 0:ℚ)/a.s := by field_simp; linarith
  obtain ⟨_,h2,h3⟩ := newtonPair_spec hl (Nat.pos_of_ne_zero hs) 3
  have hQ : ((newtonPair (a.l.getD 0 0) a.s 3).2:ℚ)≠0 := by exact_mod_cast h2.ne'
  simp only [toPoly,mul_zero,add_zero]
  rw [hp,h3,← C_mul]
  congr 1
  field_simp

private def newtonMassS (a : Scaled) : Scaled :=
  let w := Scaled.normF ((inv0 a).mulF ((trunc4 a).subF (const0 a)))
  Scaled.normF (trunc4 ((newton3 a).mulF
    ((((Scaled.ofNat 1).addF ((Scaled.const (1/2)).mulF w)).subF
    ((Scaled.const (1/8)).mulF (w.powF 2))).addF ((Scaled.const (1/16)).mulF (w.powF 3)))))

private theorem rep_newtonMass {a : Scaled} {p : ℚ[X]} (ha : a.Rep p)
    (hl : 0<a.l.getD 0 0) (hs : a.s≠0) : (newtonMassS a).Rep (newtonMass p) := by
  have hw := Scaled.Rep.normF ((rep_inv0 ha hl hs).mulF ((rep_trunc4 ha).subF (rep_const0 ha)))
  exact Scaled.Rep.normF (rep_trunc4 ((rep_newton3 ha hl hs).mulF ((((Scaled.rep_one).addF
    ((Scaled.rep_const _).mulF hw)).subF ((Scaled.rep_const _).mulF (hw.powF 2))).addF
    ((Scaled.rep_const _).mulF (hw.powF 3)))))

end Certificates

section Certificates2
open WholeIntervalPolynomial.Certificate

/-! #### The band polynomials -/

private def sineB : Scaled :=
  Scaled.normF ((((((((Scaled.var).subF ((Scaled.const (1/6)).mulF ((Scaled.var).powF 3))).addF
    ((Scaled.const (1/120)).mulF ((Scaled.var).powF 5))).subF
    ((Scaled.const (1/5040)).mulF ((Scaled.var).powF 7))).addF
    ((Scaled.const (1/362880)).mulF ((Scaled.var).powF 9))).subF
    ((Scaled.const (1/39916800)).mulF ((Scaled.var).powF 11))).addF
    ((Scaled.const (1/6227020800)).mulF ((Scaled.var).powF 13))).subF
    ((Scaled.const (1/1307674368000)).mulF ((Scaled.var).powF 15)))

private theorem rep_sineB : sineB.Rep PositiveScalarPolynomials.sine :=
  Scaled.Rep.normF ((((((((Scaled.rep_var).subF
    ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 3))).addF
    ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 5))).subF
    ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 7))).addF
    ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 9))).subF
    ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 11))).addF
    ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 13))).subF
    ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 15)))

private def cosineB : Scaled :=
  Scaled.normF (((((((((Scaled.ofNat 1).subF ((Scaled.const (1/2)).mulF ((Scaled.var).powF 2))).addF
    ((Scaled.const (1/24)).mulF ((Scaled.var).powF 4))).subF
    ((Scaled.const (1/720)).mulF ((Scaled.var).powF 6))).addF
    ((Scaled.const (1/40320)).mulF ((Scaled.var).powF 8))).subF
    ((Scaled.const (1/3628800)).mulF ((Scaled.var).powF 10))).addF
    ((Scaled.const (1/479001600)).mulF ((Scaled.var).powF 12))).subF
    ((Scaled.const (1/87178291200)).mulF ((Scaled.var).powF 14))).addF
    ((Scaled.const (1/20922789888000)).mulF ((Scaled.var).powF 16)))

private theorem rep_cosineB : cosineB.Rep PositiveScalarPolynomials.cosine :=
  Scaled.Rep.normF (((((((((Scaled.rep_one).subF
    ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 2))).addF
    ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 4))).subF
    ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 6))).addF
    ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 8))).subF
    ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 10))).addF
    ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 12))).subF
    ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 14))).addF
    ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 16)))

private theorem comp_parameter (b : Band) (p : ℚ[X]) :
    p.comp (parameter b)=centered (origin b-1) (origin b+1) p := by
  have e1 : (origin b-1+(origin b+1))/2=origin b := by ring
  have e2 : (origin b+1-(origin b-1))/2=(1:ℚ) := by ring
  rw [centered,affine,e1,e2,map_one,one_mul,parameter]

private theorem comp_half (b : Band) (p : ℚ[X]) :
    p.comp (C (1/2)*parameter b)=centered (origin b/2-1/2) (origin b/2+1/2) p := by
  have e1 : (origin b/2-1/2+(origin b/2+1/2))/2=1/2*origin b := by ring
  have e2 : (origin b/2+1/2-(origin b/2-1/2))/2=(1/2:ℚ) := by ring
  rw [centered,affine,e1,e2,parameter,mul_add,← C_mul]

private def sinB : Band → Scaled
  | .low => Scaled.normF (sineB.centerF 1 1 0 1)
  | .middle => Scaled.normF (sineB.centerF 1 5 1 5)
  | .high => Scaled.normF (sineB.centerF 1 20 7 20)

private theorem rep_sinB (b : Band) : (sinB b).Rep (sine b) := by
  rw [sine,comp_parameter]
  cases b <;> exact Scaled.Rep.normF (rep_sineB.centeredF _ _ _ _ (by norm_num)
    (by norm_num [origin]) (by norm_num [origin]))

private def cosB : Band → Scaled
  | .low => Scaled.normF (cosineB.centerF 1 1 0 1)
  | .middle => Scaled.normF (cosineB.centerF 1 5 1 5)
  | .high => Scaled.normF (cosineB.centerF 1 20 7 20)

private theorem rep_cosB (b : Band) : (cosB b).Rep (cosine b) := by
  rw [cosine,comp_parameter]
  cases b <;> exact Scaled.Rep.normF (rep_cosineB.centeredF _ _ _ _ (by norm_num)
    (by norm_num [origin]) (by norm_num [origin]))

private def halfSinB : Band → Scaled
  | .low => Scaled.normF (sineB.centerF 1 2 0 1)
  | .middle => Scaled.normF (sineB.centerF 1 10 1 5)
  | .high => Scaled.normF (sineB.centerF 1 40 7 20)

private theorem rep_halfSinB (b : Band) : (halfSinB b).Rep (halfSine b) := by
  rw [halfSine,comp_half]
  cases b <;> exact Scaled.Rep.normF (rep_sineB.centeredF _ _ _ _ (by norm_num)
    (by norm_num [origin]) (by norm_num [origin]))

private def parHighS : Scaled := (Scaled.const (7/20)).addF (Scaled.var)

private theorem rep_par : parHighS.Rep (parameter .high) :=
  (Scaled.rep_const _).addF (Scaled.rep_var)

private def kS : Band → Scaled
  | .low => ((Scaled.const (17253/20000)).addF ((Scaled.const (11/20)).mulF (Scaled.var))).addF
      ((Scaled.const (3/10)).mulF ((Scaled.var).powF 2))
  | .middle => ((Scaled.const (983/1000)).addF ((Scaled.const (1/10)).mulF (Scaled.var))).subF
      ((Scaled.const (3/10)).mulF ((Scaled.var).powF 2))
  | .high => (Scaled.const (1017/1000)).subF ((Scaled.const (1/50)).mulF (parHighS))

private theorem rep_k : ∀ b,(kS b).Rep (k b)
  | .low => ((Scaled.rep_const _).addF ((Scaled.rep_const _).mulF (Scaled.rep_var))).addF
      ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 2))
  | .middle => ((Scaled.rep_const _).addF ((Scaled.rep_const _).mulF (Scaled.rep_var))).subF
      ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 2))
  | .high => (Scaled.rep_const _).subF ((Scaled.rep_const _).mulF (rep_par))

private def cS : Band → Scaled
  | .low => (kS .low).addF ((Scaled.const (3/10)).mulF (Scaled.var))
  | .middle => ((Scaled.const (209/200)).addF ((Scaled.const (13/20)).mulF (Scaled.var))).subF
      ((Scaled.const (3/2)).mulF ((Scaled.var).powF 2))
  | .high => Scaled.const (113/100)

private theorem rep_c : ∀ b,(cS b).Rep (c b)
  | .low => (rep_k .low).addF ((Scaled.rep_const _).mulF (Scaled.rep_var))
  | .middle => ((Scaled.rep_const _).addF ((Scaled.rep_const _).mulF (Scaled.rep_var))).subF
      ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 2))
  | .high => Scaled.rep_const _

private def ellS : Band → Scaled
  | .low => ((Scaled.const (50521/100000)).addF ((Scaled.const (823/1000)).mulF (Scaled.var))).addF
      ((Scaled.const (7/10)).mulF ((Scaled.var).powF 2))
  | .middle => ((Scaled.const (349/500)).addF ((Scaled.const (9/10)).mulF (Scaled.var))).subF
      ((Scaled.var).powF 2)
  | .high => (Scaled.const (7/10)).addF ((Scaled.const (9/25)).mulF (parHighS))

private theorem rep_ell : ∀ b,(ellS b).Rep (ell b)
  | .low => ((Scaled.rep_const _).addF ((Scaled.rep_const _).mulF (Scaled.rep_var))).addF
      ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 2))
  | .middle => ((Scaled.rep_const _).addF ((Scaled.rep_const _).mulF (Scaled.rep_var))).subF
      ((Scaled.rep_var).powF 2)
  | .high => (Scaled.rep_const _).addF ((Scaled.rep_const _).mulF (rep_par))

private def gS : Band → Scaled
  | .low => Scaled.const (8/25)
  | .middle => Scaled.const (31/100)
  | .high => (Scaled.const (27/100)).addF ((Scaled.const (2/25)).mulF (parHighS))

private theorem rep_g : ∀ b,(gS b).Rep (g b)
  | .low => Scaled.rep_const _
  | .middle => Scaled.rep_const _
  | .high => (Scaled.rep_const _).addF ((Scaled.rep_const _).mulF (rep_par))

private def etaS : Band → Scaled
  | .low => ((Scaled.const (131/500)).addF ((Scaled.const (267/1000)).mulF (Scaled.var))).addF
      ((Scaled.const (1/10)).mulF ((Scaled.var).powF 2))
  | .middle => (Scaled.const (319/1000)).addF ((Scaled.const (1/5)).mulF (Scaled.var))
  | .high => Scaled.const (7/20)

private theorem rep_eta : ∀ b,(etaS b).Rep (eta b)
  | .low => ((Scaled.rep_const _).addF ((Scaled.rep_const _).mulF (Scaled.rep_var))).addF
      ((Scaled.rep_const _).mulF ((Scaled.rep_var).powF 2))
  | .middle => (Scaled.rep_const _).addF ((Scaled.rep_const _).mulF (Scaled.rep_var))
  | .high => Scaled.rep_const _

private def nS (b : Band) : Scaled :=
  Scaled.normF ((kS b).mulF ((cosB b).addF ((gS b).mulF (sinB b))))

private theorem rep_n (b : Band) : (nS b).Rep (n b) :=
  Scaled.Rep.normF ((rep_k b).mulF ((rep_cosB b).addF ((rep_g b).mulF (rep_sinB b))))

private def pS (b : Band) : Scaled :=
  if b=.high then Scaled.ofNat 1 else Scaled.normF ((cosB b).addF ((etaS b).mulF (sinB b)))

private theorem rep_p (b : Band) : (pS b).Rep (p b) := by
  unfold pS p
  split_ifs
  · exact Scaled.rep_one
  · exact Scaled.Rep.normF ((rep_cosB b).addF ((rep_eta b).mulF (rep_sinB b)))

private def rS (b : Band) : Scaled :=
  Scaled.normF ((cosB b).addF ((Scaled.const (7/10)).mulF (sinB b)))

private theorem rep_r (b : Band) : (rS b).Rep (r b) :=
  Scaled.Rep.normF ((rep_cosB b).addF ((Scaled.rep_const _).mulF (rep_sinB b)))

/-! #### The scalar cases -/

private def firstS (s : ScalarCase) : Fin 4 → Scaled :=
  if atG s then ![Scaled.ofNat 1,kS (band s),ellS (band s),Scaled.ofNat 1]
  else if isDE s then ![rS (band s),kS (band s),ellS (band s),Scaled.ofNat 1]
  else ![Scaled.ofNat 1,kS (band s),ellS (band s),pS (band s)]

private theorem rep_ite {c : Prop} [Decidable c] {a b : Scaled} {p q : ℚ[X]}
    (ha : a.Rep p) (hb : b.Rep q) : (if c then a else b).Rep (if c then p else q) := by
  split_ifs
  · exact ha
  · exact hb

private theorem rep_vec4 {a0 a1 a2 a3 : Scaled} {p0 p1 p2 p3 : ℚ[X]} (h0 : a0.Rep p0)
    (h1 : a1.Rep p1) (h2 : a2.Rep p2) (h3 : a3.Rep p3) (j : Fin 4) :
    (![a0,a1,a2,a3] j).Rep (![p0,p1,p2,p3] j) := by
  fin_cases j
  exacts [h0,h1,h2,h3]

private theorem rep_first (s : ScalarCase) (i : Fin 4) : (firstS s i).Rep (first s i) := by
  have h := rep_ite (c := atG s=true)
    (rep_vec4 Scaled.rep_one (rep_k (band s)) (rep_ell (band s)) Scaled.rep_one i)
    (rep_ite (c := isDE s=true)
      (rep_vec4 (rep_r (band s)) (rep_k (band s)) (rep_ell (band s)) Scaled.rep_one i)
      (rep_vec4 Scaled.rep_one (rep_k (band s)) (rep_ell (band s)) (rep_p (band s)) i))
  simp only [firstS,first]
  split_ifs at h ⊢ <;> exact h

private def secondS (s : ScalarCase) : Fin 4 → Scaled :=
  ![if atG s then nS (band s) else kS (band s),ellS (band s),cS (band s),cS (band s)]

private theorem rep_second (s : ScalarCase) (i : Fin 4) : (secondS s i).Rep (second s i) :=
  rep_vec4 (rep_ite (rep_n (band s)) (rep_k (band s))) (rep_ell (band s)) (rep_c (band s))
    (rep_c (band s)) i

private def nuS (s : ScalarCase) : Scaled :=
  if s=.highDEH then Scaled.const (53/50)
  else ![if atG s then nS (band s) else if isDE s then rS (band s) else kS (band s),
    ellS (band s),cS (band s),cS (band s)] (negativeIndex s)

private theorem rep_nu (s : ScalarCase) : (nuS s).Rep (nu s) :=
  rep_ite (Scaled.rep_const _) (rep_vec4 (rep_ite (rep_n (band s))
    (rep_ite (rep_r (band s)) (rep_k (band s)))) (rep_ell (band s)) (rep_c (band s))
    (rep_c (band s)) (negativeIndex s))

private def outsideS (s : ScalarCase) : Scaled :=
  let b := band s
  Scaled.normF (((if atG s then
      (((Scaled.ofNat 3).addF ((Scaled.ofNat 2).mulF (ellS b))).addF ((Scaled.ofNat 3).mulF (cS b))).addF
        ((kS b).mulF (((Scaled.ofNat 1).addF ((Scaled.ofNat 2).mulF (cosB b))).addF
          (((Scaled.ofNat 1).addF ((Scaled.ofNat 2).mulF (gS b))).mulF (sinB b))))
    else if isDE s then
      (((((((Scaled.ofNat 3).mulF (kS b)).addF ((Scaled.ofNat 2).mulF (ellS b))).addF
        ((Scaled.ofNat 3).mulF (cS b))).addF (Scaled.ofNat 1)).addF
        ((Scaled.const (1/2)).mulF (cosB b))).addF
        ((Scaled.const (1/2-axisUpper)).mulF (sinB b))).addF ((Scaled.const (3/2)).mulF (rS b))
    else if b=.high then
      (((((Scaled.ofNat 3).addF (sinB b)).subF
        ((Scaled.const (2*radiusUpper)).mulF (halfSinB b))).addF ((Scaled.ofNat 3).mulF (kS b))).addF
        ((Scaled.ofNat 2).mulF (ellS b))).addF ((Scaled.ofNat 3).mulF (cS b))
    else
      ((((((Scaled.ofNat 3).mulF (kS b)).addF ((Scaled.ofNat 2).mulF (ellS b))).addF
        ((Scaled.ofNat 3).mulF (cS b))).addF (Scaled.ofNat 1)).addF
        ((Scaled.ofNat 2).mulF (cosB b))).addF
        (((Scaled.ofNat 1).addF ((Scaled.ofNat 2).mulF (etaS b))).mulF (sinB b)))).addF
    ((nuS s).mulF ((cosB b).subF (Scaled.ofNat 1))))

private theorem rep_outside (s : ScalarCase) : (outsideS s).Rep (outside s) := by
  simp only [outsideS,outside]
  apply Scaled.Rep.normF
  have hnu := (rep_nu s).mulF ((rep_cosB (band s)).subF (Scaled.rep_one))
  split_ifs
  · exact ((((Scaled.rep_ofNat 3).addF ((Scaled.rep_ofNat 2).mulF (rep_ell _))).addF
      ((Scaled.rep_ofNat 3).mulF (rep_c _))).addF ((rep_k _).mulF (((Scaled.rep_one).addF
      ((Scaled.rep_ofNat 2).mulF (rep_cosB _))).addF (((Scaled.rep_one).addF
      ((Scaled.rep_ofNat 2).mulF (rep_g _))).mulF (rep_sinB _))))).addF hnu
  · exact ((((((((Scaled.rep_ofNat 3).mulF (rep_k _)).addF ((Scaled.rep_ofNat 2).mulF (rep_ell _))).addF
      ((Scaled.rep_ofNat 3).mulF (rep_c _))).addF (Scaled.rep_one)).addF
      ((Scaled.rep_const _).mulF (rep_cosB _))).addF ((Scaled.rep_const _).mulF (rep_sinB _))).addF
      ((Scaled.rep_const _).mulF (rep_r _))).addF hnu
  · exact ((((((Scaled.rep_ofNat 3).addF (rep_sinB _)).subF
      ((Scaled.rep_const _).mulF (rep_halfSinB _))).addF ((Scaled.rep_ofNat 3).mulF (rep_k _))).addF
      ((Scaled.rep_ofNat 2).mulF (rep_ell _))).addF ((Scaled.rep_ofNat 3).mulF (rep_c _))).addF hnu
  · exact (((((((Scaled.rep_ofNat 3).mulF (rep_k _)).addF ((Scaled.rep_ofNat 2).mulF (rep_ell _))).addF
      ((Scaled.rep_ofNat 3).mulF (rep_c _))).addF (Scaled.rep_one)).addF
      ((Scaled.rep_ofNat 2).mulF (rep_cosB _))).addF (((Scaled.rep_one).addF
      ((Scaled.rep_ofNat 2).mulF (rep_eta _))).mulF (rep_sinB _))).addF hnu

private def squaredNormS (s : ScalarCase) (i : Fin 4) : Scaled :=
  (((firstS s i).powF 2).addF ((secondS s i).powF 2)).subF
    (if i=negativeIndex s then
      (((Scaled.ofNat 2).mulF (firstS s i)).mulF (secondS s i)).mulF (sinB (band s))
    else ⟨[],1⟩)

private theorem rep_squaredNorm (s : ScalarCase) (i : Fin 4) :
    (squaredNormS s i).Rep (squaredNorm s i) := by
  simp only [squaredNormS,squaredNorm]
  split_ifs
  · exact (((rep_first s i).powF 2).addF ((rep_second s i).powF 2)).subF
      ((((Scaled.rep_ofNat 2).mulF (rep_first s i)).mulF (rep_second s i)).mulF (rep_sinB _))
  · exact (((rep_first s i).powF 2).addF ((rep_second s i).powF 2)).subF Scaled.rep_zero

private def rowSquareS (s : ScalarCase) (i : Fin 5) : Scaled :=
  Scaled.normF (if hi : i.val<4 then squaredNormS s ⟨i.val,hi⟩
    else if atG s then (Scaled.ofNat 1).addF ((gS (band s)).powF 2)
    else if isDE s=true ∨ band s=.high then Scaled.ofNat 1
    else (Scaled.ofNat 1).addF ((etaS (band s)).powF 2))

private theorem rep_rowSquare (s : ScalarCase) (i : Fin 5) :
    (rowSquareS s i).Rep (rowSquare s i) := by
  simp only [rowSquareS,rowSquare]
  apply Scaled.Rep.normF
  split_ifs
  · exact rep_squaredNorm s _
  · exact (Scaled.rep_one).addF ((rep_g _).powF 2)
  · exact Scaled.rep_one
  · exact (Scaled.rep_one).addF ((rep_eta _).powF 2)

private def rowWeightS (s : ScalarCase) (i : Fin 5) : Scaled :=
  if i.val<4 then Scaled.ofNat 1 else if atG s then (kS (band s)).mulF (sinB (band s))
  else if isDE s=true ∨ band s=.high then ⟨[],1⟩ else sinB (band s)

private theorem rep_rowWeight (s : ScalarCase) (i : Fin 5) :
    (rowWeightS s i).Rep (rowWeight s i) := by
  simp only [rowWeightS,rowWeight]
  split_ifs
  · exact Scaled.rep_one
  · exact (rep_k _).mulF (rep_sinB _)
  · exact Scaled.rep_zero
  · exact rep_sinB _

/-- The rows have positive constant terms and nonzero scales. -/
private def RowsOk (s : ScalarCase) : Prop :=
  ∀ i : Fin 5,0<(rowSquareS s i).l.getD 0 0 ∧ (rowSquareS s i).s≠0

private def massAtS (s : ScalarCase) (i : Fin 5) : Scaled :=
  if i.val=4 ∧ (isDE s=true ∨ band s=.high) ∧ atG s=false then Scaled.ofNat 1
  else newtonMassS (rowSquareS s i)

private theorem rep_massAt {s : ScalarCase} (h : RowsOk s) (i : Fin 5) :
    (massAtS s i).Rep (massAt s i) := by
  simp only [massAtS,massAt]
  split_ifs
  · exact Scaled.rep_one
  · exact rep_newtonMass (rep_rowSquare s i) (h i).1 (h i).2

private def massS (s : ScalarCase) : Scaled :=
  ((((massAtS s 0).mulF (massAtS s 1)).mulF (massAtS s 2)).mulF (massAtS s 3)).mulF
    (massAtS s 4)

private theorem rep_mass {s : ScalarCase} (h : RowsOk s) : (massS s).Rep (mass s) := by
  rw [mass,Fin.prod_univ_five]
  exact ((((rep_massAt h 0).mulF (rep_massAt h 1)).mulF (rep_massAt h 2)).mulF
    (rep_massAt h 3)).mulF (rep_massAt h 4)

private def massExceptS (s : ScalarCase) (i : Fin 5) : Scaled :=
  ((((if (0:Fin 5)=i then Scaled.ofNat 1 else massAtS s 0).mulF
    (if (1:Fin 5)=i then Scaled.ofNat 1 else massAtS s 1)).mulF
    (if (2:Fin 5)=i then Scaled.ofNat 1 else massAtS s 2)).mulF
    (if (3:Fin 5)=i then Scaled.ofNat 1 else massAtS s 3)).mulF
    (if (4:Fin 5)=i then Scaled.ofNat 1 else massAtS s 4)

private theorem rep_massExcept {s : ScalarCase} (h : RowsOk s) (i : Fin 5) :
    (massExceptS s i).Rep (massExcept s i) := by
  rw [massExcept,Fin.prod_univ_five]
  exact ((((rep_ite Scaled.rep_one (rep_massAt h 0)).mulF
    (rep_ite Scaled.rep_one (rep_massAt h 1))).mulF (rep_ite Scaled.rep_one (rep_massAt h 2))).mulF
    (rep_ite Scaled.rep_one (rep_massAt h 3))).mulF (rep_ite Scaled.rep_one (rep_massAt h 4))

private def termS (s : ScalarCase) (i : Fin 5) : Scaled :=
  ((rowWeightS s i).mulF ((rowSquareS s i).addF ((massAtS s i).powF 2))).mulF (massExceptS s i)

private def certificateS (s : ScalarCase) : Scaled :=
  (((Scaled.ofNat 2).mulF ((outsideS s).subF (Scaled.const margin))).mulF (massS s)).subF
    ((Scaled.const radiusUpper).mulF (((((termS s 0).addF (termS s 1)).addF (termS s 2)).addF
      (termS s 3)).addF (termS s 4)))

private theorem rep_certificate {s : ScalarCase} (h : RowsOk s) :
    (certificateS s).Rep (certificate s) := by
  have ht (i : Fin 5) : (termS s i).Rep
      (rowWeight s i*(rowSquare s i+(massAt s i)^2)*massExcept s i) :=
    ((rep_rowWeight s i).mulF ((rep_rowSquare s i).addF ((rep_massAt h i).powF 2))).mulF
      (rep_massExcept h i)
  rw [certificate,Fin.sum_univ_five]
  exact (((Scaled.rep_ofNat 2).mulF ((rep_outside s).subF (Scaled.rep_const _))).mulF
    (rep_mass h)).subF ((Scaled.rep_const _).mulF (((((ht 0).addF (ht 1)).addF (ht 2)).addF
      (ht 3)).addF (ht 4)))

/-- Centering on the band interval `[0,length b]`. -/
private def centerB (b : Band) (a : Scaled) : Scaled :=
  match b with
  | .low => a.centerF 1 10 1 1
  | .middle => a.centerF 3 40 1 1
  | .high => a.centerF 7 40 1 1

private theorem rep_centerB (b : Band) {a : Scaled} {q : ℚ[X]} (ha : a.Rep q) :
    (centerB b a).Rep (centered 0 (length b) q) := by
  cases b <;> exact ha.centeredF _ _ _ _ (by norm_num) (by norm_num [length])
    (by norm_num [length])

end Certificates2

section Certificates3
open WholeIntervalPolynomial.Certificate

/-! #### Reserves as integer comparisons -/

private abbrev LowerOk (c : Scaled) (D n d : ℕ) : Prop :=
  (Fast.chebF c.l).length≤D+1 ∧
    (n:ℤ)*((c.s:ℤ)*2^c.l.length)<2*(d:ℤ)*Fast.lowL (Fast.chebF c.l)

private abbrev UpperOk (c : Scaled) (D n d : ℕ) : Prop :=
  (Fast.chebF c.l).length≤D+1 ∧
    2*(d:ℤ)*Fast.upL (Fast.chebF c.l)<(n:ℤ)*((c.s:ℤ)*2^c.l.length)

private theorem lowerOn_gt {c : Scaled} {a b r : ℚ} {q : ℚ[X]} {D n d : ℕ}
    (hc : c.Rep (centered a b q)) (hs : c.s≠0) (hl : c.l.length≤D+1)
    (hr : r=(n:ℚ)/d) (hd : 0<d) (h : LowerOk c D n d) : r<lowerOn D a b q :=
  lt_lowerOn_of_int hc hs hl h.1 hr hd h.2

private theorem upperOn_lt {c : Scaled} {a b r : ℚ} {q : ℚ[X]} {D n d : ℕ}
    (hc : c.Rep (centered a b q)) (hs : c.s≠0) (hl : c.l.length≤D+1)
    (hr : r=(n:ℚ)/d) (hd : 0<d) (h : UpperOk c D n d) : upperOn D a b q<r :=
  upperOn_lt_of_int hc hs hl h.1 hr hd h.2

/-- The kernel facts for the five rows of one case. -/
private abbrev RowFacts (s : ScalarCase) (i : Fin 5) : Prop :=
  (0<(rowSquareS s i).l.getD 0 0 ∧ (rowSquareS s i).s≠0) ∧
  ((centerB (band s) (rowSquareS s i)).s≠0 ∧
    (centerB (band s) (rowSquareS s i)).l.length≤38+1 ∧
    LowerOk (centerB (band s) (rowSquareS s i)) 38 1 4 ∧
    UpperOk (centerB (band s) (rowSquareS s i)) 38 6 1) ∧
  ((centerB (band s) (massAtS s i)).s≠0 ∧
    (centerB (band s) (massAtS s i)).l.length≤3+1 ∧
    LowerOk (centerB (band s) (massAtS s i)) 3 4 5 ∧
    UpperOk (centerB (band s) (massAtS s i)) 3 3 1)

/-- The kernel facts for the certificate of one case. -/
private abbrev CertFacts (s : ScalarCase) : Prop :=
  (centerB (band s) (certificateS s)).s≠0 ∧
  (centerB (band s) (certificateS s)).l.length≤degree s+1 ∧
  (s≠.lowDE → LowerOk (centerB (band s) (certificateS s)) (degree s) 1 100000)

/-! One kernel computation per case: the rows, the masses and the certificate. -/

private theorem facts_lowE : (∀ i : Fin 5,RowFacts .lowE i) ∧ CertFacts .lowE := by
  decide +kernel

private theorem facts_lowG : (∀ i : Fin 5,RowFacts .lowG i) ∧ CertFacts .lowG := by
  decide +kernel

private theorem facts_middleE (j : Fin 4) :
    (∀ i : Fin 5,RowFacts (.middleE j) i) ∧ CertFacts (.middleE j) := by
  fin_cases j <;> decide +kernel

private theorem facts_middleG (j : Fin 4) :
    (∀ i : Fin 5,RowFacts (.middleG j) i) ∧ CertFacts (.middleG j) := by
  fin_cases j <;> decide +kernel

private theorem facts_highE (j : Fin 4) :
    (∀ i : Fin 5,RowFacts (.highE j) i) ∧ CertFacts (.highE j) := by
  fin_cases j <;> decide +kernel

private theorem facts_highG (j : Fin 4) :
    (∀ i : Fin 5,RowFacts (.highG j) i) ∧ CertFacts (.highG j) := by
  fin_cases j <;> decide +kernel

private theorem facts_lowDE : (∀ i : Fin 5,RowFacts .lowDE i) ∧ CertFacts .lowDE := by
  decide +kernel

private theorem facts_middleDE (j : Fin 4) :
    (∀ i : Fin 5,RowFacts (.middleDE j) i) ∧ CertFacts (.middleDE j) := by
  fin_cases j <;> decide +kernel

private theorem facts_highDEH : (∀ i : Fin 5,RowFacts .highDEH i) ∧ CertFacts .highDEH := by
  decide +kernel

private theorem case_facts (s : ScalarCase) : (∀ i : Fin 5,RowFacts s i) ∧ CertFacts s := by
  rcases s with _|_|j|j|j|j|_|j|_
  exacts [facts_lowE,facts_lowG,facts_middleE j,facts_middleG j,facts_highE j,facts_highG j,
    facts_lowDE,facts_middleDE j,facts_highDEH]

private theorem row_facts (s : ScalarCase) (i : Fin 5) : RowFacts s i := (case_facts s).1 i

private theorem rows_ok (s : ScalarCase) : RowsOk s := fun i => (row_facts s i).1

private theorem cert_facts (s : ScalarCase) : CertFacts s := (case_facts s).2

/-! #### Bernstein coefficients -/

private theorem bern_monomial {D : ℕ} {b : ℚ} (hb : b≠0) {j : ℕ} (hj : j≤D) :
    ∑ i : Fin (D+1),C (b^j*(Nat.choose i.val j:ℚ)/(Nat.choose D j:ℚ))*
      WholeIntervalBernstein.basis D b i=X^j := by
  simp only [WholeIntervalBernstein.basis]
  rw [Fin.sum_univ_eq_sum_range (fun i => C (b^j*(Nat.choose i j:ℚ)/(Nat.choose D j:ℚ))*
    (C ((Nat.choose D i:ℚ)/b^D)*X^i*(C b-X)^(D-i))) (D+1)]
  rw [← Finset.sum_range_add_sum_Ico _ (show j≤D+1 by omega)]
  rw [Finset.sum_eq_zero (fun i hi => by
    rw [Finset.mem_range] at hi
    rw [Nat.choose_eq_zero_of_lt hi]
    simp),zero_add,Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ m∈Finset.range (D+1-j),
      C (b^j*(Nat.choose (j+m) j:ℚ)/(Nat.choose D j:ℚ))*
        (C ((Nat.choose D (j+m):ℚ)/b^D)*X^(j+m)*(C b-X)^(D-(j+m)))=
      C (b^j/b^D)*X^j*(X^m*(C b-X)^(D-j-m)*((D-j).choose m:ℚ[X])) := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hc := Nat.choose_mul (n := D) (k := j+m) (s := j) (by omega)
    rw [show j+m-j=m by omega] at hc
    have hcq : (D.choose (j+m):ℚ)*((j+m).choose j:ℚ)=(D.choose j:ℚ)*((D-j).choose m:ℚ) := by
      exact_mod_cast hc
    have hDj : (D.choose j:ℚ)≠0 := by exact_mod_cast (Nat.choose_pos hj).ne'
    have hbD : b^D≠0 := pow_ne_zero _ hb
    have hab : b^j*((j+m).choose j:ℚ)/(D.choose j:ℚ)*((D.choose (j+m):ℚ)/b^D)=
        b^j/b^D*((D-j).choose m:ℚ) := by
      rw [show b^j*((j+m).choose j:ℚ)/(D.choose j:ℚ)*((D.choose (j+m):ℚ)/b^D)=
        b^j/b^D*((D.choose (j+m):ℚ)*((j+m).choose j:ℚ)/(D.choose j:ℚ)) by ring,hcq,
        mul_div_cancel_left₀ _ hDj]
    rw [show D-(j+m)=D-j-m by omega,← C_eq_natCast,pow_add]
    calc _=C (b^j*((j+m).choose j:ℚ)/(D.choose j:ℚ)*((D.choose (j+m):ℚ)/b^D))*
          (X^j*X^m*(C b-X)^(D-j-m)) := by rw [C_mul]; ring
      _=_ := by rw [hab,C_mul]; ring
  rw [Finset.sum_congr rfl hterm,← Finset.mul_sum,show D+1-j=D-j+1 by omega,← add_pow,
    add_sub_cancel,← C_pow,mul_comm (C (b^j/b^D)*X^j),← mul_assoc,← C_mul]
  have hone : b^(D-j)*(b^j/b^D)=1 := by
    rw [← mul_div_assoc,← pow_add,Nat.sub_add_cancel hj,div_self (pow_ne_zero _ hb)]
  rw [hone,map_one,one_mul]

private theorem bern_expansion {D : ℕ} {b : ℚ} (hb : b≠0) {q : ℚ[X]} (hq : q.natDegree≤D) :
    q=WholeIntervalBernstein.expansion D b q := by
  have hco (i : Fin (D+1)) : WholeIntervalBernstein.coefficient D b q i=
      ∑ j∈Finset.range (D+1),q.coeff j*(b^j*(Nat.choose i.val j:ℚ)/(Nat.choose D j:ℚ)) := by
    unfold WholeIntervalBernstein.coefficient
    rw [← Finset.sum_range_add_sum_Ico _ (show i.val+1≤D+1 by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico _ _) (fun j hj => by
      rw [Finset.mem_Ico] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp),add_zero]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  simp only [WholeIntervalBernstein.expansion,hco,map_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => rw [q.as_sum_range_C_mul_X_pow' (n := D+1) (by omega)]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [← bern_monomial hb (by simp at hj; omega),Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul]
  ring

/-- The Bernstein coefficients on `[0,1/5]`, times `s*D!*5^D`. -/
private def bernZ (D : ℕ) (l : List ℤ) (i : ℕ) : ℤ :=
  ∑ j∈Finset.range (i+1),l.getD j 0*5^(D-j)*(i.descFactorial j:ℤ)*((D-j).factorial:ℤ)

private theorem bern_coeff {a : Scaled} {q : ℚ[X]} (ha : a.Rep q) (hs : a.s≠0) {D : ℕ}
    (i : Fin (D+1)) :
    WholeIntervalBernstein.coefficient D (1/5) q i=(bernZ D a.l i:ℚ)/(a.s*D.factorial*5^D) := by
  unfold WholeIntervalBernstein.coefficient bernZ
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j≤D := by have := i.isLt; simp at hj; omega
  have hs' : (a.s:ℚ)≠0 := by exact_mod_cast hs
  have hq : q.coeff j=(a.l.getD j 0:ℚ)/a.s := by
    have h := rep_coeff_mul ha j
    field_simp
    linarith
  have h1 : ((i:ℕ).descFactorial j:ℚ)=(j.factorial:ℚ)*((i:ℕ).choose j:ℚ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose _ _
  have h2 : (D.factorial:ℚ)=(D.choose j:ℚ)*(j.factorial:ℚ)*((D-j).factorial:ℚ) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hj').symm
  have h3 : (5:ℚ)^D=5^(D-j)*5^j := by rw [← pow_add,Nat.sub_add_cancel hj']
  have hc : (D.choose j:ℚ)≠0 := by exact_mod_cast (Nat.choose_pos hj').ne'
  have hf1 : (j.factorial:ℚ)≠0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have hf2 : ((D-j).factorial:ℚ)≠0 := by exact_mod_cast (Nat.factorial_pos (D-j)).ne'
  rw [hq,h1,h2,h3,div_pow,one_pow]
  field_simp

private abbrev BernOk (c : Scaled) (D n d : ℕ) (i : ℕ) : Prop :=
  (n:ℤ)*((c.s:ℤ)*(D.factorial:ℤ)*5^D)≤(d:ℤ)*bernZ D c.l i

private theorem lowDE_facts :
    (certificateS .lowDE).s≠0 ∧ (certificateS .lowDE).l.length≤41+1 ∧
      ∀ i : Fin 42,BernOk (certificateS .lowDE) 41 1 500 i := by
  decide +kernel

end Certificates3

/- These exact reductions are deliberately unrun. Their inputs are the
displayed rational formulas, not a stored angle or state enumeration. -/
theorem certificate_identity (s : ScalarCase) :
    centered 0 (length (band s)) (certificate s)=
      expansion (degree s) (centered 0 (length (band s)) (certificate s)) := by
  exact (rep_centerB _ (rep_certificate (rows_ok s))).eq_expansion (cert_facts s).1
    (cert_facts s).2.1

theorem certificate_reserve (s : ScalarCase) (hs : s≠.lowDE) :
    (1/100000 : ℚ)<lowerOn (degree s) 0 (length (band s)) (certificate s) := by
  exact lowerOn_gt (rep_centerB _ (rep_certificate (rows_ok s))) (cert_facts s).1
    (cert_facts s).2.1 (by norm_num) (by norm_num) ((cert_facts s).2.2 hs)

theorem lowDE_identity : certificate .lowDE=
    WholeIntervalBernstein.expansion 41 (1/5) (certificate .lowDE) := by
  have h := rep_certificate (rows_ok .lowDE)
  exact bern_expansion (by norm_num)
    ((h.natDegree_le lowDE_facts.1).trans (by have := lowDE_facts.2.1; omega))

theorem lowDE_partition :
    (∑i : Fin 42,WholeIntervalBernstein.basis 41 (1/5) i)=1 := by
  have h := bern_monomial (D := 41) (b := 1/5) (by norm_num) (j := 0) (by norm_num)
  simpa using h

theorem lowDE_reserve (i : Fin 42) :
    (1/500 : ℚ)≤WholeIntervalBernstein.coefficient 41 (1/5) (certificate .lowDE) i := by
  have h := rep_certificate (rows_ok .lowDE)
  rw [bern_coeff h lowDE_facts.1 i,le_div_iff₀ (by
    have := Nat.pos_of_ne_zero lowDE_facts.1
    positivity)]
  have h' := (Int.cast_le (R := ℚ)).mpr (lowDE_facts.2.2 i)
  push_cast at h'
  norm_num at h' ⊢
  linarith

theorem mass_identity (s : ScalarCase) (i : Fin 5) :
    centered 0 (length (band s)) (massAt s i)=
      expansion 3 (centered 0 (length (band s)) (massAt s i)) := by
  exact (rep_centerB _ (rep_massAt (rows_ok s) i)).eq_expansion (row_facts s i).2.2.1
    (row_facts s i).2.2.2.1

theorem mass_reserves (s : ScalarCase) (i : Fin 5) :
    (4/5 : ℚ)<lowerOn 3 0 (length (band s)) (massAt s i) ∧
      upperOn 3 0 (length (band s)) (massAt s i)<3 := by
  have hc := rep_centerB (band s) (rep_massAt (rows_ok s) i)
  obtain ⟨h1,h2,h3,h4⟩ := (row_facts s i).2.2
  exact ⟨lowerOn_gt hc h1 h2 (by norm_num) (by norm_num) h3,
    upperOn_lt hc h1 h2 (by norm_num) (by norm_num) h4⟩

theorem square_identity (s : ScalarCase) (i : Fin 5) :
    centered 0 (length (band s)) (rowSquare s i)=
      expansion 38 (centered 0 (length (band s)) (rowSquare s i)) := by
  exact (rep_centerB _ (rep_rowSquare s i)).eq_expansion (row_facts s i).2.1.1
    (row_facts s i).2.1.2.1

theorem square_reserves (s : ScalarCase) (i : Fin 5) :
    (1/4 : ℚ)<lowerOn 38 0 (length (band s)) (rowSquare s i) ∧
      upperOn 38 0 (length (band s)) (rowSquare s i)<6 := by
  have hc := rep_centerB (band s) (rep_rowSquare s i)
  obtain ⟨h1,h2,h3,h4⟩ := (row_facts s i).2.1
  exact ⟨lowerOn_gt hc h1 h2 (by norm_num) (by norm_num) h3,
    upperOn_lt hc h1 h2 (by norm_num) (by norm_num) h4⟩

theorem certificate_positive (s : ScalarCase) {z : ℝ}
    (hz : z∈Set.Icc 0 (length (band s):ℝ)) : 0<aeval z (certificate s) := by
  by_cases hs : s=.lowDE
  · subst s
    have hh := WholeIntervalBernstein.lower_on_interval (by norm_num : (0:ℚ)<1/5)
      lowDE_identity lowDE_partition lowDE_reserve hz
    norm_num at hh
    linarith
  · have hz' : z∈Set.Icc ((0:ℚ):ℝ) (length (band s):ℝ) := by simpa using hz
    have hh := positive_on_interval (length_pos (band s)) (certificate_identity s)
      (certificate_reserve s hs) hz'
    norm_num at hh
    linarith

theorem mass_bounds (s : ScalarCase) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length (band s):ℝ)) :
    4/5<aeval z (massAt s i) ∧ aeval z (massAt s i)<3 := by
  have hz' : z∈Set.Icc ((0:ℚ):ℝ) (length (band s):ℝ) := by simpa using hz
  have hh := interval_bounds (length_pos (band s)) (mass_identity s i) hz'
  have hl : (4/5 : ℝ)<(lowerOn 3 0 (length (band s)) (massAt s i):ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (mass_reserves s i).1
    push_cast at h
    exact h
  have hu : (upperOn 3 0 (length (band s)) (massAt s i):ℝ)<(3:ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (mass_reserves s i).2
    push_cast at h
    exact h
  exact ⟨hl.trans_le hh.1,hh.2.trans_lt hu⟩

theorem square_bounds (s : ScalarCase) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length (band s):ℝ)) :
    1/4<aeval z (rowSquare s i) ∧ aeval z (rowSquare s i)<6 := by
  have hz' : z∈Set.Icc ((0:ℚ):ℝ) (length (band s):ℝ) := by simpa using hz
  have hh := interval_bounds (length_pos (band s)) (square_identity s i) hz'
  have hl : (1/4 : ℝ)<(lowerOn 38 0 (length (band s)) (rowSquare s i):ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (square_reserves s i).1
    push_cast at h
    exact h
  have hu : (upperOn 38 0 (length (band s)) (rowSquare s i):ℝ)<(6:ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (square_reserves s i).2
    push_cast at h
    exact h
  exact ⟨hl.trans_le hh.1,hh.2.trans_lt hu⟩

theorem radius_upper : Real.sqrt qTrial<(radiusUpper:ℝ) := by
  have hs := Real.sq_sqrt (show 0≤qTrial by norm_num [qTrial])
  have hn := Real.sqrt_nonneg qTrial
  norm_num [qTrial,radiusUpper] at *
  nlinarith

theorem axis_upper : axisCoordinate qTrial<(axisUpper:ℝ) := by
  have hs := Real.sq_sqrt (show 0≤qTrial-1/4 by norm_num [qTrial])
  have hn := Real.sqrt_nonneg (qTrial-1/4)
  norm_num [axisCoordinate,qTrial,axisUpper] at *
  nlinarith

end SquaresInCircles.Eight.SoleScalarPolynomials
