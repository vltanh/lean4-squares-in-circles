module

public import SquaresInCircles.Eight.TableFree.ExceptionalECoefficients
public import SquaresInCircles.Eight.TableFree.SoleScalarPolynomials
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# Ten whole-interval exceptional endpoint polynomials

Uncompiled source. The four domains are the two low intervals and the
complete middle and high intervals in the hand argument. Each of the
five radical masses comes from three rational Newton steps and a cubic
truncation. The displayed arithmetic proofs have not been run. These
polynomial facts are transferred to the actual trigonometric stress in
subsequent files; they are not assumed geometric conclusions.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalEPolynomials
open Polynomial WholeIntervalPolynomial ExceptionalECoefficients
open WholeIntervalPolynomial.Certificate (Scaled lowerZ upperZ chebList lowerOn_eq_of_rep
  upperOn_eq_of_rep)
open WholeIntervalPolynomial.Certificate.Scaled (const var ofNat rep_const rep_var rep_one
  rep_ofNat rep_zero)

inductive ScalarCase where
  | lowZero | lowReturn | middle (i : Fin 4) | high (i : Fin 4)
  deriving DecidableEq

instance : Fintype ScalarCase where
  elems := {.lowZero, .lowReturn} ∪
    Finset.univ.image ScalarCase.middle ∪
    Finset.univ.image ScalarCase.high
  complete x := by cases x <;> simp

def band : ScalarCase → Band
  | .lowZero | .lowReturn => .low
  | .middle _ => .middle
  | .high _ => .high

def origin : ScalarCase → ℚ
  | .lowZero => 0 | .lowReturn => 4/25 | .middle _ => 9/50 | .high _ => 7/20

def length : ScalarCase → ℚ
  | .lowZero => 1/10 | .lowReturn => 1/50 | .middle _ => 17/100 | .high _ => 7/20

def domain (s : ScalarCase) : Set ℝ := Set.Icc (origin s:ℝ) ((origin s+length s):ℝ)

def negativeIndex : ScalarCase → Fin 4
  | .lowZero | .lowReturn => 2
  | .middle i | .high i => i

def radiusUpper : ℚ := 989385433/500000000
def margin : ℚ := 1/100000000
def parameter (s : ScalarCase) : ℚ[X] := C (origin s)+X
def sine (s : ScalarCase) : ℚ[X] := PositiveScalarPolynomials.sine.comp (parameter s)
def cosine (s : ScalarCase) : ℚ[X] := PositiveScalarPolynomials.cosine.comp (parameter s)

def k (s : ScalarCase) : ℚ[X] :=
  if band s=.low then C (17253/20000)+C (67/100)*parameter s+C (27/100)*(parameter s)^2 else 1

def ell (s : ScalarCase) : ℚ[X] :=
  match band s with
  | .low => C (50521/100000)+C (21/25)*parameter s+C (1/2)*(parameter s)^2
  | .middle => C (551/1000)+C (67/100)*parameter s+C (21/100)*(parameter s)^2
  | .high => C (7/10)+C (8/25)*parameter s

def c (s : ScalarCase) : ℚ[X] :=
  match band s with
  | .low => C (17253/20000)+C (18/25)*parameter s+C (3/10)*(parameter s)^2
  | .middle => C (891/1000)+C (16/25)*parameter s+C (1/50)*(parameter s)^2
  | .high => C (113/100)

def eta (s : ScalarCase) : ℚ[X] :=
  match band s with
  | .low => C (131/500)+C (19/100)*parameter s+C (2/25)*(parameter s)^2
  | .middle => C (61/200)-C (1/50)*parameter s+C (7/200)*(parameter s)^2
  | .high => C (27/100)+C (2/25)*parameter s

def p (s : ScalarCase) : ℚ[X] := cosine s+eta s*sine s
def first (s : ScalarCase) : Fin 4 → ℚ[X] := ![p s,k s,ell s,1]
def second (s : ScalarCase) : Fin 4 → ℚ[X] := ![k s,ell s,c s,c s]
def nu (s : ScalarCase) : ℚ[X] := ![C (53/50),ell s,c s,c s] (negativeIndex s)

def outside (s : ScalarCase) : ℚ[X] :=
  3*k s+2*ell s+3*c s+1+2*cosine s+(1+2*eta s)*sine s+nu s*(cosine s-1)

def squaredNorm (s : ScalarCase) (i : Fin 4) : ℚ[X] :=
  (first s i)^2+(second s i)^2-
    (if i=negativeIndex s then 2*first s i*second s i*sine s else 0)

def rowSquare (s : ScalarCase) (i : Fin 5) : ℚ[X] :=
  if hi : i.val<4 then squaredNorm s ⟨i.val,hi⟩ else 1+(eta s)^2

def rowWeight (s : ScalarCase) (i : Fin 5) : ℚ[X] := if i.val<4 then 1 else sine s
def massAt (s : ScalarCase) (i : Fin 5) : ℚ[X] := SoleScalarPolynomials.newtonMass (rowSquare s i)
def mass (s : ScalarCase) : ℚ[X] := ∏i : Fin 5,massAt s i
def massExcept (s : ScalarCase) (i : Fin 5) : ℚ[X] :=
  ∏j : Fin 5,if j=i then 1 else massAt s j

def certificate (s : ScalarCase) : ℚ[X] :=
  2*(outside s-C margin)*mass s-C radiusUpper*
    ∑i : Fin 5,rowWeight s i*(rowSquare s i+(massAt s i)^2)*massExcept s i

def middleBQuotient : ℚ[X] := (certificate (.middle 2)-C ((certificate (.middle 2)).coeff 0)).divX

theorem length_pos (s : ScalarCase) : 0<length s := by cases s <;> norm_num [length]

theorem family_domain {s : ScalarCase} {t : ℝ} (ht : t∈domain s) :
    t∈ExceptionalECoefficients.domain (band s) := by
  cases s <;> norm_num [domain,ExceptionalECoefficients.domain,origin,length,band,frameCap] at ht ⊢ <;>
    constructor <;> linarith [ht.1,ht.2]

theorem local_parameter {s : ScalarCase} {t : ℝ} (ht : t∈domain s) :
    t-(origin s:ℝ)∈Set.Icc 0 (length s:ℝ) := by
  dsimp [domain] at ht
  push_cast at ht
  constructor <;> linarith [ht.1,ht.2]

/-! ## Kernel certificates

Each polynomial is mirrored by a `Certificate.Scaled` integer list (module
`PolynomialCertificates`); the kernel evaluates the lists, one scalar case per
declaration. -/

private def sineL : Certificate.Scaled := ⟨[0, 1307674368000, 0, -217945728000, 0, 10897286400, 0,
  -259459200, 0, 3603600, 0, -32760, 0, 210, 0, -1], 1307674368000⟩

private def cosineL : Certificate.Scaled := ⟨[20922789888000, 0, -10461394944000, 0, 871782912000, 0,
  -29059430400, 0, 518918400, 0, -5765760, 0, 43680, 0, -240, 0, 1], 20922789888000⟩

private def shiftL (s : ScalarCase) (c : Certificate.Scaled) : Certificate.Scaled :=
  c.center 1 (origin s).den (origin s).num (origin s).den

private def parL (s : ScalarCase) : Certificate.Scaled :=
  (Certificate.Scaled.const (origin s)).add Certificate.Scaled.var

private def sineS (s : ScalarCase) : Certificate.Scaled := shiftL s sineL

private def cosineS (s : ScalarCase) : Certificate.Scaled := shiftL s cosineL

private def quadL (s : ScalarCase) (a b c : ℚ) : Certificate.Scaled :=
  ((const a).add ((const b).mul (parL s))).add ((const c).mul ((parL s).pow 2))

private def kS (s : ScalarCase) : Certificate.Scaled :=
  if band s = .low then quadL s (17253/20000) (67/100) (27/100) else Certificate.Scaled.ofNat 1

private def ellS (s : ScalarCase) : Certificate.Scaled :=
  match band s with
  | .low => quadL s (50521/100000) (21/25) (1/2)
  | .middle => quadL s (551/1000) (67/100) (21/100)
  | .high => (Certificate.Scaled.const (7/10)).add ((Certificate.Scaled.const (8/25)).mul (parL s))

private def cS (s : ScalarCase) : Certificate.Scaled :=
  match band s with
  | .low => quadL s (17253/20000) (18/25) (3/10)
  | .middle => quadL s (891/1000) (16/25) (1/50)
  | .high => Certificate.Scaled.const (113/100)

private def etaS (s : ScalarCase) : Certificate.Scaled :=
  match band s with
  | .low => quadL s (131/500) (19/100) (2/25)
  | .middle => (((Certificate.Scaled.const (61/200)).sub
      ((Certificate.Scaled.const (1/50)).mul (parL s))).add
      ((Certificate.Scaled.const (7/200)).mul ((parL s).pow 2)))
  | .high => (Certificate.Scaled.const (27/100)).add ((Certificate.Scaled.const (2/25)).mul (parL s))

private def pS (s : ScalarCase) : Certificate.Scaled := (cosineS s).add ((etaS s).mul (sineS s))

private def firstS (s : ScalarCase) : Fin 4 → Certificate.Scaled :=
  ![pS s, kS s, ellS s, Certificate.Scaled.ofNat 1]

private def secondS (s : ScalarCase) : Fin 4 → Certificate.Scaled := ![kS s, ellS s, cS s, cS s]

private def nuS (s : ScalarCase) : Certificate.Scaled :=
  ![Certificate.Scaled.const (53/50), ellS s, cS s, cS s] (negativeIndex s)

private def outsideS (s : ScalarCase) : Certificate.Scaled :=
  (((((((ofNat 3).mul (kS s)).add ((ofNat 2).mul (ellS s))).add ((ofNat 3).mul (cS s))).add
    (ofNat 1)).add ((ofNat 2).mul (cosineS s))).add (((ofNat 1).add ((ofNat 2).mul (etaS s))).mul
    (sineS s))).add ((nuS s).mul ((cosineS s).sub (ofNat 1)))

private def squaredNormS (s : ScalarCase) (i : Fin 4) : Certificate.Scaled :=
  (((firstS s i).pow 2).add ((secondS s i).pow 2)).sub
    (if i = negativeIndex s then (((ofNat 2).mul (firstS s i)).mul (secondS s i)).mul (sineS s)
      else ⟨[], 1⟩)

private def rowSquareS (s : ScalarCase) (i : Fin 5) : Certificate.Scaled :=
  if hi : i.val < 4 then squaredNormS s ⟨i.val, hi⟩ else (ofNat 1).add ((etaS s).pow 2)

private def rowWeightS (s : ScalarCase) (i : Fin 5) : Certificate.Scaled :=
  if i.val < 4 then ofNat 1 else sineS s

private def coeffQ (c : Certificate.Scaled) (i : ℕ) : ℚ := (c.l.getD i 0 : ℚ) / c.s

private def truncL (c : Certificate.Scaled) : Certificate.Scaled :=
  (((const (coeffQ c 0)).add ((const (coeffQ c 1)).mul var)).add
    ((const (coeffQ c 2)).mul (var.pow 2))).add ((const (coeffQ c 3)).mul (var.pow 3))

private def massInner (c : Certificate.Scaled) : Certificate.Scaled :=
  let v0 := coeffQ c 0
  let w := (const (1/v0)).mul ((truncL c).sub (const v0))
  (const (SoleScalarPolynomials.newton v0 3)).mul
    ((((ofNat 1).add ((const (1/2)).mul w)).sub ((const (1/8)).mul (w.pow 2))).add
      ((const (1/16)).mul (w.pow 3)))

private def newtonMassL (c : Certificate.Scaled) : Certificate.Scaled := truncL (massInner c)

private def massAtS (s : ScalarCase) (i : Fin 5) : Certificate.Scaled := newtonMassL (rowSquareS s i)

private def massS (s : ScalarCase) : Certificate.Scaled :=
  ((((massAtS s 0).mul (massAtS s 1)).mul (massAtS s 2)).mul (massAtS s 3)).mul (massAtS s 4)

private def exceptS (s : ScalarCase) (i j : Fin 5) : Certificate.Scaled :=
  if j = i then Certificate.Scaled.ofNat 1 else massAtS s j

private def massExceptS (s : ScalarCase) (i : Fin 5) : Certificate.Scaled :=
  ((((exceptS s i 0).mul (exceptS s i 1)).mul (exceptS s i 2)).mul (exceptS s i 3)).mul (exceptS s i 4)

private def termS (s : ScalarCase) (i : Fin 5) : Certificate.Scaled :=
  ((rowWeightS s i).mul ((rowSquareS s i).add ((massAtS s i).pow 2))).mul (massExceptS s i)

private def certS (s : ScalarCase) : Certificate.Scaled :=
  (((ofNat 2).mul ((outsideS s).sub (const margin))).mul (massS s)).sub
    ((const radiusUpper).mul (((((termS s 0).add (termS s 1)).add (termS s 2)).add (termS s 3)).add
      (termS s 4)))

private def lnum : ScalarCase → ℕ
  | .lowZero | .lowReturn => 1 | .middle _ => 17 | .high _ => 7

private def lden : ScalarCase → ℕ
  | .lowZero => 20 | .lowReturn => 100 | .middle _ => 200 | .high _ => 40

private def cen (s : ScalarCase) (c : Certificate.Scaled) : Certificate.Scaled :=
  c.center (lnum s) (lden s) 1 1

private def loCheck (D : ℕ) (c : Scaled) (r : ℚ) : Bool :=
  decide (c.l.length ≤ D+1) &&
    decide (r < (lowerZ D (fun j => (chebList c.l).getD j 0) : ℚ)/(c.s*2^c.l.length/2))

private def upCheck (D : ℕ) (c : Scaled) (r : ℚ) : Bool :=
  decide (c.l.length ≤ D+1) &&
    decide ((upperZ D (fun j => (chebList c.l).getD j 0) : ℚ)/(c.s*2^c.l.length/2) < r)

private def rowCheck (s : ScalarCase) (i : Fin 5) : Bool :=
  loCheck 38 (cen s (rowSquareS s i)) (1/4) && upCheck 38 (cen s (rowSquareS s i)) 6 &&
  loCheck 3 (cen s (massAtS s i)) (4/5) && upCheck 3 (cen s (massAtS s i)) 3

private def rowsCheck (s : ScalarCase) : Bool :=
  rowCheck s 0 && rowCheck s 1 && rowCheck s 2 && rowCheck s 3 && rowCheck s 4

/-- The derivative of a coefficient list. -/
private def derivAux : ℕ → List ℤ → List ℤ
  | _, [] => []
  | k, a :: t => ((k:ℤ) * a) :: derivAux (k+1) t

private def derivS (c : Certificate.Scaled) : Certificate.Scaled := ⟨derivAux 1 c.l.tail, c.s⟩

/-- The value of a coefficient list at a rational point. -/
private def evalL (x : ℚ) : List ℤ → ℚ
  | [] => 0
  | a :: t => (a : ℚ) + x * evalL x t

private def lowZeroOK : Bool :=
  upCheck 45 (cen .lowZero (derivS (certS .lowZero))) (-49/1000) &&
    decide ((1/2000 : ℚ) < evalL (1/10) (certS .lowZero).l / (certS .lowZero).s)

private def middleBOK : Bool :=
  decide ((1/250 : ℚ) < coeffQ (certS (.middle 2)) 0) &&
    loCheck 45 (cen (.middle 2) (certS (.middle 2)).divX) (1/5)

/-- The certificate checks of one scalar case. -/
private def certOK (s : ScalarCase) : Bool :=
  decide ((cen s (certS s)).l.length ≤ 46+1) &&
    (if s = .lowZero then lowZeroOK else if s = .middle 2 then middleBOK
      else loCheck 46 (cen s (certS s)) (1/1000))

/-! ### The kernel checks, one declaration per scalar case -/

private theorem certOK_lowZero : certOK .lowZero = true := by decide +kernel

private theorem certOK_lowReturn : certOK .lowReturn = true := by decide +kernel

private theorem certOK_middle0 : certOK (.middle 0) = true := by decide +kernel

private theorem certOK_middle1 : certOK (.middle 1) = true := by decide +kernel

private theorem certOK_middle2 : certOK (.middle 2) = true := by decide +kernel

private theorem certOK_middle3 : certOK (.middle 3) = true := by decide +kernel

private theorem certOK_high0 : certOK (.high 0) = true := by decide +kernel

private theorem certOK_high1 : certOK (.high 1) = true := by decide +kernel

private theorem certOK_high2 : certOK (.high 2) = true := by decide +kernel

private theorem certOK_high3 : certOK (.high 3) = true := by decide +kernel

private theorem rowsCheck_lowZero : rowsCheck .lowZero = true := by decide +kernel

private theorem rowsCheck_lowReturn : rowsCheck .lowReturn = true := by decide +kernel

private theorem rowsCheck_middle0 : rowsCheck (.middle 0) = true := by decide +kernel

private theorem rowsCheck_middle1 : rowsCheck (.middle 1) = true := by decide +kernel

private theorem rowsCheck_middle2 : rowsCheck (.middle 2) = true := by decide +kernel

private theorem rowsCheck_middle3 : rowsCheck (.middle 3) = true := by decide +kernel

private theorem rowsCheck_high0 : rowsCheck (.high 0) = true := by decide +kernel

private theorem rowsCheck_high1 : rowsCheck (.high 1) = true := by decide +kernel

private theorem rowsCheck_high2 : rowsCheck (.high 2) = true := by decide +kernel

private theorem rowsCheck_high3 : rowsCheck (.high 3) = true := by decide +kernel

private theorem r39_sine_rep : (⟨[0, 1307674368000, 0, -217945728000, 0, 10897286400, 0, -259459200,
    0, 3603600, 0, -32760, 0, 210, 0, -1], 1307674368000⟩ : Certificate.Scaled).Rep
    PositiveScalarPolynomials.sine := by
  unfold Certificate.Scaled.Rep
  apply Polynomial.funext; intro x
  simp only [Certificate.toPoly, PositiveScalarPolynomials.sine, eval_mul, eval_C, eval_add,
    eval_X, eval_sub, eval_pow, eval_zero]
  push_cast; ring

private theorem r39_cosine_rep : (⟨[20922789888000, 0, -10461394944000, 0, 871782912000, 0,
    -29059430400, 0, 518918400, 0, -5765760, 0, 43680, 0, -240, 0, 1], 20922789888000⟩ :
    Certificate.Scaled).Rep PositiveScalarPolynomials.cosine := by
  unfold Certificate.Scaled.Rep
  apply Polynomial.funext; intro x
  simp only [Certificate.toPoly, PositiveScalarPolynomials.cosine, eval_mul, eval_C, eval_add,
    eval_X, eval_sub, eval_pow, eval_zero, eval_one]
  push_cast; ring

/-- `p(origin s + X)` as a centering on `[origin s - 1, origin s + 1]`. -/

private theorem parameter_eq (s : ScalarCase) :
    parameter s = affine (origin s - 1) (origin s + 1) := by
  simp only [parameter, affine]; congr 1 <;> ring_nf; simp

private theorem shiftL_rep (s : ScalarCase) {c : Certificate.Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (shiftL s c).Rep (p.comp (parameter s)) := by
  rw [parameter_eq]
  have h := hc.centered 1 (origin s).den (origin s).num (origin s).den (a := origin s - 1)
    (b := origin s + 1) (Rat.den_ne_zero _) (by push_cast; rw [one_mul, Rat.num_div_den]; ring)
    (by push_cast; rw [one_mul, div_self (by exact_mod_cast Rat.den_ne_zero _)]; ring)
  exact h

private theorem parL_rep (s : ScalarCase) : (parL s).Rep (parameter s) :=
  (Certificate.Scaled.rep_const _).add Certificate.Scaled.rep_var

private theorem sineS_rep (s : ScalarCase) : (sineS s).Rep (sine s) := shiftL_rep s r39_sine_rep

private theorem cosineS_rep (s : ScalarCase) : (cosineS s).Rep (cosine s) :=
  shiftL_rep s r39_cosine_rep


private theorem quadL_rep (s : ScalarCase) (a b c : ℚ) :
    (quadL s a b c).Rep (C a + C b * parameter s + C c * (parameter s)^2) :=
  ((Certificate.Scaled.rep_const a).add ((Certificate.Scaled.rep_const b).mul (parL_rep s))).add
    ((Certificate.Scaled.rep_const c).mul ((parL_rep s).pow 2))

private theorem kS_rep (s : ScalarCase) : (kS s).Rep (k s) := by
  unfold kS k; split_ifs
  · exact quadL_rep s _ _ _
  · exact Certificate.Scaled.rep_one

private theorem ellS_rep (s : ScalarCase) : (ellS s).Rep (ell s) := by
  unfold ellS ell
  generalize band s = b
  cases b
  · exact quadL_rep s _ _ _
  · exact quadL_rep s _ _ _
  · exact (Certificate.Scaled.rep_const _).add ((Certificate.Scaled.rep_const _).mul (parL_rep s))

private theorem cS_rep (s : ScalarCase) : (cS s).Rep (c s) := by
  unfold cS c
  generalize band s = b
  cases b
  · exact quadL_rep s _ _ _
  · exact quadL_rep s _ _ _
  · exact Certificate.Scaled.rep_const _

private theorem etaS_rep (s : ScalarCase) : (etaS s).Rep (eta s) := by
  unfold etaS eta
  generalize band s = b
  cases b
  · exact quadL_rep s _ _ _
  · exact ((Certificate.Scaled.rep_const _).sub ((Certificate.Scaled.rep_const _).mul
      (parL_rep s))).add ((Certificate.Scaled.rep_const _).mul ((parL_rep s).pow 2))
  · exact (Certificate.Scaled.rep_const _).add ((Certificate.Scaled.rep_const _).mul (parL_rep s))

private theorem pS_rep (s : ScalarCase) : (pS s).Rep (p s) :=
  (cosineS_rep s).add ((etaS_rep s).mul (sineS_rep s))

private theorem firstS_rep (s : ScalarCase) (i : Fin 4) : (firstS s i).Rep (first s i) := by
  fin_cases i
  · exact pS_rep s
  · exact kS_rep s
  · exact ellS_rep s
  · exact Certificate.Scaled.rep_one

private theorem secondS_rep (s : ScalarCase) (i : Fin 4) : (secondS s i).Rep (second s i) := by
  fin_cases i
  · exact kS_rep s
  · exact ellS_rep s
  · exact cS_rep s
  · exact cS_rep s

private theorem nuS_rep (s : ScalarCase) : (nuS s).Rep (nu s) := by
  unfold nuS nu
  generalize negativeIndex s = i
  fin_cases i
  · exact Certificate.Scaled.rep_const _
  · exact ellS_rep s
  · exact cS_rep s
  · exact cS_rep s



private theorem outsideS_rep (s : ScalarCase) : (outsideS s).Rep (outside s) :=
  ((((((((rep_ofNat 3).mul (kS_rep s)).add ((rep_ofNat 2).mul (ellS_rep s))).add
    ((rep_ofNat 3).mul (cS_rep s))).add rep_one).add ((rep_ofNat 2).mul (cosineS_rep s))).add
    ((rep_one.add ((rep_ofNat 2).mul (etaS_rep s))).mul (sineS_rep s))).add
    ((nuS_rep s).mul ((cosineS_rep s).sub rep_one)))



private theorem squaredNormS_rep (s : ScalarCase) (i : Fin 4) :
    (squaredNormS s i).Rep (squaredNorm s i) := by
  unfold squaredNormS squaredNorm
  refine (((firstS_rep s i).pow 2).add ((secondS_rep s i).pow 2)).sub ?_
  split_ifs
  · exact (((rep_ofNat 2).mul (firstS_rep s i)).mul (secondS_rep s i)).mul (sineS_rep s)
  · exact rep_zero



private theorem rowSquareS_rep (s : ScalarCase) (i : Fin 5) :
    (rowSquareS s i).Rep (rowSquare s i) := by
  unfold rowSquareS rowSquare
  split_ifs
  · exact squaredNormS_rep s _
  · exact rep_one.add ((etaS_rep s).pow 2)



private theorem rowWeightS_rep (s : ScalarCase) (i : Fin 5) :
    (rowWeightS s i).Rep (rowWeight s i) := by
  unfold rowWeightS rowWeight
  split_ifs
  · exact rep_one
  · exact sineS_rep s



private theorem truncL_rep {c : Certificate.Scaled} {v : ℚ[X]} (hc : c.Rep v) (hs : c.s ≠ 0) :
    (truncL c).Rep (SoleScalarPolynomials.truncateThree v) := by
  unfold SoleScalarPolynomials.truncateThree
  rw [hc.coeff hs 0, hc.coeff hs 1, hc.coeff hs 2, hc.coeff hs 3]
  exact (((rep_const _).add ((rep_const _).mul rep_var)).add ((rep_const _).mul (rep_var.pow 2))).add
    ((rep_const _).mul (rep_var.pow 3))



private theorem newtonMassL_rep {c : Certificate.Scaled} {v : ℚ[X]} (hc : c.Rep v) (hs : c.s ≠ 0) :
    (newtonMassL c).Rep (SoleScalarPolynomials.newtonMass v) := by
  have h0 : v.coeff 0 = coeffQ c 0 := hc.coeff hs 0
  unfold newtonMassL SoleScalarPolynomials.newtonMass
  simp only [h0]
  refine truncL_rep ?_ ?_
  · unfold massInner
    exact (rep_const _).mul ((((rep_one).add ((rep_const _).mul ((rep_const _).mul
      ((truncL_rep hc hs).sub (rep_const _))))).sub ((rep_const _).mul (((rep_const _).mul
      ((truncL_rep hc hs).sub (rep_const _))).pow 2))).add ((rep_const _).mul (((rep_const _).mul
      ((truncL_rep hc hs).sub (rep_const _))).pow 3)))
  · simp only [massInner, truncL, Certificate.Scaled.add, Certificate.Scaled.sub,
      Certificate.Scaled.mul, Certificate.Scaled.pow, Certificate.Scaled.const, Certificate.Scaled.var,
      Certificate.Scaled.ofNat]
    repeat' (first | apply mul_ne_zero | apply pow_ne_zero | exact Rat.den_ne_zero _ | exact one_ne_zero)

private theorem quadL_s (s : ScalarCase) (a b c : ℚ) : (quadL s a b c).s ≠ 0 := by
  simp only [quadL, parL, Certificate.Scaled.add, Certificate.Scaled.mul, Certificate.Scaled.pow,
    Certificate.Scaled.const, Certificate.Scaled.var]
  repeat' (first | apply mul_ne_zero | apply pow_ne_zero | exact Rat.den_ne_zero _ | exact one_ne_zero)

private theorem shiftL_s (s : ScalarCase) {c : Certificate.Scaled} (hc : c.s ≠ 0) :
    (shiftL s c).s ≠ 0 := by
  simp only [shiftL, Certificate.Scaled.center]
  exact mul_ne_zero hc (pow_ne_zero _ (Rat.den_ne_zero _))

private theorem sineS_s (s : ScalarCase) : (sineS s).s ≠ 0 := shiftL_s s (by simp [sineL])

private theorem cosineS_s (s : ScalarCase) : (cosineS s).s ≠ 0 := shiftL_s s (by simp [cosineL])

private theorem kS_s (s : ScalarCase) : (kS s).s ≠ 0 := by
  unfold kS; split_ifs; exacts [quadL_s _ _ _ _, by simp [Certificate.Scaled.ofNat]]

private theorem ellS_s (s : ScalarCase) : (ellS s).s ≠ 0 := by
  unfold ellS; generalize band s = b; cases b
  · exact quadL_s _ _ _ _
  · exact quadL_s _ _ _ _
  · simp only [parL, Certificate.Scaled.add, Certificate.Scaled.mul, Certificate.Scaled.const,
      Certificate.Scaled.var]
    repeat' (first | apply mul_ne_zero | exact Rat.den_ne_zero _ | exact one_ne_zero)

private theorem cS_s (s : ScalarCase) : (cS s).s ≠ 0 := by
  unfold cS; generalize band s = b; cases b
  · exact quadL_s _ _ _ _
  · exact quadL_s _ _ _ _
  · exact Rat.den_ne_zero _

private theorem etaS_s (s : ScalarCase) : (etaS s).s ≠ 0 := by
  unfold etaS; generalize band s = b; cases b
  · exact quadL_s _ _ _ _
  · simp only [parL, Certificate.Scaled.add, Certificate.Scaled.sub, Certificate.Scaled.mul,
      Certificate.Scaled.pow, Certificate.Scaled.const, Certificate.Scaled.var]
    repeat' (first | apply mul_ne_zero | apply pow_ne_zero | exact Rat.den_ne_zero _ | exact one_ne_zero)
  · simp only [parL, Certificate.Scaled.add, Certificate.Scaled.mul, Certificate.Scaled.const,
      Certificate.Scaled.var]
    repeat' (first | apply mul_ne_zero | exact Rat.den_ne_zero _ | exact one_ne_zero)

private theorem pS_s (s : ScalarCase) : (pS s).s ≠ 0 := by
  simp only [pS, Certificate.Scaled.add, Certificate.Scaled.mul]
  exact mul_ne_zero (cosineS_s s) (mul_ne_zero (etaS_s s) (sineS_s s))

private theorem firstS_s (s : ScalarCase) (j : Fin 4) : (firstS s j).s ≠ 0 := by
  fin_cases j
  exacts [pS_s s, kS_s s, ellS_s s, by simp [firstS, Certificate.Scaled.ofNat]]

private theorem secondS_s (s : ScalarCase) (j : Fin 4) : (secondS s j).s ≠ 0 := by
  fin_cases j
  exacts [kS_s s, ellS_s s, cS_s s, cS_s s]

private theorem nuS_s (s : ScalarCase) : (nuS s).s ≠ 0 := by
  unfold nuS; generalize negativeIndex s = j; fin_cases j
  exacts [Rat.den_ne_zero _, ellS_s s, cS_s s, cS_s s]

private theorem rowSquareS_s (s : ScalarCase) (i : Fin 5) : (rowSquareS s i).s ≠ 0 := by
  unfold rowSquareS
  split_ifs
  · simp only [squaredNormS, Certificate.Scaled.add, Certificate.Scaled.sub, Certificate.Scaled.mul,
      Certificate.Scaled.pow, Certificate.Scaled.ofNat]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (firstS_s _ _)) (pow_ne_zero _ (secondS_s _ _))) ?_
    split_ifs
    · exact mul_ne_zero (mul_ne_zero (mul_ne_zero one_ne_zero (firstS_s _ _)) (secondS_s _ _))
        (sineS_s s)
    · exact one_ne_zero
  · simp only [Certificate.Scaled.add, Certificate.Scaled.pow, Certificate.Scaled.ofNat]
    exact mul_ne_zero one_ne_zero (pow_ne_zero _ (etaS_s s))

private theorem massAtS_s (s : ScalarCase) (i : Fin 5) : (massAtS s i).s ≠ 0 := by
  simp only [massAtS, newtonMassL, truncL, Certificate.Scaled.add, Certificate.Scaled.mul,
    Certificate.Scaled.pow, Certificate.Scaled.const, Certificate.Scaled.var]
  repeat' (first | apply mul_ne_zero | apply pow_ne_zero | exact Rat.den_ne_zero _ | exact one_ne_zero)

private theorem massAtS_rep (s : ScalarCase) (i : Fin 5) : (massAtS s i).Rep (massAt s i) :=
  newtonMassL_rep (rowSquareS_rep s i) (rowSquareS_s s i)

private theorem massS_rep (s : ScalarCase) : (massS s).Rep (mass s) := by
  unfold massS mass
  rw [Fin.prod_univ_five]
  exact ((((massAtS_rep s 0).mul (massAtS_rep s 1)).mul (massAtS_rep s 2)).mul
    (massAtS_rep s 3)).mul (massAtS_rep s 4)

private theorem exceptS_rep (s : ScalarCase) (i j : Fin 5) :
    (exceptS s i j).Rep (if j = i then 1 else massAt s j) := by
  unfold exceptS; split_ifs
  · exact Certificate.Scaled.rep_one
  · exact massAtS_rep s j

private theorem massExceptS_rep (s : ScalarCase) (i : Fin 5) :
    (massExceptS s i).Rep (massExcept s i) := by
  unfold massExceptS massExcept
  rw [Fin.prod_univ_five]
  exact ((((exceptS_rep s i 0).mul (exceptS_rep s i 1)).mul (exceptS_rep s i 2)).mul
    (exceptS_rep s i 3)).mul (exceptS_rep s i 4)

private theorem termS_rep (s : ScalarCase) (i : Fin 5) :
    (termS s i).Rep (rowWeight s i * (rowSquare s i + (massAt s i)^2) * massExcept s i) :=
  ((rowWeightS_rep s i).mul ((rowSquareS_rep s i).add ((massAtS_rep s i).pow 2))).mul
    (massExceptS_rep s i)



private theorem certS_rep (s : ScalarCase) : (certS s).Rep (certificate s) := by
  unfold certS certificate
  rw [Fin.sum_univ_five]
  exact (((rep_ofNat 2).mul ((outsideS_rep s).sub (rep_const _))).mul (massS_rep s)).sub
    ((rep_const _).mul (((((termS_rep s 0).add (termS_rep s 1)).add (termS_rep s 2)).add
      (termS_rep s 3)).add (termS_rep s 4)))

private theorem outsideS_s (s : ScalarCase) : (outsideS s).s ≠ 0 := by
  have h1 : (Certificate.Scaled.ofNat 1).s ≠ 0 := one_ne_zero
  have h2 : ∀ n, (Certificate.Scaled.ofNat n).s ≠ 0 := fun _ => one_ne_zero
  unfold outsideS
  simp only [Certificate.Scaled.add, Certificate.Scaled.sub, Certificate.Scaled.mul]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (h2 3) (kS_s s)) (mul_ne_zero (h2 2) (ellS_s s))) (mul_ne_zero (h2 3) (cS_s s)))
    (h2 1)) (mul_ne_zero (h2 2) (cosineS_s s))) (mul_ne_zero (mul_ne_zero (h2 1)
    (mul_ne_zero (h2 2) (etaS_s s))) (sineS_s s))) (mul_ne_zero (nuS_s s)
    (mul_ne_zero (cosineS_s s) (h2 1)))

private theorem massS_s (s : ScalarCase) : (massS s).s ≠ 0 := by
  unfold massS; simp only [Certificate.Scaled.mul]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (massAtS_s s 0) (massAtS_s s 1))
    (massAtS_s s 2)) (massAtS_s s 3)) (massAtS_s s 4)

private theorem exceptS_s (s : ScalarCase) (i j : Fin 5) : (exceptS s i j).s ≠ 0 := by
  unfold exceptS; split_ifs; exacts [one_ne_zero, massAtS_s s j]

private theorem termS_s (s : ScalarCase) (i : Fin 5) : (termS s i).s ≠ 0 := by
  have hw : (rowWeightS s i).s ≠ 0 := by
    unfold rowWeightS; split_ifs; exacts [one_ne_zero, sineS_s s]
  unfold termS massExceptS; simp only [Certificate.Scaled.mul, Certificate.Scaled.add,
    Certificate.Scaled.pow]
  exact mul_ne_zero (mul_ne_zero hw (mul_ne_zero (rowSquareS_s s i) (pow_ne_zero _ (massAtS_s s i))))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (exceptS_s s i 0) (exceptS_s s i 1))
    (exceptS_s s i 2)) (exceptS_s s i 3)) (exceptS_s s i 4))

private theorem certS_s (s : ScalarCase) : (certS s).s ≠ 0 := by
  unfold certS; simp only [Certificate.Scaled.add, Certificate.Scaled.sub, Certificate.Scaled.mul]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero one_ne_zero (mul_ne_zero (outsideS_s s)
    (Rat.den_ne_zero _))) (massS_s s)) (mul_ne_zero (Rat.den_ne_zero _) (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (termS_s s 0) (termS_s s 1)) (termS_s s 2)) (termS_s s 3))
    (termS_s s 4)))

/-- The length of the scalar interval as `num/(2 den)` halves. -/

private theorem cen_rep (s : ScalarCase) {c : Certificate.Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (cen s c).Rep (centered 0 (length s) p) := by
  unfold cen
  cases s <;> exact hc.centered _ _ 1 1 (by simp [lden]) (by norm_num [length, lnum, lden])
    (by norm_num [length, lnum, lden])

private theorem cen_s (s : ScalarCase) {c : Certificate.Scaled} (hc : c.s ≠ 0) : (cen s c).s ≠ 0 := by
  unfold cen Certificate.Scaled.center
  exact mul_ne_zero hc (pow_ne_zero _ (by cases s <;> simp [lden]))




private theorem lo_of_check {D : ℕ} {a b r : ℚ} {c : Scaled} {p : ℚ[X]} (hc : c.Rep (centered a b p))
    (hs : c.s ≠ 0) (h : loCheck D c r = true) :
    r < lowerOn D a b p ∧ centered a b p = expansion D (centered a b p) := by
  simp only [loCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨by rw [lowerOn_eq_of_rep hc hs h.1]; exact h.2, hc.eq_expansion hs h.1⟩


private theorem up_of_check {D : ℕ} {a b r : ℚ} {c : Scaled} {p : ℚ[X]} (hc : c.Rep (centered a b p))
    (hs : c.s ≠ 0) (h : upCheck D c r = true) : upperOn D a b p < r := by
  simp only [upCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [upperOn_eq_of_rep hc hs h.1]; exact h.2

/-- The four whole-interval bounds of a row and its Newton mass. -/

private theorem rows_lowReturn : rowsCheck .lowReturn = true := by decide +kernel

private theorem rows_middle0 : rowsCheck (.middle 0) = true := by decide +kernel

private theorem cert_lowReturn : loCheck 46 (cen .lowReturn (certS .lowReturn)) (1/1000) = true := by
  decide +kernel

private theorem derivAux_getD : ∀ (l : List ℤ) (k n : ℕ),
    (derivAux k l).getD n 0 = ((k + n : ℕ) : ℤ) * l.getD n 0
  | [], k, n => by simp [derivAux]
  | a :: t, k, 0 => by simp [derivAux]
  | a :: t, k, n+1 => by
      simp only [derivAux, List.getD_cons_succ, derivAux_getD t (k+1) n]
      congr 2; omega

private theorem derivS_rep {c : Certificate.Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (derivS c).Rep (derivative p) := by
  unfold Certificate.Scaled.Rep at *
  have h : Certificate.toPoly (derivAux 1 c.l.tail) = derivative (Certificate.toPoly c.l) := by
    ext n
    rw [coeff_derivative, Certificate.coeff_toPoly, Certificate.coeff_toPoly, derivAux_getD]
    rcases c.l with _ | ⟨a, t⟩
    · simp
    · simp only [List.tail_cons, List.getD_cons_succ]; push_cast; ring
  simp only [derivS]
  rw [h, hc, derivative_C_mul]

private theorem evalL_eq (x : ℚ) : ∀ l : List ℤ, evalL x l = (Certificate.toPoly l).eval x
  | [] => by simp [evalL, Certificate.toPoly]
  | a :: t => by simp [evalL, Certificate.toPoly, evalL_eq x t]

private theorem eval_of_rep {c : Certificate.Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s ≠ 0)
    (x : ℚ) : p.eval x = evalL x c.l / c.s := by
  unfold Certificate.Scaled.Rep at hc
  have hs' : (c.s:ℚ) ≠ 0 := by exact_mod_cast hs
  rw [evalL_eq, hc, eval_mul, eval_C]
  field_simp

private theorem certOK_all (s : ScalarCase) : certOK s = true := by
  cases s with
  | lowZero => exact certOK_lowZero
  | lowReturn => exact certOK_lowReturn
  | middle i =>
      fin_cases i
      exacts [certOK_middle0, certOK_middle1, certOK_middle2, certOK_middle3]
  | high i =>
      fin_cases i
      exacts [certOK_high0, certOK_high1, certOK_high2, certOK_high3]

private theorem rowsCheck_all (s : ScalarCase) : rowsCheck s = true := by
  cases s with
  | lowZero => exact rowsCheck_lowZero
  | lowReturn => exact rowsCheck_lowReturn
  | middle i =>
      fin_cases i
      exacts [rowsCheck_middle0, rowsCheck_middle1, rowsCheck_middle2, rowsCheck_middle3]
  | high i =>
      fin_cases i
      exacts [rowsCheck_high0, rowsCheck_high1, rowsCheck_high2, rowsCheck_high3]

private theorem rowCheck_all (s : ScalarCase) (i : Fin 5) : rowCheck s i = true := by
  have h := rowsCheck_all s
  simp only [rowsCheck, Bool.and_eq_true] at h
  fin_cases i
  exacts [h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2]

private theorem rowCheck_spec (s : ScalarCase) (i : Fin 5) :
    loCheck 38 (cen s (rowSquareS s i)) (1/4) = true ∧ upCheck 38 (cen s (rowSquareS s i)) 6 = true ∧
    loCheck 3 (cen s (massAtS s i)) (4/5) = true ∧ upCheck 3 (cen s (massAtS s i)) 3 = true := by
  have h := rowCheck_all s i
  simp only [rowCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

private theorem certLen (s : ScalarCase) : (cen s (certS s)).l.length ≤ 46+1 := by
  have h := certOK_all s
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1


theorem certificate_identity (s : ScalarCase) :
    centered 0 (length s) (certificate s)=expansion 46 (centered 0 (length s) (certificate s)) :=
  (cen_rep s (certS_rep s)).eq_expansion (cen_s s (certS_s s)) (certLen s)

theorem ordinary_reserve (s : ScalarCase) (h0 : s≠.lowZero) (hB : s≠.middle 2) :
    (1/1000:ℚ)<lowerOn 46 0 (length s) (certificate s) := by
  have h := certOK_all s
  simp only [certOK, h0, hB, ite_false, Bool.and_eq_true] at h
  exact (lo_of_check (cen_rep s (certS_rep s)) (cen_s s (certS_s s)) h.2).1

private theorem lowZeroOK_spec :
    upCheck 45 (cen .lowZero (derivS (certS .lowZero))) (-49/1000) = true ∧
    (1/2000 : ℚ) < evalL (1/10) (certS .lowZero).l / (certS .lowZero).s := by
  have h := certOK_lowZero
  simp only [certOK, ite_true, lowZeroOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

private theorem middleBOK_spec :
    (1/250 : ℚ) < coeffQ (certS (.middle 2)) 0 ∧
    loCheck 45 (cen (.middle 2) (certS (.middle 2)).divX) (1/5) = true := by
  have h := certOK_middle2
  simp only [certOK, reduceCtorEq, ite_false, ite_true, middleBOK, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h.2

private theorem lowZero_deriv_len :
    (cen .lowZero (derivS (certS .lowZero))).l.length ≤ 45+1 := by
  have h := lowZeroOK_spec.1
  simp only [upCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem low_derivative_identity :
    centered 0 (1/10) (certificate .lowZero).derivative=
      expansion 45 (centered 0 (1/10) (certificate .lowZero).derivative) :=
  (cen_rep .lowZero (derivS_rep (certS_rep .lowZero))).eq_expansion
    (cen_s .lowZero (c := derivS (certS .lowZero)) (certS_s .lowZero)) lowZero_deriv_len

theorem low_derivative_reserve :
    upperOn 45 0 (1/10) (certificate .lowZero).derivative< -(49/1000:ℚ) := by
  have h := up_of_check (cen_rep .lowZero (derivS_rep (certS_rep .lowZero)))
    (cen_s .lowZero (c := derivS (certS .lowZero)) (certS_s .lowZero)) lowZeroOK_spec.1
  exact h.trans_le (by norm_num)

theorem low_right_reserve : (1/2000:ℚ)<(certificate .lowZero).eval (1/10) := by
  rw [eval_of_rep (certS_rep .lowZero) (certS_s .lowZero)]
  exact lowZeroOK_spec.2

theorem middleB_identity :
    certificate (.middle 2)=C ((certificate (.middle 2)).coeff 0)+X*middleBQuotient := by
  have h := X_mul_divX_add (certificate (.middle 2)-C ((certificate (.middle 2)).coeff 0))
  simp only [coeff_sub, coeff_C_zero, sub_self, map_zero, add_zero] at h
  rw [middleBQuotient, h]
  ring

private theorem middleBQuotient_eq : middleBQuotient = (certificate (.middle 2)).divX := by
  ext n
  simp [middleBQuotient, coeff_divX, coeff_sub]

private theorem middleBQuotient_rep : (certS (.middle 2)).divX.Rep middleBQuotient := by
  rw [middleBQuotient_eq]; exact (certS_rep _).divX

theorem middleB_quotient_identity :
    centered 0 (17/100) middleBQuotient=expansion 45 (centered 0 (17/100) middleBQuotient) :=
  (lo_of_check (cen_rep (.middle 2) middleBQuotient_rep) (cen_s (.middle 2) (c := (certS (.middle 2)).divX) (certS_s (.middle 2))) middleBOK_spec.2).2

theorem middleB_reserves : (1/250:ℚ)<(certificate (.middle 2)).coeff 0 ∧
    (1/5:ℚ)<lowerOn 45 0 (17/100) middleBQuotient := by
  refine ⟨?_, (lo_of_check (cen_rep (.middle 2) middleBQuotient_rep) (cen_s (.middle 2) (c := (certS (.middle 2)).divX) (certS_s (.middle 2)))
    middleBOK_spec.2).1⟩
  rw [(certS_rep _).coeff (certS_s _) 0]
  exact middleBOK_spec.1

theorem polynomial_hasDerivAt (P : ℚ[X]) (z : ℝ) :
    HasDerivAt (fun x : ℝ => aeval x P) (aeval z P.derivative) z := by
  simpa [Polynomial.aeval_def,Polynomial.derivative_map] using
    (P.map (algebraMap ℚ ℝ)).hasDerivAt z

theorem certificate_positive (s : ScalarCase) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s:ℝ)) : 0<aeval z (certificate s) := by
  by_cases h0 : s=.lowZero
  · subst s
    have hz' : z∈Set.Icc (0:ℝ) (1/10) := by simpa [length] using hz
    have hmono : MonotoneOn (fun x : ℝ => -aeval x (certificate .lowZero)) (Set.Icc 0 (1/10)) := by
      apply monoOn_of_hasDeriv_nonneg (d := fun x => -aeval x (certificate .lowZero).derivative)
      · exact fun x _ => ((polynomial_hasDerivAt _ x).neg).continuousAt.continuousWithinAt
      · intro x _; exact (polynomial_hasDerivAt _ x).neg
      · intro x hx
        have hb := (interval_bounds (by norm_num : (0:ℚ)<1/10)
          low_derivative_identity (x := x) (by
            have := Set.Ioo_subset_Icc_self hx; push_cast; exact this)).2
        have hr : (upperOn 45 0 (1/10) (certificate .lowZero).derivative:ℝ) < -49/1000 := by
          have := (Rat.cast_lt (K := ℝ)).mpr low_derivative_reserve; push_cast at this; linarith
        show 0 ≤ -aeval x (certificate .lowZero).derivative
        linarith
    have hright : (1/2000:ℝ)<aeval (1/10:ℝ) (certificate .lowZero) := by
      have h := low_right_reserve
      have e : aeval (1/10:ℝ) (certificate .lowZero) = (((certificate .lowZero).eval (1/10) : ℚ) : ℝ) := by
        rw [show (1/10:ℝ) = algebraMap ℚ ℝ (1/10) by norm_num, aeval_algebraMap_apply_eq_algebraMap_eval]
        rfl
      rw [e]
      have := (Rat.cast_lt (K := ℝ)).mpr h; push_cast at this; exact this
    have hm := hmono hz' (by norm_num) hz'.2
    simp only at hm
    linarith
  · by_cases hB : s=.middle 2
    · subst s
      have hz' : z∈Set.Icc ((0:ℚ):ℝ) ((17/100:ℚ):ℝ) := by
        simpa [length] using hz
      have hquot := positive_on_interval (by norm_num : (0:ℚ)<17/100)
        middleB_quotient_identity middleB_reserves.2 hz'
      have hc0 : (1/250:ℝ)<((certificate (.middle 2)).coeff 0:ℝ) := by
        have := (Rat.cast_lt (K := ℝ)).mpr middleB_reserves.1; push_cast at this; exact this
      have hz0 : 0 ≤ z := by simpa using hz'.1
      have hm := mul_nonneg hz0 (show 0≤aeval z middleBQuotient by push_cast at hquot; linarith)
      rw [middleB_identity]
      simp only [map_add,map_mul,aeval_C,aeval_X]
      simp only [eq_ratCast] at *
      linarith
    · have hh := positive_on_interval (length_pos s) (certificate_identity s)
        (ordinary_reserve s h0 hB) (by simpa using hz)
      norm_num at hh
      linarith

theorem mass_identity (s : ScalarCase) (i : Fin 5) :
    centered 0 (length s) (massAt s i)=expansion 3 (centered 0 (length s) (massAt s i)) :=
  (lo_of_check (cen_rep s (massAtS_rep s i)) (cen_s s (massAtS_s s i)) (rowCheck_spec s i).2.2.1).2

theorem mass_reserves (s : ScalarCase) (i : Fin 5) :
    (4/5:ℚ)<lowerOn 3 0 (length s) (massAt s i) ∧ upperOn 3 0 (length s) (massAt s i)<3 :=
  ⟨(lo_of_check (cen_rep s (massAtS_rep s i)) (cen_s s (massAtS_s s i)) (rowCheck_spec s i).2.2.1).1,
    up_of_check (cen_rep s (massAtS_rep s i)) (cen_s s (massAtS_s s i)) (rowCheck_spec s i).2.2.2⟩

theorem square_identity (s : ScalarCase) (i : Fin 5) :
    centered 0 (length s) (rowSquare s i)=expansion 38 (centered 0 (length s) (rowSquare s i)) :=
  (lo_of_check (cen_rep s (rowSquareS_rep s i)) (cen_s s (rowSquareS_s s i)) (rowCheck_spec s i).1).2

theorem square_reserves (s : ScalarCase) (i : Fin 5) :
    (1/4:ℚ)<lowerOn 38 0 (length s) (rowSquare s i) ∧ upperOn 38 0 (length s) (rowSquare s i)<6 :=
  ⟨(lo_of_check (cen_rep s (rowSquareS_rep s i)) (cen_s s (rowSquareS_s s i)) (rowCheck_spec s i).1).1,
    up_of_check (cen_rep s (rowSquareS_rep s i)) (cen_s s (rowSquareS_s s i)) (rowCheck_spec s i).2.1⟩

theorem mass_bounds (s : ScalarCase) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s:ℝ)) : 4/5<aeval z (massAt s i) ∧ aeval z (massAt s i)<3 := by
  have hh := interval_bounds (length_pos s) (mass_identity s i) (by simpa using hz)
  have hl : (4/5:ℝ)<(lowerOn 3 0 (length s) (massAt s i):ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr (mass_reserves s i).1; push_cast at this; exact this
  have hu : (upperOn 3 0 (length s) (massAt s i):ℝ)<(3:ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr (mass_reserves s i).2; push_cast at this; exact this
  exact ⟨hl.trans_le hh.1,hh.2.trans_lt hu⟩

theorem square_bounds (s : ScalarCase) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s:ℝ)) : 1/4<aeval z (rowSquare s i) ∧ aeval z (rowSquare s i)<6 := by
  have hh := interval_bounds (length_pos s) (square_identity s i) (by simpa using hz)
  have hl : (1/4:ℝ)<(lowerOn 38 0 (length s) (rowSquare s i):ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr (square_reserves s i).1; push_cast at this; exact this
  have hu : (upperOn 38 0 (length s) (rowSquare s i):ℝ)<(6:ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr (square_reserves s i).2; push_cast at this; exact this
  exact ⟨hl.trans_le hh.1,hh.2.trans_lt hu⟩


end SquaresInCircles.Eight.TableFree.ExceptionalEPolynomials
