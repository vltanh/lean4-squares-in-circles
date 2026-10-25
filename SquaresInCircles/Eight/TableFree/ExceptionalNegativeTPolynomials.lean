module

public import SquaresInCircles.Eight.TableFree.ExceptionalNegativeTScalarModel
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# Whole-interval certificates for the forty-four negative-T endpoints

Uncompiled source. This is the exact cubic-Newton-mass construction in
the outside-strip hand proof. Each rational assertion concerns a whole
intrinsic interval. The middle TD diagonal uses its constant term and
positive first quotient. The arithmetic proof terms have not been run.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalNegativeTPolynomials
open Polynomial WholeIntervalPolynomial ExceptionalECoefficients
open ExceptionalNegativeTScalarModel (Row Case band isTD diagonal index origin length domain cap)
open WholeIntervalPolynomial.Certificate (Scaled lowerZ upperZ chebList lowerOn_eq_of_rep
  upperOn_eq_of_rep)
open WholeIntervalPolynomial.Certificate.Scaled (const var ofNat rep_const rep_var rep_one
  rep_ofNat rep_zero)

def radiusUpper : ℚ := 989385433/500000000
def parameter (s : Case) : ℚ[X] := C (origin s.row)+X
def removed (s : Case) : ℚ[X] := if diagonal s.row then parameter s else C (cap s.row)
def angle (s : Case) : ℚ[X] := parameter s-removed s
def sine (s : Case) : ℚ[X] := PositiveScalarPolynomials.sine.comp (parameter s)
def cosine (s : Case) : ℚ[X] := PositiveScalarPolynomials.cosine.comp (parameter s)
def shortSine (s : Case) : ℚ[X] := PositiveScalarPolynomials.sine.comp (angle s)
def shortCosine (s : Case) : ℚ[X] := PositiveScalarPolynomials.cosine.comp (angle s)

def k (s : Case) : ℚ[X] :=
  if band s.row=.low then C (17253/20000)+C (67/100)*parameter s+C (27/100)*(parameter s)^2 else 1
def ell (s : Case) : ℚ[X] :=
  match band s.row with
  | .low => C (50521/100000)+C (21/25)*parameter s+C (1/2)*(parameter s)^2
  | .middle => C (551/1000)+C (67/100)*parameter s+C (21/100)*(parameter s)^2
  | .high => C (7/10)+C (8/25)*parameter s
def c (s : Case) : ℚ[X] :=
  match band s.row with
  | .low => C (17253/20000)+C (18/25)*parameter s+C (3/10)*(parameter s)^2
  | .middle => C (891/1000)+C (16/25)*parameter s+C (1/50)*(parameter s)^2
  | .high => C (113/100)
def eta (s : Case) : ℚ[X] :=
  match band s.row with
  | .low => C (131/500)+C (19/100)*parameter s+C (2/25)*(parameter s)^2
  | .middle => C (61/200)-C (1/50)*parameter s+C (7/200)*(parameter s)^2
  | .high => C (27/100)+C (2/25)*parameter s
def slope (s : Case) : ℚ[X] :=
  if isTD s.row then C (13/12)-C (1/5)*removed s+C (8/25)*(removed s)^2 else C (21/20)
def correction (s : Case) : ℚ[X] :=
  if isTD s.row && decide (band s.row≠.low) then C (8/25)*(c s-1)^2 else 0
def p (s : Case) : ℚ[X] := cosine s+eta s*sine s
def first (s : Case) : Fin 4 → ℚ[X] := ![if s.atG then 1 else p s,k s,ell s,1]
def second (s : Case) : Fin 4 → ℚ[X] := ![if s.atG then k s*p s else k s,ell s,c s,c s]
def nu (s : Case) : ℚ[X] := ![C (53/50),ell s,c s] (index s.row)

def outside (s : Case) : ℚ[X] :=
  (if s.atG then 3+2*ell s+3*c s+k s*(1+2*cosine s+(1+2*eta s)*sine s)
    else 3*k s+2*ell s+3*c s+1+2*cosine s+(1+2*eta s)*sine s)+
    correction s+c s*slope s*removed s+
    (if diagonal s.row then 0 else nu s*(shortCosine s-1))
def squaredNorm (s : Case) (i : Fin 4) : ℚ[X] :=
  (first s i)^2+(second s i)^2-
    (if !diagonal s.row && decide (i.val=(index s.row).val)
      then 2*first s i*second s i*shortSine s else 0)
def rowSquare (s : Case) (i : Fin 5) : ℚ[X] :=
  if hi : i.val<4 then squaredNorm s ⟨i.val,hi⟩ else 1+(eta s)^2
def rowWeight (s : Case) (i : Fin 5) : ℚ[X] :=
  if i.val<4 then 1 else if s.atG then k s*sine s else sine s
def massAt (s : Case) (i : Fin 5) : ℚ[X] := SoleScalarPolynomials.newtonMass (rowSquare s i)
def mass (s : Case) : ℚ[X] := ∏i : Fin 5,massAt s i
def massExcept (s : Case) (i : Fin 5) : ℚ[X] := ∏j : Fin 5,if j=i then 1 else massAt s j
def certificate (s : Case) : ℚ[X] :=
  2*outside s*mass s-C radiusUpper*
    ∑i : Fin 5,rowWeight s i*(rowSquare s i+(massAt s i)^2)*massExcept s i
def middleQuotient (face : Bool) : ℚ[X] :=
  (certificate ⟨.tdMiddleDiagonal,face⟩-C ((certificate ⟨.tdMiddleDiagonal,face⟩).coeff 0)).divX

/-! ## Kernel certificates

Each polynomial is mirrored by a `Certificate.Scaled` integer list (module
`PolynomialCertificates`); the kernel evaluates the lists, one interval row per
declaration. -/

private def sineL : Scaled := ⟨[0, 1307674368000, 0, -217945728000, 0, 10897286400, 0,
  -259459200, 0, 3603600, 0, -32760, 0, 210, 0, -1], 1307674368000⟩
private def cosineL : Scaled := ⟨[20922789888000, 0, -10461394944000, 0, 871782912000, 0,
  -29059430400, 0, 518918400, 0, -5765760, 0, 43680, 0, -240, 0, 1], 20922789888000⟩

/-- `p(q + X)` as a centering on `[q - 1, q + 1]`. -/
private def shiftQ (q : ℚ) (c : Scaled) : Scaled := c.center 1 q.den q.num q.den

private def parL (s : Case) : Scaled := (const (origin s.row)).add var
private def sineS (s : Case) : Scaled := shiftQ (origin s.row) sineL
private def cosineS (s : Case) : Scaled := shiftQ (origin s.row) cosineL
private def shortL (s : Case) (c : Scaled) : Scaled :=
  if diagonal s.row then c.center 0 1 0 0 else shiftQ (origin s.row - cap s.row) c
private def shortSineS (s : Case) : Scaled := shortL s sineL
private def shortCosineS (s : Case) : Scaled := shortL s cosineL
private def removedS (s : Case) : Scaled := if diagonal s.row then parL s else const (cap s.row)

private def quadL (s : Case) (a b c : ℚ) : Scaled :=
  ((const a).add ((const b).mul (parL s))).add ((const c).mul ((parL s).pow 2))

private def kS (s : Case) : Scaled :=
  if band s.row = .low then quadL s (17253/20000) (67/100) (27/100) else ofNat 1

private def ellS (s : Case) : Scaled :=
  match band s.row with
  | .low => quadL s (50521/100000) (21/25) (1/2)
  | .middle => quadL s (551/1000) (67/100) (21/100)
  | .high => (const (7/10)).add ((const (8/25)).mul (parL s))

private def cS (s : Case) : Scaled :=
  match band s.row with
  | .low => quadL s (17253/20000) (18/25) (3/10)
  | .middle => quadL s (891/1000) (16/25) (1/50)
  | .high => const (113/100)

private def etaS (s : Case) : Scaled :=
  match band s.row with
  | .low => quadL s (131/500) (19/100) (2/25)
  | .middle => (((const (61/200)).sub ((const (1/50)).mul (parL s))).add
      ((const (7/200)).mul ((parL s).pow 2)))
  | .high => (const (27/100)).add ((const (2/25)).mul (parL s))

private def slopeS (s : Case) : Scaled :=
  if isTD s.row then ((const (13/12)).sub ((const (1/5)).mul (removedS s))).add
    ((const (8/25)).mul ((removedS s).pow 2)) else const (21/20)

private def correctionS (s : Case) : Scaled :=
  if isTD s.row && decide (band s.row ≠ .low) then (const (8/25)).mul (((cS s).sub (ofNat 1)).pow 2)
  else ⟨[], 1⟩

private def pS (s : Case) : Scaled := (cosineS s).add ((etaS s).mul (sineS s))
private def firstS (s : Case) : Fin 4 → Scaled :=
  ![if s.atG then ofNat 1 else pS s, kS s, ellS s, ofNat 1]
private def secondS (s : Case) : Fin 4 → Scaled :=
  ![if s.atG then (kS s).mul (pS s) else kS s, ellS s, cS s, cS s]
private def nuS (s : Case) : Scaled := ![const (53/50), ellS s, cS s] (index s.row)

private def outsideG (s : Case) : Scaled :=
  (((ofNat 3).add ((ofNat 2).mul (ellS s))).add ((ofNat 3).mul (cS s))).add
    ((kS s).mul (((ofNat 1).add ((ofNat 2).mul (cosineS s))).add
      (((ofNat 1).add ((ofNat 2).mul (etaS s))).mul (sineS s))))

private def outsideE (s : Case) : Scaled :=
  (((((((ofNat 3).mul (kS s)).add ((ofNat 2).mul (ellS s))).add ((ofNat 3).mul (cS s))).add
    (ofNat 1)).add ((ofNat 2).mul (cosineS s))).add
    (((ofNat 1).add ((ofNat 2).mul (etaS s))).mul (sineS s)))

private def outsideS (s : Case) : Scaled :=
  ((((if s.atG then outsideG s else outsideE s).add (correctionS s)).add
    (((cS s).mul (slopeS s)).mul (removedS s))).add
    (if diagonal s.row then ⟨[], 1⟩ else (nuS s).mul ((shortCosineS s).sub (ofNat 1))))

private def squaredNormS (s : Case) (i : Fin 4) : Scaled :=
  (((firstS s i).pow 2).add ((secondS s i).pow 2)).sub
    (if !diagonal s.row && decide (i.val = (index s.row).val)
      then (((ofNat 2).mul (firstS s i)).mul (secondS s i)).mul (shortSineS s) else ⟨[], 1⟩)

private def rowSquareS (s : Case) (i : Fin 5) : Scaled :=
  if hi : i.val < 4 then squaredNormS s ⟨i.val, hi⟩ else (ofNat 1).add ((etaS s).pow 2)

private def rowWeightS (s : Case) (i : Fin 5) : Scaled :=
  if i.val < 4 then ofNat 1 else if s.atG then (kS s).mul (sineS s) else sineS s

private def coeffQ (c : Scaled) (i : ℕ) : ℚ := (c.l.getD i 0 : ℚ) / c.s

private def truncL (c : Scaled) : Scaled :=
  (((const (coeffQ c 0)).add ((const (coeffQ c 1)).mul var)).add
    ((const (coeffQ c 2)).mul (var.pow 2))).add ((const (coeffQ c 3)).mul (var.pow 3))

private def massInner (c : Scaled) : Scaled :=
  let v0 := coeffQ c 0
  let w := (const (1/v0)).mul ((truncL c).sub (const v0))
  (const (SoleScalarPolynomials.newton v0 3)).mul
    ((((ofNat 1).add ((const (1/2)).mul w)).sub ((const (1/8)).mul (w.pow 2))).add
      ((const (1/16)).mul (w.pow 3)))

private def newtonMassL (c : Scaled) : Scaled := truncL (massInner c)
private def massAtS (s : Case) (i : Fin 5) : Scaled := newtonMassL (rowSquareS s i)
private def massS (s : Case) : Scaled :=
  ((((massAtS s 0).mul (massAtS s 1)).mul (massAtS s 2)).mul (massAtS s 3)).mul (massAtS s 4)
private def exceptS (s : Case) (i j : Fin 5) : Scaled := if j = i then ofNat 1 else massAtS s j
private def massExceptS (s : Case) (i : Fin 5) : Scaled :=
  ((((exceptS s i 0).mul (exceptS s i 1)).mul (exceptS s i 2)).mul (exceptS s i 3)).mul (exceptS s i 4)
private def termS (s : Case) (i : Fin 5) : Scaled :=
  ((rowWeightS s i).mul ((rowSquareS s i).add ((massAtS s i).pow 2))).mul (massExceptS s i)

private def certS (s : Case) : Scaled :=
  (((ofNat 2).mul (outsideS s)).mul (massS s)).sub
    ((const radiusUpper).mul (((((termS s 0).add (termS s 1)).add (termS s 2)).add (termS s 3)).add
      (termS s 4)))

/-- Centering on `[0, length r]`. -/
private def cen (r : Row) (c : Scaled) : Scaled :=
  c.center (length r).num.toNat (2 * (length r).den) 1 1

private def loCheck (D : ℕ) (c : Scaled) (r : ℚ) : Bool :=
  decide (c.l.length ≤ D+1) &&
    decide (r < (lowerZ D (fun j => (chebList c.l).getD j 0) : ℚ)/(c.s*2^c.l.length/2))

private def upCheck (D : ℕ) (c : Scaled) (r : ℚ) : Bool :=
  decide (c.l.length ≤ D+1) &&
    decide ((upperZ D (fun j => (chebList c.l).getD j 0) : ℚ)/(c.s*2^c.l.length/2) < r)

/-- The four whole-interval bounds of a row and its Newton mass. -/
private def rowCheck (s : Case) (i : Fin 5) : Bool :=
  loCheck 38 (cen s.row (rowSquareS s i)) (79/100) && upCheck 38 (cen s.row (rowSquareS s i)) 3 &&
  loCheck 3 (cen s.row (massAtS s i)) (89/100) && upCheck 3 (cen s.row (massAtS s i)) (151/100)

private def rowsCheck (s : Case) : Bool :=
  rowCheck s 0 && rowCheck s 1 && rowCheck s 2 && rowCheck s 3 && rowCheck s 4

private def middleOK (s : Case) : Bool :=
  decide ((119/50000 : ℚ) < coeffQ (certS s) 0) && loCheck 49 (cen s.row (certS s).divX) (9/1250)

/-- The certificate checks of one scalar. -/
private def certOK (s : Case) : Bool :=
  decide ((cen s.row (certS s)).l.length ≤ 50+1) &&
    (if s.row = .tdMiddleDiagonal then middleOK s else loCheck 50 (cen s.row (certS s)) (1/250))

/-- All checks of the two scalars of one interval row. -/
private def rowOK (r : Row) : Bool :=
  certOK ⟨r, false⟩ && certOK ⟨r, true⟩ && rowsCheck ⟨r, false⟩ && rowsCheck ⟨r, true⟩

/-! ### The kernel checks, one declaration per interval row -/

private theorem rowOK_tdLowZero : rowOK .tdLowZero = true := by decide +kernel

private theorem rowOK_tdLowReturn : rowOK .tdLowReturn = true := by decide +kernel

private theorem rowOK_tdMiddleDiagonal : rowOK .tdMiddleDiagonal = true := by decide +kernel

private theorem rowOK_btLowDiagonal : rowOK .btLowDiagonal = true := by decide +kernel

private theorem rowOK_tdMiddle0 : rowOK (.tdMiddle 0) = true := by decide +kernel

private theorem rowOK_tdMiddle1 : rowOK (.tdMiddle 1) = true := by decide +kernel

private theorem rowOK_tdMiddle2 : rowOK (.tdMiddle 2) = true := by decide +kernel

private theorem rowOK_tdHigh0 : rowOK (.tdHigh 0) = true := by decide +kernel

private theorem rowOK_tdHigh1 : rowOK (.tdHigh 1) = true := by decide +kernel

private theorem rowOK_tdHigh2 : rowOK (.tdHigh 2) = true := by decide +kernel

private theorem rowOK_btLowZero0 : rowOK (.btLowZero 0) = true := by decide +kernel

private theorem rowOK_btLowZero1 : rowOK (.btLowZero 1) = true := by decide +kernel

private theorem rowOK_btLowZero2 : rowOK (.btLowZero 2) = true := by decide +kernel

private theorem rowOK_btLowReturn0 : rowOK (.btLowReturn 0) = true := by decide +kernel

private theorem rowOK_btLowReturn1 : rowOK (.btLowReturn 1) = true := by decide +kernel

private theorem rowOK_btLowReturn2 : rowOK (.btLowReturn 2) = true := by decide +kernel

private theorem rowOK_btMiddle0 : rowOK (.btMiddle 0) = true := by decide +kernel

private theorem rowOK_btMiddle1 : rowOK (.btMiddle 1) = true := by decide +kernel

private theorem rowOK_btMiddle2 : rowOK (.btMiddle 2) = true := by decide +kernel

private theorem rowOK_btHigh0 : rowOK (.btHigh 0) = true := by decide +kernel

private theorem rowOK_btHigh1 : rowOK (.btHigh 1) = true := by decide +kernel

private theorem rowOK_btHigh2 : rowOK (.btHigh 2) = true := by decide +kernel

/-! ### The lists represent the scalars -/

private theorem sineL_rep : sineL.Rep PositiveScalarPolynomials.sine := by
  unfold Certificate.Scaled.Rep
  apply Polynomial.funext; intro x
  simp only [sineL, Certificate.toPoly, PositiveScalarPolynomials.sine, eval_mul, eval_C, eval_add,
    eval_X, eval_sub, eval_pow, eval_zero]
  push_cast; ring

private theorem cosineL_rep : cosineL.Rep PositiveScalarPolynomials.cosine := by
  unfold Certificate.Scaled.Rep
  apply Polynomial.funext; intro x
  simp only [cosineL, Certificate.toPoly, PositiveScalarPolynomials.cosine, eval_mul, eval_C,
    eval_add, eval_X, eval_sub, eval_pow, eval_zero, eval_one]
  push_cast; ring

private theorem shiftQ_rep (q : ℚ) {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (shiftQ q c).Rep (p.comp (C q + X)) := by
  have e : C q + X = affine (q - 1) (q + 1) := by
    simp only [affine]; congr 1 <;> ring_nf; simp
  rw [e]
  exact hc.centered 1 q.den q.num q.den (Rat.den_ne_zero _)
    (by push_cast; rw [one_mul, Rat.num_div_den]; ring)
    (by push_cast; rw [one_mul, div_self (by exact_mod_cast Rat.den_ne_zero _)]; ring)

private theorem parL_rep (s : Case) : (parL s).Rep (parameter s) := (rep_const _).add rep_var

private theorem sineS_rep (s : Case) : (sineS s).Rep (sine s) := shiftQ_rep _ sineL_rep
private theorem cosineS_rep (s : Case) : (cosineS s).Rep (cosine s) := shiftQ_rep _ cosineL_rep

private theorem shortL_rep (s : Case) {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (shortL s c).Rep (p.comp (angle s)) := by
  unfold shortL angle removed
  split_ifs with h
  · have e : parameter s - parameter s = affine 0 0 := by simp [affine]
    rw [e]
    exact hc.centered 0 1 0 0 one_ne_zero (by norm_num) (by norm_num)
  · have e : parameter s - C (cap s.row) = C (origin s.row - cap s.row) + X := by
      simp only [parameter, map_sub]; ring
    rw [e]
    exact shiftQ_rep _ hc

private theorem shortSineS_rep (s : Case) : (shortSineS s).Rep (shortSine s) :=
  shortL_rep s sineL_rep
private theorem shortCosineS_rep (s : Case) : (shortCosineS s).Rep (shortCosine s) :=
  shortL_rep s cosineL_rep

private theorem removedS_rep (s : Case) : (removedS s).Rep (removed s) := by
  unfold removedS removed; split_ifs
  · exact parL_rep s
  · exact rep_const _

private theorem quadL_rep (s : Case) (a b c : ℚ) :
    (quadL s a b c).Rep (C a + C b * parameter s + C c * (parameter s)^2) :=
  ((rep_const a).add ((rep_const b).mul (parL_rep s))).add ((rep_const c).mul ((parL_rep s).pow 2))

private theorem kS_rep (s : Case) : (kS s).Rep (k s) := by
  unfold kS k; split_ifs
  · exact quadL_rep s _ _ _
  · exact rep_one

private theorem ellS_rep (s : Case) : (ellS s).Rep (ell s) := by
  unfold ellS ell
  generalize band s.row = b
  cases b
  · exact quadL_rep s _ _ _
  · exact quadL_rep s _ _ _
  · exact (rep_const _).add ((rep_const _).mul (parL_rep s))

private theorem cS_rep (s : Case) : (cS s).Rep (c s) := by
  unfold cS c
  generalize band s.row = b
  cases b
  · exact quadL_rep s _ _ _
  · exact quadL_rep s _ _ _
  · exact rep_const _

private theorem etaS_rep (s : Case) : (etaS s).Rep (eta s) := by
  unfold etaS eta
  generalize band s.row = b
  cases b
  · exact quadL_rep s _ _ _
  · exact ((rep_const _).sub ((rep_const _).mul (parL_rep s))).add
      ((rep_const _).mul ((parL_rep s).pow 2))
  · exact (rep_const _).add ((rep_const _).mul (parL_rep s))

private theorem slopeS_rep (s : Case) : (slopeS s).Rep (slope s) := by
  unfold slopeS slope; split_ifs
  · exact ((rep_const _).sub ((rep_const _).mul (removedS_rep s))).add
      ((rep_const _).mul ((removedS_rep s).pow 2))
  · exact rep_const _

private theorem correctionS_rep (s : Case) : (correctionS s).Rep (correction s) := by
  unfold correctionS correction; split_ifs
  · exact (rep_const _).mul (((cS_rep s).sub rep_one).pow 2)
  · exact rep_zero

private theorem pS_rep (s : Case) : (pS s).Rep (p s) :=
  (cosineS_rep s).add ((etaS_rep s).mul (sineS_rep s))

private theorem firstS_rep (s : Case) (i : Fin 4) : (firstS s i).Rep (first s i) := by
  fin_cases i
  · show (if s.atG then ofNat 1 else pS s).Rep (if s.atG then 1 else p s)
    split_ifs
    · exact rep_one
    · exact pS_rep s
  · exact kS_rep s
  · exact ellS_rep s
  · exact rep_one

private theorem secondS_rep (s : Case) (i : Fin 4) : (secondS s i).Rep (second s i) := by
  fin_cases i
  · show (if s.atG then (kS s).mul (pS s) else kS s).Rep (if s.atG then k s * p s else k s)
    split_ifs
    · exact (kS_rep s).mul (pS_rep s)
    · exact kS_rep s
  · exact ellS_rep s
  · exact cS_rep s
  · exact cS_rep s

private theorem nuS_rep (s : Case) : (nuS s).Rep (nu s) := by
  unfold nuS nu
  generalize index s.row = i
  fin_cases i
  · exact rep_const _
  · exact ellS_rep s
  · exact cS_rep s

private theorem outsideS_rep (s : Case) : (outsideS s).Rep (outside s) := by
  unfold outsideS outside
  refine (((?_ : Certificate.Scaled.Rep _ _).add (correctionS_rep s)).add
    (((cS_rep s).mul (slopeS_rep s)).mul (removedS_rep s))).add ?_
  · split_ifs
    · exact (((rep_ofNat 3).add ((rep_ofNat 2).mul (ellS_rep s))).add ((rep_ofNat 3).mul (cS_rep s))).add
        ((kS_rep s).mul ((rep_one.add ((rep_ofNat 2).mul (cosineS_rep s))).add
          ((rep_one.add ((rep_ofNat 2).mul (etaS_rep s))).mul (sineS_rep s))))
    · exact ((((((rep_ofNat 3).mul (kS_rep s)).add ((rep_ofNat 2).mul (ellS_rep s))).add
        ((rep_ofNat 3).mul (cS_rep s))).add rep_one).add ((rep_ofNat 2).mul (cosineS_rep s))).add
        ((rep_one.add ((rep_ofNat 2).mul (etaS_rep s))).mul (sineS_rep s))
  · split_ifs
    · exact rep_zero
    · exact (nuS_rep s).mul ((shortCosineS_rep s).sub rep_one)

private theorem squaredNormS_rep (s : Case) (i : Fin 4) : (squaredNormS s i).Rep (squaredNorm s i) := by
  unfold squaredNormS squaredNorm
  refine (((firstS_rep s i).pow 2).add ((secondS_rep s i).pow 2)).sub ?_
  split_ifs
  · exact (((rep_ofNat 2).mul (firstS_rep s i)).mul (secondS_rep s i)).mul (shortSineS_rep s)
  · exact rep_zero

private theorem rowSquareS_rep (s : Case) (i : Fin 5) : (rowSquareS s i).Rep (rowSquare s i) := by
  unfold rowSquareS rowSquare
  split_ifs
  · exact squaredNormS_rep s _
  · exact rep_one.add ((etaS_rep s).pow 2)

private theorem rowWeightS_rep (s : Case) (i : Fin 5) : (rowWeightS s i).Rep (rowWeight s i) := by
  unfold rowWeightS rowWeight
  split_ifs
  · exact rep_one
  · exact (kS_rep s).mul (sineS_rep s)
  · exact sineS_rep s

private theorem truncL_rep {c : Scaled} {v : ℚ[X]} (hc : c.Rep v) (hs : c.s ≠ 0) :
    (truncL c).Rep (SoleScalarPolynomials.truncateThree v) := by
  unfold SoleScalarPolynomials.truncateThree
  rw [hc.coeff hs 0, hc.coeff hs 1, hc.coeff hs 2, hc.coeff hs 3]
  exact (((rep_const _).add ((rep_const _).mul rep_var)).add ((rep_const _).mul (rep_var.pow 2))).add
    ((rep_const _).mul (rep_var.pow 3))

private theorem newtonMassL_rep {c : Scaled} {v : ℚ[X]} (hc : c.Rep v) (hs : c.s ≠ 0) :
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

/-! ### The scales are positive -/

private theorem quadL_s (s : Case) (a b c : ℚ) : (quadL s a b c).s ≠ 0 := by
  simp only [quadL, parL, Certificate.Scaled.add, Certificate.Scaled.mul, Certificate.Scaled.pow,
    Certificate.Scaled.const, Certificate.Scaled.var]
  repeat' (first | apply mul_ne_zero | apply pow_ne_zero | exact Rat.den_ne_zero _ | exact one_ne_zero)

private theorem shiftQ_s (q : ℚ) {c : Scaled} (hc : c.s ≠ 0) : (shiftQ q c).s ≠ 0 := by
  simp only [shiftQ, Certificate.Scaled.center]
  exact mul_ne_zero hc (pow_ne_zero _ (Rat.den_ne_zero _))

private theorem sineL_s : sineL.s ≠ 0 := by simp [sineL]
private theorem cosineL_s : cosineL.s ≠ 0 := by simp [cosineL]
private theorem sineS_s (s : Case) : (sineS s).s ≠ 0 := shiftQ_s _ sineL_s
private theorem cosineS_s (s : Case) : (cosineS s).s ≠ 0 := shiftQ_s _ cosineL_s

private theorem shortL_s (s : Case) {c : Scaled} (hc : c.s ≠ 0) : (shortL s c).s ≠ 0 := by
  unfold shortL; split_ifs
  · simp only [Certificate.Scaled.center]; exact mul_ne_zero hc (pow_ne_zero _ one_ne_zero)
  · exact shiftQ_s _ hc

private theorem parL_s (s : Case) : (parL s).s ≠ 0 := by
  simp only [parL, Certificate.Scaled.add, Certificate.Scaled.const, Certificate.Scaled.var]
  exact mul_ne_zero (Rat.den_ne_zero _) one_ne_zero

private theorem removedS_s (s : Case) : (removedS s).s ≠ 0 := by
  unfold removedS; split_ifs
  · exact parL_s s
  · exact Rat.den_ne_zero _

private theorem kS_s (s : Case) : (kS s).s ≠ 0 := by
  unfold kS; split_ifs; exacts [quadL_s _ _ _ _, one_ne_zero]

private theorem ellS_s (s : Case) : (ellS s).s ≠ 0 := by
  unfold ellS; generalize band s.row = b; cases b
  · exact quadL_s _ _ _ _
  · exact quadL_s _ _ _ _
  · simp only [Certificate.Scaled.add, Certificate.Scaled.mul, Certificate.Scaled.const]
    exact mul_ne_zero (Rat.den_ne_zero _) (mul_ne_zero (Rat.den_ne_zero _) (parL_s s))

private theorem cS_s (s : Case) : (cS s).s ≠ 0 := by
  unfold cS; generalize band s.row = b; cases b
  · exact quadL_s _ _ _ _
  · exact quadL_s _ _ _ _
  · exact Rat.den_ne_zero _

private theorem etaS_s (s : Case) : (etaS s).s ≠ 0 := by
  unfold etaS; generalize band s.row = b; cases b
  · exact quadL_s _ _ _ _
  · simp only [Certificate.Scaled.add, Certificate.Scaled.sub, Certificate.Scaled.mul,
      Certificate.Scaled.pow, Certificate.Scaled.const]
    exact mul_ne_zero (mul_ne_zero (Rat.den_ne_zero _) (mul_ne_zero (Rat.den_ne_zero _) (parL_s s)))
      (mul_ne_zero (Rat.den_ne_zero _) (pow_ne_zero _ (parL_s s)))
  · simp only [Certificate.Scaled.add, Certificate.Scaled.mul, Certificate.Scaled.const]
    exact mul_ne_zero (Rat.den_ne_zero _) (mul_ne_zero (Rat.den_ne_zero _) (parL_s s))

private theorem slopeS_s (s : Case) : (slopeS s).s ≠ 0 := by
  unfold slopeS; split_ifs
  · simp only [Certificate.Scaled.add, Certificate.Scaled.sub, Certificate.Scaled.mul,
      Certificate.Scaled.pow, Certificate.Scaled.const]
    exact mul_ne_zero (mul_ne_zero (Rat.den_ne_zero _) (mul_ne_zero (Rat.den_ne_zero _)
      (removedS_s s))) (mul_ne_zero (Rat.den_ne_zero _) (pow_ne_zero _ (removedS_s s)))
  · exact Rat.den_ne_zero _

private theorem correctionS_s (s : Case) : (correctionS s).s ≠ 0 := by
  unfold correctionS; split_ifs
  · simp only [Certificate.Scaled.sub, Certificate.Scaled.mul, Certificate.Scaled.pow,
      Certificate.Scaled.const, Certificate.Scaled.ofNat]
    exact mul_ne_zero (Rat.den_ne_zero _) (pow_ne_zero _ (mul_ne_zero (cS_s s) one_ne_zero))
  · exact one_ne_zero

private theorem pS_s (s : Case) : (pS s).s ≠ 0 := by
  simp only [pS, Certificate.Scaled.add, Certificate.Scaled.mul]
  exact mul_ne_zero (cosineS_s s) (mul_ne_zero (etaS_s s) (sineS_s s))

private theorem firstS_s (s : Case) (j : Fin 4) : (firstS s j).s ≠ 0 := by
  fin_cases j
  · show (if s.atG then ofNat 1 else pS s).s ≠ 0
    split_ifs; exacts [one_ne_zero, pS_s s]
  · exact kS_s s
  · exact ellS_s s
  · exact one_ne_zero

private theorem secondS_s (s : Case) (j : Fin 4) : (secondS s j).s ≠ 0 := by
  fin_cases j
  · show (if s.atG then (kS s).mul (pS s) else kS s).s ≠ 0
    split_ifs
    · exact mul_ne_zero (kS_s s) (pS_s s)
    · exact kS_s s
  · exact ellS_s s
  · exact cS_s s
  · exact cS_s s

private theorem nuS_s (s : Case) : (nuS s).s ≠ 0 := by
  unfold nuS; generalize index s.row = j; fin_cases j
  exacts [Rat.den_ne_zero _, ellS_s s, cS_s s]

private theorem rowSquareS_s (s : Case) (i : Fin 5) : (rowSquareS s i).s ≠ 0 := by
  unfold rowSquareS
  split_ifs
  · simp only [squaredNormS, Certificate.Scaled.add, Certificate.Scaled.sub, Certificate.Scaled.mul,
      Certificate.Scaled.pow, Certificate.Scaled.ofNat]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (firstS_s _ _)) (pow_ne_zero _ (secondS_s _ _))) ?_
    split_ifs
    · exact mul_ne_zero (mul_ne_zero (mul_ne_zero one_ne_zero (firstS_s _ _)) (secondS_s _ _))
        (shortL_s s sineL_s)
    · exact one_ne_zero
  · simp only [Certificate.Scaled.add, Certificate.Scaled.pow, Certificate.Scaled.ofNat]
    exact mul_ne_zero one_ne_zero (pow_ne_zero _ (etaS_s s))

private theorem massAtS_s (s : Case) (i : Fin 5) : (massAtS s i).s ≠ 0 := by
  simp only [massAtS, newtonMassL, truncL, Certificate.Scaled.add, Certificate.Scaled.mul,
    Certificate.Scaled.pow, Certificate.Scaled.const, Certificate.Scaled.var]
  repeat' (first | apply mul_ne_zero | apply pow_ne_zero | exact Rat.den_ne_zero _ | exact one_ne_zero)

private theorem massAtS_rep (s : Case) (i : Fin 5) : (massAtS s i).Rep (massAt s i) :=
  newtonMassL_rep (rowSquareS_rep s i) (rowSquareS_s s i)

private theorem massS_rep (s : Case) : (massS s).Rep (mass s) := by
  unfold massS mass
  rw [Fin.prod_univ_five]
  exact ((((massAtS_rep s 0).mul (massAtS_rep s 1)).mul (massAtS_rep s 2)).mul
    (massAtS_rep s 3)).mul (massAtS_rep s 4)

private theorem exceptS_rep (s : Case) (i j : Fin 5) :
    (exceptS s i j).Rep (if j = i then 1 else massAt s j) := by
  unfold exceptS; split_ifs
  · exact rep_one
  · exact massAtS_rep s j

private theorem massExceptS_rep (s : Case) (i : Fin 5) : (massExceptS s i).Rep (massExcept s i) := by
  unfold massExceptS massExcept
  rw [Fin.prod_univ_five]
  exact ((((exceptS_rep s i 0).mul (exceptS_rep s i 1)).mul (exceptS_rep s i 2)).mul
    (exceptS_rep s i 3)).mul (exceptS_rep s i 4)

private theorem termS_rep (s : Case) (i : Fin 5) :
    (termS s i).Rep (rowWeight s i * (rowSquare s i + (massAt s i)^2) * massExcept s i) :=
  ((rowWeightS_rep s i).mul ((rowSquareS_rep s i).add ((massAtS_rep s i).pow 2))).mul
    (massExceptS_rep s i)

private theorem certS_rep (s : Case) : (certS s).Rep (certificate s) := by
  unfold certS certificate
  rw [Fin.sum_univ_five]
  exact (((rep_ofNat 2).mul (outsideS_rep s)).mul (massS_rep s)).sub
    ((rep_const _).mul (((((termS_rep s 0).add (termS_rep s 1)).add (termS_rep s 2)).add
      (termS_rep s 3)).add (termS_rep s 4)))

private theorem outsideS_s (s : Case) : (outsideS s).s ≠ 0 := by
  have h2 : ∀ n, (ofNat n).s ≠ 0 := fun _ => one_ne_zero
  have hG : (outsideG s).s ≠ 0 := by
    simp only [outsideG, Certificate.Scaled.add, Certificate.Scaled.mul]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (h2 3) (mul_ne_zero (h2 2) (ellS_s s)))
      (mul_ne_zero (h2 3) (cS_s s))) (mul_ne_zero (kS_s s) (mul_ne_zero (mul_ne_zero (h2 1)
      (mul_ne_zero (h2 2) (cosineS_s s))) (mul_ne_zero (mul_ne_zero (h2 1) (mul_ne_zero (h2 2)
      (etaS_s s))) (sineS_s s))))
  have hE : (outsideE s).s ≠ 0 := by
    simp only [outsideE, Certificate.Scaled.add, Certificate.Scaled.mul]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (h2 3) (kS_s s))
      (mul_ne_zero (h2 2) (ellS_s s))) (mul_ne_zero (h2 3) (cS_s s))) (h2 1))
      (mul_ne_zero (h2 2) (cosineS_s s))) (mul_ne_zero (mul_ne_zero (h2 1) (mul_ne_zero (h2 2)
      (etaS_s s))) (sineS_s s))
  have hI : (if s.atG then outsideG s else outsideE s).s ≠ 0 := by split_ifs; exacts [hG, hE]
  have hD : (if diagonal s.row then (⟨[], 1⟩ : Scaled) else (nuS s).mul ((shortCosineS s).sub
      (ofNat 1))).s ≠ 0 := by
    split_ifs
    · exact one_ne_zero
    · simp only [Certificate.Scaled.mul, Certificate.Scaled.sub]
      exact mul_ne_zero (nuS_s s) (mul_ne_zero (shortL_s s cosineL_s) one_ne_zero)
  unfold outsideS
  simp only [Certificate.Scaled.add, Certificate.Scaled.mul]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hI (correctionS_s s))
    (mul_ne_zero (mul_ne_zero (cS_s s) (slopeS_s s)) (removedS_s s))) hD

private theorem massS_s (s : Case) : (massS s).s ≠ 0 := by
  unfold massS; simp only [Certificate.Scaled.mul]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (massAtS_s s 0) (massAtS_s s 1))
    (massAtS_s s 2)) (massAtS_s s 3)) (massAtS_s s 4)

private theorem exceptS_s (s : Case) (i j : Fin 5) : (exceptS s i j).s ≠ 0 := by
  unfold exceptS; split_ifs; exacts [one_ne_zero, massAtS_s s j]

private theorem termS_s (s : Case) (i : Fin 5) : (termS s i).s ≠ 0 := by
  have hw : (rowWeightS s i).s ≠ 0 := by
    unfold rowWeightS; split_ifs
    · exact one_ne_zero
    · exact mul_ne_zero (kS_s s) (sineS_s s)
    · exact sineS_s s
  unfold termS massExceptS; simp only [Certificate.Scaled.mul, Certificate.Scaled.add,
    Certificate.Scaled.pow]
  exact mul_ne_zero (mul_ne_zero hw (mul_ne_zero (rowSquareS_s s i) (pow_ne_zero _ (massAtS_s s i))))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (exceptS_s s i 0) (exceptS_s s i 1))
    (exceptS_s s i 2)) (exceptS_s s i 3)) (exceptS_s s i 4))

private theorem certS_s (s : Case) : (certS s).s ≠ 0 := by
  unfold certS; simp only [Certificate.Scaled.add, Certificate.Scaled.sub, Certificate.Scaled.mul]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero one_ne_zero (outsideS_s s)) (massS_s s))
    (mul_ne_zero (Rat.den_ne_zero _) (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (termS_s s 0) (termS_s s 1)) (termS_s s 2)) (termS_s s 3)) (termS_s s 4)))

/-! ### Centering and the checked bounds -/

private theorem half_eq (L : ℚ) (hL : 0 < L) :
    L / 2 = ((L.num.toNat : ℕ) : ℚ) * ((1:ℤ) : ℚ) / ((2 * L.den : ℕ) : ℚ) := by
  have hn : ((L.num.toNat : ℕ) : ℚ) = L.num := by
    have : 0 ≤ L.num := Rat.num_nonneg.mpr hL.le
    exact_mod_cast Int.toNat_of_nonneg this
  have hd : (L.den : ℚ) ≠ 0 := by exact_mod_cast L.den_ne_zero
  rw [hn]
  conv_lhs => rw [← Rat.num_div_den L]
  push_cast
  field_simp

private theorem cen_rep (r : Row) {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (cen r c).Rep (centered 0 (length r) p) := by
  have hL := ExceptionalNegativeTScalarModel.length_pos r
  unfold cen
  exact hc.centered _ _ 1 1 (by simp) (by rw [zero_add, half_eq _ hL])
    (by rw [sub_zero, half_eq _ hL])

private theorem cen_s (r : Row) {c : Scaled} (hc : c.s ≠ 0) : (cen r c).s ≠ 0 := by
  unfold cen Certificate.Scaled.center
  exact mul_ne_zero hc (pow_ne_zero _ (mul_ne_zero two_ne_zero (Rat.den_ne_zero _)))

private theorem lo_of_check {D : ℕ} {a b r : ℚ} {c : Scaled} {p : ℚ[X]} (hc : c.Rep (centered a b p))
    (hs : c.s ≠ 0) (h : loCheck D c r = true) :
    r < lowerOn D a b p ∧ centered a b p = expansion D (centered a b p) := by
  simp only [loCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨by rw [lowerOn_eq_of_rep hc hs h.1]; exact h.2, hc.eq_expansion hs h.1⟩

private theorem up_of_check {D : ℕ} {a b r : ℚ} {c : Scaled} {p : ℚ[X]} (hc : c.Rep (centered a b p))
    (hs : c.s ≠ 0) (h : upCheck D c r = true) : upperOn D a b p < r := by
  simp only [upCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [upperOn_eq_of_rep hc hs h.1]; exact h.2

private theorem rowOK_all (r : Row) : rowOK r = true := by
  cases r with
  | tdLowZero => exact rowOK_tdLowZero
  | tdLowReturn => exact rowOK_tdLowReturn
  | tdMiddleDiagonal => exact rowOK_tdMiddleDiagonal
  | btLowDiagonal => exact rowOK_btLowDiagonal
  | tdMiddle i =>
      fin_cases i
      exacts [rowOK_tdMiddle0, rowOK_tdMiddle1, rowOK_tdMiddle2]
  | tdHigh i =>
      fin_cases i
      exacts [rowOK_tdHigh0, rowOK_tdHigh1, rowOK_tdHigh2]
  | btLowZero i =>
      fin_cases i
      exacts [rowOK_btLowZero0, rowOK_btLowZero1, rowOK_btLowZero2]
  | btLowReturn i =>
      fin_cases i
      exacts [rowOK_btLowReturn0, rowOK_btLowReturn1, rowOK_btLowReturn2]
  | btMiddle i =>
      fin_cases i
      exacts [rowOK_btMiddle0, rowOK_btMiddle1, rowOK_btMiddle2]
  | btHigh i =>
      fin_cases i
      exacts [rowOK_btHigh0, rowOK_btHigh1, rowOK_btHigh2]

private theorem certOK_all (s : Case) : certOK s = true := by
  have h := rowOK_all s.row
  simp only [rowOK, Bool.and_eq_true] at h
  rcases s with ⟨r, _ | _⟩
  · exact h.1.1.1
  · exact h.1.1.2

private theorem rowsCheck_all (s : Case) : rowsCheck s = true := by
  have h := rowOK_all s.row
  simp only [rowOK, Bool.and_eq_true] at h
  rcases s with ⟨r, _ | _⟩
  · exact h.1.2
  · exact h.2

private theorem rowCheck_spec (s : Case) (i : Fin 5) :
    loCheck 38 (cen s.row (rowSquareS s i)) (79/100) = true ∧
    upCheck 38 (cen s.row (rowSquareS s i)) 3 = true ∧
    loCheck 3 (cen s.row (massAtS s i)) (89/100) = true ∧
    upCheck 3 (cen s.row (massAtS s i)) (151/100) = true := by
  have h := rowsCheck_all s
  simp only [rowsCheck, Bool.and_eq_true] at h
  have h' : rowCheck s i = true := by
    fin_cases i
    exacts [h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2]
  simp only [rowCheck, Bool.and_eq_true] at h'
  exact ⟨h'.1.1.1, h'.1.1.2, h'.1.2, h'.2⟩

private theorem certLen (s : Case) : (cen s.row (certS s)).l.length ≤ 50+1 := by
  have h := certOK_all s
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

private theorem middle_spec (face : Bool) :
    (119/50000 : ℚ) < coeffQ (certS ⟨.tdMiddleDiagonal, face⟩) 0 ∧
    loCheck 49 (cen .tdMiddleDiagonal (certS ⟨.tdMiddleDiagonal, face⟩).divX) (9/1250) = true := by
  have h := certOK_all ⟨.tdMiddleDiagonal, face⟩
  simp only [certOK, ite_true, middleOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem certificate_identity (s : Case) :
    centered 0 (length s.row) (certificate s)=
      expansion 50 (centered 0 (length s.row) (certificate s)) :=
  (cen_rep s.row (certS_rep s)).eq_expansion (cen_s s.row (certS_s s)) (certLen s)

theorem ordinary_reserve (s : Case) (hm : s.row≠.tdMiddleDiagonal) :
    (1/250:ℚ)<lowerOn 50 0 (length s.row) (certificate s) := by
  have h := certOK_all s
  simp only [certOK, hm, ite_false, Bool.and_eq_true] at h
  exact (lo_of_check (cen_rep s.row (certS_rep s)) (cen_s s.row (certS_s s)) h.2).1

theorem middle_identity (face : Bool) :
    certificate ⟨.tdMiddleDiagonal,face⟩=
      C ((certificate ⟨.tdMiddleDiagonal,face⟩).coeff 0)+X*middleQuotient face := by
  have h := X_mul_divX_add (certificate ⟨.tdMiddleDiagonal,face⟩-
    C ((certificate ⟨.tdMiddleDiagonal,face⟩).coeff 0))
  simp only [coeff_sub, coeff_C_zero, sub_self, map_zero, add_zero] at h
  rw [middleQuotient, h]
  ring

private theorem middleQuotient_eq (face : Bool) :
    middleQuotient face = (certificate ⟨.tdMiddleDiagonal,face⟩).divX := by
  ext n
  simp [middleQuotient, coeff_divX, coeff_sub]

private theorem middleQuotient_rep (face : Bool) :
    (certS ⟨.tdMiddleDiagonal,face⟩).divX.Rep (middleQuotient face) := by
  rw [middleQuotient_eq]; exact (certS_rep _).divX

private theorem middle_check (face : Bool) :
    (9/1250:ℚ)<lowerOn 49 0 (3/25) (middleQuotient face) ∧
      centered 0 (3/25) (middleQuotient face)=expansion 49 (centered 0 (3/25) (middleQuotient face)) :=
  lo_of_check (cen_rep .tdMiddleDiagonal (middleQuotient_rep face))
    (cen_s .tdMiddleDiagonal (c := (certS ⟨.tdMiddleDiagonal,face⟩).divX)
      (certS_s ⟨.tdMiddleDiagonal,face⟩)) (middle_spec face).2

theorem middle_quotient_identity (face : Bool) :
    centered 0 (3/25) (middleQuotient face)=
      expansion 49 (centered 0 (3/25) (middleQuotient face)) :=
  (middle_check face).2

theorem middle_reserves (face : Bool) :
    (119/50000:ℚ)<(certificate ⟨.tdMiddleDiagonal,face⟩).coeff 0 ∧
      (9/1250:ℚ)<lowerOn 49 0 (3/25) (middleQuotient face) := by
  refine ⟨?_, (middle_check face).1⟩
  rw [(certS_rep _).coeff (certS_s _) 0]
  exact (middle_spec face).1

theorem certificate_reserve (s : Case) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ)) :
    (119/50000:ℝ)<aeval z (certificate s) := by
  by_cases hm : s.row=.tdMiddleDiagonal
  · rcases s with ⟨r,face⟩
    dsimp at hm
    subst r
    have hz' : z∈Set.Icc ((0:ℚ):ℝ) ((3/25:ℚ):ℝ) := by
      simpa [ExceptionalNegativeTScalarModel.length] using hz
    have hquot := positive_on_interval (by norm_num : (0:ℚ)<3/25)
      (middle_quotient_identity face) (middle_reserves face).2 hz'
    have hzero : (119/50000:ℝ)<((certificate ⟨.tdMiddleDiagonal,face⟩).coeff 0:ℝ) := by
      have := (Rat.cast_lt (K := ℝ)).mpr (middle_reserves face).1; push_cast at this; exact this
    have hz0 : 0 ≤ z := by simpa using hz'.1
    have hprod := mul_nonneg hz0 (show 0≤aeval z (middleQuotient face) by push_cast at hquot; linarith)
    rw [middle_identity]
    simp only [map_add,map_mul,aeval_C,aeval_X]
    simp only [eq_ratCast] at *
    linarith
  · have hb := (interval_bounds (ExceptionalNegativeTScalarModel.length_pos s.row)
      (certificate_identity s) (by simpa using hz)).1
    have hr : (1/250:ℝ)<(lowerOn 50 0 (length s.row) (certificate s):ℝ) := by
      have := (Rat.cast_lt (K := ℝ)).mpr (ordinary_reserve s hm); push_cast at this; exact this
    linarith

theorem mass_identity (s : Case) (i : Fin 5) :
    centered 0 (length s.row) (massAt s i)=
      expansion 3 (centered 0 (length s.row) (massAt s i)) :=
  (lo_of_check (cen_rep s.row (massAtS_rep s i)) (cen_s s.row (massAtS_s s i))
    (rowCheck_spec s i).2.2.1).2

theorem mass_reserves (s : Case) (i : Fin 5) :
    (89/100:ℚ)<lowerOn 3 0 (length s.row) (massAt s i) ∧
      upperOn 3 0 (length s.row) (massAt s i)<151/100 :=
  ⟨(lo_of_check (cen_rep s.row (massAtS_rep s i)) (cen_s s.row (massAtS_s s i))
    (rowCheck_spec s i).2.2.1).1,
    up_of_check (cen_rep s.row (massAtS_rep s i)) (cen_s s.row (massAtS_s s i))
      (rowCheck_spec s i).2.2.2⟩

theorem square_identity (s : Case) (i : Fin 5) :
    centered 0 (length s.row) (rowSquare s i)=
      expansion 38 (centered 0 (length s.row) (rowSquare s i)) :=
  (lo_of_check (cen_rep s.row (rowSquareS_rep s i)) (cen_s s.row (rowSquareS_s s i))
    (rowCheck_spec s i).1).2

theorem square_reserves (s : Case) (i : Fin 5) :
    (79/100:ℚ)<lowerOn 38 0 (length s.row) (rowSquare s i) ∧
      upperOn 38 0 (length s.row) (rowSquare s i)<3 :=
  ⟨(lo_of_check (cen_rep s.row (rowSquareS_rep s i)) (cen_s s.row (rowSquareS_s s i))
    (rowCheck_spec s i).1).1,
    up_of_check (cen_rep s.row (rowSquareS_rep s i)) (cen_s s.row (rowSquareS_s s i))
      (rowCheck_spec s i).2.1⟩

theorem mass_bounds (s : Case) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ)) :
    89/100<aeval z (massAt s i) ∧ aeval z (massAt s i)<151/100 := by
  have hb := interval_bounds (ExceptionalNegativeTScalarModel.length_pos s.row) (mass_identity s i)
    (by simpa using hz)
  have hl : (89/100:ℝ)<(lowerOn 3 0 (length s.row) (massAt s i):ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr (mass_reserves s i).1; push_cast at this; exact this
  have hu : (upperOn 3 0 (length s.row) (massAt s i):ℝ)<(151/100:ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr (mass_reserves s i).2; push_cast at this; exact this
  exact ⟨hl.trans_le hb.1,hb.2.trans_lt hu⟩

theorem square_bounds (s : Case) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ)) :
    79/100<aeval z (rowSquare s i) ∧ aeval z (rowSquare s i)<3 := by
  have hb := interval_bounds (ExceptionalNegativeTScalarModel.length_pos s.row) (square_identity s i)
    (by simpa using hz)
  have hl : (79/100:ℝ)<(lowerOn 38 0 (length s.row) (rowSquare s i):ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr (square_reserves s i).1; push_cast at this; exact this
  have hu : (upperOn 38 0 (length s.row) (rowSquare s i):ℝ)<(3:ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr (square_reserves s i).2; push_cast at this; exact this
  exact ⟨hl.trans_le hb.1,hb.2.trans_lt hu⟩

end SquaresInCircles.Eight.TableFree.ExceptionalNegativeTPolynomials
