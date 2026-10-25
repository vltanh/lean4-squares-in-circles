module

public import SquaresInCircles.Eight.Arithmetic.BivariateCertificates
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsData

/-!
# Eight squares: exact models of the nonnegative-total weights

Exact bivariate models (`BivariateCertificate.XM`) of the polynomials of
`GlobalGA.NonnegativeTotals.Certificate`, for any packing `Config`, each with its `rep_` lemma:
the weights `theta`, `e`, `k`, `l`, `c`, the charge `J`, and the parts `delta`, `qStar`, `jTheta`,
`jE`, `M`, `ABase`, `qB`, `A`, `baseNorm`, `P`, `mass` and `numerator` of the twelve numerators.
The models of `P`, `mass` and `numerator` are reduced (`XM.reduce`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.NonnegativeTotalsMirrors
open Polynomial PackedModels BivariateCertificate TensorWholeIntervalPolynomial
open GlobalGA.NonnegativeTotals

/-- `theta r`. -/
def thetaM (c : Config) : Region → XM
  | .triangle => XM.add c (XM.ofInt c 1 6) (XM.varX c)
  | .rectangle => XM.sub c (XM.ofInt c 1 6) (XM.varX c)

theorem rep_thetaM (c : Config) (r : Region) : (thetaM c r).Rep c (Certificate.theta r) := by
  cases r <;> simp only [thetaM, Certificate.theta] <;> build_xm

/-- `e r`. -/
def eM (c : Config) : Region → XM
  | .triangle => XM.varY c
  | .rectangle => XM.add c (XM.varX c) (XM.varY c)

theorem rep_eM (c : Config) (r : Region) : (eM c r).Rep c (Certificate.e r) := by
  cases r <;> simp only [eM, Certificate.e] <;> build_xm

/-- `k r`. -/
def kM (c : Config) : Region → XM
  | .triangle => XM.add c (XM.add c (XM.sub c (XM.add c (XM.ofInt c 1673 2500)
      (XM.mul c (XM.ofInt c 2609 5000) (XM.varX c)))
      (XM.mul c (XM.ofInt c 1489 2500) (XM.pow c (XM.varX c) 2)))
      (XM.mul c (XM.ofInt c 527 1250) (XM.pow c (XM.varX c) 3)))
      (XM.mul c (XM.ofInt c 7 25) (XM.varY c))
  | .rectangle => XM.add c (XM.add c (XM.ofInt c 1673 2500)
      (XM.mul c (XM.ofInt c 9 50) (XM.varX c))) (XM.mul c (XM.ofInt c 7 25) (XM.varY c))

theorem rep_kM (c : Config) (r : Region) : (kM c r).Rep c (Certificate.k r) := by
  cases r <;> simp only [kM, Certificate.k] <;> build_xm

/-- `l r`. -/
def lM (c : Config) : Region → XM
  | .triangle => XM.add c (XM.add c (XM.sub c (XM.add c (XM.ofInt c 1 1)
      (XM.mul c (XM.ofInt c 7 400) (XM.varX c)))
      (XM.mul c (XM.ofInt c 2733 2500) (XM.pow c (XM.varX c) 2)))
      (XM.mul c (XM.ofInt c 639 500) (XM.pow c (XM.varX c) 3)))
      (XM.mul c (XM.ofInt c 1 4) (XM.varY c))
  | .rectangle => XM.add c (XM.ofInt c 1 1)
      (XM.mul c (XM.ofInt c 1 4) (XM.add c (XM.varX c) (XM.varY c)))

theorem rep_lM (c : Config) (r : Region) : (lM c r).Rep c (Certificate.l r) := by
  cases r <;> simp only [lM, Certificate.l] <;> build_xm

/-- `c r`. -/
def cM (c : Config) : Region → XM
  | .triangle => XM.add c (XM.add c (XM.sub c (XM.sub c (XM.ofInt c 10163 10000)
      (XM.mul c (XM.ofInt c 209 10000) (XM.varX c)))
      (XM.mul c (XM.ofInt c 5743 5000) (XM.pow c (XM.varX c) 2)))
      (XM.mul c (XM.ofInt c 14069 10000) (XM.pow c (XM.varX c) 3)))
      (XM.mul c (XM.ofInt c 1 4) (XM.varY c))
  | .rectangle => XM.add c (XM.ofInt c 10163 10000)
      (XM.mul c (XM.ofInt c 1 4) (XM.add c (XM.varX c) (XM.varY c)))

theorem rep_cM (c : Config) (r : Region) : (cM c r).Rep c (Certificate.c r) := by
  cases r <;> simp only [cM, Certificate.c] <;> build_xm

/-- `J f`, from a model `u` of `f`. -/
def JM (c : Config) (u : XM) : XM :=
  XM.add c (XM.mul c (XM.ofInt c 1 2) (XM.sub c (XM.liftM c u XM.C10L) (XM.ofInt c 1 1)))
    (XM.mul c (XM.ofInt c (-114321959) 125000000) (XM.liftM c u XM.S9L))

theorem rep_JM {c : Config} {u : XM} {f : Bivar} (hu : u.Rep c f) :
    (JM c u).Rep c (Certificate.J f) := by
  simp only [JM, Certificate.J]; build_xm [hu]

/-! ## The parts of the numerators -/

/-- `delta r`. -/
def deltaM (c : Config) (r : Region) : XM := XM.add c (thetaM c r) (eM c r)

theorem rep_deltaM (c : Config) (r : Region) : (deltaM c r).Rep c (Certificate.delta r) :=
  XM.rep_add (rep_thetaM c r) (rep_eM c r)

def qStarS (c : Config) (r : Region) : {m : XM // m.Rep c (Certificate.qStar r)} := by
  apply Subtype.mk; simp only [Certificate.qStar]; build_xm [rep_lM c r]
/-- `qStar r`. -/
def qStarM (c : Config) (r : Region) : XM := (qStarS c r).1
theorem rep_qStarM (c : Config) (r : Region) : (qStarM c r).Rep c (Certificate.qStar r) :=
  (qStarS c r).2

def jThetaS (c : Config) : (r : Region) → {m : XM // m.Rep c (Certificate.jTheta r)}
  | .triangle => by apply Subtype.mk; simp only [Certificate.jTheta]; build_xm [rep_JM, rep_thetaM c _]
  | .rectangle => by apply Subtype.mk; simp only [Certificate.jTheta]; build_xm [rep_JM, rep_thetaM c _]
/-- `jTheta r`. -/
def jThetaM (c : Config) (r : Region) : XM := (jThetaS c r).1
theorem rep_jThetaM (c : Config) (r : Region) : (jThetaM c r).Rep c (Certificate.jTheta r) :=
  (jThetaS c r).2

def jES (c : Config) : (r : Region) → {m : XM // m.Rep c (Certificate.jE r)}
  | .triangle => by apply Subtype.mk; simp only [Certificate.jE]; build_xm [rep_JM, rep_eM c _]
  | .rectangle => by apply Subtype.mk; simp only [Certificate.jE]; build_xm [rep_JM, rep_eM c _]
/-- `jE r`. -/
def jEM (c : Config) (r : Region) : XM := (jES c r).1
theorem rep_jEM (c : Config) (r : Region) : (jEM c r).Rep c (Certificate.jE r) := (jES c r).2

def MS (c : Config) (r : Region) : (ep : Endpoint) → {m : XM // m.Rep c (Certificate.M r ep)}
  | .atA => by apply Subtype.mk; simp only [Certificate.M]; build_xm [rep_cM c r]
  | .atT => by apply Subtype.mk; simp only [Certificate.M]; build_xm [rep_cM c r, rep_thetaM c r]
/-- `M r ep`. -/
def MM (c : Config) (r : Region) (ep : Endpoint) : XM := (MS c r ep).1
theorem rep_MM (c : Config) (r : Region) (ep : Endpoint) : (MM c r ep).Rep c (Certificate.M r ep) :=
  (MS c r ep).2

def ABaseS (c : Config) (r : Region) :
    (ep : Endpoint) → {m : XM // m.Rep c (Certificate.ABase r ep)}
  | .atA => by
    apply Subtype.mk; simp only [Certificate.ABase]
    build_xm [rep_kM c r, rep_lM c r, rep_cM c r, rep_jThetaM c r, rep_jEM c r]
  | .atT => by
    apply Subtype.mk; simp only [Certificate.ABase]
    build_xm [rep_kM c r, rep_lM c r, rep_cM c r, rep_jEM c r, rep_thetaM c r]
/-- `ABase r ep`. -/
def ABaseM (c : Config) (r : Region) (ep : Endpoint) : XM := (ABaseS c r ep).1
theorem rep_ABaseM (c : Config) (r : Region) (ep : Endpoint) :
    (ABaseM c r ep).Rep c (Certificate.ABase r ep) := (ABaseS c r ep).2

def qBS (c : Config) : (r : Region) → (ep : Endpoint) → {m : XM // m.Rep c (Certificate.qB r ep)}
  | .triangle, _ => by apply Subtype.mk; simp only [Certificate.qB]; build_xm [rep_qStarM c _]
  | .rectangle, ep => by apply Subtype.mk; simp only [Certificate.qB]; build_xm [rep_MM c _ ep]
/-- `qB r ep`. -/
def qBM (c : Config) (r : Region) (ep : Endpoint) : XM := (qBS c r ep).1
theorem rep_qBM (c : Config) (r : Region) (ep : Endpoint) : (qBM c r ep).Rep c (Certificate.qB r ep) :=
  (qBS c r ep).2

def AS (c : Config) (r : Region) (ep : Endpoint) (i : Fin 3) :
    {m : XM // m.Rep c (Certificate.A r ep i)} := by
  apply Subtype.mk; simp only [Certificate.A]
  build_xm [rep_ABaseM c r ep, rep_lM c r, rep_qBM c r ep, rep_deltaM c r]
/-- `A r ep i`. -/
def AM (c : Config) (r : Region) (ep : Endpoint) (i : Fin 3) : XM := (AS c r ep i).1
theorem rep_AM (c : Config) (r : Region) (ep : Endpoint) (i : Fin 3) :
    (AM c r ep i).Rep c (Certificate.A r ep i) := (AS c r ep i).2

def baseNormS (c : Config) (r : Region) (ep : Endpoint) (j : Fin 4) :
    {m : XM // m.Rep c (Certificate.baseNorm r ep j)} := by
  apply Subtype.mk; simp only [Certificate.baseNorm]
  build_xm [rep_kM c r, rep_lM c r, rep_MM c r ep, rep_cM c r]

def PS (c : Config) (r : Region) (ep : Endpoint) (i : Fin 3) (j : Fin 4) :
    {m : XM // m.Rep c (Certificate.P r ep i j)} := by
  apply Subtype.mk; simp only [Certificate.P]
  build_xm [(baseNormS c r ep j).2, rep_kM c r, rep_lM c r, rep_MM c r ep, rep_deltaM c r]
/-- `P r ep i j`, reduced. -/
def PM (c : Config) (r : Region) (ep : Endpoint) (i : Fin 3) (j : Fin 4) : XM :=
  XM.reduce c (PS c r ep i j).1
theorem rep_PM (c : Config) (r : Region) (ep : Endpoint) (i : Fin 3) (j : Fin 4) :
    (PM c r ep i j).Rep c (Certificate.P r ep i j) := XM.rep_reduce (PS c r ep i j).2

/-- `rho ep i j` as a numerator and a denominator. -/
def rhoP (ep : Endpoint) (i : Fin 3) (j : Fin 4) : ℤ × ℕ :=
  if j.val=i.val then
    if j=2 then match ep with
      | .atA => (81386069, 62500000)
      | .atT => (1325511353, 1000000000)
    else (27678887, 25000000)
  else if j=2 then match ep with
    | .atA => (142578599, 100000000)
    | .atT => (1451171531, 1000000000)
  else if j=3 then (142578599, 100000000)
  else (150407189, 125000000)

theorem rho_eq (ep : Endpoint) (i : Fin 3) (j : Fin 4) :
    Certificate.rho ep i j = ((rhoP ep i j).1 : ℚ) / (rhoP ep i j).2 := by
  unfold Certificate.rho rhoP
  split_ifs <;> cases ep <;> norm_num

/-- `mass r ep i j`, reduced. -/
def massM (c : Config) (r : Region) (ep : Endpoint) (i : Fin 3) (j : Fin 4) : XM :=
  XM.reduce c (XM.cubicMassRM c (rhoP ep i j).1 (rhoP ep i j).2 (PM c r ep i j))
theorem rep_massM (c : Config) (r : Region) (ep : Endpoint) (i : Fin 3) (j : Fin 4) :
    (massM c r ep i j).Rep c (Certificate.mass r ep i j) :=
  XM.rep_reduce (XM.rep_cubicMassRM (rep_PM c r ep i j) (rho_eq ep i j))

def numeratorS (c : Config) (r : Region) (ep : Endpoint) (i : Fin 3) :
    {m : XM // m.Rep c (Certificate.numerator r ep i)} := by
  apply Subtype.mk; simp only [Certificate.numerator]
  build_xm [rep_AM c r ep i, rep_massM c r ep i _, rep_PM c r ep i _]
/-- `numerator r ep i`, reduced. -/
def numeratorM (c : Config) (r : Region) (ep : Endpoint) (i : Fin 3) : XM :=
  XM.reduce c (numeratorS c r ep i).1
theorem rep_numeratorM (c : Config) (r : Region) (ep : Endpoint) (i : Fin 3) :
    (numeratorM c r ep i).Rep c (Certificate.numerator r ep i) := XM.rep_reduce (numeratorS c r ep i).2

end SquaresInCircles.Eight.NonnegativeTotalsMirrors
