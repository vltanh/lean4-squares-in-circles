module

public import SquaresInCircles.Eight.Candidate.Geometry
public import SquaresInCircles.Eight.Candidate.Mismatch
public import SquaresInCircles.Eight.Arithmetic.Bernstein
public import SquaresInCircles.Eight.Arithmetic.ClosedCover
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Circle duals and the common-weight error disjunction

F8 draft. Circle completion is applied to the actual seven centers. The
same edge-weight vector is fixed before the signed-error alternative is
chosen. A finite polynomial certificate remains attached to the force
and right-hand-side expressions reconstructed from its own multipliers.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.Candidate.Dual

theorem circle_linear_upper {a b C D μ Q : ℝ} (hμ : 0 < μ)
    (hcircle : (a + 1 / 2) ^ 2 + (b + 1 / 2) ^ 2 ≤ Q) :
    C * (a + 1 / 2) + D * (b + 1 / 2) ≤ μ * Q + (C ^ 2 + D ^ 2) / (4 * μ) := by
  have hid :
      μ * ((a + 1 / 2) ^ 2 + (b + 1 / 2) ^ 2) + (C ^ 2 + D ^ 2) / (4 * μ) -
        C * (a + 1 / 2) - D * (b + 1 / 2) =
      ((2 * μ * (a + 1 / 2) - C) ^ 2 + (2 * μ * (b + 1 / 2) - D) ^ 2) / (4 * μ) := by
    field_simp [ne_of_gt hμ]
    ring
  have hnonneg : 0 ≤
      ((2 * μ * (a + 1 / 2) - C) ^ 2 + (2 * μ * (b + 1 / 2) - D) ^ 2) / (4 * μ) := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hcircle hμ.le
  linarith

theorem circle_dual_necessary (a b C D μ : Vertex → ℝ) {Q B : ℝ}
    (hμ : ∀ i, 0 < μ i)
    (hcircle : ∀ i, (a i + 1 / 2) ^ 2 + (b i + 1 / 2) ^ 2 ≤ Q)
    (hlinear : B ≤ ∑ i, (C i * a i + D i * b i)) :
    B + (1 / 2) * ∑ i, (C i + D i) ≤
      Q * (∑ i, μ i) + ∑ i, (C i ^ 2 + D i ^ 2) / (4 * μ i) := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset Vertex))
    (fun i _ => circle_linear_upper (hμ i) (hcircle i))
  have hleft : (∑ i, (C i * (a i + 1 / 2) + D i * (b i + 1 / 2))) =
      (∑ i, (C i * a i + D i * b i)) + (1 / 2) * ∑ i, (C i + D i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hleft, Finset.sum_add_distrib] at hs
  have hright : (∑ i, μ i * Q) = Q * ∑ i, μ i := by
    rw [Finset.mul_sum]
    congr 1
    ext i
    ring
  rw [hright] at hs
  linarith

theorem weighted_total_error {ι : Type*} [Fintype ι]
    (λ d : ι → ℝ) {M ε : ℝ}
    (hM : 0 ≤ M) (hλ : ∀ i, λ i ≤ M) (hε : ∑ i, |d i| ≤ ε) :
    (∑ i, λ i * |d i|) ≤ M * ε := by
  calc
    (∑ i, λ i * |d i|) ≤ ∑ i, M * |d i| :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hλ i) (abs_nonneg _))
    _ = M * ∑ i, |d i| := (Finset.mul_sum _ _ _).symm
    _ ≤ M * ε := mul_le_mul_of_nonneg_left hε hM

/-- Common-weight l1 disjunction, including the zero-error alternative. -/
theorem error_vertex_disjunction {ι : Type*} [Fintype ι] [Nonempty ι]
    (c λ d : ι → ℝ) {B R ε : ℝ} (hε : 0 ≤ ε)
    (hball : ∑ i, |d i| ≤ ε)
    (hnecessary : 0 ≤ B + (∑ i, (c i * d i - λ i / 2 * |d i|)) + R) :
    0 ≤ B + R ∨ ∃ i, ∃ s : ℝ, (s = -1 ∨ s = 1) ∧
      0 ≤ B + ε * (s * c i - λ i / 2) + R := by
  by_cases hzero : 0 ≤ B + R
  · exact Or.inl hzero
  · right
    by_contra hn
    push_neg at hn
    let M : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => |c i| - λ i / 2)
    have hMi (i : ι) : |c i| - λ i / 2 ≤ M := Finset.le_sup' (s := Finset.univ) (by simp)
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => |c i| - λ i / 2)
    have hterm (i : ι) : c i * d i - λ i / 2 * |d i| ≤ (|c i| - λ i / 2) * |d i| := by
      have hh : c i * d i ≤ |c i| * |d i| := by simpa [abs_mul] using le_abs_self (c i * d i)
      nlinarith
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun i _ => hterm i)
    by_cases hM : 0 ≤ M
    · have hw := weighted_total_error (fun i => |c i| - λ i / 2) d hM hMi hball
      have hlast : 0 ≤ B + ε * M + R := by linarith
      rcases le_total 0 (c j) with hc | hc
      · have hh := hn j 1 (Or.inr rfl)
        have he : M = c j - λ j / 2 := by simpa [M, abs_of_nonneg hc] using hj.symm
        rw [he] at hlast
        nlinarith
      · have hh := hn j (-1) (Or.inl rfl)
        have he : M = -c j - λ j / 2 := by simpa [M, abs_of_nonpos hc] using hj.symm
        rw [he] at hlast
        nlinarith
    · have hnonpos : (∑ i, (|c i| - λ i / 2) * |d i|) ≤ 0 :=
        Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonpos_of_nonneg
          ((hMi i).trans (le_of_not_ge hM)) (abs_nonneg _))
      linarith

def alignedEdge : Fin 5 → Vertex := ![0, 2, 3, 4, 5]
def nominalOwner : Vertex → Fin 4 := ![0, 0, 0, 2, 0, 2, 1]
def signs : Vertex → ℚ := ![1, -1, 1, -1, 1, -1, -1]

inductive Alternative
  | zero
  | spike (edge : Fin 5) (secondOwner : Bool) (positive : Bool)
  deriving DecidableEq, Fintype

theorem alternative_count : Fintype.card Alternative = 21 := by decide

def Alternative.owner (j : Fin 5) (second : Bool) : Fin 4 :=
  if second then (if j = 2 ∨ j = 4 then 3 else 2)
  else (if j = 2 ∨ j = 4 then 2 else 0)

def signValue (positive : Bool) : ℚ := if positive then 1 else -1

abbrev Poly := Polynomial ℚ
def peval (p : Poly) (z : ℝ) : ℝ := Polynomial.eval₂ (algebraMap ℚ ℝ) z p
def Dpoly : Poly := 1 + Polynomial.X ^ 2
def Cpoly : Poly := 1 - Polynomial.X ^ 2
def Spoly : Poly := 2 * Polynomial.X

@[simp] theorem eval_D (z : ℝ) : peval Dpoly z = 1 + z ^ 2 := by simp [peval, Dpoly]
@[simp] theorem eval_C (z : ℝ) : peval Cpoly z = 1 - z ^ 2 := by simp [peval, Cpoly]
@[simp] theorem eval_S (z : ℝ) : peval Spoly z = 2 * z := by simp [peval, Spoly]
theorem D_positive (z : ℝ) : 0 < peval Dpoly z := by rw [eval_D]; positivity

def sinNumerator (i : Vertex) : Poly :=
  if i ∈ zeroEdges then 0 else if i ∈ otherQuarterEdges then Dpoly else Cpoly
def cosNumerator (i : Vertex) : Poly :=
  if i ∈ zeroEdges then Dpoly else if i ∈ otherQuarterEdges then 0
  else if i = G then Spoly else -Spoly

def coefficient (j r : Vertex) (p : Poly) : Poly := if j = r then p else 0

def nominalA (i : Vertex) (owner : Fin 4) (r : Vertex) : Poly :=
  ![coefficient (next i) r (sinNumerator i),
    -coefficient i r (cosNumerator i) + coefficient (next i) r Dpoly,
    coefficient i r (sinNumerator i),
    coefficient i r Dpoly - coefficient (next i) r (cosNumerator i)] owner

def nominalB (i : Vertex) (owner : Fin 4) (r : Vertex) : Poly :=
  ![coefficient i r (Polynomial.C (signs i) * Dpoly) -
      coefficient (next i) r (Polynomial.C (signs (next i)) * cosNumerator i),
    coefficient i r (Polynomial.C (signs i) * sinNumerator i),
    coefficient i r (Polynomial.C (signs i) * cosNumerator i) -
      coefficient (next i) r (Polynomial.C (signs (next i)) * Dpoly),
    -coefficient (next i) r (Polynomial.C (signs (next i)) * sinNumerator i)] owner

def derivativeA (i : Vertex) (owner : Fin 4) (r : Vertex) : Poly :=
  ![coefficient (next i) r (cosNumerator i),
    coefficient i r (sinNumerator i), coefficient i r (cosNumerator i),
    coefficient (next i) r (sinNumerator i)] owner

def derivativeB (i : Vertex) (owner : Fin 4) (r : Vertex) : Poly :=
  ![coefficient (next i) r (Polynomial.C (signs (next i)) * sinNumerator i),
    coefficient i r (Polynomial.C (signs i) * cosNumerator i),
    -coefficient i r (Polynomial.C (signs i) * sinNumerator i),
    -coefficient (next i) r (Polynomial.C (signs (next i)) * cosNumerator i)] owner

def widthNumerator (positive : Bool) : Poly :=
  Polynomial.C (1 / 2) * (Dpoly + Cpoly + Polynomial.C (signValue positive) * Spoly)
def lastWidthDerivative (positive : Bool) : Poly :=
  if positive then Polynomial.C (1 / 2) * (Cpoly - Spoly)
  else Polynomial.C (-1 / 2) * (Cpoly + Spoly)
def edgeWidth (positive : Bool) (i : Vertex) : Poly :=
  if i ∈ mixedEdges then widthNumerator positive else Dpoly

def lowerRatio : Vertex → ℚ := ![1 / 2, 1 / 20, 0, 0, 1 / 20, 1 / 2, 0]
def upperRatio : Vertex → ℚ := ![1, 4 / 5, 1, 1, 4 / 5, 1, 1]
def lowerPrimary (i : Vertex) : ℚ := if i = G ∨ i = T then 7 / 12 else 447 / 800
def upperPrimary (i : Vertex) : ℚ := if i = G ∨ i = T then 349 / 250 else 283 / 200

abbrev ConeIndex := Fin 7 × Fin 5

def coneA (j : ConeIndex) (r : Vertex) : ℚ :=
  if j.1 = r then ![1, -1, -lowerRatio r, upperRatio r, 0] j.2 else 0
def coneB (j : ConeIndex) (r : Vertex) : ℚ :=
  if j.1 = r then ![0, 0, 1, -1, -1] j.2 else 0
def coneRhs (j : ConeIndex) : ℚ :=
  ![lowerPrimary j.1, -upperPrimary j.1, 0, 0, -9 / 10] j.2

inductive Mode | quarter | mixed | tilt
  deriving DecidableEq

structure Row where
  mode : Mode
  positive : Bool
  interval : Arithmetic.QInterval
  owners : Vertex → Fin 4
  lambda : Vertex → ℚ
  cone : ConeIndex → ℚ
  mu : Vertex → ℚ
  alternative : Alternative := .zero
  polynomial : Arithmetic.QPoly
  bernstein : List ℚ
  reserve : ℚ

def Row.Q (r : Row) : ℚ := if r.mode = .tilt then 1957767069 / 500000000 else 9789 / 2500
def Row.epsilon (r : Row) : ℚ := if r.mode = .quarter then 3 / 200 else 1 / 1000
def Row.maxLambda (r : Row) : ℚ :=
  max (r.lambda 0) (max (r.lambda 2) (max (r.lambda 3) (max (r.lambda 4) (r.lambda 5))))

def Row.loss (r : Row) : ℚ :=
  match r.mode with
  | .quarter => r.epsilon * ((3 / 2) * ∑ j : Fin 5, r.lambda (alignedEdge j) + 2 * r.lambda E)
  | .mixed => r.epsilon * ((1001 / 1000) * r.maxLambda + 2 * r.lambda E)
  | .tilt => r.epsilon ^ 2 * ((1001 / 1000) * r.maxLambda + (9 / 8) * r.lambda E)

def Row.errorA (r : Row) (i : Vertex) : Poly :=
  match r.alternative with
  | .zero => 0
  | .spike j second positive =>
    Polynomial.C (signValue positive * r.epsilon) *
      (Polynomial.C (r.lambda (alignedEdge j)) * derivativeA (alignedEdge j) (Alternative.owner j second) i -
        Polynomial.C (r.lambda E) * derivativeA E 1 i)

def Row.errorB (r : Row) (i : Vertex) : Poly :=
  match r.alternative with
  | .zero => 0
  | .spike j second positive =>
    Polynomial.C (signValue positive * r.epsilon) *
      (Polynomial.C (r.lambda (alignedEdge j)) * derivativeB (alignedEdge j) (Alternative.owner j second) i -
        Polynomial.C (r.lambda E) * derivativeB E 1 i)

def Row.errorRhs (r : Row) : Poly :=
  match r.alternative with
  | .zero => 0
  | .spike j _ positive =>
    -Polynomial.C (signValue positive * r.epsilon * r.lambda E) * lastWidthDerivative r.positive +
      Polynomial.C (r.epsilon * r.lambda (alignedEdge j) / 2) * Dpoly

def Row.forceA (r : Row) (j : Vertex) : Poly :=
  (∑ i, Polynomial.C (r.lambda i) * nominalA i (r.owners i) j) +
  Polynomial.C (∑ i, r.cone i * coneA i j) * Dpoly + r.errorA j
def Row.forceB (r : Row) (j : Vertex) : Poly :=
  (∑ i, Polynomial.C (r.lambda i) * nominalB i (r.owners i) j) +
  Polynomial.C (∑ i, r.cone i * coneB i j) * Dpoly + r.errorB j
def Row.rhs (r : Row) : Poly :=
  (∑ i, Polynomial.C (r.lambda i) * edgeWidth r.positive i) +
  Polynomial.C ((∑ j, r.cone j * coneRhs j) - r.loss) * Dpoly + r.errorRhs
def Row.L (r : Row) : Poly := r.rhs + Polynomial.C (1 / 2) * ∑ i, (r.forceA i + r.forceB i)
def Row.quartic (r : Row) : Poly :=
  Dpoly * r.L - Polynomial.C (r.Q * ∑ i, r.mu i) * Dpoly ^ 2 -
    ∑ i, Polynomial.C (1 / (4 * r.mu i)) * (r.forceA i ^ 2 + r.forceB i ^ 2)

def Row.bernsteinRow (r : Row) : Arithmetic.BernsteinRow :=
  ⟨r.interval, r.polynomial, 4, r.bernstein⟩

def listPoly : List ℚ → Poly
  | [] => 0
  | a :: p => Polynomial.C a + Polynomial.X * listPoly p

theorem listPoly_eval (p : List ℚ) (z : ℝ) : peval (listPoly p) z = Arithmetic.QPoly.eval p z := by
  induction p with
  | nil => simp [listPoly, peval, Arithmetic.QPoly.eval]
  | cons a p ih => simp [listPoly, peval, Arithmetic.QPoly.eval, ← ih]

structure Row.Valid (r : Row) : Prop where
  lambda_nonneg : ∀ i, 0 ≤ r.lambda i
  cone_nonneg : ∀ i, 0 ≤ r.cone i
  mu_pos : ∀ i, 0 < r.mu i
  interval_sign : if r.positive then 0 ≤ r.interval.lo else r.interval.hi ≤ 0
  polynomial_identity : r.quartic = listPoly r.polynomial
  bernstein_valid : r.bernsteinRow.Valid r.reserve
  reserve_pos : 0 < r.reserve

theorem Row.Valid.quartic_pos {r : Row} (hr : r.Valid) {z : ℝ} (hz : r.interval.Mem z) :
    0 < peval r.quartic z := by
  rw [hr.polynomial_identity, listPoly_eval]
  exact hr.bernstein_valid.positive hr.reserve_pos hz

/-- Contradiction for the exact weighted necessary inequality. Its force and
rhs are those in the certified quartic, not a separately asserted bound. -/
theorem Row.Valid.excludes {r : Row} (hr : r.Valid) {z : ℝ} (hz : r.interval.Mem z)
    (a b : Vertex → ℝ)
    (hcircle : ∀ i, (a i + 1 / 2) ^ 2 + (b i + 1 / 2) ^ 2 ≤ (r.Q : ℝ))
    (hnecessary : peval r.rhs z / peval Dpoly z ≤
      ∑ i, (peval (r.forceA i) z / peval Dpoly z * a i +
        peval (r.forceB i) z / peval Dpoly z * b i)) : False := by
  have hd := D_positive z
  have hdual := circle_dual_necessary a b
    (fun i => peval (r.forceA i) z / peval Dpoly z)
    (fun i => peval (r.forceB i) z / peval Dpoly z)
    (fun i => (r.mu i : ℝ)) (fun i => by exact_mod_cast hr.mu_pos i) hcircle hnecessary
  have hp := hr.quartic_pos hz
  have hidentity : peval r.quartic z = (peval Dpoly z) ^ 2 *
      ((peval r.rhs z / peval Dpoly z + (1 / 2) * ∑ i,
          (peval (r.forceA i) z / peval Dpoly z + peval (r.forceB i) z / peval Dpoly z)) -
        ((r.Q : ℝ) * ∑ i, (r.mu i : ℝ) + ∑ i,
          ((peval (r.forceA i) z / peval Dpoly z) ^ 2 +
           (peval (r.forceB i) z / peval Dpoly z) ^ 2) / (4 * (r.mu i : ℝ)))) := by
    simp [Row.quartic, Row.L, peval, Polynomial.eval₂_finset_sum,
      Fin.sum_univ_succ, map_add, map_mul, map_pow]
    field_simp [ne_of_gt hd, fun i => ne_of_gt (show (0 : ℝ) < r.mu i by exact_mod_cast hr.mu_pos i)]
    ring
  rw [hidentity] at hp
  have hn := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (peval Dpoly z)) (sub_nonpos.mpr hdual)
  linarith

/-- Every owner table covers the entire closed half-angle chart. Metadata
equalities are proved from each row, independently of polynomial positivity. -/
structure OwnerTable where
  mode : Mode
  owners : Vertex → Fin 4
  rows : List Row
  valid : ∀ r ∈ rows, r.Valid
  same_mode : ∀ r ∈ rows, r.mode = mode
  same_owners : ∀ r ∈ rows, r.owners = owners
  no_error : ∀ r ∈ rows, r.alternative = .zero
  cover : Arithmetic.ClosedChain (-3 / 8) (3 / 8) (rows.map Row.interval)

theorem OwnerTable.select (T : OwnerTable) {z : ℝ}
    (hz : -(3 / 8 : ℝ) ≤ z ∧ z ≤ 3 / 8) :
    ∃ r ∈ T.rows, r.interval.Mem z := by
  obtain ⟨I, hI, hzI⟩ := T.cover.covers (by exact_mod_cast hz)
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hI
  exact ⟨r, hr, hzI⟩

/-- An interval chooses its common SAT weights before the error alternative.
Only the cone and circle multipliers vary with that alternative. -/
structure TiltBundle where
  interval : Arithmetic.QInterval
  lambda : Vertex → ℚ
  row : Alternative → Row
  valid : ∀ a, (row a).Valid
  same_interval : ∀ a, (row a).interval = interval
  same_lambda : ∀ a, (row a).lambda = lambda
  same_mode : ∀ a, (row a).mode = .tilt
  same_owners : ∀ a, (row a).owners = nominalOwner
  same_alternative : ∀ a, (row a).alternative = a
  same_sign : ∀ a, (row a).positive = (row .zero).positive

def ConeBounds (a b : Vertex → ℝ) : Prop :=
  ∀ i, (lowerPrimary i : ℝ) ≤ a i ∧ a i ≤ upperPrimary i ∧
    (lowerRatio i : ℝ) * a i ≤ b i ∧ b i ≤ (upperRatio i : ℝ) * a i ∧ b i ≤ 9 / 10

theorem ConeBounds.row {a b : Vertex → ℝ} (hc : ConeBounds a b) (k : ConeIndex) :
    (coneRhs k : ℝ) ≤ ∑ i, ((coneA k i : ℝ) * a i + (coneB k i : ℝ) * b i) := by
  obtain ⟨i, j⟩ := k
  have hi := hc i
  fin_cases j <;>
    simp [coneA, coneB, coneRhs, Fin.sum_univ_succ] <;>
    fin_cases i <;> norm_num [lowerPrimary, upperPrimary, lowerRatio, upperRatio] at * <;> linarith

def projectionNumerator (a b : Vertex → ℝ) (z : ℝ) (i : Vertex) (j : Fin 4) : ℝ :=
  ∑ k, (peval (nominalA i j k) z * a k + peval (nominalB i j k) z * b k)

def derivativeNumerator (a b : Vertex → ℝ) (z : ℝ) (i : Vertex) (j : Fin 4) : ℝ :=
  ∑ k, (peval (derivativeA i j k) z * a k + peval (derivativeB i j k) z * b k)

def Row.originalNecessary (r : Row) (a b : Vertex → ℝ) (z : ℝ) : Prop :=
  (∑ i, (r.lambda i : ℝ) * peval (edgeWidth r.positive i) z) -
      (r.loss : ℝ) * peval Dpoly z + peval r.errorRhs z ≤
    (∑ i, (r.lambda i : ℝ) * projectionNumerator a b z i (r.owners i)) +
      ∑ i, (peval (r.errorA i) z * a i + peval (r.errorB i) z * b i)

theorem Row.Valid.excludes_original {r : Row} (hr : r.Valid) {z : ℝ}
    (hz : r.interval.Mem z) (a b : Vertex → ℝ)
    (hc : ConeBounds a b)
    (hcircle : ∀ i, (a i + 1 / 2) ^ 2 + (b i + 1 / 2) ^ 2 ≤ (r.Q : ℝ))
    (hnecessary : r.originalNecessary a b z) : False := by
  apply hr.excludes hz a b hcircle
  have hd := D_positive z
  have hk := Finset.sum_le_sum (s := (Finset.univ : Finset ConeIndex))
    (fun k _ => mul_le_mul_of_nonneg_left (hc.row k)
      (show (0 : ℝ) ≤ r.cone k by exact_mod_cast hr.cone_nonneg k))
  have hident : peval r.rhs z -
      (∑ i, (peval (r.forceA i) z * a i + peval (r.forceB i) z * b i)) =
      ((∑ i, (r.lambda i : ℝ) * peval (edgeWidth r.positive i) z) -
        (r.loss : ℝ) * peval Dpoly z + peval r.errorRhs z -
        ((∑ i, (r.lambda i : ℝ) * projectionNumerator a b z i (r.owners i)) +
          ∑ i, (peval (r.errorA i) z * a i + peval (r.errorB i) z * b i))) +
      peval Dpoly z * ((∑ k, (r.cone k : ℝ) * coneRhs k) -
        ∑ k, (r.cone k : ℝ) * ∑ i, ((coneA k i : ℝ) * a i + (coneB k i : ℝ) * b i)) := by
    simp [Row.rhs, Row.forceA, Row.forceB, projectionNumerator, peval,
      Polynomial.eval₂_finset_sum, Finset.mul_sum, Finset.sum_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_comm]
    ring
  have hh : peval r.rhs z ≤ ∑ i, (peval (r.forceA i) z * a i + peval (r.forceB i) z * b i) := by
    have h₁ : ((∑ i, (r.lambda i : ℝ) * peval (edgeWidth r.positive i) z) -
        (r.loss : ℝ) * peval Dpoly z + peval r.errorRhs z -
        ((∑ i, (r.lambda i : ℝ) * projectionNumerator a b z i (r.owners i)) +
          ∑ i, (peval (r.errorA i) z * a i + peval (r.errorB i) z * b i))) ≤ 0 :=
      sub_nonpos.mpr hnecessary
    have h₂ := mul_nonpos_of_nonneg_of_nonpos hd.le (sub_nonpos.mpr hk)
    linarith
  have hh' := (div_le_div_iff_of_pos_right hd).2 hh
  simpa [Finset.sum_div, add_div, div_mul_eq_mul_div] using hh'

end SquaresInCircles.Eight.Candidate.Dual
