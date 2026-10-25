module

public import SquaresInCircles.Eight.Arithmetic.BivariateCertificates

/-!
# Eight squares: rounded bivariate certificates

The exact models `BivariateCertificate.XM` carry digits of thousands of bits on the largest
certificates, because the exact coefficients have huge common denominators, and an external
kernel multiplies such numbers in quadratic time. A rounded model `XE` is an exact model `m` of an
approximation of `p`, with a bound `e` on the ℓ¹ norm of the coefficients of `s · p - m.val` (`s`
is the scale of `m`) and bounds on the degrees of `p`. Products are rounded back to a power-of-two
scale by masks and shifts, so the digits stay small; the final bound of the Chebyshev coefficients
absorbs `e`.

* `l1`: the ℓ¹ norm of the coefficients of a bivariate polynomial; it is subadditive and
  submultiplicative (`l1_add_le`, `l1_mul_le`), does not grow under the quotients by `x` and `y`
  and under substitutions by polynomials of norm at most one (`l1_substitute_le`), and grows at
  most by the degree under a derivative.
* `DegQ p dx dy dt`: the coefficients vanish outside `i ≤ dx`, `j ≤ dy`, `i + j ≤ dt`.
* `digitMapZ`: every digit of a packed number through a map, from one digit width into another,
  by halvings (`digitMapZ_pack`); `round_box`: every digit divided by `2 ^ L`, by a mask and a shift.
* `repackM`: an exact model in another packing of the same box.
* `XE.Rep c x p`: `x` represents `p` within its error. Operations: `add`, `neg`, `sub`, `mul`,
  `round` and `mulR` (a product rounded by `L` bits), `scale` (every digit times `a / b`, into
  another packing: `toScale` to the scale `2 ^ K`, `repack`, and `ofXMAt` from an exact model),
  the linear maps `divY`, `derivY`, `divX`, `derivX`, `triangle`, `rectangle` (through `lin`), and
  `norm`.
* `XE.upperCheck`, `XE.lowerCheck` and `XE.upper_certificate`, `XE.lower_certificate`: the final
  bound of `BivariateCertificate.XM` for the approximation, widened by `4 (D + 1)² e / s`, gives
  the bound of the represented polynomial.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.BivariateRounding
open Polynomial TensorWholeIntervalPolynomial

/-! ## Sums of a norm of the coefficients -/

section Gen
variable {R : Type*} [Semiring R]

/-- A nonnegative, subadditive and submultiplicative function that vanishes at `0`. -/
structure IsNorm (N : R → ℚ) : Prop where
  zero : N 0 = 0
  nonneg : ∀ a, 0 ≤ N a
  add : ∀ a b, N (a + b) ≤ N a + N b
  mul : ∀ a b, N (a * b) ≤ N a * N b

/-- The sum of `N` over the coefficients. -/
def gsum (N : R → ℚ) (p : R[X]) : ℚ := p.sum fun _ a => N a

variable {N : R → ℚ}

theorem gsum_eq_of_subset (hN : IsNorm N) {p : R[X]} {s : Finset ℕ} (hs : p.support ⊆ s) :
    gsum N p = ∑ n ∈ s, N (p.coeff n) :=
  Polynomial.sum_eq_of_subset _ (fun _ => hN.zero) hs

theorem gsum_nonneg (hN : IsNorm N) (p : R[X]) : 0 ≤ gsum N p :=
  Finset.sum_nonneg fun _ _ => hN.nonneg _

theorem gsum_zero : gsum N (0 : R[X]) = 0 := by
  simp [gsum]

theorem gsum_monomial (hN : IsNorm N) (n : ℕ) (a : R) : gsum N (monomial n a) = N a := by
  unfold gsum; exact Polynomial.sum_monomial_index a _ hN.zero

theorem gsum_C (hN : IsNorm N) (a : R) : gsum N (C a) = N a := by
  rw [← monomial_zero_left]; exact gsum_monomial hN 0 a

theorem gsum_add_le (hN : IsNorm N) (p q : R[X]) : gsum N (p + q) ≤ gsum N p + gsum N q := by
  have h1 : p.support ⊆ p.support ∪ q.support := Finset.subset_union_left
  have h2 : q.support ⊆ p.support ∪ q.support := Finset.subset_union_right
  rw [gsum_eq_of_subset hN (Polynomial.support_add), gsum_eq_of_subset hN h1,
    gsum_eq_of_subset hN h2, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun n _ => by rw [Polynomial.coeff_add]; exact hN.add _ _

theorem gsum_sum_le (hN : IsNorm N) {ι : Type*} (s : Finset ι) (f : ι → R[X]) :
    gsum N (∑ i ∈ s, f i) ≤ ∑ i ∈ s, gsum N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gsum_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (gsum_add_le hN _ _).trans (by linarith)

theorem gsum_mul_le (hN : IsNorm N) (p q : R[X]) : gsum N (p * q) ≤ gsum N p * gsum N q := by
  rw [Polynomial.mul_eq_sum_sum]
  refine (gsum_sum_le hN _ _).trans ?_
  rw [gsum, Polynomial.sum_def, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Polynomial.sum_def]
  refine (gsum_sum_le hN _ _).trans ?_
  rw [gsum, Polynomial.sum_def, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [gsum_monomial hN]
  exact hN.mul _ _

theorem gsum_neg {R : Type*} [Ring R] {N : R → ℚ} (hneg : ∀ a, N (-a) = N a) (p : R[X]) :
    gsum N (-p) = gsum N p := by
  unfold gsum
  rw [Polynomial.sum_def, Polynomial.sum_def, Polynomial.support_neg]
  exact Finset.sum_congr rfl fun n _ => by rw [Polynomial.coeff_neg, hneg]

theorem isNorm_gsum (hN : IsNorm N) : IsNorm (gsum N) where
  zero := gsum_zero
  nonneg := gsum_nonneg hN
  add := gsum_add_le hN
  mul := gsum_mul_le hN

end Gen

/-! ## The ℓ¹ norm of rational polynomials -/

/-- The ℓ¹ norm of a univariate rational polynomial. -/
def l1u (p : ℚ[X]) : ℚ := gsum (fun a : ℚ => |a|) p

theorem isNorm_abs : IsNorm (fun a : ℚ => |a|) where
  zero := abs_zero
  nonneg := abs_nonneg
  add := abs_add_le
  mul a b := (abs_mul a b).le

theorem isNorm_l1u : IsNorm l1u := isNorm_gsum isNorm_abs

/-- The ℓ¹ norm of the coefficients of a bivariate polynomial. -/
def l1 (p : Bivar) : ℚ := gsum l1u p

theorem isNorm_l1 : IsNorm l1 := isNorm_gsum isNorm_l1u

theorem l1_nonneg (p : Bivar) : 0 ≤ l1 p := isNorm_l1.nonneg p
theorem l1_add_le (p q : Bivar) : l1 (p + q) ≤ l1 p + l1 q := isNorm_l1.add p q
theorem l1_mul_le (p q : Bivar) : l1 (p * q) ≤ l1 p * l1 q := isNorm_l1.mul p q
theorem l1_zero : l1 0 = 0 := isNorm_l1.zero

theorem l1u_neg (p : ℚ[X]) : l1u (-p) = l1u p := gsum_neg (fun a => abs_neg a) p
theorem l1_neg (p : Bivar) : l1 (-p) = l1 p := gsum_neg l1u_neg p

theorem l1_sub_le (p q : Bivar) : l1 (p - q) ≤ l1 p + l1 q := by
  rw [sub_eq_add_neg]; exact (l1_add_le _ _).trans (by rw [l1_neg])

theorem l1_sub_comm (p q : Bivar) : l1 (p - q) = l1 (q - p) := by
  rw [← neg_sub, l1_neg]

theorem l1u_C (a : ℚ) : l1u (C a) = |a| := gsum_C isNorm_abs a
theorem l1_C (p : ℚ[X]) : l1 (C p) = l1u p := gsum_C isNorm_l1u p
theorem l1_scalar (r : ℚ) : l1 (scalar r) = |r| := by
  rw [scalar, l1_C, l1u_C]

theorem l1_scalar_mul (r : ℚ) (p : Bivar) : l1 (scalar r * p) ≤ |r| * l1 p :=
  (l1_mul_le _ _).trans (by rw [l1_scalar])

theorem l1u_monomial (n : ℕ) (a : ℚ) : l1u (monomial n a) = |a| := gsum_monomial isNorm_abs n a

theorem l1_monomial (n : ℕ) (p : ℚ[X]) : l1 (monomial n p) = l1u p :=
  gsum_monomial isNorm_l1u n p

theorem l1_sum_le {ι : Type*} (s : Finset ι) (f : ι → Bivar) :
    l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := gsum_sum_le isNorm_l1u s f

theorem l1_pow_le (p : Bivar) : ∀ n, l1 (p ^ n) ≤ l1 p ^ n
  | 0 => by
    rw [pow_zero, pow_zero, ← map_one C, l1_C, ← map_one C, l1u_C, abs_one]
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (l1_mul_le _ _).trans (mul_le_mul_of_nonneg_right (l1_pow_le p n) (l1_nonneg p))

/-- The ℓ¹ norm is the sum of the absolute values over any box holding the support. -/
theorem l1_eq_sum {p : Bivar} {I J : ℕ} (h : ∀ i j, (p.coeff i).coeff j ≠ 0 → i < I ∧ j < J) :
    l1 p = ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J, |(p.coeff i).coeff j| := by
  have hI : p.support ⊆ Finset.range I := fun i hi => by
    rw [Polynomial.mem_support_iff] at hi
    obtain ⟨j, hj⟩ := Polynomial.ext_iff.not.mp hi |> not_forall.mp
    exact Finset.mem_range.mpr (h i j hj).1
  rw [l1, gsum_eq_of_subset isNorm_l1u hI]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hJ : (p.coeff i).support ⊆ Finset.range J := fun j hj => by
    rw [Polynomial.mem_support_iff] at hj
    exact Finset.mem_range.mpr (h i j hj).2
  rw [l1u, gsum_eq_of_subset isNorm_abs hJ]

/-! ## Degrees -/

/-- The coefficients vanish outside `i ≤ dx`, `j ≤ dy`, `i + j ≤ dt`. -/
def DegQ (p : Bivar) (dx dy dt : ℕ) : Prop :=
  ∀ i j, (p.coeff i).coeff j ≠ 0 → i ≤ dx ∧ j ≤ dy ∧ i + j ≤ dt

theorem DegQ.mono {p : Bivar} {dx dy dt ex ey et : ℕ} (h : DegQ p dx dy dt) (hx : dx ≤ ex)
    (hy : dy ≤ ey) (ht : dt ≤ et) : DegQ p ex ey et := fun i j hij => by
  have := h i j hij; omega

theorem DegQ.add {p q : Bivar} {dx dy dt : ℕ} (hp : DegQ p dx dy dt) (hq : DegQ q dx dy dt) :
    DegQ (p + q) dx dy dt := fun i j h => by
  rw [Polynomial.coeff_add, Polynomial.coeff_add] at h
  by_cases h1 : (p.coeff i).coeff j = 0
  · rw [h1, zero_add] at h; exact hq i j h
  · exact hp i j h1

theorem DegQ.neg {p : Bivar} {dx dy dt : ℕ} (hp : DegQ p dx dy dt) : DegQ (-p) dx dy dt :=
  fun i j h => hp i j (by simpa using h)

theorem DegQ.sub {p q : Bivar} {dx dy dt : ℕ} (hp : DegQ p dx dy dt) (hq : DegQ q dx dy dt) :
    DegQ (p - q) dx dy dt := by
  rw [sub_eq_add_neg]; exact hp.add hq.neg

theorem DegQ.mul {p q : Bivar} {dx dy dt ex ey et : ℕ} (hp : DegQ p dx dy dt)
    (hq : DegQ q ex ey et) : DegQ (p * q) (dx + ex) (dy + ey) (dt + et) := by
  intro i j h
  simp only [Polynomial.coeff_mul, Polynomial.finsetSum_coeff] at h
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨y, hy, hy0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx0
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hy' := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
  have h1 : (p.coeff x.1).coeff y.1 ≠ 0 := fun h0 => hy0 (by rw [h0, zero_mul])
  have h2 : (q.coeff x.2).coeff y.2 ≠ 0 := fun h0 => hy0 (by rw [h0, mul_zero])
  have := hp _ _ h1
  have := hq _ _ h2
  omega

theorem DegQ.scalar (r : ℚ) : DegQ (scalar r) 0 0 0 := fun i j h => by
  simp only [TensorWholeIntervalPolynomial.scalar, Polynomial.coeff_C] at h
  split_ifs at h with hi
  · subst hi; simp only [Polynomial.coeff_C] at h; split_ifs at h with hj
    · omega
    · exact absurd rfl h
  · simp at h

theorem DegQ.one : DegQ 1 0 0 0 := by
  have h := DegQ.scalar 1; rwa [TensorWholeIntervalPolynomial.scalar, map_one, map_one] at h

theorem DegQ.pow {p : Bivar} {dx dy dt : ℕ} (hp : DegQ p dx dy dt) :
    ∀ n, DegQ (p ^ n) (n * dx) (n * dy) (n * dt)
  | 0 => by rw [pow_zero]; simpa using DegQ.one
  | n + 1 => by
    rw [pow_succ]
    exact ((hp.pow n).mul hp).mono (by rw [Nat.succ_mul]) (by rw [Nat.succ_mul])
      (by rw [Nat.succ_mul])

theorem DegQ.natDegree {p : Bivar} {dx dy dt : ℕ} (hp : DegQ p dx dy dt) : p.natDegree ≤ dx := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro i hi
  ext j
  rw [Polynomial.coeff_zero]
  by_contra h0
  have := (hp i j h0).1
  omega

theorem DegQ.natDegree_coeff {p : Bivar} {dx dy dt : ℕ} (hp : DegQ p dx dy dt) (i : ℕ) :
    (p.coeff i).natDegree ≤ dy := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  by_contra h0
  have := (hp i j h0).2.1
  omega

theorem DegQ.zero (dx dy dt : ℕ) : DegQ 0 dx dy dt := fun i j h => by simp at h

theorem DegQ.sum {ι : Type*} (s : Finset ι) {f : ι → Bivar} {dx dy dt : ℕ}
    (h : ∀ i ∈ s, DegQ (f i) dx dy dt) : DegQ (∑ i ∈ s, f i) dx dy dt := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact DegQ.zero _ _ _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem degQ_X : DegQ (Polynomial.X : Bivar) 1 0 1 := fun i j h => by
  rw [Polynomial.coeff_X] at h
  split_ifs at h with hi
  · subst hi; rw [Polynomial.coeff_one] at h; split_ifs at h with hj
    · omega
    · exact absurd rfl h
  · simp at h

theorem degQ_Y : DegQ (C Polynomial.X : Bivar) 0 1 1 := fun i j h => by
  rw [Polynomial.coeff_C] at h
  split_ifs at h with hi
  · subst hi; rw [Polynomial.coeff_X] at h; split_ifs at h with hj
    · omega
    · exact absurd rfl h
  · simp at h

theorem DegQ.divY {p : Bivar} {dx dy dt : ℕ} (hp : DegQ p dx dy dt) :
    DegQ (TwoVariablePolynomial.divY p) dx (dy - 1) (dt - 1) := fun i j h => by
  rw [BivariateCertificate.coeff_divY] at h
  have := hp i (j + 1) h; omega

theorem DegQ.derivY {p : Bivar} {dx dy dt : ℕ} (hp : DegQ p dx dy dt) :
    DegQ (TwoVariablePolynomial.derivativeY p) dx (dy - 1) (dt - 1) := fun i j h => by
  rw [BivariateCertificate.coeff_derivativeY] at h
  have := hp i (j + 1) (right_ne_zero_of_mul h); omega

theorem DegQ.divX {p : Bivar} {dx dy dt : ℕ} (hp : DegQ p dx dy dt) :
    DegQ p.divX (dx - 1) dy (dt - 1) := fun i j h => by
  rw [Polynomial.coeff_divX] at h
  have := hp (i + 1) j h; omega

theorem DegQ.derivX {p : Bivar} {dx dy dt : ℕ} (hp : DegQ p dx dy dt) :
    DegQ (Polynomial.derivative p) (dx - 1) dy (dt - 1) := fun i j h => by
  rw [BivariateCertificate.coeff_derivativeX] at h
  have := hp (i + 1) j (right_ne_zero_of_mul h); omega

/-- The substitution `x ↦ f`, `y ↦ g`, term by term. -/
theorem substitute_eq_sum (f g p : Bivar) :
    TwoVariablePolynomial.substitute f g p = ∑ i ∈ p.support, ∑ j ∈ (p.coeff i).support,
      scalar ((p.coeff i).coeff j) * g ^ j * f ^ i := by
  rw [TwoVariablePolynomial.substitute, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum,
    Polynomial.sum_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TwoVariablePolynomial.lift, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum,
    Polynomial.sum_def, Finset.sum_mul]
  rfl

theorem DegQ.substitute {p f g : Bivar} {dx dy dt a₁ b₁ t₁ a₂ b₂ t₂ ex ey et : ℕ}
    (hp : DegQ p dx dy dt) (hf : DegQ f a₁ b₁ t₁) (hg : DegQ g a₂ b₂ t₂)
    (hx : ∀ i j, i ≤ dx → j ≤ dy → i + j ≤ dt → j * a₂ + i * a₁ ≤ ex)
    (hy : ∀ i j, i ≤ dx → j ≤ dy → i + j ≤ dt → j * b₂ + i * b₁ ≤ ey)
    (ht : ∀ i j, i ≤ dx → j ≤ dy → i + j ≤ dt → j * t₂ + i * t₁ ≤ et) :
    DegQ (TwoVariablePolynomial.substitute f g p) ex ey et := by
  rw [substitute_eq_sum]
  refine DegQ.sum _ fun i _ => DegQ.sum _ fun j hj => ?_
  have h0 := hp i j (Polynomial.mem_support_iff.mp hj)
  have h1 := ((DegQ.scalar ((p.coeff i).coeff j)).mul (hg.pow j)).mul (hf.pow i)
  simp only [zero_add] at h1
  exact h1.mono (hx i j h0.1 h0.2.1 h0.2.2) (hy i j h0.1 h0.2.1 h0.2.2)
    (ht i j h0.1 h0.2.1 h0.2.2)

/-! ## The ℓ¹ norm under linear maps -/

theorem l1_divY_le {R : Bivar} {DX DY DT : ℕ} (hR : DegQ R DX DY DT) :
    l1 (TwoVariablePolynomial.divY R) ≤ l1 R := by
  have h1 : ∀ i j, ((TwoVariablePolynomial.divY R).coeff i).coeff j ≠ 0 →
      i < DX + 1 ∧ j < DY + 1 := fun i j h => by
    rw [BivariateCertificate.coeff_divY] at h; have := hR i (j + 1) h; omega
  have h2 : ∀ i j, (R.coeff i).coeff j ≠ 0 → i < DX + 1 ∧ j < DY + 1 + 1 := fun i j h => by
    have := hR i j h; omega
  rw [l1_eq_sum h1, l1_eq_sum h2]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_range_succ' (fun j => |(R.coeff i).coeff j|) (DY + 1)]
  simp only [BivariateCertificate.coeff_divY]
  linarith [abs_nonneg ((R.coeff i).coeff 0)]

theorem l1_derivY_le {R : Bivar} {DX DY DT : ℕ} (hR : DegQ R DX DY DT) :
    l1 (TwoVariablePolynomial.derivativeY R) ≤ DY * l1 R := by
  have h1 : ∀ i j, ((TwoVariablePolynomial.derivativeY R).coeff i).coeff j ≠ 0 →
      i < DX + 1 ∧ j < DY + 1 := fun i j h => by
    rw [BivariateCertificate.coeff_derivativeY] at h
    have := hR i (j + 1) (right_ne_zero_of_mul h); omega
  have h2 : ∀ i j, (R.coeff i).coeff j ≠ 0 → i < DX + 1 ∧ j < DY + 1 + 1 := fun i j h => by
    have := hR i j h; omega
  rw [l1_eq_sum h1, l1_eq_sum h2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_range_succ' (fun j => |(R.coeff i).coeff j|) (DY + 1), mul_add, Finset.mul_sum]
  have hz : (0 : ℚ) ≤ DY * |(R.coeff i).coeff 0| := by positivity
  refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun j _ => ?_) hz
  rw [BivariateCertificate.coeff_derivativeY, abs_mul]
  by_cases h0 : (R.coeff i).coeff (j + 1) = 0
  · rw [h0]; simp
  · have := hR i (j + 1) h0
    have hj : ((j : ℚ) + 1) ≤ DY := by exact_mod_cast (show j + 1 ≤ DY by omega)
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right hj (abs_nonneg _)

theorem l1_divX_le {R : Bivar} {DX DY DT : ℕ} (hR : DegQ R DX DY DT) : l1 R.divX ≤ l1 R := by
  have h1 : ∀ i j, (R.divX.coeff i).coeff j ≠ 0 → i < DX + 1 ∧ j < DY + 1 := fun i j h => by
    rw [Polynomial.coeff_divX] at h; have := hR (i + 1) j h; omega
  have h2 : ∀ i j, (R.coeff i).coeff j ≠ 0 → i < DX + 1 + 1 ∧ j < DY + 1 := fun i j h => by
    have := hR i j h; omega
  rw [l1_eq_sum h1, l1_eq_sum h2,
    Finset.sum_range_succ' (fun i => ∑ j ∈ Finset.range (DY + 1), |(R.coeff i).coeff j|) (DX + 1)]
  simp only [Polynomial.coeff_divX]
  have : 0 ≤ ∑ j ∈ Finset.range (DY + 1), |(R.coeff 0).coeff j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  linarith

theorem l1_derivX_le {R : Bivar} {DX DY DT : ℕ} (hR : DegQ R DX DY DT) :
    l1 (Polynomial.derivative R) ≤ DX * l1 R := by
  have h1 : ∀ i j, ((Polynomial.derivative R).coeff i).coeff j ≠ 0 →
      i < DX + 1 ∧ j < DY + 1 := fun i j h => by
    rw [BivariateCertificate.coeff_derivativeX] at h
    have := hR (i + 1) j (right_ne_zero_of_mul h); omega
  have h2 : ∀ i j, (R.coeff i).coeff j ≠ 0 → i < DX + 1 + 1 ∧ j < DY + 1 := fun i j h => by
    have := hR i j h; omega
  rw [l1_eq_sum h1, l1_eq_sum h2,
    Finset.sum_range_succ' (fun i => ∑ j ∈ Finset.range (DY + 1), |(R.coeff i).coeff j|) (DX + 1),
    mul_add, Finset.mul_sum]
  have hz : (0 : ℚ) ≤ DX * ∑ j ∈ Finset.range (DY + 1), |(R.coeff 0).coeff j| := by
    have : 0 ≤ ∑ j ∈ Finset.range (DY + 1), |(R.coeff 0).coeff j| :=
      Finset.sum_nonneg fun j _ => abs_nonneg _
    positivity
  refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun i _ => ?_) hz
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [BivariateCertificate.coeff_derivativeX, abs_mul]
  by_cases h0 : (R.coeff (i + 1)).coeff j = 0
  · rw [h0]; simp
  · have := hR (i + 1) j h0
    have hi : ((i : ℚ) + 1) ≤ DX := by exact_mod_cast (show i + 1 ≤ DX by omega)
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right hi (abs_nonneg _)

/-- A substitution by polynomials of norm at most one does not increase the norm. -/
theorem l1_substitute_le (f g R : Bivar) (hf : l1 f ≤ 1) (hg : l1 g ≤ 1) :
    l1 (TwoVariablePolynomial.substitute f g R) ≤ l1 R := by
  have hR : l1 R = ∑ i ∈ R.support, l1u (R.coeff i) := by rw [l1, gsum, Polynomial.sum_def]
  rw [substitute_eq_sum, hR]
  refine (l1_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hRi : l1u (R.coeff i) = ∑ j ∈ (R.coeff i).support, |(R.coeff i).coeff j| := by
    rw [l1u, gsum, Polynomial.sum_def]
  rw [hRi]
  refine (l1_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (l1_mul_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_left ((l1_pow_le f i).trans (pow_le_one₀ (l1_nonneg f) hf))
    (l1_nonneg _)).trans ?_
  rw [mul_one]
  refine (l1_mul_le _ _).trans ?_
  rw [l1_scalar]
  exact mul_le_of_le_one_right (abs_nonneg _) ((l1_pow_le g j).trans (pow_le_one₀ (l1_nonneg g) hg))

theorem l1_X : l1 (X : Bivar) = 1 := by
  rw [← Polynomial.monomial_one_one_eq_X, l1_monomial, ← map_one C, l1u_C, abs_one]

theorem l1_Y : l1 (C X : Bivar) = 1 := by
  rw [l1_C, ← Polynomial.monomial_one_one_eq_X, l1u_monomial, abs_one]

theorem l1_one : l1 (1 : Bivar) = 1 := by
  rw [← map_one C, l1_C, ← map_one C, l1u_C, abs_one]

theorem l1_half_add_le {u : Bivar} (hu : l1 u ≤ 1) : l1 (scalar (1 / 2) * (u + 1)) ≤ 1 := by
  refine (l1_scalar_mul _ _).trans ?_
  have := l1_add_le u 1
  rw [l1_one] at this
  rw [abs_of_pos (by norm_num)]
  linarith

theorem l1_unitX : l1 TwoVariablePolynomial.unitX ≤ 1 := l1_half_add_le l1_X.le
theorem l1_unitY : l1 TwoVariablePolynomial.unitY ≤ 1 := l1_half_add_le l1_Y.le

theorem one_sub_unitY : 1 - TwoVariablePolynomial.unitY = scalar (1 / 2) * (-(C X : Bivar) + 1) := by
  apply BivariateCertificate.eq_of_evaluate; intro x y
  simp [TwoVariablePolynomial.unitY]; ring

theorem l1_one_sub_unitY : l1 (1 - TwoVariablePolynomial.unitY) ≤ 1 := by
  rw [one_sub_unitY]; exact l1_half_add_le (by rw [l1_neg, l1_Y])

theorem degQ_unitX : DegQ TwoVariablePolynomial.unitX 1 0 1 := by
  have h := (DegQ.scalar (1 / 2)).mul (degQ_X.add (DegQ.one.mono (by omega) le_rfl (by omega)))
  simpa [TwoVariablePolynomial.unitX] using h

theorem degQ_unitY : DegQ TwoVariablePolynomial.unitY 0 1 1 := by
  have h := (DegQ.scalar (1 / 2)).mul (degQ_Y.add (DegQ.one.mono le_rfl (by omega) (by omega)))
  simpa [TwoVariablePolynomial.unitY] using h

theorem degQ_one_sub_unitY : DegQ (1 - TwoVariablePolynomial.unitY) 0 1 1 := by
  rw [one_sub_unitY]
  have h := (DegQ.scalar (1 / 2)).mul (degQ_Y.neg.add (DegQ.one.mono le_rfl (by omega) (by omega)))
  simpa using h

/-! ## Exact models -/

open PackedModels BivariateCertificate

theorem l1_mapQ_ofFun (c : Config) (d : ℕ → ℕ → ℕ) :
    l1 (mapQ (ofFun c d)) ≤ (dsum (ofFun c d) : ℚ) := by
  rw [dsum_ofFun]; push_cast
  simp only [ofFun, map_sum]
  refine (l1_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (l1_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rw [mapQ, Polynomial.coe_mapRingHom, Polynomial.map_monomial, Polynomial.coe_mapRingHom,
    Polynomial.map_monomial, l1_monomial, l1u_monomial, eq_natCast, Nat.abs_cast]

theorem l1_val_le {c : Config} {m : XM} (g : m.Good c) : l1 (m.val c) ≤ (m.sz : ℚ) := by
  rw [XM.val, sub_eq_add_neg]
  refine (l1_add_le _ _).trans ?_
  rw [l1_neg]
  have h1 := l1_mapQ_ofFun c (coeffs c m.U)
  have h2 := l1_mapQ_ofFun c (coeffs c m.V)
  have hs : ((dsum (poly c m.U) + dsum (poly c m.V) : ℕ) : ℚ) ≤ m.sz := by exact_mod_cast g.size
  push_cast at hs
  exact (add_le_add h1 h2).trans hs

/-- The value of a good model vanishes outside its support. -/
theorem degQ_val {c : Config} {m : XM} (g : m.Good c) : DegQ (m.val c) m.dx m.dy m.dt := by
  intro i j h
  rw [XM.coeff_val g] at h
  split_ifs at h with hij
  · by_cases hU : coeffs c m.U i j = 0
    · have hV : coeffs c m.V i j ≠ 0 := fun h0 => h (by rw [hU, h0]; simp)
      exact g.suppV i j (by rw [cf_poly, ite_eq_left hij]; exact hV)
    · exact g.suppU i j (by rw [cf_poly, ite_eq_left hij]; exact hU)
  · exact absurd rfl h

/-! ## Digit maps -/

/-- Maps the `2 ^ k` digits of width `w₁` of `N` through `f` into digits of width `w₂`, by halves. -/
def digitMapZ (w₁ w₂ : ℕ) (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, N => f N
  | k + 1, N => if N == 0 then 0 else
      digitMapZ w₁ w₂ f k (N &&& ((1 <<< (w₁ * 2 ^ k)) - 1)) +
        (digitMapZ w₁ w₂ f k (N >>> (w₁ * 2 ^ k)) <<< (w₂ * 2 ^ k))

theorem digitMapZ_eq (w₁ w₂ : ℕ) {f : ℕ → ℕ} (hf : f 0 = 0) :
    ∀ k N, N < 2 ^ (w₁ * 2 ^ k) →
      digitMapZ w₁ w₂ f k N = ∑ u ∈ Finset.range (2 ^ k), f (digit w₁ N u) * (2 ^ w₂) ^ u
  | 0, N, h => by
    rw [digitMapZ, pow_zero, Finset.sum_range_one, pow_zero, mul_one, digit_zero_right,
      Nat.mod_eq_of_lt (by simpa using h)]
  | k + 1, N, h => by
    rw [digitMapZ]
    by_cases hN : N = 0
    · subst hN
      simp [digit, hf]
    · rw [ite_eq_right (by simpa using hN)]
      have hpow : 2 ^ (w₁ * 2 ^ (k + 1)) = 2 ^ (w₁ * 2 ^ k) * 2 ^ (w₁ * 2 ^ k) := by
        rw [← pow_add]; congr 1; ring
      have hlo : N &&& ((1 <<< (w₁ * 2 ^ k)) - 1) = N % 2 ^ (w₁ * 2 ^ k) := by
        rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
      have hhi : N >>> (w₁ * 2 ^ k) < 2 ^ (w₁ * 2 ^ k) := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_lt_of_lt_mul (by rw [← hpow]; exact h)
      rw [hlo, digitMapZ_eq w₁ w₂ hf k _ (Nat.mod_lt _ (by positivity)),
        digitMapZ_eq w₁ w₂ hf k _ hhi, Nat.shiftLeft_eq, pow_succ, mul_two, Finset.sum_range_add,
        Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun u hu => ?_
        rw [digit_mod, ite_eq_left (Finset.mem_range.mp hu)]
      · refine Finset.sum_congr rfl fun v _ => ?_
        rw [digit_shiftRight, pow_add, pow_mul, add_comm v]
        ring

/-- The number of halvings of the digit maps: boxes of at most `2 ^ 12` digits. -/
def digitDepth : ℕ := 12

theorem digitMapZ_pack {c₁ c₂ : Config} (hS : c₁.S = c₂.S) {f : ℕ → ℕ} (hf : f 0 = 0) {N : ℕ}
    (hN : Box c₁ N) {k : ℕ} (hlt : c₁.S * c₁.S ≤ 2 ^ k) :
    digitMapZ c₁.w c₂.w f k N = pack c₂ (fun i j => f (coeffs c₁ N i j)) := by
  have hbox : N < 2 ^ (c₁.w * 2 ^ k) := by
    have h1 : c₁.b ^ (c₁.S * c₁.S) ≤ c₁.b ^ 2 ^ k := Nat.pow_le_pow_right c₁.b_pos hlt
    rw [pow_mul]
    exact lt_of_lt_of_le hN h1
  rw [digitMapZ_eq c₁.w c₂.w hf k N hbox, pack_eq_sum, ← hS,
    ← Nat.add_sub_cancel' hlt, Finset.sum_range_add]
  have hzero : ∑ v ∈ Finset.range (2 ^ k - c₁.S * c₁.S),
      f (digit c₁.w N (c₁.S * c₁.S + v)) * (2 ^ c₂.w) ^ (c₁.S * c₁.S + v) = 0 := by
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [digit_of_lt (lt_of_lt_of_le hN (Nat.pow_le_pow_right c₁.b_pos (by omega))), hf, zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [PackedModels.coeffs, Nat.div_add_mod]
  rfl

/-- Clearing the low `L` bits of every digit, then shifting: every digit divided by `2 ^ L`. -/
theorem round_box {c : Config} (hw : 1 ≤ c.w) {L : ℕ} (hL : L ≤ c.w) (N : ℕ) :
    (N &&& boxPat c (c.b - 2 ^ L)) >>> L = pack c (fun i j => coeffs c N i j / 2 ^ L) := by
  have hbm : c.b - 2 ^ L < c.b := Nat.sub_lt c.b_pos (by positivity)
  have h1 : N &&& boxPat c (c.b - 2 ^ L) = pack c (fun i j => 2 ^ L * (coeffs c N i j / 2 ^ L)) := by
    apply land_pattern (P := boxPat c (c.b - 2 ^ L))
      (by rw [boxPat_eq c hw]; exact pack_box c (fun _ _ => hbm))
    · intro i j hi hj
      rw [boxPat_eq c hw, coeffs_pack c (fun _ _ => hbm) hi hj]
      exact land_high hL (coeffs_lt c N i j)
    · intro i j
      exact lt_of_le_of_lt (Nat.mul_div_le _ _) (coeffs_lt c N i j)
  rw [h1, Nat.shiftRight_eq_div_pow]
  have h2 : pack c (fun i j => 2 ^ L * (coeffs c N i j / 2 ^ L)) =
      pack c (fun i j => coeffs c N i j / 2 ^ L) * 2 ^ L := by
    rw [pack_mul_const]; congr 1; funext i j; ring
  rw [h2, Nat.mul_div_cancel _ (by positivity)]

/-! ## Exact models in another packing -/

/-- The exact model `m` in the packing `c'` (the same box, other digits). -/
def repackM (c c' : Config) (m : XM) : XM :=
  ⟨digitMapZ c.w c'.w id digitDepth m.U, digitMapZ c.w c'.w id digitDepth m.V, m.s, m.dx, m.dy,
    m.dt, m.sz, m.ok && (c.S == c'.S) && Nat.ble (c.S * c.S) (2 ^ digitDepth) &&
      XM.fits c' m.sz m.dx m.dy⟩

theorem rep_repackM {c c' : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) :
    (repackM c c' m).Rep c' p := by
  intro hok
  simp only [repackM, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hok
  obtain ⟨⟨⟨hok, hS⟩, hk⟩, hfit⟩ := hok
  obtain ⟨g, v⟩ := hm hok
  obtain ⟨hsmall, hdx, hdy⟩ := XM.fits_spec hfit
  have hU := digitMapZ_pack (c₂ := c') hS (f := id) rfl g.boxU hk
  have hV := digitMapZ_pack (c₂ := c') hS (f := id) rfl g.boxV hk
  simp only [id] at hU hV
  have hlt : ∀ (N : ℕ), Box c N → dsum (poly c N) ≤ m.sz → ∀ i j, coeffs c N i j < c'.b :=
    fun N hN hN' i j => lt_of_le_of_lt ((XM.digit_le_dsum hN _).trans hN') (XM.small_lt_b c' hsmall)
  have hUlt := hlt _ g.boxU ((Nat.le_add_right _ _).trans g.size)
  have hVlt := hlt _ g.boxV ((Nat.le_add_left _ _).trans g.size)
  have hsupp : ∀ (N : ℕ), Supp (poly c N) m.dx m.dy m.dt → ∀ i j, i < c'.S → j < c'.S →
      coeffs c N i j ≠ 0 → i ≤ m.dx ∧ j ≤ m.dy ∧ i + j ≤ m.dt := fun N hN i j hi hj h =>
    hN i j (by rw [cf_poly, ite_eq_left ⟨hS ▸ hi, hS ▸ hj⟩]; exact h)
  have hsum : ∑ i ∈ Finset.range c'.S, ∑ j ∈ Finset.range c'.S,
      (coeffs c m.U i j + coeffs c m.V i j) ≤ m.sz := by
    have eU : ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, coeffs c m.U i j =
        dsum (poly c m.U) := dsumN_eq c m.U
    have eV : ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, coeffs c m.V i j =
        dsum (poly c m.V) := dsumN_eq c m.V
    simp only [Finset.sum_add_distrib, ← hS, eU, eV]
    exact g.size
  have hgood : (repackM c c' m).Good c' :=
    XM.good_pack _ hU hV hUlt hVlt (hsupp _ g.suppU) (hsupp _ g.suppV) hsum hsmall hdx hdy
  refine ⟨hgood, ?_⟩
  have hv : (repackM c c' m).val c' = m.val c := by
    refine XM.val_pack hU hV hUlt hVlt fun i j => ?_
    rw [XM.coeff_val g, hS]
  rw [hv, v]; rfl

theorem truncTot_truncTot (T : ℕ) (p : Bivar) : truncTot T (truncTot T p) = truncTot T p := by
  ext a b
  rw [coeff_truncTot, coeff_truncTot]
  split_ifs <;> rfl

/-- The cubic mass reads only the truncation to total degree three. -/
theorem cubicMass_truncTot (ρ : ℚ) (p : Bivar) :
    TwoVariablePolynomial.cubicMass ρ (truncTot 3 p) = TwoVariablePolynomial.cubicMass ρ p := by
  have h1 : TwoVariablePolynomial.truncate3 (truncTot 3 p) = TwoVariablePolynomial.truncate3 p := by
    rw [truncate3_eq, truncate3_eq, truncTot_truncTot]
  have h2 : TwoVariablePolynomial.constant (truncTot 3 p) = TwoVariablePolynomial.constant p := by
    rw [TwoVariablePolynomial.constant, TwoVariablePolynomial.constant, coeff_truncTot,
      ite_eq_left (by norm_num)]
  simp only [TwoVariablePolynomial.cubicMass, h1, h2]

/-! ## Rounded models -/

/-- A rounded model: an exact model `m` of an approximation, a bound `e` on the error of its
numerator, and degree bounds `ex`, `ey`, `et` of the represented polynomial. -/
structure XE where
  m : XM
  e : ℕ
  ex : ℕ
  ey : ℕ
  et : ℕ

namespace XE

/-- `x` represents `p`: the numerator `x.m.val` is `x.m.s · p` within `x.e` in ℓ¹ norm. -/
def Rep (c : Config) (x : XE) (p : Bivar) : Prop :=
  x.m.ok = true → x.m.Good c ∧ 0 < x.m.s ∧ DegQ p x.ex x.ey x.et ∧
    l1 (scalar (x.m.s : ℚ) * p - x.m.val c) ≤ x.e

/-- The polynomial that the exact part represents. -/
def approx (c : Config) (x : XE) : Bivar := scalar (1 / (x.m.s : ℚ)) * x.m.val c

theorem rep_approx {c : Config} {x : XE} (hs : 0 < x.m.s) (g : x.m.Good c) :
    x.m.Rep c (approx c x) := fun _ => by
  refine ⟨g, ?_⟩
  have hs' : (x.m.s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [approx, ← mul_assoc, ← scalar_mul, mul_one_div_cancel hs', show scalar 1 = 1 by
    simp [TensorWholeIntervalPolynomial.scalar], one_mul]

/-- An exact model, with no error. -/
def ofXM (m : XM) : XE := ⟨XM.guard m (Nat.blt 0 m.s), 0, m.dx, m.dy, m.dt⟩

theorem rep_ofXM {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) : (ofXM m).Rep c p := by
  intro hok
  simp only [ofXM, XM.guard, Bool.and_eq_true, Nat.blt_eq] at hok
  obtain ⟨g, v⟩ := hm hok.1
  have hs : (m.s : ℚ) ≠ 0 := by exact_mod_cast hok.2.ne'
  refine ⟨⟨g.boxU, g.boxV, g.suppU, g.suppV, g.size, g.small, g.dxS, g.dyS⟩, hok.2, ?_, ?_⟩
  · intro i j hij
    have h := degQ_val g i j
    rw [v, XM.coeff_scalar_mul] at h
    exact h (mul_ne_zero hs hij)
  · show l1 (scalar (m.s : ℚ) * p - m.val c) ≤ 0
    rw [v, sub_self, l1_zero]

/-- `a + b`. -/
def add (c : Config) (a b : XE) : XE :=
  ⟨XM.add c a.m b.m, a.e * (b.m.s / Nat.gcd a.m.s b.m.s) + b.e * (a.m.s / Nat.gcd a.m.s b.m.s),
    max a.ex b.ex, max a.ey b.ey, max a.et b.et⟩

theorem rep_add {c : Config} {a b : XE} {p q : Bivar} (ha : a.Rep c p) (hb : b.Rep c q) :
    (add c a b).Rep c (p + q) := by
  intro hok
  dsimp only [add] at hok ⊢
  have hok' := hok
  simp only [XM.add, Bool.and_eq_true] at hok'
  obtain ⟨ga, hsa, da, ea⟩ := ha hok'.1.1
  obtain ⟨gb, hsb, db, eb⟩ := hb hok'.1.2
  obtain ⟨g', v'⟩ := XM.rep_add (rep_approx hsa ga) (rep_approx hsb gb) hok
  set g := Nat.gcd a.m.s b.m.s with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hsa
  have hkb : g ∣ a.m.s := Nat.gcd_dvd_left _ _
  have hs' : (XM.add c a.m b.m).s = a.m.s / g * b.m.s := rfl
  have hpos : 0 < a.m.s / g := Nat.div_pos (Nat.le_of_dvd hsa hkb) hg0
  refine ⟨g', by rw [hs']; positivity, (da.mono (le_max_left _ _) (le_max_left _ _)
    (le_max_left _ _)).add (db.mono (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)), ?_⟩
  have e1 : ((a.m.s / g * b.m.s : ℕ) : ℚ) = ((b.m.s / g : ℕ) : ℚ) * a.m.s := by
    exact_mod_cast (lcm_eq a.m.s b.m.s).symm
  have e2 : ((a.m.s / g * b.m.s : ℕ) : ℚ) = ((a.m.s / g : ℕ) : ℚ) * b.m.s := by push_cast; ring
  have hsa' : (a.m.s : ℚ) ≠ 0 := by exact_mod_cast hsa.ne'
  have hsb' : (b.m.s : ℚ) ≠ 0 := by exact_mod_cast hsb.ne'
  have hA : scalar ((a.m.s / g * b.m.s : ℕ) : ℚ) * scalar (1 / (a.m.s : ℚ)) =
      scalar ((b.m.s / g : ℕ) : ℚ) := by
    rw [← scalar_mul, e1, mul_assoc, mul_one_div_cancel hsa', mul_one]
  have hB : scalar ((a.m.s / g * b.m.s : ℕ) : ℚ) * scalar (1 / (b.m.s : ℚ)) =
      scalar ((a.m.s / g : ℕ) : ℚ) := by
    rw [← scalar_mul, e2, mul_assoc, mul_one_div_cancel hsb', mul_one]
  have hC : scalar ((a.m.s / g * b.m.s : ℕ) : ℚ) =
      scalar ((b.m.s / g : ℕ) : ℚ) * scalar (a.m.s : ℚ) := by rw [← scalar_mul, e1]
  have hD : scalar ((a.m.s / g * b.m.s : ℕ) : ℚ) =
      scalar ((a.m.s / g : ℕ) : ℚ) * scalar (b.m.s : ℚ) := by rw [← scalar_mul, e2]
  have key : scalar ((XM.add c a.m b.m).s : ℚ) * (p + q) - (XM.add c a.m b.m).val c =
      scalar ((b.m.s / g : ℕ) : ℚ) * (scalar (a.m.s : ℚ) * p - a.m.val c) +
        scalar ((a.m.s / g : ℕ) : ℚ) * (scalar (b.m.s : ℚ) * q - b.m.val c) := by
    rw [v', hs']
    simp only [approx]
    linear_combination p * hC + q * hD - a.m.val c * hA - b.m.val c * hB
  rw [key]
  refine (l1_add_le _ _).trans ?_
  have t1 := l1_scalar_mul ((b.m.s / g : ℕ) : ℚ) (scalar (a.m.s : ℚ) * p - a.m.val c)
  have t2 := l1_scalar_mul ((a.m.s / g : ℕ) : ℚ) (scalar (b.m.s : ℚ) * q - b.m.val c)
  rw [abs_of_nonneg (by positivity)] at t1 t2
  have n1 : 0 ≤ ((b.m.s / g : ℕ) : ℚ) := by positivity
  have n2 : 0 ≤ ((a.m.s / g : ℕ) : ℚ) := by positivity
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left ea n1, mul_le_mul_of_nonneg_left eb n2]

/-- `-a`. -/
def neg (a : XE) : XE := ⟨XM.neg a.m, a.e, a.ex, a.ey, a.et⟩

theorem rep_neg {c : Config} {a : XE} {p : Bivar} (ha : a.Rep c p) : (neg a).Rep c (-p) := by
  intro hok
  dsimp only [neg] at hok ⊢
  obtain ⟨ga, hsa, da, ea⟩ := ha hok
  obtain ⟨g', v'⟩ := XM.rep_neg (rep_approx hsa ga) hok
  refine ⟨g', hsa, da.neg, ?_⟩
  have hsa' : (a.m.s : ℚ) ≠ 0 := by exact_mod_cast hsa.ne'
  have hA : scalar (a.m.s : ℚ) * scalar (1 / (a.m.s : ℚ)) = 1 := by
    rw [← scalar_mul, mul_one_div_cancel hsa']; simp [TensorWholeIntervalPolynomial.scalar]
  have key : scalar ((XM.neg a.m).s : ℚ) * -p - (XM.neg a.m).val c =
      -(scalar (a.m.s : ℚ) * p - a.m.val c) := by
    rw [v']
    simp only [XM.neg, approx]
    linear_combination (a.m.val c) * hA
  rw [key, l1_neg]; exact ea

/-- `a - b`. -/
def sub (c : Config) (a b : XE) : XE := add c a (neg b)

theorem rep_sub {c : Config} {a b : XE} {p q : Bivar} (ha : a.Rep c p) (hb : b.Rep c q) :
    (sub c a b).Rep c (p - q) := by
  rw [sub_eq_add_neg]; exact rep_add ha (rep_neg hb)

/-- `a b`, without rounding. -/
def mul (c : Config) (a b : XE) : XE :=
  ⟨XM.mul c a.m b.m, a.e * (b.m.sz + b.e) + a.m.sz * b.e, a.ex + b.ex, a.ey + b.ey, a.et + b.et⟩

theorem rep_mul {c : Config} {a b : XE} {p q : Bivar} (ha : a.Rep c p) (hb : b.Rep c q) :
    (mul c a b).Rep c (p * q) := by
  intro hok
  dsimp only [mul] at hok ⊢
  have hok' := hok
  simp only [XM.mul, Bool.and_eq_true] at hok'
  obtain ⟨ga, hsa, da, ea⟩ := ha hok'.1.1
  obtain ⟨gb, hsb, db, eb⟩ := hb hok'.1.2
  obtain ⟨g', v'⟩ := XM.rep_mul (rep_approx hsa ga) (rep_approx hsb gb) hok
  have hs' : (XM.mul c a.m b.m).s = a.m.s * b.m.s := rfl
  refine ⟨g', by rw [hs']; positivity, da.mul db, ?_⟩
  have hsa' : (a.m.s : ℚ) ≠ 0 := by exact_mod_cast hsa.ne'
  have hsb' : (b.m.s : ℚ) ≠ 0 := by exact_mod_cast hsb.ne'
  have hA : scalar (a.m.s : ℚ) * scalar (1 / (a.m.s : ℚ)) = 1 := by
    rw [← scalar_mul, mul_one_div_cancel hsa']; simp [TensorWholeIntervalPolynomial.scalar]
  have hB : scalar (b.m.s : ℚ) * scalar (1 / (b.m.s : ℚ)) = 1 := by
    rw [← scalar_mul, mul_one_div_cancel hsb']; simp [TensorWholeIntervalPolynomial.scalar]
  have key : scalar ((XM.mul c a.m b.m).s : ℚ) * (p * q) - (XM.mul c a.m b.m).val c =
      (scalar (a.m.s : ℚ) * p - a.m.val c) * (scalar (b.m.s : ℚ) * q) +
        a.m.val c * (scalar (b.m.s : ℚ) * q - b.m.val c) := by
    rw [v', hs']
    simp only [approx]
    push_cast
    rw [scalar_mul]
    linear_combination (-(a.m.val c * b.m.val c)) * hA -
      (a.m.val c * b.m.val c * (scalar (a.m.s : ℚ) * scalar (1 / (a.m.s : ℚ)))) * hB
  rw [key]
  refine (l1_add_le _ _).trans ?_
  have hq : l1 (scalar (b.m.s : ℚ) * q) ≤ b.m.sz + b.e := by
    have : scalar (b.m.s : ℚ) * q = (scalar (b.m.s : ℚ) * q - b.m.val c) + b.m.val c := by ring
    rw [this]
    exact (l1_add_le _ _).trans (by linarith [l1_val_le gb])
  have t1 := l1_mul_le (scalar (a.m.s : ℚ) * p - a.m.val c) (scalar (b.m.s : ℚ) * q)
  have t2 := l1_mul_le (a.m.val c) (scalar (b.m.s : ℚ) * q - b.m.val c)
  have na := l1_val_le ga
  have h0' := l1_nonneg (scalar (b.m.s : ℚ) * q - b.m.val c)
  push_cast
  nlinarith [mul_le_mul ea hq (l1_nonneg _) (by positivity : (0 : ℚ) ≤ a.e),
    mul_le_mul na eb h0' (by positivity : (0 : ℚ) ≤ a.m.sz)]

/-! ### Digitwise rescaling -/

/-- `t u - ⌊t u⌋` and `t v - ⌊t v⌋` lie in `[0, 1)`, for `t = a / b`. -/
theorem abs_scaled_sub_le (u v a b : ℕ) (hb : 0 < b) :
    |(a : ℚ) / b * ((u : ℚ) - v) - (((u * a / b : ℕ) : ℚ) - ((v * a / b : ℕ) : ℚ))| ≤ 1 := by
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have key : ∀ n : ℕ, ((n * a / b : ℕ) : ℚ) ≤ (a : ℚ) / b * n ∧
      (a : ℚ) / b * n < ((n * a / b : ℕ) : ℚ) + 1 := by
    intro n
    have h1 : ((n * a / b : ℕ) : ℚ) * b ≤ (n * a : ℕ) := by exact_mod_cast Nat.div_mul_le_self _ _
    have h2 : ((n * a : ℕ) : ℚ) < ((n * a / b : ℕ) : ℚ) * b + b := by
      exact_mod_cast Nat.lt_div_mul_add hb
    push_cast at h1 h2
    constructor
    · rw [div_mul_eq_mul_div, le_div_iff₀ hb']; linarith
    · rw [div_mul_eq_mul_div, div_lt_iff₀ hb']; linarith
  obtain ⟨u1, u2⟩ := key u
  obtain ⟨v1, v2⟩ := key v
  rw [abs_le]; constructor <;> linarith

/-- The floors of the digits: `∑ ⌊F a / b⌋ ≤ ⌊(∑ F) a / b⌋`. -/
theorem sum_floor_le (S a b : ℕ) (hb : 0 < b) (F : ℕ → ℕ → ℕ) :
    ∑ i ∈ Finset.range S, ∑ j ∈ Finset.range S, F i j * a / b ≤
      (∑ i ∈ Finset.range S, ∑ j ∈ Finset.range S, F i j) * a / b := by
  rw [Nat.le_div_iff_mul_le hb, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => Nat.div_mul_le_self _ _

/-- A model whose digits are those of `x.m` times `a / b` (rounded down), at the scale
`x.m.s · a / b`: the error grows by the rounding of each coefficient. -/
theorem rep_digits {c c' : Config} {x : XE} {p : Bivar} (hx : x.Rep c p) (hok : x.m.ok = true)
    {a b : ℕ} (hb : 0 < b) (hS : c'.S = c.S) (m' : XM)
    (hU : m'.U = pack c' (fun i j => coeffs c x.m.U i j * a / b))
    (hV : m'.V = pack c' (fun i j => coeffs c x.m.V i j * a / b))
    (hs : m'.s * b = x.m.s * a) (hs0 : 0 < m'.s) (hsz : x.m.sz * a / b ≤ m'.sz)
    (hsmall : m'.sz < 2 ^ (c'.w - 2)) (hdx : m'.dx = x.m.dx) (hdy : m'.dy = x.m.dy)
    (hdt : m'.dt = x.m.dt) :
    m'.Good c' ∧ 0 < m'.s ∧ DegQ p x.ex x.ey x.et ∧
      l1 (scalar (m'.s : ℚ) * p - m'.val c') ≤
        ((x.e * a / b + 1 + (x.m.dx + 1) * (x.m.dy + 1) : ℕ) : ℚ) := by
  obtain ⟨g, -, hd, he⟩ := hx hok
  set dU : ℕ → ℕ → ℕ := fun i j => coeffs c x.m.U i j * a / b with hdU
  set dV : ℕ → ℕ → ℕ := fun i j => coeffs c x.m.V i j * a / b with hdV
  have hlt : ∀ (N : ℕ), Box c N → dsum (poly c N) ≤ x.m.sz → ∀ i j,
      coeffs c N i j * a / b < c'.b := fun N hN hN' i j =>
    calc coeffs c N i j * a / b ≤ x.m.sz * a / b :=
          Nat.div_le_div_right (Nat.mul_le_mul_right a ((XM.digit_le_dsum hN _).trans hN'))
      _ ≤ m'.sz := hsz
      _ < c'.b := XM.small_lt_b c' hsmall
  have hdUlt : ∀ i j, dU i j < c'.b :=
    hlt _ g.boxU ((Nat.le_add_right _ _).trans g.size)
  have hdVlt : ∀ i j, dV i j < c'.b :=
    hlt _ g.boxV ((Nat.le_add_left _ _).trans g.size)
  have hsupp : ∀ (N : ℕ), Supp (poly c N) x.m.dx x.m.dy x.m.dt → ∀ i j, i < c'.S → j < c'.S →
      coeffs c N i j * a / b ≠ 0 → i ≤ m'.dx ∧ j ≤ m'.dy ∧ i + j ≤ m'.dt := by
    intro N hN i j hi hj h
    have h0 : coeffs c N i j ≠ 0 := fun h0 => h (by rw [h0]; simp)
    rw [hdx, hdy, hdt]
    exact hN i j (by rw [cf_poly, ite_eq_left ⟨hS ▸ hi, hS ▸ hj⟩]; exact h0)
  have hsum : ∑ i ∈ Finset.range c'.S, ∑ j ∈ Finset.range c'.S, (dU i j + dV i j) ≤ m'.sz := by
    have eU : ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, coeffs c x.m.U i j =
        dsum (poly c x.m.U) := dsumN_eq c x.m.U
    have eV : ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, coeffs c x.m.V i j =
        dsum (poly c x.m.V) := dsumN_eq c x.m.V
    have hfU := sum_floor_le c.S a b hb (coeffs c x.m.U)
    have hfV := sum_floor_le c.S a b hb (coeffs c x.m.V)
    rw [eU] at hfU
    rw [eV] at hfV
    simp only [Finset.sum_add_distrib, hS]
    calc _ ≤ dsum (poly c x.m.U) * a / b + dsum (poly c x.m.V) * a / b := add_le_add hfU hfV
      _ ≤ (dsum (poly c x.m.U) * a + dsum (poly c x.m.V) * a) / b := Nat.div_add_div_le_add_div
      _ ≤ x.m.sz * a / b := Nat.div_le_div_right (by rw [← add_mul]; exact Nat.mul_le_mul_right a g.size)
      _ ≤ m'.sz := hsz
  have hgood : m'.Good c' := by
    obtain ⟨U', V', s', dx', dy', dt', sz', o'⟩ := m'
    simp only at hU hV hdx hdy hdt hsum hsmall ⊢
    exact XM.good_pack o' hU hV hdUlt hdVlt (hsupp _ g.suppU) (hsupp _ g.suppV) hsum hsmall
      (by rw [hdx, hS]; exact g.dxS) (by rw [hdy, hS]; exact g.dyS)
  refine ⟨hgood, hs0, hd, ?_⟩
  -- the error: the old one scaled by `a / b`, plus the rounding of each coefficient
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have hst : (m'.s : ℚ) = (a : ℚ) / b * x.m.s := by
    have h : (m'.s : ℚ) * b = x.m.s * a := by exact_mod_cast hs
    field_simp; linarith
  have split : scalar (m'.s : ℚ) * p - m'.val c' =
      scalar ((a : ℚ) / b) * (scalar (x.m.s : ℚ) * p - x.m.val c) +
        (scalar ((a : ℚ) / b) * x.m.val c - m'.val c') := by
    rw [hst, scalar_mul]; ring
  rw [split]
  refine (l1_add_le _ _).trans ?_
  have t1 : l1 (scalar ((a : ℚ) / b) * (scalar (x.m.s : ℚ) * p - x.m.val c)) ≤
      ((x.e * a / b : ℕ) : ℚ) + 1 := by
    refine (l1_scalar_mul _ _).trans ?_
    rw [abs_of_nonneg (by positivity)]
    have h1 : (a : ℚ) / b * l1 (scalar (x.m.s : ℚ) * p - x.m.val c) ≤ (a : ℚ) / b * x.e :=
      mul_le_mul_of_nonneg_left he (by positivity)
    have h2 : ((x.e * a : ℕ) : ℚ) < ((x.e * a / b : ℕ) : ℚ) * b + b := by
      exact_mod_cast Nat.lt_div_mul_add hb
    push_cast at h2
    have h3 : (a : ℚ) / b * x.e < ((x.e * a / b : ℕ) : ℚ) + 1 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hb']; linarith
    linarith
  have hcoef : ∀ i j, ((scalar ((a : ℚ) / b) * x.m.val c - m'.val c').coeff i).coeff j =
      if i < c.S ∧ j < c.S then (a : ℚ) / b * ((coeffs c x.m.U i j : ℚ) - coeffs c x.m.V i j) -
        (((dU i j : ℕ) : ℚ) - ((dV i j : ℕ) : ℚ)) else 0 := by
    intro i j
    rw [Polynomial.coeff_sub, Polynomial.coeff_sub, XM.coeff_scalar_mul, XM.coeff_val g,
      XM.coeff_val hgood, hS]
    split_ifs with hij
    · rw [hU, hV, coeffs_pack c' hdUlt (hS ▸ hij.1) (hS ▸ hij.2),
        coeffs_pack c' hdVlt (hS ▸ hij.1) (hS ▸ hij.2)]
    · simp
  have hzero : ∀ i j, ((scalar ((a : ℚ) / b) * x.m.val c - m'.val c').coeff i).coeff j ≠ 0 →
      i < x.m.dx + 1 ∧ j < x.m.dy + 1 := by
    intro i j h
    rw [hcoef] at h
    split_ifs at h with hij
    · by_cases hU0 : coeffs c x.m.U i j = 0
      · by_cases hV0 : coeffs c x.m.V i j = 0
        · exfalso; apply h; simp [hdU, hdV, hU0, hV0]
        · have := g.suppV i j (by rw [cf_poly, ite_eq_left hij]; exact hV0); omega
      · have := g.suppU i j (by rw [cf_poly, ite_eq_left hij]; exact hU0); omega
    · exact absurd rfl h
  have t2 : l1 (scalar ((a : ℚ) / b) * x.m.val c - m'.val c') ≤
      (((x.m.dx + 1) * (x.m.dy + 1) : ℕ) : ℚ) := by
    rw [l1_eq_sum hzero]
    calc _ ≤ ∑ i ∈ Finset.range (x.m.dx + 1), ∑ j ∈ Finset.range (x.m.dy + 1), (1 : ℚ) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [hcoef]
          split_ifs
          · exact abs_scaled_sub_le _ _ a b hb
          · simp
      _ = _ := by simp; ring
  push_cast at t1 t2 ⊢
  linarith

/-- Every digit divided by `2 ^ L` (rounding down), and the scale too. -/
def roundM (c : Config) (L : ℕ) (m : XM) : XM :=
  ⟨(m.U &&& boxPat c (c.b - (1 <<< L))) >>> L, (m.V &&& boxPat c (c.b - (1 <<< L))) >>> L,
    m.s >>> L, m.dx, m.dy, m.dt, m.sz >>> L,
    m.ok && (m.s &&& ((1 <<< L) - 1) == 0) && Nat.ble L c.w && Nat.ble 1 c.w &&
      Nat.blt 0 (m.s >>> L)⟩

/-- `x` at the scale `x.m.s / 2 ^ L`. -/
def round (c : Config) (L : ℕ) (x : XE) : XE :=
  ⟨roundM c L x.m, (x.e >>> L) + 1 + (x.m.dx + 1) * (x.m.dy + 1), x.ex, x.ey, x.et⟩

theorem rep_round {c : Config} {x : XE} {p : Bivar} (hx : x.Rep c p) (L : ℕ) :
    (round c L x).Rep c p := by
  intro hok
  dsimp only [round, roundM] at hok ⊢
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq, Nat.blt_eq] at hok
  obtain ⟨⟨⟨⟨hok, hmod⟩, hL⟩, hw⟩, hs0⟩ := hok
  have hdvd : x.m.s % 2 ^ L = 0 := by
    rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod] at hmod; exact hmod
  have h := rep_digits hx hok (a := 1) (b := 2 ^ L) (by positivity) rfl
    ⟨(x.m.U &&& boxPat c (c.b - (1 <<< L))) >>> L, (x.m.V &&& boxPat c (c.b - (1 <<< L))) >>> L,
      x.m.s >>> L, x.m.dx, x.m.dy, x.m.dt, x.m.sz >>> L, true⟩
    (by simp only [mul_one]; rw [Nat.one_shiftLeft]; exact round_box hw hL _)
    (by simp only [mul_one]; rw [Nat.one_shiftLeft]; exact round_box hw hL _)
    (by simp only [mul_one, Nat.shiftRight_eq_div_pow]; exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdvd))
    hs0 (by simp [Nat.shiftRight_eq_div_pow])
    (by
      simp only [Nat.shiftRight_eq_div_pow]
      obtain ⟨g, -⟩ := hx hok
      exact lt_of_le_of_lt (Nat.div_le_self _ _) g.small)
    rfl rfl rfl
  simp only [mul_one, Nat.shiftRight_eq_div_pow] at h ⊢
  obtain ⟨g', h1, h2, h3⟩ := h
  exact ⟨⟨g'.boxU, g'.boxV, g'.suppU, g'.suppV, g'.size, g'.small, g'.dxS, g'.dyS⟩, h1, h2, h3⟩

/-- `a b`, rounded back by `L` bits. -/
def mulR (c : Config) (L : ℕ) (a b : XE) : XE := round c L (mul c a b)

theorem rep_mulR {c : Config} {a b : XE} {p q : Bivar} (ha : a.Rep c p) (hb : b.Rep c q)
    (L : ℕ) : (mulR c L a b).Rep c (p * q) := rep_round (rep_mul ha hb) L

/-- `p q` with the factors exchanged: the smaller model goes on the right, where the
multiplication of the packed numbers is cheap for an external kernel. -/
theorem rep_mulR_swap {c : Config} {a b : XE} {p q : Bivar} (ha : a.Rep c p) (hb : b.Rep c q)
    (L : ℕ) : (mulR c L b a).Rep c (p * q) := by
  rw [mul_comm]; exact rep_mulR hb ha L

/-- Every digit times `a / b` (rounding down), from the packing `c` into `c'`, at the scale `s'`;
`s' b = s a` is checked. -/
def scaleM (c c' : Config) (a b s' : ℕ) (m : XM) : XM :=
  ⟨digitMapZ c.w c'.w (fun d => d * a / b) digitDepth m.U,
    digitMapZ c.w c'.w (fun d => d * a / b) digitDepth m.V, s', m.dx, m.dy, m.dt,
    m.sz * a / b, m.ok && (c.S == c'.S) && Nat.ble (c.S * c.S) (2 ^ digitDepth) &&
      XM.fits c' (m.sz * a / b) m.dx m.dy && Nat.blt 0 b && Nat.blt 0 s' && (s' * b == m.s * a)⟩

/-- `x` in the packing `c'` at the scale `s' = x.m.s · a / b`. -/
def scale (c c' : Config) (a b s' : ℕ) (x : XE) : XE :=
  ⟨scaleM c c' a b s' x.m, x.e * a / b + 1 + (x.m.dx + 1) * (x.m.dy + 1), x.ex, x.ey, x.et⟩

theorem rep_scale {c c' : Config} {x : XE} {p : Bivar} (hx : x.Rep c p) (a b s' : ℕ) :
    (scale c c' a b s' x).Rep c' p := by
  intro hok
  dsimp only [scale, scaleM] at hok ⊢
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, Nat.ble_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨hok, hS⟩, hk⟩, hfit⟩, hb⟩, hs0⟩, hs⟩ := hok
  obtain ⟨g, -⟩ := hx hok
  have hf : (fun d => d * a / b) 0 = 0 := by simp
  have h := rep_digits hx hok hb hS.symm
    ⟨digitMapZ c.w c'.w (fun d => d * a / b) digitDepth x.m.U,
      digitMapZ c.w c'.w (fun d => d * a / b) digitDepth x.m.V, s', x.m.dx, x.m.dy,
      x.m.dt, x.m.sz * a / b, true⟩
    (digitMapZ_pack hS hf g.boxU hk) (digitMapZ_pack hS hf g.boxV hk) hs hs0 le_rfl
    (XM.fits_spec hfit).1 rfl rfl rfl
  obtain ⟨g', h1, h2, h3⟩ := h
  exact ⟨⟨g'.boxU, g'.boxV, g'.suppU, g'.suppV, g'.size, g'.small, g'.dxS, g'.dyS⟩, h1, h2, h3⟩

/-- `x` at the scale `2 ^ K`, in the packing `c'`. -/
def toScale (c c' : Config) (K : ℕ) (x : XE) : XE := scale c c' (1 <<< K) x.m.s (1 <<< K) x

theorem rep_toScale {c c' : Config} {x : XE} {p : Bivar} (hx : x.Rep c p) (K : ℕ) :
    (toScale c c' K x).Rep c' p := rep_scale hx _ _ _

/-- `x` in the packing `c'`, at its scale. -/
def repack (c c' : Config) (x : XE) : XE := scale c c' 1 1 x.m.s x

theorem rep_repack {c c' : Config} {x : XE} {p : Bivar} (hx : x.Rep c p) :
    (repack c c' x).Rep c' p := rep_scale hx _ _ _

/-- An exact model at the scale `2 ^ K`, in the packing `c'`. -/
def ofXMAt (c c' : Config) (K : ℕ) (m : XM) : XE := toScale c c' K (ofXM m)

theorem rep_ofXMAt {c c' : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) (K : ℕ) :
    (ofXMAt c c' K m).Rep c' p := rep_toScale (rep_ofXM hm) K

/-! ### Linear maps -/

/-- The model `op x.m` of the image under a linear map, with the error scaled by the growth of
the scale and by the bound `lam` of the map. -/
def lin (op : XM → XM) (lam ex ey et : ℕ) (x : XE) : XE :=
  ⟨XM.guard (op x.m) (x.m.ok && Nat.blt 0 x.m.s && Nat.blt 0 (op x.m).s &&
      ((op x.m).s % x.m.s == 0)), (op x.m).s / x.m.s * lam * x.e, ex, ey, et⟩

theorem rep_lin {c : Config} {x : XE} {p : Bivar} (hx : x.Rep c p) {op : XM → XM}
    {Lf : Bivar → Bivar} (hop : ∀ q, x.m.Rep c q → (op x.m).Rep c (Lf q))
    (hsub : ∀ q₁ q₂, Lf (q₁ - q₂) = Lf q₁ - Lf q₂)
    (hsmul : ∀ r q, Lf (scalar r * q) = scalar r * Lf q) {lam ex ey et : ℕ}
    (hbound : ∀ R, DegQ R (max x.ex x.m.dx) (max x.ey x.m.dy) (max x.et x.m.dt) →
      l1 (Lf R) ≤ lam * l1 R)
    (hdeg : DegQ p x.ex x.ey x.et → DegQ (Lf p) ex ey et) :
    (lin op lam ex ey et x).Rep c (Lf p) := by
  intro hok
  dsimp only [lin, XM.guard] at hok ⊢
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hok
  obtain ⟨hop_ok, ⟨⟨hxok, hs⟩, hs'⟩, hdvd⟩ := hok
  obtain ⟨g, -, hd, he⟩ := hx hxok
  obtain ⟨g', v'⟩ := hop _ (rep_approx hs g) hop_ok
  refine ⟨⟨g'.boxU, g'.boxV, g'.suppU, g'.suppV, g'.size, g'.small, g'.dxS, g'.dyS⟩, hs',
    hdeg hd, ?_⟩
  have hsq : (x.m.s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
  have hdiv : (((op x.m).s / x.m.s : ℕ) : ℚ) = ((op x.m).s : ℚ) / x.m.s :=
    Nat.cast_div (Nat.dvd_of_mod_eq_zero hdvd) hsq
  have hp : p - approx c x = scalar (1 / (x.m.s : ℚ)) * (scalar (x.m.s : ℚ) * p - x.m.val c) := by
    have h1 : scalar (1 / (x.m.s : ℚ)) * scalar (x.m.s : ℚ) = 1 := by
      rw [← scalar_mul, one_div_mul_cancel hsq]; simp [TensorWholeIntervalPolynomial.scalar]
    simp only [approx]
    linear_combination (-p) * h1
  have key : scalar ((op x.m).s : ℚ) * Lf p - (op x.m).val c =
      scalar ((((op x.m).s / x.m.s : ℕ) : ℚ)) * Lf (scalar (x.m.s : ℚ) * p - x.m.val c) := by
    rw [v', ← mul_sub, ← hsub, hp, hsmul, ← mul_assoc, ← scalar_mul, hdiv, mul_one_div]
  change l1 (scalar ((op x.m).s : ℚ) * Lf p - (op x.m).val c) ≤ _
  rw [key]
  have hR : DegQ (scalar (x.m.s : ℚ) * p - x.m.val c) (max x.ex x.m.dx) (max x.ey x.m.dy)
      (max x.et x.m.dt) := by
    have h1 := (DegQ.scalar (x.m.s : ℚ)).mul hd
    simp only [zero_add] at h1
    exact (h1.mono (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)).sub
      ((degQ_val g).mono (le_max_right _ _) (le_max_right _ _) (le_max_right _ _))
  refine (l1_scalar_mul _ _).trans ?_
  rw [abs_of_nonneg (by positivity)]
  have h3 : (lam : ℚ) * l1 (scalar (x.m.s : ℚ) * p - x.m.val c) ≤ lam * x.e :=
    mul_le_mul_of_nonneg_left he (by positivity)
  push_cast
  calc _ ≤ (((op x.m).s / x.m.s : ℕ) : ℚ) * (lam * x.e) :=
        mul_le_mul_of_nonneg_left ((hbound _ hR).trans h3) (by positivity)
    _ = _ := by ring

theorem divY_sub (q₁ q₂ : Bivar) : TwoVariablePolynomial.divY (q₁ - q₂) =
    TwoVariablePolynomial.divY q₁ - TwoVariablePolynomial.divY q₂ := by
  ext i j; simp only [BivariateCertificate.coeff_divY, Polynomial.coeff_sub]

theorem divY_smul (r : ℚ) (q : Bivar) : TwoVariablePolynomial.divY (scalar r * q) =
    scalar r * TwoVariablePolynomial.divY q := by
  ext i j; simp only [BivariateCertificate.coeff_divY, XM.coeff_scalar_mul]

theorem derivY_sub (q₁ q₂ : Bivar) : TwoVariablePolynomial.derivativeY (q₁ - q₂) =
    TwoVariablePolynomial.derivativeY q₁ - TwoVariablePolynomial.derivativeY q₂ := by
  ext i j; simp only [BivariateCertificate.coeff_derivativeY, Polynomial.coeff_sub]; ring

theorem derivY_smul (r : ℚ) (q : Bivar) : TwoVariablePolynomial.derivativeY (scalar r * q) =
    scalar r * TwoVariablePolynomial.derivativeY q := by
  ext i j; simp only [BivariateCertificate.coeff_derivativeY, XM.coeff_scalar_mul]; ring

theorem divX_smul (r : ℚ) (q : Bivar) : (scalar r * q).divX = scalar r * q.divX := by
  ext i j; simp only [Polynomial.coeff_divX, XM.coeff_scalar_mul]

theorem divX_sub' (q₁ q₂ : Bivar) : (q₁ - q₂).divX = q₁.divX - q₂.divX := by
  ext i j; simp only [Polynomial.coeff_divX, Polynomial.coeff_sub]

theorem derivX_smul (r : ℚ) (q : Bivar) :
    Polynomial.derivative (scalar r * q) = scalar r * Polynomial.derivative q := by
  rw [TensorWholeIntervalPolynomial.scalar, Polynomial.derivative_C_mul]

theorem substitute_smul (f g : Bivar) (r : ℚ) (q : Bivar) :
    TwoVariablePolynomial.substitute f g (scalar r * q) =
      scalar r * TwoVariablePolynomial.substitute f g q := by
  rw [map_mul, BivariateCertificate.substitute_scalar]

/-- `p / y`. -/
def divY (c : Config) (x : XE) : XE := lin (XM.divYM c) 1 x.ex (x.ey - 1) (x.et - 1) x

theorem rep_divY {c : Config} {x : XE} {p : Bivar} (hx : x.Rep c p) :
    (divY c x).Rep c (TwoVariablePolynomial.divY p) :=
  rep_lin hx (fun _ hq => XM.rep_divYM hq) divY_sub divY_smul
    (fun _ hR => by rw [Nat.cast_one, one_mul]; exact l1_divY_le hR) fun hd => hd.divY

/-- `∂_y p`. -/
def derivY (c : Config) (x : XE) : XE :=
  lin (XM.derivYM c) (max x.ey x.m.dy) x.ex (x.ey - 1) (x.et - 1) x

theorem rep_derivY {c : Config} {x : XE} {p : Bivar} (hx : x.Rep c p) :
    (derivY c x).Rep c (TwoVariablePolynomial.derivativeY p) :=
  rep_lin hx (fun _ hq => XM.rep_derivYM hq) derivY_sub derivY_smul
    (fun _ hR => l1_derivY_le hR) fun hd => hd.derivY

/-- `p / x`. -/
def divX (c : Config) (x : XE) : XE := lin (XM.divXM c) 1 (x.ex - 1) x.ey (x.et - 1) x

theorem rep_divX {c : Config} {x : XE} {p : Bivar} (hx : x.Rep c p) :
    (divX c x).Rep c p.divX :=
  rep_lin hx (fun _ hq => XM.rep_divXM hq) divX_sub' divX_smul
    (fun _ hR => by rw [Nat.cast_one, one_mul]; exact l1_divX_le hR) fun hd => hd.divX

/-- `∂_x p`. -/
def derivX (c : Config) (x : XE) : XE :=
  lin (XM.derivXM c) (max x.ex x.m.dx) (x.ex - 1) x.ey (x.et - 1) x

theorem rep_derivX {c : Config} {x : XE} {p : Bivar} (hx : x.Rep c p) :
    (derivX c x).Rep c (Polynomial.derivative p) :=
  rep_lin hx (fun _ hq => XM.rep_derivXM hq) (fun _ _ => Polynomial.derivative_sub) derivX_smul
    (fun _ hR => l1_derivX_le hR) fun hd => hd.derivX

theorem abs_ratio_le {d : ℚ} {dn dd : ℕ} (hd : d = dn / dd) (h1 : dn ≤ dd) : |d| ≤ 1 := by
  rw [hd, abs_of_nonneg (by positivity)]
  rcases Nat.eq_zero_or_pos dd with h0 | h0
  · simp [h0]
  · rw [div_le_one (by exact_mod_cast h0)]; exact_mod_cast h1

/-- The triangle `x, y ≥ 0`, `x + y ≤ d`, for `d = dn / dd ≤ 1`. -/
def triangle (c : Config) (dn dd : ℕ) (x : XE) : XE :=
  lin (fun m => XM.triangleM c m dn dd) 1 x.et x.et (2 * x.et) x

theorem rep_triangle {c : Config} {x : XE} {p : Bivar} (hx : x.Rep c p) {d : ℚ} {dn dd : ℕ}
    (hd : d = dn / dd) (h1 : dn ≤ dd) :
    (triangle c dn dd x).Rep c (TwoVariablePolynomial.triangle d p) := by
  have hd1 := abs_ratio_le hd h1
  have hf : l1 (scalar d * TwoVariablePolynomial.unitX * (1 - TwoVariablePolynomial.unitY)) ≤ 1 := by
    refine (l1_mul_le _ _).trans ?_
    refine (mul_le_mul (l1_scalar_mul _ _) l1_one_sub_unitY (l1_nonneg _)
      (mul_nonneg (abs_nonneg _) (l1_nonneg _))).trans ?_
    nlinarith [l1_unitX, abs_nonneg d, l1_nonneg TwoVariablePolynomial.unitX]
  have hg : l1 (scalar d * TwoVariablePolynomial.unitX * TwoVariablePolynomial.unitY) ≤ 1 := by
    refine (l1_mul_le _ _).trans ?_
    refine (mul_le_mul (l1_scalar_mul _ _) l1_unitY (l1_nonneg _)
      (mul_nonneg (abs_nonneg _) (l1_nonneg _))).trans ?_
    nlinarith [l1_unitX, abs_nonneg d, l1_nonneg TwoVariablePolynomial.unitX]
  have dF : DegQ (scalar d * TwoVariablePolynomial.unitX * (1 - TwoVariablePolynomial.unitY)) 1 1 2 := by
    simpa using ((DegQ.scalar d).mul degQ_unitX).mul degQ_one_sub_unitY
  have dG : DegQ (scalar d * TwoVariablePolynomial.unitX * TwoVariablePolynomial.unitY) 1 1 2 := by
    simpa using ((DegQ.scalar d).mul degQ_unitX).mul degQ_unitY
  exact rep_lin hx (fun _ hq => XM.rep_triangleM hq hd) (fun _ _ => map_sub _ _ _)
    (substitute_smul _ _) (fun R _ => by rw [Nat.cast_one, one_mul]; exact l1_substitute_le _ _ R hf hg)
    fun hd' => hd'.substitute dF dG (fun i j _ _ h => by omega) (fun i j _ _ h => by omega)
      (fun i j _ _ h => by omega)

/-- The rectangle `[0, a] × [0, b]`, for `a = an / ad ≤ 1` and `b = bn / bd ≤ 1`. -/
def rectangle (c : Config) (an ad bn bd : ℕ) (x : XE) : XE :=
  lin (fun m => XM.rectangleM c m an ad bn bd) 1 x.ex x.ey x.et x

theorem rep_rectangle {c : Config} {x : XE} {p : Bivar} (hx : x.Rep c p) {a b : ℚ}
    {an ad bn bd : ℕ} (ha : a = an / ad) (hb : b = bn / bd) (ha1 : an ≤ ad) (hb1 : bn ≤ bd) :
    (rectangle c an ad bn bd x).Rep c (TwoVariablePolynomial.rectangle a b p) := by
  have ha' := abs_ratio_le ha ha1
  have hb' := abs_ratio_le hb hb1
  have hf : l1 (scalar a * TwoVariablePolynomial.unitX) ≤ 1 :=
    (l1_scalar_mul _ _).trans (by nlinarith [l1_unitX, abs_nonneg a, l1_nonneg TwoVariablePolynomial.unitX])
  have hg : l1 (scalar b * TwoVariablePolynomial.unitY) ≤ 1 :=
    (l1_scalar_mul _ _).trans (by nlinarith [l1_unitY, abs_nonneg b, l1_nonneg TwoVariablePolynomial.unitY])
  have dF : DegQ (scalar a * TwoVariablePolynomial.unitX) 1 0 1 := by
    simpa using (DegQ.scalar a).mul degQ_unitX
  have dG : DegQ (scalar b * TwoVariablePolynomial.unitY) 0 1 1 := by
    simpa using (DegQ.scalar b).mul degQ_unitY
  exact rep_lin hx (fun _ hq => XM.rep_rectangleM hq ha hb) (fun _ _ => map_sub _ _ _)
    (substitute_smul _ _) (fun R _ => by rw [Nat.cast_one, one_mul]; exact l1_substitute_le _ _ R hf hg)
    fun hd' => hd'.substitute dF dG (fun i j h _ _ => by omega) (fun i j _ h _ => by omega)
      (fun i j _ _ h => by omega)

/-- Sign normalization, with the exact digit sums. -/
def norm (c : Config) (x : XE) : XE := ⟨XM.norm c x.m, x.e, x.ex, x.ey, x.et⟩

theorem rep_norm {c : Config} {x : XE} {p : Bivar} (hx : x.Rep c p) : (norm c x).Rep c p := by
  intro hok
  dsimp only [norm] at hok ⊢
  have hxok : x.m.ok = true := by
    simp only [XM.norm, Bool.and_eq_true] at hok; exact hok.1
  obtain ⟨g, hs, hd, he⟩ := hx hxok
  obtain ⟨g', v'⟩ := XM.rep_norm (rep_approx hs g) hok
  refine ⟨g', hs, hd, ?_⟩
  have hs' : (XM.norm c x.m).s = x.m.s := rfl
  have hsq : (x.m.s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
  have hv : (XM.norm c x.m).val c = x.m.val c := by
    rw [v', hs', approx, ← mul_assoc, ← scalar_mul, mul_one_div_cancel hsq]
    simp [TensorWholeIntervalPolynomial.scalar]
  rw [hs', hv]; exact he

/-! ### The final bounds -/

/-- The check of `upper < r` for `r = rn / rd`, with the error of the model. -/
def upperCheck (c : Config) (x : XE) (D : ℕ) (rn : ℤ) (rd : ℕ) : Bool :=
  XM.finalOk c x.m D && Nat.blt 0 rd && Nat.ble x.ex D && Nat.ble x.ey D &&
    decide ((XM.upperZ c x.m D + ((4 ^ D * (4 * (D + 1) ^ 2) * x.e : ℕ) : ℤ)) * (rd : ℤ) <
      rn * ((4 ^ D * x.m.s : ℕ) : ℤ))

/-- The check of `r < lower` for `r = rn / rd`, with the error of the model. -/
def lowerCheck (c : Config) (x : XE) (D : ℕ) (rn : ℤ) (rd : ℕ) : Bool :=
  XM.finalOk c x.m D && Nat.blt 0 rd && Nat.ble x.ex D && Nat.ble x.ey D &&
    decide (rn * ((4 ^ D * x.m.s : ℕ) : ℤ) <
      (XM.lowerZ c x.m D - ((4 ^ D * (4 * (D + 1) ^ 2) * x.e : ℕ) : ℤ)) * (rd : ℤ))

/-- The remainder `q - approx` and its norm. -/
theorem remainder {c : Config} {x : XE} {q : Bivar} (hx : x.Rep c q) (hok : x.m.ok = true) :
    l1 (q - approx c x) ≤ x.e / x.m.s ∧ DegQ (q - approx c x) (max x.ex x.m.dx)
      (max x.ey x.m.dy) (max x.et x.m.dt) := by
  obtain ⟨g, hs, hd, he⟩ := hx hok
  have hsq : (x.m.s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
  have hspos : (0 : ℚ) < x.m.s := by exact_mod_cast hs
  have hR : q - approx c x = scalar (1 / (x.m.s : ℚ)) * (scalar (x.m.s : ℚ) * q - x.m.val c) := by
    have h1 : scalar (1 / (x.m.s : ℚ)) * scalar (x.m.s : ℚ) = 1 := by
      rw [← scalar_mul, one_div_mul_cancel hsq]; simp [TensorWholeIntervalPolynomial.scalar]
    simp only [approx]
    linear_combination (-q) * h1
  constructor
  · rw [hR]
    refine (l1_scalar_mul _ _).trans ?_
    rw [abs_of_pos (by positivity), one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right he hspos.le
  · have h1 : DegQ (approx c x) x.m.dx x.m.dy x.m.dt := by
      simpa [approx] using (DegQ.scalar _).mul (degQ_val g)
    exact (hd.mono (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)).sub
      (h1.mono (le_max_right _ _) (le_max_right _ _) (le_max_right _ _))

theorem abs_monomialCoefficient_le (a i : ℕ) :
    |WholeIntervalPolynomial.monomialCoefficient a i| ≤ 2 := by
  have hc : (Nat.choose a ((a - i) / 2) : ℚ) ≤ 2 ^ a := by
    exact_mod_cast Nat.choose_le_two_pow a _
  unfold WholeIntervalPolynomial.monomialCoefficient
  split_ifs
  · rw [abs_of_nonneg (by positivity), one_mul, div_le_iff₀ (by positivity)]; linarith
  · rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]; linarith
  · simp

theorem coefficient_sub (D : ℕ) (p q : Bivar) (i j : ℕ) :
    coefficient D (p - q) i j = coefficient D p i j - coefficient D q i j := by
  simp only [coefficient_eq_sum, Polynomial.coeff_sub, sub_mul, Finset.sum_sub_distrib]

theorem sum_abs_coefficient_le {R : Bivar} {D T : ℕ} (hR : DegQ R D D T) :
    ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1), |coefficient D R i j| ≤
      4 * ((D : ℚ) + 1) ^ 2 * l1 R := by
  set L := ∑ a ∈ Finset.range (D + 1), ∑ b ∈ Finset.range (D + 1), |(R.coeff a).coeff b|
  have hl1 : l1 R = L := l1_eq_sum fun a b h => by have := hR a b h; omega
  have h1 : ∀ i j, |coefficient D R i j| ≤ 4 * L := by
    intro i j
    rw [coefficient_eq_sum, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [abs_mul, abs_mul]
    calc |(R.coeff a).coeff b| * |WholeIntervalPolynomial.monomialCoefficient a i| *
          |WholeIntervalPolynomial.monomialCoefficient b j| ≤ |(R.coeff a).coeff b| * 2 * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (abs_monomialCoefficient_le a i) (abs_nonneg _))
            (abs_monomialCoefficient_le b j) (abs_nonneg _) (by positivity)
      _ = 4 * |(R.coeff a).coeff b| := by ring
  calc _ ≤ ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1), 4 * L :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ = 4 * ((D : ℚ) + 1) ^ 2 * l1 R := by rw [hl1]; simp; ring

theorem upper_add_le (D : ℕ) (c₁ c₂ : ℕ → ℕ → ℚ) :
    TwoVariablePolynomial.upper D (fun i j => c₁ i j + c₂ i j) ≤ TwoVariablePolynomial.upper D c₁ +
      ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1), |c₂ i j| := by
  have hn : TensorWholeIntervalPolynomial.norm D (fun i j => c₁ i j + c₂ i j) ≤
      TensorWholeIntervalPolynomial.norm D c₁ + TensorWholeIntervalPolynomial.norm D c₂ := by
    unfold TensorWholeIntervalPolynomial.norm
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun ij _ => abs_add_le _ _
  have h2 := norm_eq_sum D c₂
  have := le_abs_self (c₂ 0 0)
  unfold TwoVariablePolynomial.upper
  linarith

theorem lower_add_ge (D : ℕ) (c₁ c₂ : ℕ → ℕ → ℚ) :
    lower D c₁ - ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1), |c₂ i j| ≤
      lower D (fun i j => c₁ i j + c₂ i j) := by
  have hn : TensorWholeIntervalPolynomial.norm D (fun i j => c₁ i j + c₂ i j) ≤
      TensorWholeIntervalPolynomial.norm D c₁ + TensorWholeIntervalPolynomial.norm D c₂ := by
    unfold TensorWholeIntervalPolynomial.norm
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun ij _ => abs_add_le _ _
  have h2 := norm_eq_sum D c₂
  have := neg_abs_le (c₂ 0 0)
  unfold lower
  linarith

/-- The facts of a final check: the expansion, the bound of the approximation, and the size of
the correction. -/
theorem final_parts {c : Config} {x : XE} {q : Bivar} (hx : x.Rep c q) {D : ℕ}
    (hf : XM.finalOk c x.m D = true) (hex : x.ex ≤ D) (hey : x.ey ≤ D) :
    q = expansion D q ∧ 0 < x.m.s ∧
      lower D (coefficient D (approx c x)) = (XM.lowerZ c x.m D : ℚ) / (4 ^ D * x.m.s) ∧
      TwoVariablePolynomial.upper D (coefficient D (approx c x)) =
        (XM.upperZ c x.m D : ℚ) / (4 ^ D * x.m.s) ∧
      coefficient D q = (fun i j => coefficient D (approx c x) i j + coefficient D (q - approx c x) i j) ∧
      ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1), |coefficient D (q - approx c x) i j| ≤
        4 * ((D : ℚ) + 1) ^ 2 * (x.e / x.m.s) := by
  have hf' := hf
  simp only [XM.finalOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hf'
  obtain ⟨⟨⟨⟨⟨⟨hok, hs⟩, -⟩, -⟩, hdx⟩, hdy⟩, -⟩ := hf'
  obtain ⟨g, -, hd, -⟩ := hx hok
  obtain ⟨-, hl, hu⟩ := XM.final_spec (rep_approx hs g) hf
  obtain ⟨hR, hRd⟩ := remainder hx hok
  refine ⟨eq_expansion_of_degrees (hd.natDegree.trans hex) (fun a => (hd.natDegree_coeff a).trans hey),
    hs, hl, hu, ?_, ?_⟩
  · funext i j; rw [coefficient_sub]; ring
  · refine (sum_abs_coefficient_le (hRd.mono (max_le hex hdx) (max_le hey hdy) le_rfl)).trans ?_
    exact mul_le_mul_of_nonneg_left hR (by positivity)

theorem upper_certificate {c : Config} {x : XE} {q : Bivar} (hx : x.Rep c q) {D : ℕ} {rn : ℤ}
    {rd : ℕ} (h : upperCheck c x D rn rd = true) {r : ℚ} (hr : r = rn / rd) :
    q = expansion D q ∧ TwoVariablePolynomial.upper D (coefficient D q) < r := by
  simp only [upperCheck, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hf, hrd⟩, hex⟩, hey⟩, hlt⟩ := h
  obtain ⟨he, hs, -, hu, hsplit, hsum⟩ := final_parts hx hf hex hey
  refine ⟨he, ?_⟩
  have hup := upper_add_le D (coefficient D (approx c x)) (coefficient D (q - approx c x))
  rw [← hsplit, hu] at hup
  have hK : (0 : ℚ) < 4 ^ D * x.m.s := by positivity
  have hsq : (0 : ℚ) < x.m.s := by exact_mod_cast hs
  have hrd' : (0 : ℚ) < rd := by exact_mod_cast hrd
  have hlt' : ((XM.upperZ c x.m D : ℚ) + ((4 ^ D * (4 * (D + 1) ^ 2) * x.e : ℕ) : ℚ)) * rd <
      rn * ((4 ^ D * x.m.s : ℕ) : ℚ) := by exact_mod_cast hlt
  push_cast at hlt'
  have heq : (XM.upperZ c x.m D : ℚ) / (4 ^ D * x.m.s) + 4 * ((D : ℚ) + 1) ^ 2 * (x.e / x.m.s) =
      ((XM.upperZ c x.m D : ℚ) + 4 ^ D * (4 * ((D : ℚ) + 1) ^ 2) * x.e) / (4 ^ D * x.m.s) := by
    field_simp
  rw [hr, lt_div_iff₀ hrd']
  calc TwoVariablePolynomial.upper D (coefficient D q) * rd ≤
        (((XM.upperZ c x.m D : ℚ) + 4 ^ D * (4 * ((D : ℚ) + 1) ^ 2) * x.e) / (4 ^ D * x.m.s)) * rd := by
        rw [← heq]; exact mul_le_mul_of_nonneg_right (by linarith) hrd'.le
    _ < rn := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hK]; linarith

theorem lower_certificate {c : Config} {x : XE} {q : Bivar} (hx : x.Rep c q) {D : ℕ} {rn : ℤ}
    {rd : ℕ} (h : lowerCheck c x D rn rd = true) {r : ℚ} (hr : r = rn / rd) :
    q = expansion D q ∧ r < lower D (coefficient D q) := by
  simp only [lowerCheck, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hf, hrd⟩, hex⟩, hey⟩, hlt⟩ := h
  obtain ⟨he, hs, hl, -, hsplit, hsum⟩ := final_parts hx hf hex hey
  refine ⟨he, ?_⟩
  have hlo := lower_add_ge D (coefficient D (approx c x)) (coefficient D (q - approx c x))
  rw [← hsplit, hl] at hlo
  have hK : (0 : ℚ) < 4 ^ D * x.m.s := by positivity
  have hsq : (0 : ℚ) < x.m.s := by exact_mod_cast hs
  have hrd' : (0 : ℚ) < rd := by exact_mod_cast hrd
  have hlt' : (rn : ℚ) * ((4 ^ D * x.m.s : ℕ) : ℚ) <
      ((XM.lowerZ c x.m D : ℚ) - ((4 ^ D * (4 * (D + 1) ^ 2) * x.e : ℕ) : ℚ)) * rd := by
    exact_mod_cast hlt
  push_cast at hlt'
  have heq : (XM.lowerZ c x.m D : ℚ) / (4 ^ D * x.m.s) - 4 * ((D : ℚ) + 1) ^ 2 * (x.e / x.m.s) =
      ((XM.lowerZ c x.m D : ℚ) - 4 ^ D * (4 * ((D : ℚ) + 1) ^ 2) * x.e) / (4 ^ D * x.m.s) := by
    field_simp
  rw [hr, div_lt_iff₀ hrd']
  calc (rn : ℚ) < (((XM.lowerZ c x.m D : ℚ) - 4 ^ D * (4 * ((D : ℚ) + 1) ^ 2) * x.e) /
        (4 ^ D * x.m.s)) * rd := by
        rw [div_mul_eq_mul_div, lt_div_iff₀ hK]; linarith
    _ ≤ lower D (coefficient D q) * rd := by
        rw [← heq]; exact mul_le_mul_of_nonneg_right (by linarith) hrd'.le

end XE

end SquaresInCircles.Eight.BivariateRounding
