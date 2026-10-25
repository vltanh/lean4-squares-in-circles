module

public import SquaresInCircles.Eight.TableFree.PackedModels
public import SquaresInCircles.Eight.TableFree.TwoVariablePolynomial
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDPolynomialData

/-!
# Exact bivariate certificates

A rational bivariate polynomial `p` is carried by an exact model `m : XM`: two natural numbers
`U`, `V` packing digitwise (base `2 ^ w`, stride `S = 2 B + 1`) the integer coefficients of
`s · p = U - V`, with tracked degree bounds and a digit-sum bound. `XM.Rep c m p` says that the
model represents `p` whenever its flag `ok` is `true`. The kernel only computes on `ℕ` and `ℤ`.

* Building models: `XM.ofInt` (`rep_ofInt`, `rep_lit`, `rep_one`), `XM.varX`, `XM.varY`,
  `XM.add`, `XM.sub`, `XM.neg`, `XM.mul`, `XM.pow`, `XM.mulQ` (times `n / d`), `XM.monoMul`,
  `XM.norm`, `XM.const0` (the constant term), `XM.rowSlice`, `XM.colSlice`, `XM.trunc` (total
  degree), `XM.guard` (an extra check), each with its `rep_` lemma.
* Derived operations: `XM.divXM` (`p.divX`), `XM.divYM` (`divY p`), `XM.derivXM`
  (`derivative p`), `XM.derivYM` (`derivativeY p`), `XM.cubicMassM` and `XM.cubicMassRM`
  (`cubicMass ρ p`), and `XM.liftM` (`lift f q` by Horner's rule, for `q = uniQ L`), with
  `rep_liftC10`, `rep_liftC12`, `rep_liftS9`, `rep_liftS11` for the Taylor polynomials of
  `GlobalGA.PositiveTD.Certificate`.
* Reduction: `XM.reduce` divides the numerators and the scale by the gcd of the scale and of all
  digits (`XM.digitGcdZ`), when the division is exact digit by digit (`rep_reduce`).
* Automation: `build_xm [h₁, …]` proves `m.Rep c p` along the syntax of `p`, building the model
  `m` when it is a metavariable; `rep_scalar` handles the scalars, `XM.rep_ite` and
  `XM.rep_vec2`–`XM.rep_vec4` the case distinctions.
* Changes of variables: `XM.substX`, `XM.substY` (`x` or `y` replaced by `F / q` for a short
  integer polynomial `F`), and the regions `XM.triangleM` (`rep_triangleM`), `XM.rectangleM`
  (`rep_rectangleM`), `XM.fanM` (`rep_fanM`, `rep_trapezoidM`, `rep_fanNegM`).
* Certificates: `XM.lowerCheck` and `XM.upperCheck`, with `XM.lower_certificate` and
  `XM.upper_certificate`: from `m.Rep c q` and a check evaluated by `decide +kernel`,
  `q = expansion D q` and `r < lower D (coefficient D q)` (or `upper … < r`). The tensor
  Chebyshev coefficients are computed row by row and column by column on the packed numbers,
  and the sum of their absolute values is a digit sum, read modulo `2 ^ w - 1` (`XM.final_spec`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.BivariateCertificate
open Polynomial PackedModels TensorWholeIntervalPolynomial

/-! ## Supports of natural bivariate polynomials -/

/-- The coefficients vanish outside `i ≤ dx`, `j ≤ dy`, `i + j ≤ dt`. -/
def Supp (P : NB) (dx dy dt : ℕ) : Prop :=
  ∀ i j, cf P i j ≠ 0 → i ≤ dx ∧ j ≤ dy ∧ i + j ≤ dt

theorem Supp.mono {P : NB} {dx dy dt ex ey et : ℕ} (h : Supp P dx dy dt) (hx : dx ≤ ex)
    (hy : dy ≤ ey) (ht : dt ≤ et) : Supp P ex ey et := fun i j hij => by
  have := h i j hij; omega

theorem Supp.add {P Q : NB} {dx dy dt : ℕ} (hP : Supp P dx dy dt) (hQ : Supp Q dx dy dt) :
    Supp (P + Q) dx dy dt := fun i j h => by
  rw [cf_add] at h
  by_cases h1 : cf P i j = 0
  · rw [h1, zero_add] at h; exact hQ i j h
  · exact hP i j h1

theorem Supp.zero (dx dy dt : ℕ) : Supp 0 dx dy dt := fun i j h => by simp [cf] at h

theorem cf_smul (k : ℕ) (P : NB) (i j : ℕ) : cf (k • P) i j = k * cf P i j := by
  simp [cf]

theorem Supp.smul {P : NB} {dx dy dt : ℕ} (hP : Supp P dx dy dt) (k : ℕ) :
    Supp (k • P) dx dy dt := fun i j h => by
  rw [cf_smul] at h
  exact hP i j (fun h0 => h (by rw [h0, mul_zero]))

theorem Supp.mul {P Q : NB} {dx dy dt ex ey et : ℕ} (hP : Supp P dx dy dt) (hQ : Supp Q ex ey et) :
    Supp (P * Q) (dx + ex) (dy + ey) (dt + et) := by
  intro i j h
  simp only [cf, Polynomial.coeff_mul, Polynomial.finsetSum_coeff] at h
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨y, hy, hy0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx0
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hy' := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
  have h1 : cf P x.1 y.1 ≠ 0 := fun h0 => hy0 (by simp only [cf] at h0; rw [h0, zero_mul])
  have h2 : cf Q x.2 y.2 ≠ 0 := fun h0 => hy0 (by simp only [cf] at h0; rw [h0, mul_zero])
  have := hP _ _ h1
  have := hQ _ _ h2
  omega

theorem Supp.boxSupp {c : Config} {P : NB} {dx dy dt : ℕ} (h : Supp P dx dy dt) (hx : dx < c.S)
    (hy : dy < c.S) : BoxSupp c P := fun i j hij => by
  have := h i j hij; omega

theorem cf_X_mul (P : NB) (i j : ℕ) : cf (X * P) (i + 1) j = cf P i j := by
  simp [cf, Polynomial.coeff_X_mul]

theorem cf_X_mul_zero (P : NB) (j : ℕ) : cf (X * P) 0 j = 0 := by
  simp [cf]

theorem cf_CX_mul (P : NB) (i j : ℕ) : cf (C X * P) i (j + 1) = cf P i j := by
  simp [cf, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]

theorem cf_CX_mul_zero (P : NB) (i : ℕ) : cf (C X * P) i 0 = 0 := by
  simp [cf, Polynomial.coeff_C_mul]

/-! ## Packed numbers of a box -/

/-- The value of a packed natural polynomial in `Bivar`. -/
def mapQ : NB →+* Bivar := Polynomial.mapRingHom (Polynomial.mapRingHom (Nat.castRingHom ℚ))

theorem coeff_mapQ (P : NB) (i j : ℕ) : ((mapQ P).coeff i).coeff j = (cf P i j : ℚ) := by
  simp [mapQ, cf, Polynomial.coeff_map]

theorem dsum_add (P Q : NB) : dsum (P + Q) = dsum P + dsum Q := map_add _ _ _
theorem dsum_mul (P Q : NB) : dsum (P * Q) = dsum P * dsum Q := map_mul _ _ _
theorem dsum_smul (k : ℕ) (P : NB) : dsum (k • P) = k * dsum P := by
  rw [nsmul_eq_mul, dsum_mul]; simp [dsum]

/-- Decoding a natural polynomial of the box with small coefficients. -/
theorem poly_evB' {c : Config} {P : NB} {dx dy dt : ℕ} (h : Supp P dx dy dt) (hx : dx < c.S)
    (hy : dy < c.S) (hs : dsum P < c.b) : poly c (evB c P) = P :=
  poly_evB (h.boxSupp hx hy) fun i j => (cf_le_dsum (h.boxSupp hx hy) i j).trans_lt hs

theorem box_evB' {c : Config} {P : NB} {dx dy dt : ℕ} (h : Supp P dx dy dt) (hx : dx < c.S)
    (hy : dy < c.S) (hs : dsum P < c.b) : Box c (evB c P) :=
  box_evB (h.boxSupp hx hy) fun i j => (cf_le_dsum (h.boxSupp hx hy) i j).trans_lt hs


theorem evB_poly_eq {c : Config} {N : ℕ} (h : Box c N) : N = evB c (poly c N) := (evB_poly h).symm

theorem cf_C_C (k i j : ℕ) : cf (C (C k) : NB) i j = if i = 0 ∧ j = 0 then k else 0 := by
  simp only [cf, Polynomial.coeff_C]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]

theorem supp_C_C (k : ℕ) : Supp (C (C k) : NB) 0 0 0 := fun i j h => by
  rw [cf_C_C] at h; split_ifs at h with hij
  · omega
  · exact absurd rfl h

theorem dsum_C_C (k : ℕ) : dsum (C (C k) : NB) = k := by simp [dsum, ev]

theorem evB_C_C (c : Config) (k : ℕ) : evB c (C (C k)) = k := by simp [evB, ev]

theorem supp_X : Supp (X : NB) 1 0 1 := fun i j h => by
  simp only [cf, Polynomial.coeff_X] at h
  split_ifs at h with h1
  · subst h1; simp only [Polynomial.coeff_one] at h; split_ifs at h with h2 <;> omega
  · simp at h

theorem supp_Y : Supp (C X : NB) 0 1 1 := fun i j h => by
  simp only [cf, Polynomial.coeff_C] at h
  split_ifs at h with h1
  · subst h1; simp only [Polynomial.coeff_X] at h; split_ifs at h with h2 <;> omega
  · simp at h

theorem dsum_X : dsum (X : NB) = 1 := by simp [dsum, ev]
theorem dsum_Y : dsum (C X : NB) = 1 := by simp [dsum, ev]
theorem evB_X (c : Config) : evB c X = c.b ^ c.S := by simp [evB, ev]
theorem evB_Y (c : Config) : evB c (C X) = c.b := by simp [evB, ev]

theorem lcm_eq (a b : ℕ) : b / Nat.gcd a b * a = a / Nat.gcd a b * b := by
  have ha := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hb := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  calc b / Nat.gcd a b * a = b / Nat.gcd a b * (Nat.gcd a b * (a / Nat.gcd a b)) := by rw [ha]
    _ = a / Nat.gcd a b * (Nat.gcd a b * (b / Nat.gcd a b)) := by ring
    _ = a / Nat.gcd a b * b := by rw [hb]

theorem Supp.max_left {P : NB} {dx dy dt : ℕ} (h : Supp P dx dy dt) (ex ey et : ℕ) :
    Supp P (max dx ex) (max dy ey) (max dt et) :=
  h.mono (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
theorem Supp.max_right {P : NB} {dx dy dt : ℕ} (h : Supp P dx dy dt) (ex ey et : ℕ) :
    Supp P (max ex dx) (max ey dy) (max et dt) :=
  h.mono (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)

theorem cf_monomial (a b i j : ℕ) :
    cf ((X : NB) ^ a * (C X) ^ b) i j = if i = a ∧ j = b then 1 else 0 := by
  simp only [cf, ← map_pow, mul_comm ((X : NB) ^ a), Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h1 : i = a <;> by_cases h2 : j = b <;> simp [h1, h2]

theorem supp_monomial (a b : ℕ) : Supp ((X : NB) ^ a * (C X) ^ b) a b (a + b) := fun i j h => by
  rw [cf_monomial] at h; split_ifs at h with hij
  · omega
  · exact absurd rfl h

theorem dsum_monomial (a b : ℕ) : dsum ((X : NB) ^ a * (C X) ^ b) = 1 := by
  simp [dsum, ev]

theorem evB_monomial (c : Config) (a b : ℕ) :
    evB c ((X : NB) ^ a * (C X) ^ b) = 2 ^ (c.w * (c.S * a + b)) := by
  simp only [map_mul, map_pow, evB, ev, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Config.b]
  rw [← pow_mul, ← pow_add, Nat.mul_add, ← pow_mul, Nat.mul_add]

/-! ## Box patterns and sign normalization -/

/-- The number with every digit of the box equal to `1`. -/
def onesBox (c : Config) : ℕ := (c.b ^ (c.S * c.S) - 1) / (c.b - 1)

theorem onesBox_eq (c : Config) (hw : 1 ≤ c.w) : onesBox c = pack c (fun _ _ => 1) := by
  have hb : 2 ≤ c.b := by
    unfold Config.b; calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ c.w := Nat.pow_le_pow_right (by norm_num) hw
  rw [pack_eq_sum, onesBox, ← Nat.geomSum_eq hb]
  simp

/-- The number with every digit of the box equal to `k`. -/
def boxPat (c : Config) (k : ℕ) : ℕ := k * onesBox c

theorem boxPat_eq (c : Config) (hw : 1 ≤ c.w) (k : ℕ) : boxPat c k = pack c (fun _ _ => k) := by
  rw [boxPat, onesBox_eq c hw, mul_comm, pack_mul_const]; simp

theorem topbit_box {c : Config} (hw : 1 ≤ c.w) {d : ℕ → ℕ → ℕ} (hd : ∀ i j, d i j < c.b) :
    (pack c d >>> (c.w - 1)) &&& onesBox c = pack c (fun i j => d i j / 2 ^ (c.w - 1)) := by
  have hb2 : 2 ≤ c.b := by
    unfold Config.b; calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ c.w := Nat.pow_le_pow_right (by norm_num) hw
  have hbw : (c.b : ℕ) = 2 ^ (c.w - 1) * 2 := by
    unfold Config.b; rw [← pow_succ, Nat.sub_add_cancel hw]
  have hq : ∀ i j, d i j / 2 ^ (c.w - 1) < 2 := fun i j => by
    rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← hbw]; exact hd i j
  have h1 : ∀ _ _ : ℕ, (1 : ℕ) < c.b := fun _ _ => by omega
  have h2 : ∀ i j, d i j / 2 ^ (c.w - 1) < c.b := fun i j => lt_of_lt_of_le (hq i j) hb2
  apply eq_of_digit_eq (show 0 < c.w by omega)
  intro m
  rw [digit_land, onesBox_eq c hw, digit_pack c h1, digit_pack c h2]
  by_cases hm : m < c.S * c.S
  · rw [ite_eq_left hm, ite_eq_left hm, Nat.and_one_is_mod]
    have hdm := digit_pack c hd m
    rw [ite_eq_left hm] at hdm
    rw [← hdm]
    simp only [digit, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ c.w from dvd_pow_self 2 (by omega)),
      show (2 : ℕ) ^ c.w = 2 ^ (c.w - 1) * 2 by rw [← pow_succ, Nat.sub_add_cancel hw],
      Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
  · rw [ite_eq_right hm, ite_eq_right hm, Nat.and_zero]

/-- Splitting `U - V` into its positive and negative digit parts (the whole box). -/
def normBox (c : Config) (U V : ℕ) : ℕ × ℕ :=
  let O := boxPat c (2 ^ (c.w - 1))
  let W := U + O - V
  let G := (W >>> (c.w - 1)) &&& onesBox c
  let Sm := G * (c.b - 1)
  let Nm := boxPat c (c.b - 1) - Sm
  ((W &&& Sm) - (O &&& Sm), (O &&& Nm) - (W &&& Nm))

theorem normBox_spec {c : Config} (hw : 2 ≤ c.w) {U V : ℕ} (hU : Box c U) (hV : Box c V)
    (hu : ∀ i j, coeffs c U i j < 2 ^ (c.w - 1)) (hv : ∀ i j, coeffs c V i j < 2 ^ (c.w - 1)) :
    (normBox c U V).1 = pack c (fun i j => coeffs c U i j - coeffs c V i j) ∧
    (normBox c U V).2 = pack c (fun i j => coeffs c V i j - coeffs c U i j) := by
  set h := 2 ^ (c.w - 1) with hh
  have hbw : c.b = h * 2 := by
    unfold Config.b; rw [hh, ← pow_succ, Nat.sub_add_cancel (by omega)]
  have hh0 : 0 < h := by positivity
  have hw1 : 1 ≤ c.w := by omega
  set dW : ℕ → ℕ → ℕ := fun i j => coeffs c U i j + h - coeffs c V i j with hdW
  have hdW_lt : ∀ i j, dW i j < c.b := fun i j => by
    simp only [hdW]; have := hu i j; have := hv i j; omega
  have hO : boxPat c h = pack c (fun _ _ => h) := boxPat_eq c hw1 h
  have hW : U + boxPat c h - V = pack c dW := by
    rw [← pack_coeffs hU, ← pack_coeffs hV, hO, pack_add, pack_sub]
    intro i j; have := hv i j; omega
  set g : ℕ → ℕ → ℕ := fun i j => dW i j / h with hg
  have hG : (pack c dW >>> (c.w - 1)) &&& onesBox c = pack c g := topbit_box hw1 hdW_lt
  have hg_val : ∀ i j, g i j = if coeffs c V i j ≤ coeffs c U i j then 1 else 0 := fun i j => by
    simp only [hg, hdW]; exact div_half_eq (hu i j) (hv i j)
  have hg_lt : ∀ i j, g i j * (c.b - 1) < c.b := fun i j => by
    rw [hg_val i j]; split_ifs <;> omega
  have hSm : pack c g * (c.b - 1) = pack c (fun i j => g i j * (c.b - 1)) := pack_mul_const _ _ _
  have hNm : boxPat c (c.b - 1) - pack c (fun i j => g i j * (c.b - 1)) =
      pack c (fun i j => (c.b - 1) - g i j * (c.b - 1)) := by
    rw [boxPat_eq c hw1, pack_sub]
    intro i j
    rw [hg_val i j]; split_ifs <;> omega
  have hNm_lt : ∀ i j, (c.b - 1) - g i j * (c.b - 1) < c.b := fun i j => by omega
  have hO_lt : ∀ _ _ : ℕ, h < c.b := fun _ _ => by omega
  have land_mask : ∀ x k, x < c.b → k = 0 ∨ k = c.b - 1 → x &&& k = if k = 0 then 0 else x := by
    intro x k hx hk
    rcases hk with rfl | rfl
    · simp
    · rw [ite_eq_right (by omega)]; exact land_full hx
  have key : ∀ (P : ℕ) (p : ℕ → ℕ → ℕ) (q : ℕ → ℕ → ℕ), (∀ i j, p i j < c.b) → (∀ i j, q i j < c.b) →
      (∀ i j, q i j = 0 ∨ q i j = c.b - 1) → P = pack c p →
      P &&& pack c q = pack c (fun i j => if q i j = 0 then 0 else p i j) := by
    intro P p q hp hq hq01 hP
    apply land_pattern (pack_box c hq)
    · intro i j hi hj
      rw [hP, coeffs_pack c hp hi hj, coeffs_pack c hq hi hj, land_mask _ _ (hp i j) (hq01 i j)]
    · intro i j; split_ifs
      · exact c.b_pos
      · exact hp i j
  have hq1 : ∀ i j, g i j * (c.b - 1) = 0 ∨ g i j * (c.b - 1) = c.b - 1 := fun i j => by
    rw [hg_val i j]; split_ifs <;> simp
  have hq2 : ∀ i j, (c.b - 1) - g i j * (c.b - 1) = 0 ∨
      (c.b - 1) - g i j * (c.b - 1) = c.b - 1 := fun i j => by
    rw [hg_val i j]; split_ifs <;> simp
  simp only [normBox]
  rw [hW, hG, hSm, hNm, key _ dW _ hdW_lt hg_lt hq1 rfl, key _ _ _ hO_lt hg_lt hq1 hO,
    key _ _ _ hO_lt hNm_lt hq2 hO, key _ dW _ hdW_lt hNm_lt hq2 rfl]
  constructor
  · rw [pack_sub]
    · apply pack_congr; intro i j _ _
      simp only [hdW, hg_val i j]
      have := hu i j; have := hv i j
      split_ifs <;> omega
    · intro i j
      simp only [hdW, hg_val i j]; split_ifs <;> omega
  · rw [pack_sub]
    · apply pack_congr; intro i j _ _
      simp only [hdW, hg_val i j]
      have := hu i j; have := hv i j
      split_ifs <;> omega
    · intro i j
      simp only [hdW, hg_val i j]; split_ifs <;> omega

/-! ## Slices and masks -/

theorem testBit_digit_ge {w N m k : ℕ} (hk : w ≤ k) : (digit w N m).testBit k = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (digit_lt w N m) (Nat.pow_le_pow_right (by norm_num) hk))

theorem digit_mod {w N n m : ℕ} :
    digit w (N % 2 ^ (w * n)) m = if m < n then digit w N m else 0 := by
  apply Nat.eq_of_testBit_eq; intro k
  by_cases hk : k < w
  · rw [testBit_digit hk, Nat.testBit_mod_two_pow]
    split_ifs with hm
    · rw [testBit_digit hk]
      have : w * m + k < w * n := by nlinarith
      simp [this]
    · have : ¬ w * m + k < w * n := by nlinarith
      simp [this]
  · rw [testBit_digit_ge (by omega)]
    split_ifs
    · rw [testBit_digit_ge (by omega)]
    · simp

theorem geom_mul (b n : ℕ) (hb : 1 ≤ b) : (b - 1) * ∑ j ∈ Finset.range n, b ^ j = b ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    have h1 : 1 ≤ b ^ n := Nat.one_le_pow _ _ hb
    zify [h1, Nat.one_le_pow (n + 1) b hb, hb, Nat.mul_le_mul h1 hb]
    ring

/-- The row mask: the digits `0 ≤ j < S` of row `0`. -/
def rowMask (c : Config) : ℕ := c.b ^ c.S - 1

/-- `N` restricted to its row `k`, moved to row `0`. -/
theorem rowSlice_eq {c : Config} (hw : 0 < c.w) (N : ℕ) {k : ℕ} (hk : k < c.S) :
    (N >>> (c.w * (c.S * k))) &&& rowMask c =
      pack c (fun i j => if i = 0 then coeffs c N k j else 0) := by
  have hd : ∀ i j, (if i = 0 then coeffs c N k j else 0) < c.b := fun i j => by
    split_ifs
    · exact coeffs_lt c N k j
    · exact c.b_pos
  apply eq_of_digit_eq hw
  intro m
  rw [rowMask, show c.b ^ c.S = 2 ^ (c.w * c.S) by simp [Config.b, ← pow_mul],
    Nat.and_two_pow_sub_one_eq_mod, digit_mod, digit_pack c hd, digit_shiftRight]
  by_cases hm : m < c.S
  · have hS : m < c.S * c.S := lt_of_lt_of_le hm (Nat.le_mul_of_pos_left _ (by omega))
    rw [ite_eq_left hm, ite_eq_left hS, Nat.div_eq_of_lt hm, ite_eq_left rfl, Nat.mod_eq_of_lt hm,
      PackedModels.coeffs, add_comm]
  · rw [ite_eq_right hm]
    split_ifs with h1 h2
    · exfalso; apply hm; rw [Nat.div_eq_zero_iff] at h2; omega
    · rfl
    · rfl

/-- The column mask: digit `0` of every row. -/
def col0Mask (c : Config) : ℕ := (c.b - 1) * ((c.b ^ (c.S * c.S) - 1) / (c.b ^ c.S - 1))

theorem col0Mask_eq (c : Config) (hw : 1 ≤ c.w) :
    col0Mask c = pack c (fun _ j => if j = 0 then c.b - 1 else 0) := by
  have hb : 2 ≤ c.b := by
    unfold Config.b; calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ c.w := Nat.pow_le_pow_right (by norm_num) hw
  have hbS : 2 ≤ c.b ^ c.S := le_trans hb (Nat.le_self_pow (by have := c.S_pos; omega) _)
  rw [col0Mask, pack, sumTo_eq]
  have hrow : ∀ i, sumTo (fun j => (if j = 0 then c.b - 1 else 0) * c.b ^ (c.S * i + j)) c.S =
      (c.b - 1) * (c.b ^ c.S) ^ i := fun i => by
    rw [sumTo_eq, Finset.sum_eq_single 0]
    · simp [← pow_mul]
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_range.mpr c.S_pos) h
  simp only [hrow, ← Finset.mul_sum]
  rw [Nat.geomSum_eq hbS, ← pow_mul]

/-- `N` restricted to its column `k`, moved to column `0`. -/
theorem colSlice_eq {c : Config} (hw : 0 < c.w) (N : ℕ) {k : ℕ} (_hk : k < c.S) :
    (N >>> (c.w * k)) &&& col0Mask c = pack c (fun i j => if j = 0 then coeffs c N i k else 0) := by
  have hd : ∀ i j, (if j = 0 then coeffs c N i k else 0) < c.b := fun i j => by
    split_ifs
    · exact coeffs_lt c N i k
    · exact c.b_pos
  have hd' : ∀ _ j : ℕ, (if j = 0 then c.b - 1 else 0) < c.b := fun _ j => by
    have := c.b_pos; split_ifs <;> omega
  apply eq_of_digit_eq hw
  intro m
  rw [digit_land, col0Mask_eq c hw, digit_pack c hd, digit_pack c hd', digit_shiftRight]
  split_ifs with h1 h2
  · rw [show c.b - 1 = 2 ^ c.w - 1 from rfl, land_full (digit_lt _ _ _)]
    have e : m = c.S * (m / c.S) := by have := Nat.div_add_mod m c.S; omega
    rw [PackedModels.coeffs]; congr 1; omega
  · simp
  · simp

/-- The triangle mask `i + j ≤ T`. -/
def triMaskT (c : Config) (T : ℕ) : ℕ :=
  sumTo (fun i => (c.b ^ (T + 1 - i) - 1) * c.b ^ (c.S * i)) (T + 1)

theorem triMaskT_eq (c : Config) (_hw : 1 ≤ c.w) {T : ℕ} (hT : T < c.S) :
    triMaskT c T = pack c (fun i j => if i + j ≤ T then c.b - 1 else 0) := by
  have hb : 1 ≤ c.b := c.b_pos
  rw [triMaskT, pack, sumTo_eq, sumTo_eq]
  have hrow : ∀ i, sumTo (fun j => (if i + j ≤ T then c.b - 1 else 0) * c.b ^ (c.S * i + j)) c.S =
      if i ≤ T then (c.b ^ (T + 1 - i) - 1) * c.b ^ (c.S * i) else 0 := fun i => by
    rw [sumTo_eq]
    split_ifs with hi
    · rw [← Finset.sum_range_add_sum_Ico _ (show T + 1 - i ≤ c.S by omega),
        Finset.sum_eq_zero (s := Finset.Ico _ _) (fun j hj => by
          rw [Finset.mem_Ico] at hj; rw [ite_eq_right (by omega), zero_mul]), add_zero,
        ← geom_mul c.b (T + 1 - i) hb, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j hj
      rw [Finset.mem_range] at hj; rw [ite_eq_left (by omega), pow_add]; ring
    · apply Finset.sum_eq_zero; intro j _; rw [ite_eq_right (by omega), zero_mul]
  simp only [hrow]
  rw [← Finset.sum_range_add_sum_Ico _ (show T + 1 ≤ c.S by omega)]
  rw [Finset.sum_eq_zero (s := Finset.Ico _ _) (fun i hi => by
    rw [Finset.mem_Ico] at hi; rw [ite_eq_right (by omega)]), add_zero]
  apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi; rw [ite_eq_left (by omega)]

/-- The truncation to total degree `≤ T`. -/
theorem truncT_eq {c : Config} (hw : 1 ≤ c.w) (N : ℕ) {T : ℕ} (hT : T < c.S) :
    N &&& triMaskT c T = pack c (fun i j => if i + j ≤ T then coeffs c N i j else 0) := by
  have hbm : c.b - 1 < c.b := Nat.sub_lt c.b_pos one_pos
  rw [triMaskT_eq c hw hT]
  apply land_pattern (pack_box c (fun i j => by split_ifs <;> omega))
  · intro i j hi hj
    rw [coeffs_pack c (fun i j => by split_ifs <;> omega) hi hj]
    split_ifs
    · exact land_full (coeffs_lt c N i j)
    · exact Nat.and_zero _
  · intro i j; split_ifs
    · exact coeffs_lt c N i j
    · exact c.b_pos

/-! ## Columns and truncations of rational bivariate polynomials -/

/-- The column `k` of `p`, as a polynomial in `x`. -/
def colPoly (p : Bivar) (k : ℕ) : Bivar := p.sum (fun i q => Polynomial.monomial i (C (q.coeff k)))

theorem coeff_colPoly (p : Bivar) (k i : ℕ) : (colPoly p k).coeff i = C ((p.coeff i).coeff k) := by
  rw [colPoly, Polynomial.sum_def, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Polynomial.notMem_support_iff.mp h]; simp

/-- The truncation of `p` to total degree `≤ T`. -/
def truncTot (T : ℕ) (p : Bivar) : Bivar :=
  ∑ i ∈ Finset.range (T + 1), ∑ j ∈ Finset.range (T + 1),
    if i + j ≤ T then scalar ((p.coeff i).coeff j) * X ^ i * (C X) ^ j else 0

theorem coeff_term (r : ℚ) (i j a b : ℕ) :
    ((scalar r * X ^ i * (C X) ^ j : Bivar).coeff a).coeff b = if a = i ∧ b = j then r else 0 := by
  have e : (scalar r * X ^ i * (C X) ^ j : Bivar) = X ^ i * C (X ^ j * C r) := by
    simp only [scalar, map_mul, map_pow]; ring
  rw [e, Polynomial.coeff_X_pow_mul']
  by_cases h1 : i ≤ a
  · rw [ite_eq_left h1, Polynomial.coeff_C]
    by_cases h2 : a - i = 0
    · rw [ite_eq_left h2, Polynomial.coeff_X_pow_mul']
      by_cases h3 : j ≤ b
      · rw [ite_eq_left h3, Polynomial.coeff_C]
        by_cases h4 : b - j = 0
        · rw [ite_eq_left h4, ite_eq_left ⟨by omega, by omega⟩]
        · rw [ite_eq_right h4, ite_eq_right (by omega)]
      · rw [ite_eq_right h3, ite_eq_right (by omega)]
    · rw [ite_eq_right h2, ite_eq_right (by omega)]; rfl
  · rw [ite_eq_right h1, ite_eq_right (by omega)]; rfl

theorem coeff_truncTot (T : ℕ) (p : Bivar) (a b : ℕ) :
    (((truncTot T p).coeff a).coeff b) = if a + b ≤ T then (p.coeff a).coeff b else 0 := by
  simp only [truncTot, Polynomial.finsetSum_coeff]
  have h : ∀ i j, ((if i + j ≤ T then scalar ((p.coeff i).coeff j) * X ^ i * (C X) ^ j else 0 :
      Bivar).coeff a).coeff b = if a = i ∧ b = j ∧ a + b ≤ T then (p.coeff a).coeff b else 0 := by
    intro i j
    split_ifs with h1 h2 h2
    · rw [coeff_term, ite_eq_left ⟨h2.1, h2.2.1⟩, h2.1, h2.2.1]
    · rw [coeff_term]; split_ifs with h3
      · exact absurd ⟨h3.1, h3.2, by omega⟩ h2
      · rfl
    · exact absurd (by omega) h1
    · simp
  simp only [h]
  by_cases hab : a + b ≤ T
  · rw [ite_eq_left hab, Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp [hab]
    · intro j _ hj; simp [Ne.symm hj]
    · intro hb; exact absurd (Finset.mem_range.mpr (by omega)) hb
    · intro i _ hi; apply Finset.sum_eq_zero; intro j _; simp [Ne.symm hi]
    · intro ha; exact absurd (Finset.mem_range.mpr (by omega)) ha
  · rw [ite_eq_right hab]
    apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro j _
    rw [ite_eq_right (fun h => hab h.2.2)]

theorem truncate3_eq (p : Bivar) : TwoVariablePolynomial.truncate3 p = truncTot 3 p := by
  rw [TwoVariablePolynomial.truncate3, truncTot,
    Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin 4, if i + j.val ≤ 3 then
      scalar ((p.coeff i).coeff j.val) * X ^ i * (C X) ^ j.val else 0) 4]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun j => if i + j ≤ 3 then
      scalar ((p.coeff i).coeff j) * X ^ i * (C X) ^ j else 0) 4

theorem scalar_add (r t : ℚ) : scalar (r + t) = scalar r + scalar t := by simp [scalar]
theorem scalar_sub (r t : ℚ) : scalar (r - t) = scalar r - scalar t := by simp [scalar]
theorem scalar_mul (r t : ℚ) : scalar (r * t) = scalar r * scalar t := by simp [scalar]
theorem scalar_neg (r : ℚ) : scalar (-r) = -scalar r := by simp [scalar]
theorem mapQ_CC (k : ℕ) : mapQ (C (C k)) = scalar (k : ℚ) := by simp [mapQ, scalar]

/-! ## Substitutions -/

open TwoVariablePolynomial (substitute lift) in
theorem substitute_X (f g : Bivar) : TwoVariablePolynomial.substitute f g X = f := by
  simp [TwoVariablePolynomial.substitute]

theorem lift_X (g : Bivar) : TwoVariablePolynomial.lift g X = g := by
  simp [TwoVariablePolynomial.lift]

theorem lift_C (g : Bivar) (r : ℚ) : TwoVariablePolynomial.lift g (C r) = scalar r := by
  simp [TwoVariablePolynomial.lift, scalar]

theorem substitute_C (f g : Bivar) (q : ℚ[X]) :
    TwoVariablePolynomial.substitute f g (C q) = TwoVariablePolynomial.lift g q := by
  simp [TwoVariablePolynomial.substitute]

theorem substitute_CX (f g : Bivar) : TwoVariablePolynomial.substitute f g (C X) = g := by
  rw [substitute_C, lift_X]

theorem substitute_scalar (f g : Bivar) (r : ℚ) :
    TwoVariablePolynomial.substitute f g (scalar r) = scalar r := by
  rw [scalar, substitute_C, lift_C]; rfl

theorem lift_CX (q : ℚ[X]) : TwoVariablePolynomial.lift (C X) q = C q := by
  have h : TwoVariablePolynomial.lift (C X) = (C : ℚ[X] →+* Bivar) := by
    apply Polynomial.ringHom_ext
    · intro r; rw [lift_C]; rfl
    · rw [lift_X]
  rw [h]

theorem substitute_comp (f g f' g' : Bivar) (p : Bivar) :
    TwoVariablePolynomial.substitute f g (TwoVariablePolynomial.substitute f' g' p) =
      TwoVariablePolynomial.substitute (TwoVariablePolynomial.substitute f g f')
        (TwoVariablePolynomial.substitute f g g') p := by
  have h : (TwoVariablePolynomial.substitute f g).comp (TwoVariablePolynomial.substitute f' g') =
      TwoVariablePolynomial.substitute (TwoVariablePolynomial.substitute f g f')
        (TwoVariablePolynomial.substitute f g g') := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, substitute_C]
      have h2 : (TwoVariablePolynomial.substitute f g).comp (TwoVariablePolynomial.lift g') =
          TwoVariablePolynomial.lift (TwoVariablePolynomial.substitute f g g') := by
        apply Polynomial.ringHom_ext
        · intro r; simp only [RingHom.comp_apply, lift_C, substitute_scalar]
        · simp only [RingHom.comp_apply, lift_X]
      exact congrArg (fun φ : ℚ[X] →+* Bivar => φ a) h2
    · simp only [RingHom.comp_apply, substitute_X]
  exact congrArg (fun φ : Bivar →+* Bivar => φ p) h

/-- Row decomposition: `p = ∑ x ^ k · p_k(y)`. -/
theorem substitute_rows (f : Bivar) {p : Bivar} {n : ℕ} (hp : p.natDegree ≤ n) :
    TwoVariablePolynomial.substitute f (C X) p =
      ∑ k ∈ Finset.range (n + 1), f ^ k * C (p.coeff k) := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (by omega : p.natDegree < n + 1)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, substitute_X, substitute_C, lift_CX, mul_comm]

theorem colPoly_substitute (g : Bivar) (p : Bivar) (k : ℕ) :
    TwoVariablePolynomial.substitute X g (colPoly p k) = colPoly p k := by
  rw [colPoly, Polynomial.sum_def, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, substitute_X, substitute_C, lift_C]
  rfl

theorem eq_sum_colPoly {p : Bivar} {n : ℕ} (hp : ∀ i, (p.coeff i).natDegree ≤ n) :
    p = ∑ k ∈ Finset.range (n + 1), colPoly p k * (C X) ^ k := by
  ext i j
  simp only [Polynomial.finsetSum_coeff, ← map_pow, Polynomial.coeff_mul_C, coeff_colPoly,
    Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range] at h
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hp i; omega)

theorem substitute_cols (g : Bivar) {p : Bivar} {n : ℕ} (hp : ∀ i, (p.coeff i).natDegree ≤ n) :
    TwoVariablePolynomial.substitute X g p = ∑ k ∈ Finset.range (n + 1), g ^ k * colPoly p k := by
  conv_lhs => rw [eq_sum_colPoly hp]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, colPoly_substitute, substitute_CX, mul_comm]

theorem sum_rows_eq {f : Bivar} {p : Bivar} {q n : ℕ} (hq : q ≠ 0) (hp : p.natDegree ≤ n) :
    ∑ i ∈ Finset.range (n + 1), scalar ((q : ℚ) ^ (n - i)) * f ^ i * C (p.coeff i) =
      scalar ((q : ℚ) ^ n) *
        TwoVariablePolynomial.substitute (scalar (1 / (q : ℚ)) * f) (C X) p := by
  rw [substitute_rows _ hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  rw [mul_pow, ← mul_assoc, ← mul_assoc]
  congr 2
  rw [show ∀ r : ℚ, scalar r ^ i = scalar (r ^ i) from fun r => by simp [scalar], ← scalar_mul]
  congr 1
  rw [div_pow, one_pow, mul_one_div, eq_div_iff (pow_ne_zero _ hq'), ← pow_add,
    Nat.sub_add_cancel (by omega)]

theorem sum_cols_eq {g : Bivar} {p : Bivar} {q n : ℕ} (hq : q ≠ 0)
    (hp : ∀ i, (p.coeff i).natDegree ≤ n) :
    ∑ i ∈ Finset.range (n + 1), scalar ((q : ℚ) ^ (n - i)) * g ^ i * colPoly p i =
      scalar ((q : ℚ) ^ n) *
        TwoVariablePolynomial.substitute X (scalar (1 / (q : ℚ)) * g) p := by
  rw [substitute_cols _ hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  rw [mul_pow, ← mul_assoc, ← mul_assoc]
  congr 2
  rw [show ∀ r : ℚ, scalar r ^ i = scalar (r ^ i) from fun r => by simp [scalar], ← scalar_mul]
  congr 1
  rw [div_pow, one_pow, mul_one_div, eq_div_iff (pow_ne_zero _ hq'), ← pow_add,
    Nat.sub_add_cancel (by omega)]

/-! ## Chebyshev coefficients, row by row

Along `y`, the Chebyshev coefficients of every row are computed by the recursion of
`WholeIntervalPolynomial.Certificate.chebList`: `acc ← 2 ^ t · a_k + twoX acc`, where `twoX`
(multiplication by `2y` in the Chebyshev basis) is `divY (acc - col₀) + y · acc + y · col₀`. -/

/-- Column `k`, moved to column `0`. -/
def colK (c : Config) (P : NB) (k : ℕ) : NB := ofFun c (fun i j => if j = 0 then cf P i k else 0)
/-- Columns shifted down by one (column `0` dropped). -/
def dropY (c : Config) (P : NB) : NB := ofFun c (fun i j => cf P i (j + 1))
/-- Multiplication by `2 y` in the Chebyshev basis, row by row. -/
def twoXY (c : Config) (Q : NB) : NB := dropY c Q + C X * Q + C X * colK c Q 0
/-- `t` steps of the recursion along `y`, from column `D`. -/
def chebYP (c : Config) (P : NB) (D : ℕ) : ℕ → NB
  | 0 => 0
  | t + 1 => 2 ^ t • colK c P (D - t) + twoXY c (chebYP c P D t)

/-- Row `k`, moved to row `0`. -/
def rowK (c : Config) (P : NB) (k : ℕ) : NB := ofFun c (fun i j => if i = 0 then cf P k j else 0)
/-- Rows shifted down by one (row `0` dropped). -/
def dropX (c : Config) (P : NB) : NB := ofFun c (fun i j => cf P (i + 1) j)
/-- Multiplication by `2 x` in the Chebyshev basis, column by column. -/
def twoXX (c : Config) (Q : NB) : NB := dropX c Q + X * Q + X * rowK c Q 0
/-- `t` steps of the recursion along `x`, from row `D`. -/
def chebXP (c : Config) (P : NB) (D : ℕ) : ℕ → NB
  | 0 => 0
  | t + 1 => 2 ^ t • rowK c P (D - t) + twoXX c (chebXP c P D t)

theorem cf_mul_CX (Q : NB) (i j : ℕ) : cf (C X * Q) i j = if j = 0 then 0 else cf Q i (j - 1) := by
  rcases j with _ | j
  · rw [cf_CX_mul_zero]; rfl
  · rw [cf_CX_mul]; simp

theorem cf_mul_X (Q : NB) (i j : ℕ) : cf (X * Q) i j = if i = 0 then 0 else cf Q (i - 1) j := by
  rcases i with _ | i
  · rw [cf_X_mul_zero]; rfl
  · rw [cf_X_mul]; simp

/-- The row `i` of `P` from column `k`, `t` entries. -/
def rowFrom (P : NB) (i k t : ℕ) : List ℤ := (List.range t).map fun j => (cf P i (k + j) : ℤ)
/-- The column `j` of `P` from row `k`, `t` entries. -/
def colFrom (P : NB) (j k t : ℕ) : List ℤ := (List.range t).map fun i => (cf P (k + i) j : ℤ)

theorem rowFrom_succ (P : NB) (i k t : ℕ) :
    rowFrom P i k (t + 1) = (cf P i k : ℤ) :: rowFrom P i (k + 1) t := by
  simp only [rowFrom, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left; intro j _; simp [Nat.add_comm, Nat.add_left_comm]

theorem colFrom_succ (P : NB) (j k t : ℕ) :
    colFrom P j k (t + 1) = (cf P k j : ℤ) :: colFrom P j (k + 1) t := by
  simp only [colFrom, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left; intro i _; simp [Nat.add_comm, Nat.add_left_comm]

theorem length_rowFrom (P : NB) (i k t : ℕ) : (rowFrom P i k t).length = t := by simp [rowFrom]
theorem length_colFrom (P : NB) (j k t : ℕ) : (colFrom P j k t).length = t := by simp [colFrom]

open WholeIntervalPolynomial.Certificate in
/-- Along `y`: the rows of `chebYP` are the `chebList` of the rows of `P`. -/
theorem chebYP_spec {c : Config} (P : NB) {D : ℕ} (hD : D + 1 < c.S) :
    ∀ t, t ≤ D + 1 → (∀ i j, t ≤ j → cf (chebYP c P D t) i j = 0) ∧
      ∀ i, i < c.S → ∀ j, (cf (chebYP c P D t) i j : ℤ) =
        (chebList (rowFrom P i (D + 1 - t) t)).getD j 0
  | 0, _ => ⟨fun i j _ => by simp [chebYP, cf], fun i _ j => by simp [chebYP, cf, rowFrom, chebList]⟩
  | t + 1, ht => by
    obtain ⟨hsupp, hval⟩ := chebYP_spec P hD t (by omega)
    have hS1 : 1 < c.S := by omega
    have cfQ : ∀ i j, cf (chebYP c P D (t + 1)) i j =
        2 ^ t * (if i < c.S ∧ j < c.S then (if j = 0 then cf P i (D - t) else 0) else 0) +
        (if i < c.S ∧ j < c.S then cf (chebYP c P D t) i (j + 1) else 0) +
        (if j = 0 then 0 else cf (chebYP c P D t) i (j - 1)) +
        (if j = 0 then 0 else (if i < c.S ∧ j - 1 < c.S then (if j - 1 = 0 then cf (chebYP c P D t) i 0 else 0)
          else 0)) := by
      intro i j
      simp only [chebYP, twoXY, cf_add, cf_smul, cf_mul_CX, colK, dropY, cf_ofFun]
      ring
    constructor
    · intro i j hj
      rw [cfQ]
      have h1 := hsupp i (j + 1) (by omega)
      have h2 := hsupp i (j - 1) (by omega)
      split_ifs <;> simp_all
    · intro i hi j
      rw [show D + 1 - (t + 1) = D - t by omega, rowFrom_succ,
        show D - t + 1 = D + 1 - t by omega, chebList, length_rowFrom, getD_add]
      have hL := hval i hi
      rcases j with _ | _ | k
      · rw [getD_twoX_zero, ← hL 1, cfQ]
        simp only [hi, c.S_pos, true_and, ite_true, List.getD_cons_zero]
        push_cast; ring
      · rw [getD_twoX_one, ← hL 2, ← hL 0, cfQ]
        simp only [hi, hS1, true_and, ite_true, List.getD_cons_succ, List.getD_nil,
          Nat.sub_self, c.S_pos]
        push_cast; ring
      · rw [getD_twoX_succ, ← hL (k + 3), ← hL (k + 1), cfQ]
        simp only [List.getD_cons_succ, List.getD_nil]
        have e1 : k + 2 - 1 = k + 1 := by omega
        rw [e1]
        by_cases hk : k + 2 < c.S
        · simp only [hi, hk, true_and, ite_true, show k + 2 ≠ 0 by omega, ite_false,
            show k + 1 ≠ 0 by omega]
          push_cast; split_ifs <;> ring
        · have h3 := hsupp i (k + 3) (by omega)
          simp only [hi, hk, and_false, ite_false, show k + 2 ≠ 0 by omega, h3, ite_self]
          push_cast; split_ifs <;> ring

open WholeIntervalPolynomial.Certificate in
/-- Along `x`: the columns of `chebXP` are the `chebList` of the columns of `P`. -/
theorem chebXP_spec {c : Config} (P : NB) {D : ℕ} (hD : D + 1 < c.S) :
    ∀ t, t ≤ D + 1 → (∀ i j, t ≤ i → cf (chebXP c P D t) i j = 0) ∧
      ∀ j, j < c.S → ∀ i, (cf (chebXP c P D t) i j : ℤ) =
        (chebList (colFrom P j (D + 1 - t) t)).getD i 0
  | 0, _ => ⟨fun i j _ => by simp [chebXP, cf], fun j _ i => by simp [chebXP, cf, colFrom, chebList]⟩
  | t + 1, ht => by
    obtain ⟨hsupp, hval⟩ := chebXP_spec P hD t (by omega)
    have hS1 : 1 < c.S := by omega
    have cfQ : ∀ i j, cf (chebXP c P D (t + 1)) i j =
        2 ^ t * (if i < c.S ∧ j < c.S then (if i = 0 then cf P (D - t) j else 0) else 0) +
        (if i < c.S ∧ j < c.S then cf (chebXP c P D t) (i + 1) j else 0) +
        (if i = 0 then 0 else cf (chebXP c P D t) (i - 1) j) +
        (if i = 0 then 0 else (if i - 1 < c.S ∧ j < c.S then (if i - 1 = 0 then cf (chebXP c P D t) 0 j else 0)
          else 0)) := by
      intro i j
      simp only [chebXP, twoXX, cf_add, cf_smul, cf_mul_X, rowK, dropX, cf_ofFun]
      ring
    constructor
    · intro i j hi
      rw [cfQ]
      have h1 := hsupp (i + 1) j (by omega)
      have h2 := hsupp (i - 1) j (by omega)
      split_ifs <;> simp_all
    · intro j hj i
      rw [show D + 1 - (t + 1) = D - t by omega, colFrom_succ,
        show D - t + 1 = D + 1 - t by omega, chebList, length_colFrom, getD_add]
      have hL := hval j hj
      rcases i with _ | _ | k
      · rw [getD_twoX_zero, ← hL 1, cfQ]
        simp only [hj, c.S_pos, and_true, ite_true, List.getD_cons_zero]
        push_cast; ring
      · rw [getD_twoX_one, ← hL 2, ← hL 0, cfQ]
        simp only [hj, hS1, and_true, ite_true, List.getD_cons_succ, List.getD_nil,
          Nat.sub_self, c.S_pos]
        push_cast; ring
      · rw [getD_twoX_succ, ← hL (k + 3), ← hL (k + 1), cfQ]
        simp only [List.getD_cons_succ, List.getD_nil]
        have e1 : k + 2 - 1 = k + 1 := by omega
        rw [e1]
        by_cases hk : k + 2 < c.S
        · simp only [hj, hk, and_true, ite_true, show k + 2 ≠ 0 by omega, ite_false,
            show k + 1 ≠ 0 by omega]
          push_cast; split_ifs <;> ring
        · have h3 := hsupp (k + 3) j (by omega)
          simp only [hj, hk, false_and, ite_false, show k + 2 ≠ 0 by omega, h3, ite_self]
          push_cast; split_ifs <;> ring

open WholeIntervalPolynomial.Certificate in
theorem chebQ_rowFrom (P : NB) (a D j : ℕ) :
    chebQ (rowFrom P a 0 (D + 1)) j =
      ∑ b ∈ Finset.range (D + 1), (cf P a b : ℚ) * WholeIntervalPolynomial.monomialCoefficient b j := by
  rw [chebQ, length_rowFrom]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [rowFrom, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (Finset.mem_range.mp hb)]
  simp

open WholeIntervalPolynomial.Certificate in
theorem chebQ_colFrom (P : NB) (j D i : ℕ) :
    chebQ (colFrom P j 0 (D + 1)) i =
      ∑ a ∈ Finset.range (D + 1), (cf P a j : ℚ) * WholeIntervalPolynomial.monomialCoefficient a i := by
  rw [chebQ, length_colFrom]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [colFrom, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (Finset.mem_range.mp ha)]
  simp

open WholeIntervalPolynomial.Certificate in
/-- The Chebyshev transform of a row, from `chebYP`. -/
theorem sum_row_cheb {c : Config} (P : NB) {D : ℕ} (hD : D + 1 < c.S) {a : ℕ} (ha : a < c.S) (j : ℕ) :
    ∑ b ∈ Finset.range (D + 1), (cf P a b : ℚ) * WholeIntervalPolynomial.monomialCoefficient b j =
      2 * (cf (chebYP c P D (D + 1)) a j : ℚ) / 2 ^ (D + 1) := by
  have h := (chebYP_spec P hD (D + 1) le_rfl).2 a ha j
  rw [Nat.sub_self] at h
  have hs := chebList_spec (rowFrom P a 0 (D + 1)) j
  rw [length_rowFrom, ← h] at hs
  rw [← chebQ_rowFrom, eq_div_iff (by positivity)]
  push_cast at hs ⊢
  linarith

open WholeIntervalPolynomial.Certificate in
theorem sum_col_cheb {c : Config} (P : NB) {D : ℕ} (hD : D + 1 < c.S) {j : ℕ} (hj : j < c.S) (i : ℕ) :
    ∑ a ∈ Finset.range (D + 1), (cf P a j : ℚ) * WholeIntervalPolynomial.monomialCoefficient a i =
      2 * (cf (chebXP c P D (D + 1)) i j : ℚ) / 2 ^ (D + 1) := by
  have h := (chebXP_spec P hD (D + 1) le_rfl).2 j hj i
  rw [Nat.sub_self] at h
  have hs := chebList_spec (colFrom P j 0 (D + 1)) i
  rw [length_colFrom, ← h] at hs
  rw [← chebQ_colFrom, eq_div_iff (by positivity)]
  push_cast at hs ⊢
  linarith

/-- The two-dimensional Chebyshev coefficients of `q = (U - V) / σ`. -/
theorem coefficient_cheb {c : Config} {D : ℕ} (hD : D + 1 < c.S) (U V : NB) {σ : ℚ} (hσ : σ ≠ 0)
    {q : Bivar} (hq : ∀ a b, (q.coeff a).coeff b = ((cf U a b : ℚ) - cf V a b) / σ)
    {i j : ℕ} (_hi : i < c.S) (hj : j < c.S) :
    coefficient D q i j =
      ((cf (chebXP c (chebYP c U D (D + 1)) D (D + 1)) i j : ℚ) -
        cf (chebXP c (chebYP c V D (D + 1)) D (D + 1)) i j) / (4 ^ D * σ) := by
  rw [coefficient]
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin (D + 1), (q.coeff a).coeff b.val *
    WholeIntervalPolynomial.monomialCoefficient a i *
      WholeIntervalPolynomial.monomialCoefficient b.val j) (D + 1)]
  have inner : ∀ a ∈ Finset.range (D + 1), (∑ b : Fin (D + 1), (q.coeff a).coeff b.val *
      WholeIntervalPolynomial.monomialCoefficient a i *
        WholeIntervalPolynomial.monomialCoefficient b.val j) =
      WholeIntervalPolynomial.monomialCoefficient a i *
        (2 * ((cf (chebYP c U D (D + 1)) a j : ℚ) - cf (chebYP c V D (D + 1)) a j) /
          (2 ^ (D + 1) * σ)) := by
    intro a ha
    have ha' : a < c.S := by have := Finset.mem_range.mp ha; omega
    rw [Fin.sum_univ_eq_sum_range (fun b => (q.coeff a).coeff b *
      WholeIntervalPolynomial.monomialCoefficient a i *
        WholeIntervalPolynomial.monomialCoefficient b j) (D + 1)]
    have e1 := sum_row_cheb U hD ha' j
    have e2 := sum_row_cheb V hD ha' j
    have e3 : ∑ b ∈ Finset.range (D + 1), (q.coeff a).coeff b *
        WholeIntervalPolynomial.monomialCoefficient a i * WholeIntervalPolynomial.monomialCoefficient b j =
        WholeIntervalPolynomial.monomialCoefficient a i *
          ((∑ b ∈ Finset.range (D + 1), (cf U a b : ℚ) * WholeIntervalPolynomial.monomialCoefficient b j) -
            ∑ b ∈ Finset.range (D + 1), (cf V a b : ℚ) * WholeIntervalPolynomial.monomialCoefficient b j) / σ := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hq]; field_simp
    rw [e3, e1, e2]
    field_simp
  rw [Finset.sum_congr rfl inner]
  have e4 := sum_col_cheb (chebYP c U D (D + 1)) hD hj i
  have e5 := sum_col_cheb (chebYP c V D (D + 1)) hD hj i
  have e6 : ∑ a ∈ Finset.range (D + 1), WholeIntervalPolynomial.monomialCoefficient a i *
      (2 * ((cf (chebYP c U D (D + 1)) a j : ℚ) - cf (chebYP c V D (D + 1)) a j) / (2 ^ (D + 1) * σ)) =
      2 / (2 ^ (D + 1) * σ) *
        ((∑ a ∈ Finset.range (D + 1), (cf (chebYP c U D (D + 1)) a j : ℚ) *
            WholeIntervalPolynomial.monomialCoefficient a i) -
          ∑ a ∈ Finset.range (D + 1), (cf (chebYP c V D (D + 1)) a j : ℚ) *
            WholeIntervalPolynomial.monomialCoefficient a i) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    field_simp
  rw [e6, e4, e5, show (4 : ℚ) ^ D = 2 ^ D * 2 ^ D by rw [← mul_pow]; norm_num]
  field_simp
  ring

/-! ### Supports and digit sums along the recursion -/

theorem cf_ofFun_le (c : Config) (d : ℕ → ℕ → ℕ) (i j : ℕ) : cf (ofFun c d) i j ≤ d i j := by
  rw [cf_ofFun]; split_ifs <;> simp

theorem dsum_le_box {c : Config} {P : NB} (h : BoxSupp c P) :
    dsum P = ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, cf P i j := by
  conv_lhs => rw [eq_ofFun h]
  rw [dsum_ofFun]

theorem dsum_colK_le {c : Config} {P : NB} (h : BoxSupp c P) (k : ℕ) : dsum (colK c P k) ≤ dsum P := by
  rw [colK, dsum_ofFun, dsum_le_box h]
  apply Finset.sum_le_sum; intro i _
  rw [Finset.sum_eq_single 0 (fun j _ hj => by simp [hj]) (fun h0 => absurd (Finset.mem_range.mpr c.S_pos) h0)]
  simp only [ite_true]
  by_cases hk : k < c.S
  · exact Finset.single_le_sum (f := fun j => cf P i j) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hk)
  · have : cf P i k = 0 := by by_contra h0; have := h i k h0; omega
    rw [this]; exact Nat.zero_le _

theorem dsum_rowK_le {c : Config} {P : NB} (h : BoxSupp c P) (k : ℕ) : dsum (rowK c P k) ≤ dsum P := by
  rw [rowK, dsum_ofFun, dsum_le_box h]
  rw [Finset.sum_eq_single 0 (fun i _ hi => by simp [hi]) (fun h0 => absurd (Finset.mem_range.mpr c.S_pos) h0)]
  simp only [ite_true]
  by_cases hk : k < c.S
  · exact Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range c.S, cf P i j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hk)
  · have : ∀ j, cf P k j = 0 := fun j => by by_contra h0; have := h k j h0; omega
    simp [this]

theorem dsum_dropY_le {c : Config} {P : NB} (h : BoxSupp c P) : dsum (dropY c P) ≤ dsum P := by
  rw [dropY, dsum_ofFun, dsum_le_box h]
  apply Finset.sum_le_sum; intro i _
  have hS := c.S_pos
  obtain ⟨n, hn⟩ : ∃ n, c.S = n + 1 := ⟨c.S - 1, by omega⟩
  rw [hn, Finset.sum_range_succ, Finset.sum_range_succ' (fun j => cf P i j)]
  have : cf P i (n + 1) = 0 := by by_contra h0; have := h i (n + 1) h0; omega
  rw [this, add_zero]; omega

theorem dsum_dropX_le {c : Config} {P : NB} (h : BoxSupp c P) : dsum (dropX c P) ≤ dsum P := by
  rw [dropX, dsum_ofFun, dsum_le_box h]
  have hS := c.S_pos
  obtain ⟨n, hn⟩ : ∃ n, c.S = n + 1 := ⟨c.S - 1, by omega⟩
  rw [hn, Finset.sum_range_succ, Finset.sum_range_succ' (fun i => ∑ j ∈ Finset.range (n + 1), cf P i j)]
  have : ∑ j ∈ Finset.range (n + 1), cf P (n + 1) j = 0 :=
    Finset.sum_eq_zero fun j _ => by by_contra h0; have := h (n + 1) j h0; omega
  rw [this, add_zero]; omega

theorem boxSupp_ofFun (c : Config) (d : ℕ → ℕ → ℕ) : BoxSupp c (ofFun c d) := fun i j h => by
  rw [cf_ofFun] at h; split_ifs at h with hij
  · exact hij
  · exact absurd rfl h

theorem chebYP_box {c : Config} (P : NB) {D : ℕ} (hD : D + 1 < c.S) (t : ℕ) (ht : t ≤ D + 1) :
    BoxSupp c (chebYP c P D t) := by
  have hsupp := (chebYP_spec P hD t ht).1
  intro i j h
  refine ⟨?_, by by_contra hj; exact h (hsupp i j (by omega))⟩
  induction t generalizing i j with
  | zero => simp [chebYP, cf] at h
  | succ t ih =>
    by_contra hi
    apply h
    simp only [chebYP, twoXY, cf_add, cf_smul, cf_mul_CX, colK, dropY, cf_ofFun]
    have h1 : ∀ j', cf (chebYP c P D t) i j' = 0 := fun j' => by
      by_contra h0; exact hi (ih (by omega) (chebYP_spec P hD t (by omega)).1 i j' h0)
    simp [hi, h1]

theorem chebXP_box {c : Config} (P : NB) {D : ℕ} (hD : D + 1 < c.S) (t : ℕ) (ht : t ≤ D + 1) :
    BoxSupp c (chebXP c P D t) := by
  have hsupp := (chebXP_spec P hD t ht).1
  intro i j h
  refine ⟨by by_contra hi; exact h (hsupp i j (by omega)), ?_⟩
  induction t generalizing i j with
  | zero => simp [chebXP, cf] at h
  | succ t ih =>
    by_contra hj
    apply h
    simp only [chebXP, twoXX, cf_add, cf_smul, cf_mul_X, rowK, dropX, cf_ofFun]
    have h1 : ∀ i', cf (chebXP c P D t) i' j = 0 := fun i' => by
      by_contra h0; exact hj (ih (by omega) (chebXP_spec P hD t (by omega)).1 i' j h0)
    simp [hj, h1]

theorem dsum_CX_mul (Q : NB) : dsum (C X * Q) = dsum Q := by rw [dsum_mul, dsum_Y, one_mul]
theorem dsum_X_mul (Q : NB) : dsum (X * Q) = dsum Q := by rw [dsum_mul, dsum_X, one_mul]

theorem dsum_chebYP {c : Config} {P : NB} (hP : BoxSupp c P) {D : ℕ} (hD : D + 1 < c.S) :
    ∀ t, t ≤ D + 1 → dsum (chebYP c P D t) ≤ 4 ^ t * dsum P
  | 0, _ => by simp [chebYP, dsum]
  | t + 1, ht => by
    have ih := dsum_chebYP hP hD t (by omega)
    have hb := chebYP_box P hD t (by omega)
    simp only [chebYP, twoXY, dsum_add, dsum_smul, dsum_CX_mul]
    have h1 := dsum_colK_le hP (D - t)
    have h2 := dsum_dropY_le hb
    have h3 := dsum_colK_le hb 0
    have h4 : 2 ^ t ≤ 4 ^ t := Nat.pow_le_pow_left (by norm_num) t
    have h5 : 4 ^ (t + 1) = 4 * 4 ^ t := by ring
    rw [h5]
    nlinarith [Nat.mul_le_mul h4 h1]

theorem dsum_chebXP {c : Config} {P : NB} (hP : BoxSupp c P) {D : ℕ} (hD : D + 1 < c.S) :
    ∀ t, t ≤ D + 1 → dsum (chebXP c P D t) ≤ 4 ^ t * dsum P
  | 0, _ => by simp [chebXP, dsum]
  | t + 1, ht => by
    have ih := dsum_chebXP hP hD t (by omega)
    have hb := chebXP_box P hD t (by omega)
    simp only [chebXP, twoXX, dsum_add, dsum_smul, dsum_X_mul]
    have h1 := dsum_rowK_le hP (D - t)
    have h2 := dsum_dropX_le hb
    have h3 := dsum_rowK_le hb 0
    have h4 : 2 ^ t ≤ 4 ^ t := Nat.pow_le_pow_left (by norm_num) t
    have h5 : 4 ^ (t + 1) = 4 * 4 ^ t := by ring
    rw [h5]
    nlinarith [Nat.mul_le_mul h4 h1]

/-! ### The recursion on packed numbers -/

/-- All digits except those of column `0`. -/
def notCol0 (c : Config) : ℕ := boxPat c (c.b - 1) - col0Mask c

theorem notCol0_eq (c : Config) (hw : 1 ≤ c.w) :
    notCol0 c = pack c (fun _ j => if j = 0 then 0 else c.b - 1) := by
  rw [notCol0, boxPat_eq c hw, col0Mask_eq c hw, pack_sub]
  · apply pack_congr; intro i j _ _; split_ifs <;> omega
  · intro i j; split_ifs <;> omega

def colKN (c : Config) (N k : ℕ) : ℕ := (N >>> (c.w * k)) &&& col0Mask c
def dropYN (c : Config) (N : ℕ) : ℕ := (N &&& notCol0 c) >>> c.w
def twoXYN (c : Config) (N : ℕ) : ℕ := dropYN c N + (N <<< c.w) + (colKN c N 0 <<< c.w)
def chebYN (c : Config) (N D : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => colKN c N (D - t) * 2 ^ t + twoXYN c (chebYN c N D t)

def rowKN (c : Config) (N k : ℕ) : ℕ := (N >>> (c.w * (c.S * k))) &&& rowMask c
def dropXN (c : Config) (N : ℕ) : ℕ := N >>> (c.w * c.S)
def twoXXN (c : Config) (N : ℕ) : ℕ := dropXN c N + (N <<< (c.w * c.S)) + (rowKN c N 0 <<< (c.w * c.S))
def chebXN (c : Config) (N D : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => rowKN c N (D - t) * 2 ^ t + twoXXN c (chebXN c N D t)

theorem colKN_eq {c : Config} (hw : 0 < c.w) (N : ℕ) {k : ℕ} (hk : k < c.S) :
    colKN c N k = evB c (colK c (poly c N) k) := by
  rw [colKN, colSlice_eq hw N hk, colK, evB_ofFun]
  apply pack_congr; intro i j hi _
  split_ifs
  · rw [cf_poly, ite_eq_left ⟨hi, hk⟩]; rfl
  · rfl

theorem rowKN_eq {c : Config} (hw : 0 < c.w) (N : ℕ) {k : ℕ} (hk : k < c.S) :
    rowKN c N k = evB c (rowK c (poly c N) k) := by
  rw [rowKN, rowSlice_eq hw N hk, rowK, evB_ofFun]
  apply pack_congr; intro i j _ hj
  split_ifs
  · rw [cf_poly, ite_eq_left ⟨hk, hj⟩]; rfl
  · rfl

theorem dropYN_eq {c : Config} (hw : 1 ≤ c.w) {N : ℕ} (_hN : Box c N) :
    dropYN c N = evB c (dropY c (poly c N)) := by
  set d : ℕ → ℕ → ℕ := fun i j => if j = 0 then 0 else coeffs c N i j with hd
  set d' : ℕ → ℕ → ℕ := fun i j => if j + 1 < c.S then coeffs c N i (j + 1) else 0 with hd'
  have hdlt : ∀ i j, d i j < c.b := fun i j => by
    simp only [hd]; split_ifs; exacts [c.b_pos, coeffs_lt c _ _ _]
  have h1 : N &&& notCol0 c = pack c d := by
    rw [notCol0_eq c hw]
    apply land_pattern (pack_box c (fun i j => by have := c.b_pos; split_ifs <;> omega))
    · intro i j hi hj
      rw [coeffs_pack c (fun i j => by have := c.b_pos; split_ifs <;> omega) hi hj]
      simp only [hd]; split_ifs
      · exact Nat.and_zero _
      · exact land_full (coeffs_lt c N i j)
    · exact hdlt
  have h2 : ofFun c d = C X * ofFun c d' := by
    apply ext_cf; intro i j
    rw [cf_mul_CX, cf_ofFun, cf_ofFun]
    simp only [hd, hd']
    rcases j with _ | j
    · simp
    · simp only [Nat.add_sub_cancel, show j + 1 ≠ 0 by omega, ite_false]
      by_cases hij : i < c.S ∧ j + 1 < c.S
      · rw [ite_eq_left hij, ite_eq_left ⟨hij.1, by omega⟩, ite_eq_left hij.2]
      · rw [ite_eq_right hij]
        split_ifs <;> simp_all
  have h3 : pack c d = c.b * pack c d' := by
    rw [← evB_ofFun, h2, map_mul, evB_Y, evB_ofFun]
  rw [dropYN, h1, h3, Nat.shiftRight_eq_div_pow, show 2 ^ c.w = c.b from rfl,
    Nat.mul_div_cancel_left _ c.b_pos, dropY, evB_ofFun]
  apply pack_congr; intro i j hi hj
  simp only [hd']
  rw [cf_poly]
  split_ifs with h4 h5 h5
  · rfl
  · exact absurd ⟨hi, h4⟩ h5
  · exact absurd h5.2 h4
  · rfl

/-- A packed number of a single row is below `b ^ S`. -/
theorem evB_row_lt {c : Config} {R : NB} (hR : BoxSupp c R) (h0 : ∀ i j, 1 ≤ i → cf R i j = 0)
    (hlt : ∀ i j, cf R i j < c.b) : evB c R < c.b ^ c.S := by
  rw [eq_ofFun hR, evB_ofFun, pack_eq_sum,
    ← Finset.sum_range_add_sum_Ico _ (Nat.le_mul_self c.S)]
  rw [Finset.sum_eq_zero (s := Finset.Ico _ _) (fun u hu => by
    rw [Finset.mem_Ico] at hu
    rw [h0 _ _ ((Nat.le_div_iff_mul_le c.S_pos).mpr (by omega)), zero_mul]), add_zero]
  have e : ∀ u ∈ Finset.range c.S, cf R (u / c.S) (u % c.S) * c.b ^ u = cf R 0 u * c.b ^ u :=
    fun u hu => by
      rw [Finset.mem_range] at hu; rw [Nat.div_eq_of_lt hu, Nat.mod_eq_of_lt hu]
  rw [Finset.sum_congr rfl e]
  exact sum_digits_lt c.b_pos (fun u => cf R 0 u) (fun u => hlt 0 u) c.S

theorem dropXN_eq {c : Config} {N : ℕ} (hN : Box c N) : dropXN c N = evB c (dropX c (poly c N)) := by
  have hP := poly_boxSupp c N
  have hid : poly c N = rowK c (poly c N) 0 + X * dropX c (poly c N) := by
    apply ext_cf; intro i j
    rw [cf_add, cf_mul_X, rowK, dropX, cf_ofFun, cf_ofFun]
    rcases i with _ | i
    · by_cases hj : j < c.S
      · simp [hj, c.S_pos]
      · have : cf (poly c N) 0 j = 0 := by by_contra h0; exact hj (hP 0 j h0).2
        simp [hj, this]
    · by_cases hij : i + 1 < c.S ∧ j < c.S
      · simp [hij.2, show i < c.S by omega]
      · have : cf (poly c N) (i + 1) j = 0 := by by_contra h0; exact hij (hP _ _ h0)
        simp [this]
  have hlt : ∀ i j, cf (rowK c (poly c N) 0) i j < c.b := fun i j => by
    rw [rowK, cf_ofFun]; split_ifs
    · exact cf_poly_lt c N 0 j
    · exact c.b_pos
    · exact c.b_pos
  have hrow : evB c (rowK c (poly c N) 0) < c.b ^ c.S :=
    evB_row_lt (R := rowK c (poly c N) 0) (boxSupp_ofFun c _) (fun i j hi => by
      rw [rowK, cf_ofFun]; split_ifs with h1 h2 <;> first | rfl | omega) hlt
  have e : N = evB c (rowK c (poly c N) 0) + c.b ^ c.S * evB c (dropX c (poly c N)) := by
    have h := congrArg (evB c) hid
    rw [evB_poly hN, map_add, map_mul, evB_X] at h
    exact h
  rw [dropXN, Nat.shiftRight_eq_div_pow, show 2 ^ (c.w * c.S) = c.b ^ c.S by
    simp [Config.b, ← pow_mul]]
  conv_lhs => rw [e]
  rw [Nat.add_mul_div_left _ _ (pow_pos c.b_pos _), Nat.div_eq_of_lt hrow, zero_add]

theorem twoXYN_eq {c : Config} (hw : 1 ≤ c.w) {N : ℕ} (hN : Box c N) (hS : 1 < c.S) :
    twoXYN c N = evB c (twoXY c (poly c N)) := by
  rw [twoXYN, twoXY, map_add, map_add, map_mul, map_mul, evB_Y, dropYN_eq hw hN,
    colKN_eq (by omega) N (by omega), evB_poly hN, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    show 2 ^ c.w = c.b from rfl]
  ring

theorem twoXXN_eq {c : Config} (hw : 1 ≤ c.w) {N : ℕ} (hN : Box c N) :
    twoXXN c N = evB c (twoXX c (poly c N)) := by
  rw [twoXXN, twoXX, map_add, map_add, map_mul, map_mul, evB_X, dropXN_eq hN,
    rowKN_eq (by omega) N c.S_pos, evB_poly hN, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    show 2 ^ (c.w * c.S) = c.b ^ c.S by simp [Config.b, ← pow_mul]]
  ring

theorem chebYN_eq {c : Config} (hw : 1 ≤ c.w) {N : ℕ} (hN : Box c N) {D : ℕ} (hD : D + 1 < c.S)
    (hb : 4 ^ (D + 1) * dsum (poly c N) < c.b) :
    ∀ t, t ≤ D + 1 → chebYN c N D t = evB c (chebYP c (poly c N) D t)
  | 0, _ => by simp [chebYN, chebYP]
  | t + 1, ht => by
    have ih := chebYN_eq hw hN hD hb t (by omega)
    set Q := chebYP c (poly c N) D t
    have hQ := chebYP_box (poly c N) hD t (by omega)
    have hds : dsum Q < c.b := lt_of_le_of_lt ((dsum_chebYP (poly_boxSupp c N) hD t (by omega)).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega)))) hb
    have hlt : ∀ i j, cf Q i j < c.b := fun i j => (cf_le_dsum hQ i j).trans_lt hds
    have hbox : Box c (evB c Q) := box_evB hQ hlt
    have hpoly : poly c (evB c Q) = Q := poly_evB hQ hlt
    rw [chebYN, chebYP, ih, twoXYN_eq hw hbox (by omega), hpoly,
      colKN_eq (by omega) N (by omega), map_add, map_nsmul, smul_eq_mul, mul_comm]

theorem chebXN_eq {c : Config} (hw : 1 ≤ c.w) {N : ℕ} (hN : Box c N) {D : ℕ} (hD : D + 1 < c.S)
    (hb : 4 ^ (D + 1) * dsum (poly c N) < c.b) :
    ∀ t, t ≤ D + 1 → chebXN c N D t = evB c (chebXP c (poly c N) D t)
  | 0, _ => by simp [chebXN, chebXP]
  | t + 1, ht => by
    have ih := chebXN_eq hw hN hD hb t (by omega)
    set Q := chebXP c (poly c N) D t
    have hQ := chebXP_box (poly c N) hD t (by omega)
    have hds : dsum Q < c.b := lt_of_le_of_lt ((dsum_chebXP (poly_boxSupp c N) hD t (by omega)).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega)))) hb
    have hlt : ∀ i j, cf Q i j < c.b := fun i j => (cf_le_dsum hQ i j).trans_lt hds
    have hbox : Box c (evB c Q) := box_evB hQ hlt
    have hpoly : poly c (evB c Q) = Q := poly_evB hQ hlt
    rw [chebXN, chebXP, ih, twoXXN_eq hw hbox, hpoly,
      rowKN_eq (by omega) N (by omega), map_add, map_nsmul, smul_eq_mul, mul_comm]

/-! ### The degree-`D` expansion identity -/

theorem scalar_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    scalar (∑ i ∈ s, f i) = ∑ i ∈ s, scalar (f i) := by simp [scalar, map_sum]

theorem series_eq_sum (D : ℕ) (c : ℕ → ℕ → ℚ) :
    series D c = ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
      scalar (c i j) * basis i j := by
  rw [series, indices]
  have h0 : scalar (c 0 0) = (fun ij : Fin (D + 1) × Fin (D + 1) =>
      scalar (c ij.1.val ij.2.val) * basis ij.1.val ij.2.val) (0, 0) := by
    simp [basis, Polynomial.Chebyshev.T_zero]
  rw [h0, Finset.add_sum_erase Finset.univ (fun ij : Fin (D + 1) × Fin (D + 1) =>
      scalar (c ij.1.val ij.2.val) * basis ij.1.val ij.2.val) (Finset.mem_univ (0, 0)),
    Fintype.sum_prod_type,
    Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin (D + 1), scalar (c i j.val) * basis i j.val)]
  exact Finset.sum_congr rfl fun i _ =>
    Fin.sum_univ_eq_sum_range (fun j => scalar (c i j) * basis i j) (D + 1)

theorem coefficient_eq_sum (D : ℕ) (q : Bivar) (i j : ℕ) :
    coefficient D q i j = ∑ a ∈ Finset.range (D + 1), ∑ b ∈ Finset.range (D + 1),
      (q.coeff a).coeff b * WholeIntervalPolynomial.monomialCoefficient a i *
        WholeIntervalPolynomial.monomialCoefficient b j := by
  rw [coefficient, Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin (D + 1), (q.coeff a).coeff b.val *
    WholeIntervalPolynomial.monomialCoefficient a i *
      WholeIntervalPolynomial.monomialCoefficient b.val j) (D + 1)]
  exact Finset.sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range (fun b => (q.coeff a).coeff b *
    WholeIntervalPolynomial.monomialCoefficient a i *
      WholeIntervalPolynomial.monomialCoefficient b j) (D + 1)

/-- A polynomial of degree at most `D` in each variable equals its degree-`D` expansion. -/
theorem eq_expansion_of_degrees {q : Bivar} {D : ℕ} (h1 : q.natDegree ≤ D)
    (h2 : ∀ a, (q.coeff a).natDegree ≤ D) : q = expansion D q := by
  have hX : ∀ a, a ≤ D → (X : Bivar) ^ a = ∑ i ∈ Finset.range (D + 1),
      scalar (WholeIntervalPolynomial.monomialCoefficient a i) *
        Polynomial.Chebyshev.T (Polynomial ℚ) (i : ℤ) := by
    intro a ha
    have h := congrArg (Polynomial.map (C : ℚ →+* ℚ[X]))
      (WholeIntervalPolynomial.sum_monomialCoefficient_mul_T_of_le (D := D) ha)
    simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.Chebyshev.map_T, Polynomial.map_pow, Polynomial.map_X] at h
    rw [← h]; rfl
  have hY : ∀ b, b ≤ D → (C X : Bivar) ^ b = ∑ j ∈ Finset.range (D + 1),
      scalar (WholeIntervalPolynomial.monomialCoefficient b j) * C (Polynomial.Chebyshev.T ℚ (j : ℤ)) := by
    intro b hb
    have h := congrArg (C : ℚ[X] →+* Bivar)
      (WholeIntervalPolynomial.sum_monomialCoefficient_mul_T_of_le (D := D) hb)
    simp only [map_sum, map_mul, map_pow] at h
    rw [← h]; rfl
  have hq : q = ∑ a ∈ Finset.range (D + 1), ∑ b ∈ Finset.range (D + 1),
      scalar ((q.coeff a).coeff b) * X ^ a * (C X) ^ b := by
    conv_lhs => rw [q.as_sum_range_C_mul_X_pow' (by omega : q.natDegree < D + 1)]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [(q.coeff a).as_sum_range_C_mul_X_pow' (n := D + 1) (by have := h2 a; omega)]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [scalar, map_mul, map_pow]; ring
  rw [expansion, series_eq_sum]
  simp only [coefficient_eq_sum, scalar_sum, Finset.sum_mul]
  conv_lhs => rw [hq]
  have e : ∀ a ∈ Finset.range (D + 1), ∀ b ∈ Finset.range (D + 1),
      scalar ((q.coeff a).coeff b) * X ^ a * (C X) ^ b =
        ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
          scalar ((q.coeff a).coeff b * WholeIntervalPolynomial.monomialCoefficient a i *
            WholeIntervalPolynomial.monomialCoefficient b j) * basis i j := by
    intro a ha b hb
    rw [hX a (by simp at ha; omega), hY b (by simp at hb; omega), mul_assoc, Finset.sum_mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [basis, scalar_mul]; ring
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => e a ha b hb]
  set R := Finset.range (D + 1)
  set F : ℕ → ℕ → ℕ → ℕ → Bivar := fun a b i j =>
    scalar ((q.coeff a).coeff b * WholeIntervalPolynomial.monomialCoefficient a i *
      WholeIntervalPolynomial.monomialCoefficient b j) * basis i j
  show ∑ a ∈ R, ∑ b ∈ R, ∑ i ∈ R, ∑ j ∈ R, F a b i j = ∑ i ∈ R, ∑ j ∈ R, ∑ a ∈ R, ∑ b ∈ R, F a b i j
  calc ∑ a ∈ R, ∑ b ∈ R, ∑ i ∈ R, ∑ j ∈ R, F a b i j
      = ∑ a ∈ R, ∑ i ∈ R, ∑ b ∈ R, ∑ j ∈ R, F a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i ∈ R, ∑ a ∈ R, ∑ b ∈ R, ∑ j ∈ R, F a b i j := Finset.sum_comm
    _ = ∑ i ∈ R, ∑ a ∈ R, ∑ j ∈ R, ∑ b ∈ R, F a b i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i ∈ R, ∑ j ∈ R, ∑ a ∈ R, ∑ b ∈ R, F a b i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem chebXP_col_zero (c : Config) (P : NB) (D : ℕ) {j : ℕ} (hj : ∀ i, cf P i j = 0) :
    ∀ t i, cf (chebXP c P D t) i j = 0
  | 0, i => by simp [chebXP, cf]
  | t + 1, i => by
    have ih := chebXP_col_zero c P D hj t
    simp only [chebXP, twoXX, cf_add, cf_smul, cf_mul_X, rowK, dropX, cf_ofFun, hj, ih]
    simp

/-- The norm of a coefficient function, as a double sum. -/
theorem norm_eq_sum (D : ℕ) (f : ℕ → ℕ → ℚ) :
    TensorWholeIntervalPolynomial.norm D f =
      (∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1), |f i j|) - |f 0 0| := by
  rw [TensorWholeIntervalPolynomial.norm, indices, eq_sub_iff_add_eq, add_comm]
  have h := Finset.add_sum_erase (Finset.univ : Finset (Fin (D + 1) × Fin (D + 1)))
    (fun ij => |f ij.1.val ij.2.val|) (Finset.mem_univ (0, 0))
  simp only [Fin.val_zero] at h
  rw [h, Fintype.sum_prod_type,
    Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin (D + 1), |f i j.val|)]
  exact Finset.sum_congr rfl fun i _ => Fin.sum_univ_eq_sum_range (fun j => |f i j|) (D + 1)

/-- Two bivariate polynomials with the same values on `ℝ²` are equal. -/
theorem eq_of_evaluate {p q : Bivar} (h : ∀ x y : ℝ, evaluate x y p = evaluate x y q) : p = q := by
  rw [← sub_eq_zero]
  have hr : ∀ x y : ℝ, evaluate x y (p - q) = 0 := fun x y => by rw [map_sub, h, sub_self]
  generalize p - q = r at hr
  ext k j
  have h1 : ∀ y : ℝ, aeval y (r.coeff k) = 0 := by
    intro y
    have hm : r.map (aeval y : ℚ[X] →ₐ[ℚ] ℝ).toRingHom = 0 := by
      apply Polynomial.funext; intro x
      rw [Polynomial.eval_map, Polynomial.eval_zero]
      exact hr x y
    have := congrArg (fun P => P.coeff k) hm
    simpa [Polynomial.coeff_map] using this
  have h2 : (r.coeff k).map (algebraMap ℚ ℝ) = 0 := by
    apply Polynomial.funext; intro y
    rw [Polynomial.eval_map_algebraMap, Polynomial.eval_zero]
    exact h1 y
  have h3 : r.coeff k = 0 :=
    Polynomial.map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective (by rw [h2, Polynomial.map_zero])
  simp [h3]

/-! ## Coefficients of swaps, quotients and derivatives -/

theorem lift_X_eq_map (q : ℚ[X]) : TwoVariablePolynomial.lift X q = q.map C := rfl

theorem coeff_swap (p : Bivar) (i j : ℕ) :
    ((TwoVariablePolynomial.swap p).coeff i).coeff j = (p.coeff j).coeff i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [TwoVariablePolynomial.swap, map_add, Polynomial.coeff_add] at hp hq ⊢
    rw [hp, hq]
  | monomial n a =>
    rw [TwoVariablePolynomial.swap, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
      substitute_X, substitute_C, lift_X_eq_map, ← map_pow, Polynomial.coeff_mul_C,
      Polynomial.coeff_map, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp

theorem coeff_divY (p : Bivar) (i j : ℕ) :
    ((TwoVariablePolynomial.divY p).coeff i).coeff j = (p.coeff i).coeff (j + 1) := by
  rw [TwoVariablePolynomial.divY, coeff_swap, Polynomial.coeff_divX, coeff_swap]

theorem coeff_derivativeY (p : Bivar) (i j : ℕ) :
    ((TwoVariablePolynomial.derivativeY p).coeff i).coeff j = ((j : ℚ) + 1) * (p.coeff i).coeff (j + 1) := by
  rw [TwoVariablePolynomial.derivativeY, coeff_swap, Polynomial.coeff_derivative,
    show ((j : ℚ[X]) + 1) = C ((j : ℚ) + 1) by simp, Polynomial.coeff_mul_C, coeff_swap, mul_comm]

theorem coeff_derivativeX (p : Bivar) (i j : ℕ) :
    ((Polynomial.derivative p).coeff i).coeff j = ((i : ℚ) + 1) * (p.coeff (i + 1)).coeff j := by
  rw [Polynomial.coeff_derivative, show ((i : ℚ[X]) + 1) = C ((i : ℚ) + 1) by simp,
    Polynomial.coeff_mul_C, mul_comm]

theorem coeff_colTerm (r : ℚ) (k : ℕ) (p : Bivar) (m i j : ℕ) :
    ((scalar r * (X ^ 0 * (C X) ^ k) * colPoly p m).coeff i).coeff j =
      if j = k then r * (p.coeff i).coeff m else 0 := by
  have e : scalar r * (X ^ 0 * (C X) ^ k) = C (C r * X ^ k) := by simp [scalar]
  rw [e, Polynomial.coeff_C_mul, coeff_colPoly, Polynomial.coeff_mul_C, Polynomial.coeff_C_mul_X_pow]
  split_ifs <;> simp

theorem coeff_rowTerm (r : ℚ) (k : ℕ) (a : ℚ[X]) (i j : ℕ) :
    ((scalar r * (X ^ k * (C X) ^ 0) * C a).coeff i).coeff j =
      if i = k then r * a.coeff j else 0 := by
  rw [pow_zero, mul_one, Polynomial.coeff_mul_C, scalar, Polynomial.coeff_C_mul_X_pow]
  split_ifs <;> simp [Polynomial.coeff_C_mul]

/-- `∂_y p`, column by column. -/
theorem derivativeY_eq_sum {p : Bivar} {n : ℕ} (hp : ∀ i, (p.coeff i).natDegree ≤ n) :
    TwoVariablePolynomial.derivativeY p = ∑ k ∈ Finset.range n,
      scalar ((((k + 1 : ℕ) : ℤ)) : ℚ) * (X ^ 0 * (C X) ^ k) * colPoly p (k + 1) := by
  ext i j
  rw [coeff_derivativeY, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  simp only [coeff_colTerm]
  rw [Finset.sum_ite_eq (Finset.range n) j]
  split_ifs with hj
  · push_cast; ring
  · rw [Finset.mem_range, not_lt] at hj
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hp i; omega), mul_zero]

/-- `∂_x p`, row by row. -/
theorem derivativeX_eq_sum {p : Bivar} {n : ℕ} (hp : p.natDegree ≤ n) :
    Polynomial.derivative p = ∑ k ∈ Finset.range n,
      scalar ((((k + 1 : ℕ) : ℤ)) : ℚ) * (X ^ k * (C X) ^ 0) * C (p.coeff (k + 1)) := by
  ext i j
  rw [coeff_derivativeX, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  simp only [coeff_rowTerm]
  rw [Finset.sum_ite_eq (Finset.range n) i]
  split_ifs with hi
  · push_cast; ring
  · rw [Finset.mem_range, not_lt] at hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := p) (n := i + 1) (by omega), Polynomial.coeff_zero,
      mul_zero]

/-! ## Exact models -/

/-- An exact model: the polynomial `(poly U - poly V) / s`, with bounds on its support and on the
sum of its numerator coefficients, and the conjunction `ok` of the checks made while building it. -/
structure XM where
  U : ℕ
  V : ℕ
  s : ℕ
  dx : ℕ
  dy : ℕ
  dt : ℕ
  sz : ℕ
  ok : Bool

namespace XM

/-- The numerator `poly U - poly V`. -/
def val (c : Config) (m : XM) : Bivar := mapQ (poly c m.U) - mapQ (poly c m.V)

/-- The invariant of a model whose checks passed. -/
structure Good (c : Config) (m : XM) : Prop where
  boxU : Box c m.U
  boxV : Box c m.V
  suppU : Supp (poly c m.U) m.dx m.dy m.dt
  suppV : Supp (poly c m.V) m.dx m.dy m.dt
  size : dsum (poly c m.U) + dsum (poly c m.V) ≤ m.sz
  small : m.sz < 2 ^ (c.w - 2)
  dxS : m.dx + 1 < c.S
  dyS : m.dy + 1 < c.S

/-- `m` represents `p`. -/
def Rep (c : Config) (m : XM) (p : Bivar) : Prop :=
  m.ok = true → m.Good c ∧ m.val c = scalar (m.s : ℚ) * p

/-- The checks of a result. -/
def fits (c : Config) (sz dx dy : ℕ) : Bool :=
  Nat.blt sz (2 ^ (c.w - 2)) && Nat.blt (dx + 1) c.S && Nat.blt (dy + 1) c.S

theorem fits_spec {c : Config} {sz dx dy : ℕ} (h : fits c sz dx dy = true) :
    sz < 2 ^ (c.w - 2) ∧ dx + 1 < c.S ∧ dy + 1 < c.S := by
  simp only [fits, Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem small_lt_b (c : Config) {n : ℕ} (h : n < 2 ^ (c.w - 2)) : n < c.b :=
  lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- The integer `n / s`. -/
def ofInt (c : Config) (n : ℤ) (s : ℕ) : XM :=
  ⟨if 0 ≤ n then n.toNat else 0, if 0 ≤ n then 0 else n.natAbs, s, 0, 0, 0, n.natAbs,
    fits c n.natAbs 0 0 && Nat.blt 0 s⟩

theorem poly_const {c : Config} {k : ℕ} (hk : k < c.b) : poly c k = C (C k) := by
  have h := poly_evB' (c := c) (supp_C_C k) (by have := c.S_pos; omega) (by have := c.S_pos; omega)
    (by rw [dsum_C_C]; exact hk)
  rwa [evB_C_C] at h

theorem rep_ofInt (c : Config) (n : ℤ) (s : ℕ) : (ofInt c n s).Rep c (scalar ((n : ℚ) / s)) := by
  intro hok
  simp only [ofInt, Bool.and_eq_true, Nat.blt_eq] at hok
  obtain ⟨hf, hs⟩ := hok
  obtain ⟨h1, h2, h3⟩ := fits_spec hf
  have hb := small_lt_b c h1
  have hb0 : 0 < c.b := c.b_pos
  have hS1 : (0 : ℕ) < c.S := c.S_pos
  have hs' : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
  by_cases hn : 0 ≤ n
  · simp only [ofInt, hn, ite_true]
    have e1 : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hn
    have e2 : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
    have e3 : n.toNat = n.natAbs := by exact_mod_cast e2.trans e1.symm
    have hk : n.toNat < c.b := by rw [e3]; exact hb
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, h1, h2, h3⟩, ?_⟩
    · rw [← evB_C_C c n.toNat]; exact box_evB' (supp_C_C _) hS1 hS1 (by rw [dsum_C_C]; exact hk)
    · rw [← evB_C_C c 0]; exact box_evB' (supp_C_C _) hS1 hS1 (by rw [dsum_C_C]; exact hb0)
    · rw [poly_const hk]; exact supp_C_C _
    · rw [poly_const hb0]; exact supp_C_C _
    · rw [poly_const hk, poly_const hb0, dsum_C_C, dsum_C_C, e3, Nat.add_zero]
    · rw [val, poly_const hk, poly_const hb0, mapQ_CC, mapQ_CC, ← scalar_sub, ← scalar_mul]
      congr 1
      have : ((n.toNat : ℕ) : ℚ) = n := by exact_mod_cast e2
      rw [this]
      field_simp
      simp
  · simp only [ofInt, hn, ite_false]
    have e1 : (n.natAbs : ℤ) = -n := Int.ofNat_natAbs_of_nonpos (by omega)
    have hk : n.natAbs < c.b := hb
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, h1, h2, h3⟩, ?_⟩
    · rw [← evB_C_C c 0]; exact box_evB' (supp_C_C _) hS1 hS1 (by rw [dsum_C_C]; exact hb0)
    · rw [← evB_C_C c n.natAbs]; exact box_evB' (supp_C_C _) hS1 hS1 (by rw [dsum_C_C]; exact hk)
    · rw [poly_const hb0]; exact supp_C_C _
    · rw [poly_const hk]; exact supp_C_C _
    · rw [poly_const hk, poly_const hb0, dsum_C_C, dsum_C_C, Nat.zero_add]
    · rw [val, poly_const hk, poly_const hb0, mapQ_CC, mapQ_CC, ← scalar_sub, ← scalar_mul]
      congr 1
      have : ((n.natAbs : ℕ) : ℚ) = -n := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast (lt_of_not_ge hn))]
      rw [this]
      field_simp
      simp

/-- Decoding the result of a ring operation. -/
theorem decode {c : Config} {P : NB} {dx dy dt sz : ℕ} (hP : Supp P dx dy dt) (hx : dx + 1 < c.S)
    (hy : dy + 1 < c.S) (hs : dsum P ≤ sz) (hsz : sz < 2 ^ (c.w - 2)) :
    Box c (evB c P) ∧ poly c (evB c P) = P :=
  have hb : dsum P < c.b := lt_of_le_of_lt hs (small_lt_b c hsz)
  ⟨box_evB' hP (by omega) (by omega) hb, poly_evB' hP (by omega) (by omega) hb⟩

theorem mapQ_smul (k : ℕ) (P : NB) : mapQ (k • P) = (k : Bivar) * mapQ P := by
  rw [nsmul_eq_mul, map_mul, map_natCast]

theorem natCast_eq_scalar (k : ℕ) : (k : Bivar) = scalar (k : ℚ) := by simp [scalar]

theorem Good.U_eq {c : Config} {m : XM} (h : m.Good c) : m.U = evB c (poly c m.U) :=
  evB_poly_eq h.boxU
theorem Good.V_eq {c : Config} {m : XM} (h : m.Good c) : m.V = evB c (poly c m.V) :=
  evB_poly_eq h.boxV

/-- `a + b`, over the least common multiple of the scales. -/
def add (c : Config) (a b : XM) : XM :=
  let g := Nat.gcd a.s b.s
  let ka := b.s / g
  let kb := a.s / g
  ⟨a.U * ka + b.U * kb, a.V * ka + b.V * kb, a.s / g * b.s, max a.dx b.dx, max a.dy b.dy,
    max a.dt b.dt, a.sz * ka + b.sz * kb,
    a.ok && b.ok && fits c (a.sz * ka + b.sz * kb) (max a.dx b.dx) (max a.dy b.dy)⟩

theorem rep_add {c : Config} {a b : XM} {p q : Bivar} (ha : a.Rep c p) (hb : b.Rep c q) :
    (add c a b).Rep c (p + q) := by
  intro hok
  simp only [add, Bool.and_eq_true] at hok
  obtain ⟨⟨hao, hbo⟩, hf⟩ := hok
  obtain ⟨hsz, hdx, hdy⟩ := fits_spec hf
  obtain ⟨ga, va⟩ := ha hao
  obtain ⟨gb, vb⟩ := hb hbo
  set g := Nat.gcd a.s b.s
  set ka := b.s / g
  set kb := a.s / g
  have sU := (ga.suppU.max_left b.dx b.dy b.dt).smul ka
  have sU' := (gb.suppU.max_right a.dx a.dy a.dt).smul kb
  have sV := (ga.suppV.max_left b.dx b.dy b.dt).smul ka
  have sV' := (gb.suppV.max_right a.dx a.dy a.dt).smul kb
  have hdU : dsum (ka • poly c a.U + kb • poly c b.U) ≤ a.sz * ka + b.sz * kb := by
    rw [dsum_add, dsum_smul, dsum_smul]
    nlinarith [Nat.mul_le_mul_right ka ga.size, Nat.mul_le_mul_right kb gb.size]
  have hdV : dsum (ka • poly c a.V + kb • poly c b.V) ≤ a.sz * ka + b.sz * kb := by
    rw [dsum_add, dsum_smul, dsum_smul]
    nlinarith [Nat.mul_le_mul_right ka ga.size, Nat.mul_le_mul_right kb gb.size]
  have eU : a.U * ka + b.U * kb = evB c (ka • poly c a.U + kb • poly c b.U) := by
    rw [map_add, map_nsmul, map_nsmul, ← ga.U_eq, ← gb.U_eq, smul_eq_mul, smul_eq_mul]; ring
  have eV : a.V * ka + b.V * kb = evB c (ka • poly c a.V + kb • poly c b.V) := by
    rw [map_add, map_nsmul, map_nsmul, ← ga.V_eq, ← gb.V_eq, smul_eq_mul, smul_eq_mul]; ring
  have hsum : dsum (ka • poly c a.U + kb • poly c b.U) + dsum (ka • poly c a.V + kb • poly c b.V) ≤
      a.sz * ka + b.sz * kb := by
    rw [dsum_add, dsum_add, dsum_smul, dsum_smul, dsum_smul, dsum_smul]
    nlinarith [Nat.mul_le_mul_right ka ga.size, Nat.mul_le_mul_right kb gb.size]
  obtain ⟨bU, pU⟩ := decode (sU.add sU') hdx hdy hdU hsz
  obtain ⟨bV, pV⟩ := decode (sV.add sV') hdx hdy hdV hsz
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hsz, hdx, hdy⟩, ?_⟩
  · simp only [add]; rw [eU]; exact bU
  · simp only [add]; rw [eV]; exact bV
  · simp only [add]; rw [eU, pU]; exact sU.add sU'
  · simp only [add]; rw [eV, pV]; exact sV.add sV'
  · simp only [add]; rw [eU, pU, eV, pV]; exact hsum
  · simp only [val, add]
    rw [eU, pU, eV, pV]
    simp only [val] at va vb
    simp only [map_add, mapQ_smul]
    have e1 : (ka : Bivar) * mapQ (poly c a.U) + (kb : Bivar) * mapQ (poly c b.U) -
        ((ka : Bivar) * mapQ (poly c a.V) + (kb : Bivar) * mapQ (poly c b.V)) =
        (ka : Bivar) * (mapQ (poly c a.U) - mapQ (poly c a.V)) +
        (kb : Bivar) * (mapQ (poly c b.U) - mapQ (poly c b.V)) := by ring
    rw [e1, va, vb, natCast_eq_scalar, natCast_eq_scalar, ← mul_assoc, ← mul_assoc,
      ← scalar_mul, ← scalar_mul]
    have hl := lcm_eq a.s b.s
    have hl1 : ((ka : ℚ) * a.s) = ((a.s / g * b.s : ℕ) : ℚ) := by exact_mod_cast hl
    have hl2 : ((kb : ℚ) * b.s) = ((a.s / g * b.s : ℕ) : ℚ) := by push_cast; ring
    rw [hl1, hl2, mul_add]

/-- `-a`. -/
def neg (a : XM) : XM := ⟨a.V, a.U, a.s, a.dx, a.dy, a.dt, a.sz, a.ok⟩

theorem rep_neg {c : Config} {a : XM} {p : Bivar} (ha : a.Rep c p) : (neg a).Rep c (-p) := by
  intro hok
  obtain ⟨ga, va⟩ := ha hok
  refine ⟨⟨ga.boxV, ga.boxU, ga.suppV, ga.suppU, by simp only [neg]; have := ga.size; omega,
    ga.small, ga.dxS, ga.dyS⟩, ?_⟩
  simp only [val, neg] at va ⊢
  linear_combination (-1 : Bivar) * va

/-- `a - b`. -/
def sub (c : Config) (a b : XM) : XM := add c a (neg b)

theorem rep_sub {c : Config} {a b : XM} {p q : Bivar} (ha : a.Rep c p) (hb : b.Rep c q) :
    (sub c a b).Rep c (p - q) := by
  rw [sub_eq_add_neg]; exact rep_add ha (rep_neg hb)

/-- `a * b`. -/
def mul (c : Config) (a b : XM) : XM :=
  ⟨a.U * b.U + a.V * b.V, a.U * b.V + a.V * b.U, a.s * b.s, a.dx + b.dx, a.dy + b.dy,
    a.dt + b.dt, a.sz * b.sz, a.ok && b.ok && fits c (a.sz * b.sz) (a.dx + b.dx) (a.dy + b.dy)⟩

theorem rep_mul {c : Config} {a b : XM} {p q : Bivar} (ha : a.Rep c p) (hb : b.Rep c q) :
    (mul c a b).Rep c (p * q) := by
  intro hok
  simp only [mul, Bool.and_eq_true] at hok
  obtain ⟨⟨hao, hbo⟩, hf⟩ := hok
  obtain ⟨hsz, hdx, hdy⟩ := fits_spec hf
  obtain ⟨ga, va⟩ := ha hao
  obtain ⟨gb, vb⟩ := hb hbo
  set Pa := poly c a.U
  set Va := poly c a.V
  set Pb := poly c b.U
  set Vb := poly c b.V
  have sU := (ga.suppU.mul gb.suppU).add (ga.suppV.mul gb.suppV)
  have sV := (ga.suppU.mul gb.suppV).add (ga.suppV.mul gb.suppU)
  have hsa := ga.size
  have hsb := gb.size
  have hdU : dsum (Pa * Pb + Va * Vb) ≤ a.sz * b.sz := by
    rw [dsum_add, dsum_mul, dsum_mul]; nlinarith
  have hdV : dsum (Pa * Vb + Va * Pb) ≤ a.sz * b.sz := by
    rw [dsum_add, dsum_mul, dsum_mul]; nlinarith
  have eU : a.U * b.U + a.V * b.V = evB c (Pa * Pb + Va * Vb) := by
    rw [map_add, map_mul, map_mul, ← ga.U_eq, ← gb.U_eq, ← ga.V_eq, ← gb.V_eq]
  have eV : a.U * b.V + a.V * b.U = evB c (Pa * Vb + Va * Pb) := by
    rw [map_add, map_mul, map_mul, ← ga.U_eq, ← gb.U_eq, ← ga.V_eq, ← gb.V_eq]
  obtain ⟨bU, pU⟩ := decode sU hdx hdy hdU hsz
  obtain ⟨bV, pV⟩ := decode sV hdx hdy hdV hsz
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hsz, hdx, hdy⟩, ?_⟩
  · simp only [mul]; rw [eU]; exact bU
  · simp only [mul]; rw [eV]; exact bV
  · simp only [mul]; rw [eU, pU]; exact sU
  · simp only [mul]; rw [eV, pV]; exact sV
  · simp only [mul]; rw [eU, pU, eV, pV, dsum_add, dsum_add, dsum_mul, dsum_mul, dsum_mul, dsum_mul]
    nlinarith
  · simp only [val, mul] at va vb ⊢
    rw [eU, pU, eV, pV]
    simp only [map_add, map_mul]
    have e1 : mapQ Pa * mapQ Pb + mapQ Va * mapQ Vb - (mapQ Pa * mapQ Vb + mapQ Va * mapQ Pb) =
        (mapQ Pa - mapQ Va) * (mapQ Pb - mapQ Vb) := by ring
    rw [e1, va, vb, Nat.cast_mul, scalar_mul]; ring

/-- `a ^ n`. -/
def pow (c : Config) (a : XM) : ℕ → XM
  | 0 => ofInt c 1 1
  | 1 => a
  | n + 2 => mul c (pow c a (n + 1)) a

theorem rep_pow {c : Config} {a : XM} {p : Bivar} (ha : a.Rep c p) : ∀ n, (pow c a n).Rep c (p ^ n)
  | 0 => by
    have h := rep_ofInt c 1 1
    simp only [Int.cast_one, Nat.cast_one, div_one] at h
    simpa [pow, scalar] using h
  | 1 => by simpa [pow] using ha
  | n + 2 => by rw [pow, pow_succ]; exact rep_mul (rep_pow ha (n + 1)) ha

/-- The variable `x`. -/
def varX (c : Config) : XM := ⟨c.b ^ c.S, 0, 1, 1, 0, 1, 1, fits c 1 1 0⟩
/-- The variable `y`. -/
def varY (c : Config) : XM := ⟨c.b, 0, 1, 0, 1, 1, 1, fits c 1 0 1⟩

theorem rep_X (c : Config) : (varX c).Rep c Polynomial.X := by
  intro hok
  obtain ⟨hsz, hdx, hdy⟩ := fits_spec hok
  obtain ⟨bU, pU⟩ := decode (c := c) supp_X hdx hdy (le_of_eq dsum_X) hsz
  obtain ⟨b0, p0⟩ := decode (c := c) (Supp.zero 1 0 1) hdx hdy (by simp [dsum]) hsz
  rw [evB_X] at bU pU
  rw [map_zero] at b0 p0
  refine ⟨⟨bU, b0, ?_, ?_, ?_, hsz, hdx, hdy⟩, ?_⟩
  · simp only [varX]; rw [pU]; exact supp_X
  · simp only [varX]; rw [p0]; exact Supp.zero _ _ _
  · simp only [varX]; rw [pU, p0, dsum_X]; simp [dsum]
  · simp only [val, varX]; rw [pU, p0]; simp [mapQ, scalar]

theorem rep_Y (c : Config) : (varY c).Rep c (C Polynomial.X) := by
  intro hok
  obtain ⟨hsz, hdx, hdy⟩ := fits_spec hok
  obtain ⟨bU, pU⟩ := decode (c := c) supp_Y hdx hdy (le_of_eq dsum_Y) hsz
  obtain ⟨b0, p0⟩ := decode (c := c) (Supp.zero 0 1 1) hdx hdy (by simp [dsum]) hsz
  rw [evB_Y] at bU pU
  rw [map_zero] at b0 p0
  refine ⟨⟨bU, b0, ?_, ?_, ?_, hsz, hdx, hdy⟩, ?_⟩
  · simp only [varY]; rw [pU]; exact supp_Y
  · simp only [varY]; rw [p0]; exact Supp.zero _ _ _
  · simp only [varY]; rw [pU, p0, dsum_Y]; simp [dsum]
  · simp only [val, varY]; rw [pU, p0]; simp [mapQ, scalar]

/-- Every digit of a box number is at most its digit sum. -/
theorem digit_le_dsum {c : Config} {N : ℕ} (h : Box c N) (m : ℕ) :
    digit c.w N m ≤ dsum (poly c N) := by
  by_cases hm : m < c.S * c.S
  · have hS := c.S_pos
    have hi : m / c.S < c.S := Nat.div_lt_of_lt_mul hm
    have hj : m % c.S < c.S := Nat.mod_lt _ hS
    have e : m = c.S * (m / c.S) + m % c.S := (Nat.div_add_mod m c.S).symm
    have hc := cf_le_dsum (poly_boxSupp c N) (m / c.S) (m % c.S)
    rw [cf_poly, ite_eq_left ⟨hi, hj⟩, ← e] at hc
    exact hc
  · rw [digit_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right c.b_pos (by omega)))]
    exact Nat.zero_le _

theorem coeffs_lt_half {c : Config} {N sz : ℕ} (h : Box c N) (hs : dsum (poly c N) ≤ sz)
    (hsz : sz < 2 ^ (c.w - 2)) (i j : ℕ) : coeffs c N i j < 2 ^ (c.w - 1) :=
  lt_of_le_of_lt ((digit_le_dsum h _).trans hs)
    (lt_of_lt_of_le hsz (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- Sign normalization, with the exact digit sums. -/
def norm (c : Config) (m : XM) : XM :=
  let r := normBox c m.U m.V
  ⟨r.1, r.2, m.s, m.dx, m.dy, m.dt, r.1 % (c.b - 1) + r.2 % (c.b - 1), m.ok && Nat.ble 2 c.w⟩

theorem rep_norm {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) : (norm c m).Rep c p := by
  intro hok
  simp only [norm, Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨hok, hw⟩ := hok
  obtain ⟨g, v⟩ := hm hok
  have hu := coeffs_lt_half g.boxU (le_trans (Nat.le_add_right _ _) g.size) g.small
  have hv := coeffs_lt_half g.boxV (le_trans (Nat.le_add_left _ _) g.size) g.small
  obtain ⟨e1, e2⟩ := normBox_spec hw g.boxU g.boxV hu hv
  set U' := (normBox c m.U m.V).1
  set V' := (normBox c m.U m.V).2
  have hb : ∀ i j, coeffs c m.U i j - coeffs c m.V i j < c.b := fun i j =>
    lt_of_le_of_lt (Nat.sub_le _ _) (coeffs_lt c _ i j)
  have hb' : ∀ i j, coeffs c m.V i j - coeffs c m.U i j < c.b := fun i j =>
    lt_of_le_of_lt (Nat.sub_le _ _) (coeffs_lt c _ i j)
  have bU : Box c U' := by rw [e1]; exact pack_box c hb
  have bV : Box c V' := by rw [e2]; exact pack_box c hb'
  -- coefficients of the normalized polynomials
  have cU : ∀ i j, cf (poly c U') i j = cf (poly c m.U) i j - cf (poly c m.V) i j := fun i j => by
    rw [cf_poly, cf_poly, cf_poly]
    split_ifs with hij
    · rw [e1]; exact coeffs_pack c hb hij.1 hij.2
    · rfl
  have cV : ∀ i j, cf (poly c V') i j = cf (poly c m.V) i j - cf (poly c m.U) i j := fun i j => by
    rw [cf_poly, cf_poly, cf_poly]
    split_ifs with hij
    · rw [e2]; exact coeffs_pack c hb' hij.1 hij.2
    · rfl
  have sU : Supp (poly c U') m.dx m.dy m.dt := fun i j hij => by
    rw [cU] at hij
    exact g.suppU i j (fun h0 => hij (by rw [h0, Nat.zero_sub]))
  have sV : Supp (poly c V') m.dx m.dy m.dt := fun i j hij => by
    rw [cV] at hij
    exact g.suppV i j (fun h0 => hij (by rw [h0, Nat.zero_sub]))
  -- digit sums
  have hle : dsum (poly c U') + dsum (poly c V') ≤ dsum (poly c m.U) + dsum (poly c m.V) := by
    have hsU := g.suppU.boxSupp (c := c) (by have := g.dxS; omega) (by have := g.dyS; omega)
    have hsV := g.suppV.boxSupp (c := c) (by have := g.dxS; omega) (by have := g.dyS; omega)
    have hsU' := sU.boxSupp (c := c) (by have := g.dxS; omega) (by have := g.dyS; omega)
    have hsV' := sV.boxSupp (c := c) (by have := g.dxS; omega) (by have := g.dyS; omega)
    rw [eq_ofFun hsU, eq_ofFun hsV, eq_ofFun hsU', eq_ofFun hsV', dsum_ofFun, dsum_ofFun,
      dsum_ofFun, dsum_ofFun, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro j _
    rw [cU, cV]; omega
  have hlt : dsum (poly c U') + dsum (poly c V') < c.b - 1 := by
    have := g.size; have := g.small
    have : 2 ^ (c.w - 2) < c.b - 1 := by
      unfold Config.b
      have : 2 ^ (c.w - 2) * 4 = 2 ^ c.w := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
      have : 2 ^ (c.w - 2) ≥ 1 := Nat.one_le_two_pow
      omega
    omega
  have mU : U' % (c.b - 1) = dsum (poly c U') := by
    rw [← dsumN_eq]; exact mod_eq_dsumN bU (by unfold Config.M; rw [dsumN_eq]; omega)
  have mV : V' % (c.b - 1) = dsum (poly c V') := by
    rw [← dsumN_eq]; exact mod_eq_dsumN bV (by unfold Config.M; rw [dsumN_eq]; omega)
  refine ⟨⟨bU, bV, sU, sV, ?_, ?_, g.dxS, g.dyS⟩, ?_⟩
  · show dsum (poly c U') + dsum (poly c V') ≤ U' % (c.b - 1) + V' % (c.b - 1)
    rw [mU, mV]
  · show U' % (c.b - 1) + V' % (c.b - 1) < 2 ^ (c.w - 2)
    rw [mU, mV]; have := g.size; have := g.small; omega
  · show mapQ (poly c U') - mapQ (poly c V') = scalar (m.s : ℚ) * p
    simp only [val] at v
    rw [← v]
    ext i j
    simp only [Polynomial.coeff_sub, coeff_mapQ, cU, cV]
    rcases le_total (cf (poly c m.U) i j) (cf (poly c m.V) i j) with h | h
    · rw [Nat.sub_eq_zero_of_le h]; push_cast [h]; ring
    · rw [Nat.sub_eq_zero_of_le h]; push_cast [h]; ring

/-- `(n / d) · a`: numerator times `n`, scale times `d`. -/
def mulQ (c : Config) (a : XM) (n : ℤ) (d : ℕ) : XM :=
  let k := n.natAbs
  if 0 ≤ n then ⟨a.U * k, a.V * k, a.s * d, a.dx, a.dy, a.dt, a.sz * k,
      a.ok && fits c (a.sz * k) a.dx a.dy && Nat.blt 0 d⟩
  else ⟨a.V * k, a.U * k, a.s * d, a.dx, a.dy, a.dt, a.sz * k,
      a.ok && fits c (a.sz * k) a.dx a.dy && Nat.blt 0 d⟩

/-- `e · x ^ ax · y ^ ay · a`, by shifts. -/
def monoMul (c : Config) (a : XM) (e : ℤ) (ax ay : ℕ) : XM :=
  let k := e.natAbs
  let sh := c.w * (c.S * ax + ay)
  let U := (a.U <<< sh) * k
  let V := (a.V <<< sh) * k
  let ok := a.ok && fits c (a.sz * k) (a.dx + ax) (a.dy + ay)
  if 0 ≤ e then ⟨U, V, a.s, a.dx + ax, a.dy + ay, a.dt + ax + ay, a.sz * k, ok⟩
  else ⟨V, U, a.s, a.dx + ax, a.dy + ay, a.dt + ax + ay, a.sz * k, ok⟩

/-- The general scaling lemma: the numerators become `evB (k • P)` for a natural factor `k`. -/
theorem rep_scaleMono {c : Config} {a : XM} {p : Bivar} (ha : a.Rep c p) (k ax ay : ℕ) (d : ℕ)
    (_hd : 0 < d) (o : Bool) {U V : ℕ} (hU : U = (a.U <<< (c.w * (c.S * ax + ay))) * k)
    (hV : V = (a.V <<< (c.w * (c.S * ax + ay))) * k) (hok : a.ok = true)
    (hf : fits c (a.sz * k) (a.dx + ax) (a.dy + ay) = true) :
    (⟨U, V, a.s * d, a.dx + ax, a.dy + ay, a.dt + ax + ay, a.sz * k, o⟩ : XM).Good c ∧
      mapQ (poly c U) - mapQ (poly c V) =
        (k : Bivar) * (Polynomial.X ^ ax * (C Polynomial.X) ^ ay) * (scalar (a.s : ℚ) * p) := by
  obtain ⟨hsz, hdx, hdy⟩ := fits_spec hf
  obtain ⟨g, v⟩ := ha hok
  set M : NB := (X : NB) ^ ax * (C X) ^ ay
  have sU := ((g.suppU.mul (supp_monomial ax ay)).smul k)
  have sV := ((g.suppV.mul (supp_monomial ax ay)).smul k)
  have hsa := g.size
  have hM : dsum M = 1 := dsum_monomial ax ay
  have dU : dsum (k • (poly c a.U * M)) ≤ a.sz * k := by
    rw [dsum_smul, dsum_mul (poly c a.U) M, hM]; nlinarith
  have dV : dsum (k • (poly c a.V * M)) ≤ a.sz * k := by
    rw [dsum_smul, dsum_mul (poly c a.V) M, hM]; nlinarith
  have eU : U = evB c (k • (poly c a.U * M)) := by
    rw [hU, map_nsmul, map_mul, ← g.U_eq, evB_monomial, Nat.shiftLeft_eq, smul_eq_mul, mul_comm k]
  have eV : V = evB c (k • (poly c a.V * M)) := by
    rw [hV, map_nsmul, map_mul, ← g.V_eq, evB_monomial, Nat.shiftLeft_eq, smul_eq_mul, mul_comm k]
  have hx : a.dx + ax + 1 < c.S := hdx
  have hy : a.dy + ay + 1 < c.S := hdy
  obtain ⟨bU, pU⟩ := decode (dt := a.dt + ax + ay) (sU.mono le_rfl le_rfl (by omega)) hx hy dU hsz
  obtain ⟨bV, pV⟩ := decode (dt := a.dt + ax + ay) (sV.mono le_rfl le_rfl (by omega)) hx hy dV hsz
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hsz, hdx, hdy⟩, ?_⟩
  · simp only; rw [eU]; exact bU
  · simp only; rw [eV]; exact bV
  · simp only; rw [eU, pU]; exact sU.mono le_rfl le_rfl (by omega)
  · simp only; rw [eV, pV]; exact sV.mono le_rfl le_rfl (by omega)
  · simp only; rw [eU, pU, eV, pV, dsum_smul, dsum_smul, dsum_mul (poly c a.U) M,
      dsum_mul (poly c a.V) M, hM]
    nlinarith
  · rw [eU, pU, eV, pV, mapQ_smul, mapQ_smul]
    have hv : mapQ (poly c a.U) - mapQ (poly c a.V) = scalar (a.s : ℚ) * p := v
    have hMQ : mapQ M = Polynomial.X ^ ax * (C Polynomial.X) ^ ay := by simp [M, mapQ]
    rw [map_mul mapQ (poly c a.U) M, map_mul mapQ (poly c a.V) M, hMQ]
    linear_combination ((k : Bivar) * (Polynomial.X ^ ax * (C Polynomial.X) ^ ay)) * hv

theorem rep_mulQ {c : Config} {a : XM} {p : Bivar} (ha : a.Rep c p) (n : ℤ) (d : ℕ) :
    (mulQ c a n d).Rep c (scalar ((n : ℚ) / d) * p) := by
  intro hok
  by_cases hn : 0 ≤ n
  · simp only [mulQ, hn, ite_true, Bool.and_eq_true, Nat.blt_eq] at hok
    obtain ⟨⟨hao, hf⟩, hd⟩ := hok
    have hf' : fits c (a.sz * n.natAbs) (a.dx + 0) (a.dy + 0) = true := by simpa using hf
    obtain ⟨g, v⟩ := rep_scaleMono ha n.natAbs 0 0 d hd true rfl rfl hao hf'
    simp only [mulQ, hn, ite_true]
    simp only [Nat.mul_zero, Nat.add_zero, Nat.shiftLeft_zero] at g v
    refine ⟨⟨g.boxU, g.boxV, g.suppU, g.suppV, g.size, g.small, g.dxS, g.dyS⟩, ?_⟩
    rw [val, v]
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have e : ((n.natAbs : ℕ) : ℚ) = n := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hn)]
    simp only [pow_zero, mul_one, natCast_eq_scalar, ← mul_assoc, ← scalar_mul, e]
    congr 2
    push_cast; field_simp
  · simp only [mulQ, hn, ite_false, Bool.and_eq_true, Nat.blt_eq] at hok
    obtain ⟨⟨hao, hf⟩, hd⟩ := hok
    have hf' : fits c (a.sz * n.natAbs) (a.dx + 0) (a.dy + 0) = true := by simpa using hf
    obtain ⟨g, v⟩ := rep_scaleMono ha n.natAbs 0 0 d hd true rfl rfl hao hf'
    simp only [mulQ, hn, ite_false]
    simp only [Nat.mul_zero, Nat.add_zero, Nat.shiftLeft_zero] at g v
    refine ⟨⟨g.boxV, g.boxU, g.suppV, g.suppU, by have := g.size; simp only at this ⊢; omega,
      g.small, g.dxS, g.dyS⟩, ?_⟩
    simp only [val]
    rw [show mapQ (poly c (a.V * n.natAbs)) - mapQ (poly c (a.U * n.natAbs)) =
      -(mapQ (poly c (a.U * n.natAbs)) - mapQ (poly c (a.V * n.natAbs))) by ring, v]
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have e : ((n.natAbs : ℕ) : ℚ) = -n := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast (lt_of_not_ge hn))]
    simp only [pow_zero, mul_one, natCast_eq_scalar, ← mul_assoc, ← scalar_mul, e]
    have e2 : (((a.s * d : ℕ) : ℚ) * ((n : ℚ) / d)) = -(-(n : ℚ) * a.s) := by
      push_cast; field_simp
    rw [e2, scalar_neg]; ring

theorem rep_monoMul {c : Config} {a : XM} {p : Bivar} (ha : a.Rep c p) (e : ℤ) (ax ay : ℕ) :
    (monoMul c a e ax ay).Rep c (scalar (e : ℚ) * (Polynomial.X ^ ax * (C Polynomial.X) ^ ay) * p) := by
  intro hok
  by_cases he : 0 ≤ e
  · simp only [monoMul, he, ite_true, Bool.and_eq_true] at hok
    obtain ⟨hao, hf⟩ := hok
    obtain ⟨g, v⟩ := rep_scaleMono ha e.natAbs ax ay 1 one_pos
      (a.ok && fits c (a.sz * e.natAbs) (a.dx + ax) (a.dy + ay)) rfl rfl hao hf
    simp only [monoMul, he, ite_true]
    simp only [Nat.mul_one] at g
    refine ⟨g, ?_⟩
    rw [val, v]
    have e1 : ((e.natAbs : ℕ) : ℚ) = e := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast he)]
    rw [natCast_eq_scalar, e1]; ring
  · simp only [monoMul, he, ite_false, Bool.and_eq_true] at hok
    obtain ⟨hao, hf⟩ := hok
    obtain ⟨g, v⟩ := rep_scaleMono ha e.natAbs ax ay 1 one_pos true rfl rfl hao hf
    simp only [monoMul, he, ite_false]
    simp only [Nat.mul_one] at g
    refine ⟨⟨g.boxV, g.boxU, g.suppV, g.suppU, by have := g.size; simp only at this ⊢; omega,
      g.small, g.dxS, g.dyS⟩, ?_⟩
    simp only [val]
    rw [show ∀ A B : Bivar, A - B = -(B - A) from fun A B => by ring, v]
    have e1 : ((e.natAbs : ℕ) : ℚ) = -e := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast (lt_of_not_ge he))]
    rw [natCast_eq_scalar, e1, scalar_neg]; ring

/-! ### Models given digitwise -/

theorem cf_poly_pack {c : Config} {d : ℕ → ℕ → ℕ} (hd : ∀ i j, d i j < c.b) (i j : ℕ) :
    cf (poly c (pack c d)) i j = if i < c.S ∧ j < c.S then d i j else 0 := by
  rw [cf_poly]; split_ifs with h
  · exact digit_pack_ij c hd h.1 h.2
  · rfl

theorem good_pack {c : Config} {U V s dx dy dt sz : ℕ} (o : Bool) {dU dV : ℕ → ℕ → ℕ}
    (hU : U = pack c dU) (hV : V = pack c dV) (hdU : ∀ i j, dU i j < c.b)
    (hdV : ∀ i j, dV i j < c.b)
    (sU : ∀ i j, i < c.S → j < c.S → dU i j ≠ 0 → i ≤ dx ∧ j ≤ dy ∧ i + j ≤ dt)
    (sV : ∀ i j, i < c.S → j < c.S → dV i j ≠ 0 → i ≤ dx ∧ j ≤ dy ∧ i + j ≤ dt)
    (hsz : (∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, (dU i j + dV i j)) ≤ sz)
    (hsmall : sz < 2 ^ (c.w - 2)) (hdx : dx + 1 < c.S) (hdy : dy + 1 < c.S) :
    (⟨U, V, s, dx, dy, dt, sz, o⟩ : XM).Good c := by
  refine ⟨by rw [hU]; exact pack_box c hdU, by rw [hV]; exact pack_box c hdV, ?_, ?_, ?_,
    hsmall, hdx, hdy⟩
  · intro i j h; simp only at h; rw [hU, cf_poly_pack hdU] at h
    split_ifs at h with hij
    · exact sU i j hij.1 hij.2 h
    · exact absurd rfl h
  · intro i j h; simp only at h; rw [hV, cf_poly_pack hdV] at h
    split_ifs at h with hij
    · exact sV i j hij.1 hij.2 h
    · exact absurd rfl h
  · simp only
    rw [hU, hV, eq_ofFun (poly_boxSupp c (pack c dU)), eq_ofFun (poly_boxSupp c (pack c dV)),
      dsum_ofFun, dsum_ofFun, ← Finset.sum_add_distrib]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_)) hsz
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [cf_poly_pack hdU, cf_poly_pack hdV, ite_eq_left ⟨Finset.mem_range.mp hi, Finset.mem_range.mp hj⟩,
      ite_eq_left ⟨Finset.mem_range.mp hi, Finset.mem_range.mp hj⟩]

theorem val_pack {c : Config} {m : XM} {dU dV : ℕ → ℕ → ℕ} (hU : m.U = pack c dU)
    (hV : m.V = pack c dV) (hdU : ∀ i j, dU i j < c.b) (hdV : ∀ i j, dV i j < c.b) {q : Bivar}
    (hq : ∀ i j, (q.coeff i).coeff j = if i < c.S ∧ j < c.S then (dU i j : ℚ) - dV i j else 0) :
    m.val c = q := by
  ext i j
  rw [val, Polynomial.coeff_sub, Polynomial.coeff_sub, coeff_mapQ, coeff_mapQ, hU, hV,
    cf_poly_pack hdU, cf_poly_pack hdV, hq]
  split_ifs <;> simp

theorem coeff_scalar_mul (r : ℚ) (p : Bivar) (i j : ℕ) :
    ((scalar r * p).coeff i).coeff j = r * (p.coeff i).coeff j := by
  simp [scalar, Polynomial.coeff_C_mul]

/-- The coefficients of a model with a good invariant. -/
theorem coeff_val {c : Config} {m : XM} (_g : m.Good c) (i j : ℕ) :
    ((m.val c).coeff i).coeff j =
      if i < c.S ∧ j < c.S then (coeffs c m.U i j : ℚ) - coeffs c m.V i j else 0 := by
  rw [val, Polynomial.coeff_sub, Polynomial.coeff_sub, coeff_mapQ, coeff_mapQ, cf_poly, cf_poly]
  split_ifs <;> simp [PackedModels.coeffs]

/-- The constant term of the numerator. -/
def const0 (c : Config) (m : XM) : ℤ := ((m.U % c.b : ℕ) : ℤ) - ((m.V % c.b : ℕ) : ℤ)

theorem const0_spec {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) (hok : m.ok = true)
    (hs : m.s ≠ 0) : (p.coeff 0).coeff 0 = (const0 c m : ℚ) / m.s := by
  obtain ⟨g, v⟩ := hm hok
  have h := coeff_val g 0 0
  rw [v, coeff_scalar_mul, ite_eq_left ⟨c.S_pos, c.S_pos⟩] at h
  have hs' : (m.s : ℚ) ≠ 0 := by exact_mod_cast hs
  have hd : ∀ N, PackedModels.coeffs c N 0 0 = N % c.b := fun N => by
    simp [PackedModels.coeffs, digit, Config.b]
  rw [hd, hd] at h
  rw [const0, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, eq_div_iff hs', mul_comm, h]

/-- The row `k`, as a polynomial in `y`. -/
def rowSlice (c : Config) (m : XM) (k : ℕ) : XM :=
  ⟨(m.U >>> (c.w * (c.S * k))) &&& rowMask c, (m.V >>> (c.w * (c.S * k))) &&& rowMask c, m.s, 0,
    min m.dy (m.dt - k), min m.dy (m.dt - k), m.sz, m.ok && Nat.blt k c.S && Nat.ble 1 c.w⟩

theorem rep_rowSlice {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) (k : ℕ) :
    (rowSlice c m k).Rep c (C (p.coeff k)) := by
  intro hok
  simp only [rowSlice, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hok
  obtain ⟨⟨hok, hk⟩, hw⟩ := hok
  obtain ⟨g, v⟩ := hm hok
  have hdU : ∀ i j, (if i = 0 then coeffs c m.U k j else 0) < c.b := fun i j => by
    split_ifs; exacts [coeffs_lt c _ _ _, c.b_pos]
  have hdV : ∀ i j, (if i = 0 then coeffs c m.V k j else 0) < c.b := fun i j => by
    split_ifs; exacts [coeffs_lt c _ _ _, c.b_pos]
  have eU := rowSlice_eq (c := c) (by omega) m.U hk
  have eV := rowSlice_eq (c := c) (by omega) m.V hk
  have cfk : ∀ N j, j < c.S → coeffs c N k j = cf (poly c N) k j := fun N j hj => by
    rw [cf_poly, ite_eq_left ⟨hk, hj⟩]; rfl
  have supp : ∀ (N : ℕ), Supp (poly c N) m.dx m.dy m.dt → ∀ i j, i < c.S → j < c.S →
      (if i = 0 then coeffs c N k j else 0) ≠ 0 →
        i ≤ 0 ∧ j ≤ min m.dy (m.dt - k) ∧ i + j ≤ min m.dy (m.dt - k) := by
    intro N hN i j _ hj h
    split_ifs at h with hi
    · rw [cfk N j hj] at h
      have := hN k j h
      omega
    · exact absurd rfl h
  have hsum : ∀ N, (∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S,
      (if i = 0 then coeffs c N k j else 0)) ≤ dsum (poly c N) := fun N => by
    rw [eq_ofFun (poly_boxSupp c N), dsum_ofFun]
    rw [Finset.sum_eq_single 0 (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_range.mpr c.S_pos) h)]
    simp only [ite_true]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun j hj => cfk N j (Finset.mem_range.mp hj)))
      (Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range c.S, cf (poly c N) i j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hk))
  refine ⟨good_pack _ eU eV hdU hdV (supp _ g.suppU) (supp _ g.suppV) ?_ g.small
    (by have := c.S_pos; have := g.dxS; omega) (by have := g.dyS; omega), ?_⟩
  · simp only [Finset.sum_add_distrib]; have := hsum m.U; have := hsum m.V; have := g.size; omega
  · apply val_pack eU eV hdU hdV
    intro i j
    rw [coeff_scalar_mul, Polynomial.coeff_C]
    have hv := congrArg (fun q : Bivar => (q.coeff k).coeff j) v
    simp only [coeff_scalar_mul] at hv
    rw [coeff_val g] at hv
    show (m.s : ℚ) * _ = _
    by_cases hi : i = 0
    · subst hi
      simp only [ite_true]
      by_cases hj : j < c.S
      · rw [ite_eq_left ⟨c.S_pos, hj⟩]; rw [ite_eq_left ⟨hk, hj⟩] at hv; rw [hv]
      · rw [ite_eq_right (fun h => hj h.2)]; rw [ite_eq_right (fun h => hj h.2)] at hv; rw [hv]
    · simp [hi]

/-- The column `k`, as a polynomial in `x`. -/
def colSlice (c : Config) (m : XM) (k : ℕ) : XM :=
  ⟨(m.U >>> (c.w * k)) &&& col0Mask c, (m.V >>> (c.w * k)) &&& col0Mask c, m.s,
    min m.dx (m.dt - k), 0, min m.dx (m.dt - k), m.sz, m.ok && Nat.blt k c.S && Nat.ble 1 c.w⟩

theorem rep_colSlice {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) (k : ℕ) :
    (colSlice c m k).Rep c (colPoly p k) := by
  intro hok
  simp only [colSlice, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hok
  obtain ⟨⟨hok, hk⟩, hw⟩ := hok
  obtain ⟨g, v⟩ := hm hok
  have hdU : ∀ i j, (if j = 0 then coeffs c m.U i k else 0) < c.b := fun i j => by
    split_ifs; exacts [coeffs_lt c _ _ _, c.b_pos]
  have hdV : ∀ i j, (if j = 0 then coeffs c m.V i k else 0) < c.b := fun i j => by
    split_ifs; exacts [coeffs_lt c _ _ _, c.b_pos]
  have eU := colSlice_eq (c := c) (by omega) m.U hk
  have eV := colSlice_eq (c := c) (by omega) m.V hk
  have cfk : ∀ N i, i < c.S → coeffs c N i k = cf (poly c N) i k := fun N i hi => by
    rw [cf_poly, ite_eq_left ⟨hi, hk⟩]; rfl
  have supp : ∀ (N : ℕ), Supp (poly c N) m.dx m.dy m.dt → ∀ i j, i < c.S → j < c.S →
      (if j = 0 then coeffs c N i k else 0) ≠ 0 →
        i ≤ min m.dx (m.dt - k) ∧ j ≤ 0 ∧ i + j ≤ min m.dx (m.dt - k) := by
    intro N hN i j hi _ h
    split_ifs at h with hj
    · rw [cfk N i hi] at h
      have := hN i k h
      omega
    · exact absurd rfl h
  have hsum : ∀ N, (∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S,
      (if j = 0 then coeffs c N i k else 0)) ≤ dsum (poly c N) := fun N => by
    rw [eq_ofFun (poly_boxSupp c N), dsum_ofFun]
    apply Finset.sum_le_sum; intro i hi
    rw [Finset.sum_eq_single 0 (fun j _ hj => by simp [hj])
      (fun h => absurd (Finset.mem_range.mpr c.S_pos) h)]
    simp only [ite_true]
    rw [cfk N i (Finset.mem_range.mp hi)]
    exact Finset.single_le_sum (f := fun j => cf (poly c N) i j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hk)
  refine ⟨good_pack _ eU eV hdU hdV (supp _ g.suppU) (supp _ g.suppV) ?_ g.small
    (by have := g.dxS; omega) (by have := c.S_pos; have := g.dyS; omega), ?_⟩
  · simp only [Finset.sum_add_distrib]; have := hsum m.U; have := hsum m.V; have := g.size; omega
  · apply val_pack eU eV hdU hdV
    intro i j
    rw [coeff_scalar_mul, coeff_colPoly, Polynomial.coeff_C]
    have hv := congrArg (fun q : Bivar => (q.coeff i).coeff k) v
    simp only [coeff_scalar_mul] at hv
    rw [coeff_val g] at hv
    show (m.s : ℚ) * _ = _
    by_cases hj : j = 0
    · subst hj
      simp only [ite_true]
      by_cases hi : i < c.S
      · rw [ite_eq_left ⟨hi, c.S_pos⟩]; rw [ite_eq_left ⟨hi, hk⟩] at hv; rw [hv]
      · rw [ite_eq_right (fun h => hi h.1)]; rw [ite_eq_right (fun h => hi h.1)] at hv; rw [hv]
    · simp [hj]

/-- The truncation to total degree `≤ T`. -/
def trunc (c : Config) (m : XM) (T : ℕ) : XM :=
  ⟨m.U &&& triMaskT c T, m.V &&& triMaskT c T, m.s, min m.dx T, min m.dy T, min m.dt T, m.sz,
    m.ok && Nat.blt T c.S && Nat.ble 1 c.w⟩

theorem rep_trunc {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) (T : ℕ) :
    (trunc c m T).Rep c (truncTot T p) := by
  intro hok
  simp only [trunc, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hok
  obtain ⟨⟨hok, hT⟩, hw⟩ := hok
  obtain ⟨g, v⟩ := hm hok
  have hdU : ∀ i j, (if i + j ≤ T then coeffs c m.U i j else 0) < c.b := fun i j => by
    split_ifs; exacts [coeffs_lt c _ _ _, c.b_pos]
  have hdV : ∀ i j, (if i + j ≤ T then coeffs c m.V i j else 0) < c.b := fun i j => by
    split_ifs; exacts [coeffs_lt c _ _ _, c.b_pos]
  have eU := truncT_eq hw m.U hT
  have eV := truncT_eq hw m.V hT
  have cfij : ∀ N i j, i < c.S → j < c.S → cf (poly c N) i j = coeffs c N i j := fun N i j hi hj => by
    rw [cf_poly, ite_eq_left ⟨hi, hj⟩]; rfl
  have supp : ∀ (N : ℕ), Supp (poly c N) m.dx m.dy m.dt → ∀ i j, i < c.S → j < c.S →
      (if i + j ≤ T then coeffs c N i j else 0) ≠ 0 →
        i ≤ min m.dx T ∧ j ≤ min m.dy T ∧ i + j ≤ min m.dt T := by
    intro N hN i j hi hj h
    split_ifs at h with hij
    · have h' : cf (poly c N) i j ≠ 0 := by rw [cfij N i j hi hj]; exact h
      have := hN i j h'
      omega
    · exact absurd rfl h
  have hsum : ∀ N, (∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S,
      (if i + j ≤ T then coeffs c N i j else 0)) ≤ dsum (poly c N) := fun N => by
    rw [eq_ofFun (poly_boxSupp c N), dsum_ofFun]
    apply Finset.sum_le_sum; intro i hi; apply Finset.sum_le_sum; intro j hj
    rw [cfij N i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _
  refine ⟨good_pack _ eU eV hdU hdV (supp _ g.suppU) (supp _ g.suppV) ?_ g.small
    (by have := g.dxS; omega) (by have := g.dyS; omega), ?_⟩
  · simp only [Finset.sum_add_distrib]; have := hsum m.U; have := hsum m.V; have := g.size; omega
  · apply val_pack eU eV hdU hdV
    intro i j
    rw [coeff_scalar_mul, coeff_truncTot]
    have hv := congrArg (fun q : Bivar => (q.coeff i).coeff j) v
    simp only [coeff_scalar_mul] at hv
    rw [coeff_val g] at hv
    show (m.s : ℚ) * _ = _
    by_cases hij : i + j ≤ T
    · rw [ite_eq_left hij, ← hv]
      by_cases hb : i < c.S ∧ j < c.S
      · rw [ite_eq_left hb, ite_eq_left hb, ite_eq_left hij, ite_eq_left hij]
      · rw [ite_eq_right hb, ite_eq_right hb]
    · rw [ite_eq_right hij, mul_zero]
      by_cases hb : i < c.S ∧ j < c.S
      · rw [ite_eq_left hb, ite_eq_right hij, ite_eq_right hij]; simp
      · rw [ite_eq_right hb]

/-! ### Horner's rule over slices -/

/-- `∑ e · x ^ ax · y ^ ay` over a list of terms. -/
def polyF : List (ℤ × ℕ × ℕ) → Bivar
  | [] => 0
  | t :: F => scalar (t.1 : ℚ) * (X ^ t.2.1 * (C X) ^ t.2.2) + polyF F

/-- `F · a`, for a nonempty list `F` of terms. -/
def mulF (c : Config) (a : XM) : List (ℤ × ℕ × ℕ) → XM
  | [] => ofInt c 0 1
  | [t] => monoMul c a t.1 t.2.1 t.2.2
  | t :: F => add c (monoMul c a t.1 t.2.1 t.2.2) (mulF c a F)

theorem rep_mulF {c : Config} {a : XM} {p : Bivar} (ha : a.Rep c p) :
    ∀ F : List (ℤ × ℕ × ℕ), F ≠ [] → (mulF c a F).Rep c (polyF F * p)
  | [], h => absurd rfl h
  | [t], _ => by simpa [mulF, polyF] using rep_monoMul ha t.1 t.2.1 t.2.2
  | t :: t' :: F, _ => by
    have h := rep_add (rep_monoMul ha t.1 t.2.1 t.2.2) (rep_mulF ha (t' :: F) (by simp))
    have e : mulF c a (t :: t' :: F) = add c (monoMul c a t.1 t.2.1 t.2.2) (mulF c a (t' :: F)) := rfl
    rw [e]
    convert h using 1
    simp only [polyF]; ring

/-- Horner's rule `acc_j = q ^ (n - j) · s_j + F · acc_{j+1}` from `acc_n = s_n`, `t` steps. -/
def horner (c : Config) (sl : ℕ → XM) (F : List (ℤ × ℕ × ℕ)) (q n : ℕ) : ℕ → XM
  | 0 => sl n
  | t + 1 => add c (mulQ c (sl (n - (t + 1))) ((q ^ (t + 1) : ℕ) : ℤ) 1)
      (mulF c (horner c sl F q n t) F)

/-- The value of `horner`. -/
def hornerVal (sp : ℕ → Bivar) (f : Bivar) (q n : ℕ) : ℕ → Bivar
  | 0 => sp n
  | t + 1 => scalar ((q : ℚ) ^ (t + 1)) * sp (n - (t + 1)) + f * hornerVal sp f q n t

theorem rep_horner {c : Config} {sl : ℕ → XM} {sp : ℕ → Bivar} (hs : ∀ k, (sl k).Rep c (sp k))
    {F : List (ℤ × ℕ × ℕ)} (hF : F ≠ []) (q n : ℕ) :
    ∀ t, (horner c sl F q n t).Rep c (hornerVal sp (polyF F) q n t)
  | 0 => hs n
  | t + 1 => by
    have h := rep_add (rep_mulQ (hs (n - (t + 1))) ((q ^ (t + 1) : ℕ) : ℤ) 1)
      (rep_mulF (rep_horner hs hF q n t) F hF)
    rw [horner, hornerVal]
    convert h using 2
    push_cast; ring_nf

theorem hornerVal_eq (sp : ℕ → Bivar) (f : Bivar) (q n : ℕ) :
    ∀ t, t ≤ n → hornerVal sp f q n t =
      ∑ i ∈ Finset.range (t + 1), scalar ((q : ℚ) ^ (t - i)) * f ^ i * sp (n - t + i)
  | 0, _ => by simp [hornerVal, scalar]
  | t + 1, ht => by
    rw [hornerVal, hornerVal_eq sp f q n t (by omega),
      Finset.sum_range_succ' (fun i => scalar ((q : ℚ) ^ (t + 1 - i)) * f ^ i * sp (n - (t + 1) + i)),
      Finset.mul_sum]
    simp only [pow_zero, mul_one, Nat.sub_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [show n - (t + 1) + (i + 1) = n - t + i by omega, show t + 1 - (i + 1) = t - i by omega,
      pow_succ]
    ring

/-! ### Degrees and the Horner transforms -/

theorem coeff_eq_zero_of_rep {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) (hok : m.ok = true)
    (hs : m.s ≠ 0) (i j : ℕ) (h : m.dx < i ∨ m.dy < j) : (p.coeff i).coeff j = 0 := by
  obtain ⟨g, v⟩ := hm hok
  have hv := congrArg (fun q : Bivar => (q.coeff i).coeff j) v
  simp only [coeff_scalar_mul] at hv
  rw [coeff_val g] at hv
  have hU : coeffs c m.U i j = 0 ∨ ¬ (i < c.S ∧ j < c.S) := by
    by_cases hij : i < c.S ∧ j < c.S
    · left; by_contra h0
      have := g.suppU i j (by rw [cf_poly, ite_eq_left hij]; exact h0); omega
    · right; exact hij
  have hV : coeffs c m.V i j = 0 ∨ ¬ (i < c.S ∧ j < c.S) := by
    by_cases hij : i < c.S ∧ j < c.S
    · left; by_contra h0
      have := g.suppV i j (by rw [cf_poly, ite_eq_left hij]; exact h0); omega
    · right; exact hij
  have hs' : (m.s : ℚ) ≠ 0 := by exact_mod_cast hs
  have h0 : (m.s : ℚ) * (p.coeff i).coeff j = 0 := by
    rw [← hv]
    split_ifs with hij
    · rcases hU with hU | hU
      · rcases hV with hV | hV
        · rw [hU, hV]; simp
        · exact absurd hij hV
      · exact absurd hij hU
    · rfl
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact absurd h1 hs'
  · exact h1

theorem natDegree_of_rep {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) (hok : m.ok = true)
    (hs : m.s ≠ 0) : p.natDegree ≤ m.dx := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro i hi
  ext j
  rw [Polynomial.coeff_zero]
  exact coeff_eq_zero_of_rep hm hok hs i j (Or.inl (by exact_mod_cast hi))

theorem natDegree_coeff_of_rep {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p)
    (hok : m.ok = true) (hs : m.s ≠ 0) (i : ℕ) : (p.coeff i).natDegree ≤ m.dy := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  exact coeff_eq_zero_of_rep hm hok hs i j (Or.inr (by exact_mod_cast hj))

/-- Horner's rule over the rows: `∑ q ^ (n - k) F ^ k p_k(y)`. -/
def rowsHorner (c : Config) (m : XM) (F : List (ℤ × ℕ × ℕ)) (q n : ℕ) : XM :=
  horner c (rowSlice c m) F q n n

/-- Horner's rule over the columns: `∑ q ^ (n - k) F ^ k p^k(x)`. -/
def colsHorner (c : Config) (m : XM) (F : List (ℤ × ℕ × ℕ)) (q n : ℕ) : XM :=
  horner c (colSlice c m) F q n n

theorem rep_rowsHorner {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p)
    {F : List (ℤ × ℕ × ℕ)} (hF : F ≠ []) (q n : ℕ) :
    (rowsHorner c m F q n).Rep c
      (∑ i ∈ Finset.range (n + 1), scalar ((q : ℚ) ^ (n - i)) * polyF F ^ i * C (p.coeff i)) := by
  have h := rep_horner (fun k => rep_rowSlice hm k) hF q n n
  rw [hornerVal_eq _ _ _ _ n le_rfl] at h
  unfold rowsHorner
  simpa only [Nat.sub_self, zero_add] using h

theorem rep_colsHorner {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p)
    {F : List (ℤ × ℕ × ℕ)} (hF : F ≠ []) (q n : ℕ) :
    (colsHorner c m F q n).Rep c
      (∑ i ∈ Finset.range (n + 1), scalar ((q : ℚ) ^ (n - i)) * polyF F ^ i * colPoly p i) := by
  have h := rep_horner (fun k => rep_colSlice hm k) hF q n n
  rw [hornerVal_eq _ _ _ _ n le_rfl] at h
  unfold colsHorner
  simpa only [Nat.sub_self, zero_add] using h

@[simp] theorem evaluate_polyF (x y : ℝ) : ∀ F : List (ℤ × ℕ × ℕ),
    evaluate x y (polyF F) = (F.map fun t => (t.1 : ℝ) * x ^ t.2.1 * y ^ t.2.2).sum
  | [] => by simp [polyF]
  | t :: F => by simp [polyF, evaluate_polyF x y F]; ring

/-! ### Changes of variables -/

/-- The scale times `k`, with an extra check. -/
def rescale (m : XM) (k : ℕ) (b : Bool) : XM := ⟨m.U, m.V, m.s * k, m.dx, m.dy, m.dt, m.sz, m.ok && b⟩

theorem rep_rescale {c : Config} {m : XM} {p : Bivar} {k : ℕ} {b : Bool}
    (h : m.ok = true → b = true → m.Rep c (scalar (k : ℚ) * p)) : (rescale m k b).Rep c p := by
  intro hok
  simp only [rescale, Bool.and_eq_true] at hok
  obtain ⟨g, v⟩ := h hok.1 hok.2 hok.1
  refine ⟨⟨g.boxU, g.boxV, g.suppU, g.suppV, g.size, g.small, g.dxS, g.dyS⟩, ?_⟩
  show m.val c = _
  rw [v, ← mul_assoc, ← scalar_mul, show (rescale m k b).s = m.s * k from rfl]
  push_cast; rfl

/-- `x ↦ F / q`. -/
def substX (c : Config) (m : XM) (F : List (ℤ × ℕ × ℕ)) (q : ℕ) : XM :=
  rescale (rowsHorner c m F q m.dx) (q ^ m.dx) (m.ok && Nat.blt 0 m.s && Nat.blt 0 q)

/-- `y ↦ F / q`. -/
def substY (c : Config) (m : XM) (F : List (ℤ × ℕ × ℕ)) (q : ℕ) : XM :=
  rescale (colsHorner c m F q m.dy) (q ^ m.dy) (m.ok && Nat.blt 0 m.s && Nat.blt 0 q)

theorem rep_substX {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) {F : List (ℤ × ℕ × ℕ)}
    (hF : F ≠ []) (q : ℕ) :
    (substX c m F q).Rep c (TwoVariablePolynomial.substitute (scalar (1 / (q : ℚ)) * polyF F) (C X) p) := by
  apply rep_rescale
  intro _ hb
  simp only [Bool.and_eq_true, Nat.blt_eq] at hb
  obtain ⟨⟨hok, hs⟩, hq⟩ := hb
  have h := rep_rowsHorner hm hF q m.dx
  rw [sum_rows_eq (by omega) (natDegree_of_rep hm hok (by omega))] at h
  push_cast; exact h

theorem rep_substY {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) {F : List (ℤ × ℕ × ℕ)}
    (hF : F ≠ []) (q : ℕ) :
    (substY c m F q).Rep c (TwoVariablePolynomial.substitute X (scalar (1 / (q : ℚ)) * polyF F) p) := by
  apply rep_rescale
  intro _ hb
  simp only [Bool.and_eq_true, Nat.blt_eq] at hb
  obtain ⟨⟨hok, hs⟩, hq⟩ := hb
  have h := rep_colsHorner hm hF q m.dy
  rw [sum_cols_eq (by omega) (natDegree_coeff_of_rep hm hok (by omega))] at h
  push_cast; exact h

/-- `x ↦ (n / d) (x + 1) / 2`. -/
def unitXM (c : Config) (m : XM) (n d : ℕ) : XM := substX c m [((n : ℤ), 0, 0), ((n : ℤ), 1, 0)] (2 * d)
/-- `y ↦ (n / d) (y + 1) / 2`. -/
def unitYM (c : Config) (m : XM) (n d : ℕ) : XM := substY c m [((n : ℤ), 0, 0), ((n : ℤ), 0, 1)] (2 * d)

/-- The triangle `0 ≤ y ≤ x ≤ d`... as `(d u (1 - v), d u v)`. -/
def triangleM (c : Config) (m : XM) (dn dd : ℕ) : XM :=
  unitYM c (unitXM c (substY c (substX c m [(1, 1, 0), (-1, 0, 1)] 1) [(1, 1, 1)] 1) dn dd) 1 1

/-- The rectangle `[0, a] × [0, b]`. -/
def rectangleM (c : Config) (m : XM) (an ad bn bd : ℕ) : XM :=
  unitYM c (unitXM c m an ad) bn bd

/-- The fan `(d u, (l + e d u) v)`. -/
def fanM (c : Config) (m : XM) (ln : ℤ) (ld : ℕ) (en : ℤ) (ed dn dd : ℕ) : XM :=
  unitYM c (unitXM c (substY c m [(ln * ed, 0, 1), (en * ld, 1, 1)] (ld * ed)) dn dd) 1 1

theorem rep_triangleM {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) {d : ℚ} {dn dd : ℕ}
    (hd : d = dn / dd) : (triangleM c m dn dd).Rep c (TwoVariablePolynomial.triangle d p) := by
  have h := rep_substY (rep_substX (rep_substY (rep_substX hm (F := [(1, 1, 0), (-1, 0, 1)])
    (by simp) 1) (F := [(1, 1, 1)]) (by simp) 1) (F := [((dn : ℤ), 0, 0), ((dn : ℤ), 1, 0)])
    (by simp) (2 * dd)) (F := [(((1 : ℕ) : ℤ), 0, 0), (((1 : ℕ) : ℤ), 0, 1)]) (by simp) (2 * 1)
  rw [substitute_comp, substitute_comp, substitute_comp] at h
  unfold triangleM unitYM unitXM TwoVariablePolynomial.triangle
  convert h using 3 <;>
    (apply eq_of_evaluate; intro x y; simp [TwoVariablePolynomial.unitX, TwoVariablePolynomial.unitY, hd]; ring)

theorem rep_rectangleM {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) {a b : ℚ} {an ad bn bd : ℕ}
    (ha : a = an / ad) (hb : b = bn / bd) : (rectangleM c m an ad bn bd).Rep c (TwoVariablePolynomial.rectangle a b p) := by
  have h := rep_substY (rep_substX hm (F := [((an : ℤ), 0, 0), ((an : ℤ), 1, 0)]) (by simp) (2 * ad))
    (F := [((bn : ℤ), 0, 0), ((bn : ℤ), 0, 1)]) (by simp) (2 * bd)
  rw [substitute_comp] at h
  unfold rectangleM unitYM unitXM TwoVariablePolynomial.rectangle
  convert h using 3 <;>
    (apply eq_of_evaluate; intro x y; simp [TwoVariablePolynomial.unitX, TwoVariablePolynomial.unitY, ha, hb]; ring)

theorem rep_fanM {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) {l e d : ℚ} {ln : ℤ}
    {ld : ℕ} {en : ℤ} {ed dn dd : ℕ} (hl : l = ln / ld) (he : e = en / ed) (hd : d = dn / dd)
    (hld : ld ≠ 0) (hed : ed ≠ 0) {f g : Bivar} (hf : ∀ x y : ℝ, evaluate x y f = d * ((x + 1) / 2))
    (hg : ∀ x y : ℝ, evaluate x y g = (l + e * (d * ((x + 1) / 2))) * ((y + 1) / 2)) :
    (fanM c m ln ld en ed dn dd).Rep c (TwoVariablePolynomial.substitute f g p) := by
  have h := rep_substY (rep_substX (rep_substY hm (F := [(ln * ed, 0, 1), (en * ld, 1, 1)]) (by simp)
    (ld * ed)) (F := [((dn : ℤ), 0, 0), ((dn : ℤ), 1, 0)]) (by simp) (2 * dd))
    (F := [(((1 : ℕ) : ℤ), 0, 0), (((1 : ℕ) : ℤ), 0, 1)]) (by simp) (2 * 1)
  rw [substitute_comp, substitute_comp] at h
  unfold fanM unitYM unitXM
  have hld' : (ld : ℝ) ≠ 0 := by exact_mod_cast hld
  have hed' : (ed : ℝ) ≠ 0 := by exact_mod_cast hed
  convert h using 3 <;>
    (apply eq_of_evaluate; intro x y; simp [hf, hg, hl, he, hd]; field_simp; ring)

theorem rep_trapezoidM {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) {l d : ℚ} {ln : ℤ}
    {ld dn dd : ℕ} (hl : l = ln / ld) (hd : d = dn / dd) (hld : ld ≠ 0) :
    (fanM c m ln ld 1 1 dn dd).Rep c (TwoVariablePolynomial.trapezoid l d p) :=
  rep_fanM hm hl (e := 1) (by simp) hd hld one_ne_zero
    (fun x y => by
      simp only [TwoVariablePolynomial.unitX, map_mul, map_add, evaluate_scalar, evaluate_X, map_one]
      push_cast; ring)
    (fun x y => by
      simp only [TwoVariablePolynomial.unitX, TwoVariablePolynomial.unitY, map_mul, map_add,
        evaluate_scalar, evaluate_X, evaluate_inner_X, map_one]
      push_cast; ring)

/-- The fan `(d u, (l - d u) v)` (the `RE` region). -/
theorem rep_fanNegM {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) {l d : ℚ} {ln : ℤ}
    {ld dn dd : ℕ} (hl : l = ln / ld) (hd : d = dn / dd) (hld : ld ≠ 0) :
    (fanM c m ln ld (-1) 1 dn dd).Rep c (TwoVariablePolynomial.substitute
      (scalar d * TwoVariablePolynomial.unitX)
      ((scalar l - scalar d * TwoVariablePolynomial.unitX) * TwoVariablePolynomial.unitY) p) :=
  rep_fanM hm hl (e := -1) (by simp) hd hld one_ne_zero
    (fun x y => by
      simp only [TwoVariablePolynomial.unitX, map_mul, map_add, evaluate_scalar, evaluate_X, map_one]
      push_cast; ring)
    (fun x y => by
      simp only [TwoVariablePolynomial.unitX, TwoVariablePolynomial.unitY, map_mul, map_add, map_sub,
        evaluate_scalar, evaluate_X, evaluate_inner_X, map_one]
      push_cast; ring)

/-! ### The final bound -/

/-- The two-dimensional Chebyshev coefficients of the numerator, normalized. -/
def chebFinal (c : Config) (m : XM) (D : ℕ) : ℕ × ℕ :=
  normBox c (chebXN c (chebYN c m.U D (D + 1)) D (D + 1)) (chebXN c (chebYN c m.V D (D + 1)) D (D + 1))

/-- The constant coefficient and the sum of all absolute values. -/
def finalParts (c : Config) (m : XM) (D : ℕ) : ℤ × ℤ :=
  let r := chebFinal c m D
  (((r.1 % c.b : ℕ) : ℤ) - ((r.2 % c.b : ℕ) : ℤ), ((r.1 % (c.b - 1) + r.2 % (c.b - 1) : ℕ) : ℤ))

/-- `4 ^ D · s · lower`. -/
def lowerZ (c : Config) (m : XM) (D : ℕ) : ℤ :=
  (finalParts c m D).1 + |(finalParts c m D).1| - (finalParts c m D).2
/-- `4 ^ D · s · upper`. -/
def upperZ (c : Config) (m : XM) (D : ℕ) : ℤ :=
  (finalParts c m D).1 - |(finalParts c m D).1| + (finalParts c m D).2

/-- The checks of the final bound. -/
def finalOk (c : Config) (m : XM) (D : ℕ) : Bool :=
  m.ok && Nat.blt 0 m.s && Nat.ble 2 c.w && Nat.blt (D + 1) c.S && Nat.ble m.dx D &&
    Nat.ble m.dy D && Nat.blt (16 ^ (D + 1) * m.sz) (2 ^ (c.w - 2))

theorem normBox_parts {c : Config} (hw : 2 ≤ c.w) {N₁ N₂ T : ℕ} (h1 : Box c N₁) (h2 : Box c N₂)
    (hs1 : dsum (poly c N₁) ≤ T) (hs2 : dsum (poly c N₂) ≤ T) (hT : T < 2 ^ (c.w - 2)) :
    (((normBox c N₁ N₂).1 % c.b : ℕ) : ℤ) - (((normBox c N₁ N₂).2 % c.b : ℕ) : ℤ) =
        (coeffs c N₁ 0 0 : ℤ) - coeffs c N₂ 0 0 ∧
      (((normBox c N₁ N₂).1 % (c.b - 1) + (normBox c N₁ N₂).2 % (c.b - 1) : ℕ) : ℤ) =
        ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, |(coeffs c N₁ i j : ℤ) - coeffs c N₂ i j| := by
  have hu := coeffs_lt_half h1 hs1 hT
  have hv := coeffs_lt_half h2 hs2 hT
  obtain ⟨e1, e2⟩ := normBox_spec hw h1 h2 hu hv
  have hb : ∀ i j, coeffs c N₁ i j - coeffs c N₂ i j < c.b := fun i j =>
    lt_of_le_of_lt (Nat.sub_le _ _) (coeffs_lt c _ i j)
  have hb' : ∀ i j, coeffs c N₂ i j - coeffs c N₁ i j < c.b := fun i j =>
    lt_of_le_of_lt (Nat.sub_le _ _) (coeffs_lt c _ i j)
  have hd : ∀ N, coeffs c N 0 0 = N % c.b := fun N => by
    simp [PackedModels.coeffs, digit, Config.b]
  have hbT : T < c.b - 1 := by
    have : 2 ^ (c.w - 2) * 4 = c.b := by
      unfold Config.b; rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    have : 1 ≤ 2 ^ (c.w - 2) := Nat.one_le_two_pow
    omega
  have hsum : ∀ (d : ℕ → ℕ → ℕ) (N : ℕ), (∀ i j, d i j ≤ coeffs c N i j) → dsum (poly c N) ≤ T →
      ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, d i j < c.b - 1 := by
    intro d N hdN hN
    refine lt_of_le_of_lt ?_ (hN.trans_lt hbT)
    rw [← dsumN_eq, dsumN]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hdN i j
  have m1 := mod_eq_dsumN (pack_box c hb) (by
    unfold Config.M; rw [dsumN_pack c hb]; exact hsum _ N₁ (fun i j => Nat.sub_le _ _) hs1)
  have m2 := mod_eq_dsumN (pack_box c hb') (by
    unfold Config.M; rw [dsumN_pack c hb']; exact hsum _ N₂ (fun i j => Nat.sub_le _ _) hs2)
  unfold Config.M at m1 m2
  rw [dsumN_pack c hb] at m1
  rw [dsumN_pack c hb'] at m2
  constructor
  · rw [e1, e2, ← hd, ← hd, coeffs_pack c hb c.S_pos c.S_pos, coeffs_pack c hb' c.S_pos c.S_pos]
    omega
  · rw [e1, e2, m1, m2]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases le_total (coeffs c N₁ i j) (coeffs c N₂ i j) with h | h
    · rw [abs_of_nonpos (by omega)]; omega
    · rw [abs_of_nonneg (by omega)]; omega

/-- The two Chebyshev stages on a packed numerator. -/
theorem chebN_eq {c : Config} (hw : 1 ≤ c.w) {N : ℕ} (hN : Box c N) {D : ℕ} (hD : D + 1 < c.S)
    (hb : 16 ^ (D + 1) * dsum (poly c N) < c.b) :
    chebXN c (chebYN c N D (D + 1)) D (D + 1) =
        evB c (chebXP c (chebYP c (poly c N) D (D + 1)) D (D + 1)) ∧
      Box c (evB c (chebXP c (chebYP c (poly c N) D (D + 1)) D (D + 1))) ∧
      poly c (evB c (chebXP c (chebYP c (poly c N) D (D + 1)) D (D + 1))) =
        chebXP c (chebYP c (poly c N) D (D + 1)) D (D + 1) ∧
      dsum (chebXP c (chebYP c (poly c N) D (D + 1)) D (D + 1)) ≤ 16 ^ (D + 1) * dsum (poly c N) := by
  have h16 : (16 : ℕ) ^ (D + 1) = 4 ^ (D + 1) * 4 ^ (D + 1) := by
    rw [← mul_pow]; norm_num
  have h4 : 4 ^ (D + 1) ≤ 16 ^ (D + 1) := Nat.pow_le_pow_left (by norm_num) _
  have hYd := dsum_chebYP (poly_boxSupp c N) hD (D + 1) le_rfl
  have hYb := chebYP_box (poly c N) hD (D + 1) le_rfl
  have hY4 : 4 ^ (D + 1) * dsum (chebYP c (poly c N) D (D + 1)) < c.b := by
    refine lt_of_le_of_lt ?_ hb
    rw [h16, mul_assoc]; exact Nat.mul_le_mul_left _ hYd
  have hYlt : ∀ i j, cf (chebYP c (poly c N) D (D + 1)) i j < c.b := fun i j =>
    (cf_le_dsum hYb i j).trans_lt (lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by positivity)) hY4)
  have hYbox := box_evB hYb hYlt
  have hYpoly := poly_evB hYb hYlt
  have hY := chebYN_eq hw hN hD (lt_of_le_of_lt (Nat.mul_le_mul_right _ h4) hb) (D + 1) le_rfl
  have hX := chebXN_eq hw hYbox hD (by rw [hYpoly]; exact hY4) (D + 1) le_rfl
  rw [hYpoly] at hX
  have hFb := chebXP_box (chebYP c (poly c N) D (D + 1)) hD (D + 1) le_rfl
  have hFd := dsum_chebXP hYb hD (D + 1) le_rfl
  have hFd' : dsum (chebXP c (chebYP c (poly c N) D (D + 1)) D (D + 1)) ≤ 16 ^ (D + 1) * dsum (poly c N) := by
    refine hFd.trans ?_
    rw [h16, mul_assoc]; exact Nat.mul_le_mul_left _ hYd
  have hFlt : ∀ i j, cf (chebXP c (chebYP c (poly c N) D (D + 1)) D (D + 1)) i j < c.b := fun i j =>
    (cf_le_dsum hFb i j).trans_lt (lt_of_le_of_lt hFd' hb |>.trans_le' (Nat.le_refl _))
  refine ⟨by rw [hY, hX], box_evB hFb hFlt, poly_evB hFb hFlt, hFd'⟩

theorem final_spec {c : Config} {m : XM} {q : Bivar} (hm : m.Rep c q) {D : ℕ}
    (h : finalOk c m D = true) :
    q = expansion D q ∧
      lower D (coefficient D q) = (lowerZ c m D : ℚ) / (4 ^ D * m.s) ∧
      TwoVariablePolynomial.upper D (coefficient D q) = (upperZ c m D : ℚ) / (4 ^ D * m.s) := by
  simp only [finalOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hok, hs⟩, hw⟩, hD⟩, hdx⟩, hdy⟩, hbound⟩ := h
  obtain ⟨g, v⟩ := hm hok
  have hs0 : m.s ≠ 0 := by omega
  have hsq : (m.s : ℚ) ≠ 0 := by exact_mod_cast hs0
  refine ⟨eq_expansion_of_degrees ((natDegree_of_rep hm hok hs0).trans hdx)
    (fun a => (natDegree_coeff_of_rep hm hok hs0 a).trans hdy), ?_⟩
  have hsz := g.size
  have hbw : 2 ^ (c.w - 2) ≤ c.b := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbU : 16 ^ (D + 1) * dsum (poly c m.U) < c.b :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) (lt_of_lt_of_le hbound hbw)
  have hbV : 16 ^ (D + 1) * dsum (poly c m.V) < c.b :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) (lt_of_lt_of_le hbound hbw)
  obtain ⟨eU, bU, pU, dU⟩ := chebN_eq (by omega) g.boxU hD hbU
  obtain ⟨eV, bV, pV, dV⟩ := chebN_eq (by omega) g.boxV hD hbV
  have parts := normBox_parts hw bU bV (T := 16 ^ (D + 1) * m.sz)
    (by rw [pU]; exact dU.trans (Nat.mul_le_mul_left _ (by omega)))
    (by rw [pV]; exact dV.trans (Nat.mul_le_mul_left _ (by omega))) hbound
  have hfin : chebFinal c m D = normBox c (evB c (chebXP c (chebYP c (poly c m.U) D (D + 1)) D (D + 1)))
      (evB c (chebXP c (chebYP c (poly c m.V) D (D + 1)) D (D + 1))) := by
    rw [chebFinal, eU, eV]
  -- the digits of the transforms
  have cU : ∀ i j, i < c.S → j < c.S → coeffs c (evB c (chebXP c (chebYP c (poly c m.U) D (D + 1)) D (D + 1))) i j =
      cf (chebXP c (chebYP c (poly c m.U) D (D + 1)) D (D + 1)) i j := fun i j hi hj => by
    conv_rhs => rw [← pU]
    rw [cf_poly, ite_eq_left ⟨hi, hj⟩]; rfl
  have cV : ∀ i j, i < c.S → j < c.S → coeffs c (evB c (chebXP c (chebYP c (poly c m.V) D (D + 1)) D (D + 1))) i j =
      cf (chebXP c (chebYP c (poly c m.V) D (D + 1)) D (D + 1)) i j := fun i j hi hj => by
    conv_rhs => rw [← pV]
    rw [cf_poly, ite_eq_left ⟨hi, hj⟩]; rfl
  set FU := chebXP c (chebYP c (poly c m.U) D (D + 1)) D (D + 1) with hFU
  set FV := chebXP c (chebYP c (poly c m.V) D (D + 1)) D (D + 1) with hFV
  set e : ℕ → ℕ → ℤ := fun i j => (cf FU i j : ℤ) - cf FV i j with he
  have hS := c.S_pos
  have p1 : (finalParts c m D).1 = e 0 0 := by
    rw [finalParts]; simp only; rw [hfin, parts.1, cU 0 0 hS hS, cV 0 0 hS hS]
  have p2 : (finalParts c m D).2 = ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, |e i j| := by
    rw [finalParts]; simp only; rw [hfin, parts.2]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [cU i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj),
      cV i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]
  -- zero outside the square `[0, D]²`
  have zU : ∀ i j, (D + 1 ≤ i ∨ D + 1 ≤ j) → cf FU i j = 0 := by
    intro i j hij
    rcases hij with hi | hj
    · exact (chebXP_spec _ hD (D + 1) le_rfl).1 i j hi
    · exact chebXP_col_zero c _ D (fun i' => (chebYP_spec _ hD (D + 1) le_rfl).1 i' j hj) (D + 1) i
  have zV : ∀ i j, (D + 1 ≤ i ∨ D + 1 ≤ j) → cf FV i j = 0 := by
    intro i j hij
    rcases hij with hi | hj
    · exact (chebXP_spec _ hD (D + 1) le_rfl).1 i j hi
    · exact chebXP_col_zero c _ D (fun i' => (chebYP_spec _ hD (D + 1) le_rfl).1 i' j hj) (D + 1) i
  have ze : ∀ i j, (D + 1 ≤ i ∨ D + 1 ≤ j) → e i j = 0 := fun i j hij => by
    simp only [he, zU i j hij, zV i j hij, Nat.cast_zero, sub_self]
  -- the coefficients
  have hq : ∀ a b, (q.coeff a).coeff b = ((cf (poly c m.U) a b : ℚ) - cf (poly c m.V) a b) / m.s := by
    intro a b
    have h := congrArg (fun p : Bivar => (p.coeff a).coeff b) v
    simp only [val, Polynomial.coeff_sub, coeff_mapQ, coeff_scalar_mul] at h
    rw [eq_div_iff hsq, mul_comm, ← h]
  have hK : (0 : ℚ) < 4 ^ D * m.s := by positivity
  have hcoef : ∀ i j, i < D + 1 → j < D + 1 → coefficient D q i j = (e i j : ℚ) / (4 ^ D * m.s) := by
    intro i j hi hj
    rw [coefficient_cheb hD _ _ hsq hq (by omega) (by omega)]
    simp only [he]; push_cast; ring
  have hsumq : ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1), |coefficient D q i j| =
      ((∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, |e i j| : ℤ) : ℚ) / (4 ^ D * m.s) := by
    have hsub : Finset.range (D + 1) ⊆ Finset.range c.S := Finset.range_subset_range.mpr (by omega)
    calc ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1), |coefficient D q i j|
        = ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1), |(e i j : ℚ)| / (4 ^ D * m.s) :=
          Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by
            rw [hcoef i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj), abs_div, abs_of_pos hK]
      _ = ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, |(e i j : ℚ)| / (4 ^ D * m.s) := by
          rw [Finset.sum_subset hsub (fun i _ hi => by
            rw [Finset.mem_range, not_lt] at hi
            exact Finset.sum_eq_zero fun j _ => by rw [ze i j (Or.inl hi)]; simp)]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_subset hsub (fun j _ hj => ?_)
          rw [Finset.mem_range, not_lt] at hj
          rw [ze i j (Or.inr hj)]; simp
      _ = _ := by
          push_cast
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => (Finset.sum_div _ _ _).symm
  have h00 := hcoef 0 0 (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rw [lower, norm_eq_sum, hsumq, h00, lowerZ, p1, p2, abs_div, abs_of_pos hK]
    push_cast; ring
  · rw [TwoVariablePolynomial.upper, norm_eq_sum, hsumq, h00, upperZ, p1, p2, abs_div, abs_of_pos hK]
    push_cast; ring

/-! ### Certificates -/

/-- The check of `r < lower` for `r = rn / rd`. -/
def lowerCheck (c : Config) (m : XM) (D : ℕ) (rn : ℤ) (rd : ℕ) : Bool :=
  finalOk c m D && Nat.blt 0 rd && decide (rn * ((4 ^ D * m.s : ℕ) : ℤ) < lowerZ c m D * (rd : ℤ))

/-- The check of `upper < r` for `r = rn / rd`. -/
def upperCheck (c : Config) (m : XM) (D : ℕ) (rn : ℤ) (rd : ℕ) : Bool :=
  finalOk c m D && Nat.blt 0 rd && decide (upperZ c m D * (rd : ℤ) < rn * ((4 ^ D * m.s : ℕ) : ℤ))

theorem finalOk_s {c : Config} {m : XM} {D : ℕ} (h : finalOk c m D = true) : 0 < m.s := by
  simp only [finalOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  exact h.1.1.1.1.1.2

theorem lower_certificate {c : Config} {m : XM} {q : Bivar} (hm : m.Rep c q) {D : ℕ} {rn : ℤ}
    {rd : ℕ} (h : lowerCheck c m D rn rd = true) {r : ℚ} (hr : r = rn / rd) :
    q = expansion D q ∧ r < lower D (coefficient D q) := by
  simp only [lowerCheck, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hf, hrd⟩, hlt⟩ := h
  obtain ⟨he, hl, -⟩ := final_spec hm hf
  have hs := finalOk_s hf
  refine ⟨he, ?_⟩
  rw [hl, hr, div_lt_div_iff₀ (by exact_mod_cast hrd) (by positivity)]
  exact_mod_cast hlt

theorem upper_certificate {c : Config} {m : XM} {q : Bivar} (hm : m.Rep c q) {D : ℕ} {rn : ℤ}
    {rd : ℕ} (h : upperCheck c m D rn rd = true) {r : ℚ} (hr : r = rn / rd) :
    q = expansion D q ∧ TwoVariablePolynomial.upper D (coefficient D q) < r := by
  simp only [upperCheck, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hf, hrd⟩, hlt⟩ := h
  obtain ⟨he, -, hu⟩ := final_spec hm hf
  have hs := finalOk_s hf
  refine ⟨he, ?_⟩
  rw [hu, hr, div_lt_div_iff₀ (by positivity) (by exact_mod_cast hrd)]
  exact_mod_cast hlt

/-! ### Literals -/

theorem rep_lit (c : Config) {r : ℚ} {n : ℤ} {s : ℕ} (h : r = n / s) : (ofInt c n s).Rep c (scalar r) :=
  h ▸ rep_ofInt c n s

theorem rep_one (c : Config) : (ofInt c 1 1).Rep c 1 := by
  have h := rep_ofInt c 1 1
  simpa [scalar] using h

/-! ### Guards, quotients, derivatives, cubic masses and lifts -/

/-- An extra check. -/
def guard (m : XM) (b : Bool) : XM := ⟨m.U, m.V, m.s, m.dx, m.dy, m.dt, m.sz, m.ok && b⟩

theorem rep_guard {c : Config} {m : XM} {p : Bivar} {b : Bool}
    (h : m.ok = true → b = true → m.Rep c p) : (guard m b).Rep c p := by
  intro hok
  simp only [guard, Bool.and_eq_true] at hok
  obtain ⟨g, v⟩ := h hok.1 hok.2 hok.1
  exact ⟨⟨g.boxU, g.boxV, g.suppU, g.suppV, g.size, g.small, g.dxS, g.dyS⟩, v⟩

theorem rep_mulQ' {c : Config} {a : XM} {p : Bivar} (ha : a.Rep c p) {r : ℚ} {n : ℤ} {d : ℕ}
    (h : r = n / d) : (mulQ c a n d).Rep c (scalar r * p) := h ▸ rep_mulQ ha n d

theorem rep_zero (c : Config) : (ofInt c 0 1).Rep c 0 := by
  have h := rep_ofInt c 0 1
  simpa [scalar] using h

/-- A model given by two natural polynomials of the box. -/
theorem good_evB {c : Config} {PU PV : NB} {U V s dx dy dt sz : ℕ} (o : Bool)
    (eU : U = evB c PU) (eV : V = evB c PV) (hU : BoxSupp c PU) (hV : BoxSupp c PV)
    (sU : Supp PU dx dy dt) (sV : Supp PV dx dy dt) (hsz : dsum PU + dsum PV ≤ sz)
    (hsmall : sz < 2 ^ (c.w - 2)) (hdx : dx + 1 < c.S) (hdy : dy + 1 < c.S) :
    (⟨U, V, s, dx, dy, dt, sz, o⟩ : XM).Good c ∧ poly c U = PU ∧ poly c V = PV := by
  have hb := small_lt_b c hsmall
  have lU : ∀ i j, cf PU i j < c.b := fun i j => (cf_le_dsum hU i j).trans_lt (by omega)
  have lV : ∀ i j, cf PV i j < c.b := fun i j => (cf_le_dsum hV i j).trans_lt (by omega)
  have pU := poly_evB hU lU
  have pV := poly_evB hV lV
  subst eU eV
  refine ⟨⟨box_evB hU lU, box_evB hV lV, ?_, ?_, ?_, hsmall, hdx, hdy⟩, pU, pV⟩
  · show Supp (poly c (evB c PU)) dx dy dt
    rw [pU]; exact sU
  · show Supp (poly c (evB c PV)) dx dy dt
    rw [pV]; exact sV
  · show dsum (poly c (evB c PU)) + dsum (poly c (evB c PV)) ≤ sz
    rw [pU, pV]; exact hsz

/-- `divY p`: the columns shifted down by one. -/
def divYM (c : Config) (m : XM) : XM :=
  ⟨dropYN c m.U, dropYN c m.V, m.s, m.dx, m.dy - 1, m.dt - 1, m.sz, m.ok && Nat.ble 1 c.w⟩

theorem rep_divYM {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) :
    (divYM c m).Rep c (TwoVariablePolynomial.divY p) := by
  intro hok
  simp only [divYM, Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨hok, hw⟩ := hok
  obtain ⟨g, v⟩ := hm hok
  have sd : ∀ N, Supp (poly c N) m.dx m.dy m.dt →
      Supp (dropY c (poly c N)) m.dx (m.dy - 1) (m.dt - 1) := by
    intro N hN i j h
    rw [dropY, cf_ofFun] at h
    split_ifs at h
    · have := hN i (j + 1) h; omega
    · exact absurd rfl h
  have dsU := dsum_dropY_le (poly_boxSupp c m.U)
  have dsV := dsum_dropY_le (poly_boxSupp c m.V)
  obtain ⟨gd, pU, pV⟩ := good_evB (s := m.s) (sz := m.sz) (m.ok && Nat.ble 1 c.w)
    (dropYN_eq hw g.boxU) (dropYN_eq hw g.boxV) (boxSupp_ofFun _ _) (boxSupp_ofFun _ _)
    (sd _ g.suppU) (sd _ g.suppV) (by have := g.size; omega) g.small (by have := g.dxS; omega)
    (by have := g.dyS; omega)
  refine ⟨gd, ?_⟩
  show mapQ (poly c (dropYN c m.U)) - mapQ (poly c (dropYN c m.V)) = _
  rw [pU, pV]
  ext i j
  have hv := congrArg (fun q : Bivar => (q.coeff i).coeff (j + 1)) v
  simp only [val, Polynomial.coeff_sub, coeff_mapQ, coeff_scalar_mul] at hv
  rw [Polynomial.coeff_sub, Polynomial.coeff_sub, coeff_mapQ, coeff_mapQ, coeff_scalar_mul,
    coeff_divY, show (divYM c m).s = m.s from rfl, ← hv]
  simp only [dropY, cf_ofFun]
  split_ifs with h
  · rfl
  · have z : ∀ N, cf (poly c N) i (j + 1) = 0 := fun N => by
      by_contra h0
      have := poly_boxSupp c N i (j + 1) h0
      exact h ⟨this.1, by omega⟩
    rw [z, z]

/-- `divX p`: the rows shifted down by one. -/
def divXM (c : Config) (m : XM) : XM :=
  ⟨dropXN c m.U, dropXN c m.V, m.s, m.dx - 1, m.dy, m.dt - 1, m.sz, m.ok⟩

theorem rep_divXM {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) :
    (divXM c m).Rep c p.divX := by
  intro hok
  obtain ⟨g, v⟩ := hm hok
  have sd : ∀ N, Supp (poly c N) m.dx m.dy m.dt →
      Supp (dropX c (poly c N)) (m.dx - 1) m.dy (m.dt - 1) := by
    intro N hN i j h
    rw [dropX, cf_ofFun] at h
    split_ifs at h
    · have := hN (i + 1) j h; omega
    · exact absurd rfl h
  have dsU := dsum_dropX_le (poly_boxSupp c m.U)
  have dsV := dsum_dropX_le (poly_boxSupp c m.V)
  obtain ⟨gd, pU, pV⟩ := good_evB (s := m.s) (sz := m.sz) m.ok
    (dropXN_eq g.boxU) (dropXN_eq g.boxV) (boxSupp_ofFun _ _) (boxSupp_ofFun _ _)
    (sd _ g.suppU) (sd _ g.suppV) (by have := g.size; omega) g.small (by have := g.dxS; omega)
    (by have := g.dyS; omega)
  refine ⟨gd, ?_⟩
  show mapQ (poly c (dropXN c m.U)) - mapQ (poly c (dropXN c m.V)) = _
  rw [pU, pV]
  ext i j
  have hv := congrArg (fun q : Bivar => (q.coeff (i + 1)).coeff j) v
  simp only [val, Polynomial.coeff_sub, coeff_mapQ, coeff_scalar_mul] at hv
  rw [Polynomial.coeff_sub, Polynomial.coeff_sub, coeff_mapQ, coeff_mapQ, coeff_scalar_mul,
    Polynomial.coeff_divX, show (divXM c m).s = m.s from rfl, ← hv]
  simp only [dropX, cf_ofFun]
  split_ifs with h
  · rfl
  · have z : ∀ N, cf (poly c N) (i + 1) j = 0 := fun N => by
      by_contra h0
      have := poly_boxSupp c N (i + 1) j h0
      exact h ⟨by omega, this.2⟩
    rw [z, z]

/-- `∑_{k < n} (k + 1) y ^ k p^{(k + 1)}(x)`. -/
def derivYAux (c : Config) (m : XM) : ℕ → XM
  | 0 => ofInt c 0 1
  | k + 1 => add c (derivYAux c m k) (monoMul c (colSlice c m (k + 1)) ((k + 1 : ℕ) : ℤ) 0 k)

theorem rep_derivYAux {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) :
    ∀ n, (derivYAux c m n).Rep c (∑ k ∈ Finset.range n,
      scalar ((((k + 1 : ℕ) : ℤ)) : ℚ) * (X ^ 0 * (C X) ^ k) * colPoly p (k + 1))
  | 0 => by rw [Finset.sum_range_zero]; exact rep_zero c
  | n + 1 => by
    rw [Finset.sum_range_succ]
    exact rep_add (rep_derivYAux hm n) (rep_monoMul (rep_colSlice hm (n + 1)) _ 0 n)

/-- `∂_y p`. -/
def derivYM (c : Config) (m : XM) : XM := guard (derivYAux c m m.dy) (m.ok && Nat.blt 0 m.s)

theorem rep_derivYM {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) :
    (derivYM c m).Rep c (TwoVariablePolynomial.derivativeY p) := by
  apply rep_guard
  intro _ hb
  simp only [Bool.and_eq_true, Nat.blt_eq] at hb
  rw [derivativeY_eq_sum (natDegree_coeff_of_rep hm hb.1 (by omega))]
  exact rep_derivYAux hm _

/-- `∑_{k < n} (k + 1) x ^ k p_{k + 1}(y)`. -/
def derivXAux (c : Config) (m : XM) : ℕ → XM
  | 0 => ofInt c 0 1
  | k + 1 => add c (derivXAux c m k) (monoMul c (rowSlice c m (k + 1)) ((k + 1 : ℕ) : ℤ) k 0)

theorem rep_derivXAux {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) :
    ∀ n, (derivXAux c m n).Rep c (∑ k ∈ Finset.range n,
      scalar ((((k + 1 : ℕ) : ℤ)) : ℚ) * (X ^ k * (C X) ^ 0) * C (p.coeff (k + 1)))
  | 0 => by rw [Finset.sum_range_zero]; exact rep_zero c
  | n + 1 => by
    rw [Finset.sum_range_succ]
    exact rep_add (rep_derivXAux hm n) (rep_monoMul (rep_rowSlice hm (n + 1)) _ n 0)

/-- `∂_x p`. -/
def derivXM (c : Config) (m : XM) : XM := guard (derivXAux c m m.dx) (m.ok && Nat.blt 0 m.s)

theorem rep_derivXM {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) :
    (derivXM c m).Rep c (Polynomial.derivative p) := by
  apply rep_guard
  intro _ hb
  simp only [Bool.and_eq_true, Nat.blt_eq] at hb
  rw [derivativeX_eq_sum (natDegree_of_rep hm hb.1 (by omega))]
  exact rep_derivXAux hm _

/-- The relative deviation `w = (T₃ p - p₀₀) / p₀₀` of a cubic mass. -/
def massDevM (c : Config) (m : XM) : XM :=
  mulQ c (sub c (trunc c m 3) (ofInt c (const0 c m) m.s))
    (if 0 ≤ const0 c m then (m.s : ℤ) else -(m.s : ℤ)) (const0 c m).natAbs

/-- `cubicMass (ρn / ρd) p`. -/
def cubicMassM (c : Config) (ρn : ℤ) (ρd : ℕ) (m : XM) : XM :=
  guard (mulQ c (trunc c (add c (sub c (add c (ofInt c 1 1) (mulQ c (massDevM c m) 1 2))
    (mulQ c (pow c (massDevM c m) 2) 1 8)) (mulQ c (pow c (massDevM c m) 3) 1 16)) 3) ρn ρd)
    (m.ok && Nat.blt 0 m.s && decide (const0 c m ≠ 0))

theorem rep_cubicMassM {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) {ρ : ℚ} {ρn : ℤ}
    {ρd : ℕ} (hρ : ρ = ρn / ρd) : (cubicMassM c ρn ρd m).Rep c (TwoVariablePolynomial.cubicMass ρ p) := by
  apply rep_guard
  intro _ hb
  simp only [Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq] at hb
  obtain ⟨⟨hok, hs⟩, hk⟩ := hb
  have hc := const0_spec hm hok (by omega)
  have hsq : (m.s : ℚ) ≠ 0 := by exact_mod_cast (show m.s ≠ 0 by omega)
  have hkq : (const0 c m : ℚ) ≠ 0 := by exact_mod_cast hk
  have hW : (massDevM c m).Rep c (scalar (1 / TwoVariablePolynomial.constant p) *
      (TwoVariablePolynomial.truncate3 p - scalar (TwoVariablePolynomial.constant p))) := by
    rw [truncate3_eq, TwoVariablePolynomial.constant, hc]
    refine rep_mulQ' (rep_sub (rep_trunc hm 3) (rep_ofInt c _ _)) ?_
    have hd : (((const0 c m).natAbs : ℕ) : ℚ) = |(const0 c m : ℚ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [hd]
    split_ifs with h0
    · rw [abs_of_nonneg (by exact_mod_cast h0)]; push_cast; field_simp
    · rw [abs_of_neg (by exact_mod_cast lt_of_not_ge h0)]; push_cast; field_simp
  rw [TwoVariablePolynomial.cubicMass, truncate3_eq]
  exact rep_mulQ' (rep_trunc (rep_add (rep_sub (rep_add (rep_one c) (rep_mulQ' hW (by norm_num)))
    (rep_mulQ' (rep_pow hW 2) (by norm_num))) (rep_mulQ' (rep_pow hW 3) (by norm_num))) 3) hρ

/-- The univariate polynomial `∑ (n_k / d_k) x ^ k`. -/
def uniQ : List (ℤ × ℕ) → ℚ[X]
  | [] => 0
  | t :: L => C ((t.1 : ℚ) / t.2) + X * uniQ L

/-- `q(u)` by Horner's rule, for `q = uniQ L`. -/
def liftM (c : Config) (u : XM) : List (ℤ × ℕ) → XM
  | [] => ofInt c 0 1
  | [t] => ofInt c t.1 t.2
  | t :: t' :: L => add c (ofInt c t.1 t.2) (mul c (liftM c u (t' :: L)) u)

theorem rep_liftM {c : Config} {u : XM} {f : Bivar} (hu : u.Rep c f) :
    ∀ L, (liftM c u L).Rep c (TwoVariablePolynomial.lift f (uniQ L))
  | [] => by simpa [liftM, uniQ] using rep_zero c
  | [t] => by simpa [liftM, uniQ, lift_C] using rep_ofInt c t.1 t.2
  | t :: t' :: L => by
    have h := rep_add (rep_ofInt c t.1 t.2) (rep_mul (rep_liftM hu (t' :: L)) hu)
    have e : liftM c u (t :: t' :: L) = add c (ofInt c t.1 t.2) (mul c (liftM c u (t' :: L)) u) := rfl
    rw [e]
    convert h using 1
    rw [uniQ, map_add, map_mul, lift_C, lift_X, mul_comm f]

/-- The Taylor polynomials of `cos` and `sin` of `GlobalGA.PositiveTD.Certificate`. -/
def C10L : List (ℤ × ℕ) :=
  [(1, 1), (0, 1), (-1, 2), (0, 1), (1, 24), (0, 1), (-1, 720), (0, 1), (1, 40320), (0, 1),
    (-1, 3628800)]
def C12L : List (ℤ × ℕ) := C10L ++ [(0, 1), (1, 479001600)]
def S9L : List (ℤ × ℕ) :=
  [(0, 1), (1, 1), (0, 1), (-1, 6), (0, 1), (1, 120), (0, 1), (-1, 5040), (0, 1), (1, 362880)]
def S11L : List (ℤ × ℕ) := S9L ++ [(0, 1), (-1, 39916800)]

theorem uniQ_C10 : uniQ C10L = GlobalGA.PositiveTD.Certificate.C10 := by
  simp [uniQ, C10L, neg_div, GlobalGA.PositiveTD.Certificate.C10, GlobalGA.PositiveTD.Certificate.C4]; ring
theorem uniQ_C12 : uniQ C12L = GlobalGA.PositiveTD.Certificate.C12 := by
  simp [uniQ, C12L, neg_div, C10L, GlobalGA.PositiveTD.Certificate.C12, GlobalGA.PositiveTD.Certificate.C10,
    GlobalGA.PositiveTD.Certificate.C4]; ring
theorem uniQ_S9 : uniQ S9L = GlobalGA.PositiveTD.Certificate.S9 := by
  simp [uniQ, S9L, neg_div, GlobalGA.PositiveTD.Certificate.S9, GlobalGA.PositiveTD.Certificate.S5]; ring
theorem uniQ_S11 : uniQ S11L = GlobalGA.PositiveTD.Certificate.S11 := by
  simp [uniQ, S11L, neg_div, S9L, GlobalGA.PositiveTD.Certificate.S11, GlobalGA.PositiveTD.Certificate.S9,
    GlobalGA.PositiveTD.Certificate.S5]; ring

theorem rep_liftC10 {c : Config} {u : XM} {f : Bivar} (hu : u.Rep c f) :
    (liftM c u C10L).Rep c (TwoVariablePolynomial.lift f GlobalGA.PositiveTD.Certificate.C10) := by
  rw [← uniQ_C10]; exact rep_liftM hu _
theorem rep_liftC12 {c : Config} {u : XM} {f : Bivar} (hu : u.Rep c f) :
    (liftM c u C12L).Rep c (TwoVariablePolynomial.lift f GlobalGA.PositiveTD.Certificate.C12) := by
  rw [← uniQ_C12]; exact rep_liftM hu _
theorem rep_liftS9 {c : Config} {u : XM} {f : Bivar} (hu : u.Rep c f) :
    (liftM c u S9L).Rep c (TwoVariablePolynomial.lift f GlobalGA.PositiveTD.Certificate.S9) := by
  rw [← uniQ_S9]; exact rep_liftM hu _
theorem rep_liftS11 {c : Config} {u : XM} {f : Bivar} (hu : u.Rep c f) :
    (liftM c u S11L).Rep c (TwoVariablePolynomial.lift f GlobalGA.PositiveTD.Certificate.S11) := by
  rw [← uniQ_S11]; exact rep_liftM hu _

/-! ### Reduction by a common factor -/

/-- The gcd of the `2 ^ k` lowest base-`2 ^ w` digits of `N`, by halving. -/
def digitGcd (w : ℕ) : ℕ → ℕ → ℕ
  | N, 0 => N % 2 ^ w
  | N, k + 1 => Nat.gcd (digitGcd w (N % 2 ^ (w * 2 ^ k)) k) (digitGcd w (N >>> (w * 2 ^ k)) k)

/-- `gcd(g, the 2 ^ k lowest base-2 ^ w digits of N)`, by halving; zero halves are skipped, and
the search stops once the gcd is `1`. -/
def digitGcdZ (w : ℕ) : ℕ → ℕ → ℕ → ℕ
  | g, N, 0 => if N == 0 then g else Nat.gcd g (N % 2 ^ w)
  | g, N, k + 1 =>
    if N == 0 then g else if g == 1 then 1 else
      digitGcdZ w (digitGcdZ w g (N % 2 ^ (w * 2 ^ k)) k) (N >>> (w * 2 ^ k)) k

/-- Normalizes, then divides `U`, `V` and `s` by `g = gcd(s, digits of U and V)`, when the
division is exact digit by digit (`g` divides `U`, `V`, `s`, and every digit of `U / g` and
`V / g` is below `2 ^ t` with `g < 2 ^ (w - t)`); otherwise only normalizes. -/
def reduce (c : Config) (m : XM) : XM :=
  let n := norm c m
  let K := Nat.log2 (c.S * c.S) + 1
  let g := digitGcdZ c.w (digitGcdZ c.w n.s n.U K) n.V K
  let hi := boxPat c (c.b - 2 ^ (c.w - (Nat.log2 g + 1)))
  if n.ok && Nat.blt 0 g && Nat.ble 2 c.w && (n.U % g == 0) && (n.V % g == 0) && (n.s % g == 0) &&
      (n.U / g &&& hi == 0) && (n.V / g &&& hi == 0) then
    ⟨n.U / g, n.V / g, n.s / g, n.dx, n.dy, n.dt, n.U / g % (c.b - 1) + n.V / g % (c.b - 1), true⟩
  else n

/-- The digits of a box number that vanishes under the mask `hi`. -/
theorem coeffs_lt_of_mask {c : Config} (hw : 1 ≤ c.w) {N t : ℕ} (ht : t ≤ c.w)
    (h : N &&& boxPat c (c.b - 2 ^ t) = 0) {i j : ℕ} (hi : i < c.S) (hj : j < c.S) :
    coeffs c N i j < 2 ^ t := by
  have hb : c.b - 2 ^ t < c.b := Nat.sub_lt c.b_pos (by positivity)
  have h1 := coeffs_land c N (boxPat c (c.b - 2 ^ t)) i j
  rw [h, boxPat_eq c hw, coeffs_pack c (fun _ _ => hb) hi hj] at h1
  have h0 : coeffs c 0 i j = 0 := by simp [PackedModels.coeffs, digit]
  rw [h0, Config.b, land_high ht (coeffs_lt c N i j)] at h1
  have := Nat.lt_pow_self (n := t) (a := 2) (by norm_num)
  rcases Nat.eq_zero_or_pos (coeffs c N i j / 2 ^ t) with h2 | h2
  · exact (Nat.div_eq_zero_iff_lt (by positivity)).mp h2
  · exfalso; have : 0 < 2 ^ t * (coeffs c N i j / 2 ^ t) := by positivity
    omega

/-- Exact division of a box number by `g`, digit by digit. -/
theorem div_digits {c : Config} (hw : 1 ≤ c.w) {N g : ℕ} (hN : Box c N) (hdvd : g ∣ N)
    (h : N / g &&& boxPat c (c.b - 2 ^ (c.w - (Nat.log2 g + 1))) = 0) :
    Box c (N / g) ∧ ∀ i j, cf (poly c N) i j = cf (poly c (N / g)) i j * g := by
  have hB : Box c (N / g) := box_of_le (Nat.div_le_self _ _) hN
  have hlt : ∀ i j, i < c.S → j < c.S → coeffs c (N / g) i j * g < c.b := by
    intro i j hi hj
    have hd := coeffs_lt_of_mask hw (Nat.sub_le _ _) h hi hj
    have hg2 : g < 2 ^ (Nat.log2 g + 1) := Nat.lt_log2_self
    rcases Nat.eq_zero_or_pos (coeffs c (N / g) i j) with h0 | h0
    · rw [h0, zero_mul]; exact c.b_pos
    · have ht : 1 ≤ c.w - (Nat.log2 g + 1) := by
        by_contra hc
        have : c.w - (Nat.log2 g + 1) = 0 := by omega
        rw [this, pow_zero] at hd; omega
      calc coeffs c (N / g) i j * g < 2 ^ (c.w - (Nat.log2 g + 1)) * 2 ^ (Nat.log2 g + 1) :=
            Nat.mul_lt_mul'' hd hg2
        _ = c.b := by rw [← pow_add, Config.b]; congr 1; omega
  set d : ℕ → ℕ → ℕ := fun i j => if i < c.S ∧ j < c.S then coeffs c (N / g) i j * g else 0 with hd
  have hdlt : ∀ i j, d i j < c.b := fun i j => by
    simp only [hd]; split_ifs with h'; exacts [hlt i j h'.1 h'.2, c.b_pos]
  have hNd : N = pack c d := by
    have e1 : N = N / g * g := (Nat.div_mul_cancel hdvd).symm
    rw [e1, eq_pack_coeffs hB, pack_mul_const]
    exact pack_congr c fun i j hi hj => by simp [hd, hi, hj]
  refine ⟨hB, fun i j => ?_⟩
  rw [cf_poly, cf_poly]
  split_ifs with hij
  · show coeffs c N i j = coeffs c (N / g) i j * g
    have e := coeffs_pack c hdlt hij.1 hij.2
    rw [← hNd] at e
    rw [e]
    simp [hd, hij.1, hij.2]
  · simp

theorem rep_reduce {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) : (reduce c m).Rep c p := by
  have hn := rep_norm hm
  unfold reduce
  simp only []
  split_ifs with h
  · intro _
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hok, hg⟩, hw⟩, mU0⟩, mV0⟩, ms0⟩, hU⟩, hV⟩ := h
    set n := norm c m
    set g := digitGcdZ c.w (digitGcdZ c.w n.s n.U (Nat.log2 (c.S * c.S) + 1)) n.V
      (Nat.log2 (c.S * c.S) + 1)
    obtain ⟨gn, vn⟩ := hn hok
    have dU : g ∣ n.U := Nat.dvd_of_mod_eq_zero mU0
    have dV : g ∣ n.V := Nat.dvd_of_mod_eq_zero mV0
    have ds : g ∣ n.s := Nat.dvd_of_mod_eq_zero ms0
    obtain ⟨bU, cU⟩ := div_digits (by omega) gn.boxU dU hU
    obtain ⟨bV, cV⟩ := div_digits (by omega) gn.boxV dV hV
    have sU : Supp (poly c (n.U / g)) n.dx n.dy n.dt := fun i j h0 =>
      gn.suppU i j (by rw [cU]; exact mul_ne_zero h0 (by omega))
    have sV : Supp (poly c (n.V / g)) n.dx n.dy n.dt := fun i j h0 =>
      gn.suppV i j (by rw [cV]; exact mul_ne_zero h0 (by omega))
    have dle : ∀ N, (∀ i j, cf (poly c N) i j = cf (poly c (N / g)) i j * g) →
        dsum (poly c (N / g)) ≤ dsum (poly c N) := by
      intro N hc
      rw [← dsumN_eq, ← dsumN_eq]
      unfold dsumN
      refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
      have e1 := cf_poly c N i j
      have e2 := cf_poly c (N / g) i j
      rw [ite_eq_left ⟨Finset.mem_range.mp hi, Finset.mem_range.mp hj⟩] at e1 e2
      have := hc i j
      rw [e1, e2] at this
      show digit c.w (N / g) (c.S * i + j) ≤ digit c.w N (c.S * i + j)
      rw [this]; exact Nat.le_mul_of_pos_right _ (by omega)
    have dsU := dle n.U cU
    have dsV := dle n.V cV
    have hsz := gn.size
    have hsmall := gn.small
    have hb1 : 2 ^ (c.w - 2) < c.b - 1 := by
      have : 2 ^ (c.w - 2) * 4 = c.b := by
        unfold Config.b; rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
      have : 1 ≤ 2 ^ (c.w - 2) := Nat.one_le_two_pow
      omega
    have mU : n.U / g % (c.b - 1) = dsum (poly c (n.U / g)) := by
      rw [← dsumN_eq]; exact mod_eq_dsumN bU (by unfold Config.M; rw [dsumN_eq]; omega)
    have mV : n.V / g % (c.b - 1) = dsum (poly c (n.V / g)) := by
      rw [← dsumN_eq]; exact mod_eq_dsumN bV (by unfold Config.M; rw [dsumN_eq]; omega)
    refine ⟨⟨bU, bV, sU, sV, ?_, ?_, gn.dxS, gn.dyS⟩, ?_⟩
    · show dsum (poly c (n.U / g)) + dsum (poly c (n.V / g)) ≤ n.U / g % (c.b - 1) + n.V / g % (c.b - 1)
      rw [mU, mV]
    · show n.U / g % (c.b - 1) + n.V / g % (c.b - 1) < 2 ^ (c.w - 2)
      rw [mU, mV]; omega
    · show mapQ (poly c (n.U / g)) - mapQ (poly c (n.V / g)) = scalar ((n.s / g : ℕ) : ℚ) * p
      have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
      ext i j
      have hv := congrArg (fun q : Bivar => (q.coeff i).coeff j) vn
      simp only [val, Polynomial.coeff_sub, coeff_mapQ, coeff_scalar_mul, cU, cV] at hv
      rw [Polynomial.coeff_sub, Polynomial.coeff_sub, coeff_mapQ, coeff_mapQ, coeff_scalar_mul,
        Nat.cast_div ds hgq]
      push_cast at hv
      field_simp
      linarith
  · exact hn

/-- `cubicMass (ρn / ρd) p`, with the deviation `w` reduced (`reduce`) before its powers. -/
def cubicMassRM (c : Config) (ρn : ℤ) (ρd : ℕ) (m : XM) : XM :=
  guard (mulQ c (trunc c (add c (sub c (add c (ofInt c 1 1) (mulQ c (reduce c (massDevM c m)) 1 2))
    (mulQ c (pow c (reduce c (massDevM c m)) 2) 1 8)) (mulQ c (pow c (reduce c (massDevM c m)) 3) 1 16))
    3) ρn ρd) (m.ok && Nat.blt 0 m.s && decide (const0 c m ≠ 0))

theorem rep_cubicMassRM {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p) {ρ : ℚ} {ρn : ℤ}
    {ρd : ℕ} (hρ : ρ = ρn / ρd) : (cubicMassRM c ρn ρd m).Rep c (TwoVariablePolynomial.cubicMass ρ p) := by
  apply rep_guard
  intro _ hb
  simp only [Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq] at hb
  obtain ⟨⟨hok, hs⟩, hk⟩ := hb
  have hc := const0_spec hm hok (by omega)
  have hsq : (m.s : ℚ) ≠ 0 := by exact_mod_cast (show m.s ≠ 0 by omega)
  have hkq : (const0 c m : ℚ) ≠ 0 := by exact_mod_cast hk
  have hW : (massDevM c m).Rep c (scalar (1 / TwoVariablePolynomial.constant p) *
      (TwoVariablePolynomial.truncate3 p - scalar (TwoVariablePolynomial.constant p))) := by
    rw [truncate3_eq, TwoVariablePolynomial.constant, hc]
    refine rep_mulQ' (rep_sub (rep_trunc hm 3) (rep_ofInt c _ _)) ?_
    have hd : (((const0 c m).natAbs : ℕ) : ℚ) = |(const0 c m : ℚ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [hd]
    split_ifs with h0
    · rw [abs_of_nonneg (by exact_mod_cast h0)]; push_cast; field_simp
    · rw [abs_of_neg (by exact_mod_cast lt_of_not_ge h0)]; push_cast; field_simp
  replace hW := rep_reduce hW
  rw [TwoVariablePolynomial.cubicMass, truncate3_eq]
  exact rep_mulQ' (rep_trunc (rep_add (rep_sub (rep_add (rep_one c) (rep_mulQ' hW (by norm_num)))
    (rep_mulQ' (rep_pow hW 2) (by norm_num))) (rep_mulQ' (rep_pow hW 3) (by norm_num))) 3) hρ

/-! ### Case distinctions -/

theorem rep_ite {c : Config} {P : Prop} [Decidable P] {a b : XM} {A B : Bivar} (h1 : a.Rep c A)
    (h2 : b.Rep c B) : (if P then a else b).Rep c (if P then A else B) := by
  split_ifs; exacts [h1, h2]

theorem rep_vec2 {c : Config} {a0 a1 : XM} {p0 p1 : Bivar} (h0 : a0.Rep c p0) (h1 : a1.Rep c p1)
    (i : Fin 2) : (![a0, a1] i).Rep c (![p0, p1] i) := by
  fin_cases i; exacts [h0, h1]

theorem rep_vec3 {c : Config} {a0 a1 a2 : XM} {p0 p1 p2 : Bivar} (h0 : a0.Rep c p0)
    (h1 : a1.Rep c p1) (h2 : a2.Rep c p2) (i : Fin 3) : (![a0, a1, a2] i).Rep c (![p0, p1, p2] i) := by
  fin_cases i; exacts [h0, h1, h2]

theorem rep_vec4 {c : Config} {a0 a1 a2 a3 : XM} {p0 p1 p2 p3 : Bivar} (h0 : a0.Rep c p0)
    (h1 : a1.Rep c p1) (h2 : a2.Rep c p2) (h3 : a3.Rep c p3) (i : Fin 4) :
    (![a0, a1, a2, a3] i).Rep c (![p0, p1, p2, p3] i) := by
  fin_cases i; exacts [h0, h1, h2, h3]

end XM

/-! ## Building models along the syntax of a polynomial

`build_xm [h₁, …]` proves a goal `m.Rep c p` whose model `m` is a metavariable, by following the
syntax of `p`: sums, differences, products, powers, negations, `X`, `C X`, `0`, `1`, scalars,
`lift f` of `C10`, `C12`, `S9`, `S11`, `if … then … else …`, `![…] i`, and the given lemmas `hᵢ`
(for instance `(fooM c _).2` for a polynomial `foo _` modelled earlier). The model is built in
the process. Scalars `scalar r` need `r` to be a closed rational expression; constants in it are
unfolded. -/

open Lean Meta Elab Tactic in
/-- The value of a closed rational expression, and the constants unfolded on the way. -/
meta partial def evalQ (e : Expr) : MetaM (ℚ × Array Name) := do
  let e ← instantiateMVars e
  let bin (f : ℚ → ℚ → ℚ) (a b : Expr) : MetaM (ℚ × Array Name) := do
    let (x, n1) ← evalQ a
    let (y, n2) ← evalQ b
    return (f x y, n1 ++ n2)
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => bin (· + ·) a b
  | (``HSub.hSub, #[_, _, _, _, a, b]) => bin (· - ·) a b
  | (``HMul.hMul, #[_, _, _, _, a, b]) => bin (· * ·) a b
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) => bin (· / ·) a b
  | (``Neg.neg, #[_, _, a]) => do let (x, ns) ← evalQ a; return (-x, ns)
  | (``Inv.inv, #[_, _, a]) => do let (x, ns) ← evalQ a; return (x⁻¹, ns)
  | (``OfNat.ofNat, #[_, n, _]) =>
    match n.rawNatLit? with
    | some k => return ((k : ℚ), #[])
    | none => evalQ n
  | (``Nat.cast, #[_, _, a]) => evalQ a
  | (``Int.cast, #[_, _, a]) => evalQ a
  | _ =>
    match e with
    | .lit (.natVal k) => return ((k : ℚ), #[])
    | _ =>
      let some n := e.getAppFn.constName? | throwError "evalQ: cannot evaluate {e}"
      let some v ← unfoldDefinition? e | throwError "evalQ: cannot evaluate {e}"
      let (x, ns) ← evalQ v
      return (x, ns.push n)

open Lean Meta Elab Tactic in
/-- Proves `?m.Rep c (scalar r)` with `?m := ofInt c n d` for the value `n / d` of `r`. -/
elab "rep_scalar" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some p := (if ty.isAppOfArity ``XM.Rep 3 then some ty.appArg! else none)
    | throwError "rep_scalar: the goal is not `XM.Rep`"
  let p ← whnfR p
  unless p.isAppOfArity ``TensorWholeIntervalPolynomial.scalar 1 do
    throwError "rep_scalar: not a scalar"
  let (q, ns) ← evalQ p.appArg!
  let nlit : TSyntax `term := ⟨Syntax.mkNumLit (toString q.num.natAbs)⟩
  let n : TSyntax `term ← if q.num < 0 then `(-$nlit) else pure nlit
  let d : TSyntax `term := ⟨Syntax.mkNumLit (toString q.den)⟩
  let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    ns.mapM fun nm => `(Lean.Parser.Tactic.simpLemma| $(mkIdent nm):ident)
  let side ← if lemmas.isEmpty then `(tactic| norm_num)
    else `(tactic| (simp only [$lemmas,*]; norm_num))
  evalTactic (← `(tactic| exact XM.rep_lit _ (n := $n) (s := $d) (by $side:tactic)))

syntax "build_xm" (" [" term,* "]")? : tactic
macro_rules
  | `(tactic| build_xm $[[$ts,*]]?) => do
    let ts : Array (Lean.TSyntax `term) := (ts.map (·.getElems)).getD #[]
    let mut user : Lean.TSyntax ``Lean.Parser.Tactic.tacticSeq ← `(tacticSeq| fail "build_xm: no rule")
    for t in ts.reverse do
      user ← `(tacticSeq| first | with_reducible apply $t | $user)
    `(tactic| repeat' first
      | with_reducible apply XM.rep_add
      | with_reducible apply XM.rep_sub
      | with_reducible apply XM.rep_mul
      | with_reducible apply XM.rep_pow
      | with_reducible apply XM.rep_neg
      | with_reducible apply XM.rep_ite
      | with_reducible apply XM.rep_vec2
      | with_reducible apply XM.rep_vec3
      | with_reducible apply XM.rep_vec4
      | with_reducible apply XM.rep_liftC10
      | with_reducible apply XM.rep_liftC12
      | with_reducible apply XM.rep_liftS9
      | with_reducible apply XM.rep_liftS11
      | with_reducible exact XM.rep_X _
      | with_reducible exact XM.rep_Y _
      | with_reducible exact XM.rep_one _
      | with_reducible exact XM.rep_zero _
      | rep_scalar
      | $user)

end SquaresInCircles.Eight.TableFree.BivariateCertificate
