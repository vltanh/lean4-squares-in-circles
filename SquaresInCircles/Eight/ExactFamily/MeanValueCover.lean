module

public import SquaresInCircles.Eight.ExactFamily.FixedEval
public import SquaresInCircles.Eight.ExactFamily.CompactRootCover

/-!
# Mean-value exclusion for root localization

On a box where a formula is regular, its value at a point differs from its value at the centre
of the box by a sum of partial derivatives times coordinate offsets: the mean value theorem is
applied along one coordinate at a time, so every intermediate point stays in the box. Interval
enclosures of the partial derivatives on the box therefore enclose the formula on the whole box;
on small boxes this enclosure is much tighter than the direct one. The partial derivatives are
given as formulas that agree in value with the symbolic ones, and all intervals are evaluated in
fixed point (`FixedEval`).

`Covered targets target B` says that every simultaneous zero of `targets` in `B` lies in
`target`. A localization is proved by splitting boxes (`covered_split`) down to leaves, each
covered by inclusion (`covered_inside`), by a direct enclosure of one target that excludes zero
(`covered_exclude`), or by a mean-value enclosure that excludes zero (`covered_meanValue`).
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily.MeanValueCover
open Arithmetic FixedEval CompactRootCover

/-- The centre of a box. -/
def center {n : ℕ} (B : QBox n) (i : Fin n) : ℚ := ((B i).lo + (B i).hi) / 2

/-- The box reduced to its centre. -/
def centerBox {n : ℕ} (B : QBox n) : QBox n := fun i => ⟨center B i, center B i⟩

/-- The offsets of a coordinate interval from its centre, rounded outwards. -/
def offset {n : ℕ} (p : ℕ) (B : QBox n) (i : Fin n) : DI :=
  ⟨(DI.ofRat p ((B i).lo - center B i)).lo, (DI.ofRat p ((B i).hi - center B i)).hi⟩

/-- The mean-value enclosure `f c + Σⱼ Dⱼ (B) (Bⱼ - cⱼ)` of `f` on `B`, where `c` is the centre
and `D` are the partial derivatives. -/
def meanValue (p : ℕ) (B : QBox 3) (f : Formula 3) (D : Fin 3 → Formula 3) : Option DI :=
  match eval p (ofBox p (centerBox B)) f, eval p (ofBox p B) (D 0), eval p (ofBox p B) (D 1),
      eval p (ofBox p B) (D 2) with
  | some I, some D₀, some D₁, some D₂ =>
    some (((I.add (D₀.mul p (offset p B 0))).add (D₁.mul p (offset p B 1))).add
      (D₂.mul p (offset p B 2)))
  | _, _, _, _ => none

/-- An enclosure that excludes zero. -/
def excludesZero : Option DI → Bool
  | some I => decide (I.hi < 0 ∨ 0 < I.lo)
  | none => false

theorem ne_zero_of_excludesZero {p : ℕ} {I : DI} (h : excludesZero (some I) = true) {x : ℝ}
    (hx : I.Mem p x) : x ≠ 0 := by
  have hs : I.hi < 0 ∨ 0 < I.lo := by simpa [excludesZero] using h
  obtain ⟨h1, h2⟩ := hx
  intro hz
  rw [hz, zero_mul] at h1 h2
  rcases hs with hs | hs
  · have : (I.hi : ℝ) < 0 := by exact_mod_cast hs
    linarith
  · have : (0 : ℝ) < I.lo := by exact_mod_cast hs
    linarith

theorem regular_of_inside {B outer : QBox 3} {f : Formula 3} (hsub : inside B outer = true)
    (h : ∀ x, outer.Mem x → f.RegularAt x) : ∀ x, B.Mem x → f.RegularAt x :=
  fun x hx => h x (box_mem_of_subset (by simpa [inside] using hsub) hx)

theorem center_mem {n : ℕ} {B : QBox n} {x : Fin n → ℝ} (hx : B.Mem x) (i : Fin n) :
    (B i).Mem (center B i) := by
  have h1 := (hx i).1
  have h2 := (hx i).2
  constructor <;> simp only [center] <;> push_cast <;> linarith

theorem mem_update {n : ℕ} {B : QBox n} {x : Fin n → ℝ} (hx : B.Mem x) {j : Fin n} {t : ℝ}
    (ht : (B j).Mem t) : B.Mem (Function.update x j t) := by
  intro i
  by_cases hij : i = j
  · subst hij
    simpa using ht
  · simpa [Function.update_of_ne hij] using hx i

/-- The mean value theorem along the coordinate `j`, inside a box where `f` is regular: the
slope is a value of the partial derivative, so it has every property `P` that those values have. -/
theorem mean_value_step {n : ℕ} {f : Formula n} {B : QBox n} (j : Fin n) {P : ℝ → Prop}
    (hreg : ∀ x, B.Mem x → f.RegularAt x) (hD : ∀ x, B.Mem x → P ((f.diff j).eval x))
    {p : Fin n → ℝ} (hp : B.Mem p) {c : ℝ} (hc : (B j).Mem c) :
    ∃ d, P d ∧ f.eval p - f.eval (Function.update p j c) = d * (p j - c) := by
  set φ : ℝ → ℝ := fun t => f.eval (Function.update p j t) with hφ
  set φ' : ℝ → ℝ := fun t => (f.diff j).eval (Function.update p j t) with hφ'
  have hseg : ∀ t, min c (p j) ≤ t → t ≤ max c (p j) → (B j).Mem t := fun t h1 h2 =>
    ⟨(le_min hc.1 (hp j).1).trans h1, h2.trans (max_le hc.2 (hp j).2)⟩
  have hder : ∀ t, (B j).Mem t → HasDerivAt φ (φ' t) t := by
    intro t ht
    have h := Formula.hasDerivAt_partial f j (Function.update p j t) (hreg _ (mem_update hp ht))
    simpa [φ, φ', Function.update_idem, Function.update_self] using h
  have hp' : f.eval p = φ (p j) := by simp [φ, Function.update_eq_self]
  rcases lt_trichotomy c (p j) with hlt | heq | hgt
  · have hmem : ∀ t ∈ Set.Icc c (p j), (B j).Mem t := fun t ht =>
      hseg t ((min_le_left _ _).trans ht.1) (ht.2.trans (le_max_right _ _))
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope φ φ' hlt
      (fun t ht => (hder t (hmem t ht)).continuousAt.continuousWithinAt)
      (fun t ht => hder t (hmem t (Set.Ioo_subset_Icc_self ht)))
    refine ⟨φ' ξ, hD _ (mem_update hp (hmem ξ (Set.Ioo_subset_Icc_self hξ))), ?_⟩
    rw [hslope, hp']
    field_simp [sub_ne_zero.2 hlt.ne']
    rfl
  · refine ⟨(f.diff j).eval p, hD p hp, ?_⟩
    subst heq
    simp [Function.update_eq_self]
  · have hmem : ∀ t ∈ Set.Icc (p j) c, (B j).Mem t := fun t ht =>
      hseg t ((min_le_right _ _).trans ht.1) (ht.2.trans (le_max_left _ _))
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope φ φ' hgt
      (fun t ht => (hder t (hmem t ht)).continuousAt.continuousWithinAt)
      (fun t ht => hder t (hmem t (Set.Ioo_subset_Icc_self ht)))
    refine ⟨φ' ξ, hD _ (mem_update hp (hmem ξ (Set.Ioo_subset_Icc_self hξ))), ?_⟩
    rw [hslope, hp']
    field_simp [sub_ne_zero.2 hgt.ne']
    ring

theorem meanValue_sound {p : ℕ} {B : QBox 3} {f : Formula 3} {D : Fin 3 → Formula 3} {I : DI}
    (hreg : ∀ x, B.Mem x → f.RegularAt x) (hD : ∀ k x, (f.diff k).eval x = (D k).eval x)
    (hI : meanValue p B f D = some I) {x : Fin 3 → ℝ} (hx : B.Mem x) : I.Mem p (f.eval x) := by
  cases h₀ : eval p (ofBox p (centerBox B)) f with
  | none => simp [meanValue, h₀] at hI
  | some I₀ =>
  cases h₁ : eval p (ofBox p B) (D 0) with
  | none => simp [meanValue, h₀, h₁] at hI
  | some D₀ =>
  cases h₂ : eval p (ofBox p B) (D 1) with
  | none => simp [meanValue, h₀, h₁, h₂] at hI
  | some D₁ =>
  cases h₃ : eval p (ofBox p B) (D 2) with
  | none => simp [meanValue, h₀, h₁, h₂, h₃] at hI
  | some D₂ =>
  simp only [meanValue, h₀, h₁, h₂, h₃, Option.some.injEq] at hI
  subst hI
  have h2 := two_pow_pos p
  set m : Fin 3 → ℝ := fun i => (center B i : ℝ) with hm_def
  have hm : ∀ i, (B i).Mem (m i) := center_mem hx
  set p₁ := Function.update x 0 (m 0) with hp₁_def
  set p₂ := Function.update p₁ 1 (m 1) with hp₂_def
  set p₃ := Function.update p₂ 2 (m 2) with hp₃_def
  have hp₁ : B.Mem p₁ := mem_update hx (hm 0)
  have hp₂ : B.Mem p₂ := mem_update hp₁ (hm 1)
  have hp₃m : p₃ = m := by
    funext i
    fin_cases i <;> simp [p₃, p₂, p₁, m, Function.update]
  have hcenter : (centerBox B).Mem m := fun i => ⟨le_rfl, le_rfl⟩
  have hI₀ : I₀.Mem p (f.eval p₃) := by
    rw [hp₃m]
    exact (eval_sound (mem_ofBox hcenter) f h₀).1
  have hDk : ∀ (k : Fin 3) (Dk : DI), eval p (ofBox p B) (D k) = some Dk →
      ∀ y, B.Mem y → Dk.Mem p ((f.diff k).eval y) := by
    intro k Dk hk y hy
    rw [hD k y]
    exact (eval_sound (mem_ofBox hy) (D k) hk).1
  obtain ⟨d₀, hd₀, e₀⟩ := mean_value_step 0 hreg (hDk 0 D₀ h₁) hx (hm 0)
  obtain ⟨d₁, hd₁, e₁⟩ := mean_value_step 1 hreg (hDk 1 D₁ h₂) hp₁ (hm 1)
  obtain ⟨d₂, hd₂, e₂⟩ := mean_value_step 2 hreg (hDk 2 D₂ h₃) hp₂ (hm 2)
  have ho : ∀ i, (offset p B i).Mem p (x i - m i) := by
    intro i
    have hlo := (DI.mem_ofRat p ((B i).lo - center B i)).1
    have hhi := (DI.mem_ofRat p ((B i).hi - center B i)).2
    have h1 := (hx i).1
    have h2' := (hx i).2
    push_cast at hlo hhi
    constructor
    · show ((DI.ofRat p ((B i).lo - center B i)).lo : ℝ) ≤ (x i - m i) * 2 ^ p
      refine hlo.trans (mul_le_mul_of_nonneg_right ?_ h2.le)
      simp only [m]; linarith
    · show (x i - m i) * 2 ^ p ≤ ((DI.ofRat p ((B i).hi - center B i)).hi : ℝ)
      refine (mul_le_mul_of_nonneg_right ?_ h2.le).trans hhi
      simp only [m]; linarith
  have hx₁ : p₁ 1 = x 1 := by simp [p₁, Function.update_of_ne]
  have hx₂ : p₂ 2 = x 2 := by simp [p₂, p₁, Function.update_of_ne]
  have hs₀ := DI.mem_mul hd₀ (ho 0)
  have hs₁ := DI.mem_mul hd₁ (ho 1)
  have hs₂ := DI.mem_mul hd₂ (ho 2)
  have hsum := DI.mem_add (DI.mem_add (DI.mem_add hI₀ hs₀) hs₁) hs₂
  rw [hx₁] at e₁
  rw [hx₂] at e₂
  have he : f.eval x = f.eval p₃ + d₀ * (x 0 - m 0) + d₁ * (x 1 - m 1) + d₂ * (x 2 - m 2) := by
    linarith
  rw [he]
  exact hsum

/-- Every simultaneous zero of `targets` in `B` lies in `target`. -/
def Covered (targets : Fin 3 → Formula 3) (target B : QBox 3) : Prop :=
  ∀ env, B.Mem env → SimultaneousZeros targets env → target.Mem env

theorem covered_split {targets : Fin 3 → Formula 3} {target : QBox 3} (B : QBox 3) (i : Fin 3)
    (c : ℚ) (hl : Covered targets target (B.left i c)) (hr : Covered targets target (B.right i c)) :
    Covered targets target B := fun env he hz =>
  closed_box_split B i c (P := fun x => SimultaneousZeros targets x → target.Mem x) hl hr env he hz

theorem covered_inside {targets : Fin 3 → Formula 3} {target B : QBox 3}
    (h : inside B target = true) : Covered targets target B :=
  fun _ he _ => box_mem_of_subset (by simpa [inside] using h) he

theorem covered_exclude {targets : Fin 3 → Formula 3} {target B : QBox 3} {p : ℕ} (j : Fin 3)
    (h : excludes p B (targets j) = true) : Covered targets target B :=
  fun _ he hz => absurd (hz j) (excludes_sound h he)

theorem covered_meanValue {targets : Fin 3 → Formula 3} {target B : QBox 3} {p : ℕ}
    (j : Fin 3) (D : Fin 3 → Formula 3) (hD : ∀ k x, ((targets j).diff k).eval x = (D k).eval x)
    (hreg : ∀ x, B.Mem x → (targets j).RegularAt x)
    (h : excludesZero (meanValue p B (targets j) D) = true) : Covered targets target B := by
  intro env he hz
  cases hc : meanValue p B (targets j) D with
  | none => simp [hc, excludesZero] at h
  | some I =>
    rw [hc] at h
    exact absurd (hz j) (ne_zero_of_excludesZero h (meanValue_sound hreg hD hc he))

end SquaresInCircles.Eight.ExactFamily.MeanValueCover
