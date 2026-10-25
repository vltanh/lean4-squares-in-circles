module

public import SquaresInCircles.Eight.Owners.Tensor.ResidualEnclosure

/-!
# Eight squares: arithmetic expressions with certified root and denominator domains

`Valid` is a recursively computed rational property
of one complete polynomial model. Applications discharge it by exact
arithmetic on their literal formulas. It checks every square-root
domain, every reciprocal denominator, and every trigonometric argument.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TensorRadicalExpression
open TensorPolynomialEnclosure TensorResidualEnclosure

inductive Expr (ι : Type*) where
  | literal (r : ℚ)
  | variable (i : ι)
  | add (a b : Expr ι)
  | neg (a : Expr ι)
  | mul (a b : Expr ι)
  | power (a : Expr ι) (n : ℕ)
  | root (a : Expr ι)
  | reciprocal (a : Expr ι)
  | sine (a : Expr ι)
  | cosine (a : Expr ι)

namespace Expr

instance {ι : Type*} : Add (Expr ι) := ⟨.add⟩
instance {ι : Type*} : Neg (Expr ι) := ⟨.neg⟩
instance {ι : Type*} : Sub (Expr ι) := ⟨fun a b => .add a (.neg b)⟩
instance {ι : Type*} : Mul (Expr ι) := ⟨.mul⟩
instance {ι : Type*} : Div (Expr ι) := ⟨fun a b => .mul a (.reciprocal b)⟩
instance {ι : Type*} : Pow (Expr ι) ℕ := ⟨.power⟩
instance {ι : Type*} (n : ℕ) : OfNat (Expr ι) n := ⟨.literal n⟩

def value {ι : Type*} (v : ι → ℝ) : Expr ι → ℝ
  | .literal r => r
  | .variable i => v i
  | .add a b => value v a+value v b
  | .neg a => -value v a
  | .mul a b => value v a*value v b
  | .power a n => value v a^n
  | .root a => Real.sqrt (value v a)
  | .reciprocal a => 1/value v a
  | .sine a => Real.sin (value v a)
  | .cosine a => Real.cos (value v a)

def enclose {ι : Type*} (w : ι → Enclosure) : Expr ι → Enclosure
  | .literal r => constant r
  | .variable i => w i
  | .add a b => TensorPolynomialEnclosure.add (enclose w a) (enclose w b)
  | .neg a => TensorPolynomialEnclosure.neg (enclose w a)
  | .mul a b => TensorPolynomialEnclosure.mul (enclose w a) (enclose w b)
  | .power a n => TensorPolynomialEnclosure.power (enclose w a) n
  | .root a => TensorResidualEnclosure.root (enclose w a)
  | .reciprocal a => TensorResidualEnclosure.reciprocal (enclose w a)
  | .sine a => TensorPolynomialEnclosure.sine (enclose w a)
  | .cosine a => TensorPolynomialEnclosure.cosine (enclose w a)

def Valid {ι : Type*} (w : ι → Enclosure) : Expr ι → Prop
  | .literal _ | .variable _ => True
  | .add a b | .mul a b => Valid w a ∧ Valid w b
  | .neg a | .power a _ => Valid w a
  | .root a => Valid w a ∧ 0≤floor (enclose w a) ∧ 0<rootFloor (enclose w a) ∧
      (radicandRootLower (enclose w a))^2≤floor (enclose w a)
  | .reciprocal a => Valid w a ∧ 0<floor (enclose w a)
  | .sine a | .cosine a => Valid w a ∧ 0≤floor (enclose w a) ∧
      norm (enclose w a).polynomial+(enclose w a).error≤7/10

instance {ι : Type*} (w : ι → Enclosure) (e : Expr ι) : Decidable (Valid w e) := by
  induction e with
  | literal r => exact isTrue trivial
  | «variable» i => exact isTrue trivial
  | add a b ha hb =>
      letI := ha
      letI := hb
      change Decidable (Valid w a ∧ Valid w b)
      infer_instance
  | mul a b ha hb =>
      letI := ha
      letI := hb
      change Decidable (Valid w a ∧ Valid w b)
      infer_instance
  | neg a ha => exact ha
  | power a n ha => exact ha
  | root a ha =>
      letI := ha
      unfold Valid
      infer_instance
  | reciprocal a ha =>
      letI := ha
      unfold Valid
      infer_instance
  | sine a ha =>
      letI := ha
      unfold Valid
      infer_instance
  | cosine a ha =>
      letI := ha
      unfold Valid
      infer_instance

theorem contains {ι : Type*} (e : Expr ι) {v : ι → ℝ} {w : ι → Enclosure} {x y : ℝ}
    (hw : ∀ i,Contains (w i) x y (v i)) (hx : |x|≤1) (hy : |y|≤1)
    (hg : Valid w e) : Contains (enclose w e) x y (value v e) := by
  induction e with
  | literal r => exact contains_constant r x y
  | «variable» i => exact hw i
  | add a b ha hb => exact (ha hg.1).add (hb hg.2)
  | neg a ha => exact (ha hg).neg
  | mul a b ha hb => exact (ha hg.1).mul (hb hg.2) hx hy
  | power a n ha => exact (ha hg).power hx hy n
  | root a ha =>
      have hh := ha hg.1
      have hlo := Contains.lower hh hx hy
      have hnonneg : 0≤value v a :=
        (show (0:ℝ)≤(floor (enclose w a):ℝ) by exact_mod_cast hg.2.1).trans hlo
      exact Contains.root hh hx hy hnonneg hg.2.2.1 hg.2.2.2
  | reciprocal a ha => exact Contains.reciprocal (ha hg.1) hx hy hg.2
  | sine a ha =>
      have hh := ha hg.1
      have hlo := Contains.lower hh hx hy
      have hhi := (le_abs_self (value v a)).trans (Contains.value_bound hh hx hy)
      have hnonneg : 0≤value v a :=
        (show (0:ℝ)≤(floor (enclose w a):ℝ) by exact_mod_cast hg.2.1).trans hlo
      have hu : value v a≤frameCap := by
        have hbound : (norm (enclose w a).polynomial:ℝ)+((enclose w a).error:ℝ)≤7/10 := by
          have h := (Rat.cast_le (K := ℝ)).mpr hg.2.2
          push_cast at h
          exact h
        dsimp [frameCap]
        linarith
      exact Contains.sine hh hx hy ⟨hnonneg,hu⟩
  | cosine a ha =>
      have hh := ha hg.1
      have hlo := Contains.lower hh hx hy
      have hhi := (le_abs_self (value v a)).trans (Contains.value_bound hh hx hy)
      have hnonneg : 0≤value v a :=
        (show (0:ℝ)≤(floor (enclose w a):ℝ) by exact_mod_cast hg.2.1).trans hlo
      have hu : value v a≤frameCap := by
        have hbound : (norm (enclose w a).polynomial:ℝ)+((enclose w a).error:ℝ)≤7/10 := by
          have h := (Rat.cast_le (K := ℝ)).mpr hg.2.2
          push_cast at h
          exact h
        dsimp [frameCap]
        linarith
      exact Contains.cosine hh hx hy ⟨hnonneg,hu⟩

end Expr
end SquaresInCircles.Eight.TensorRadicalExpression
