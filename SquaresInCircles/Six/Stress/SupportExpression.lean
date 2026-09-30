import SquaresInCircles.Six.Stress.ExactSupport
import SquaresInCircles.Six.Normalization.Certificates.Model

/-!
# Exact support as a reified real expression

The expression uses the genuine condition 2 R min(|x|,|y|) <= sqrt(x^2+y^2).
An undecided interval comparison encloses both branches, by Expr.eval_sound.
The equality below identifies this expression with the support already proved
for actual contained square centers.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open ProofTools Normalization

lemma scalarSupport_max_min (R x y : ℝ) :
    scalarSupport R x y =
      if 2*R*min |x| |y| ≤ Real.sqrt (x^2+y^2) then
        rhoAt R*max |x| |y|
      else R*Real.sqrt (x^2+y^2)-(|x|+|y|)/2 := by
  unfold scalarSupport orderedSupport
  by_cases h : |y|≤|x|
  · simp only [if_pos h,min_eq_right h,max_eq_left h,sq_abs]
  · have h' : |x|≤|y| := (lt_of_not_ge h).le
    simp only [if_neg h,min_eq_left h',max_eq_right h',sq_abs]
    rw [show y^2+x^2=x^2+y^2 by ring]
    split_ifs <;> ring

namespace Reified

abbrev rat {n : ℕ} (q : ℚ) : Expr n := .rat q

def rho {n : ℕ} (R : Expr n) : Expr n := .sqrt (.sq R-rat (1/4))-rat (1/2)

def support {n : ℕ} (R x y : Expr n) : Expr n :=
  let q := Expr.sqrt (.sq x+.sq y)
  let u := Expr.max (.abs x) (.abs y)
  let v := Expr.min (.abs x) (.abs y)
  .iteLe (2*R*v) q (rho R*u) (R*q-(.abs x+.abs y)/2)

def boxSupport {n : ℕ} (c x y : Expr n) : Expr n := c*(.max x 0+.max y 0)

@[simp] lemma denote_rho {n : ℕ} (z : Fin n → ℝ) (R : Expr n) :
    Expr.denote (rho R) z=rhoAt (Expr.denote R z) := by
  simp [rho,Expr.denote,rhoAt,div_eq_mul_inv,sub_eq_add_neg]

@[simp] lemma denote_support {n : ℕ} (z : Fin n → ℝ) (R x y : Expr n) :
    Expr.denote (support R x y) z=
      scalarSupport (Expr.denote R z) (Expr.denote x z) (Expr.denote y z) := by
  rw [scalarSupport_max_min]
  simp [support,Expr.denote,rho,rhoAt,div_eq_mul_inv,sub_eq_add_neg]

@[simp] lemma denote_boxSupport {n : ℕ} (z : Fin n → ℝ) (c x y : Expr n) :
    Expr.denote (boxSupport c x y) z=
      Stress.boxSupport (Expr.denote c z) (Expr.denote x z,Expr.denote y z) := by
  simp [boxSupport,Stress.boxSupport,Expr.denote]

end Reified

/-- Every closed real segment is parametrized by the unit interval, including
its two endpoints. Degenerate segments use parameter zero. -/
lemma segment_parameter {a b x : ℝ} (hx : a≤x ∧ x≤b) :
    ∃ u : ℝ, (0≤u ∧ u≤1) ∧ x=a+(b-a)*u := by
  by_cases hab : a=b
  · refine ⟨0,⟨le_rfl,by norm_num⟩,?_⟩
    have hax : x=a := by linarith [hx.1,hx.2]
    simp [hax]
  · have hpos : 0<b-a := sub_pos.mpr (lt_of_le_of_ne (hx.1.trans hx.2) hab)
    refine ⟨(x-a)/(b-a),⟨div_nonneg (sub_nonneg.mpr hx.1) hpos.le,?_⟩,?_⟩
    · apply (div_le_iff₀ hpos).mpr
      linarith [hx.2]
    · field_simp [ne_of_gt hpos]
      ring

end SquaresInCircles.Six.Stress
