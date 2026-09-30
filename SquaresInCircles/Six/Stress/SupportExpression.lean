import SquaresInCircles.Six.Stress.SupportFormula
import SquaresInCircles.Six.Normalization.Certificates.Model

/-!
# Exploratory reification of the exact support

The mathematical formula and its proof live in SupportFormula, which has no
computational-certificate imports. This file retains the expression syntax
needed by the not-yet-converted certificate developments. It is not an allowed
mathematical dependency of the final human-analytic proof.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open ProofTools Normalization

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
