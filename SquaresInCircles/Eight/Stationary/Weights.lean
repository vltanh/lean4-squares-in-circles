module

public import SquaresInCircles.Eight.Stationary.Coordinates

/-!
# Eight squares: the contact and circle weights of the chain

From the coordinates of a chain, the module defines five circle weights `mu`, one for each corner
on the circle, normalized to add up to `1` (`WeightDomain.mu_sum`), and seven contact weights `lam`,
one for each contact of the cycle. They are positive on the sign domain `WeightDomain`, which holds
at every point of the stationary system (`IsStationary.weightDomain`). With these weights the
forces on the squares balance: at each of `A`, `B`, `D`, `E` and `H` the contact forces cancel the
corner force `2 μ P` (`force_balance`), and on `T` and `G` they cancel each other
(`slider_forces_zero`). The vertical balance at `E` is not an assumption on the weights; it follows
from the position equation `positionDerivative = 0` (`last_force_residual`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.Stationary
namespace Coordinates

def rawMuA (d : Coordinates) : ℝ := d.c / (2*d.x₁)
def rawAlpha (d : Coordinates) : ℝ := d.s-d.c*d.y/d.x₁
def rawMuB (d : Coordinates) : ℝ := d.rawAlpha/(2*(d.y+2))
def rawBeta (d : Coordinates) : ℝ := d.rawAlpha*d.x₂/(d.y+2)
def rawMuD (d : Coordinates) : ℝ := -d.rawBeta/(2*d.x₃)
def rawDelta (d : Coordinates) : ℝ := 2*d.rawMuD*d.y₃
def rawMuH (d : Coordinates) : ℝ := -1/(2*d.h₁)
def rawEpsilon (d : Coordinates) : ℝ := d.h₂/d.h₁
def rawMuE (d : Coordinates) : ℝ := -d.s*d.rawEpsilon/(2*d.x₄)

def rawMu (d : Coordinates) : Fin 5 → ℝ :=
  ![d.rawMuA,d.rawMuB,d.rawMuD,d.rawMuE,d.rawMuH]
def weightMass (d : Coordinates) : ℝ := ∑ i : Fin 5, d.rawMu i
def mu (d : Coordinates) (i : Fin 5) : ℝ := d.rawMu i/d.weightMass

/-- Contact order AB, TB, DT, ED, GA, HG, HE. -/
def rawLambda (d : Coordinates) : Fin 7 → ℝ :=
  ![d.rawAlpha,d.rawBeta,d.rawBeta,d.rawDelta,1,1,d.rawEpsilon]
def lam (d : Coordinates) (i : Fin 7) : ℝ := d.rawLambda i/d.weightMass

/-- The sign conditions under which the weights are positive. The adaptive comparison uses them
at every tilt; they assert neither stationarity nor optimality. -/
structure WeightDomain (d : Coordinates) : Prop where
  x₁_pos : 0 < d.x₁
  x₂_pos : 0 < d.x₂
  y₃_pos : 0 < d.y₃
  x₃_neg : d.x₃ < 0
  x₄_neg : d.x₄ < 0
  y_neg : d.y < 0
  y_add_two_pos : 0 < d.y+2
  c_pos : 0 < d.c
  s_pos : 0 < d.s
  h₁_neg : d.h₁ < 0
  h₂_neg : d.h₂ < 0

theorem IsStationary.weightDomain {d : Coordinates} (hd : d.IsStationary) :
    d.WeightDomain := by
  have hc : 0 < d.c := halfAngleCos_pos (abs_lt.mpr ⟨by linarith [hd.z_pos], hd.z_lt_one⟩)
  have hs : 0 < d.s := halfAngleSin_pos hd.z_pos
  have hc1 : d.c ≤ 1 := halfAngleCos_le_one d.z
  have hs1 : d.s ≤ 1 := by nlinarith [d.unit, sq_nonneg d.c]
  have hy0 : d.y < 0 := by linarith [hd.y_upper]
  have hy42 : d.y₄ < 0 := by linarith [hd.y₄_upper]
  have hy1 : d.y ^ 2 < 1 := by nlinarith [hd.y_lower, hd.y_upper]
  have hx11 : 1 < d.x₁ := by
    nlinarith [hd.q_lower, hd.first_circle, hd.x₁_pos]
  have hx12 : d.x₁ < 2 := by
    nlinarith [hd.q_upper, hd.first_circle, sq_nonneg d.y]
  have hx22 : d.x₂ < 2 := by
    nlinarith [hd.q_upper, hd.second_circle, sq_nonneg (d.y+2)]
  have hx42 : -2 < d.x₄ := by
    nlinarith [hd.q_upper, hd.fourth_circle, sq_nonneg d.y₄]
  have h₁ : d.h₁ < 0 := by
    have hcx : d.c*(d.x₁-1) < 1 := by
      have h := mul_le_mul_of_nonneg_right hc1 (by linarith : 0 ≤ d.x₁-1)
      nlinarith
    have hsy : d.s*d.y < 0 := mul_neg_of_pos_of_neg hs hy0
    dsimp [h₁]
    nlinarith
  have h₂ : d.h₂ < 0 := by
    have hsy : d.s*(-d.x₄-1) < d.s := by nlinarith
    have hcy : d.c*d.y₄ < 0 := mul_neg_of_pos_of_neg hc hy42
    dsimp [h₂]
    nlinarith
  exact ⟨hd.x₁_pos, hd.x₂_pos, hd.y₃_pos, by dsimp [x₃]; linarith,
    hd.x₄_neg, hy0, by linarith [hd.y_lower], hc, hs, h₁, h₂⟩

theorem WeightDomain.rawAlpha_pos {d : Coordinates} (h : d.WeightDomain) :
    0 < d.rawAlpha := by
  have hcy : d.c*d.y/d.x₁ < 0 := div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg h.c_pos h.y_neg) h.x₁_pos
  dsimp [rawAlpha]
  linarith [h.s_pos]

theorem WeightDomain.rawBeta_pos {d : Coordinates} (h : d.WeightDomain) :
    0 < d.rawBeta := div_pos (mul_pos h.rawAlpha_pos h.x₂_pos) h.y_add_two_pos

theorem WeightDomain.rawMu_pos {d : Coordinates} (h : d.WeightDomain) (i : Fin 5) :
    0 < d.rawMu i := by
  have hA : 0 < d.rawMuA := div_pos h.c_pos (by linarith [h.x₁_pos])
  have hB : 0 < d.rawMuB := div_pos h.rawAlpha_pos (by linarith [h.y_add_two_pos])
  have hD : 0 < d.rawMuD := div_pos_of_neg_of_neg (by linarith [h.rawBeta_pos])
    (by linarith [h.x₃_neg])
  have hH : 0 < d.rawMuH := div_pos_of_neg_of_neg (by norm_num)
    (by linarith [h.h₁_neg])
  have hε : 0 < d.rawEpsilon := div_pos_of_neg_of_neg h.h₂_neg h.h₁_neg
  have hE : 0 < d.rawMuE := div_pos_of_neg_of_neg
    (mul_neg_of_neg_of_pos (by linarith [h.s_pos]) hε) (by linarith [h.x₄_neg])
  fin_cases i <;> simp only [rawMu] <;> assumption

theorem WeightDomain.weightMass_pos {d : Coordinates} (h : d.WeightDomain) :
    0 < d.weightMass := by
  exact Finset.sum_pos (fun i _ => h.rawMu_pos i) Finset.univ_nonempty

theorem WeightDomain.mu_pos {d : Coordinates} (h : d.WeightDomain) (i : Fin 5) :
    0 < d.mu i := div_pos (h.rawMu_pos i) h.weightMass_pos

theorem WeightDomain.mu_sum {d : Coordinates} (h : d.WeightDomain) :
    ∑ i : Fin 5, d.mu i = 1 := by
  simp only [mu]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt h.weightMass_pos)

theorem WeightDomain.rawLambda_pos {d : Coordinates} (h : d.WeightDomain) (i : Fin 7) :
    0 < d.rawLambda i := by
  have hα : 0 < d.rawAlpha := h.rawAlpha_pos
  have hβ : 0 < d.rawBeta := h.rawBeta_pos
  have hδ : 0 < d.rawDelta := mul_pos
    (mul_pos (by norm_num) (h.rawMu_pos 2)) h.y₃_pos
  have hε : 0 < d.rawEpsilon := div_pos_of_neg_of_neg h.h₂_neg h.h₁_neg
  fin_cases i <;> simp only [rawLambda, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> first | assumption | norm_num

theorem WeightDomain.lam_pos {d : Coordinates} (h : d.WeightDomain) (i : Fin 7) :
    0 < d.lam i := div_pos (h.rawLambda_pos i) h.weightMass_pos

/-- The scalar identity behind the E vertical balance. -/
theorem last_force_residual {d : Coordinates} (h : d.WeightDomain) :
    2*d.rawMuE*d.y₄+d.rawDelta-d.c*d.rawEpsilon =
      -d.positionDerivative/(2*d.h₁*d.y₄deriv) := by
  have hx₁ := ne_of_gt h.x₁_pos
  have hx₂ := ne_of_gt h.x₂_pos
  have hy₃ := ne_of_gt h.y₃_pos
  have hx₃ := ne_of_lt h.x₃_neg
  have hx₄ := ne_of_lt h.x₄_neg
  have hy := ne_of_gt h.y_add_two_pos
  have hh₁ := ne_of_lt h.h₁_neg
  dsimp [rawMuE, rawEpsilon, rawDelta, rawMuD, rawBeta, rawAlpha,
    positionDerivative, h₁deriv, h₂deriv, y₄deriv]
  field_simp [hx₁,hx₂,hy₃,hx₃,hx₄,hy,hh₁]
  ring

/-- The unnormalized centre forces, in the order `A, B, D, E, H, T, G`. -/
def rawForces (d : Coordinates) : Fin 7 → Point :=
  ![(-d.c, d.rawAlpha-d.s),
    (-d.rawBeta,-d.rawAlpha),
    (d.rawBeta,-d.rawDelta),
    (d.rawEpsilon*d.s,d.rawDelta-d.rawEpsilon*d.c),
    (d.c-d.rawEpsilon*d.s,d.s+d.rawEpsilon*d.c),
    (0,0),(0,0)]

theorem raw_force_balance {d : Coordinates} (h : d.WeightDomain)
    (hstation : d.positionDerivative = 0) (i : Fin 5) :
    add (scale (2*d.rawMu i) (d.anchorPoints i)) (d.rawForces i.castSucc.castSucc) = (0,0) := by
  have hx₁ := ne_of_gt h.x₁_pos
  have hx₃ := ne_of_lt h.x₃_neg
  have hx₄ := ne_of_lt h.x₄_neg
  have hy := ne_of_gt h.y_add_two_pos
  have hh₁ := ne_of_lt h.h₁_neg
  have hE : 2*d.rawMuE*d.y₄+d.rawDelta-d.c*d.rawEpsilon = 0 := by
    rw [last_force_residual h, hstation]
    simp
  fin_cases i
  all_goals
    ext <;> simp only [rawMu, rawForces, anchorPoints, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Fin.reduceCastSucc, Matrix.cons_val, add, scale]
  all_goals
    first
    | linear_combination hE
    | dsimp [rawMuA,rawMuB,rawMuD,rawMuE,rawMuH,rawAlpha,rawBeta,
        rawDelta,rawEpsilon,inFrame]
      field_simp [hx₁,hx₃,hx₄,hy,hh₁]
      ring

def forces (d : Coordinates) (i : Fin 7) : Point :=
  scale (1/d.weightMass) (d.rawForces i)

theorem force_balance {d : Coordinates} (h : d.WeightDomain)
    (hstation : d.positionDerivative = 0) (i : Fin 5) :
    d.forces i.castSucc.castSucc =
      scale (-2*d.mu i) (d.anchorPoints i) := by
  have hf := raw_force_balance h hstation i
  have hx := congrArg Prod.fst hf
  have hy := congrArg Prod.snd hf
  ext <;> dsimp [forces,mu,add,scale] at hx hy ⊢
  · linear_combination (1/d.weightMass)*hx
  · linear_combination (1/d.weightMass)*hy

theorem slider_forces_zero (d : Coordinates) :
    d.forces 5 = (0,0) ∧ d.forces 6 = (0,0) := by
  simp [forces,rawForces,scale]

end Coordinates
end SquaresInCircles.Eight.Stationary
