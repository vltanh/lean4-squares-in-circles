module

public import Mathlib.Tactic

/-!
# Eight squares: centered power bounds on one complete interval

These elementary coefficient-norm inequalities
keep a linear or quadratic leading part and bound every higher power at
once.  Applications prove their exact polynomial expansion and exact
rational coefficient reserves separately.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.PowerTailBounds
open Polynomial

def tail (p : ℚ[X]) (start count : ℕ) : ℚ[X] :=
  ∑ j : Fin count,C (p.coeff (j.val+start))*X^(j.val+start)

def norm (p : ℚ[X]) (start count : ℕ) (r : ℚ) : ℚ :=
  ∑ j : Fin count,|p.coeff (j.val+start)| *r^(j.val+1)

theorem tail_linear_lower {p : ℚ[X]} {n : ℕ} {r : ℚ} {x : ℝ}
    (_hr : 0≤r) (hx : |x|≤(r:ℝ)) :
    -(norm p 2 n r:ℝ)*|x|≤aeval x (tail p 2 n) := by
  have hterm (j : Fin n) :
      -|(p.coeff (j.val+2):ℝ)| *(r:ℝ)^(j.val+1)*|x|≤
        (p.coeff (j.val+2):ℝ)*x^(j.val+2) := by
    have hp : |x|^(j.val+1)≤(r:ℝ)^(j.val+1) :=
      pow_le_pow_left₀ (abs_nonneg x) hx _
    have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (p.coeff (j.val+2):ℝ))
    have hm' := mul_le_mul_of_nonneg_right hm (abs_nonneg x)
    have he : |(p.coeff (j.val+2):ℝ)*x^(j.val+2)|=
        |(p.coeff (j.val+2):ℝ)| *|x|^(j.val+1)*|x| := by
      rw [abs_mul,abs_pow,show j.val+2=(j.val+1)+1 by omega,pow_add,pow_one]
      ring
    rw [← he] at hm'
    have hlo := (abs_le.mp hm').1
    linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j)
  simp only [tail,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  have hn : (norm p 2 n r:ℝ)=
      ∑ j : Fin n,|(p.coeff (j.val+2):ℝ)| *(r:ℝ)^(j.val+1) := by
    simp [norm]
  rw [hn]
  simpa only [neg_mul,Finset.sum_neg_distrib,Finset.sum_mul] using hs

theorem tail_quadratic_lower {p : ℚ[X]} {n : ℕ} {r : ℚ} {x : ℝ}
    (_hr : 0≤r) (hx : |x|≤(r:ℝ)) :
    -(norm p 3 n r:ℝ)*x^2≤aeval x (tail p 3 n) := by
  have hterm (j : Fin n) :
      -|(p.coeff (j.val+3):ℝ)| *(r:ℝ)^(j.val+1)*x^2≤
        (p.coeff (j.val+3):ℝ)*x^(j.val+3) := by
    have hp : |x^(j.val+1)|≤(r:ℝ)^(j.val+1) := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg x) hx _
    have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (p.coeff (j.val+3):ℝ))
    rw [← abs_mul] at hm
    have hlo := mul_le_mul_of_nonneg_right (abs_le.mp hm).1 (sq_nonneg x)
    have he : (p.coeff (j.val+3):ℝ)*x^(j.val+3)=
        ((p.coeff (j.val+3):ℝ)*x^(j.val+1))*x^2 := by
      rw [show j.val+3=(j.val+1)+2 by omega,pow_add]
      ring
    rw [he]
    linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j)
  simp only [tail,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  have hn : (norm p 3 n r:ℝ)=
      ∑ j : Fin n,|(p.coeff (j.val+3):ℝ)| *(r:ℝ)^(j.val+1) := by
    simp [norm]
  rw [hn]
  simpa only [neg_mul,Finset.sum_neg_distrib,Finset.sum_mul] using hs

theorem linear_lower {p : ℚ[X]} {n : ℕ} {r : ℚ} {x : ℝ}
    (hidentity : p=C (p.coeff 0)+C (p.coeff 1)*X+tail p 2 n)
    (hr : 0≤r) (hx : |x|≤(r:ℝ)) :
    (p.coeff 0:ℝ)+(p.coeff 1:ℝ)*x-(norm p 2 n r:ℝ)*|x|≤aeval x p := by
  have ht := tail_linear_lower (p := p) (n := n) hr hx
  have he := congrArg (fun z : ℚ[X] => aeval x z) hidentity
  simp only [map_add,map_mul,aeval_C,aeval_X,eq_ratCast] at he
  linarith

theorem quadratic_lower {p : ℚ[X]} {n : ℕ} {r : ℚ} {x : ℝ}
    (hidentity : p=C (p.coeff 0)+C (p.coeff 1)*X+C (p.coeff 2)*X^2+tail p 3 n)
    (hr : 0≤r) (hx : |x|≤(r:ℝ)) :
    (p.coeff 0:ℝ)+(p.coeff 1:ℝ)*x+
      ((p.coeff 2:ℝ)-(norm p 3 n r:ℝ))*x^2≤aeval x p := by
  have ht := tail_quadratic_lower (p := p) (n := n) hr hx
  have he := congrArg (fun z : ℚ[X] => aeval x z) hidentity
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at he
  linarith

end SquaresInCircles.Eight.PowerTailBounds
