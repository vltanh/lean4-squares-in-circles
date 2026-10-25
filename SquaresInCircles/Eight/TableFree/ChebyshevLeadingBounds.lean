module

public import SquaresInCircles.Eight.TableFree.WholeIntervalPolynomial

/-!
# Retaining the quadratic and cubic parts of a whole-interval bound

The higher Chebyshev terms are bounded by one coefficient norm.
The leading quadratic is completed exactly; for a cubic, its odd
degree-three term is bounded by the square on [-1,1].  Concrete
applications supply exact rational polynomial identities, so no
coefficient expansion is assumed.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.TableFree.ChebyshevLeadingBounds

open Polynomial WholeIntervalPolynomial

def tail (b : ℕ→ℚ) (start count : ℕ) : ℚ[X] :=
  ∑ j : Fin count,C (b (j.val+start))*Polynomial.Chebyshev.T ℚ (j.val+start)

def tailNorm (b : ℕ→ℚ) (start count : ℕ) : ℚ :=
  ∑ j : Fin count,|b (j.val+start)|

def quadraticReserve (b : ℕ→ℚ) (count : ℕ) : ℚ :=
  b 0-b 2-(b 1)^2/(8*b 2)-tailNorm b 3 count

def cubicReserve (b : ℕ→ℚ) (count : ℕ) : ℚ :=
  b 0-b 2-(b 1-3*b 3)^2/(4*(2*b 2-4*|b 3|))-tailNorm b 4 count

theorem tail_lower (b : ℕ→ℚ) (start count : ℕ) {x : ℝ} (hx : |x|≤1) :
    -(tailNorm b start count:ℝ)≤aeval x (tail b start count) := by
  have ht (j : Fin count) : -|(b (j.val+start):ℝ)|≤
      (b (j.val+start):ℝ)*(Polynomial.Chebyshev.T ℝ (j.val+start)).eval x :=
    (scalar_bounds (Polynomial.Chebyshev.abs_eval_T_real_le_one _ hx)).1
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => ht j)
  simp only [tail,map_sum,map_mul,aeval_C,Polynomial.Chebyshev.aeval_T]
  simpa [tailNorm,Finset.sum_neg_distrib] using hh

theorem quadratic_min {a b q x : ℝ} (hq : 0<q) :
    a-b^2/(4*q)≤a+b*x+q*x^2 := by
  have hh : -(b^2/(4*q))≤b*x+q*x^2 := by
    rw [← neg_div]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<4*q)).2
    nlinarith [sq_nonneg (2*q*x+b)]
  linarith

theorem quadratic_lower {p : ℚ[X]} {b : ℕ→ℚ} {count : ℕ}
    (hid : p=C (b 0-b 2)+C (b 1)*X+C (2*b 2)*X^2+tail b 3 count)
    (hb : 0<b 2) {x : ℝ} (hx : |x|≤1) :
    (quadraticReserve b count:ℝ)≤aeval x p := by
  have ht := tail_lower b 3 count hx
  have hq : (0:ℝ)<2*(b 2:ℝ) := by exact_mod_cast mul_pos (by norm_num : (0:ℚ)<2) hb
  have hm := quadratic_min (a:=(b 0:ℝ)-(b 2:ℝ)) (b:=(b 1:ℝ)) (x:=x) hq
  rw [show 4*(2*(b 2:ℝ))=8*(b 2:ℝ) by ring] at hm
  have he := congrArg (fun f : ℚ[X] => aeval x f) hid
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at he
  push_cast at he
  dsimp [quadraticReserve]
  push_cast
  linarith

theorem cubic_lower {p : ℚ[X]} {b : ℕ→ℚ} {count : ℕ}
    (hid : p=C (b 0-b 2)+C (b 1-3*b 3)*X+C (2*b 2)*X^2+
      C (4*b 3)*X^3+tail b 4 count)
    (hb : 0<2*b 2-4*|b 3|) {x : ℝ} (hx : |x|≤1) :
    (cubicReserve b count:ℝ)≤aeval x p := by
  have ht := tail_lower b 4 count hx
  have hcub : |x^3|≤x^2 := by
    rw [abs_pow,show (3:ℕ)=2+1 from rfl,pow_add,pow_one,sq_abs]
    nlinarith [mul_le_mul_of_nonneg_left hx (sq_nonneg x)]
  have hprod := mul_le_mul_of_nonneg_left hcub (abs_nonneg (4*(b 3:ℝ)))
  rw [← abs_mul] at hprod
  have hodd := (abs_le.mp hprod).1
  have habs : |4*(b 3:ℝ)|=4*|(b 3:ℝ)| := by rw [abs_mul]; norm_num
  rw [habs] at hodd
  have hq : (0:ℝ)<2*(b 2:ℝ)-4*|(b 3:ℝ)| := by exact_mod_cast hb
  have hm := quadratic_min (a:=(b 0:ℝ)-(b 2:ℝ))
    (b:=(b 1:ℝ)-3*(b 3:ℝ)) (x:=x) hq
  have he := congrArg (fun f : ℚ[X] => aeval x f) hid
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at he
  push_cast at he
  dsimp [cubicReserve]
  push_cast
  linarith

/-- Transfer any centered whole-interval estimate back to its actual
rational interval. -/
theorem transfer {a b : ℚ} {p : ℚ[X]} {v : ℝ} (hab : a<b)
    (hv : ∀u : ℝ,|u|≤1 → v≤aeval u (centered a b p))
    {x : ℝ} (hx : x∈Set.Icc (a:ℝ) (b:ℝ)) : v≤aeval x p := by
  have hgap : 0<(b:ℝ)-(a:ℝ) := by exact_mod_cast sub_pos.mpr hab
  obtain ⟨u,hu_def⟩ : ∃ u : ℝ,u=(2*x-(a:ℝ)-(b:ℝ))/((b:ℝ)-(a:ℝ)) := ⟨_,rfl⟩
  have hu : |u|≤1 := by
    apply abs_le.mpr
    rw [hu_def]
    constructor
    · apply (le_div_iff₀ hgap).2
      linarith [hx.1]
    · apply (div_le_iff₀ hgap).2
      linarith [hx.2]
  have haff : aeval u (affine a b)=x := by
    simp only [affine,map_add,map_mul,aeval_C,aeval_X,eq_ratCast]
    push_cast
    rw [hu_def]
    field_simp [hgap.ne']
    ring
  have hh := hv u hu
  simpa only [centered,aeval_comp,haff] using hh

theorem quadratic_on_interval {a b : ℚ} {p : ℚ[X]} {c : ℕ→ℚ} {count : ℕ}
    (hab : a<b)
    (hid : centered a b p=C (c 0-c 2)+C (c 1)*X+C (2*c 2)*X^2+tail c 3 count)
    (hc : 0<c 2) {x : ℝ} (hx : x∈Set.Icc (a:ℝ) (b:ℝ)) :
    (quadraticReserve c count:ℝ)≤aeval x p :=
  transfer hab (fun _ hu => quadratic_lower hid hc hu) hx

theorem cubic_on_interval {a b : ℚ} {p : ℚ[X]} {c : ℕ→ℚ} {count : ℕ}
    (hab : a<b)
    (hid : centered a b p=C (c 0-c 2)+C (c 1-3*c 3)*X+C (2*c 2)*X^2+
      C (4*c 3)*X^3+tail c 4 count)
    (hc : 0<2*c 2-4*|c 3|) {x : ℝ} (hx : x∈Set.Icc (a:ℝ) (b:ℝ)) :
    (cubicReserve c count:ℝ)≤aeval x p :=
  transfer hab (fun _ hu => cubic_lower hid hc hu) hx

end SquaresInCircles.Eight.TableFree.ChebyshevLeadingBounds
