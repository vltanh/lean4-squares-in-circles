module

public import SquaresInCircles.Eight.TableFree.PowerTailBounds

/-!
# Whole-interval power bounds with a retained leading part

Uncompiled source.  On a nonnegative interval only negative higher
coefficients need be charged against the retained leading power.  On
a centered interval the absolute coefficient sum gives the constant
bound.  The finite identities and rational reserves are proved by each
application for its explicitly defined polynomial.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.DirectedPowerBounds
open Polynomial PowerTailBounds

def shift (a : ℚ) (p : ℚ[X]) : ℚ[X] := p.comp (C a+X)
def reverse (a : ℚ) (p : ℚ[X]) : ℚ[X] := p.comp (C a-X)

@[simp] theorem shift_eval (a : ℚ) (p : ℚ[X]) (x : ℝ) :
    aeval x (shift a p)=aeval ((a:ℝ)+x) p := by simp [shift,aeval_comp]

@[simp] theorem reverse_eval (a : ℚ) (p : ℚ[X]) (x : ℝ) :
    aeval x (reverse a p)=aeval ((a:ℝ)-x) p := by simp [reverse,aeval_comp]

def negativeNorm (p : ℚ[X]) (start count : ℕ) (r : ℚ) : ℚ :=
  ∑ j : Fin count,max (-(p.coeff (j.val+start))) 0*r^(j.val+1)

theorem tail_lower {p : ℚ[X]} {k n : ℕ} {r : ℚ} {x : ℝ}
    (hx : x∈Set.Icc 0 (r:ℝ)) :
    -(negativeNorm p (k+1) n r:ℝ)*x^k≤aeval x (tail p (k+1) n) := by
  have hterm (j : Fin n) :
      -max (-(p.coeff (j.val+(k+1)):ℝ)) 0*(r:ℝ)^(j.val+1)*x^k≤
        (p.coeff (j.val+(k+1)):ℝ)*x^(j.val+(k+1)) := by
    set c : ℝ := (p.coeff (j.val+(k+1)):ℝ)
    have hc : -max (-c) 0≤c := by linarith [le_max_left (-c) 0]
    have hp := pow_le_pow_left₀ hx.1 hx.2 (j.val+1)
    have hm := mul_le_mul_of_nonneg_left hp (le_max_right (-c) 0)
    have hl := mul_le_mul_of_nonneg_right hc (pow_nonneg hx.1 (j.val+1))
    have hbase : -max (-c) 0*(r:ℝ)^(j.val+1)≤c*x^(j.val+1) := by linarith
    have hk := mul_le_mul_of_nonneg_right hbase (pow_nonneg hx.1 k)
    have he : x^(j.val+(k+1))=x^(j.val+1)*x^k := by
      rw [← pow_add]
      congr 1
      omega
    rw [he,← mul_assoc]
    exact hk
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hterm j)
  have he : (negativeNorm p (k+1) n r:ℝ)=
      ∑ j : Fin n,max (-(p.coeff (j.val+(k+1)):ℝ)) 0*(r:ℝ)^(j.val+1) := by
    simp [negativeNorm]
  simp only [tail,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  rw [he]
  simpa only [neg_mul,Finset.sum_neg_distrib,Finset.sum_mul] using hh

theorem quadratic_lower {p : ℚ[X]} {n : ℕ} {r : ℚ} {x : ℝ}
    (he : p=C (p.coeff 0)+C (p.coeff 1)*X+C (p.coeff 2)*X^2+tail p 3 n)
    (hx : x∈Set.Icc 0 (r:ℝ)) :
    (p.coeff 0:ℝ)+(p.coeff 1:ℝ)*x+
      ((p.coeff 2:ℝ)-(negativeNorm p 3 n r:ℝ))*x^2≤aeval x p := by
  have ht : -(negativeNorm p 3 n r:ℝ)*x^2≤aeval x (tail p 3 n) :=
    tail_lower (p:=p) (k:=2) (n:=n) hx
  have hi := congrArg (fun f : ℚ[X] => aeval x f) he
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at hi
  linarith

theorem cubic_lower {p : ℚ[X]} {n : ℕ} {r : ℚ} {x : ℝ}
    (he : p=C (p.coeff 0)+C (p.coeff 1)*X+C (p.coeff 2)*X^2+
      C (p.coeff 3)*X^3+tail p 4 n)
    (hx : x∈Set.Icc 0 (r:ℝ)) :
    (p.coeff 0:ℝ)+(p.coeff 1:ℝ)*x+(p.coeff 2:ℝ)*x^2+
      ((p.coeff 3:ℝ)-(negativeNorm p 4 n r:ℝ))*x^3≤aeval x p := by
  have ht : -(negativeNorm p 4 n r:ℝ)*x^3≤aeval x (tail p 4 n) :=
    tail_lower (p:=p) (k:=3) (n:=n) hx
  have hi := congrArg (fun f : ℚ[X] => aeval x f) he
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at hi
  linarith

theorem constant_lower {p : ℚ[X]} {n : ℕ} {r : ℚ} {x : ℝ}
    (he : p=C (p.coeff 0)+tail p 1 n) (hx : |x|≤(r:ℝ)) :
    (p.coeff 0:ℝ)-(PowerTailBounds.norm p 1 n r:ℝ)≤aeval x p := by
  have hterm (j : Fin n) :
      -|(p.coeff (j.val+1):ℝ)| *(r:ℝ)^(j.val+1)≤
        (p.coeff (j.val+1):ℝ)*x^(j.val+1) := by
    have hp := pow_le_pow_left₀ (abs_nonneg x) hx (j.val+1)
    have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (p.coeff (j.val+1):ℝ))
    rw [← abs_pow,← abs_mul] at hm
    rw [neg_mul]
    exact (abs_le.mp hm).1
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hterm j)
  have hi := congrArg (fun f : ℚ[X] => aeval x f) he
  simp only [tail,map_add,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at hi
  have hn : (PowerTailBounds.norm p 1 n r:ℝ)=
      ∑ j : Fin n,|(p.coeff (j.val+1):ℝ)| *(r:ℝ)^(j.val+1) := by
    simp [PowerTailBounds.norm]
  rw [hn]
  simp only [neg_mul,Finset.sum_neg_distrib] at hh
  linarith

end SquaresInCircles.Eight.TableFree.DirectedPowerBounds
