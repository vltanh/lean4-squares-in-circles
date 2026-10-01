import SquaresInCircles.Six.Analytic.FixedPairConcavity

/-!
# The exact target gap on closed sign sectors

Subtracting the proposed envelope is affine on each of the three genuine
sign walls. This file connects the smooth concavity proof to the exact
minorant, including points on the walls. No differentiation of an absolute
value at zero is used.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

def gap (no wo : Bool) (u : Fin 4) (n w : ℝ) : ℝ :=
  minorant no wo u n w-pairBase-line w-(1/1000)*|n|

def lineSlope (p : Bool) : ℝ := if p then -13/50 else -18/25

lemma abs_eq_of_HasSign {p : Bool} {x : ℝ} (hx : HasSign p x) :
    |x|=sign p*x := by
  cases p
  · simpa [sign] using abs_of_nonpos hx
  · simpa [sign] using abs_of_nonneg hx

lemma line_eq_of_HasSign {p : Bool} {x : ℝ} (hx : HasSign p x) :
    line x=lineSlope p*x := by
  cases p
  · have h : x≤0 := hx
    simp only [line,lineSlope,Bool.false_eq_true,ite_false,max_eq_right h,
      max_eq_left (neg_nonneg.mpr h),mul_zero,sub_zero]
    ring
  · have h : 0≤x := hx
    simp only [line,lineSlope,ite_true,max_eq_left h,
      max_eq_right (neg_nonpos.mpr h),mul_zero,zero_sub]
    ring

lemma gap_eq_on_sector {no wo pn pw pq : Bool} {u : Fin 4} {n w : ℝ}
    (hd : Domain no wo n w) (hs : Sector pn pw pq n w) :
    gap no wo u n w=formula no wo u pn pw pq n w-
      (pairBase+lineSlope pw*w+(sign pn/1000)*n) := by
  rw [gap,minorant_eq_formula hd hs,line_eq_of_HasSign hs.2.1,abs_eq_of_HasSign hs.1]
  ring

private lemma sub_affine_concave {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ s f) (A B : ℝ) :
    ConcaveOn ℝ s (fun x => f x-(A*x+B)) := by
  refine ⟨hf.1,?_⟩
  intro x hx y hy a b ha hb hab
  have h := hf.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have hid :
      (f (a*x+b*y)-(A*(a*x+b*y)+B))-
        (a*(f x-(A*x+B))+b*(f y-(A*y+B))) =
      f (a*x+b*y)-(a*f x+b*f y) := by
    calc
      _=f (a*x+b*y)-(a*f x+b*f y)+B*(a+b-1) := by ring
      _=_ := by rw [hab]; ring
  linarith

/-- Coordinate and diagonal concavity of the target gap, on every closed
segment lying in a geometric sign sector and in the explicit pair domain. -/
theorem gap_slice_concave {no wo pn pw pq : Bool} (u : Fin 4) (k : Fin 3)
    {n w l r : ℝ}
    (hd : ∀ x ∈ Set.Icc l r, Domain no wo (sliceN k n w x) (sliceW k n w x))
    (hs : ∀ x ∈ Set.Icc l r, Sector pn pw pq (sliceN k n w x) (sliceW k n w x)) :
    ConcaveOn ℝ (Set.Icc l r)
      (fun x => gap no wo u (sliceN k n w x) (sliceW k n w x)) := by
  have hf := formula_slice_concave u k hd hs
  fin_cases k
  · have hc := sub_affine_concave hf (sign pn/1000) (pairBase+lineSlope pw*w)
    apply hc.congr
    intro x hx
    have he := gap_eq_on_sector (u := u) (hd x hx) (hs x hx)
    simp +decide only [sliceN,sliceW,ite_true,ite_false] at he ⊢
    rw [he]
    ring
  · have hc := sub_affine_concave hf (lineSlope pw) (pairBase+(sign pn/1000)*n)
    apply hc.congr
    intro x hx
    have he := gap_eq_on_sector (u := u) (hd x hx) (hs x hx)
    simp +decide only [sliceN,sliceW,ite_true,ite_false] at he ⊢
    rw [he]
    ring
  · have hc := sub_affine_concave hf (lineSlope pw+sign pn/1000) pairBase
    apply hc.congr
    intro x hx
    have he := gap_eq_on_sector (u := u) (hd x hx) (hs x hx)
    simp +decide only [sliceN,sliceW,ite_false] at he ⊢
    rw [he]
    ring

end SquaresInCircles.Six.Analytic.FixedPair
