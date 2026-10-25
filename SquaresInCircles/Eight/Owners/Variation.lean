module

public import SquaresInCircles.Eight.Frames.Signed.Coordinates

/-!
# Eight squares: signed variation under actual endpoint alignment

The two incident errors are changed as a pair. Their sum
is invariant. Positive and negative variation are each controlled, not just
the sum of their absolute values. In particular a negative source error
cannot disappear from an equality argument by cancellation on the other edge.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight
open Candidate

def positivePart (x : ℝ) : ℝ := max x 0
def negativePart (x : ℝ) : ℝ := max (-x) 0

def positiveVariation (θ : Vertex → ℝ) : ℝ := ∑ i, positivePart (delta θ i)
def negativeVariation (θ : Vertex → ℝ) : ℝ := ∑ i, negativePart (delta θ i)

@[simp] theorem positivePart_zero : positivePart 0=0 := by simp [positivePart]
@[simp] theorem negativePart_zero : negativePart 0=0 := by simp [negativePart]

theorem positivePart_nonneg (x : ℝ) : 0 ≤ positivePart x := le_max_right _ _
theorem negativePart_nonneg (x : ℝ) : 0 ≤ negativePart x := le_max_right _ _

theorem positive_sub_negative (x : ℝ) : positivePart x-negativePart x=x := by
  rcases le_total 0 x with h | h
  · simp [positivePart,negativePart,max_eq_left h,max_eq_right (by linarith : -x ≤ 0)]
  · simp [positivePart,negativePart,max_eq_right h,max_eq_left (by linarith : 0 ≤ -x)]

theorem positive_add_negative (x : ℝ) : positivePart x+negativePart x=|x| := by
  rcases le_total 0 x with h | h
  · simp [positivePart,negativePart,max_eq_left h,max_eq_right (by linarith : -x ≤ 0),
      abs_of_nonneg h]
  · simp [positivePart,negativePart,max_eq_right h,max_eq_left (by linarith : 0 ≤ -x),
      abs_of_nonpos h]

theorem positivePart_add_le (x y : ℝ) :
    positivePart (x+y) ≤ positivePart x+positivePart y := by
  unfold positivePart
  exact max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
    (add_nonneg (le_max_right _ _) (le_max_right _ _))

theorem negativePart_add_le (x y : ℝ) :
    negativePart (x+y) ≤ negativePart x+negativePart y := by
  have h := positivePart_add_le (-x) (-y)
  unfold positivePart at h
  unfold negativePart
  rwa [neg_add]

theorem variations_equal (θ : Vertex → ℝ) : positiveVariation θ=negativeVariation θ := by
  have h : positiveVariation θ-negativeVariation θ=∑ i,delta θ i := by
    rw [positiveVariation,negativeVariation,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact positive_sub_negative _
  have hs : ∑ i,delta θ i=0 := by
    have h1 : ∑ i,delta θ i= -∑ i,(θ i-θ (next i)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [delta,neg_sub]
    rw [h1,sum_marker_difference,neg_zero]
  rw [hs] at h
  linarith

theorem positive_error_le_variation (θ : Vertex → ℝ) (i : Vertex) :
    positivePart (delta θ i) ≤ positiveVariation θ := by
  exact Finset.single_le_sum (fun j _ => positivePart_nonneg _) (Finset.mem_univ i)

theorem negative_error_le_variation (θ : Vertex → ℝ) (i : Vertex) :
    negativePart (delta θ i) ≤ negativeVariation θ := by
  exact Finset.single_le_sum (fun j _ => negativePart_nonneg _) (Finset.mem_univ i)

theorem reflected_positiveVariation (C : SignedCycle) :
    positiveVariation C.reflected.theta=positiveVariation C.theta := by
  simp only [positiveVariation,SignedCycle.reflected_delta]
  simp [Fin.sum_univ_succ,SignedCycle.reflectedIndex,next]
  ring

theorem reflected_negativeVariation (C : SignedCycle) :
    negativeVariation C.reflected.theta=negativeVariation C.theta := by
  simp only [negativeVariation,SignedCycle.reflected_delta]
  simp [Fin.sum_univ_succ,SignedCycle.reflectedIndex,next]
  ring

end SquaresInCircles.Eight