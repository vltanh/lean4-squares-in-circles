module

public import SquaresInCircles.Eight.TableFree.LossLedger

/-!
# Signed variation under actual endpoint alignment

Uncompiled draft. The two incident errors are changed as a pair. Their sum
is invariant. Positive and negative variation are each controlled, not just
the sum of their absolute values. In particular a negative source error
cannot disappear from an equality argument by cancellation on the other edge.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree
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

/-- Either endpoint alignment replaces the two errors by their sum and zero. -/
theorem endpoint_variation_le (x y : ℝ) :
    positivePart (x+y)+positivePart 0 ≤ positivePart x+positivePart y ∧
      negativePart (x+y)+negativePart 0 ≤ negativePart x+negativePart y := by
  simpa using And.intro (positivePart_add_le x y) (negativePart_add_le x y)

theorem same_sign_positive_variation {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    positivePart (x+y)=positivePart x+positivePart y ∧
      negativePart (x+y)=negativePart x+negativePart y := by
  unfold positivePart negativePart
  rw [max_eq_left hx,max_eq_left hy,max_eq_left (add_nonneg hx hy),
    max_eq_right (by linarith : -x ≤ 0),max_eq_right (by linarith : -y ≤ 0),
    max_eq_right (by linarith : -(x+y) ≤ 0)]
  exact ⟨rfl,(add_zero 0).symm⟩

theorem canceled_negative_loss {x y : ℝ} (hx : x ≤ 0) (hy : 0 ≤ y)
    (ht : 0 ≤ x+y) :
    positivePart x+positivePart y-positivePart (x+y)= -x ∧
      negativePart x+negativePart y-negativePart (x+y)= -x := by
  unfold positivePart negativePart
  rw [max_eq_right hx,max_eq_left hy,max_eq_left ht,
    max_eq_left (by linarith : 0 ≤ -x),max_eq_right (by linarith : -y ≤ 0),
    max_eq_right (by linarith : -(x+y) ≤ 0)]
  constructor <;> ring

/-- The wrong-sign nonpositive-total move removes the same amount from both
variations, including the exact zero-total boundary. -/
theorem wrong_sign_pair_variation {v z : ℝ} (hv : 0 ≤ v) (hvz : v ≤ z) :
    positivePart v+positivePart (-z)-positivePart (v-z)=v ∧
      negativePart v+negativePart (-z)-negativePart (v-z)=v := by
  unfold positivePart negativePart
  rw [max_eq_left hv,max_eq_right (by linarith : -z ≤ 0),
    max_eq_right (by linarith : v-z ≤ 0),max_eq_right (by linarith : -v ≤ 0),
    max_eq_left (by linarith : (0:ℝ) ≤ -(-z)),max_eq_left (by linarith : 0 ≤ -(v-z))]
  constructor <;> ring

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

/-- A G replacement cannot alter the error or slack on a nonincident edge. -/
theorem replacement_edge_unchanged (C : SignedCycle) (k i : Vertex)
    (p : SignedPoint) (t : ℝ) (hi : i≠k) (hj : next i≠k) (j : Fin 4) :
    (replacePoint C k p t).slack i j=C.slack i j := by
  simp [replacePoint,SignedCycle.slack,SignedCycle.edge,delta,
    Function.update_of_ne hi,Function.update_of_ne hj]

theorem g_alignment_variations (C : SignedCycle) (p : SignedPoint)
    {t : ℝ} (ht : t=C.theta H ∨ t=C.theta A) :
    positiveVariation (replacePoint C G p t).theta ≤ positiveVariation C.theta ∧
      negativeVariation (replacePoint C G p t).theta ≤ negativeVariation C.theta := by
  have hp := positivePart_add_le (C.theta 1-C.theta 0) (C.theta 2-C.theta 1)
  have hn := negativePart_add_le (C.theta 1-C.theta 0) (C.theta 2-C.theta 1)
  have he : (C.theta 1-C.theta 0)+(C.theta 2-C.theta 1)=C.theta 2-C.theta 0 := by ring
  rw [he] at hp hn
  rcases ht with rfl | rfl <;>
    simp [positiveVariation,negativeVariation,Fin.sum_univ_succ,delta,next,
      replacePoint,H,G,A,Function.update_apply] <;> constructor <;> linarith

theorem t_alignment_variations (C : SignedCycle) (p : SignedPoint)
    {t : ℝ} (ht : t=C.theta B ∨ t=C.theta D) :
    positiveVariation (replacePoint C T p t).theta ≤ positiveVariation C.theta ∧
      negativeVariation (replacePoint C T p t).theta ≤ negativeVariation C.theta := by
  have hp := positivePart_add_le (C.theta 4-C.theta 3) (C.theta 5-C.theta 4)
  have hn := negativePart_add_le (C.theta 4-C.theta 3) (C.theta 5-C.theta 4)
  have he : (C.theta 4-C.theta 3)+(C.theta 5-C.theta 4)=C.theta 5-C.theta 3 := by ring
  rw [he] at hp hn
  rcases ht with rfl | rfl <;>
    simp [positiveVariation,negativeVariation,Fin.sum_univ_succ,delta,next,
      replacePoint,B,T,D,Function.update_apply] <;> constructor <;> linarith

/-- Normalization subtracts a common angle and changes no edge error. -/
theorem delta_common_shift (θ : Vertex → ℝ) (a : ℝ) (i : Vertex) :
    delta (fun j => θ j-a) i=delta θ i := by
  unfold delta
  ring

/-- Reflection permutes edges while reversing the geometric traversal.
The individual signed error is preserved, not negated. -/
theorem reflected_error_table (C : SignedCycle) :
    (fun i => delta C.reflected.theta i)=
      ![delta C.theta 4,delta C.theta 3,delta C.theta 2,
        delta C.theta 1,delta C.theta 0,delta C.theta 6,delta C.theta 5] := by
  funext i
  fin_cases i <;> simp [SignedCycle.reflected_delta,SignedCycle.reflectedIndex,next]

end SquaresInCircles.Eight.TableFree