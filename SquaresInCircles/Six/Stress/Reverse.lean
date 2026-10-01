import SquaresInCircles.Six.Stress.Support
import SquaresInCircles.Seven.SeparatingAxes

/-!
# Stresses

A stress on `n` squares is a list of `m` edges, each with a source, a target, a
normal, a weight and a threshold. It separates a configuration if the centre of
each target lies at least the threshold beyond the centre of its source along
the normal. The force on a square is the sum of the weighted normals of the
edges into it minus that of the edges out of it. Summing by squares instead of
edges gives `balance`, and with nonnegative weights the threshold sum of a
separating stress is at most any upper bound for the total work of the forces
on the centres (`bound`). Two squares with disjoint interiors are separated
along one of the eight directed axes of the pair (`directed_pair_separator`).
-/

noncomputable section
namespace SquaresInCircles.Six.Stress

/-- A stress on `n` squares with `m` edges: the source, target, normal, weight
and threshold of each edge. -/
structure System (n m : ℕ) where
  source : Fin m → Fin n
  target : Fin m → Fin n
  normal : Fin m → Point
  weight : Fin m → ℝ
  threshold : Fin m → ℝ

namespace System
variable {n m : ℕ}

/-- The force on square `i`: the weighted normals of the edges into `i` minus
those of the edges out of `i`. -/
def force (E : System n m) (i : Fin n) : Point :=
  ((∑ e, if E.target e=i then E.weight e*(E.normal e).1 else 0)-
     ∑ e, if E.source e=i then E.weight e*(E.normal e).1 else 0,
   (∑ e, if E.target e=i then E.weight e*(E.normal e).2 else 0)-
     ∑ e, if E.source e=i then E.weight e*(E.normal e).2 else 0)

def thresholdSum (E : System n m) : ℝ := ∑ e, E.weight e*E.threshold e

/-- The squares `S` satisfy the separating inequality of every edge. -/
def Separates (E : System n m) (S : Fin n → UnitSquare) : Prop :=
  ∀ e, E.threshold e ≤ dot (E.normal e) (sub (S (E.target e)).center (S (E.source e)).center)

def Nonnegative (E : System n m) : Prop := ∀ e, 0 ≤ E.weight e

private lemma incidence_sum (f : Fin m → Fin n) (w : Fin m → ℝ) (p : Fin n → ℝ) :
    (∑ i, (∑ e, if f e=i then w e else 0)*p i) = ∑ e, w e*p (f e) := by
  classical
  calc
    (∑ i, (∑ e, if f e=i then w e else 0)*p i) =
        ∑ i, ∑ e, if f e=i then w e*p i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> simp
    _ = ∑ e, ∑ i, if f e=i then w e*p i else 0 := Finset.sum_comm
    _ = ∑ e, w e*p (f e) := by simp

/-- For any points `p i`, the sum of the works `⟨force i, p i⟩` is the weighted
sum over the edges of the normal components of `p (target e) - p (source e)`. -/
theorem balance (E : System n m) (p : Fin n → Point) :
    (∑ i, dot (E.force i) (p i)) =
      ∑ e, E.weight e*dot (E.normal e) (sub (p (E.target e)) (p (E.source e))) := by
  classical
  calc
    (∑ i, dot (E.force i) (p i)) =
        ((∑ i, (∑ e, if E.target e=i then E.weight e*(E.normal e).1 else 0)*(p i).1)-
          ∑ i, (∑ e, if E.source e=i then E.weight e*(E.normal e).1 else 0)*(p i).1)+
        ((∑ i, (∑ e, if E.target e=i then E.weight e*(E.normal e).2 else 0)*(p i).2)-
          ∑ i, (∑ e, if E.source e=i then E.weight e*(E.normal e).2 else 0)*(p i).2) := by
      simp only [force,dot,sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    _ = ((∑ e, E.weight e*(E.normal e).1*(p (E.target e)).1)-
          ∑ e, E.weight e*(E.normal e).1*(p (E.source e)).1)+
        ((∑ e, E.weight e*(E.normal e).2*(p (E.target e)).2)-
          ∑ e, E.weight e*(E.normal e).2*(p (E.source e)).2) := by
      rw [incidence_sum,incidence_sum,incidence_sum,incidence_sum]
    _ = ∑ e, E.weight e*dot (E.normal e) (sub (p (E.target e)) (p (E.source e))) := by
      rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      dsimp [dot,sub]
      ring

lemma threshold_le_forces (E : System n m) (S : Fin n → UnitSquare)
    (hn : E.Nonnegative) (hs : E.Separates S) :
    E.thresholdSum ≤ ∑ i, dot (E.force i) (S i).center := by
  rw [E.balance]
  exact Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (hs e) (hn e))

/-- With nonnegative weights, the threshold sum of a separating stress is at
most the sum of any upper bounds `U` for the works of the forces. -/
theorem bound (E : System n m) (S : Fin n → UnitSquare) (U : Fin n → ℝ)
    (hn : E.Nonnegative) (hs : E.Separates S)
    (hu : ∀ i, dot (E.force i) (S i).center ≤ U i) : E.thresholdSum ≤ ∑ i, U i :=
  (E.threshold_le_forces S hn hs).trans (Finset.sum_le_sum (fun i _ => hu i))

theorem defect_nonpos (E : System n m) (S : Fin n → UnitSquare) (U : Fin n → ℝ)
    (hn : E.Nonnegative) (hs : E.Separates S)
    (hu : ∀ i, dot (E.force i) (S i).center ≤ U i) :
    E.thresholdSum-(∑ i, U i) ≤ 0 := sub_nonpos.mpr (E.bound S U hn hs hu)

end System

/-- The eight directed axes of a pair of squares: each frame axis of `S` and of
`T`, in both directions. -/
def pairNormal (i : Fin 8) (S T : UnitSquare) : Point :=
  ![normalX S,scale (-1) (normalX S),normalY S,scale (-1) (normalY S),
    normalX T,scale (-1) (normalX T),normalY T,scale (-1) (normalY T)] i

lemma directed_pair_separator (S T : UnitSquare)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) :
    ∃ i : Fin 8, Seven.SAT.threshold S T ≤ dot (pairNormal i S T) (sub T.center S.center) := by
  have hs := Seven.SAT.separating_axes S T hd
  rcases hs with hs | hs | hs | hs
  · by_cases h : 0 ≤ frameX S (sub T.center S.center)
    · rw [abs_of_nonneg h] at hs
      exact ⟨0,by simpa [pairNormal,normalX,frameX,dot] using hs⟩
    · rw [abs_of_neg (lt_of_not_ge h)] at hs
      exact ⟨1,by simp [pairNormal,normalX,frameX,dot,scale] at hs ⊢; linarith⟩
  · by_cases h : 0 ≤ frameY S (sub T.center S.center)
    · rw [abs_of_nonneg h] at hs
      exact ⟨2,by simpa [pairNormal,normalY,frameY,dot] using hs⟩
    · rw [abs_of_neg (lt_of_not_ge h)] at hs
      exact ⟨3,by simp [pairNormal,normalY,frameY,dot,scale] at hs ⊢; linarith⟩
  · by_cases h : 0 ≤ frameX T (sub T.center S.center)
    · rw [abs_of_nonneg h] at hs
      exact ⟨4,by simpa [pairNormal,normalX,frameX,dot] using hs⟩
    · rw [abs_of_neg (lt_of_not_ge h)] at hs
      exact ⟨5,by simp [pairNormal,normalX,frameX,dot,scale] at hs ⊢; linarith⟩
  · by_cases h : 0 ≤ frameY T (sub T.center S.center)
    · rw [abs_of_nonneg h] at hs
      exact ⟨6,by simpa [pairNormal,normalY,frameY,dot] using hs⟩
    · rw [abs_of_neg (lt_of_not_ge h)] at hs
      exact ⟨7,by simp [pairNormal,normalY,frameY,dot,scale] at hs ⊢; linarith⟩

end SquaresInCircles.Six.Stress
