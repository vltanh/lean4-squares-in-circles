import SquaresInCircles.Six.Stress.Support
import SquaresInCircles.Seven.SeparatingAxes

/-!
# Finite reverse stresses

The algebraic incidence identity is proved once. Every application supplies
actual selected separator inequalities and proved support bounds. Thresholds
may be weakened, but their inequalities must still be proved at the call site.
Equality propagation is part of the theorem, not a separate rigidity oracle.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress

structure System (n m : ℕ) where
  source : Fin m → Fin n
  target : Fin m → Fin n
  normal : Fin m → Point
  weight : Fin m → ℝ
  threshold : Fin m → ℝ

namespace System
variable {n m : ℕ}

def force (E : System n m) (i : Fin n) : Point :=
  ((∑ e, if E.target e=i then E.weight e*(E.normal e).1 else 0)-
     ∑ e, if E.source e=i then E.weight e*(E.normal e).1 else 0,
   (∑ e, if E.target e=i then E.weight e*(E.normal e).2 else 0)-
     ∑ e, if E.source e=i then E.weight e*(E.normal e).2 else 0)

def thresholdSum (E : System n m) : ℝ := ∑ e, E.weight e*E.threshold e

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

/-- The force on each square is exactly the incidence sum of the chosen edges. -/
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

/-- The reverse-stress inequality for any supplied valid upper supports. -/
theorem bound (E : System n m) (S : Fin n → UnitSquare) (U : Fin n → ℝ)
    (hn : E.Nonnegative) (hs : E.Separates S)
    (hu : ∀ i, dot (E.force i) (S i).center ≤ U i) : E.thresholdSum ≤ ∑ i, U i :=
  (E.threshold_le_forces S hn hs).trans (Finset.sum_le_sum (fun i _ => hu i))

theorem defect_nonpos (E : System n m) (S : Fin n → UnitSquare) (U : Fin n → ℝ)
    (hn : E.Nonnegative) (hs : E.Separates S)
    (hu : ∀ i, dot (E.force i) (S i).center ≤ U i) :
    E.thresholdSum-(∑ i, U i) ≤ 0 := sub_nonpos.mpr (E.bound S U hn hs hu)

/-- Equality in the reverse stress forces every support inequality to be tight. -/
theorem support_tight (E : System n m) (S : Fin n → UnitSquare) (U : Fin n → ℝ)
    (hn : E.Nonnegative) (hs : E.Separates S)
    (hu : ∀ i, dot (E.force i) (S i).center ≤ U i)
    (heq : E.thresholdSum = ∑ i, U i) (i : Fin n) :
    dot (E.force i) (S i).center = U i := by
  have hb := E.threshold_le_forces S hn hs
  have hnslack (j : Fin n) : 0 ≤ U j-dot (E.force j) (S j).center := sub_nonneg.mpr (hu j)
  have hsingle : U i-dot (E.force i) (S i).center ≤
      ∑ j, (U j-dot (E.force j) (S j).center) :=
    Finset.single_le_sum (fun j _ => hnslack j) (Finset.mem_univ i)
  rw [Finset.sum_sub_distrib] at hsingle
  linarith [hu i]

/-- Positive edge multipliers also force the corresponding separating contact. -/
theorem separator_tight (E : System n m) (S : Fin n → UnitSquare) (U : Fin n → ℝ)
    (hn : E.Nonnegative) (hs : E.Separates S)
    (hu : ∀ i, dot (E.force i) (S i).center ≤ U i)
    (heq : E.thresholdSum = ∑ i, U i) (e : Fin m) (hw : 0 < E.weight e) :
    dot (E.normal e) (sub (S (E.target e)).center (S (E.source e)).center) = E.threshold e := by
  let slack : Fin m → ℝ := fun j => E.weight j*
    (dot (E.normal j) (sub (S (E.target j)).center (S (E.source j)).center)-E.threshold j)
  have hnonneg (j : Fin m) : 0 ≤ slack j := mul_nonneg (hn j) (sub_nonneg.mpr (hs j))
  have hsum : (∑ j, slack j) ≤ 0 := by
    have hf := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hu i)
    rw [E.balance] at hf
    have hid : (∑ j, slack j) =
        (∑ j, E.weight j*dot (E.normal j)
          (sub (S (E.target j)).center (S (E.source j)).center))-E.thresholdSum := by
      simp only [slack,mul_sub,Finset.sum_sub_distrib,thresholdSum]
    rw [hid]
    linarith
  have hone := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hnonneg j) (Finset.mem_univ e)
  have hzero : slack e=0 := by linarith [hnonneg e]
  dsimp [slack] at hzero
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (ne_of_gt hw))

end System

/-- The eight directed source axes; signs are retained rather than guessed. -/
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
