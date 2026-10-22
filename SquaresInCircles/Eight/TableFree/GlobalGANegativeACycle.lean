module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeAReduction
public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDSource

/-!
# The A-normalization is a necessary-system transport, not a new packing

Uncompiled transcription of the scope and provenance assertions in
Sections 4--7 of the mixed-negative-A note. Only A's point and frame
change. The other five original edge inequalities, all other points,
and all other frames are retained literally. Positive and negative
variation do not increase when A is placed at either adjacent frame.
No marker or physical order theorem is applied to the transported data.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeANormalForm
open Candidate Secondary

def replace (C : SignedCycle) (P : SignedPoint) (t : ℝ) : SignedCycle :=
  { C with point := Function.update C.point A P, theta := Function.update C.theta A t }

@[simp] theorem replace_point_A (C : SignedCycle) (P : SignedPoint) (t : ℝ) :
    (replace C P t).point A=P := by simp [replace]

@[simp] theorem replace_theta_A (C : SignedCycle) (P : SignedPoint) (t : ℝ) :
    (replace C P t).theta A=t := by simp [replace]

theorem replace_point_other (C : SignedCycle) (P : SignedPoint) (t : ℝ)
    {i : Vertex} (hi : i≠A) : (replace C P t).point i=C.point i := by simp [replace,hi]

theorem replace_theta_other (C : SignedCycle) (P : SignedPoint) (t : ℝ)
    {i : Vertex} (hi : i≠A) : (replace C P t).theta i=C.theta i := by simp [replace,hi]

theorem replace_delta_other (C : SignedCycle) (P : SignedPoint) (t : ℝ)
    {i : Vertex} (hi : i≠G ∧ i≠A) : delta (replace C P t).theta i=delta C.theta i := by
  fin_cases i <;> simp [replace,delta,next,G,A] at hi ⊢

theorem replace_edge_other (C : SignedCycle) (P : SignedPoint) (t : ℝ)
    {i : Vertex} (hi : i≠G ∧ i≠A) (j : Fin 4) :
    (replace C P t).edge i j=C.edge i j := by
  fin_cases i <;> simp [SignedCycle.edge,replace,delta,next,G,A] at hi ⊢

theorem replace_feasible_other (C : SignedCycle) (P : SignedPoint) (t : ℝ)
    {i : Vertex} (hi : i≠G ∧ i≠A) (j : Fin 4) :
    (replace C P t).Feasible i j ↔ C.Feasible i j := by
  simp only [SignedCycle.Feasible,SignedCycle.slack,replace_edge_other C P t hi j,
    replace_delta_other C P t hi]

theorem replace_GA (C : SignedCycle) (P : SignedPoint) (t : ℝ) (j : Fin 4) :
    (replace C P t).Feasible G j ↔ quarterFeasible (C.point G) P (t-C.theta G) j := by
  simp [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,replace,
    quarterFeasible,word,delta,next,G,A,sub_nonneg]

theorem replace_AB (C : SignedCycle) (P : SignedPoint) (t : ℝ) (j : Fin 4) :
    (replace C P t).Feasible A j ↔ zeroFeasible P (C.point B) (C.theta B-t) j := by
  simp [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,replace,
    zeroFeasible,word,delta,next,A,B,sub_nonneg]

theorem positivePart_add (u v : ℝ) : positivePart (u+v)≤positivePart u+positivePart v := by
  unfold positivePart
  apply max_le
  · exact add_le_add (le_max_left _ _) (le_max_left _ _)
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

theorem variation_identity (C : SignedCycle) (P : SignedPoint) (t : ℝ) :
    positiveVariation (replace C P t).theta+positivePart (delta C.theta G)+positivePart (delta C.theta A)=
      positiveVariation C.theta+positivePart (t-C.theta G)+positivePart (C.theta B-t) := by
  norm_num [positiveVariation,Fin.sum_univ_succ,replace,delta,next,G,A,B]
  ring

theorem variation_nonincreasing (C : SignedCycle) (P : SignedPoint) {t : ℝ}
    (ht : t=C.theta A ∨ t=C.theta G ∨ t=C.theta B) :
    positiveVariation (replace C P t).theta≤positiveVariation C.theta := by
  have hid := variation_identity C P t
  have htriangle := positivePart_add (C.theta A-C.theta G) (C.theta B-C.theta A)
  have he : (C.theta A-C.theta G)+(C.theta B-C.theta A)=C.theta B-C.theta G := by ring
  rw [he] at htriangle
  rcases ht with rfl|rfl|rfl
  · dsimp [delta,G,A,B,next] at hid
    linarith
  · simp only [sub_self,positivePart_zero,add_zero] at hid
    dsimp [delta,G,A,B,next] at hid
    linarith
  · simp only [sub_self,positivePart_zero,add_zero] at hid
    dsimp [delta,G,A,B,next] at hid
    linarith

theorem negative_variation_nonincreasing (C : SignedCycle) (P : SignedPoint) {t : ℝ}
    (ht : t=C.theta A ∨ t=C.theta G ∨ t=C.theta B) :
    negativeVariation (replace C P t).theta≤negativeVariation C.theta := by
  rw [←variations_equal,←variations_equal]
  exact variation_nonincreasing C P ht

theorem strict_spread_preserved {C : SignedCycle} (P : SignedPoint) {t : ℝ}
    (hs : C.StrictSpread) (ht : t=C.theta A ∨ t=C.theta G ∨ t=C.theta B) :
    (replace C P t).StrictSpread := by
  intro i j
  by_cases hi : i=A <;> by_cases hj : j=A
  · subst i
    subst j
    simp [replace,frameCap]
  · subst i
    rw [replace_theta_A,replace_theta_other C P t hj]
    rcases ht with rfl|rfl|rfl
    · exact hs A j
    · exact hs G j
    · exact hs B j
  · subst j
    rw [replace_theta_other C P t hi,replace_theta_A]
    rcases ht with rfl|rfl|rfl
    · exact hs i A
    · exact hs i G
    · exact hs i B
  · rw [replace_theta_other C P t hi,replace_theta_other C P t hj]
    exact hs i j

structure CycleResult (Q : ℝ) (C : SignedCycle) where
  cycle : SignedCycle
  ga : Bool
  ab : Bool
  necessary : cycle.Necessary Q
  radial : ∀i,(cycle.point i).Boundary Q
  tangent_upper : (cycle.point A).y<1/2
  point_other : ∀i,i≠A → cycle.point i=C.point i
  theta_other : ∀i,i≠A → cycle.theta i=C.theta i
  theta_A : cycle.theta A=C.theta A ∨ cycle.theta A=C.theta G ∨ cycle.theta A=C.theta B
  other_edges : ∀i,i≠G ∧ i≠A → ∀j,cycle.Feasible i j ↔ C.Feasible i j
  variation : positiveVariation cycle.theta≤positiveVariation C.theta
  GA : cycle.Feasible G (if ga then 3 else 2)
  AB : cycle.Feasible A (if ab then 2 else 0)
  reduced : Reduced (cycle.point A) ga ab (delta cycle.theta G) (delta cycle.theta A)

def Result.toCycle {Q : ℝ} {C : SignedCycle}
    (R : Result Q (C.point G) (C.point A) (C.point B) (C.theta G) (C.theta A) (C.theta B))
    (hn : C.Necessary Q) (hr : ∀i,(C.point i).Boundary Q) : CycleResult Q C where
  cycle := replace C R.point R.theta
  ga := R.ga
  ab := R.ab
  necessary := {
    sorted := by
      intro i
      by_cases hi : i=A
      · subst i
        simpa using R.sorted
      · simpa [replace,hi] using hn.sorted i
    contained := by
      intro i
      by_cases hi : i=A
      · subst i
        simpa using R.contained
      · simpa [replace,hi] using hn.contained i
    core := by
      intro i
      by_cases hi : i=A
      · subst i
        simpa using R.core
      · simpa [replace,hi] using hn.core i }
  radial := by
    intro i
    by_cases hi : i=A
    · subst i
      simpa using R.radial
    · simpa [replace,hi] using hr i
  tangent_upper := by simpa using R.tangent_upper
  point_other := fun i hi => replace_point_other C R.point R.theta hi
  theta_other := fun i hi => replace_theta_other C R.point R.theta hi
  theta_A := by simpa using R.frame
  other_edges := fun i hi j => replace_feasible_other C R.point R.theta hi j
  variation := variation_nonincreasing C R.point R.frame
  GA := (replace_GA C R.point R.theta _).2 R.GA
  AB := (replace_AB C R.point R.theta _).2 R.AB
  reduced := by
    simpa [replace,delta,next,G,A,B] using R.reduced

theorem cycle_reduce {Q : ℝ} {C : SignedCycle} (ga ab : Bool)
    (hQlo : (5/2:ℝ)≤Q) (hQ : Q≤qCap)
    (hn : C.Necessary Q) (hr : ∀i,(C.point i).Boundary Q)
    (hGy : (C.point G).y≤0) (hBo : (C.point B).Outer Q) (hBy : (C.point B).y≤0)
    (hAy : (C.point A).y<1/2) (hAouter : (C.point A).y≤0 → (C.point A).Outer Q)
    (hs : C.StrictSpread)
    (hGA : C.Feasible G (if ga then 3 else 2)) (hAB : C.Feasible A (if ab then 2 else 0)) :
    Nonempty (CycleResult Q C) := by
  have hGA' : quarterFeasible (C.point G) (C.point A) (C.theta A-C.theta G) (if ga then 3 else 2) := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,delta,next,G,A,sub_nonneg] using hGA
  have hAB' : zeroFeasible (C.point A) (C.point B) (C.theta B-C.theta A) (if ab then 2 else 0) := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,delta,next,A,B,sub_nonneg] using hAB
  obtain ⟨R⟩ := reduce ga ab hQlo hQ (hn.sorted G) (hn.contained G) (hn.core G) hGy
    (hn.sorted A) (hn.contained A) (hn.core A) (hr A) hAy hAouter
    (hn.sorted B) (hn.contained B) (hn.core B) hBo hBy (hs A G).le (hs B A).le (hs G B).le hGA' hAB'
  exact ⟨R.toCycle hn hr⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeANormalForm
