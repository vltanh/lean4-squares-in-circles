import SquaresInCircles.Six.Analytic.RectangleWallReduction
import SquaresInCircles.Six.Analytic.FixedPairPolynomialBound

/-!
# The pair gap at the endpoints

The concavity reduction leaves the gap to be checked at the points of the domain
rectangle whose coordinates are endpoints of their intervals or zero, and at the
points where the diagonal `n = w` meets a side or an axis. At the origin the gap
is zero for the sources `0` and `3`, which carry the contact N–W of the model,
by `pairBase_vertex_identity`. At every other such point, and at the origin for
the other two sources, `EndpointAlgebra` holds by rational arithmetic, so the
gap is positive there. This gives `EndpointCondition` for every source axis and
every choice of separators of N and W.
-/
noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization FixedPair.Polynomial PairTaylor

def northEndpoint (no : Bool) : Fin 3 → ℝ := ![(northLo no:ℝ),0,(northHi no:ℝ)]
def westEndpoint (wo : Bool) : Fin 3 → ℝ := ![(westLo wo:ℝ),0,(westHi wo:ℝ)]

def diagonalEndpoint (no wo : Bool) : Fin 3 → ℝ :=
  ![max (northLo no:ℝ) (westLo wo:ℝ),0,min (northHi no:ℝ) (westHi wo:ℝ)]

/-- Unfolds `EndpointAlgebra` at an endpoint and checks it by rational
arithmetic. -/
macro "pair_endpoint_rational" : tactic =>
  `(tactic| norm_num [EndpointAlgebra,budget,linearPart,squareN,squareW,
    northSquare,westSquare,northScale,northVector,westVector,baseVector,
    northSource,westSource,thresholdP,halfWidth,penaltyP,
    rApprox,mApprox,cApprox,circleUpper,radialUpper,baseUpper,
    PairTaylor.sinP,PairTaylor.cosP,line,northEndpoint,westEndpoint,diagonalEndpoint,
    northLo,northHi,westLo,westHi] at *)

/-- `EndpointAlgebra` at the corners, one lemma for each choice of separators. -/
private lemma corner_algebra_ff (u : Fin 4) (i j : Fin 3)
    (h : i≠1 ∨ j≠1 ∨ u=1 ∨ u=2) :
    EndpointAlgebra false false u (northEndpoint false i) (westEndpoint false j) := by
  fin_cases u <;> fin_cases i <;> fin_cases j
  all_goals pair_endpoint_rational

private lemma corner_algebra_ft (u : Fin 4) (i j : Fin 3)
    (h : i≠1 ∨ j≠1 ∨ u=1 ∨ u=2) :
    EndpointAlgebra false true u (northEndpoint false i) (westEndpoint true j) := by
  fin_cases u <;> fin_cases i <;> fin_cases j
  all_goals pair_endpoint_rational

private lemma corner_algebra_tf (u : Fin 4) (i j : Fin 3)
    (h : i≠1 ∨ j≠1 ∨ u=1 ∨ u=2) :
    EndpointAlgebra true false u (northEndpoint true i) (westEndpoint false j) := by
  fin_cases u <;> fin_cases i <;> fin_cases j
  all_goals pair_endpoint_rational

private lemma corner_algebra_tt (u : Fin 4) (i j : Fin 3)
    (h : i≠1 ∨ j≠1 ∨ u=1 ∨ u=2) :
    EndpointAlgebra true true u (northEndpoint true i) (westEndpoint true j) := by
  fin_cases u <;> fin_cases i <;> fin_cases j
  all_goals pair_endpoint_rational

/-- `EndpointAlgebra` holds at the corners and axis points of the rectangle,
except at the origin for the sources `0` and `3`. -/
lemma corner_algebra (no wo : Bool) (u : Fin 4) (i j : Fin 3)
    (h : i≠1 ∨ j≠1 ∨ u=1 ∨ u=2) :
    EndpointAlgebra no wo u (northEndpoint no i) (westEndpoint wo j) := by
  cases no <;> cases wo
  exacts [corner_algebra_ff u i j h,corner_algebra_ft u i j h,
    corner_algebra_tf u i j h,corner_algebra_tt u i j h]

lemma diagonal_algebra (no wo : Bool) (u : Fin 4) (i : Fin 3)
    (h : i≠1 ∨ u=1 ∨ u=2) :
    EndpointAlgebra no wo u (diagonalEndpoint no wo i) (diagonalEndpoint no wo i) := by
  cases no <;> cases wo <;> fin_cases u <;> fin_cases i
  all_goals pair_endpoint_rational

lemma corner_in_domain (no wo : Bool) (i j : Fin 3) :
    Domain no wo (northEndpoint no i) (westEndpoint wo j) := by
  cases no <;> cases wo <;> fin_cases i <;> fin_cases j <;>
    norm_num [Domain,northEndpoint,westEndpoint,northLo,northHi,westLo,westHi]

lemma diagonal_in_domain (no wo : Bool) (i : Fin 3) :
    Domain no wo (diagonalEndpoint no wo i) (diagonalEndpoint no wo i) := by
  cases no <;> cases wo <;> fin_cases i <;>
    norm_num [Domain,diagonalEndpoint,northLo,northHi,westLo,westHi]

lemma origin_in_domain (no wo : Bool) : Domain no wo 0 0 := by
  cases no <;> cases wo <;> norm_num [Domain]

lemma candidate_gap_origin (no wo : Bool) {u : Fin 4} (hu : u=0 ∨ u=3) :
    gap no wo u 0 0=0 := by
  rw [gap,minorant_zero no wo hu]
  norm_num [line]

lemma alternate_gap_origin (no wo : Bool) {u : Fin 4} (hu : u=1 ∨ u=2) :
    0<gap no wo u 0 0 := by
  have he := corner_algebra no wo u 1 1 (Or.inr (Or.inr hu))
  apply positive_of_endpoint_algebra (origin_in_domain no wo)
  simpa only [northEndpoint,westEndpoint,Matrix.cons_val_one,Matrix.cons_val_zero] using he

lemma gap_origin_nonnegative (no wo : Bool) (u : Fin 4) : 0≤gap no wo u 0 0 := by
  by_cases hu : u=0 ∨ u=3
  · rw [candidate_gap_origin no wo hu]
  · have halt : u=1 ∨ u=2 := by omega
    exact (alternate_gap_origin no wo halt).le

lemma corner_nonnegative (no wo : Bool) (u : Fin 4) (i j : Fin 3) :
    0≤gap no wo u (northEndpoint no i) (westEndpoint wo j) := by
  by_cases hi : i=1
  · by_cases hj : j=1
    · subst i
      subst j
      exact gap_origin_nonnegative no wo u
    · exact (positive_of_endpoint_algebra (corner_in_domain no wo i j)
        (corner_algebra no wo u i j (Or.inr (Or.inl hj)))).le
  · exact (positive_of_endpoint_algebra (corner_in_domain no wo i j)
      (corner_algebra no wo u i j (Or.inl hi))).le

lemma diagonal_nonnegative (no wo : Bool) (u : Fin 4) (i : Fin 3) :
    0≤gap no wo u (diagonalEndpoint no wo i) (diagonalEndpoint no wo i) := by
  by_cases hi : i=1
  · subst i
    exact gap_origin_nonnegative no wo u
  · exact (positive_of_endpoint_algebra (diagonal_in_domain no wo i)
      (diagonal_algebra no wo u i (Or.inl hi))).le

lemma north_boundary_index (no : Bool) {n : ℝ}
    (hn : AxisBoundary (northLo no) (northHi no) n) :
    ∃ i : Fin 3, n=northEndpoint no i := by
  rcases hn with rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩

lemma west_boundary_index (wo : Bool) {w : ℝ}
    (hw : AxisBoundary (westLo wo) (westHi wo) w) :
    ∃ i : Fin 3, w=westEndpoint wo i := by
  rcases hw with rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩

/-- A point of the diagonal on a side or an axis of the rectangle is one of the
three diagonal endpoints. -/
lemma diagonal_boundary_index (no wo : Bool) {z : ℝ}
    (hd : Domain no wo z z)
    (hb : AxisBoundary (northLo no) (northHi no) z ∨
      AxisBoundary (westLo wo) (westHi wo) z) :
    ∃ i : Fin 3, z=diagonalEndpoint no wo i := by
  have hr := (domain_iff_rectangle no wo z z).mp hd
  rcases hb with hn | hw
  · rcases hn with h | h | h
    · refine ⟨0,?_⟩
      have hm : max (northLo no:ℝ) (westLo wo:ℝ)=northLo no :=
        max_eq_left (by linarith [hr.2.1])
      simpa only [diagonalEndpoint,hm,Matrix.cons_val_zero] using h
    · exact ⟨1,h⟩
    · refine ⟨2,?_⟩
      have hm : min (northHi no:ℝ) (westHi wo:ℝ)=northHi no :=
        min_eq_left (by linarith [hr.2.2])
      simpa only [diagonalEndpoint,hm,Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons] using h
  · rcases hw with h | h | h
    · refine ⟨0,?_⟩
      have hm : max (northLo no:ℝ) (westLo wo:ℝ)=westLo wo :=
        max_eq_right (by linarith [hr.1.1])
      simpa only [diagonalEndpoint,hm,Matrix.cons_val_zero] using h
    · exact ⟨1,h⟩
    · refine ⟨2,?_⟩
      have hm : min (northHi no:ℝ) (westHi wo:ℝ)=westHi wo :=
        min_eq_right (by linarith [hr.1.2])
      simpa only [diagonalEndpoint,hm,Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons] using h

/-- The gap is nonnegative at all the endpoints of the concavity reduction. -/
theorem endpoint_condition (no wo : Bool) (u : Fin 4) : EndpointCondition no wo u := by
  constructor
  · intro n w hn hw
    obtain ⟨i,rfl⟩ := north_boundary_index no hn
    obtain ⟨j,rfl⟩ := west_boundary_index wo hw
    exact corner_nonnegative no wo u i j
  · intro z hd hb
    obtain ⟨i,rfl⟩ := diagonal_boundary_index no wo hd hb
    exact diagonal_nonnegative no wo u i

end SquaresInCircles.Six.Analytic.FixedPair
