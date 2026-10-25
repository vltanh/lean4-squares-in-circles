module

public import SquaresInCircles.Eight.Words.Common.OneCorePrimary
public import SquaresInCircles.Eight.Words.Common.OneMixedPrimary

/-!
# Eight squares: the common-label bound for one quarter increment

An edge with quarter increment one has cost above `157/200` for each of its four owners
(`one_cost`). The two source owners are proved on every signed core or outer state
(`one_primary_cost`, `one_secondary_cost`); exact reflection and reversal move the two target
owners to those formulas without changing their cost. `actual_one` applies this to a weak
physical owner of an edge of the boundary cycle, with its integer frame lift.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.CommonQuarter

open WordProblems

theorem one_primary_cost {source target : RadialKind} {a b A B x : ℝ}
    (hs : State source a b) (ht : State target A B) (σ τ : Bool)
    (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (sign σ) (sign τ) (Real.pi/2+x)) :
    (157/200:ℝ)<cost source target σ τ a b A B (Real.pi/2+x) := by
  by_cases hso : source=.outer
  · have hs' : OuterState a b := by simpa [State,hso] using hs
    have hsL := (outer_label_bounds hs').1.le
    by_cases hto : target=.outer
    · have ht' : OuterState A B := by simpa [State,hto] using ht
      cases τ
      · have hm' : 0≤forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+x) := by
          simpa [forwardMargin,sign] using hm
        have hh := one_outer_negative_primary hs' ht' hx hm'
        cases σ <;> norm_num [cost,sign,label,hso,hto] <;> linarith
      · have hm' : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x) := by
          simpa [forwardMargin,sign] using hm
        have hh := one_outer_opposite_primary hs' ht' hx hm'
        cases σ <;> norm_num [cost,sign,label,hso,hto] <;> linarith
    · have ht' : CorePairGeometry.CoreState A B := by simpa [State,hto] using ht
      cases τ
      · have hm' : 0≤forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+x) := by
          simpa [forwardMargin,sign] using hm
        have hh := one_outer_core_negative_primary hs' ht' hx hm'
        cases σ <;> norm_num [cost,sign,label,hso,hto] <;> linarith
      · have hm' : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x) := by
          simpa [forwardMargin,sign] using hm
        have hh := one_outer_core_positive_primary hs' ht' hx hm'
        cases σ <;> norm_num [cost,sign,label,hso,hto] <;> linarith
  · have hs' : CorePairGeometry.CoreState a b := by simpa [State,hso] using hs
    exact one_core_primary_cost hso hs' ht σ τ hx hm

/-- The continuous one-quarter inequality, from the weak separating owner alone, with no
center-gap premise. -/
theorem one_cost {source target : RadialKind} {a b A B x : ℝ}
    (hs : State source a b) (ht : State target A B) (σ τ : Bool)
    (hx : |x|≤7/10) (j : Fin 4)
    (hm : 0≤forwardMargin j a b A B (sign σ) (sign τ) (Real.pi/2+x)) :
    (157/200:ℝ)<cost source target σ τ a b A B (Real.pi/2+x) := by
  fin_cases j
  · exact one_secondary_cost hs ht σ τ hx hm
  · have hr : 0≤forwardMargin 3 A B a b (sign (!τ)) (sign (!σ)) (Real.pi/2+x) := by
      change 0≤forwardMargin 1 a b A B (sign σ) (sign τ) (Real.pi/2+x) at hm
      rw [← margin_reverse 1 σ τ a b A B (Real.pi/2+x)] at hm
      simpa using hm
    simpa [cost_reverse] using one_primary_cost ht hs (!τ) (!σ) hx hr
  · have hr : 0≤forwardMargin 0 A B a b (sign (!τ)) (sign (!σ)) (Real.pi/2+x) := by
      change 0≤forwardMargin 2 a b A B (sign σ) (sign τ) (Real.pi/2+x) at hm
      rw [← margin_reverse 2 σ τ a b A B (Real.pi/2+x)] at hm
      simpa using hm
    simpa [cost_reverse] using one_secondary_cost ht hs (!τ) (!σ) hx hr
  · exact one_primary_cost hs ht σ τ hx hm

/-- The one-quarter cost on the boundary cycle, with its closed radial states, tangent signs and
weak owner. -/
theorem actual_one (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hk : F.word hgap pi_lt_22_over_7 i=1) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (157/200:ℝ)<QuarterWordGeometry.phaseValue F hgap i+
      QuarterWordGeometry.commonMarker C i-QuarterWordGeometry.commonMarker C (next i) := by
  have hm := QuarterWordGeometry.original_margin C F hgap i j hj
  have he : QuarterWordGeometry.phaseValue F hgap i=
      Real.pi/2+QuarterWordGeometry.difference F i := by
    simp [QuarterWordGeometry.phaseValue,hk]
    ring
  rw [he] at hm ⊢
  have hh := one_cost (actual_state C i) (actual_state C (next i))
    (QuarterWordGeometry.positiveOf C i) (QuarterWordGeometry.positiveOf C (next i))
    (QuarterWordGeometry.difference_small F i).le j hm
  simpa [cost,QuarterWordGeometry.commonMarker,commonValue_eq] using hh

end SquaresInCircles.Eight.CommonQuarter
