module

public import SquaresInCircles.Eight.TableFree.CommonOneMixedPrimary

/-!
# Complete common-label bound for one quarter increment

Both source owners are proved on every original signed core/outer state.
Exact reflection and reversal move the target owners to those formulas
without changing their cost. The final theorem consumes an actual weak
physical owner on the original boundary cycle and integer frame lift.
Uncompiled source draft.
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

/-- The complete continuous one-quarter inequality needs no additional
center-gap premise beyond the retained original weak separating owner. -/
theorem one_cost {source target : RadialKind} {a b A B x : ℝ}
    (hs : State source a b) (ht : State target A B) (σ τ : Bool)
    (hx : |x|≤7/10) (j : Fin 4)
    (hm : 0≤forwardMargin j a b A B (sign σ) (sign τ) (Real.pi/2+x)) :
    (157/200:ℝ)<cost source target σ τ a b A B (Real.pi/2+x) := by
  fin_cases j
  · exact one_secondary_cost hs ht σ τ hx hm
  · have hr : 0≤forwardMargin 3 A B a b (sign (!τ)) (sign (!σ)) (Real.pi/2+x) := by
      rw [← margin_reverse 1 σ τ a b A B (Real.pi/2+x)] at hm
      simpa using hm
    simpa [cost_reverse] using one_primary_cost ht hs (!τ) (!σ) hx hr
  · have hr : 0≤forwardMargin 0 A B a b (sign (!τ)) (sign (!σ)) (Real.pi/2+x) := by
      rw [← margin_reverse 2 σ τ a b A B (Real.pi/2+x)] at hm
      simpa using hm
    simpa [cost_reverse] using one_secondary_cost ht hs (!τ) (!σ) hx hr
  · exact one_primary_cost hs ht σ τ hx hm

/-- One-quarter cost for the same actual physical squares, closed radial
states, tangent signs and original weak owner. -/
theorem actual_one (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hk : F.word hgap pi_lt_22_over_7 i=1) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (157/200:ℝ)<TableFreeWordGeometry.phaseValue F hgap i+
      TableFreeWordGeometry.commonMarker C i-TableFreeWordGeometry.commonMarker C (next i) := by
  have hm := TableFreeWordGeometry.original_margin C F hgap i j hj
  have he : TableFreeWordGeometry.phaseValue F hgap i=
      Real.pi/2+TableFreeWordGeometry.difference F i := by
    simp [TableFreeWordGeometry.phaseValue,hk]
    ring
  rw [he] at hm ⊢
  have hh := one_cost (actual_state C i) (actual_state C (next i))
    (TableFreeWordGeometry.positiveOf C i) (TableFreeWordGeometry.positiveOf C (next i))
    (TableFreeWordGeometry.difference_small F i).le j hm
  simpa [cost,TableFreeWordGeometry.commonMarker,commonValue_eq] using hh

end SquaresInCircles.Eight.CommonQuarter
