module

public import SquaresInCircles.Eight.TableFree.CommonZeroPrimary

/-!
# Complete common-label bound for a zero quarter increment

All four original weak owners are covered. The source-secondary matrix is
split by the actual signs; the impossible negative-to-positive sign uses
the physical ray gap. Reflection and reversal retain that same gap and
move the target owners to the proved source-owner formulas.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.CommonQuarter

open WordProblems

lemma gap_reverse (σ τ : Bool) (a b A B φ : ℝ) :
    φ+(sign (!τ):ℝ)*Real.arctan (B/A)-(sign (!σ):ℝ)*Real.arctan (b/a)=
      φ+(sign σ:ℝ)*Real.arctan (b/a)-(sign τ:ℝ)*Real.arctan (B/A) := by
  cases σ <;> cases τ <;> norm_num [sign] <;> ring

/-- The complete source-secondary sign matrix on the original state pair. -/
theorem zero_secondary_cost {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B) (σ τ : Bool)
    (hφ : |φ|≤7/10)
    (hg : (19/25:ℝ)<φ+(sign σ:ℝ)*Real.arctan (b/a)-(sign τ:ℝ)*Real.arctan (B/A))
    (hm : 0≤forwardMargin 0 a b A B (sign σ) (sign τ) φ) :
    (391/400:ℝ)<cost source target σ τ a b A B φ := by
  cases σ <;> cases τ
  · exact zero_same_secondary hs ht false hφ hm
  · have hg' : (19/25:ℝ)<φ-Real.arctan (b/a)-Real.arctan (B/A) := by
      simpa [sign] using hg
    exact (zero_negative_positive_false hs ht hφ hg').elim
  · have hm' : 0≤forwardMargin 0 a b A B 1 (-1) φ := by simpa [sign] using hm
    simpa [cost,sign] using zero_opposite_secondary hs ht hφ hm'
  · exact zero_same_secondary hs ht true hφ hm

/-- The full continuous zero-quarter inequality, with all original owners,
closed radial states and signed tie choices retained. -/
theorem zero_cost {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B) (σ τ : Bool)
    (hφ : |φ|≤7/10)
    (hg : (19/25:ℝ)<φ+(sign σ:ℝ)*Real.arctan (b/a)-(sign τ:ℝ)*Real.arctan (B/A))
    (j : Fin 4) (hm : 0≤forwardMargin j a b A B (sign σ) (sign τ) φ) :
    (391/400:ℝ)<cost source target σ τ a b A B φ := by
  have hgr : (19/25:ℝ)<φ+(sign (!τ):ℝ)*Real.arctan (B/A)-
      (sign (!σ):ℝ)*Real.arctan (b/a) := by
    rwa [gap_reverse]
  fin_cases j
  · exact zero_secondary_cost hs ht σ τ hφ hg hm
  · have hr : 0≤forwardMargin 3 A B a b (sign (!τ)) (sign (!σ)) φ := by
      rw [← margin_reverse 1 σ τ a b A B φ] at hm
      simpa using hm
    simpa [cost_reverse] using zero_primary_cost ht hs (!τ) (!σ) hφ hgr hr
  · have hr : 0≤forwardMargin 0 A B a b (sign (!τ)) (sign (!σ)) φ := by
      rw [← margin_reverse 2 σ τ a b A B φ] at hm
      simpa using hm
    simpa [cost_reverse] using zero_secondary_cost ht hs (!τ) (!σ) hφ hgr hr
  · exact zero_primary_cost hs ht σ τ hφ hg hm

/-- The common zero cost on the same actual physical cycle and frame lift. -/
theorem actual_zero (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hk : F.word hgap pi_lt_22_over_7 i=0) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (391/400:ℝ)<TableFreeWordGeometry.phaseValue F hgap i+
      TableFreeWordGeometry.commonMarker C i-TableFreeWordGeometry.commonMarker C (next i) := by
  have hm := TableFreeWordGeometry.original_margin C F hgap i j hj
  have hp : |TableFreeWordGeometry.phaseValue F hgap i|≤7/10 := by
    simpa [TableFreeWordGeometry.phaseValue,hk] using
      (TableFreeWordGeometry.difference_small F i).le
  have he := TableFreeWordGeometry.phase_gap C F hgap i
  rw [TableFreeWordGeometry.alpha_formula,TableFreeWordGeometry.alpha_formula] at he
  have hg : (19/25:ℝ)<TableFreeWordGeometry.phaseValue F hgap i+
      (sign (TableFreeWordGeometry.positiveOf C i):ℝ)*Real.arctan (C.b i/C.a i)-
      (sign (TableFreeWordGeometry.positiveOf C (next i)):ℝ)*
        Real.arctan (C.b (next i)/C.a (next i)) := by
    rw [he]
    exact hgap i
  have h := zero_cost (actual_state C i) (actual_state C (next i))
    (TableFreeWordGeometry.positiveOf C i) (TableFreeWordGeometry.positiveOf C (next i)) hp hg j hm
  simpa [cost,TableFreeWordGeometry.commonMarker,commonValue_eq] using h

end SquaresInCircles.Eight.CommonQuarter
