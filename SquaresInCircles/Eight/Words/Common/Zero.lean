module

public import SquaresInCircles.Eight.Words.Common.ZeroOpposite
public import SquaresInCircles.Eight.Words.Common.ZeroPrimary
public import SquaresInCircles.Eight.Words.Common.ZeroSame

/-!
# Eight squares: the common-label bound for a zero quarter increment

An edge with quarter increment zero has cost above `391/400` for each of its four weak owners
(`zero_cost`). The source-secondary owner is split by the signs of the two squares
(`zero_secondary_cost`); the impossible negative-to-positive sign uses the physical ray gap.
Reflection and reversal keep that same gap and move the target owners to the source-owner
formulas. `actual_zero` applies this to an edge of the boundary cycle with its frame lift.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.CommonQuarter

open WordProblems

lemma gap_reverse (σ τ : Bool) (a b A B φ : ℝ) :
    φ+(sign (!τ):ℝ)*Real.arctan (B/A)-(sign (!σ):ℝ)*Real.arctan (b/a)=
      φ+(sign σ:ℝ)*Real.arctan (b/a)-(sign τ:ℝ)*Real.arctan (B/A) := by
  cases σ <;> cases τ <;> norm_num [sign] <;> ring

/-- The source-secondary owner for every pair of signs, on the original state pair. -/
theorem zero_secondary_cost {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B) (σ τ : Bool)
    (hφ : |φ|≤7/10)
    (hg : (19/25:ℝ)<φ+(sign σ:ℝ)*Real.arctan (b/a)-(sign τ:ℝ)*Real.arctan (B/A))
    (hm : 0≤forwardMargin 0 a b A B (sign σ) (sign τ) φ) :
    (391/400:ℝ)<cost source target σ τ a b A B φ := by
  cases σ <;> cases τ
  · exact zero_same_secondary hs ht false hφ hm
  · have hg' : (19/25:ℝ)<φ-Real.arctan (b/a)-Real.arctan (B/A) := by
      have h := hg
      simp only [sign, Bool.false_eq_true, ite_false, ite_true, Rat.cast_neg,
        Rat.cast_one] at h
      linarith
    exact (zero_negative_positive_false hs ht hφ hg').elim
  · have hm' : 0≤forwardMargin 0 a b A B 1 (-1) φ := by simpa [sign] using hm
    simpa [cost,sign] using zero_opposite_secondary hs ht hφ hm'
  · exact zero_same_secondary hs ht true hφ hm

/-- The continuous zero-quarter inequality, for every owner, closed radial state and signed tie
choice. -/
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
      simpa using (margin_reverse 1 σ τ a b A B φ).symm ▸ hm
    simpa [cost_reverse] using zero_primary_cost ht hs (!τ) (!σ) hφ hgr hr
  · have hr : 0≤forwardMargin 0 A B a b (sign (!τ)) (sign (!σ)) φ := by
      simpa using (margin_reverse 2 σ τ a b A B φ).symm ▸ hm
    simpa [cost_reverse] using zero_secondary_cost ht hs (!τ) (!σ) hφ hgr hr
  · exact zero_primary_cost hs ht σ τ hφ hg hm

/-- The common zero cost on the boundary cycle and its frame lift. -/
theorem actual_zero (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hk : F.word hgap pi_lt_22_over_7 i=0) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (391/400:ℝ)<QuarterWordGeometry.phaseValue F hgap i+
      QuarterWordGeometry.commonMarker C i-QuarterWordGeometry.commonMarker C (next i) := by
  have hm := QuarterWordGeometry.original_margin C F hgap i j hj
  have hp : |QuarterWordGeometry.phaseValue F hgap i|≤7/10 := by
    simpa [QuarterWordGeometry.phaseValue,hk] using
      (QuarterWordGeometry.difference_small F i).le
  have he := QuarterWordGeometry.phase_gap C F hgap i
  rw [QuarterWordGeometry.alpha_formula,QuarterWordGeometry.alpha_formula] at he
  have hg : (19/25:ℝ)<QuarterWordGeometry.phaseValue F hgap i+
      (sign (QuarterWordGeometry.positiveOf C i):ℝ)*Real.arctan (C.b i/C.a i)-
      (sign (QuarterWordGeometry.positiveOf C (next i)):ℝ)*
        Real.arctan (C.b (next i)/C.a (next i)) := by
    rw [he]
    exact hgap i
  have h := zero_cost (actual_state C i) (actual_state C (next i))
    (QuarterWordGeometry.positiveOf C i) (QuarterWordGeometry.positiveOf C (next i)) hp hg j hm
  simpa [cost,QuarterWordGeometry.commonMarker,commonValue_eq] using h

end SquaresInCircles.Eight.CommonQuarter
