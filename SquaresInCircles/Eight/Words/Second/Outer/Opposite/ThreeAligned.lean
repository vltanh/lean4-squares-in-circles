module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeAlignedShape

/-!
# Eight squares: both original aligned opposite edge-three inequalities

Each whole-arc curvature estimate is integrated from its single actual
reference.  The final statements accept only the original two circle
states and their weak aligned separator, retaining zero coordinates.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

namespace Aligned

theorem forward_lower {y : ℝ} (hy : y∈Icc 0 bOne) : (89807/100000:ℝ)<cost false y := by
  have ht := curvature_tangent (f := cost false) (d := first false) (dd := second false)
    (κ := (11/50:ℝ)) hy (reference_mem false)
    (fun t ht => cost_hasDerivAt false ht) (fun t ht => first_hasDerivAt false ht)
    (fun t ht => (forward_curvature ht).le)
  have hd := abs_lt.mp (reference_first false)
  have hs : (first false (reference false))^2<(1/1000000:ℝ)^2 := by nlinarith
  have hp := sq_nonneg ((11/100:ℝ)*(y-reference false)+first false (reference false)/2)
  nlinarith [forward_reference_value]

theorem reverse_lower {y : ℝ} (hy : y∈Icc 0 bOne) : (44889/50000:ℝ)<cost true y := by
  have ht := curvature_tangent (f := cost true) (d := first true) (dd := second true)
    (κ := (87/100:ℝ)) hy (reference_mem true)
    (fun t ht => cost_hasDerivAt true ht) (fun t ht => first_hasDerivAt true ht)
    (fun t ht => (reverse_curvature ht).le)
  have hd := abs_lt.mp (reference_first true)
  have hs : (first true (reference true))^2<(1/1000000:ℝ)^2 := by nlinarith
  have hp := sq_nonneg ((87/200:ℝ)*(y-reference true)+first true (reference true)/2)
  nlinarith [reverse_reference_value]

end Aligned

lemma below_bOne_of_primary_one {a b : ℝ} (hs : OuterState a b) (ha : 1≤a) : b≤bOne := by
  have hh := ShortOuterOne.SameContact.arc_antitone (primary_domain primary_one_mem)
    (primary_domain (NegativeTwo.primary_mem hs)) ha
  rwa [(ShortOuterOne.SameContact.actual_arc hs).2] at hh

theorem aligned_first {a b A B : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hm : 1≤A-b) : (44889/50000:ℝ)<value b B (Real.pi/2) := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  have hA : 1≤A := by linarith [hb.1]
  have hdom : B∈Icc 0 bOne := ⟨hB.1,below_bOne_of_primary_one ht hA⟩
  have hbj : b≤Aligned.j B := by
    dsimp [Aligned.j]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
    linarith
  have hmono := T_monotone hb (Aligned.j_mem hdom) hbj
  have hl := Aligned.forward_lower hdom
  rw [Aligned.forward_value] at hl
  dsimp [value] at hl ⊢
  linarith

theorem aligned_last {a b A B : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hm : 1≤a-B) : (44889/50000:ℝ)<value b B (Real.pi/2) := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  have ha : 1≤a := by linarith [hB.1]
  have hdom : b∈Icc 0 bOne := ⟨hb.1,below_bOne_of_primary_one hs ha⟩
  have hBj : B≤Aligned.j b := by
    dsimp [Aligned.j]
    rw [(ShortOuterOne.SameContact.actual_arc hs).1]
    linarith
  have hmono := L_monotone hB (Aligned.j_mem hdom) hBj
  have hl := Aligned.reverse_lower hdom
  rw [Aligned.reverse_value] at hl
  dsimp [value] at hl ⊢
  linarith

end SquaresInCircles.Eight.SecondWord.OppositeThree
