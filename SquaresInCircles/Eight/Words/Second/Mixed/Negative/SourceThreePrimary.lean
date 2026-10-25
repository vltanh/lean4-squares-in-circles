module

public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.SourceThreePrimaryGeometry

/-!
# Eight squares: every original lower primary negative-core owner

The small-target contact has the already proved transverse separator.
For every larger target, its physical zero-source entry and alignment
bound the whole concave contact path. The original source is compared
with that same path before any endpoint argument.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Primary
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower)

lemma large_lower {A B φ : ℝ} (ht : OuterState A B) (hB : (43/100:ℝ)≤B)
    (hφ : Lower φ) (hb : 0≤b A φ) : γ<F A B φ := by
  obtain ⟨θ,hθ,hzero⟩ := zero_entry ht hB hφ hb
  have hentry : θ∈LPrimaryZero.angles := ⟨hθ.1,hθ.2.trans hφ.2⟩
  have hdom {x : ℝ} (hx : x∈Icc θ (Real.pi/2)) : x∈LPrimaryZero.angles :=
    ⟨hθ.1.trans hx.1,hx.2⟩
  have hnonneg (x : ℝ) (hx : x∈Icc θ (Real.pi/2)) : 0≤b A x := by
    have hh := b_monotone ht (late_lower hentry) (late_lower (hdom hx)) hx.1
    rw [hzero] at hh
    exact hh
  have hc : ConcaveOn ℝ (Icc θ (Real.pi/2)) (F A B) :=
    concave_of_deriv2 (fun x hx => F_hasDerivAt (B := B) (late_lower (hdom hx)))
      (fun x hx => F1_hasDerivAt (late_lower (hdom hx)))
      (fun x hx => (curvature_negative ht (hdom hx) (hnonneg x hx)).le)
  have hA : 1≤A := by linarith [b_upper ht hφ]
  exact concave_gt_of_endpoints hc ⟨hθ.2,hφ.2⟩
    (zero_lower ht hentry hzero) (aligned_lower ht hA)

theorem original {a b₀ A B φ : ℝ} (hs : CoreState a b₀)
    (ht : OuterState A B) (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤-a*Real.cos φ-b₀*Real.sin φ+A) :
    γ<value a b₀ B φ := by
  have hh := original_contact hs ht hφ hsep
  have hmin : γ<F A B φ := by
    by_cases he : B≤43/100
    · exact small_lower ht he hφ hh.2.1
    · exact large_lower ht (by linarith) hφ hh.2.1
  exact hmin.trans_le hh.2.2.2.2

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Primary
