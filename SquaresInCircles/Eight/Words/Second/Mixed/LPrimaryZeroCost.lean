module

public import SquaresInCircles.Eight.Words.Second.Mixed.LPrimaryZeroReferences

/-!
# Eight squares: complete lower bounds for the shared L primary zero-source curve

A single quadratic tangent controls the middle minimum. Concavity of
the first derivative covers the rest of that middle arc. The complete
late arc is concave and has both endpoint costs above .8978.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.LPrimaryZero
open CommonQuarter CorePairGeometry Arithmetic

lemma early_middle_lower {φ : ℝ} (hφ : φ∈Icc (33/25) (7/5)) :
    (44997/50000:ℝ)<K φ := by
  have hdom : ∀z∈Icc (33/25) (7/5),z∈middle :=
    fun z hz => ⟨hz.1,by linarith [hz.2]⟩
  have hc : ∀z∈Icc (33/25) (7/5),(77/100:ℝ)≤KDD z := by
    intro z hz
    have hm := KDD_antitone (hdom z hz) (show (7/5:ℝ)∈middle by norm_num [middle]) hz.2
    exact middle_reference.1.le.trans hm
  have ht := curvature_tangent (f := K) (d := KD) (dd := KDD) (κ := (77/100:ℝ))
    hφ (show (1387/1000:ℝ)∈Icc (33/25) (7/5) by norm_num)
    (fun z hz => K_hasDerivAt (middle_subset (hdom z hz)))
    (fun z hz => KD_hasDerivAt (middle_subset (hdom z hz))) hc
  have hd := abs_lt.mp reference_cost.2
  have hp := mul_pos (show 0<KD (1387/1000)+3/10000 by linarith [hd.1])
    (show 0<(3/10000:ℝ)-KD (1387/1000) by linarith [hd.2])
  have hs := sq_nonneg ((77/100)*(φ-1387/1000)+KD (1387/1000))
  nlinarith [reference_cost.1]

lemma middle_tail_slope {φ : ℝ} (hφ : φ∈Icc (7/5) (37/25)) : 0<KD φ := by
  have hdom : ∀z∈Icc (7/5) (37/25),z∈middle := fun z hz => ⟨by linarith [hz.1],hz.2⟩
  have hc : ConcaveOn ℝ (Icc (7/5) (37/25)) KD :=
    concave_of_deriv2 (fun z hz => KD_hasDerivAt (middle_subset (hdom z hz)))
      (fun z hz => KDD_hasDerivAt (middle_subset (hdom z hz)))
      (fun z hz => (KDDD_negative (hdom z hz)).le)
  exact concave_gt_of_endpoints hc hφ
    (by linarith [middle_reference.2]) (by linarith [middle_terminal_slope])

lemma middle_tail_monotone : MonotoneOn K (Icc (7/5) (37/25)) :=
  monoOn_of_hasDeriv_nonneg
    (fun z hz => (K_hasDerivAt (middle_subset
      (show z∈middle from ⟨by linarith [hz.1],hz.2⟩))).continuousAt.continuousWithinAt)
    (fun z hz => K_hasDerivAt (middle_subset
      (show z∈middle from ⟨by linarith [hz.1],hz.2.le⟩)))
    (fun z hz => (middle_tail_slope (Ioo_subset_Icc_self hz)).le)

theorem middle_lower {φ : ℝ} (hφ : φ∈middle) : (44997/50000:ℝ)<K φ := by
  by_cases he : φ≤7/5
  · exact early_middle_lower ⟨hφ.1,he⟩
  · exact (early_middle_lower (show (7/5:ℝ)∈Icc (33/25) (7/5) by norm_num)).trans_le
      (middle_tail_monotone (show (7/5:ℝ)∈Icc (7/5) (37/25) by norm_num)
        ⟨by linarith,hφ.2⟩ (by linarith))

theorem late_lower {φ : ℝ} (hφ : φ∈late) : (4489/5000:ℝ)<K φ := by
  have hc : ConcaveOn ℝ late K :=
    concave_of_deriv2 (fun z hz => K_hasDerivAt (late_subset hz))
      (fun z hz => KD_hasDerivAt (late_subset hz)) (fun z hz => (KDD_negative_late hz).le)
  exact concave_gt_of_endpoints hc hφ
    (by linarith [late_initial_cost]) aligned_cost

/-- Every angle in the complete shared zero-source range. -/
theorem lower {φ : ℝ} (hφ : φ∈angles) : (4489/5000:ℝ)<K φ := by
  by_cases hm : φ≤37/25
  · linarith [middle_lower (show φ∈middle from ⟨hφ.1,hm⟩)]
  · exact late_lower ⟨by linarith,hφ.2⟩

theorem actual_negative {A B φ : ℝ} (ht : OuterState A B)
    (hφ : φ∈angles) (hU : A+1/2=U φ) :
    (17953/20000:ℝ)<φ-e-L B := by
  have hh := lower hφ
  rw [cost_eq ht hU] at hh
  norm_num at *
  linarith

theorem actual_positive {A B φ : ℝ} (ht : OuterState A B)
    (hφ : φ∈angles) (hU : A+1/2=U φ) :
    (361/400:ℝ)<φ-1449/100000-L B := by
  have hh := lower hφ
  rw [cost_eq ht hU] at hh
  dsimp [e] at hh
  linarith

end SquaresInCircles.Eight.SecondWord.LPrimaryZero
