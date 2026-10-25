module

public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.SourceThreeData

/-!
# Eight squares: the complete large-target negative-core transverse family

The physical source contact increases continuously to alignment. Its
cost has increasing angle derivative, and that derivative is already
negative at alignment when B≥.54. There is therefore no intermediate
exit.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.High
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig)

lemma aligned_slope {A B : ℝ} (ht : OuterState A B) (hB : (27/50:ℝ)≤B) :
    CD B (Real.pi/2)<0 := by
  have hA : A<(148/125:ℝ) := by
    by_contra hn
    have ha : 148/125≤A := le_of_not_gt hn
    have ha2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤421/250)
      (show (421/250:ℝ)≤A+1/2 by linarith) 2
    have hb2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤26/25)
      (show (26/25:ℝ)≤B+1/2 by linarith) 2
    have hq := ht.2.2
    norm_num [Q0] at hq
    nlinarith
  have hc : (241/250:ℝ)<g-2*z*(A-1) := by
    dsimp [g,z,EdgeThreeAligned.gn,EdgeThreeAligned.zn]
    linarith
  have hp := mul_le_mul (show (241/250:ℝ)≤g-2*z*(A-1) by linarith)
    (show (26/25:ℝ)≤B+1/2 by linarith) (by norm_num)
    (show 0≤g-2*z*(A-1) by linarith)
  norm_num [CD,contactD,contact_aligned ht] at *
  nlinarith

theorem lower {A B φ : ℝ} (ht : OuterState A B) (hB : (27/50:ℝ)≤B)
    (hφ : Lower φ) (hb : 0≤contact B φ) : γ<C B φ := by
  have hA : 1≤A := by linarith [contact_upper ht hφ]
  have hAhi := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  have hdom {θ : ℝ} (hθ : θ∈Icc φ (Real.pi/2)) : Lower θ := ⟨hφ.1.trans hθ.1,hθ.2⟩
  have hbθ (θ : ℝ) (hθ : θ∈Icc φ (Real.pi/2)) :
      0≤contact B θ ∧ contact B θ<83/200 := by
    have hm := contact_monotone ht hφ (hdom hθ) hθ.1
    exact ⟨by linarith,by linarith [contact_upper ht (hdom hθ)]⟩
  have hcurv (θ : ℝ) (hθ : θ∈Icc φ (Real.pi/2)) : 0<CDD B θ := by
    have hh := hbθ θ hθ
    have hc : 0<g-2*z*contact B θ := by
      dsimp [g,z,EdgeThreeAligned.gn,EdgeThreeAligned.zn]
      linarith [hh.2]
    have hp := mul_pos hc (show 0<contact B θ+1/2 by linarith [hh.1])
    have hq := mul_nonneg (by norm_num [z,EdgeThreeAligned.zn] : 0≤2*z)
      (sq_nonneg (contactD B θ))
    dsimp [CDD]
    linarith
  have hdmono : MonotoneOn (CD B) (Icc φ (Real.pi/2)) :=
    monoOn_of_hasDeriv_nonneg
      (fun θ _ => (CD_hasDerivAt B θ).continuousAt.continuousWithinAt)
      (fun θ _ => CD_hasDerivAt B θ)
      (fun θ hθ => (hcurv θ (Ioo_subset_Icc_self hθ)).le)
  have hnegative (θ : ℝ) (hθ : θ∈Icc φ (Real.pi/2)) : CD B θ<0 :=
    (hdmono hθ ⟨hφ.2,le_rfl⟩ hθ.2).trans_lt (aligned_slope ht hB)
  have hm : AntitoneOn (C B) (Icc φ (Real.pi/2)) :=
    antiOn_of_hasDeriv_nonpos
      (fun θ _ => (C_hasDerivAt B θ).continuousAt.continuousWithinAt)
      (fun θ _ => C_hasDerivAt B θ)
      (fun θ hθ => (hnegative θ (Ioo_subset_Icc_self hθ)).le)
  exact (aligned_lower ht hA).trans_le
    (hm ⟨le_rfl,hφ.2⟩ ⟨hφ.2,le_rfl⟩ hφ.2)

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.High
