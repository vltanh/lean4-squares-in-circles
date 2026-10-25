module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeZeroBounds

/-!
# Eight squares: the full scalar reserve on the actual zero-source contact

The cost increases from `1.3` to `1.4`.  On the remaining arc it
is strictly concave.  Both arguments use actual angular velocities
and literal label derivatives; the two fixed physical endpoints
give a reserve above `0.902` throughout.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.ZeroContact

open CommonQuarter CorePairGeometry Arithmetic SourceCurve

lemma initial_domain {φ : ℝ} (hφ : φ∈Icc (13/10:ℝ) (7/5)) : Domain φ :=
  ⟨hφ.1,hφ.2.trans middle_mem.2⟩

lemma initial_acceleration {φ : ℝ} (hφ : φ∈Icc (13/10:ℝ) (7/5)) :
    0<bpp parameter φ := by
  have hp := domain (initial_domain hφ)
  have hu := u_antitone parameter_mem hp.2 (domain middle_mem).2 hφ.2
  have hw := target_monotone parameter_mem hp.2 (domain middle_mem).2 hφ.2
  dsimp [target] at hw
  have hf := f_monotone parameter_mem hp.2 (domain middle_mem).2 hφ.2
  have hfp := fp_monotone parameter_nonnegative (domain left_mem).2 hp.2 hφ.1
  have hmid := middle_curve
  have hul : (843/500:ℝ)≤u parameter φ := by linarith [hmid.2.1.1]
  have hwh : w parameter φ≤(259/250:ℝ) := by linarith [hmid.2.2.1.2]
  have hfh : SecondWord.PositiveThree.SourceCurve.f parameter φ≤(87/100:ℝ) := hf.trans hmid.2.2.2.1.2
  have hfpl : (679/1000:ℝ)≤fp parameter φ := left_curve.2.2.2.2.1.trans hfp
  have hf0 := (f_bounds hp).1.le
  have hf2 := pow_le_pow_left₀ hf0 hfh 2
  have hneg := mul_le_mul hwh hf2 (sq_nonneg _) (by norm_num : (0:ℝ)≤259/250)
  have hpos := mul_le_mul hul hfpl (by norm_num : (0:ℝ)≤679/1000) (u_positive hp).le
  dsimp [bpp]
  nlinarith

lemma initial_speed_monotone :
    MonotoneOn (bp parameter) (Icc (13/10:ℝ) (7/5)) :=
  monoOn_of_hasDeriv_nonneg
    (fun φ hφ => (bp_hasDerivAt (domain (initial_domain hφ))).continuousAt.continuousWithinAt)
    (fun φ hφ => bp_hasDerivAt (domain (initial_domain (Ioo_subset_Icc_self hφ))))
    (fun φ hφ => (initial_acceleration (Ioo_subset_Icc_self hφ)).le)

lemma initial_speed {φ : ℝ} (hφ : φ∈Icc (13/10:ℝ) (7/5)) :
    bp parameter φ<(1467/1000:ℝ) :=
  (initial_speed_monotone hφ ⟨by norm_num,le_rfl⟩ hφ.2).trans_lt middle_speed

lemma initial_label {φ : ℝ} (hφ : φ∈Icc (13/10:ℝ) (7/5)) :
    LLabel.d1 (target parameter φ)<659/1000 := by
  have hlo := target_monotone parameter_mem (domain left_mem).2
    (domain (initial_domain hφ)).2 hφ.1
  have hhi := target_monotone parameter_mem (domain (initial_domain hφ)).2
    (domain middle_mem).2 hφ.2
  have hend := target_monotone parameter_mem (domain left_mem).2 (domain middle_mem).2
    (show (13/10:ℝ)≤7/5 by norm_num)
  have hdom : ∀ B∈Icc (target parameter (13/10)) (target parameter (7/5)),
      B∈Icc 0 outerDiagonal := by
    intro B hB
    exact ⟨left_target.1.trans hB.1,hB.2.trans middle_target.2⟩
  have hc : ConcaveOn ℝ (Icc (target parameter (13/10)) (target parameter (7/5)))
      (fun B => -LLabel.d1 B) :=
    concave_of_deriv2
      (fun B hB => (LLabel.d1_hasDerivAt (outer_domain (hdom B hB))).neg)
      (fun B hB => (LLabel.d2_hasDerivAt (outer_domain (hdom B hB))).neg)
      (fun B hB => by linarith [L_third_positive (hdom B hB)])
  have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hend⟩ ⟨hend,le_rfl⟩ ⟨hlo,hhi⟩
  have hlow : -(659/1000:ℝ)< -LLabel.d1 (target parameter φ) :=
    (lt_min (by linarith [left_labels.1]) (by linarith [middle_labels.1])).trans_le hh
  linarith

lemma initial_first {φ : ℝ} (hφ : φ∈Icc (13/10:ℝ) (7/5)) : 0<first φ := by
  have hbpp := bp_positive (domain (initial_domain hφ))
  have h1 := mul_lt_mul_of_pos_right (initial_label hφ) hbpp
  have h2 := mul_lt_mul_of_pos_left (initial_speed hφ)
    (by norm_num : (0:ℝ)<659/1000)
  dsimp [first]
  nlinarith

lemma initial_cost_monotone : MonotoneOn cost (Icc (13/10:ℝ) (7/5)) :=
  monoOn_of_hasDeriv_nonneg
    (fun φ hφ => (cost_hasDerivAt (initial_domain hφ)).continuousAt.continuousWithinAt)
    (fun φ hφ => cost_hasDerivAt (initial_domain (Ioo_subset_Icc_self hφ)))
    (fun φ hφ => (initial_first (Ioo_subset_Icc_self hφ)).le)

lemma initial_value {φ : ℝ} (hφ : φ∈Icc (13/10:ℝ) (7/5)) :
    (451/500:ℝ)<cost φ :=
  left_labels.2.trans_le
    (initial_cost_monotone ⟨le_rfl,by norm_num⟩ hφ hφ.1)

lemma final_domain {φ : ℝ} (hφ : φ∈Icc (7/5:ℝ) (Real.pi/2)) : Domain φ :=
  ⟨by linarith [hφ.1],hφ.2⟩

lemma final_velocities {φ : ℝ} (hφ : φ∈Icc (7/5:ℝ) (Real.pi/2)) :
    (13/10:ℝ)<bp parameter φ ∧ -(11/50:ℝ)<bpp parameter φ := by
  have hd := final_domain hφ
  have hh := geometry hd
  have hfl := f_monotone parameter_mem (domain middle_mem).2 (domain hd).2 hφ.1
  have hfpl := fp_monotone parameter_nonnegative (domain middle_mem).2 (domain hd).2 hφ.1
  have hf : (8699/10000:ℝ)≤SecondWord.PositiveThree.SourceCurve.f parameter φ := middle_curve.2.2.2.1.1.trans hfl
  have hfp : (73/100:ℝ)≤fp parameter φ := middle_curve.2.2.2.2.1.trans hfpl
  have hbp := mul_le_mul hh.1.1 hf (by norm_num : (0:ℝ)≤8699/10000)
    (u_positive (domain hd)).le
  have hup := mul_le_mul hh.1.1 hfp (by norm_num : (0:ℝ)≤73/100)
    (u_positive (domain hd)).le
  have hf2 : (SecondWord.PositiveThree.SourceCurve.f parameter φ)^2≤1 := by
    have hf0 := (f_bounds (domain hd)).1
    nlinarith [hh.2.2.2.1.2]
  have hneg := mul_le_mul hh.2.1.2 hf2 (sq_nonneg _)
    (by norm_num : (0:ℝ)≤1291/1000)
  dsimp [bp,bpp]
  exact ⟨by norm_num at hbp; linarith,by norm_num at hup hneg; linarith⟩

lemma final_second {φ : ℝ} (hφ : φ∈Icc (7/5:ℝ) (Real.pi/2)) : second φ<0 := by
  have hd := final_domain hφ
  have ht := target_monotone parameter_mem (domain middle_mem).2 (domain hd).2 hφ.1
  have hL2 := middle_labels.2.trans_le
    (L_second_monotone middle_target (target_mem hd) ht)
  have hL1 := L_first_bounds (target_mem hd)
  have hLpos : 0<LLabel.d1 (target parameter φ) := by linarith [hL1.1]
  have hv := final_velocities hφ
  have hsq : (13/10:ℝ)^2<(bp parameter φ)^2 := by nlinarith [hv.1]
  have hneg := mul_lt_mul hL2 hsq.le (by norm_num : (0:ℝ)<(13/10)^2)
    (by linarith [hL2] : 0≤LLabel.d2 (target parameter φ))
  have hlast1 := mul_lt_mul_of_pos_left hv.2 hLpos
  have hlast2 := mul_lt_mul_of_pos_right hL1.2 (by norm_num : (0:ℝ)<11/50)
  dsimp [second]
  nlinarith

lemma final_value {φ : ℝ} (hφ : φ∈Icc (7/5:ℝ) (Real.pi/2)) :
    (451/500:ℝ)<cost φ := by
  have hc : ConcaveOn ℝ (Icc (7/5:ℝ) (Real.pi/2)) cost :=
    concave_of_deriv2
      (fun t ht => cost_hasDerivAt (final_domain ht))
      (fun t ht => first_hasDerivAt (final_domain ht))
      (fun t ht => (final_second ht).le)
  exact concave_gt_of_endpoints hc hφ
    (initial_value ⟨by norm_num,le_rfl⟩) (by linarith [quarter_value])

theorem cost_lower {φ : ℝ} (hφ : Domain φ) : (451/500:ℝ)<cost φ := by
  by_cases h : φ≤7/5
  · exact initial_value ⟨hφ.1,h⟩
  · exact final_value ⟨le_of_not_ge h,hφ.2⟩

end SquaresInCircles.Eight.SecondWord.PositiveThree.ZeroContact
