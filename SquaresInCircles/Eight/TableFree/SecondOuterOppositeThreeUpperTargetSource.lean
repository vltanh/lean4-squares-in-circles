module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeUpperInverse

/-!
# The full late source motion for the other upper-primary owner

On `[.1,.4]` the difference `V' - T'` is concave and positive at both
ends, so the existing physical primary ratio pays `T'` as well.  On
the remaining arc the global inverse-factor floor already suffices.
These two derivative regimes give one monotone source motion from
every source coordinate at least `.1`.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.UpperTarget
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma tenth_mem : (1/10:ℝ)∈Icc 0 outerDiagonal := by
  constructor <;> linarith [fine_outer_endpoint_bounds.2]

lemma two_fifths_mem : (2/5:ℝ)∈Icc 0 outerDiagonal := by
  constructor <;> linarith [fine_outer_endpoint_bounds.2]

lemma tenth_slopes : TLabel.d1 (1/10)<(118/125:ℝ) ∧
    (51/50:ℝ)<VLabel.d1 (1/10) := by
  have ht := TLabel.first_chart_reference (outer_domain tenth_mem)
    (l := (188562986/10^8:ℝ)) (u := (188562987/10^8:ℝ))
    (dlo := (9/10:ℝ)) (dhi := (118/125:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  have hv := VLabel.first_chart_reference (outer_domain tenth_mem)
    (l := (188562986/10^8:ℝ)) (u := (188562987/10^8:ℝ))
    (dlo := (51/50:ℝ)) (dhi := (11/10:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [VLabel,W,Q0]) (by norm_num [VLabel,W,Q0])
  exact ⟨ht.2,hv.1⟩

lemma two_fifths_slopes : TLabel.d1 (2/5)<(677/1000:ℝ) ∧
    (209/250:ℝ)<VLabel.d1 (2/5) := by
  have ht := TLabel.first_chart_reference (outer_domain two_fifths_mem)
    (l := (176227126/10^8:ℝ)) (u := (176227127/10^8:ℝ))
    (dlo := (3/5:ℝ)) (dhi := (677/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  have hv := VLabel.first_chart_reference (outer_domain two_fifths_mem)
    (l := (176227126/10^8:ℝ)) (u := (176227127/10^8:ℝ))
    (dlo := (209/250:ℝ)) (dhi := (1:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [VLabel,W,Q0]) (by norm_num [VLabel,W,Q0])
  exact ⟨ht.2,hv.1⟩

lemma source_comparison {b : ℝ} (hb : b∈Icc (1/10) (2/5)) :
    TLabel.d1 b<VLabel.d1 b := by
  have hdom {t : ℝ} (ht : t∈Icc (1/10) (2/5)) : t∈Icc 0 outerDiagonal :=
    ⟨by linarith [ht.1],ht.2.trans two_fifths_mem.2⟩
  have hc : ConcaveOn ℝ (Icc (1/10) (2/5)) (fun t => VLabel.d1 t-TLabel.d1 t) :=
    concave_of_deriv2
      (fun t ht => (VLabel.d1_hasDerivAt (outer_domain (hdom ht))).sub
        (TLabel.d1_hasDerivAt (outer_domain (hdom ht))))
      (fun t ht => (VLabel.d2_hasDerivAt (outer_domain (hdom ht))).sub
        (TLabel.d2_hasDerivAt (outer_domain (hdom ht))))
      (fun t ht => by linarith [V_third_negative (hdom ht),T_third_lower (hdom ht)])
  have hh := concave_gt_of_endpoints hc hb
    (show 0<VLabel.d1 (1/10)-TLabel.d1 (1/10) by linarith [tenth_slopes.1,tenth_slopes.2])
    (show 0<VLabel.d1 (2/5)-TLabel.d1 (2/5) by
      linarith [two_fifths_slopes.1,two_fifths_slopes.2])
  linarith

lemma source_first_late {b : ℝ} (hb : b∈Icc (2/5) outerDiagonal) :
    TLabel.d1 b<(387/500:ℝ) := by
  have hdom {t : ℝ} (ht : t∈Icc (2/5) outerDiagonal) : t∈Icc 0 outerDiagonal :=
    ⟨by linarith [ht.1],ht.2⟩
  have hc : ConcaveOn ℝ (Icc (2/5) outerDiagonal) (fun t => -TLabel.d1 t) :=
    concave_of_deriv2
      (fun t ht => (TLabel.d1_hasDerivAt (outer_domain (hdom ht))).neg)
      (fun t ht => (TLabel.d2_hasDerivAt (outer_domain (hdom ht))).neg)
      (fun t ht => by linarith [T_third_lower (hdom ht)])
  have hh := concave_gt_of_endpoints hc hb
    (show -(387/500:ℝ)< -TLabel.d1 (2/5) by linarith [two_fifths_slopes.1])
    (show -(387/500:ℝ)< -TLabel.d1 outerDiagonal by
      rw [T_first_diagonal]
      linarith [fine_outer_endpoint_bounds.2])
  linarith

theorem source_ratio_paid {b z : ℝ} (hb : b∈Icc (1/10) outerDiagonal)
    (hz : z∈UpperInverse.shifts) (hdiag : outerDiagonal-1/2≤z) :
    TLabel.d1 b<UpperInverse.F z b := by
  have hbf : b∈Icc 0 outerDiagonal := ⟨by linarith [hb.1],hb.2⟩
  by_cases hearly : b≤2/5
  · have hT := source_comparison ⟨hb.1,hearly⟩
    exact hT.trans (OppositeTwo.PrimaryInverse.F_paid hbf hz hdiag)
  · have hT := source_first_late ⟨by linarith,hb.2⟩
    have hu := U_positive (outer_domain hbf)
    have hq : 0<NegativeTwo.Inverse.q (U b) := by
      linarith [NegativeTwo.Inverse.actual_q_positive hbf]
    have hf := NegativeTwo.Inverse.factor_lower hu hq
    have hd := OppositeTwo.PrimaryInverse.data hbf hz
    have hn : 0≤z*ratio b/(NegativeTwo.Inverse.q (U b)*UpperInverse.speed z b) :=
      div_nonneg (mul_nonneg hz.1 (by linarith [(outer_ratio_bounds hbf).1]))
        (mul_nonneg hq.le hd.2.2.1.le)
    dsimp [UpperInverse.F,OppositeTwo.PrimaryInverse.F]
    linarith

lemma source_cost_monotone {z : ℝ} (hz : z∈UpperInverse.shifts)
    (hdiag : outerDiagonal-1/2≤z) :
    MonotoneOn (fun b => UpperInverse.X z b-T b) (Icc (1/10) outerDiagonal) := by
  have hdom {t : ℝ} (ht : t∈Icc (1/10) outerDiagonal) : t∈Icc 0 outerDiagonal :=
    ⟨by linarith [ht.1],ht.2⟩
  have hd {t : ℝ} (ht : t∈Icc (1/10) outerDiagonal) :
      HasDerivAt (fun b => UpperInverse.X z b-T b) (UpperInverse.F z t-TLabel.d1 t) t := by
    convert (OppositeTwo.PrimaryInverse.X_source_hasDerivAt (hdom ht) hz).sub
      (TLabel.outer_hasDerivAt (outer_domain (hdom ht))) using 1 <;> rfl
  exact monoOn_of_hasDeriv_nonneg
    (fun t ht => (hd ht).continuousAt.continuousWithinAt)
    (fun t ht => hd (Ioo_subset_Icc_self ht))
    (fun t ht => by linarith [source_ratio_paid (Ioo_subset_Icc_self ht) hz hdiag])

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.UpperTarget
