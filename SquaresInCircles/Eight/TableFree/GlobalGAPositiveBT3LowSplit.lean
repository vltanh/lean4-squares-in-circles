module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3Split

/-!
# Positivity on the whole small-total split

Uncompiled Section 3. The sum of the two sine arguments is bounded
by the fixed total, and both cosines exceed 71/72. This gives the
displayed curvature bound below -4/5 before the additional negative
curvature from D's exact diagonal support is included.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Analytic
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open NonnegativeTotals

theorem low_rest_curvature {t a : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) (ha : a∈Icc 0 t) :
    TwoPositive.Split.smoothDD (lowM t) t a+TwoPositive.ASupport.axialDD a< -(4/5:ℝ) := by
  have haL : a∈Icc 0 (1/6:ℝ) := ⟨ha.1,ha.2.trans ht.2⟩
  have huL : t-a∈Icc 0 (1/6:ℝ) := ⟨by linarith [ha.2],by linarith [ht.2,ha.1]⟩
  have hm := (low_ranges ht).2
  have hm0 : 0≤lowM t := by linarith [hm.1]
  have hca := TwoPositive.Split.low_trig haL
  have hcu := TwoPositive.Split.low_trig huL
  have hcosM := mul_le_mul_of_nonneg_right
    (show (1:ℝ)≤lowM t by linarith [hm.1]) (show 0≤Real.cos (t-a) by linarith [hcu.1])
  have hsig := mul_le_mul_of_nonneg_right
    (show PositiveTD.sigma-1/2≤229/250 by linarith [TwoPositive.Split.sigma_bound]) hcu.2.1
  have hsigM := mul_le_mul_of_nonneg_left hsig hm0
  have hsM := mul_le_mul_of_nonneg_right
    (show lowM t≤6/5 by dsimp [Cmax] at hm; linarith [hm.2]) hcu.2.1
  have hax := mul_le_mul_of_nonneg_right
    (show axial-1/2≤183/200 by linarith [axial_bounds.2]) hca.2.1
  have hsum : Real.sin a+Real.sin (t-a)≤1/6 := by
    linarith [Real.sin_le ha.1,Real.sin_le huL.1,ht.2]
  dsimp [TwoPositive.Split.smoothDD,TwoPositive.ASupport.axialDD]
  nlinarith only [hcosM,hsigM,hsM,hax,hsum,hca.1,hca.2.1,hcu.1]

def lowVariable (t a : ℝ) : ℝ :=
  TwoPositive.Split.axialRest 0 (lowM t) 1 t a+
    (1-GlobalGA.Secondary.diagonal)*PositiveTD.tilted (lowM t) (t-a)

theorem lowVariable_concave {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    ConcaveOn ℝ (Icc 0 t) (lowVariable t) := by
  have htf := PositiveTD.Certificate.low_frame_domain ht
  have hm : 0<lowM t := by linarith [(low_ranges ht).2.1]
  have hd : 0≤1-GlobalGA.Secondary.diagonal := by linarith [diagonal_bounds.2]
  apply concave_of_deriv2
    (f' := fun a => TwoPositive.Split.smoothD (lowM t) t a+
      TwoPositive.ASupport.axialD a+(1-GlobalGA.Secondary.diagonal)*TwoPositive.Split.mD (lowM t) t a)
    (f'' := fun a => TwoPositive.Split.smoothDD (lowM t) t a+
      TwoPositive.ASupport.axialDD a-(1-GlobalGA.Secondary.diagonal)*PositiveTD.tilted (lowM t) (t-a))
  · intro a _
    have hh := (TwoPositive.Split.axial_derivative 0 (lowM t) 1 t a).add
      ((TwoPositive.Split.tilted_derivative (lowM t) t a).const_mul (1-GlobalGA.Secondary.diagonal))
    convert hh using 1
    · funext x; simp only [lowVariable,Pi.add_apply]
    · ring
  · intro a _
    have hh := ((TwoPositive.Split.smooth_second (lowM t) t a).add
      (TwoPositive.ASupport.axial_second a)).add
        ((TwoPositive.Split.tilted_second (lowM t) t a).const_mul (1-GlobalGA.Secondary.diagonal))
    convert hh using 1; ring
  · intro a ha
    have hc := low_rest_curvature ht ha
    have hpos := PositiveTD.tilted_pos hm (TwoPositive.Split.split_domain htf ha).2
    have hh := mul_nonneg hd hpos.le
    linarith

def lowFixed (t : ℝ) : ℝ :=
  lowK t+4-2*fullSupport (lowK t) 1-fullSupport 1 (lowM t)-GlobalGA.Secondary.diagonal+V R (lowK t) 1 t

theorem low_split_form {t a : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) (ha : a∈Icc 0 t) :
    lowScalar t a=lowFixed t+lowVariable t a := by
  have htf := PositiveTD.Certificate.low_frame_domain ht
  have hz := (TwoPositive.Split.split_domain htf ha).2
  rw [lowScalar,TwoPositive.ASupport.charge_low (ha.2.trans ht.2)]
  dsimp [lowBaseline,lowFixed,lowVariable,TwoPositive.Split.axialRest]
  rw [TwoPositive.Split.smooth_actual hz,tilted_eq]
  ring

theorem lowScalar_concave {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    ConcaveOn ℝ (Icc 0 t) (lowScalar t) := by
  have hc := lowVariable_concave ht
  refine ⟨hc.1,?_⟩
  intro a ha b hb u v hu hv huv
  have hh := hc.2 ha hb hu hv huv
  rw [low_split_form ht ha,low_split_form ht hb,low_split_form ht (hc.1 ha hb hu hv huv)]
  simp only [smul_eq_mul] at hh ⊢
  have hconst := congrArg (fun z : ℝ => z*lowFixed t) huv
  nlinarith only [hh,hconst]

theorem low_scalar_positive {t a : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) (ha : a∈Icc 0 t) :
    0<lowScalar t a := by
  have hleft : 0<lowScalar t 0 := by
    simpa only [NonnegativeTotals.Analytic.aAt] using low_endpoint_positive .atT ht
  have hright : 0<lowScalar t t := by
    simpa only [NonnegativeTotals.Analytic.aAt] using low_endpoint_positive .atA ht
  exact concave_gt_of_endpoints (lowScalar_concave ht) ha hleft hright

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Analytic
