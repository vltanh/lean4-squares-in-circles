module

public import SquaresInCircles.Eight.TableFree.CommonSineEnvelope
public import SquaresInCircles.Eight.TableFree.CommonJumpTwo

/-!
# The critical positive source-secondary zero-quarter regimes

The original weak separator forces the frame angle above one tenth. In
the outer/outer case it also forces a transverse coordinate above `.28`;
one convex quadratic then supplies the stronger source-circle support.
The target is bounded by its full circle at the same original angle.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter

/-- All positive/positive source-secondary zero contacts lie in the same
complete positive-angle interval. -/
theorem zero_positive_secondary_angle {source target : RadialKind}
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 1 φ) :
    (1/10:ℝ)<φ := by
  have hs' := state_bounds hs
  have ht' := state_bounds ht
  have hc : 0<Real.cos φ := by linarith [(signed_cos hφ).1]
  have hw := width_ge_one φ
  have hφpos : 0<φ := by
    by_contra! hn
    have hsin : Real.sin φ≤0 := by
      have hp := positive_trig (x := -φ)
        ⟨by linarith,by linarith [(abs_le.mp hφ).1]⟩
      simpa only [Real.sin_neg,neg_nonneg] using hp.2.2.1
    have hAs := mul_nonpos_of_nonneg_of_nonpos (by linarith [ht'.1]) hsin
    have hBc := mul_nonneg ht'.2.2.1 hc.le
    norm_num [forwardMargin] at hm
    nlinarith [hs'.2.2.2.2]
  by_contra! hsmall
  have hx : φ∈Icc 0 (7/10) := ⟨hφpos.le,(abs_le.mp hφ).2⟩
  have hsin := positive_trig hx
  have hcos := cos_lower_two hx.1
  have hφ2 := pow_le_pow_left₀ hx.1 hsmall 2
  have hAc := mul_le_mul_of_nonneg_right ht'.2.1.le hsin.2.2.1
  have hBc := mul_nonneg ht'.2.2.1 hc.le
  have hwidth : pairWidth φ=(1+Real.cos φ+Real.sin φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg hsin.2.2.1]
  norm_num [forwardMargin] at hm
  rw [hwidth] at hm
  nlinarith [hs'.2.2.2.2,hsin.2.2.2.2.1]

/-- Actual target-circle support for the entire sine-norm family. -/
theorem sine_target_support {A B l x : ℝ} (ht : OuterState A B) :
    ((13/200:ℝ)+(203/200)+l*(Real.sin x-Real.cos x))/2-
      radius*SineEnvelope.N l x≤
        (-(13/200)-l*Real.sin x)*A+(l*Real.cos x-(203/200))*B := by
  have hh := outer_circle_lower (X := -(13/200)-l*Real.sin x)
    (Y := l*Real.cos x-(203/200)) ht
  have hr : (-(13/200)-l*Real.sin x)^2+(l*Real.cos x-(203/200))^2=
      CircularNorm.energy (SineEnvelope.mass l) (SineEnvelope.cosCoeff l)
        (SineEnvelope.sinCoeff l) x := by
    rw [SineEnvelope.energy_identity]
    ring
  rw [hr] at hh
  change -((-(13/200)-l*Real.sin x)+(l*Real.cos x-(203/200)))/2-
    radius*SineEnvelope.N l x≤_ at hh
  linarith

/-- Positive core source and positive outer target, with the original
secondary axis and the complete closed core boundary. -/
theorem zero_core_outer_positive {a b A B φ : ℝ}
    (hs : CorePairGeometry.CoreState a b) (ht : OuterState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 1 φ) :
    (391/400:ℝ)<φ+coreLabel a b-outerLabel A B := by
  have hs' : State .coreSide a b := by simpa [State] using hs
  have ht' : State .outer A B := by simpa [State] using ht
  have hp := zero_positive_secondary_angle hs' ht' hφ hm
  have hx : φ∈Icc (1/10) (7/10) := ⟨hp.le,(abs_le.mp hφ).2⟩
  have htrig := positive_trig (show φ∈Icc 0 (7/10) from ⟨by linarith,hx.2⟩)
  have hw : pairWidth φ=(1+Real.cos φ+Real.sin φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg htrig.2.2.1]
  have hsource := core_label_lower hs
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.1
  have htarget := sine_target_support (l := (21/20:ℝ)) ht
  have hmul := mul_nonneg (show (0:ℝ)≤21/20 by norm_num) hm
  norm_num [forwardMargin] at hmul
  rw [hw] at hmul
  have hlower : 231/200+SineEnvelope.base (21/20) φ≤
      φ+coreLabel a b-outerLabel A B := by
    dsimp [SineEnvelope.base,outerLabel]
    nlinarith
  exact (SineEnvelope.zero_core_outer_positive hx).trans_le hlower

/-- The positive outer source coordinate is bounded away from its axis by
the original separator, before choosing the support multiplier. -/
theorem zero_outer_positive_source_cut {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B 1 1 φ) : (7/25:ℝ)<b := by
  have hs' : State .outer a b := by simpa [State] using hs
  have ht' : State .outer A B := by simpa [State] using ht
  have hp := zero_positive_secondary_angle hs' ht' hφ hm
  have hx : φ∈Icc 0 (7/10) := ⟨by linarith,(abs_le.mp hφ).2⟩
  have htrig := positive_trig hx
  have hA := (state_bounds ht').2.1
  have hAs := mul_le_mul_of_nonneg_right hA.le htrig.2.2.1
  have hBc := mul_nonneg ht.1 (show 0≤Real.cos φ by linarith [htrig.1])
  have hw : pairWidth φ=(1+Real.cos φ+Real.sin φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg htrig.2.2.1]
  norm_num [forwardMargin] at hm
  rw [hw] at hm
  nlinarith [htrig.1,htrig.2.2.2.1]

/-- One convex quadratic proves the sloping source support on the entire
closed coordinate range forced by the original contact. -/
theorem outer_source_sloping_lower {a b : ℝ} (hs : OuterState a b)
    (hb : (7/25:ℝ)≤b) : (3/2:ℝ)<a+(7/10)*b := by
  have h := outer_bounds hs
  have hbu : b≤9/10 := h.2.2.2.1.trans outer_endpoint_bounds.2.2.2.le
  have hpoly := mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hbu)
  have hquadratic : (b+1/2)^2+(2-(7/10)*b)^2<Q0 := by
    norm_num [Q0]
    nlinarith
  by_contra! hbad
  have ha0 : 0≤a+1/2 := by linarith [hs.1,hs.2.1]
  have hasq := pow_le_pow_left₀ ha0
    (show a+1/2≤2-(7/10)*b by linarith) 2
  nlinarith [hs.2.2]

/-- The critical positive outer/outer zero-quarter regime is closed on the
whole actual circle and angle interval. -/
theorem zero_outer_outer_positive {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B 1 1 φ) :
    (391/400:ℝ)<φ+outerLabel a b-outerLabel A B := by
  have hs' : State .outer a b := by simpa [State] using hs
  have ht' : State .outer A B := by simpa [State] using ht
  have hp := zero_positive_secondary_angle hs' ht' hφ hm
  have hx : φ∈Icc (1/10) (7/10) := ⟨hp.le,(abs_le.mp hφ).2⟩
  have hb := zero_outer_positive_source_cut hs ht hφ hm
  have hsource := outer_source_sloping_lower hs hb.le
  have htrig := positive_trig (show φ∈Icc 0 (7/10) from ⟨by linarith,hx.2⟩)
  have hw : pairWidth φ=(1+Real.cos φ+Real.sin φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg htrig.2.2.1]
  have htarget := sine_target_support (l := (1939/2000:ℝ)) ht
  have hmul := mul_nonneg (show (0:ℝ)≤1939/2000 by norm_num) hm
  norm_num [forwardMargin] at hmul
  rw [hw] at hmul
  have hlower : 4489/4000+SineEnvelope.base (1939/2000) φ<
      φ+outerLabel a b-outerLabel A B := by
    dsimp [SineEnvelope.base,outerLabel]
    nlinarith
  exact (SineEnvelope.zero_outer_positive hx).trans hlower

end SquaresInCircles.Eight.CommonQuarter
