module

public import SquaresInCircles.Eight.Owners.CorrelatedSameBlock

/-!
# Eight squares: same-block comparisons after the short BT secant enlargement

The negative comparison retains `31/10000` of
slack in the correlated ratio; the positive comparison only needs ratio
`29/50`. These reserves cover the actual factor `cos s`, `s ≤ .09`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.RelaxedSameBlock
open PositiveAngularEnvelope OrdinaryAngleConcavity CorrelatedSameBlock
open PositiveStressCoefficients

theorem relaxed_saturated_trig {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0≤(ratio d-31/10000)*(PositiveAngularEnvelope.phi (frameCap-d)-1)+Real.cos frameCap-Real.cos d := by
  let a : ℝ := frameCap-d
  have ha : a∈Icc 0 frameCap := ⟨by dsimp [a]; linarith [hd.2],
    by dsimp [a]; linarith [hd.1]⟩
  have hsin := (transport_trig ha).2.2.1
  have hh : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hr : ratio d≤1527/2000 := (coefficient_bounds hd).2.2.2.2.2.2.2.2.2
  have hfactor : 0≤Real.cos frameCap-(ratio d-31/10000) := by
    linarith [(transport_trig hh).1]
  have hhalf := mul_le_mul_of_nonneg_left (half_angle_lower ha) hfactor
  have hbracket := correlated_bracket hd
  have hbr0 : 0≤ratio d-31/10000-Real.sin frameCap+
      (Real.cos frameCap-(ratio d-31/10000))*a/2 := by
    have ha0 : 0≤a := ha.1
    have hb := hbracket
    dsimp only [a] at ha0 ⊢
    simp only [frameCap] at hb ha0 ⊢
    linarith
  have hpositive := mul_nonneg hsin hbr0
  have hcos : Real.cos d=Real.cos frameCap*Real.cos a+
      Real.sin frameCap*Real.sin a := by
    rw [← Real.cos_sub]
    congr 1
    dsimp [a]
    ring
  change 0≤(ratio d-31/10000)*(PositiveAngularEnvelope.phi a-1)+Real.cos frameCap-Real.cos d
  rw [hcos]
  dsimp [PositiveAngularEnvelope.phi]
  nlinarith

theorem negative_surplus {R p q d s : ℝ} (hq : 0≤q)
    (hratio : (ratio d-31/10000)*q≤p)
    (hd : d∈Icc 0 frameCap) (hs : s∈Icc 0 d) :
    V R p q (d-s)≤ mixedBlock R p q (frameCap-d) (frameCap-s) := by
  have ha : frameCap-d∈Icc 0 frameCap := ⟨by linarith [hd.2],by linarith [hd.1]⟩
  have hw : d-s∈Icc 0 (frameCap-(frameCap-d)) :=
    ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hd' : d∈Icc 0 (frameCap-(frameCap-d)) := ⟨hd.1,by linarith⟩
  have hcos := cosine_increment_anti ha hw hd' (by linarith [hs.1])
  have hcos' : Real.cos frameCap-Real.cos d≤
      Real.cos (frameCap-s)-Real.cos (d-s) := by
    convert hcos using 1 <;> congr 1 <;> ring
  have hp := mul_le_mul_of_nonneg_right hratio (sub_nonneg.mpr (one_le_phi ha))
  have hqcos := mul_le_mul_of_nonneg_left hcos' hq
  have htrig := mul_nonneg hq (relaxed_saturated_trig hd)
  have harg : frameCap-d-(frameCap-s)= -(d-s) := by ring
  dsimp [V,mixedBlock]
  rw [harg]
  nlinarith

private def surplusTrig (N : ℝ) : ℝ :=
  (29/50)*(PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N))+Real.cos N-1

private theorem surplusTrig_nonneg {N : ℝ} (hN : N∈Icc 0 frameCap) :
    0≤ surplusTrig N := by
  have hconc : ConcaveOn ℝ (Icc 0 frameCap) surplusTrig := by
    apply concave_of_deriv2
      (f' := fun t => (29/50)*(Real.cos (frameCap-t)-Real.sin (frameCap-t))-Real.sin t)
      (f'' := fun t => (29/50)*PositiveAngularEnvelope.phi (frameCap-t)-Real.cos t)
    · intro t _
      have ha := (hasDerivAt_id t).const_sub frameCap
      have hraw := ((((hasDerivAt_const t (PositiveAngularEnvelope.phi frameCap)).sub
        ((phi_hasDerivAt (frameCap-t)).comp t ha)).const_mul (29/50)).add
          (Real.hasDerivAt_cos t)).sub_const 1
      convert hraw using 1
      · rfl
      · ring
    · intro t _
      have ha := (hasDerivAt_id t).const_sub frameCap
      exact (((ha.cos.fun_sub ha.sin).const_mul (29/50)).fun_sub
        (Real.hasDerivAt_sin t)).congr_deriv (by simp only [PositiveAngularEnvelope.phi,id]; ring)
    · intro t ht
      obtain ⟨hc,_,hs0,hs,hsc⟩ := transport_trig
        (show frameCap∈Icc 0 frameCap by constructor; norm_num [frameCap]; rfl)
      have hct : 0≤Real.cos t := by linarith [(transport_trig ht).1]
      have hst := (transport_trig ht).2.2.1
      have hfirst : 0≤(1-(29/50)*PositiveAngularEnvelope.phi frameCap)*Real.cos t := by
        apply mul_nonneg _ hct
        dsimp [PositiveAngularEnvelope.phi]
        linarith [Real.cos_le_one frameCap]
      have hsecond := mul_nonneg
        (show 0≤(29/50)*(Real.cos frameCap-Real.sin frameCap) by linarith) hst
      have he : PositiveAngularEnvelope.phi (frameCap-t)=PositiveAngularEnvelope.phi frameCap*Real.cos t+
          (Real.sin frameCap-Real.cos frameCap)*Real.sin t := by
        simp only [PositiveAngularEnvelope.phi,Real.cos_sub,Real.sin_sub]
        ring
      rw [he]
      nlinarith
  have hmin := hconc.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by constructor; norm_num [frameCap]; rfl) hN
  have hz : surplusTrig 0=0 := by simp [surplusTrig]
  have hh : 0≤surplusTrig frameCap := by
    have hphi := phi_cap_lower
    have hc := (transport_trig (show frameCap∈Icc 0 frameCap by
      constructor; norm_num [frameCap]; rfl)).1
    simp only [surplusTrig,sub_self,PositiveAngularEnvelope.phi,Real.cos_zero,Real.sin_zero,add_zero]
    dsimp [PositiveAngularEnvelope.phi] at hphi
    linarith
  rw [hz,min_eq_left hh] at hmin
  exact hmin

theorem positive_surplus {R p q P N : ℝ} (hq : 0≤q)
    (hratio : (29/50)*q≤p) (hP : P∈Icc 0 frameCap) (hN : N∈Icc 0 P) :
    U R p q (P-N)≤ mixedBlock R p q P N := by
  have hN' : N∈Icc 0 frameCap := ⟨hN.1,hN.2.trans hP.2⟩
  have hw : P-N∈Icc 0 frameCap := ⟨by linarith [hN.2],by linarith [hP.2,hN.1]⟩
  have hincrement := sub_nonneg.mpr (phi_mono hw hP (by linarith [hN.1]))
  have hi := phi_increment_anti hN'
    (show P-N∈Icc 0 (frameCap-N) from ⟨hw.1,by linarith [hP.2]⟩)
    (show frameCap-N∈Icc 0 (frameCap-N) from ⟨by linarith [hN'.2],le_rfl⟩)
    (by linarith [hP.2])
  have hi' : PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N)≤PositiveAngularEnvelope.phi P-PositiveAngularEnvelope.phi (P-N) := by
    convert hi using 1 <;> congr 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_right hratio hincrement
  have hmin := mul_le_mul_of_nonneg_left hi' (show 0≤(29/50 : ℝ)*q by positivity)
  have hbase := mul_nonneg hq (surplusTrig_nonneg hN')
  dsimp [surplusTrig] at hbase
  dsimp [U,mixedBlock]
  nlinarith

end SquaresInCircles.Eight.RelaxedSameBlock
