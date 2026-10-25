module

public import SquaresInCircles.Eight.Owners.Exceptional.NegativeTSortedGain

/-!
# Eight squares: sorted-D improvement of the literal original contact stress

D's actual force has no ordinary rotation in either
negative-primary row. Its sorted support is substituted only after the
fixed-source G/E split expression has been formed. Every source point,
the original EH0 contact and the original q remain unchanged.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalNegativeTSortedStress
open Candidate SignedStress ActualSortedSupport PositiveAngularEnvelope ActualCoreEBlocks
open ExceptionalContactStress ExceptionalNegativeTStress ExceptionalECoefficients
open CriticalNegativeTOrdinaryData (bWeight tWeight shortDomain short_small)
open ExceptionalNegativeTSortedGain

theorem D_force {C : SignedCycle} (ab : Fin 4) (td : Bool) (k l c eta s x e : ℝ)
    (halign : td=false → delta C.theta T=0) :
    forces C ab td k l c eta s x e D=(1,-tWeight td c s) := by
  rw [ExceptionalNegativeTStress.forces,SoleEStress.force_D (td_cases td) (Or.inr rfl)]
  cases td <;> simp [tdOwner,ordinaryDE,rotatedPair,halign]

theorem anchorWork_sorted {C : SignedCycle} {ab : Fin 4} (td : Bool)
    {q c s : ℝ} (k l eta x e : ℝ) (hab : ab=0 ∨ ab=2)
    (hq : 0≤q) (hc0 : 0<c) (hs : s∈Icc 0 frameCap)
    (hpoints : ∀ i,(C.point i).Sorted) (hcircle : ∀ i,(C.point i).Contained q)
    (hn : C.NormalAnchors) (halign : td=false → delta C.theta T=0) :
    anchorWork C ab td k l c eta s x e+
      full q 1 (tWeight td c s)-ActualSortedSupport.support q 1 (tWeight td c s)≤
        anchorSupport C ab td (Real.sqrt q) k l c eta s x e := by
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  have ht0 : 0<tWeight td c s := by cases td <;> simp [tWeight] <;> positivity
  have hD := actual_negative_support hq (hpoints D) hn.D_nonpos (hcircle D)
    (show 0≤1+tWeight td c s by positivity)
  have hFD := D_force ab td k l c eta s x e halign
  have hDwork : work (forces C ab td k l c eta s x e D) (C.point D)≤
      ActualSortedSupport.support q 1 (tWeight td c s) := by
    rw [hFD]
    dsimp [work] at *
    linarith
  have hDfull : SecondaryEStress.signedSupport (Real.sqrt q) (-1)
      (ExceptionalNegativeTStress.forces C ab td k l c eta s x e D)=
      full q 1 (tWeight td c s) := by
    rw [hFD]
    simp only [SecondaryEStress.signedSupport,full,neg_sq,one_pow]
    ring
  have hH := work_le_signed_support (Real.sqrt_nonneg q)
    (show (C.point H).Contained ((Real.sqrt q)^2) by simpa [Real.sq_sqrt hq] using hcircle H)
    (Or.inl rfl) (by simp [abs_of_nonneg hn.H_nonneg]) (forces C ab td k l c eta s x e H)
  have hA := work_le_signed_support (Real.sqrt_nonneg q)
    (show (C.point A).Contained ((Real.sqrt q)^2) by simpa [Real.sq_sqrt hq] using hcircle A)
    (Or.inl rfl) (by simp [abs_of_nonneg hn.A_nonneg]) (forces C ab td k l c eta s x e A)
  have hB := work_le_signed_support (Real.sqrt_nonneg q)
    (show (C.point B).Contained ((Real.sqrt q)^2) by simpa [Real.sq_sqrt hq] using hcircle B)
    (Or.inr rfl) (by simp [abs_of_nonpos hn.B_nonpos]) (forces C ab td k l c eta s x e B)
  have hsum := SoleEStress.sum_bounds C hab (bt_cases td) (td_cases td)
    (Or.inr rfl) (Or.inl rfl) (k*tilt eta x) k l (bWeight td c s) (tWeight td c s) 1 (tilt eta e) (Real.sqrt q)
  simp only [SoleEStress.bound,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero] at hsum
  dsimp only [ExceptionalNegativeTStress.anchorWork,ExceptionalNegativeTStress.anchorSupport,
    ExceptionalNegativeTStress.forces,SecondaryEStress.signedSupport] at *
  linarith

theorem improved_value_lower {C : SignedCycle} {ab : Fin 4} (td : Bool)
    {q k l c eta t s x : ℝ} (hab : ab=0 ∨ ab=2) (hq : 0≤q)
    (hc0 : 0<c) (heta : 0≤eta) (ht : t∈Icc 0 frameCap) (hx : x∈Icc 0 t)
    (hs : s∈Icc 0 frameCap) (hpoints : ∀ i,(C.point i).Sorted)
    (hcircle : ∀ i,(C.point i).Contained q) (hn : C.NormalAnchors)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hcontact : Contact C)
    (hsource : primary C td= -s) (hflat : (C.point T).a=7/12)
    (halign : td=false → delta C.theta T=0) :
    ExceptionalContactSupport.baseline (Real.sqrt q) k l c eta x (t-x)+
      gain td (Real.sqrt q) l c s+increment C ab td (Real.sqrt q) k l c eta s x (t-x)+
        full q 1 (tWeight td c s)-ActualSortedSupport.support q 1 (tWeight td c s)≤
          value C ab td (Real.sqrt q) k l c eta t s x := by
  have he : t-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [ht.2,hx.1]⟩
  have hw := anchorWork_sorted td k l eta x (t-x) hab hq hc0 hs hpoints hcircle hn halign
  have hT := T_work ab td k l c eta x (t-x) hs hsource hflat
  have hE := ExceptionalContactSupport.eWork_le (Real.sqrt_nonneg q) heta he
    (hpoints E) (show (C.point E).Contained ((Real.sqrt q)^2) by simpa [Real.sq_sqrt hq] using hcircle E)
  have hid := decomposition td (Real.sqrt q) k l c eta x (t-x) hab ha hs hsource halign
  rw [value_eq_stress td (Real.sqrt q) k l c eta s hab ht hx hn hcontact]
  dsimp only [ExceptionalNegativeTStress.stress]
  linarith

theorem coefficient_ratio {b : Band} {t : ℝ} (ht : t∈domain b) :
    117/200≤ell b t/c b t := by
  have hc := (ranges ht).2.2.2.1
  apply (le_div_iff₀ hc).2
  by_cases hb : b=.low
  · subst b
    have hh := (low_correlations ht).1
    nlinarith [mul_nonneg ht.1 hc.le]
  · have hh := (balanced_bounds hb ht).2.2.2.2.2.1
    nlinarith

theorem source_lower {C : SignedCycle} {ab : Fin 4} (td : Bool)
    {q t s x : ℝ} {b : Band} (hab : ab=0 ∨ ab=2)
    (hQL : qLow≤q) (hQU : q≤qCap) (ht : t∈domain b) (hx : x∈Icc 0 t)
    (hs : s∈shortDomain td) (hpoints : ∀ i,(C.point i).Sorted)
    (hcircle : ∀ i,(C.point i).Contained q) (hn : C.NormalAnchors)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hcontact : Contact C)
    (hsource : primary C td= -s) (hflat : (C.point T).a=7/12)
    (halign : td=false → delta C.theta T=0) :
    ExceptionalContactSupport.baseline (Real.sqrt q) (k b t) (ell b t) (c b t) (eta b t) x (t-x)+
      correction b td t+lowerGain b td t s+
        increment C ab td (Real.sqrt q) (k b t) (ell b t) (c b t) (eta b t) s x (t-x)≤
          value C ab td (Real.sqrt q) (k b t) (ell b t) (c b t) (eta b t) t s x := by
  have hq : 0≤q := by norm_num [qLow] at hQL; linarith
  have hc := (ranges ht).2.2.2.1
  have he : 0≤eta b t := by linarith [(ranges ht).2.2.2.2.2.1]
  cases td
  · have hs' : s∈Icc 0 (9/100:ℝ) := by simpa [shortDomain] using hs
    have hh := ExceptionalNegativeTStress.value_lower (k := k b t) (l := ell b t) (c := c b t)
      false hab (Real.sqrt_nonneg q) he (angle ht) hx
      (short_small hs) hpoints (fun i => by simpa [Real.sq_sqrt hq] using hcircle i)
      hn ha hcontact hsource hflat halign
    have hg : (21/20)*c b t*s≤gain false (Real.sqrt q) (ell b t) (c b t) s := by
      by_cases hz : s=0
      · simp [hz,gain,FlatTStress.secantCharge]
      · have hs0 : 0<s := lt_of_le_of_ne hs'.1 (Ne.symm hz)
        have hgain := mul_lt_mul_of_pos_left
          (SoleNegativeTGain.BT_strict hq hQU (coefficient_ratio ht) ⟨hs0,hs'.2⟩) hc
        simp only [gain,Bool.false_eq_true,↓reduceIte]
        rw [CriticalNegativeTCurvature.charge_eq_gain hc (short_small hs)]
        linarith
    simpa only [correction,Bool.false_and,Bool.false_eq_true,↓reduceIte,lowerGain] using
      (by linarith :
      ExceptionalContactSupport.baseline (Real.sqrt q) (k b t) (ell b t) (c b t) (eta b t) x (t-x)+
        0+(21/20)*c b t*s+increment C ab false (Real.sqrt q) (k b t) (ell b t) (c b t) (eta b t) s x (t-x)≤
          value C ab false (Real.sqrt q) (k b t) (ell b t) (c b t) (eta b t) t s x)
  · have hs' : s∈Icc 0 (3/10:ℝ) := by simpa [shortDomain] using hs
    have hh := improved_value_lower (k := k b t) (l := ell b t) true hab hq hc he (angle ht) hx
      (short_small hs)
      hpoints hcircle hn ha hcontact hsource hflat halign
    have hg := corrected_gain hQL hQU ht hs'
    simp only [tWeight,↓reduceIte] at hh
    simp only [lowerGain,↓reduceIte]
    linarith

end SquaresInCircles.Eight.ExceptionalNegativeTSortedStress
