module

public import SquaresInCircles.Eight.Owners.Primary.Cap

/-!
# Eight squares: strict concavity on the intrinsic paired-negative-E contact interval

The EH cap and its intrinsic zero-tangent endpoint are the `PrimaryCap` functions. The required D
coordinate `requiredD` has second derivative below `-11/240` on the whole interval, without a
subdivision of the angle (`requiredSecond_negative`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PairedNegativeE
open PrimaryCap

def requiredD (P v x : ℝ) : ℝ :=
  1/2+(1-value P x)*Real.cos (v-x)+K*Real.sin (v-x)

def requiredDerivative (P v x : ℝ) : ℝ :=
  Real.sin (v-x)-value P x*Real.sin v/Real.cos x

def requiredSecond (P v x : ℝ) : ℝ :=
  -Real.cos (v-x)+Real.sin v/Real.cos x*
    (K-2*value P x*(Real.sin x/Real.cos x))

theorem requiredD_hasDerivAt (P v x : ℝ) (hc : Real.cos x≠0) :
    HasDerivAt (requiredD P v) (requiredDerivative P v x) x := by
  have hD : HasDerivAt (value P)
      (value P x*(Real.sin x/Real.cos x)-K) x := by
    simpa only [derivative_rewrite P x hc,Real.tan_eq_sin_div_cos]
      using value_hasDerivAt P x hc
  have hx : HasDerivAt (fun z : ℝ => v-z) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub v
  have hc' := (Real.hasDerivAt_cos (v-x)).comp x hx
  have hs' := (Real.hasDerivAt_sin (v-x)).comp x hx
  have hd := (((hD.const_sub 1).mul hc').const_add (1/2)).add (hs'.const_mul K)
  convert hd using 1
  · rfl
  · dsimp [requiredDerivative]
    have hv : Real.sin v=Real.sin (v-x)*Real.cos x+Real.cos (v-x)*Real.sin x := by
      rw [←Real.sin_add]
      congr 1
      ring
    rw [hv]
    field_simp [hc]
    ring

theorem requiredDerivative_hasDerivAt (P v x : ℝ) (hc : Real.cos x≠0) :
    HasDerivAt (requiredDerivative P v) (requiredSecond P v x) x := by
  have hD : HasDerivAt (value P)
      (value P x*(Real.sin x/Real.cos x)-K) x := by
    simpa only [derivative_rewrite P x hc,Real.tan_eq_sin_div_cos]
      using value_hasDerivAt P x hc
  have hx : HasDerivAt (fun z : ℝ => v-z) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub v
  have hs := (Real.hasDerivAt_sin (v-x)).comp x hx
  have hd := hs.sub ((hD.const_mul (Real.sin v)).div (Real.hasDerivAt_cos x) hc)
  convert hd using 1
  · funext z
    simp only [requiredDerivative,Pi.sub_apply,Pi.div_apply,Function.comp_apply]
    ring
  · dsimp [requiredSecond]
    field_simp [hc]
    ring

/-- Multiplication by the positive cosine exposes the two negative terms of the bound on the whole
interval. -/
theorem curvature_identity (P v x : ℝ) (hc : Real.cos x≠0) :
    Real.cos x*requiredSecond P v x=
      -Real.cos v+Real.cos v*(Real.sin x)^2+K*Real.sin v-
        Real.sin v*Real.sin x*(Real.cos x+1/Real.cos x)-
        (2*value P x-1)*(Real.sin v*Real.sin x/Real.cos x) := by
  dsimp [requiredSecond]
  rw [Real.cos_sub,show (Real.sin x)^2=1-(Real.cos x)^2 by
    nlinarith [Real.sin_sq_add_cos_sq x]]
  field_simp [hc]
  ring

theorem requiredSecond_negative {P v x : ℝ}
    (hv : v∈Icc 0 (7/10:ℝ)) (hx : x∈Icc 0 v)
    (hcap : 1/2≤value P x) : requiredSecond P v x< -(11/240:ℝ) := by
  have hxwide : x∈Icc 0 (7/10:ℝ) := ⟨hx.1,hx.2.trans hv.2⟩
  obtain ⟨hcv,hsv0,hsv⟩ := transport_trig_coarse hv
  obtain ⟨hcx,hsx0,hsx⟩ := transport_trig_coarse hxwide
  have hc : 0<Real.cos x := by linarith
  have hsin : Real.sin x≤Real.sin v :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos,hx.1])
      (by linarith [hv.2,Real.pi_gt_three]) hx.2
  have hsec : 2≤Real.cos x+1/Real.cos x := by
    have hid : (Real.cos x+1/Real.cos x-2)*Real.cos x=(Real.cos x-1)^2 := by
      field_simp [hc.ne']
      ring
    nlinarith [sq_nonneg (Real.cos x-1)]
  have hprod0 : 0≤Real.sin v*Real.sin x := mul_nonneg hsv0 hsx0
  have hprod := mul_le_mul_of_nonneg_left hsec hprod0
  have hsquare := mul_le_mul_of_nonneg_right hsin hsx0
  have hcos := mul_le_mul_of_nonneg_right (Real.cos_le_one v) (sq_nonneg (Real.sin x))
  have hextra : 0≤(2*value P x-1)*(Real.sin v*Real.sin x/Real.cos x) :=
    mul_nonneg (by linarith) (div_nonneg hprod0 hc.le)
  have hid := curvature_identity P v x hc.ne'
  have hreserve : Real.cos x*requiredSecond P v x< -(11/240:ℝ) := by
    dsimp [K] at hid
    nlinarith
  have hnegative : requiredSecond P v x<0 := by nlinarith
  have hmul := mul_le_mul_of_nonpos_right (Real.cos_le_one x) hnegative.le
  simp only [one_mul] at hmul
  exact hmul.trans_lt hreserve

/-- One intrinsic endpoint strictly improves the DE margin of the cycle. The cap root comes from
the intermediate value theorem, and the strict comparison from the curvature on the whole
interval. -/
theorem endpoint_decrease {P v t z : ℝ}
    (hP : 1/2<P ∧ P<183/200)
    (hv : v∈Ioc 0 (7/10:ℝ))
    (hz : z∈Ioo 0 (9/20:ℝ)) (hzval : value P z=1/2)
    (ht : t∈Ioo 0 (min v z)) :
    requiredD P v 0<requiredD P v t ∨
      requiredD P v (min v z)<requiredD P v t := by
  have hparam {x : ℝ} (hx : x∈Icc 0 (min v z)) :
      x∈Icc 0 v ∧ x∈Icc 0 (7/10:ℝ) ∧ 1/2≤value P x := by
    have hxv : x≤v := hx.2.trans (min_le_left _ _)
    have hxz : x≤z := hx.2.trans (min_le_right _ _)
    have hxwide : x∈Icc 0 (7/10:ℝ) := ⟨hx.1,hxv.trans hv.2⟩
    exact ⟨⟨hx.1,hxv⟩,hxwide,(cap_feasible_iff_before hP hz hzval hxwide).2 hxz⟩
  have hcos {x : ℝ} (hx : x∈Icc 0 (min v z)) : Real.cos x≠0 := by
    have h := (hparam hx).2.1
    exact (transport_cos_pos (by rw [abs_of_nonneg h.1]; exact h.2)).ne'
  apply strict_endpoint_of_second_derivative (df:=requiredDerivative P v)
    (ddf:=requiredSecond P v) (k:=11/240) (by norm_num) ht
  · intro x hx
    exact requiredD_hasDerivAt P v x (hcos hx)
  · intro x hx
    exact requiredDerivative_hasDerivAt P v x (hcos hx)
  · intro x hx
    exact (requiredSecond_negative ⟨hv.1.le,hv.2⟩
      (hparam hx).1 (hparam hx).2.2).le

end SquaresInCircles.Eight.GlobalGA.PairedNegativeE
