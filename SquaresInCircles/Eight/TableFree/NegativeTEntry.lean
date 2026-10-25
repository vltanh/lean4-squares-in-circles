module

public import SquaresInCircles.Eight.TableFree.NegativePrimaryEntry

/-!
# Actual negative T entry for the positive-primary exclusion

Uncompiled source. A negative TD2 is either already secondary at the
unchanged points, or is a true flat-core contact shorter than 3/10. A sole
negative BT3 with aligned TD0 is flat and shorter than 9/100. Every radial
comparison uses the original q; only numerical reserves use qCap.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.NegativeTEntry

theorem center_norm_lt {q : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hc : P.Contained q) (hq : q≤qCap) :
    Real.sqrt (P.a^2+P.y^2)<283/200 := by
  have hr := Real.sq_sqrt (show 0≤P.a^2+P.y^2 by positivity)
  have hr0 := Real.sqrt_nonneg (P.a^2+P.y^2)
  have hb := abs_nonneg P.y
  have hab : Real.sqrt (P.a^2+P.y^2)≤P.a+|P.y| := by
    rw [Real.sqrt_le_left (by linarith [hs.1])]
    nlinarith [sq_abs P.y,mul_nonneg hs.1.le hb]
  have hh : (P.a+1/2)^2+(|P.y|+1/2)^2≤9789/2500 := hc.trans hq
  nlinarith [sq_abs P.y]

theorem unshifted_projection_le_norm (P : SignedPoint) (v : ℝ) :
    P.a*Real.cos v-P.y*Real.sin v≤Real.sqrt (P.a^2+P.y^2) := by
  have hid : (P.a*Real.cos v-P.y*Real.sin v)^2+
      (P.a*Real.sin v+P.y*Real.cos v)^2=
        (P.a^2+P.y^2)*((Real.sin v)^2+(Real.cos v)^2) := by ring
  rw [Real.sin_sq_add_cos_sq,mul_one] at hid
  have hr := Real.sq_sqrt (show 0≤P.a^2+P.y^2 by positivity)
  have hr0 := Real.sqrt_nonneg (P.a^2+P.y^2)
  nlinarith [sq_nonneg (P.a*Real.sin v+P.y*Real.cos v)]

theorem tangent_lt_from_BT2 {q v : ℝ} {B T : SignedPoint}
    (hBs : B.Sorted) (hBc : B.Contained q) (hq : q≤qCap)
    (hBT : quarterFeasible B T v 2) : T.y<83/200 := by
  have hn := center_norm_lt hBs hBc hq
  have hp := unshifted_projection_le_norm B v
  have hw := edgeWidth_ge_one v
  have hf : edgeWidth v≤B.a*Real.cos v-B.y*Real.sin v-T.y := by
    simpa [quarterFeasible,quarterProjection] using hBT
  linarith

theorem half_chord_lt {t : ℝ} (ht : t∈Ioc 0 frameCap) :
    1-Real.cos t<Real.sin t/2 := by
  obtain ⟨hc,hcu,hs0,hs,hsc⟩ := transport_trig ⟨ht.1.le,ht.2⟩
  have ht7 : t≤7/10 := ht.2
  have hsp : 0<Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [Real.pi_gt_three])
  have hu := Real.sin_sq_add_cos_sq t
  have hcl : Real.cos t<1 := by nlinarith
  by_contra! hbad
  have hm := mul_nonneg
    (show 0≤2*(1-Real.cos t)-Real.sin t by linarith)
    (show 0≤2*(1-Real.cos t)+Real.sin t by linarith)
  have hp := mul_pos (sub_pos.mpr hcl) (show 0<5*Real.cos t-3 by linarith)
  nlinarith

theorem negative_TD_signs {q t v : ℝ} {B T D : SignedPoint}
    (hBs : B.Sorted) (hTs : T.Sorted) (hDs : D.Sorted)
    (hBc : B.Contained q) (hDc : D.Contained q)
    (hDcore : D.AvoidsCore) (hq : q≤qCap) (hDy : D.y≤0)
    (ht : t∈Ioc 0 frameCap)
    (hBT : quarterFeasible B T v 2) (hTD : zeroFeasible T D (-t) 2) :
    0<T.y ∧ T.y<83/200 ∧ 1< -D.y+T.y ∧ T.y< -D.y := by
  have hyu := tangent_lt_from_BT2 hBs hBc hq hBT
  have hDu := (SignedPoint.coordinate_bounds hDs hDcore hDc hq).2.2
  rw [abs_of_nonpos hDy] at hDu
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig ⟨ht.1.le,ht.2⟩
  have hf : edgeWidth (-t)≤ -D.y+T.y*Real.cos t-T.a*Real.sin t := by
    have h : edgeWidth (-t)≤T.a*Real.sin (-t)+T.y*Real.cos (-t)-D.y := hTD
    rw [Real.sin_neg,Real.cos_neg] at h
    linarith
  have hw := edgeWidth_ge_one (-t)
  have ha := mul_nonneg hTs.1.le hs0
  have hy : 0<T.y := by
    by_contra! hbad
    have hm := mul_nonpos_of_nonpos_of_nonneg hbad (by linarith : 0≤Real.cos t)
    linarith
  have hm := mul_le_mul_of_nonneg_left hc1 hy.le
  have hsum : 1< -D.y+T.y := by
    have ht7 : t≤7/10 := ht.2
    have hspos := Real.sin_pos_of_pos_of_lt_pi ht.1
      (by linarith [Real.pi_gt_three])
    have hapos := mul_pos hTs.1 hspos
    linarith
  exact ⟨hy,hyu,hsum,by linarith⟩

/-- An outer T makes the original TD0 projection strictly larger than
the retained TD2 projection, at the same frames and original points. -/
theorem outer_negative_TD_reselect {q t v : ℝ} {B T D : SignedPoint}
    (hBs : B.Sorted) (hTs : T.Sorted) (hDs : D.Sorted)
    (hBc : B.Contained q) (hTo : T.Outer q) (hDc : D.Contained q)
    (hTcore : T.AvoidsCore) (hDcore : D.AvoidsCore)
    (hq : q≤qCap) (hDy : D.y≤0) (ht : t∈Ioc 0 frameCap)
    (hBT : quarterFeasible B T v 2) (hTD : zeroFeasible T D (-t) 2) :
    zeroProjection T D (-t) 2<zeroProjection T D (-t) 0 ∧
      zeroFeasible T D (-t) 0 := by
  obtain ⟨hy,hyu,hsum,hyD⟩ := negative_TD_signs hBs hTs hDs hBc hDc hDcore hq hDy ht hBT hTD
  have hTa := (SignedPoint.coordinate_bounds hTs hTcore hTo.le hq).2.1
  have hDa := (SignedPoint.coordinate_bounds hDs hDcore hDc hq).2.1
  have heq : (T.a+1/2)^2+(T.y+1/2)^2=q := by
    simpa [SignedPoint.Outer,SignedPoint.circle,abs_of_nonneg hy.le] using hTo
  have hineq : (D.a+1/2)^2+(-D.y+1/2)^2≤q := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos hDy] using hDc
  have hprod : (-D.y-T.y)*(-D.y+T.y+1)≤(T.a-D.a)*(T.a+D.a+1) := by nlinarith
  have hbd : 0< -D.y-T.y := by linarith
  have hmul := mul_lt_mul_of_pos_left (show (2:ℝ)< -D.y+T.y+1 by linarith) hbd
  have had : 0<T.a-D.a := by
    by_contra! hbad
    have hm := mul_nonpos_of_nonpos_of_nonneg hbad (show 0≤T.a+D.a+1 by linarith [hTs.1,hDs.1])
    nlinarith
  have htop := mul_lt_mul_of_pos_left (show T.a+D.a+1<(383/100 : ℝ) by linarith) had
  have hratio : (-D.y-T.y)/2<T.a-D.a := by linarith
  have hhalf := half_chord_lt ht
  have ht7 : t≤7/10 := ht.2
  have hsin : 0<Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [Real.pi_gt_three])
  have h1 := mul_lt_mul_of_pos_right hratio hsin
  have h2 := mul_lt_mul_of_pos_left hhalf hbd
  have hdiff : zeroProjection T D (-t) 2<zeroProjection T D (-t) 0 := by
    change T.a*Real.sin (-t)+T.y*Real.cos (-t)-D.y<
      T.y+D.a*Real.sin (-t)-D.y*Real.cos (-t)
    rw [Real.sin_neg,Real.cos_neg]
    linarith
  exact ⟨hdiff,hTD.trans hdiff.le⟩

theorem TD_short_harmonic_mono :
    StrictMonoOn (fun t : ℝ => (17/200)*Real.cos t+(13/12)*Real.sin t) (Icc 0 frameCap) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 frameCap)
  · fun_prop
  · intro t ht
    have hd : HasDerivAt (fun t : ℝ => (17/200)*Real.cos t+(13/12)*Real.sin t)
        ((17/200)*(-Real.sin t)+(13/12)*Real.cos t) t :=
      ((Real.hasDerivAt_cos t).const_mul (17/200 : ℝ)).add
        ((Real.hasDerivAt_sin t).const_mul (13/12 : ℝ))
    rw [hd.deriv]
    obtain ⟨hc,hcu,hs0,hs,hsc⟩ := transport_trig (interior_subset ht)
    linarith

theorem flat_negative_TD_short {q t v : ℝ} {B T D : SignedPoint}
    (hBs : B.Sorted) (hTs : T.Sorted) (hDs : D.Sorted)
    (hBc : B.Contained q) (hTc : T.Core) (hDc : D.Contained q)
    (hDcore : D.AvoidsCore) (hq : q≤qCap) (hDy : D.y≤0)
    (ht : t∈Ioc 0 frameCap)
    (hBT : quarterFeasible B T v 2) (hTD : zeroFeasible T D (-t) 2) :
    T.a=7/12 ∧ 0<T.y ∧ T.y<83/200 ∧ t<3/10 := by
  obtain ⟨hy,hyu,hsum,hyD⟩ := negative_TD_signs hBs hTs hDs hBc hDc hDcore hq hDy ht hBT hTD
  have hflat := (SignedPoint.flat_core_iff hTs (by rw [abs_of_pos hy]; linarith)).1 hTc
  have hDu := (SignedPoint.coordinate_bounds hDs hDcore hDc hq).2.2
  rw [abs_of_nonpos hDy] at hDu
  have hfeas := hTD
  rw [zeroFeasible,edgeWidth_negative_formula ⟨ht.1.le,ht.2⟩] at hfeas
  simp [zeroProjection,Real.sin_neg,Real.cos_neg,hflat] at hfeas
  have hc := (transport_trig ⟨ht.1.le,ht.2⟩).1
  have hyt := mul_lt_mul_of_pos_right hyu (show 0<Real.cos t by linarith)
  have hmargin : (17/200)*Real.cos t+(13/12)*Real.sin t<2/5 := by nlinarith
  have hshort : t<3/10 := by
    by_contra! hbad
    have hm := TD_short_harmonic_mono.monotoneOn
      (by constructor <;> norm_num [frameCap]) ⟨ht.1.le,ht.2⟩ hbad
    have hc0 := cos_lower_six (show (0:ℝ)≤3/10 by norm_num)
    have hs0 := sin_lower_seven (show (0:ℝ)≤3/10 by norm_num)
    norm_num at hc0 hs0
    linarith
  exact ⟨hflat,hy,hyu,hshort⟩

theorem negative_TD_entry {q t v : ℝ} {B T D : SignedPoint}
    (hBs : B.Sorted) (hTs : T.Sorted) (hDs : D.Sorted)
    (hBc : B.Contained q) (hTb : T.Boundary q) (hDc : D.Contained q)
    (hTcore : T.AvoidsCore) (hDcore : D.AvoidsCore)
    (hq : q≤qCap) (hDy : D.y≤0) (ht : t∈Ioc 0 frameCap)
    (hBT : quarterFeasible B T v 2) (hTD : zeroFeasible T D (-t) 2) :
    zeroFeasible T D (-t) 0 ∨
      (T.Core ∧ T.a=7/12 ∧ 0<T.y ∧ T.y<83/200 ∧ t<3/10) := by
  rcases hTb with ho | hc
  · exact Or.inl (outer_negative_TD_reselect hBs hTs hDs hBc ho hDc hTcore hDcore hq hDy ht hBT hTD).2
  · exact Or.inr ⟨hc,flat_negative_TD_short hBs hTs hDs hBc hc hDc hDcore hq hDy ht hBT hTD⟩

theorem BT_short_harmonic_mono :
    StrictMonoOn (fun t : ℝ => (3/5)*Real.cos t+(13/12)*Real.sin t) (Icc 0 frameCap) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 frameCap)
  · fun_prop
  · intro t ht
    have hd : HasDerivAt (fun t : ℝ => (3/5)*Real.cos t+(13/12)*Real.sin t)
        ((3/5)*(-Real.sin t)+(13/12)*Real.cos t) t :=
      ((Real.hasDerivAt_cos t).const_mul (3/5 : ℝ)).add
        ((Real.hasDerivAt_sin t).const_mul (13/12 : ℝ))
    rw [hd.deriv]
    obtain ⟨hc,hcu,hs0,hs,hsc⟩ := transport_trig (interior_subset ht)
    linarith

/-- Original sole BT3 at aligned TD0 forces the short true-core branch. -/
theorem negative_BT_aligned_entry {q t : ℝ} {B T D : SignedPoint}
    (hBs : B.Sorted) (hTs : T.Sorted) (hDs : D.Sorted)
    (hBc : B.Contained q) (hTb : T.Boundary q) (hDc : D.Contained q)
    (hDcore : D.AvoidsCore) (hq : q≤qCap) (hBy : B.y≤0) (hDy : D.y≤0)
    (ht : t∈Ioc 0 frameCap)
    (hBT : quarterFeasible B T (-t) 3) (hTD : zeroFeasible T D 0 0)
    (hnot : ¬quarterFeasible B T (-t) 2) :
    T.Core ∧ T.a=7/12 ∧ 1/10<T.y ∧ T.y<39/250 ∧ t<9/100 := by
  have hDu := (SignedPoint.coordinate_bounds hDs hDcore hDc hq).2.2
  rw [abs_of_nonpos hDy] at hDu
  have hTD' : 1≤T.y-D.y := by simpa [zeroFeasible,zeroProjection,edgeWidth,pairWidth] using hTD
  have hy : 1/10<T.y := by linarith
  have hBT' : quarterFeasible T.reflect B.reflect (-t) 1 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect B T (-t) 3).2 hBT
  have hnot' : ¬quarterFeasible T.reflect B.reflect (-t) 0 := by
    intro hf
    exact hnot ((quarterFeasible_reflect B T (-t) 2).1 (by simpa [reflectedOwner] using hf))
  have hsign : T.reflect.y≤0 := by simp [SignedPoint.reflect]; linarith
  have hBsign : 0≤B.reflect.y := by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy
  obtain ⟨hflat,hsmall,hcore,hvec⟩ := negative_primary_flat_entry
    (by simpa using hTs) (by simpa using hBs) (by simpa using hTb)
    (by simpa using hBc) hq hsign hBsign ht hBT' hnot'
  have hcuts := exceptional_negative_primary_cuts
    (by simpa using hTs) (by simpa using hBs) (by simpa using hTb)
    (by simpa using hBc) hq hsign hBsign ht hBT' hnot'
  have hflat' : T.a=7/12 := hflat
  have hcore' : T.Core := by simpa using hcore
  have hyu : T.y<39/250 := by
    simpa [SignedPoint.reflect,abs_neg,abs_of_pos (by linarith : 0<T.y)] using hcuts.2.1
  simp only [SignedPoint.reflect,abs_neg,abs_of_pos (by linarith : 0<T.y),hflat'] at hvec
  have hshort : t<9/100 := by
    by_contra! hbad
    have hm := BT_short_harmonic_mono.monotoneOn
      (by constructor <;> norm_num [frameCap]) ⟨ht.1.le,ht.2⟩ hbad
    have hc0 := cos_lower_six (show (0:ℝ)≤9/100 by norm_num)
    have hs0 := sin_lower_seven (show (0:ℝ)≤9/100 by norm_num)
    have hc := (transport_trig ⟨ht.1.le,ht.2⟩).1
    have hyprod := mul_lt_mul_of_pos_right (show (3/5 : ℝ)<T.y+1/2 by linarith)
      (show 0<Real.cos t by linarith)
    have hqcap : q≤9789/2500 := hq
    norm_num at hc0 hs0
    nlinarith
  exact ⟨hcore',hflat',hy,hyu,hshort⟩

end SquaresInCircles.Eight.TableFree.NegativeTEntry
