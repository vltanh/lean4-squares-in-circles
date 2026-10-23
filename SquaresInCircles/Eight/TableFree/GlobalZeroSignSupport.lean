module

public import SquaresInCircles.Eight.TableFree.GlobalZeroSignScalar

/-!
# The boosted original zero edge with a wrong transverse sign

Uncompiled source.  Both endpoint radial kinds and every selected common
marker chart are retained.  The source coordinate may be zero.  The
reflection uses the exact original index map and keeps the signed error.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalZeroSign
open FramePair ZeroPrimary

theorem state_circle (s : State) : (s.a+1/2)^2+(s.b+1/2)^2≤Q0 := by
  by_cases hc : s.branch.type=0
  · have ha := (FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart s hc)).2.1
    have h1 := pow_le_pow_left₀ (show 0≤s.a+1/2 by linarith [s.a_pos])
      (show s.a+1/2≤13/12 by linarith) 2
    have h2 := pow_le_pow_left₀ (show 0≤s.b+1/2 by linarith [s.b_nonneg])
      (show s.b+1/2≤13/12 by linarith [s.canonical]) 2
    norm_num [Q0] at h1 h2 ⊢
    linarith
  · exact (s.outer_eq hc).le

theorem state_sum (s : State) : s.a+s.b<9/5 := by
  have hc := state_circle s
  have ha := s.a_pos
  have hb := s.b_nonneg
  norm_num [Q0] at hc
  by_contra! hh
  nlinarith [sq_nonneg (s.a-s.b),sq_nonneg (s.a+s.b-9/5)]

theorem state_support (s : State) (f g : ℝ) :
    f*s.a+g*s.b≤CommonQuarter.radius*Real.sqrt (f^2+g^2)-(f+g)/2 := by
  have hc : normSq (s.a+1/2,s.b+1/2)≤CommonQuarter.radius^2 := by
    rw [CommonQuarter.radius_sq]
    exact state_circle s
  have hh := dot_le_radius (v:=(f,g)) (p:=(s.a+1/2,s.b+1/2))
    (show 0≤CommonQuarter.radius from Real.sqrt_nonneg Q0) hc
  dsimp [dot,vectorLength,normSq] at hh
  linarith

theorem marker_lower (s : State) : (4/5)*s.b≤unsigned s := by
  by_cases hc : s.branch.type=0
  · have hh := core_marker_lower s hc
    have ha := (FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart s hc)).2.1
    nlinarith [s.b_nonneg]
  · exact (outer_marker_bounds s hc).1

theorem marker_small_upper (s : State) (hb : s.b<1/2) : unsigned s≤(111/100)*s.b := by
  by_cases hc : s.branch.type=0
  · have ha := (CommonQuarter.core_small_side (FrameCoreArc.state_core_chart s hc) hb).1
    cases hbr : s.branch <;> simp [hbr,Branch.type] at hc
    all_goals dsimp [unsigned]; rw [hbr]; dsimp [FramePair.label]; rw [ha]; nlinarith [s.b_nonneg]
  · have hh := (outer_marker_bounds s hc).2
    have ha := (CommonQuarter.outer_bounds (outer_data s hc)).2.1
    change s.a≤a0 at ha
    linarith

theorem transverse_nonpos_eq (s : State) (hy : sign s.positive*s.b≤0) :
    sign s.positive*s.b= -s.b := by
  cases hp : s.positive <;> simp [hp,FramePair.sign] at hy ⊢
  linarith [s.b_nonneg]

theorem transverse_neg_sign (s : State) (hy : sign s.positive*s.b<0) :
    s.positive=false := by
  cases hp : s.positive
  · rfl
  · simp [hp,FramePair.sign] at hy
    linarith [s.b_nonneg]

theorem small_signed_label (s : State) (hy : sign s.positive*s.b≤0) (hb : s.b<1/2) :
    s.signedLabel= -unsigned s := by
  have hupper := marker_small_upper s hb
  have hlower := marker_nonneg s
  change sign s.positive*unsigned s= -unsigned s
  cases hp : s.positive <;> simp [hp,FramePair.sign] at hy ⊢
  have hzero : s.b=0 := le_antisymm hy s.b_nonneg
  rw [hzero] at hupper
  linarith

theorem sine_cosine_monotone :
    MonotoneOn (fun d : ℝ => Real.sin d+Real.cos d) (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · fun_prop
  · intro d _
    convert (Real.hasDerivAt_sin d).add (Real.hasDerivAt_cos d) using 1 <;> ring
  · intro d hd
    have hh := (transport_trig (Ioo_subset_Icc_self hd)).2.2.2.2
    linarith

/-- A wrong sign on the source of original owner 0 forces one long
positive increment, a negative target, and a source in the small marker
range.  No neighboring owner or frame order is used. -/
theorem source_secondary_domain (s t : State) {d : ℝ} (hd : |d|≤frameCap)
    (hy : sign s.positive*s.b≤0) (hm : s.Feasible t 0 d) :
    d∈Ioc (29/100:ℝ) frameCap ∧ sign t.positive*t.b<0 ∧ s.b<1/2 := by
  have hsc := coordinates s
  have htc := coordinates t
  have hw : 1≤pairWidth d := CommonQuarter.width_ge_one d
  have hm' : pairWidth d≤sign s.positive*s.b+t.a*Real.sin d-
      sign t.positive*t.b*Real.cos d := by simpa [State.Feasible,forwardMargin] using hm
  have hsd : sign s.positive*s.b= -s.b := transverse_nonpos_eq s hy
  have hdpos : 0<d := by
    by_contra! hn
    have hz : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    have ht := transport_trig hz
    have hsine : Real.sin d≤0 := by simpa only [Real.sin_neg,neg_nonneg] using ht.2.2.1
    have hcos : 0≤Real.cos d := by simpa only [Real.cos_neg] using (by linarith [ht.1] : 0≤Real.cos (-d))
    have hsinprod := mul_nonpos_of_nonneg_of_nonpos t.a_pos.le hsine
    have htail : -sign t.positive*t.b*Real.cos d≤t.b := by
      cases hp : t.positive <;> simp [hp,FramePair.sign]
      · nlinarith [mul_nonneg t.b_nonneg (sub_nonneg.mpr (Real.cos_le_one d))]
      · nlinarith [mul_nonneg t.b_nonneg hcos]
    nlinarith [htc.2.2.2.2]
  have hd' : d∈Icc 0 frameCap := ⟨hdpos.le,(le_abs_self d).trans hd⟩
  have ht := transport_trig hd'
  have htarget : sign t.positive*t.b<0 := by
    by_contra! hn
    have htail := mul_nonneg hn (show 0≤Real.cos d by linarith [ht.1])
    have hprod := mul_le_mul htc.2.1.le
      (show Real.sin d≤13/20 by linarith [ht.2.2.2.1]) ht.2.2.1
      (by norm_num : (0:ℝ)≤283/200)
    nlinarith only [hy,hm',hw,htail,hprod]
  have htd : sign t.positive*t.b= -t.b := transverse_nonpos_eq t htarget.le
  rw [hsd,htd] at hm'
  have hwid : pairWidth d=(1+Real.cos d+Real.sin d)/2 := by
    simpa only [edgeWidth] using edgeWidth_positive_formula hd'
  have hphi : 1≤Real.sin d+Real.cos d := by rw [hwid] at hw; linarith
  have hsupport := state_support t (Real.sin d) (Real.cos d)
  rw [Real.sin_sq_add_cos_sq,Real.sqrt_one,mul_one] at hsupport
  have hsmall : s.b<1/2 := by
    rw [hwid] at hm'
    nlinarith [CommonQuarter.radius_bounds.2]
  have horder := mul_nonneg (sub_nonneg.mpr t.canonical)
    (show 0≤Real.cos d-Real.sin d by linarith [ht.2.2.2.2])
  have hsum := mul_lt_mul_of_pos_right (state_sum t)
    (show 0<Real.sin d+Real.cos d by linarith)
  have hlargephi : (5/4:ℝ)<Real.sin d+Real.cos d := by
    rw [hwid] at hm'
    nlinarith [s.b_nonneg]
  have hlarge : (29/100:ℝ)<d := by
    by_contra! hn
    have hmono := sine_cosine_monotone hd'
      (show (29/100:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hn
    have hsine := sin_upper_five (show (0:ℝ)≤29/100 by norm_num)
    have hcos := cos_upper_four (show (0:ℝ)≤29/100 by norm_num)
    norm_num at hsine hcos
    linarith
  exact ⟨⟨hlarge,hd'.2⟩,htarget,hsmall⟩

theorem force_norm (d : ℝ) :
    Real.sqrt (((111/100)*Real.sin d)^2+((111/100)*Real.cos d-4/5)^2)=norm d := by
  unfold norm
  congr 1
  dsimp [K,M]
  nlinarith [Real.sin_sq_add_cos_sq d]

/-- The boosted cost belongs to the unchanged source edge and its
original axis 0.  Weak sign-zero cases are included. -/
theorem source_secondary_boost (s t : State) {d : ℝ} (hd : |d|≤frameCap)
    (hy : sign s.positive*s.b≤0) (hm : s.Feasible t 0 d) :
    1<d+s.signedLabel-t.signedLabel+(9/50)*frameCost |d| := by
  obtain ⟨hd',htneg,hsb⟩ := source_secondary_domain s t hd hy hm
  have hd0 : 0<d := by linarith [hd'.1]
  have hdframe : d∈Icc 0 frameCap := ⟨hd0.le,hd'.2⟩
  have hslabel := small_signed_label s hy hsb
  have htlabel : t.signedLabel= -unsigned t := by
    simp [State.signedLabel,unsigned,transverse_neg_sign t htneg,FramePair.sign]
  have hsupper := marker_small_upper s hsb
  have htlower := marker_lower t
  have hm' : pairWidth d≤ -s.b+t.a*Real.sin d+t.b*Real.cos d := by
    have hh : pairWidth d≤sign s.positive*s.b+t.a*Real.sin d-
        sign t.positive*t.b*Real.cos d := by simpa [State.Feasible,forwardMargin] using hm
    rw [transverse_nonpos_eq s hy,transverse_nonpos_eq t htneg.le] at hh
    linarith
  have hwid : pairWidth d=(1+Real.cos d+Real.sin d)/2 := by
    simpa only [edgeWidth] using edgeWidth_positive_formula hdframe
  rw [hwid] at hm'
  have hsupport := state_support t ((111/100)*Real.sin d) ((111/100)*Real.cos d-4/5)
  rw [force_norm] at hsupport
  have hscalar := scalar_gt_one ⟨hd'.1.le,hd'.2⟩
  rw [hslabel,htlabel,abs_of_pos hd0]
  dsimp [scalar,frameCost] at hscalar ⊢
  nlinarith only [hscalar,hm',hsupper,htlower,hsupport]

theorem target_secondary_boost (s t : State) {d : ℝ} (hd : |d|≤frameCap)
    (hy : 0≤sign t.positive*t.b) (hm : s.Feasible t 2 d) :
    1<d+s.signedLabel-t.signedLabel+(9/50)*frameCost |d| := by
  have hrev := (State.target_secondary_reverse s t d).1 hm
  have hbad : sign t.flip.positive*t.flip.b≤0 := by
    simpa only [State.flip,sign_not,neg_mul] using neg_nonpos.mpr hy
  have hh := source_secondary_boost t.flip s.flip hd hbad hrev
  simpa using hh

end SquaresInCircles.Eight.TableFree.GlobalZeroSign
