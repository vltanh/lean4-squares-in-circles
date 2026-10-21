module

public import SquaresInCircles.Eight.TableFree.CommonZeroSame

/-!
# Every source-primary zero-quarter regime

The physical gap removes the positive-target branch. The remaining
outer/outer branch uses the circle chord and a direct quadratic reserve.
For an outer/core contact, the original separator forces an angle above
`.4`; a fixed circle support and one completed square control the entire
core corner. Both resulting trigonometric supports are concave on the
whole remaining interval.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter

open WordProblems

lemma unsigned_angle_bounds {kind : RadialKind} {a b : ℝ} (hs : State kind a b) :
    0≤Real.arctan (b/a) ∧ Real.arctan (b/a)≤Real.pi/4 := by
  have h := state_bounds hs
  have ha : 0<a := by linarith [h.1]
  have hlo := Real.arctan_le_arctan (div_nonneg h.2.2.1 ha.le)
  have hhi := Real.arctan_le_arctan ((div_le_one ha).mpr h.2.2.2.1)
  exact ⟨by simpa using hlo,by simpa using hhi⟩

lemma signed_angle_bounds {kind : RadialKind} {a b : ℝ} (hs : State kind a b) (σ : Bool) :
    -Real.pi/4≤(sign σ:ℝ)*Real.arctan (b/a) ∧
      (sign σ:ℝ)*Real.arctan (b/a)≤Real.pi/4 := by
  have h := unsigned_angle_bounds hs
  cases σ <;> norm_num [sign] <;> constructor <;> linarith [Real.pi_pos]

lemma zero_negative_positive_false {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B) (hφ : |φ|≤7/10)
    (hg : (19/25:ℝ)<φ-Real.arctan (b/a)-Real.arctan (B/A)) : False := by
  linarith [(unsigned_angle_bounds hs).1,(unsigned_angle_bounds ht).1,(abs_le.mp hφ).2]

lemma zero_core_primary_false {target : RadialKind} {a b A B φ : ℝ}
    (hs : CorePairGeometry.CoreState a b) (ht : State target A B) (σ τ : Bool)
    (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (sign σ) (sign τ) φ) : False := by
  have hsa := CoreAngleEndpoint.state_bounds hs
  have hta := state_bounds ht
  have hc := signed_cos hφ
  have hsine := signed_sin hφ
  have hcos : (3/4:ℝ)<Real.cos φ := by linarith [hc.1]
  have hAc := mul_le_mul_of_nonneg_right hta.1.le hcos.le
  have hBc := mul_le_mul_of_nonneg_left (le_abs_self (Real.sin φ)) hta.2.2.1
  have hBn := mul_le_mul_of_nonneg_left (neg_le_abs (Real.sin φ)) hta.2.2.1
  have hBabs := mul_le_mul_of_nonneg_left hsine.le hta.2.2.1
  have hBbound := mul_le_mul_of_nonneg_right hta.2.2.2.2.le
    (show (0:ℝ)≤16106/25000 by norm_num)
  have hw := width_ge_one φ
  cases τ <;> norm_num [forwardMargin,sign] at hm <;> nlinarith [hsa.2.1]

lemma zero_primary_negative_angle {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B) (σ : Bool)
    (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (sign σ) (-1) φ) : 0<φ := by
  have hsa := state_bounds hs
  have hta := state_bounds ht
  have hc := signed_cos hφ
  have hAc := mul_le_mul_of_nonneg_right hta.1.le (show 0≤Real.cos φ by linarith [hc.1])
  have hw := width_ge_one φ
  by_contra! hn
  have hsin : Real.sin φ≤0 := by
    have hp := positive_trig (x := -φ)
      ⟨by linarith,by linarith [(abs_le.mp hφ).1]⟩
    simpa only [Real.sin_neg,neg_nonneg] using hp.2.2.1
  have hBs := mul_nonpos_of_nonneg_of_nonpos hta.2.2.1 hsin
  norm_num [forwardMargin] at hm
  nlinarith [hsa.2.1,hc.1]

lemma zero_primary_positive_target_false {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B) (σ : Bool)
    (hφ : |φ|≤7/10)
    (hg : (19/25:ℝ)<φ+(sign σ:ℝ)*Real.arctan (b/a)-Real.arctan (B/A))
    (hm : 0≤forwardMargin 3 a b A B (sign σ) 1 φ) : False := by
  have hsa := state_bounds hs
  have hta := state_bounds ht
  have hangle := (signed_angle_bounds hs σ).2
  have hangleT := (unsigned_angle_bounds ht).1
  have hφlo : -(1/30:ℝ)<φ := by linarith [pi_lt_22_over_7]
  have hw := width_ge_one φ
  by_cases hp : 0≤φ
  · have tr := positive_trig ⟨hp,(abs_le.mp hφ).2⟩
    have hAc := mul_le_mul_of_nonneg_right hta.1.le
      (show 0≤Real.cos φ by linarith [tr.1])
    have hBs := mul_nonneg hta.2.2.1 tr.2.2.1
    norm_num [forwardMargin] at hm
    nlinarith [hsa.2.1,tr.1]
  · let x : ℝ := -φ
    have hx : x∈Icc 0 (7/10) := ⟨by dsimp [x]; linarith,
      by dsimp [x]; linarith [(abs_le.mp hφ).1]⟩
    have hxsmall : x<1/30 := by dsimp [x]; linarith
    have tr := positive_trig hx
    have hcos := cos_lower_two hx.1
    have hx2 := pow_le_pow_left₀ hx.1 hxsmall.le 2
    have hAc := mul_le_mul_of_nonneg_right hta.1.le
      (show 0≤Real.cos x by linarith [tr.1])
    have hBs := mul_le_mul_of_nonneg_right hta.2.2.2.2.le tr.2.2.1
    have he : φ= -x := by dsimp [x]; ring
    norm_num [forwardMargin,he,Real.cos_neg,Real.sin_neg] at hm
    nlinarith [hsa.2.1,tr.2.2.2.2.1]

/-- Along the canonical outer arc the primary loss is no larger than the
transverse gain. This is the exact two-circle chord identity. -/
lemma outer_primary_loss {a b A B : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hb : b≤B) : a-A≤B-b := by
  have hs0 : 0≤a := hs.1.trans hs.2.1
  have ht0 : 0≤A := ht.1.trans ht.2.1
  have hid : (a-A)*(a+A+1)=(B-b)*(B+b+1) := by nlinarith [hs.2.2,ht.2.2]
  have hden : 0<a+A+1 := by linarith
  have hm := mul_le_mul_of_nonneg_left
    (show B+b+1≤a+A+1 by linarith [hs.2.1,ht.2.1]) (sub_nonneg.mpr hb)
  apply (mul_le_mul_iff_of_pos_right hden).mp
  nlinarith

lemma zero_primary_outer_outer {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) (-1) φ) :
    (391/400:ℝ)<φ-outerLabel a b+outerLabel A B := by
  have hs' : State .outer a b := by simpa [State] using hs
  have ht' : State .outer A B := by simpa [State] using ht
  have hp := zero_primary_negative_angle hs' ht' false hφ (by simpa [sign] using hm)
  have hx : φ∈Icc 0 (7/10) := ⟨hp.le,(abs_le.mp hφ).2⟩
  have tr := positive_trig hx
  have hX : 0≤1-Real.cos φ := by linarith [tr.2.1]
  have hXY : 1-Real.cos φ≤Real.sin φ := by linarith [tr.2.2.2.2.2]
  have hsupport := outer_diagonal_upper (X := 1-Real.cos φ) (Y := Real.sin φ) ht hX hXY
  have hcoef : 0≤1-Real.cos φ+Real.sin φ := by positivity
  have hdiag := mul_le_mul_of_nonneg_right outer_endpoint_bounds.2.2.2.le hcoef
  have hwidth : pairWidth φ=(1+Real.cos φ+Real.sin φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
  have hpositive : outerDiagonal*(1-Real.cos φ+Real.sin φ)<pairWidth φ := by
    rw [hwidth]
    nlinarith [tr.1,tr.2.2.2.1]
  have horder : b<B := by
    by_contra! hn
    have hA : a≤A := by
      have hsq := pow_le_pow_left₀ (show 0≤B+1/2 by linarith [ht.1])
        (show B+1/2≤b+1/2 by linarith) 2
      by_contra! hbad
      have hp' := mul_pos (sub_pos.mpr hbad)
        (show 0<a+A+1 by linarith [hs.1,hs.2.1,ht.1,ht.2.1])
      nlinarith [hs.2.2,ht.2.2]
    norm_num [forwardMargin] at hm
    nlinarith
  have hchord := outer_primary_loss hs ht horder.le
  have hse := (outer_label_error hs).2
  have hte := (outer_label_error ht).1
  have hc := cos_lower_two hx.1
  have hsq := mul_le_mul_of_nonneg_right hx.2 hx.1
  norm_num [forwardMargin] at hm
  rw [hwidth] at hm
  nlinarith [tr.2.2.2.2.1]

/-- A completed square bounds the small negative transverse coefficient
on the entire core corner; the side obeys the same estimate. -/
lemma core_small_transverse_support {A B v w : ℝ}
    (ht : CorePairGeometry.CoreState A B) (hv : (49/10:ℝ)≤v) (hw : -(2/5:ℝ)≤w) :
    min 0 (w/2)-1/500≤v*(7/12-A)+w*B := by
  have hco := CoreAngleEndpoint.state_bounds ht
  have hu : 0≤7/12-A := by linarith [hco.2.1]
  have hv0 : 0≤v := by linarith
  by_cases hp : 0≤w
  · rw [min_eq_left (by positivity : (0:ℝ)≤w/2)]
    have h₁ := mul_nonneg hv0 hu
    have h₂ := mul_nonneg hp hco.2.2.1
    linarith
  · rw [min_eq_right (by linarith : w/2≤0)]
    rcases ht with ⟨rfl,hB,hBu⟩ | ⟨hB,hBA,hcircle⟩
    · have hm := mul_le_mul_of_nonpos_left hBu (le_of_not_ge hp)
      nlinarith
    · have hd : 0≤B-1/2 := by linarith
      have hc := (CorePairGeometry.corner_geometry hB hBA hcircle).2.2.2
      have h₁ := mul_le_mul_of_nonneg_right hv hu
      have h₂ := mul_le_mul_of_nonneg_right hw hd
      have hs := sq_nonneg (147*(B-1/2)-1)
      nlinarith

def zeroPrimaryNorm : ℝ := radius*Real.sqrt ((493/200:ℝ)^2+(203/200)^2)

lemma zeroPrimaryNorm_lt : zeroPrimaryNorm<132/25 := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤(493/200)^2+(203/200)^2 by norm_num)
  have hsq : zeroPrimaryNorm^2=Q0*((493/200:ℝ)^2+(203/200)^2) := by
    rw [zeroPrimaryNorm,mul_pow,radius_sq,hs]
  have hnon : 0≤zeroPrimaryNorm := by
    dsimp [zeroPrimaryNorm]
    exact mul_nonneg (by linarith [radius_bounds.1]) (Real.sqrt_nonneg _)
  norm_num [Q0] at hsq
  nlinarith

lemma zero_primary_outer_core_angle {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 3 a b A B (-1) (-1) φ) :
    (2/5:ℝ)<φ := by
  have hs' : State .outer a b := by simpa [State] using hs
  have ht' : State .coreSide A B := by simpa [State] using ht
  have hp := zero_primary_negative_angle hs' ht' false hφ (by simpa [sign] using hm)
  have hsa := state_bounds hs'
  have hta := state_bounds ht'
  have hco := CoreAngleEndpoint.state_bounds ht
  have hB : B<14/25 := by linarith [hco.2.2.2.2,CoreAngleEndpoint.diagonal_bounds.2]
  have hx : φ∈Icc 0 (7/10) := ⟨hp.le,(abs_le.mp hφ).2⟩
  have tr := positive_trig hx
  have hAc := mul_le_mul_of_nonneg_right hta.1.le
    (show 0≤Real.cos φ by linarith [tr.1])
  have hBs := mul_le_mul_of_nonneg_right hB.le tr.2.2.1
  have hwidth : pairWidth φ=(1+Real.cos φ+Real.sin φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
  by_contra! hn
  have hc := cos_lower_two hx.1
  have hsq := pow_le_pow_left₀ hx.1 hn 2
  norm_num [forwardMargin] at hm
  rw [hwidth] at hm
  nlinarith [hsa.2.1,tr.2.2.2.2.1]

lemma zero_primary_core_scalars {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    (391/400:ℝ)<x-563/250+(13/5)*Real.cos x+(6/5)*Real.sin x ∧
      (391/400:ℝ)<x-167/100+(13/5)*Real.cos x := by
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤2/5 by norm_num)
  have hc := cos_lower_two (show (0:ℝ)≤2/5 by norm_num)
  norm_num at hs hc
  constructor
  · have h := trig_concave_gt (α := (1:ℝ)) (A := (6/5:ℝ)) (B := (13/5:ℝ))
      (m := (391/400:ℝ)+563/250) (by norm_num) (by norm_num) (by norm_num)
      (by linarith [Real.pi_gt_three]) hx
      (by linarith) (by linarith [cap_trig.1,cap_trig.2.2.1])
    linarith
  · have h := trig_concave_gt (α := (1:ℝ)) (A := (0:ℝ)) (B := (13/5:ℝ))
      (m := (391/400:ℝ)+167/100) (by norm_num) (by norm_num) (by norm_num)
      (by linarith [Real.pi_gt_three]) hx
      (by linarith) (by linarith [cap_trig.2.2.1])
    linarith

lemma zero_primary_outer_core {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 3 a b A B (-1) (-1) φ) :
    (391/400:ℝ)<φ-outerLabel a b+coreLabel A B := by
  have hp := zero_primary_outer_core_angle hs ht hφ hm
  have hx : φ∈Icc (2/5) (7/10) := ⟨hp.le,(abs_le.mp hφ).2⟩
  have tr := positive_trig (show φ∈Icc 0 (7/10) from ⟨by linarith,hx.2⟩)
  have hsource := outer_circle_lower (X := -(493/200:ℝ)) (Y := -(203/200:ℝ)) hs
  norm_num at hsource
  change (87/50:ℝ)-zeroPrimaryNorm≤-(493/200)*a-(203/200)*b at hsource
  let v : ℝ := 73/10-(12/5)*Real.cos φ
  let w : ℝ := 291/250-(12/5)*Real.sin φ
  have hv : (49/10:ℝ)≤v := by dsimp [v]; linarith [tr.2.1]
  have hw : -(2/5:ℝ)≤w := by dsimp [w]; linarith [tr.2.2.2.1]
  have htarget := core_small_transverse_support ht hv hw
  have hmul := mul_nonneg (show (0:ℝ)≤12/5 by norm_num) hm
  have hwidth : pairWidth φ=(1+Real.cos φ+Real.sin φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
  norm_num [forwardMargin] at hmul
  rw [hwidth] at hmul
  have hg := zero_primary_core_scalars hx
  by_cases hwpos : 0≤w
  · rw [min_eq_left (by positivity : (0:ℝ)≤w/2)] at htarget
    dsimp [v,w] at htarget
    dsimp [outerLabel,coreLabel]
    nlinarith [zeroPrimaryNorm_lt,hg.1]
  · rw [min_eq_right (by linarith : w/2≤0)] at htarget
    dsimp [v,w] at htarget
    dsimp [outerLabel,coreLabel]
    nlinarith [zeroPrimaryNorm_lt,hg.2]

/-- Every original source-primary zero-quarter contact, including signed
zero coordinates. The positive-target elimination uses the physical gap. -/
theorem zero_primary_cost {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B) (σ τ : Bool)
    (hφ : |φ|≤7/10)
    (hg : (19/25:ℝ)<φ+(sign σ:ℝ)*Real.arctan (b/a)-(sign τ:ℝ)*Real.arctan (B/A))
    (hm : 0≤forwardMargin 3 a b A B (sign σ) (sign τ) φ) :
    (391/400:ℝ)<cost source target σ τ a b A B φ := by
  by_cases hso : source=.outer
  · have hs' : OuterState a b := by simpa [State,hso] using hs
    cases τ
    · have hm' : 0≤forwardMargin 3 a b A B (-1) (-1) φ := by
        simpa [forwardMargin,sign] using hm
      have hlow : (391/400:ℝ)<φ-outerLabel a b+label target A B := by
        by_cases hto : target=.outer
        · have ht' : OuterState A B := by simpa [State,hto] using ht
          simpa [label,hto] using zero_primary_outer_outer hs' ht' hφ hm'
        · have ht' : CorePairGeometry.CoreState A B := by simpa [State,hto] using ht
          simpa [label,hto] using zero_primary_outer_core hs' ht' hφ hm'
      have hL := (outer_label_bounds hs').1
      cases σ <;> norm_num [cost,sign,label,hso] <;> linarith
    · have hg' : (19/25:ℝ)<φ+(sign σ:ℝ)*Real.arctan (b/a)-Real.arctan (B/A) := by
        simpa [sign] using hg
      have hm' : 0≤forwardMargin 3 a b A B (sign σ) 1 φ := by simpa [sign] using hm
      exact (zero_primary_positive_target_false hs ht σ hφ hg' hm').elim
  · have hs' : CorePairGeometry.CoreState a b := by simpa [State,hso] using hs
    exact (zero_core_primary_false hs' ht σ τ hφ hm).elim

end SquaresInCircles.Eight.CommonQuarter
