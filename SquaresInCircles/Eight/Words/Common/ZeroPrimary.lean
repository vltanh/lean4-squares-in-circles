module

public import SquaresInCircles.Eight.Words.Common.JumpTwo
public import SquaresInCircles.Eight.Words.Common.OneSecondary
public import SquaresInCircles.Eight.Words.Common.ZeroEndpoint

/-!
# Eight squares: every source-primary zero-quarter regime

The physical gap removes the positive-target branch. The remaining
outer/outer branch uses the circle chord and a direct quadratic reserve.
For an outer/core contact, the original separator forces an angle above
`.4`; a fixed circle support and one completed square control the entire
core corner. Both resulting trigonometric supports are concave on the
whole remaining interval.
-/

section
/-!
## The two outer/outer quarter-one primary regimes

Opposite tangent signs use an exact quarter-turn reference support for
negative and short positive deviations, and the actual sine-norm envelope
on the remaining interval. Two negative signs use the original outer arc
endpoint rule and the whole-angle changes already proved at quarter zero.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter

open Arithmetic

/-- The second-order cosine lower bound, in the form the proofs below cite. -/
private theorem r4_cos_lower_two {x : ℝ} (_hx : 0≤x) : 1-x^2/2≤Real.cos x :=
  Real.one_sub_sq_div_two_le_cos

theorem primary_fixed_trig :
    389/1000<Real.sin (2/5:ℝ) ∧ 23/25≤Real.cos (2/5:ℝ) ∧
    479/1000<Real.sin (1/2:ℝ) ∧ 7/8≤Real.cos (1/2:ℝ) ∧
    141/250<Real.sin (3/5:ℝ) ∧ 33/40<Real.cos (3/5:ℝ) ∧
      Real.cos (3/5:ℝ)<413/500 := by
  have hs4 := Real.sin_ge_sub_cube (show (0:ℝ)≤2/5 by norm_num)
  have hc4 := r4_cos_lower_two (show (0:ℝ)≤2/5 by norm_num)
  have hs5 := sin_lower_seven (show (0:ℝ)≤1/2 by norm_num)
  have hc5 := r4_cos_lower_two (show (0:ℝ)≤1/2 by norm_num)
  have hs6 := sin_lower_seven (show (0:ℝ)≤3/5 by norm_num)
  have hc6 := cos_lower_six (show (0:ℝ)≤3/5 by norm_num)
  have hu6 := cos_upper_four (show (0:ℝ)≤3/5 by norm_num)
  norm_num at hs4 hc4 hs5 hc5 hs6 hc6 hu6
  exact ⟨by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith⟩

theorem sine_cosine_mono :
    MonotoneOn (fun x : ℝ => Real.sin x+Real.cos x) (Icc 0 (7/10)) := by
  have hd (x : ℝ) :
      HasDerivAt (fun x : ℝ => Real.sin x+Real.cos x) (Real.cos x-Real.sin x) x := by
    convert (Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x) using 1
  apply monoOn_of_hasDeriv_nonneg (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => hd x)
  intro x hx
  have ht := positive_trig (Ioo_subset_Icc_self hx)
  linarith [ht.1,ht.2.2.2.1]

/-- A single full-circle support controls the actual sloping coordinate. -/
theorem outer_sloping_upper {a b : ℝ} (h : OuterState a b) :
    a+(7/10)*b<783/500 := by
  have hpos : 0≤(a+1/2)+(7/10)*(b+1/2) := by
    have ha : 0≤a := h.1.trans h.2.1
    linarith [h.1]
  have hid : ((a+1/2)+(7/10)*(b+1/2))^2+
      ((7/10)*(a+1/2)-(b+1/2))^2=(149/100)*Q0 := by
    nlinarith [h.2.2]
  have hnorm : (a+1/2)+(7/10)*(b+1/2)<302/125 := by
    have hsq := sq_nonneg ((7/10)*(a+1/2)-(b+1/2))
    norm_num [Q0] at hid
    by_contra! hn
    nlinarith
  linarith

def oneReferenceNorm : ℝ := Real.sqrt ((213/200:ℝ)^2+(203/200)^2)
def oneReferenceSmallNorm : ℝ := Real.sqrt ((13/200:ℝ)^2+(3/200)^2)
def oneReference : ℝ :=
  Real.pi/2+113/50-radius*(oneReferenceNorm+oneReferenceSmallNorm)

lemma one_reference_norms :
    oneReferenceNorm<147121/100000 ∧ oneReferenceSmallNorm<6671/100000 := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤(213/200)^2+(203/200)^2 by norm_num)
  have ht := Real.sq_sqrt (show (0:ℝ)≤(13/200)^2+(3/200)^2 by norm_num)
  have hs0 := Real.sqrt_nonneg ((213/200:ℝ)^2+(203/200)^2)
  have ht0 := Real.sqrt_nonneg ((13/200:ℝ)^2+(3/200)^2)
  dsimp [oneReferenceNorm,oneReferenceSmallNorm]
  constructor <;> nlinarith

theorem one_reference_gt : (787/1000:ℝ)<oneReference := by
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hN : oneReferenceNorm+oneReferenceSmallNorm<(153792/100000:ℝ) := by
    linarith [one_reference_norms.1,one_reference_norms.2]
  have hh := (mul_lt_mul_of_pos_left hN hR).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<153792/100000))
  dsimp [oneReference]
  linarith [pi_hand_enclosure.1]

lemma one_outer_reference_support {a b A B : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) :
    oneReference+(a-B-1)≤Real.pi/2-outerLabel a b-outerLabel A B := by
  have h₁ := outer_circle_lower (X := -(213/200:ℝ)) (Y := -(203/200:ℝ)) hs
  have h₂ := outer_circle_lower (X := -(13/200:ℝ)) (Y := -(3/200:ℝ)) ht
  have he₁ : Real.sqrt ((-(213/200:ℝ))^2+(-(203/200:ℝ))^2)=oneReferenceNorm := by
    norm_num [oneReferenceNorm]
  have he₂ : Real.sqrt ((-(13/200:ℝ))^2+(-(3/200:ℝ))^2)=oneReferenceSmallNorm := by
    norm_num [oneReferenceSmallNorm]
  rw [he₁] at h₁
  rw [he₂] at h₂
  dsimp [oneReference,outerLabel]
  linarith

lemma one_outer_opposite_negative_angle_cut {a b A B z : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hz : z∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2-z)) : z<2/5 := by
  have hx : |-z|≤7/10 := by rw [abs_neg,abs_of_nonneg hz.1]; exact hz.2
  have hm' : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+(-z)) := by
    simpa [sub_eq_add_neg] using hm
  rw [one_primary_margin hx] at hm'
  have tr := positive_trig hz
  have ha := (outer_bounds hs).2.1.trans_lt outer_endpoint_bounds.2.1
  have hA : (899/1000:ℝ)<A := fine_outer_endpoint_bounds.2.trans_le (outer_bounds ht).1
  have hAs := mul_le_mul_of_nonneg_right hA.le tr.2.2.1
  have hBc := mul_nonneg ht.1 (by linarith [tr.1] : 0≤Real.cos z)
  dsimp [oneWidth] at hm'
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1] at hm'
  have hcontact : (1399/1000)*Real.sin z+(1/2)*Real.cos z<183/200 := by
    nlinarith
  by_contra! hlarge
  have hscalar : (183/200:ℝ)<(1399/1000)*Real.sin z+(1/2)*Real.cos z := by
    have h := trig_concave_gt (α := 0) (A := (1399/1000:ℝ)) (B := (1/2:ℝ))
      (m := (183/200:ℝ)) (l := (2/5:ℝ)) (u := (7/10:ℝ)) (by norm_num) (by norm_num)
      (by norm_num) (by linarith [Real.pi_gt_three]) ⟨hlarge,hz.2⟩
      (by linarith [primary_fixed_trig.1,primary_fixed_trig.2.1])
      (by linarith [cap_trig.1,cap_trig.2.2.1])
    linarith
  linarith

lemma one_outer_opposite_negative {a b A B z : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hz : z∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2-z)) :
    (157/200:ℝ)<Real.pi/2-z-outerLabel a b-outerLabel A B := by
  have hcap := one_outer_opposite_negative_angle_cut hs ht hz hm
  have hx : |-z|≤7/10 := by rw [abs_neg,abs_of_nonneg hz.1]; exact hz.2
  have hm' : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+(-z)) := by
    simpa [sub_eq_add_neg] using hm
  rw [one_primary_margin hx] at hm'
  have tr := positive_trig hz
  have hcos := mul_nonneg (show 0≤A-B by linarith [ht.2.1])
    (by linarith [tr.2.1] : 0≤1-Real.cos z)
  have hsum : 0≤Real.sin z+Real.cos z-1 := by linarith [tr.2.2.2.2.2]
  have hA : (4/3:ℝ)≤A+1/2 := by
    linarith [(outer_bounds ht).1,fine_outer_endpoint_bounds.2]
  have hscale := mul_le_mul_of_nonneg_right hA hsum
  have hsine := Real.sin_ge_sub_cube hz.1
  have hcosine := r4_cos_lower_two hz.1
  have hz2 := pow_le_pow_left₀ hz.1 hcap.le 2
  have hz3 := mul_le_mul_of_nonneg_right hz2 hz.1
  have hzz := mul_le_mul_of_nonneg_right hcap.le hz.1
  have hpoly : z≤(4/3)*(z-z^2/2-z^3/6) := by nlinarith
  dsimp [oneWidth] at hm'
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1] at hm'
  have hcut : z≤a-B-1 := by nlinarith
  linarith [one_outer_reference_support hs ht,one_reference_gt]

lemma one_outer_opposite_short_positive {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (1/10))
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x-outerLabel a b-outerLabel A B := by
  have hx' : |x|≤7/10 := by rw [abs_of_nonneg hx.1]; linarith [hx.2]
  have tr := positive_trig ⟨hx.1,by linarith [hx.2]⟩
  have ho := outer_bounds ht
  have hA : A-1/2≤183/200 := by linarith [ho.2.1,outer_endpoint_bounds.2.1]
  have hB : B+1/2≤7/5 := by linarith [ho.2.2.2.1,outer_endpoint_bounds.2.2.2]
  have hsine := mul_le_mul_of_nonneg_right hA tr.2.2.1
  have hcosine := mul_le_mul_of_nonneg_right hB
    (by linarith [tr.2.1] : 0≤1-Real.cos x)
  have hsin := Real.sin_le hx.1
  have hcos := r4_cos_lower_two hx.1
  have hxx := mul_le_mul_of_nonneg_right hx.2 hx.1
  rw [one_primary_margin hx'] at hm
  dsimp [oneWidth] at hm
  rw [abs_of_nonneg tr.2.2.1] at hm
  have hcut : 0≤a-B-1+x := by nlinarith
  linarith [one_outer_reference_support hs ht,one_reference_gt]

lemma one_outer_opposite_long_positive {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc (1/10) (7/10))
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x-outerLabel a b-outerLabel A B := by
  have hx' : |x|≤7/10 := by rw [abs_of_nonneg (by linarith [hx.1] : 0≤x)]; exact hx.2
  have tr := positive_trig ⟨by linarith [hx.1],hx.2⟩
  have hsource := outer_circle_lower (X := -(26/25:ℝ)) (Y := -(203/200:ℝ)) hs
  have htarget := outer_circle_lower (X := -(13/200)-(39/40)*Real.sin x)
    (Y := -(203/200)+(39/40)*Real.cos x) ht
  have he₁ : Real.sqrt ((-(26/25:ℝ))^2+(-(203/200:ℝ))^2)=SineEnvelope.primaryNorm := by
    norm_num [SineEnvelope.primaryNorm]
  have he₂ : Real.sqrt ((-(13/200)-(39/40)*Real.sin x)^2+
      (-(203/200)+(39/40)*Real.cos x)^2)=SineEnvelope.N (39/40) x := by
    dsimp [SineEnvelope.N,CircularNorm.norm]
    rw [SineEnvelope.energy_identity]
    congr 1
    ring
  rw [he₁] at hsource
  rw [he₂] at htarget
  rw [one_primary_margin hx'] at hm
  have hm' := mul_nonneg (show (0:ℝ)≤39/40 by norm_num) hm
  have hen := SineEnvelope.one_outer_primary hx
  dsimp [oneWidth] at hm'
  rw [abs_of_nonneg tr.2.2.1] at hm'
  dsimp [outerLabel,SineEnvelope.base] at *
  nlinarith

theorem one_outer_opposite_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x-outerLabel a b-outerLabel A B := by
  by_cases hp : 0≤x
  · by_cases hshort : x≤1/10
    · exact one_outer_opposite_short_positive hs ht ⟨hp,hshort⟩ hm
    · exact one_outer_opposite_long_positive hs ht
        ⟨by linarith,(abs_le.mp hx).2⟩ hm
  · have hz : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    simpa using one_outer_opposite_negative hs ht hz (by simpa using hm)

lemma one_outer_negative_endpoint_baseline :
    (39463631/50000000:ℝ)<Real.pi/2+39/40+411/400+
      (13/200)*outerAxial-radius*SineEnvelope.primaryNorm := by
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hN := (mul_lt_mul_of_pos_left SineEnvelope.primaryNorm_lt hR).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<145322/100000))
  linarith [fine_outer_endpoint_bounds.1,pi_hand_enclosure.1]

theorem one_outer_negative_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x-outerLabel a b+outerLabel A B := by
  let base : ℝ := Real.pi/2+x+(39/40)*oneWidth x+411/400-radius*SineEnvelope.primaryNorm
  let X : ℝ := (13/200)-(39/40)*Real.sin x
  let Y : ℝ := (203/200)-(39/40)*Real.cos x
  let m : ℝ := min (X*outerAxial) ((X+Y)*outerDiagonal)
  have hsource := outer_circle_lower (X := -(26/25:ℝ)) (Y := -(203/200:ℝ)) hs
  have he : Real.sqrt ((-(26/25:ℝ))^2+(-(203/200:ℝ))^2)=SineEnvelope.primaryNorm := by
    norm_num [SineEnvelope.primaryNorm]
  rw [he] at hsource
  have hY : 0≤Y := by dsimp [Y]; linarith [Real.cos_le_one x]
  have htarget := outer_endpoints_lower (X := X) (Y := Y) (m := m) ht hY
    (min_le_left _ _) (min_le_right _ _)
  have haxial := axial_change_39_nonneg hx
  have hdiagonal := diagonal_change_nonneg (l := (39/40:ℝ)) (by norm_num) hx
  have hdiag0 : (13/200)*outerAxial≤(21/200)*outerDiagonal := by
    linarith [outer_endpoint_bounds.2.1,fine_outer_endpoint_bounds.2]
  have ha : (157/200:ℝ)<base+X*outerAxial := by
    have hh := one_outer_negative_endpoint_baseline
    dsimp [base,X,oneWidth,axialChange] at *
    nlinarith
  have hd : (157/200:ℝ)<base+(X+Y)*outerDiagonal := by
    have hh := one_outer_negative_endpoint_baseline
    dsimp [base,X,Y,oneWidth,diagonalChange] at *
    nlinarith
  have hmin : (157/200:ℝ)<base+m := by
    dsimp [m]
    rw [add_min]
    exact lt_min ha hd
  rw [one_primary_margin hx] at hm
  have hm' := mul_nonneg (show (0:ℝ)≤39/40 by norm_num) hm
  dsimp [base,X,Y,outerLabel] at *
  nlinarith

end SquaresInCircles.Eight.CommonQuarter
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter

open WordProblems

lemma unsigned_angle_bounds {kind : RadialKind} {a b : ℝ} (hs : State kind a b) :
    0≤Real.arctan (b/a) ∧ Real.arctan (b/a)≤Real.pi/4 := by
  have h := state_bounds hs
  have ha : 0<a := by linarith [h.1]
  have hlo := Real.arctan_nonneg.mpr (div_nonneg h.2.2.1 ha.le)
  have hhi := Real.arctan_mono ((div_le_one ha).mpr h.2.2.2.1)
  rw [Real.arctan_one] at hhi
  exact ⟨hlo,hhi⟩

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
  have hAc := mul_le_mul_of_nonneg_right hta.1.le (show (0:ℝ)≤Real.cos φ by linarith)
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
    have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
    have hx2 := pow_le_pow_left₀ hx.1 hxsmall.le 2
    have hAc := mul_le_mul_of_nonneg_right hta.1.le
      (show 0≤Real.cos x by linarith [tr.1])
    have hBs := mul_le_mul_of_nonneg_right hta.2.2.2.2.le tr.2.2.1
    have he : φ= -x := by dsimp [x]; ring
    have hw' := width_ge_one (-x)
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
  have hcoef : 0≤1-Real.cos φ+Real.sin φ := by linarith [tr.2.2.1]
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
  have hc := Real.one_sub_sq_div_two_le_cos (x := φ)
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
  have hc := Real.one_sub_sq_div_two_le_cos (x := φ)
  have hsq := pow_le_pow_left₀ hx.1 hn 2
  norm_num [forwardMargin] at hm
  rw [hwidth] at hm
  nlinarith [hsa.2.1,tr.2.2.2.2.1]

lemma zero_primary_core_scalars {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    (391/400:ℝ)<x-563/250+(13/5)*Real.cos x+(6/5)*Real.sin x ∧
      (391/400:ℝ)<x-167/100+(13/5)*Real.cos x := by
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤2/5 by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (2/5:ℝ))
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
  have hsource : (87/50:ℝ)-zeroPrimaryNorm≤-(493/200)*a-(203/200)*b := by
    have h := outer_circle_lower (X := -(493/200:ℝ)) (Y := -(203/200:ℝ)) hs
    have he : (-(493/200:ℝ))^2+(-(203/200:ℝ))^2=(493/200:ℝ)^2+(203/200)^2 := by norm_num
    rw [he] at h
    dsimp only [zeroPrimaryNorm]
    linarith
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
  · rw [min_eq_left (by linarith : (0:ℝ)≤w/2)] at htarget
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
      have hls : label source a b=outerLabel a b := by simp [label,hso]
      cases σ <;> simp only [cost,hls,sign,Bool.false_eq_true,ite_false,ite_true,
        Rat.cast_neg,Rat.cast_one] <;> linarith
    · have hg' : (19/25:ℝ)<φ+(sign σ:ℝ)*Real.arctan (b/a)-Real.arctan (B/A) := by
        simpa [sign] using hg
      have hm' : 0≤forwardMargin 3 a b A B (sign σ) 1 φ := by simpa [sign] using hm
      exact (zero_primary_positive_target_false hs ht σ hφ hg' hm').elim
  · have hs' : CorePairGeometry.CoreState a b := by simpa [State,hso] using hs
    exact (zero_core_primary_false hs' ht σ τ hφ hm).elim

end SquaresInCircles.Eight.CommonQuarter
end
end
end
