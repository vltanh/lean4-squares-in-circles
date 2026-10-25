module

public import SquaresInCircles.Eight.TableFree.CommonOneCorePrimary
public import SquaresInCircles.Eight.TableFree.CommonZeroEndpoint

/-!
# The two outer/outer quarter-one primary regimes

Opposite tangent signs use an exact quarter-turn reference support for
negative and short positive deviations, and the actual sine-norm envelope
on the remaining interval. Two negative signs use the original outer arc
endpoint rule and the whole-angle changes already proved at quarter zero.
Uncompiled source draft.
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
