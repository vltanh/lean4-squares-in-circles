module

public import SquaresInCircles.Eight.Words.Common.ZeroPrimary
public import SquaresInCircles.Eight.Words.Common.OneSecondary

/-!
# Eight squares: the common-label bound for one quarter increment

An edge with quarter increment one has cost above `157/200` for each of its four owners
(`one_cost`). The two source owners are proved on every signed core or outer state
(`one_primary_cost`, `one_secondary_cost`); exact reflection and reversal move the two target
owners to those formulas without changing their cost. `actual_one` applies this to a weak
physical owner of an edge of the boundary cycle, with its integer frame lift.
-/

section
/-!
## Quarter-one primary contacts with an original core source

The primary owner does not involve the source tangent sign, so the
negative source label is the worst case. Positive targets are either
impossible or have a small transverse coordinate forced by the same
contact. Negative targets admit one concave support on the complete
negative angle interval, with a direct estimate on the positive interval.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter

open WordProblems Arithmetic

/-- Both actual boundary labels lie above the transverse coordinate minus
the same small outer error. -/
theorem state_label_lower {kind : RadialKind} {a b : ℝ} (h : State kind a b) :
    b-19/1000<label kind a b := by
  by_cases hk : kind=.outer
  · have hh : OuterState a b := by simpa [State,hk] using h
    simp only [label,ite_eq_left hk]
    linarith [(outer_label_error hh).1]
  · have hh : CorePairGeometry.CoreState a b := by simpa [State,hk] using h
    simp only [label,ite_eq_right hk]
    linarith [core_label_lower hh,(CoreAngleEndpoint.state_bounds hh).2.2.1]

lemma one_core_positive_primary_angle {target : RadialKind} {a b A B x : ℝ}
    (hs : CorePairGeometry.CoreState a b) (ht : State target A B)
    (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) : 0<x := by
  have hsa := CoreAngleEndpoint.state_bounds hs
  have hta := state_bounds ht
  have hc : 0≤Real.cos x := by linarith [(signed_cos hx).1]
  have hB := mul_nonneg hta.2.2.1 hc
  have hw := oneWidth_ge_one hx
  by_contra! hbad
  have hsin : Real.sin x≤0 := by
    have hh := positive_trig (x := -x) ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    simpa only [Real.sin_neg,neg_nonneg] using hh.2.2.1
  have hA := mul_nonpos_of_nonneg_of_nonpos (by linarith [hta.1] : 0≤A) hsin
  rw [one_primary_margin hx] at hm
  nlinarith [hsa.2.1]

lemma one_core_core_positive_primary_false {a b A B x : ℝ}
    (hs : CorePairGeometry.CoreState a b) (ht : CorePairGeometry.CoreState A B)
    (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) : False := by
  have ht' : State .coreSide A B := by simpa [State] using ht
  have hp := one_core_positive_primary_angle hs ht' hx hm
  have tr := positive_trig ⟨hp.le,(abs_le.mp hx).2⟩
  have hsa := CoreAngleEndpoint.state_bounds hs
  have hta := CoreAngleEndpoint.state_bounds ht
  have hAs := mul_le_mul_of_nonneg_right hta.2.1 tr.2.2.1
  have hB := mul_nonneg hta.2.2.1 (by linarith [tr.1] : 0≤Real.cos x)
  have hw := oneWidth_ge_one hx
  rw [one_primary_margin hx] at hm
  nlinarith [tr.2.2.2.1,hsa.2.1]

/-- The original core-to-outer primary contact itself gives the transverse
cut; its full allowed angle range then has a uniform reserve. -/
lemma one_core_outer_positive_primary {a b A B x : ℝ}
    (hs : CorePairGeometry.CoreState a b) (ht : OuterState A B)
    (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x-coreLabel a b-outerLabel A B := by
  have ht' : State .outer A B := by simpa [State] using ht
  have hp := one_core_positive_primary_angle hs ht' hx hm
  have hxi : x∈Icc 0 (7/10) := ⟨hp.le,(abs_le.mp hx).2⟩
  have tr := positive_trig hxi
  have ha := (CoreAngleEndpoint.state_bounds hs).2.1
  have hA := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  have hA0 : 0≤A-1/2 := by linarith [(state_bounds ht').1]
  have hAs := mul_le_mul_of_nonneg_left tr.2.2.2.2.1 hA0
  have hAcut := mul_le_mul_of_nonneg_right (show A-1/2≤183/200 by linarith) hp.le
  have hBc := mul_lt_mul_of_pos_right
    (show (3/4:ℝ)<Real.cos x by linarith [tr.1])
    (show 0<B+1/2 by linarith [ht.1])
  rw [one_primary_margin hx] at hm
  dsimp [oneWidth] at hm
  rw [abs_of_nonneg tr.2.2.1] at hm
  have hB : B<(61/50)*x-7/18 := by nlinarith
  have hsL := (core_label_bounds hs).2
  have htL := (outer_label_error ht).2
  nlinarith [pi_hand_enclosure.1,hxi.2]

lemma one_core_positive_primary {target : RadialKind} {a b A B x : ℝ}
    (hs : CorePairGeometry.CoreState a b) (ht : State target A B)
    (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x-coreLabel a b-label target A B := by
  by_cases hk : target=.outer
  · have ht' : OuterState A B := by simpa [State,hk] using ht
    simpa [label,hk] using one_core_outer_positive_primary hs ht' hx hm
  · have ht' : CorePairGeometry.CoreState A B := by simpa [State,hk] using ht
    exact (one_core_core_positive_primary_false hs ht' hx hm).elim

lemma one_core_negative_primary_negative_angle {target : RadialKind} {a b A B z : ℝ}
    (hs : CorePairGeometry.CoreState a b) (ht : State target A B)
    (hz : z∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 3 a b A B (-1) (-1) (Real.pi/2-z)) :
    (157/200:ℝ)<Real.pi/2-z-coreLabel a b+label target A B := by
  have hx : |-z|≤7/10 := by rw [abs_neg,abs_of_nonneg hz.1]; exact hz.2
  have hm' : 0≤forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+(-z)) := by
    simpa [sub_eq_add_neg] using hm
  rw [one_primary_margin hx] at hm'
  have tr := positive_trig hz
  have hsa := CoreAngleEndpoint.state_bounds hs
  have hta := state_bounds ht
  have hBc := mul_le_mul_of_nonneg_left tr.2.1 hta.2.2.1
  have hAs := mul_le_mul_of_nonneg_right hta.1.le tr.2.2.1
  dsimp [oneWidth] at hm'
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1] at hm'
  have hB : -(1/12)+(1/2)*Real.cos z+(21/20)*Real.sin z≤B := by
    nlinarith [hsa.2.1]
  have hscalar : (1/4:ℝ)< -z+(21/20)*Real.sin z+(1/2)*Real.cos z := by
    have h := trig_concave_gt (α := (-1:ℝ)) (A := (21/20:ℝ)) (B := (1/2:ℝ)) (m := (1/4:ℝ))
      (l := 0) (u := (7/10:ℝ)) (by norm_num) (by norm_num) (by norm_num)
      (by linarith [Real.pi_gt_three]) hz (by norm_num)
      (by linarith [cap_trig.1,cap_trig.2.2.1])
    linarith
  have hsL := (core_label_bounds hs).2
  have htL := state_label_lower ht
  nlinarith [pi_hand_enclosure.1]

lemma one_core_negative_primary {target : RadialKind} {a b A B x : ℝ}
    (hs : CorePairGeometry.CoreState a b) (ht : State target A B)
    (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x-coreLabel a b+label target A B := by
  by_cases hp : 0≤x
  · have hsL := (core_label_bounds hs).2
    by_cases hlarge : (1/10:ℝ)≤x
    · linarith [(state_label_bounds ht).1,pi_hand_enclosure.1]
    · have hxi : x∈Icc 0 (7/10) := ⟨hp,(abs_le.mp hx).2⟩
      have tr := positive_trig hxi
      have hsa := CoreAngleEndpoint.state_bounds hs
      have hta := state_bounds ht
      have hAs := mul_le_mul_of_nonneg_right hta.2.1.le tr.2.2.1
      have hsin := mul_le_mul_of_nonneg_left tr.2.2.2.2.1
        (show (0:ℝ)≤283/200 by norm_num)
      have hBc := mul_le_mul_of_nonneg_left tr.2.1 hta.2.2.1
      have hw := oneWidth_ge_one hx
      rw [one_primary_margin hx] at hm
      have hB : (11/40:ℝ)<B := by nlinarith [hsa.2.1]
      linarith [state_label_lower ht,pi_hand_enclosure.1]
  · have hz : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    have hh := one_core_negative_primary_negative_angle hs ht hz
      (by simpa using hm)
    simpa using hh

/-- Source-primary contacts with any original core source and either
source sign. The source sign only improves the negative-label bound. -/
theorem one_core_primary_cost {source target : RadialKind} {a b A B x : ℝ}
    (hsource : source≠.outer) (hs : CorePairGeometry.CoreState a b)
    (ht : State target A B) (σ τ : Bool) (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (sign σ) (sign τ) (Real.pi/2+x)) :
    (157/200:ℝ)<cost source target σ τ a b A B (Real.pi/2+x) := by
  have hsL := (core_label_bounds hs).1
  have hslabel : label source a b=coreLabel a b := by simp [label,hsource]
  cases τ
  · have hm' : 0≤forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+x) := by
      simpa [forwardMargin,sign] using hm
    have hh := one_core_negative_primary hs ht hx hm'
    cases σ <;> norm_num [cost,sign,hslabel] <;> linarith
  · have hm' : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x) := by
      simpa [forwardMargin,sign] using hm
    have hh := one_core_positive_primary hs ht hx hm'
    cases σ <;> norm_num [cost,sign,hslabel] <;> linarith

end SquaresInCircles.Eight.CommonQuarter
end
end
end

section
/-!
## The remaining outer-to-core primary contacts at one quarter

The original weak primary contact forces the angle and transverse cuts
needed at the tight side endpoint. The corner is controlled by a whole
quadratic consequence of a sloping circle support. Both negative tangents
use the exact aligned baseline and a single concave trigonometric change.
All cuts are derived from the original coordinates and owner inequality.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter

open Arithmetic

/-- The second-order cosine lower bound, in the form the proofs below cite. -/
private theorem r4_cos_lower_two {x : ℝ} (_hx : 0≤x) : 1-x^2/2≤Real.cos x :=
  Real.one_sub_sq_div_two_le_cos

def corePrimaryChange (x : ℝ) : ℝ :=
  x+(291/250)*(oneWidth x-1)-(679/1000)*Real.sin x

def coreNegativeChange (z : ℝ) : ℝ :=
  -z+(291/500)*(Real.cos z-1)+(1261/1000)*Real.sin z

lemma core_primary_lower {A B : ℝ} (h : CorePairGeometry.CoreState A B) :
    (279/500:ℝ)<A := by
  have hh := core_diagonal_lower (X := (1:ℝ)) (Y := (0:ℝ)) h (by norm_num) (by norm_num)
  norm_num at hh
  linarith [CoreAngleEndpoint.diagonal_bounds.1]

lemma one_core_source_support {a b : ℝ} (hs : OuterState a b) :
    303/250-radius*OneEnvelope.N (291/250) 0≤ -outerLabel a b-(291/250)*a := by
  have hh := outer_circle_lower (X := -(1229/1000:ℝ)) (Y := -(203/200:ℝ)) hs
  have he : Real.sqrt ((-(1229/1000:ℝ))^2+(-(203/200:ℝ))^2)=
      OneEnvelope.N (291/250) 0 := by
    dsimp [OneEnvelope.N,CircularNorm.norm]
    rw [OneEnvelope.energy_identity]
    norm_num
  rw [he] at hh
  dsimp [outerLabel]
  linarith

lemma core_primary_change_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0≤corePrimaryChange x := by
  have tr := positive_trig hx
  have hs := Real.sin_le hx.1
  have hc := r4_cos_lower_two hx.1
  have hxx := mul_le_mul_of_nonneg_right hx.2 hx.1
  dsimp [corePrimaryChange,oneWidth]
  rw [abs_of_nonneg tr.2.2.1]
  nlinarith

lemma core_primary_change_negative {z : ℝ} (hz : z∈Icc 0 (7/10)) :
    corePrimaryChange (-z)=coreNegativeChange z := by
  have ht := positive_trig hz
  dsimp [corePrimaryChange,coreNegativeChange,oneWidth]
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg ht.2.2.1]
  ring

lemma core_negative_change_nonneg {z : ℝ} (hz : z∈Icc 0 (3/5)) :
    0≤coreNegativeChange z := by
  have hs := Real.sin_ge_sub_cube hz.1
  have hc := r4_cos_lower_two hz.1
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hz3 := mul_le_mul_of_nonneg_right hz2 hz.1
  have hzz := mul_le_mul_of_nonneg_right hz.2 hz.1
  dsimp [coreNegativeChange]
  nlinarith

lemma core_negative_change_lower {z : ℝ} (hz : z∈Icc (3/5) (7/10)) :
    -(1/40:ℝ)<coreNegativeChange z := by
  have hh := trig_concave_gt (α := (-1:ℝ)) (A := (1261/1000:ℝ))
    (B := (291/500:ℝ)) (m := (291/500)-(1/40)) (l := (3/5:ℝ)) (u := (7/10:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three]) hz
    (by linarith [primary_fixed_trig.2.2.2.2.1,primary_fixed_trig.2.2.2.2.2.1])
    (by linarith [cap_trig.1,cap_trig.2.2.1])
  dsimp [coreNegativeChange]
  linarith

/-- The actual large negative angle forces positive target transverse
reserve; it is not supplied as an additional leaf hypothesis. -/
lemma one_mixed_negative_large_cut {a b A B z : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B)
    (hz : z∈Icc (3/5) (7/10))
    (hm : 0≤forwardMargin 3 a b A B (-1) (-1) (Real.pi/2-z)) :
    (11/100:ℝ)<B ∧ (87/500:ℝ)<1-Real.cos z := by
  have hz' : z∈Icc 0 (7/10) := ⟨by linarith [hz.1],hz.2⟩
  have hx : |-z|≤7/10 := by rw [abs_neg,abs_of_nonneg hz'.1]; exact hz.2
  have tr := positive_trig hz'
  have hsm := sin_mono (show (3/5:ℝ)∈Icc 0 (7/10) by norm_num) hz' hz.1
  have hcm := cos_anti (show (3/5:ℝ)∈Icc 0 (7/10) by norm_num) hz' hz.1
  have hwm := sine_cosine_mono (show (3/5:ℝ)∈Icc 0 (7/10) by norm_num) hz' hz.1
  have hsin : (141/250:ℝ)<Real.sin z := by
    linarith [primary_fixed_trig.2.2.2.2.1]
  have hcos : Real.cos z<(413/500:ℝ) := by
    linarith [primary_fixed_trig.2.2.2.2.2.2]
  have hwidth : (2389/2000:ℝ)<(1+Real.cos z+Real.sin z)/2 := by
    linarith [primary_fixed_trig.2.2.2.2.1,primary_fixed_trig.2.2.2.2.2.1]
  have hA := core_primary_lower ht
  have hAs := mul_le_mul_of_nonneg_right hA.le tr.2.2.1
  have ha := (outer_bounds hs).2.1.trans_lt outer_endpoint_bounds.2.1
  have hm' : 0≤forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+(-z)) := by
    simpa [sub_eq_add_neg] using hm
  rw [one_primary_margin hx] at hm'
  dsimp [oneWidth] at hm'
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1] at hm'
  have hBc := mul_le_mul_of_nonneg_left hcos.le (CoreAngleEndpoint.state_bounds ht).2.2.1
  constructor <;> nlinarith

lemma one_mixed_negative_lower {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B) (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+x)) :
    OneEnvelope.envelope .core 0+corePrimaryChange x+
      (291/250)*B*(1-Real.cos x)≤Real.pi/2+x-outerLabel a b+coreLabel A B := by
  have hsource := one_core_source_support hs
  have hA := (CoreAngleEndpoint.state_bounds ht).2.1
  have hsin := signed_sin hx
  have hcoef : 0≤(73/10)+(291/250)*Real.sin x := by
    have hh := neg_le_abs (Real.sin x)
    linarith
  have htarget := mul_nonneg hcoef (show 0≤7/12-A by linarith)
  rw [one_primary_margin hx] at hm
  have hm' := mul_nonneg (show (0:ℝ)≤291/250 by norm_num) hm
  dsimp [OneEnvelope.envelope,OneEnvelope.weight,OneEnvelope.offset,corePrimaryChange,coreLabel]
  norm_num
  nlinarith

theorem one_outer_core_negative_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B) (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x-outerLabel a b+coreLabel A B := by
  have hlow := one_mixed_negative_lower hs ht hx hm
  have hb := (CoreAngleEndpoint.state_bounds ht).2.2.1
  have hextra := mul_nonneg hb (sub_nonneg.mpr (Real.cos_le_one x))
  by_cases hp : 0≤x
  · have hchange := core_primary_change_positive ⟨hp,(abs_le.mp hx).2⟩
    nlinarith [OneEnvelope.core_baseline]
  · let z : ℝ := -x
    have hz : z∈Icc 0 (7/10) := ⟨by dsimp [z]; linarith,
      by dsimp [z]; linarith [(abs_le.mp hx).1]⟩
    have he : x= -z := by dsimp [z]; ring
    rw [he,core_primary_change_negative hz,Real.cos_neg] at hlow
    by_cases hsmall : z≤3/5
    · have hc := core_negative_change_nonneg ⟨hz.1,hsmall⟩
      have hpositive := mul_nonneg hb (sub_nonneg.mpr (Real.cos_le_one z))
      nlinarith [OneEnvelope.core_baseline]
    · have hz' : z∈Icc (3/5) (7/10) := ⟨by linarith,hz.2⟩
      have hcut := one_mixed_negative_large_cut hs ht hz'
        (by simpa [he,sub_eq_add_neg] using hm)
      have hprod := (mul_lt_mul_of_pos_left hcut.2
        (by norm_num : (0:ℝ)<11/100)).trans
          (mul_lt_mul_of_pos_right hcut.1
            (show 0<1-Real.cos z by linarith [hcut.2]))
      have hc := core_negative_change_lower hz'
      nlinarith [OneEnvelope.core_baseline]

lemma one_corner_positive_primary_angle {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B) (hB : 1/2≤B)
    (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) : (3/10:ℝ)<x := by
  have ha := (outer_bounds hs).2.1.trans_lt outer_endpoint_bounds.2.1
  have hc := CoreAngleEndpoint.state_bounds ht
  have hp : 0<x := by
    by_contra! hn
    have hz : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    have tr := positive_trig hz
    have hA : 1/2≤A := hB.trans hc.2.2.2.1
    have hAs := mul_le_mul_of_nonneg_right hA tr.2.2.1
    have hBc := mul_le_mul_of_nonneg_right hB (by linarith [tr.1] : 0≤Real.cos (-x))
    have hw := oneWidth_ge_one hx
    rw [one_primary_margin hx] at hm
    simp only [Real.cos_neg,Real.sin_neg] at hAs hBc
    have hsum := tr.2.2.2.2.2
    simp only [Real.cos_neg,Real.sin_neg] at hsum
    nlinarith
  have tr := positive_trig ⟨hp.le,(abs_le.mp hx).2⟩
  have hAs := mul_le_mul_of_nonneg_right hc.2.1 tr.2.2.1
  have hBc := mul_le_mul_of_nonneg_right hB (by linarith [tr.1] : 0≤Real.cos x)
  rw [one_primary_margin hx] at hm
  dsimp [oneWidth] at hm
  rw [abs_of_nonneg tr.2.2.1] at hm
  by_contra! hsmall
  have hcos := r4_cos_lower_two hp.le
  have hsin := Real.sin_le hp.le
  have hx2 := pow_le_pow_left₀ hp.le hsmall 2
  nlinarith

lemma one_outer_core_corner_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B) (hB : 1/2≤B)
    (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x-outerLabel a b-coreLabel A B := by
  have hangle := one_corner_positive_primary_angle hs ht hB hx hm
  have hp : 0≤x := by linarith
  have tr := positive_trig ⟨hp,(abs_le.mp hx).2⟩
  have hc := CoreAngleEndpoint.state_bounds ht
  have hAs := mul_le_mul_of_nonneg_right hc.2.1 tr.2.2.1
  have hBc := mul_le_mul_of_nonneg_right hB (by linarith [tr.1] : 0≤Real.cos x)
  have hsloping := outer_sloping_upper hs
  rw [one_primary_margin hx] at hm
  dsimp [oneWidth] at hm
  rw [abs_of_nonneg tr.2.2.1] at hm
  have hb : b<(533/350)-(10/7)*Real.cos x+(5/42)*Real.sin x := by nlinarith
  have hsL := (outer_label_error hs).2
  have htL := (core_label_bounds ht).2
  have hcos := r4_cos_lower_two hp
  have hsin := Real.sin_le hp
  have hproduct := mul_nonneg (show 0≤x-3/10 by linarith)
    (show 0≤7/10-x by linarith [(abs_le.mp hx).2])
  have hpoly : (1/5:ℝ)≤(37/42)*x-(5/7)*x^2 := by nlinarith
  nlinarith [pi_hand_enclosure.1]

lemma one_mixed_side_lower {a b B x : ℝ} (hs : OuterState a b) (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2+x)) :
    OneEnvelope.envelope .core 0+corePrimaryChange x-(291/250)*B*(1-Real.cos x)≤
      Real.pi/2+x-outerLabel a b-coreLabel (7/12) B := by
  have hsource := one_core_source_support hs
  rw [one_primary_margin hx] at hm
  have hm' := mul_nonneg (show (0:ℝ)≤291/250 by norm_num) hm
  dsimp [OneEnvelope.envelope,OneEnvelope.weight,OneEnvelope.offset,corePrimaryChange,coreLabel]
  norm_num
  nlinarith

lemma one_side_positive_change {x B : ℝ} (hx : x∈Icc 0 (7/10)) (hB : 0≤B ∧ B≤1/2) :
    0≤corePrimaryChange x-(291/250)*B*(1-Real.cos x) := by
  have tr := positive_trig hx
  have hBc := mul_le_mul_of_nonneg_right hB.2
    (sub_nonneg.mpr (Real.cos_le_one x))
  have hs := Real.sin_le hx.1
  have hc := r4_cos_lower_two hx.1
  have hxx := mul_le_mul_of_nonneg_right hx.2 hx.1
  dsimp [corePrimaryChange,oneWidth]
  rw [abs_of_nonneg tr.2.2.1]
  nlinarith

lemma one_side_negative_angle_cut {a b B z : ℝ} (hs : OuterState a b)
    (hB : 0≤B ∧ B≤1/2) (hz : z∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2-z)) : z<1/2 := by
  have hx : |-z|≤7/10 := by rw [abs_neg,abs_of_nonneg hz.1]; exact hz.2
  have tr := positive_trig hz
  have hBc := mul_nonneg hB.1 (by linarith [tr.1] : 0≤Real.cos z)
  have ha := (outer_bounds hs).2.1.trans_lt outer_endpoint_bounds.2.1
  have hm' : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2+(-z)) := by
    simpa [sub_eq_add_neg] using hm
  rw [one_primary_margin hx] at hm'
  dsimp [oneWidth] at hm'
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1] at hm'
  by_contra! hlarge
  have hh := trig_concave_gt (α := 0) (A := (13/12:ℝ)) (B := (1/2:ℝ))
    (m := (183/200:ℝ)) (l := (1/2:ℝ)) (u := (7/10:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three])
    (show z∈Icc (1/2) (7/10) from ⟨hlarge,hz.2⟩)
    (by linarith [primary_fixed_trig.2.2.1,primary_fixed_trig.2.2.2.1])
    (by linarith [cap_trig.1,cap_trig.2.2.1])
  nlinarith

lemma one_side_negative_transverse_cut {a b B z : ℝ} (hs : OuterState a b)
    (hB : 0≤B ∧ B≤1/2) (hz : z∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2-z)) : B<83/200 := by
  have hx : |-z|≤7/10 := by rw [abs_neg,abs_of_nonneg hz.1]; exact hz.2
  have tr := positive_trig hz
  have hfirst := mul_nonneg (show 0≤7/12-B by linarith [hB.2]) tr.2.2.1
  have hsecond := mul_nonneg (show 0≤B+1/2 by linarith [hB.1])
    (show 0≤Real.sin z+Real.cos z-1 by linarith [tr.2.2.2.2.2])
  have ha := (outer_bounds hs).2.1.trans_lt outer_endpoint_bounds.2.1
  have hm' : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2+(-z)) := by
    simpa [sub_eq_add_neg] using hm
  rw [one_primary_margin hx] at hm'
  dsimp [oneWidth] at hm'
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1] at hm'
  nlinarith

lemma one_side_negative_small_change {B z : ℝ} (hz : z∈Icc 0 (2/5))
    (hB : 0≤B ∧ B≤83/200) :
    0≤coreNegativeChange z-(291/250)*B*(1-Real.cos z) := by
  have hs := Real.sin_ge_sub_cube hz.1
  have hc := r4_cos_lower_two hz.1
  have hBc := mul_le_mul_of_nonneg_right hB.2 (sub_nonneg.mpr (Real.cos_le_one z))
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hz3 := mul_le_mul_of_nonneg_right hz2 hz.1
  have hzz := mul_le_mul_of_nonneg_right hz.2 hz.1
  dsimp [coreNegativeChange]
  nlinarith

lemma one_side_negative_middle_cut {a b B z : ℝ} (hs : OuterState a b)
    (hB : 0≤B ∧ B≤1/2) (hz : z∈Icc (2/5) (1/2))
    (hm : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2-z)) : B<1/25 := by
  have hz' : z∈Icc 0 (7/10) := ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hx : |-z|≤7/10 := by rw [abs_neg,abs_of_nonneg hz'.1]; exact hz'.2
  have tr := positive_trig hz'
  have hcm := cos_anti hz' (show (1/2:ℝ)∈Icc 0 (7/10) by norm_num) hz.2
  have hc : (7/8:ℝ)≤Real.cos z := by linarith [primary_fixed_trig.2.2.2.1]
  have hBc := mul_le_mul_of_nonneg_left hc hB.1
  have hh := trig_concave_gt (α := 0) (A := (13/12:ℝ)) (B := (1/2:ℝ))
    (m := (22/25:ℝ)) (l := (2/5:ℝ)) (u := (1/2:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three]) hz
    (by linarith [primary_fixed_trig.1,primary_fixed_trig.2.1])
    (by linarith [primary_fixed_trig.2.2.1,primary_fixed_trig.2.2.2.1])
  have ha := (outer_bounds hs).2.1.trans_lt outer_endpoint_bounds.2.1
  have hm' : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2+(-z)) := by
    simpa [sub_eq_add_neg] using hm
  rw [one_primary_margin hx] at hm'
  dsimp [oneWidth] at hm'
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1] at hm'
  nlinarith

lemma one_outer_core_side_primary {a b B x : ℝ} (hs : OuterState a b)
    (hB : 0≤B ∧ B≤1/2) (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x-outerLabel a b-coreLabel (7/12) B := by
  have hlow := one_mixed_side_lower hs hx hm
  by_cases hp : 0≤x
  · have hchange := one_side_positive_change ⟨hp,(abs_le.mp hx).2⟩ hB
    linarith [OneEnvelope.core_baseline]
  · let z : ℝ := -x
    have hz : z∈Icc 0 (7/10) := ⟨by dsimp [z]; linarith,
      by dsimp [z]; linarith [(abs_le.mp hx).1]⟩
    have he : x= -z := by dsimp [z]; ring
    have hm' : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2-z) := by
      simpa [he,sub_eq_add_neg] using hm
    have hangle := one_side_negative_angle_cut hs hB hz hm'
    rw [he,core_primary_change_negative hz,Real.cos_neg] at hlow
    by_cases hsmall : z≤2/5
    · have hcut := one_side_negative_transverse_cut hs hB hz hm'
      have hchange := one_side_negative_small_change ⟨hz.1,hsmall⟩ ⟨hB.1,hcut.le⟩
      linarith [OneEnvelope.core_baseline]
    · have hcut := one_side_negative_middle_cut hs hB
        ⟨by linarith,hangle.le⟩ hm'
      have hchange := core_negative_change_nonneg ⟨hz.1,by linarith⟩
      have hBc := mul_le_mul_of_nonneg_right hcut.le
        (sub_nonneg.mpr (Real.cos_le_one z))
      have hc := r4_cos_lower_two hz.1
      have hz2 := pow_le_pow_left₀ hz.1 hangle.le 2
      have hextra : (291/250)*B*(1-Real.cos z)≤291/50000 := by nlinarith
      nlinarith [OneEnvelope.core_baseline]

theorem one_outer_core_positive_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B) (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x-outerLabel a b-coreLabel A B := by
  rcases ht with ⟨rfl,hB0,hB1⟩ | ⟨hB0,hBA,hcircle⟩
  · exact one_outer_core_side_primary hs ⟨hB0,hB1⟩ hx hm
  · exact one_outer_core_corner_primary hs (Or.inr ⟨hB0,hBA,hcircle⟩) hB0 hx hm

end SquaresInCircles.Eight.CommonQuarter
end
end
end

section
@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.CommonQuarter

open WordProblems

theorem one_primary_cost {source target : RadialKind} {a b A B x : ℝ}
    (hs : State source a b) (ht : State target A B) (σ τ : Bool)
    (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (sign σ) (sign τ) (Real.pi/2+x)) :
    (157/200:ℝ)<cost source target σ τ a b A B (Real.pi/2+x) := by
  by_cases hso : source=.outer
  · have hs' : OuterState a b := by simpa [State,hso] using hs
    have hsL := (outer_label_bounds hs').1.le
    by_cases hto : target=.outer
    · have ht' : OuterState A B := by simpa [State,hto] using ht
      cases τ
      · have hm' : 0≤forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+x) := by
          simpa [forwardMargin,sign] using hm
        have hh := one_outer_negative_primary hs' ht' hx hm'
        cases σ <;> norm_num [cost,sign,label,hso,hto] <;> linarith
      · have hm' : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x) := by
          simpa [forwardMargin,sign] using hm
        have hh := one_outer_opposite_primary hs' ht' hx hm'
        cases σ <;> norm_num [cost,sign,label,hso,hto] <;> linarith
    · have ht' : CorePairGeometry.CoreState A B := by simpa [State,hto] using ht
      cases τ
      · have hm' : 0≤forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+x) := by
          simpa [forwardMargin,sign] using hm
        have hh := one_outer_core_negative_primary hs' ht' hx hm'
        cases σ <;> norm_num [cost,sign,label,hso,hto] <;> linarith
      · have hm' : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x) := by
          simpa [forwardMargin,sign] using hm
        have hh := one_outer_core_positive_primary hs' ht' hx hm'
        cases σ <;> norm_num [cost,sign,label,hso,hto] <;> linarith
  · have hs' : CorePairGeometry.CoreState a b := by simpa [State,hso] using hs
    exact one_core_primary_cost hso hs' ht σ τ hx hm

/-- The continuous one-quarter inequality, from the weak separating owner alone, with no
center-gap premise. -/
theorem one_cost {source target : RadialKind} {a b A B x : ℝ}
    (hs : State source a b) (ht : State target A B) (σ τ : Bool)
    (hx : |x|≤7/10) (j : Fin 4)
    (hm : 0≤forwardMargin j a b A B (sign σ) (sign τ) (Real.pi/2+x)) :
    (157/200:ℝ)<cost source target σ τ a b A B (Real.pi/2+x) := by
  fin_cases j
  · exact one_secondary_cost hs ht σ τ hx hm
  · have hr : 0≤forwardMargin 3 A B a b (sign (!τ)) (sign (!σ)) (Real.pi/2+x) := by
      change 0≤forwardMargin 1 a b A B (sign σ) (sign τ) (Real.pi/2+x) at hm
      rw [← margin_reverse 1 σ τ a b A B (Real.pi/2+x)] at hm
      simpa using hm
    simpa [cost_reverse] using one_primary_cost ht hs (!τ) (!σ) hx hr
  · have hr : 0≤forwardMargin 0 A B a b (sign (!τ)) (sign (!σ)) (Real.pi/2+x) := by
      change 0≤forwardMargin 2 a b A B (sign σ) (sign τ) (Real.pi/2+x) at hm
      rw [← margin_reverse 2 σ τ a b A B (Real.pi/2+x)] at hm
      simpa using hm
    simpa [cost_reverse] using one_secondary_cost ht hs (!τ) (!σ) hx hr
  · exact one_primary_cost hs ht σ τ hx hm

/-- The one-quarter cost on the boundary cycle, with its closed radial states, tangent signs and
weak owner. -/
theorem actual_one (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hk : F.word hgap pi_lt_22_over_7 i=1) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (157/200:ℝ)<QuarterWordGeometry.phaseValue F hgap i+
      QuarterWordGeometry.commonMarker C i-QuarterWordGeometry.commonMarker C (next i) := by
  have hm := QuarterWordGeometry.original_margin C F hgap i j hj
  have he : QuarterWordGeometry.phaseValue F hgap i=
      Real.pi/2+QuarterWordGeometry.difference F i := by
    simp [QuarterWordGeometry.phaseValue,hk]
    ring
  rw [he] at hm ⊢
  have hh := one_cost (actual_state C i) (actual_state C (next i))
    (QuarterWordGeometry.positiveOf C i) (QuarterWordGeometry.positiveOf C (next i))
    (QuarterWordGeometry.difference_small F i).le j hm
  simpa [cost,QuarterWordGeometry.commonMarker,commonValue_eq] using hh

end SquaresInCircles.Eight.CommonQuarter
end
end
end
