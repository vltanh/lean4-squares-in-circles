module

public import SquaresInCircles.Eight.TableFree.CommonOneSecondary

/-!
# Quarter-one primary contacts with an original core source

The primary owner does not involve the source tangent sign, so the
negative source label is the worst case. Positive targets are either
impossible or have a small transverse coordinate forced by the same
contact. Negative targets admit one concave support on the complete
negative angle interval, with a direct estimate on the positive interval.
Uncompiled source draft.
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
    simp only [label,if_pos hk]
    linarith [(outer_label_error hh).1]
  · have hh : CorePairGeometry.CoreState a b := by simpa [State,hk] using h
    simp only [label,if_neg hk]
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
