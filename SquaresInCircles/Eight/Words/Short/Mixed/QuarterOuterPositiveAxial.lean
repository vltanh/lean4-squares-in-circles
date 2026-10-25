module

public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterPositiveReferences

/-!
# Eight squares: whole axial curvature and the unique interior/axial event

The derivative of the
axial curvature is controlled by the single completed-square polynomial
E(U) on the entire source coordinate interval. The resulting 1.09
curvature reserve proves every axial value. The target derivative H
is strictly increasing on the whole physical axial interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
open CommonQuarter CorePairGeometry Arithmetic

theorem angle_small {x : ℝ} (hx : x∈angleDomain) : x∈Icc 0 (7/10) :=
  ⟨hx.1,hx.2.trans (by norm_num [cap])⟩

theorem axial_coordinate {x : ℝ} (hx : x∈angleDomain) : U x∈coordinateDomain := by
  have h0 := U_strictMono.monotoneOn (by norm_num : (0:ℝ)∈Icc 0 (7/10)) (angle_small hx) hx.1
  have hc := U_strictMono.monotoneOn (angle_small hx)
    (by norm_num [cap] : cap∈Icc 0 (7/10)) hx.2
  have hU0 : U 0=3/2 := by norm_num [U]
  rw [hU0] at h0
  exact ⟨h0,hc.trans Reference.cap_height.2.le⟩

theorem axial_trig {x : ℝ} (hx : x∈angleDomain) :
    (903/1000:ℝ)<Real.cos x ∧ Real.sin x<107/250 ∧ (191/250:ℝ)<h x := by
  have hc := cos_anti (angle_small hx) (by norm_num [cap] : cap∈Icc 0 (7/10)) hx.2
  have hs := sin_mono (angle_small hx) (by norm_num [cap] : cap∈Icc 0 (7/10)) hx.2
  have hC := Reference.cap_trig.1.trans_le hc
  have hS := hs.trans_lt Reference.cap_trig.2
  refine ⟨hC,hS,?_⟩
  dsimp [h,c0]
  linarith

theorem E_lower (u : ℝ) : (867/1000:ℝ)<E u := by
  have hs := sq_nonneg (u-(Q0+1-J)/2)
  norm_num [Q0,J,E] at hs ⊢
  nlinarith

theorem curvature_hasDerivAt (r : Row) {u : ℝ} (hu : u∈coordinateDomain) :
    HasDerivAt (curvature r) (curvatureD r u) u := by
  have hf := (Mdd_hasDerivAt r hu).fun_mul
    ((((hasDerivAt_id' u).sub_const 1).pow 2).const_sub J)
  have hg := (Md_hasDerivAt r hu).fun_mul ((hasDerivAt_id' u).sub_const 1)
  exact (hf.fun_sub hg).congr_deriv (by simp only [curvatureD]; norm_num <;> ring)

theorem curvatureD_identity (r : Row) {u : ℝ} (hu : u∈coordinateDomain) :
    curvatureD r u*(V u)^5=
      ocQ r*(3*Q0*E u-u*(V u)^4)-ocP r*(V u)^5 := by
  have hn := (V_positive hu).ne'
  have hs := V_square hu
  simp only [curvatureD,Mddd,Mdd,Md,E]
  generalize V u = w at hn hs ⊢
  rw [← hs]
  field_simp
  ring

theorem curvatureD_positive (r : Row) (hr : Rows r) {u : ℝ} (hu : u∈coordinateDomain) :
    0<curvatureD r u := by
  have hb := coefficients r hr
  have hq : 0<ocQ r := by linarith [hb.2.2.1]
  have hv := V_bounds hu
  have hv0 := V_positive hu
  have hv4 : (V u)^4≤(833/500:ℝ)^2 := by nlinarith [sq_nonneg ((V u)^2-833/500)]
  have hv5 := pow_le_pow_left₀ hv0.le hv.2.1.le 5
  have hu0 : 0≤u := by linarith [hu.1]
  have huV := mul_le_mul hu.2 hv4 (by positivity : 0≤(V u)^4) (by norm_num : (0:ℝ)≤383/200)
  have hpV := mul_le_mul_of_nonneg_right hb.2.1.le (pow_nonneg hv0.le 5)
  have hEV := mul_lt_mul_of_pos_left (E_lower u) (by norm_num [Q0] : (0:ℝ)<3*Q0)
  have hbracket : (39/10:ℝ)<3*Q0*E u-u*(V u)^4-(253/1000)*(V u)^5 := by
    norm_num [Q0] at hEV hv5 huV ⊢
    linarith
  have hm := mul_pos hq (show 0<3*Q0*E u-u*(V u)^4-(253/1000)*(V u)^5 by linarith)
  have hid := curvatureD_identity r hu
  have hpositive : 0<curvatureD r u*(V u)^5 := by linarith
  exact pos_of_mul_pos_left hpositive (pow_nonneg hv0.le 5)

theorem curvature_monotone (r : Row) (hr : Rows r) : MonotoneOn (curvature r) coordinateDomain :=
  monoOn_of_hasDeriv_nonneg
    (fun u hu => (curvature_hasDerivAt r hu).continuousAt.continuousWithinAt)
    (fun u hu => curvature_hasDerivAt r (Ioo_subset_Icc_self hu))
    (fun u hu => (curvatureD_positive r hr (Ioo_subset_Icc_self hu)).le)

theorem K_hasDerivAt (r : Row) {x : ℝ} (hx : x∈angleDomain) : HasDerivAt (K r) (Kd r x) x := by
  have hh := (((hasDerivAt_id' x).const_sub (Real.pi/2)).add_const (ocC r)).fun_add
    ((M_hasDerivAt r (axial_coordinate hx)).comp x (U_hasDerivAt x))
  exact hh.congr_deriv (by simp only [Kd])

theorem Kd_hasDerivAt (r : Row) {x : ℝ} (hx : x∈angleDomain) : HasDerivAt (Kd r) (Kdd r x) x := by
  have hh := (((Md_hasDerivAt r (axial_coordinate hx)).comp x (U_hasDerivAt x)).fun_mul
    (h_hasDerivAt x)).const_add (-1)
  refine hh.congr_deriv ?_
  simp only [Kdd,curvature,Function.comp]
  rw [← h_square]
  ring

theorem Kdd_lower (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) : (109/100:ℝ)<Kdd r x :=
  (Reference.initial_curvature r hr).trans_le (curvature_monotone r hr
    (by norm_num [coordinateDomain]) (axial_coordinate hx) (axial_coordinate hx).1)

theorem axial_lower (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) : (449/500:ℝ)<K r x := by
  by_cases hRise : Rising r
  · have hD : MonotoneOn (Kd r) angleDomain := monoOn_of_hasDeriv_nonneg
      (fun y hy => (Kd_hasDerivAt r hy).continuousAt.continuousWithinAt)
      (fun y hy => Kd_hasDerivAt r (Ioo_subset_Icc_self hy))
      (fun y hy => by linarith [Kdd_lower r hr (Ioo_subset_Icc_self hy)])
    have hK : MonotoneOn (K r) angleDomain := monoOn_of_hasDeriv_nonneg
      (fun y hy => (K_hasDerivAt r hy).continuousAt.continuousWithinAt)
      (fun y hy => K_hasDerivAt r (Ioo_subset_Icc_self hy))
      (fun y hy => (Reference.initial_values r hr hRise).2.le.trans
        (hD (by norm_num [angleDomain,cap]) (Ioo_subset_Icc_self hy) hy.1.le))
    have hh := hK (by norm_num [angleDomain,cap]) hx hx.1
    linarith [(Reference.initial_values r hr hRise).1]
  · have href : reference r∈angleDomain := by
      dsimp [reference,angleDomain,cap]; split_ifs <;> norm_num
    have hh := CenteredMonomialBounds.second_derivative_tangent_lower
      (κ:=(109/100:ℝ)) (fun y hy => K_hasDerivAt r hy)
      (fun y hy => Kd_hasDerivAt r hy) (fun y hy => (Kdd_lower r hr hy).le) href hx
    have hs := sq_nonneg ((109/100)*(x-reference r)+Kd r (reference r))
    have hb := Reference.reference_bound r hr hRise
    nlinarith

theorem H_hasDerivAt (r : Row) {x : ℝ} (hx : x∈angleDomain) : HasDerivAt (H r) (Hd r x) x := by
  have hh := (((Md_hasDerivAt r (axial_coordinate hx)).comp x (U_hasDerivAt x)).fun_mul
    (Real.hasDerivAt_cos x)).sub_const (ocG r)
  exact hh.congr_deriv (by simp only [Hd,Function.comp]; ring)

theorem Hd_positive (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) : 0<Hd r x := by
  have hb := coefficients r hr
  have hq : 0<ocQ r := by linarith [hb.2.2.1]
  have hu := axial_coordinate hx
  have hv := V_bounds hu
  have hv0 := V_positive hu
  have tr := axial_trig hx
  have hs0 := (positive_trig (angle_small hx)).2.2.1
  have hv3 := pow_le_pow_left₀ hv0.le hv.2.1.le 3
  have hUV := mul_le_mul hu.2 hv.2.2.le (sq_nonneg _) (by norm_num : (0:ℝ)≤383/200)
  have hpV := mul_le_mul_of_nonneg_right hb.2.1.le (pow_nonneg hv0.le 3)
  have hqv3 := mul_le_mul_of_nonneg_left hv3 hq.le
  have hqUV := mul_le_mul_of_nonneg_left hUV hq.le
  have hsum : ocP r*(V (U x))^3+ocQ r*U x*(V (U x))^2≤
      ocQ r*((253/1000)*(1291/1000)^3+(383/200)*(833/500)) := by linarith
  have hprod := mul_le_mul hsum tr.2.1.le hs0
    (by positivity : 0≤ocQ r*((253/1000)*(1291/1000)^3+(383/200)*(833/500)))
  have hhk := mul_lt_mul'' tr.2.2 tr.1
    (by norm_num : (0:ℝ)≤191/250) (by norm_num : (0:ℝ)≤903/1000)
  have hnum := mul_lt_mul_of_pos_left hhk (mul_pos hq (by norm_num [Q0] : (0:ℝ)<Q0))
  have hid : Hd r x*(V (U x))^3=ocQ r*Q0*h x*Real.cos x-
      (ocP r*(V (U x))^3+ocQ r*U x*(V (U x))^2)*Real.sin x := by
    simp only [Hd,Mdd,Md]
    generalize V (U x) = w at hv0 ⊢
    field_simp
  have hpositive : 0<Hd r x*(V (U x))^3 := by
    norm_num [Q0] at hnum hid
    linarith
  exact pos_of_mul_pos_left hpositive (pow_nonneg hv0.le 3)

theorem H_strictMono (r : Row) (hr : Rows r) : StrictMonoOn (H r) angleDomain := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 cap)
  · exact fun x hx => (H_hasDerivAt r hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(H_hasDerivAt r (Ioo_subset_Icc_self hx)).deriv]
    exact Hd_positive r hr (Ioo_subset_Icc_self hx)

def IsTransition (r : Row) (e : ℝ) : Prop := e∈Ioo 0 (11/100:ℝ) ∧ H r e=0

theorem transition_exists_unique (r : Row) (hr : Rows r) (hi : Interior r) : ∃!e,IsTransition r e := by
  have hsmall : ∀x∈Icc 0 (11/100:ℝ),x∈angleDomain := by
    intro x hx; exact ⟨hx.1,hx.2.trans (by norm_num [cap])⟩
  have hc : ContinuousOn (H r) (Icc 0 (11/100:ℝ)) :=
    fun x hx => (H_hasDerivAt r (hsmall x hx)).continuousAt.continuousWithinAt
  obtain ⟨e,he,hzero⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤11/100) hc
    (show (0:ℝ)∈Icc (H r 0) (H r (11/100)) from
      ⟨(Reference.initial_event r hr).1 hi |>.le,by linarith [Reference.event_at_eleven r hr hi]⟩)
  have he0 : 0<e := lt_of_le_of_ne he.1 (by
    intro hh; subst e; exact (ne_of_lt ((Reference.initial_event r hr).1 hi)) hzero)
  have he1 : e<11/100 := lt_of_le_of_ne he.2 (by
    intro hh; rw [hh] at hzero; linarith [Reference.event_at_eleven r hr hi])
  refine ⟨e,⟨⟨he0,he1⟩,hzero⟩,?_⟩
  intro f hf
  apply (H_strictMono r hr).injOn (hsmall f ⟨hf.1.1.le,hf.1.2.le⟩) (hsmall e he)
  rw [hf.2,hzero]

theorem always_axial (r : Row) (hr : Rows r) (hi : ¬Interior r) {x : ℝ} (hx : x∈angleDomain) : 0<H r x :=
  ((Reference.initial_event r hr).2 hi).trans_le
    ((H_strictMono r hr).monotoneOn (by norm_num [angleDomain,cap]) hx hx.1)

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
