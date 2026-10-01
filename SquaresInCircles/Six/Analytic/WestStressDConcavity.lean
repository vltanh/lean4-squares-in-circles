import SquaresInCircles.Six.Analytic.WestStressBounds
import SquaresInCircles.Six.Analytic.WestSecondaryAxes
import SquaresInCircles.Six.Analytic.RadicalTrigConcavity

/-!
# Concavity of the D-secondary stress components

The positive mixed W-force term is retained. The radical curvature identity
reduces its concavity to R0*sqrt(53/200+(9/40)sin d)<=cos d+sin d, which
follows from cos d>=12/25 and the unit-circle identity. The D-force term has
root at most 1/2 and an even simpler curvature bound. The only interval splits
are the signs of the two original angles, where absolute values change form.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def westJ (positive:Bool) (t:ℝ) : ℝ :=
  (9/40-(9/20)*c0)*Real.cos t+
    (if positive then 9/40-(9/20)*c0 else -9/40)*Real.sin t

def westH (positive:Bool) (u:ℝ) : ℝ :=
  radicalTrig (3/10) (if positive then 0 else -3/10) (61/400) (-3/20) R0 u

def westG (d:ℝ) : ℝ := radicalTrig (1/4) (1/4) (53/200) (9/40) R0 d

def westDForm (pt pu:Bool) (t u:ℝ) : ℝ :=
  17/20-(3/10)*c0+westJ pt t+westH pu u+westG (u-t)

lemma westDForm_eq {t u:ℝ} (pt pu:Bool)
    (ht:-2/3≤t ∧ t≤2/5) (hu:-2/5≤u ∧ u≤2/5)
    (htsign:if pt then 0≤t else t≤0) (husign:if pu then 0≤u else u≤0) :
    westDForm pt pu t u=westStressD t u := by
  have hsinT : if pt then 0≤Real.sin t else Real.sin t≤0 := by
    cases pt
    · exact west_sin_nonpos ⟨ht.1,htsign⟩
    · exact Real.sin_nonneg_of_nonneg_of_le_pi htsign
        (by linarith [ht.2,Real.pi_gt_d2])
  have hsinU : if pu then 0≤Real.sin u else Real.sin u≤0 := by
    cases pu
    · exact west_sin_nonpos ⟨by linarith [hu.1],husign⟩
    · exact Real.sin_nonneg_of_nonneg_of_le_pi husign
        (by linarith [hu.2,Real.pi_gt_d2])
  cases pt <;> cases pu
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true] at hsinT hsinU
  all_goals simp only [westDForm,westJ,westH,westG,radicalTrig,westStressD,
    westCentralSupport,Bool.false_eq_true,ite_false,ite_true]
  all_goals first
    | rw [abs_of_nonpos hsinT,max_eq_right hsinT,max_eq_left (by linarith : 0≤-Real.sin u)]
    | rw [abs_of_nonpos hsinT,max_eq_right hsinT,max_eq_right (by linarith : -Real.sin u≤0)]
    | rw [abs_of_nonneg hsinT,max_eq_left hsinT,max_eq_left (by linarith : 0≤-Real.sin u)]
    | rw [abs_of_nonneg hsinT,max_eq_left hsinT,max_eq_right (by linarith : -Real.sin u≤0)]
  all_goals ring_nf

lemma westJ_coefficient_pos : 0<9/40-(9/20)*c0 := by linarith [c0_lt_23_200]

private lemma westJ_concave_aux (B l u:ℝ)
    (hcos:∀x∈Set.Icc l u,0≤Real.cos x)
    (hsin:∀x∈Set.Icc l u,0≤B*Real.sin x) :
    ConcaveOn ℝ (Set.Icc l u)
      (fun x=>(9/40-(9/20)*c0)*Real.cos x+B*Real.sin x) := by
  have h := radicalTrig_concave (A:=9/40-(9/20)*c0) (B:=B)
    (p:=1) (q:=0) (R:=0) (l:=l) (u:=u) (by norm_num) (by norm_num)
    (by intro x hx; norm_num)
    (by
      intro x hx
      have hp := mul_nonneg westJ_coefficient_pos.le (hcos x hx)
      have hs := hsin x hx
      simp only [zero_mul,add_zero]
      nlinarith)
  refine h.congr ?_
  intro x _
  simp only [radicalTrig]
  ring

lemma westJ_negative_concave : ConcaveOn ℝ (Set.Icc (-2/3) 0) (westJ false) := by
  apply westJ_concave_aux (-9/40) (-2/3) 0
  · intro x hx
    have h := west_angle_bounds ⟨hx.1,by linarith [hx.2]⟩
    linarith [h.1]
  · intro x hx
    have hs := west_sin_nonpos hx
    nlinarith

lemma westJ_positive_concave : ConcaveOn ℝ (Set.Icc 0 (2/5)) (westJ true) := by
  apply westJ_concave_aux (9/40-(9/20)*c0) 0 (2/5)
  · intro x hx
    have h := west_angle_bounds ⟨by linarith [hx.1],hx.2⟩
    linarith [h.1]
  · intro x hx
    exact mul_nonneg westJ_coefficient_pos.le
      (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_gt_d2]))

lemma westG_concave : ConcaveOn ℝ (Set.Icc 0 (16/15)) westG := by
  apply radicalTrig_concave R0_nonneg (by norm_num : ((9:ℝ)/40)^2≤((53:ℝ)/200)^2)
  · intro x hx
    have h := (west_difference_trig hx).2.1
    linarith
  · intro x hx
    have htr := west_difference_trig hx
    have hrad : 0≤53/200+(9/40)*Real.sin x := by linarith [htr.2.1]
    have hs := Real.sq_sqrt hrad
    have hid : (R0*Real.sqrt (53/200+(9/40)*Real.sin x))^2=
        Q0*(53/200+(9/40)*Real.sin x) := by
      calc
        _ = R0^2*(Real.sqrt (53/200+(9/40)*Real.sin x))^2 := by ring
        _ = _ := by rw [R0_sq,hs]
    have hp := mul_nonneg (show 0≤Real.cos x-12/25 by linarith [htr.1]) htr.2.1
    have hsq : (R0*Real.sqrt (53/200+(9/40)*Real.sin x))^2≤
        (Real.cos x+Real.sin x)^2 := by
      rw [hid]
      norm_num [Q0]
      nlinarith [htr.2.2]
    have hcs : 0≤Real.cos x+Real.sin x := by linarith [htr.1,htr.2.1]
    have hbound : R0*Real.sqrt (53/200+(9/40)*Real.sin x)≤Real.cos x+Real.sin x := by
      by_contra! hbad
      have hmul := mul_pos (sub_pos.mpr hbad)
        (show 0<R0*Real.sqrt (53/200+(9/40)*Real.sin x)+(Real.cos x+Real.sin x) by linarith)
      nlinarith
    nlinarith

private lemma westH_concave_aux (B l u:ℝ)
    (hsmall:∀x∈Set.Icc l u,|x|≤2/5)
    (hsign:∀x∈Set.Icc l u,0≤B*Real.sin x) :
    ConcaveOn ℝ (Set.Icc l u) (radicalTrig (3/10) B (61/400) (-3/20) R0) := by
  have hb (x:ℝ) (hx:x∈Set.Icc l u) :
      23/25≤Real.cos x ∧ -2/5≤Real.sin x ∧ Real.sin x≤2/5 := by
    have hs : |Real.sin x|≤2/5 := by
      have hh := Real.abs_sin_sub_sin_le x 0
      simp only [Real.sin_zero,sub_zero] at hh
      exact hh.trans (hsmall x hx)
    have hsq := pow_le_pow_left₀ (abs_nonneg x) (hsmall x hx) 2
    rw [sq_abs] at hsq
    exact ⟨by nlinarith [Real.one_sub_sq_div_two_le_cos (x:=x)],
      by linarith [(abs_le.mp hs).1],(abs_le.mp hs).2⟩
  apply radicalTrig_concave R0_nonneg (by norm_num : ((-3:ℝ)/20)^2≤((61:ℝ)/400)^2)
  · intro x hx
    have h := hb x hx
    linarith [h.2.2]
  · intro x hx
    have h := hb x hx
    have hroot : Real.sqrt (61/400+(-3/20)*Real.sin x)≤1/2 := by
      have hh := Real.sqrt_le_sqrt
        (show 61/400+(-3/20)*Real.sin x≤((1:ℝ)/2)^2 by linarith [h.2.1])
      rwa [Real.sqrt_sq (by norm_num)] at hh
    have hm := mul_le_mul (show R0≤17/10 by linarith [west_radius_bound]) hroot
      (Real.sqrt_nonneg _) (by norm_num : (0:ℝ)≤17/10)
    have hn := hsign x hx
    nlinarith [h.1]

lemma westH_negative_concave : ConcaveOn ℝ (Set.Icc (-2/5) 0) (westH false) := by
  apply westH_concave_aux (-3/10) (-2/5) 0
  · intro x hx
    exact abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  · intro x hx
    have h := west_sin_nonpos (t:=x) ⟨by linarith [hx.1],hx.2⟩
    nlinarith

lemma westH_positive_concave : ConcaveOn ℝ (Set.Icc 0 (2/5)) (westH true) := by
  apply westH_concave_aux 0 0 (2/5)
  · intro x hx
    exact abs_le.mpr ⟨by linarith [hx.1],hx.2⟩
  · intro x hx
    simp

/-- The first coordinate follows J and the reversed affine argument of G. -/
lemma westDForm_concave_t (pt pu:Bool) (u l h:ℝ)
    (hj:ConcaveOn ℝ (Set.Icc l h) (westJ pt))
    (hδ:∀x∈Set.Icc l h,u-x∈Set.Icc 0 (16/15)) :
    ConcaveOn ℝ (Set.Icc l h) (fun t=>westDForm pt pu t u) := by
  have hg := concave_affine_argument (a:=-1) (b:=u) westG_concave
    (by intro x hx; simpa only [neg_one_mul,neg_add_eq_sub] using hδ x hx)
  have hc := concave_constant (17/20-(3/10)*c0+westH pu u) l h
  have H := (hc.add hj).add hg
  convert H using 1
  funext x
  dsimp [westDForm]
  congr 1 <;> ring_nf

/-- The second coordinate follows H and the translated argument of G. -/
lemma westDForm_concave_u (pt pu:Bool) (t l h:ℝ)
    (hh:ConcaveOn ℝ (Set.Icc l h) (westH pu))
    (hδ:∀x∈Set.Icc l h,x-t∈Set.Icc 0 (16/15)) :
    ConcaveOn ℝ (Set.Icc l h) (fun u=>westDForm pt pu t u) := by
  have hg := concave_affine_argument (a:=1) (b:=-t) westG_concave
    (by intro x hx; simpa only [one_mul,sub_eq_add_neg] using hδ x hx)
  have hc := concave_constant (17/20-(3/10)*c0+westJ pt t) l h
  have H := (hc.add hh).add hg
  refine H.congr ?_
  intro x _
  have e : 1*x+-t=x-t := by ring
  simp only [Pi.add_apply,westDForm,e]

lemma westDForm_concave_diagonal (pt pu:Bool) (l h:ℝ)
    (hj:ConcaveOn ℝ (Set.Icc l h) (westJ pt))
    (hh:ConcaveOn ℝ (Set.Icc l h) (westH pu)) :
    ConcaveOn ℝ (Set.Icc l h) (fun t=>westDForm pt pu t t) := by
  have hc := concave_constant (17/20-(3/10)*c0+westG 0) l h
  have H := (hc.add hj).add hh
  convert H using 1
  funext x
  simp only [westDForm,sub_self,Pi.add_apply]
  ring

end SquaresInCircles.Six.Analytic
