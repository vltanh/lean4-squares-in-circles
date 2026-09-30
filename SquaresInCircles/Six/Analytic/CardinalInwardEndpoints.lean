import SquaresInCircles.Six.Analytic.FrozenPrimaryEndpoints

/-!
# Cardinal-W inward-primary endpoint bounds

A cardinal cap with transverse coordinate below 1/2 implies a+cx>=1.
Using that weaker but exact geometric inequality makes the residual for
weights (13/20,1/20,3/10) concave before support maximization. The only
endpoints are v=-w in {0,2/5} and d in {0,pi/4}.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma west_cardinal_radial_lower {w a b cx cy : ℝ}
    (ha : 1/2≤a) (hb : |b|≤1/2)
    (hwest : 0≤centralMargin .west (Real.pi+w) a b cx cy) : 1≤a+cx := by
  simp only [centralMargin,centerX,angularWidth,Real.cos_pi_add,
    Real.sin_pi_add,abs_neg] at hwest
  have hs : -(b*Real.sin w)≤|b|*|Real.sin w| := by
    simpa only [abs_mul] using neg_le_abs (b*Real.sin w)
  have hb' := mul_le_mul_of_nonneg_right hb (abs_nonneg (Real.sin w))
  have hc := mul_nonneg (show 0≤a-1/2 by linarith) (show 0≤1-Real.cos w by linarith [Real.cos_le_one w])
  have hca := le_abs_self (Real.cos w)
  nlinarith

def cardinalInwardFrozen (v d aw ad bd cx cy : ℝ) : ℝ :=
  frozenTrig (21/40-(7/20)*aw-(13/20)*ad-cx/20) 0 0
    ((13/20)*(1/2-cx)) ((13/20)*(1/2-cy))
    ((3/10)*(1/2+ad)) ((3/10)*(1/2-bd)) v d

lemma cardinal_inward_norm_identity (q : ℝ) :
    (13/20-(3/10)*Real.cos q)^2+((3/10)*Real.sin q)^2=41/80-(39/100)*Real.cos q := by
  nlinarith [Real.sin_sq_add_cos_sq q]

lemma cardinal_inward_endpoint_lower {v d aw ad bd cx cy L X Y : ℝ}
    (haw : aw≤rho0) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hq : 0≤Real.sin (v+d)) (hL : 0≤L)
    (hNorm : 41/80-(39/100)*Real.cos (v+d)≤L^2)
    (hX : 0≤X) (hY : 0≤Y)
    (hgX : 1/20+(13/20)*Real.cos d≤X) (hgY : (13/20)*Real.sin d≤Y) :
    17/20+(13/40)*(Real.cos d+Real.sin d)+(3/10)*Real.sin (v+d)-
      (7/20)*(1113/1000)-(1689/1000)*L-(113/1000)*(X+Y)≤
        cardinalInwardFrozen v d aw ad bd cx cy := by
  have hv := vertex_linear_upper hD
    (U := 13/20-(3/10)*Real.cos (v+d)) (V := (3/10)*Real.sin (v+d))
    (by positivity) hL (by rwa [cardinal_inward_norm_identity])
  have hC := coarse_central_work hc hX hY hgX hgY
  have haw' : aw≤1113/1000 := haw.trans rho0_upper.le
  dsimp [cardinalInwardFrozen,frozenTrig]
  nlinarith

lemma two_fifths_endpoint_bracket :
    (23:ℝ)/25≤Real.cos (2/5) ∧ Real.cos (2/5)≤1 ∧
      (389:ℝ)/1000≤Real.sin (2/5) ∧ Real.sin (2/5)≤2/5 := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := (2:ℝ)/5)
  have hs := Real.sin_ge_sub_cube (x := (2:ℝ)/5) (by norm_num)
  have hsu := Real.sin_le (x := (2:ℝ)/5) (by norm_num)
  exact ⟨by nlinarith,Real.cos_le_one _,by nlinarith,hsu⟩

lemma cardinal_inward_corners {aw ad bd cx cy : ℝ}
    (haw : aw≤rho0) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<cardinalInwardFrozen 0 0 aw ad bd cx cy ∧
    0<cardinalInwardFrozen 0 (Real.pi/4) aw ad bd cx cy ∧
    0<cardinalInwardFrozen (2/5) 0 aw ad bd cx cy ∧
    0<cardinalInwardFrozen (2/5) (Real.pi/4) aw ad bd cx cy := by
  obtain ⟨hcl,hcu,hsl,hsu⟩ := two_fifths_endpoint_bracket
  obtain ⟨hhl,hhu,hsc⟩ := quarter_endpoint_bracket
  have hdiff : (52:ℝ)/100≤Real.cos (2/5)-Real.sin (2/5) := by linarith
  have hsum : (1309:ℝ)/1000≤Real.cos (2/5)+Real.sin (2/5) := by linarith
  have hmc := mul_le_mul hdiff hhl (by norm_num : (0:ℝ)≤707/1000)
    (show 0≤Real.cos (2/5)-Real.sin (2/5) by linarith)
  have hms := mul_le_mul hsum hhl (by norm_num : (0:ℝ)≤707/1000)
    (show 0≤Real.cos (2/5)+Real.sin (2/5) by linarith)
  have hqcos : (52:ℝ)/100*(707/1000)≤Real.cos (2/5+Real.pi/4) := by
    rw [Real.cos_add,hsc]
    nlinarith only [hmc]
  have hqsin : (1309:ℝ)/1000*(707/1000)≤Real.sin (2/5+Real.pi/4) := by
    rw [Real.sin_add,hsc]
    nlinarith only [hms]
  refine ⟨?_,?_,?_,?_⟩
  · have h := cardinal_inward_endpoint_lower (v := 0) (d := 0)
      (L := 7/20) (X := 7/10) (Y := 0) haw hD hc
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    norm_num at h
    linarith
  · have h := cardinal_inward_endpoint_lower (v := 0) (d := Real.pi/4)
      (L := 487/1000) (X := 1/20+(13/20)*(708/1000)) (Y := (13/20)*(708/1000))
      haw hD hc (by rw [zero_add,hsc]; linarith) (by norm_num)
      (by simp only [zero_add]; nlinarith) (by norm_num) (by norm_num)
      (by linarith) (by rw [hsc]; linarith)
    simp only [zero_add,hsc] at h
    linarith
  · have h := cardinal_inward_endpoint_lower (v := (2:ℝ)/5) (d := 0)
      (L := 393/1000) (X := 7/10) (Y := 0) haw hD hc
      (by simp only [add_zero]; linarith) (by norm_num)
      (by simp only [add_zero]; nlinarith) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    simp only [Real.cos_zero,Real.sin_zero,add_zero] at h
    linarith
  · have h := cardinal_inward_endpoint_lower (v := (2:ℝ)/5) (d := Real.pi/4)
      (L := 608/1000) (X := 1/20+(13/20)*(708/1000)) (Y := (13/20)*(708/1000))
      haw hD hc (by linarith) (by norm_num) (by nlinarith)
      (by norm_num) (by norm_num) (by linarith) (by rw [hsc]; linarith)
    rw [hsc] at h
    linarith

lemma cardinal_inward_frozen_positive {v d aw ad bd cx cy : ℝ}
    (hv : 0≤v ∧ v≤2/5) (hd : 0≤d ∧ d≤Real.pi/4)
    (haw : aw≤rho0) (hD : ContainedChart ad |bd|) (hb : |bd|<1/2)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<cardinalInwardFrozen v d aw ad bd cx cy := by
  have hx : 0≤1/2-cx := by linarith [hc.1.2,c0_lt_23_200]
  have hy : 0≤1/2-cy := by linarith [hc.2.2,c0_lt_23_200]
  have ha : 0≤1/2+ad := by linarith [hD.half_le]
  have hb' : 0≤1/2-bd := by linarith [(abs_lt.mp hb).2]
  obtain ⟨h00,h0D,hV0,hVD⟩ := cardinal_inward_corners haw hD hc
  unfold cardinalInwardFrozen
  exact frozenTrig_positive (by norm_num) (by norm_num) (by positivity) (by positivity)
    (by positivity) (by positivity) (by norm_num) (by positivity)
    (by linarith [Real.pi_gt_d2]) hv hd h00 h0D hV0 hVD

end SquaresInCircles.Six.Analytic
