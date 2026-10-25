module

public import SquaresInCircles.Eight.TableFree.EPairMinimum

/-!
# The original E-pair minimum for negative total error

Uncompiled source draft. The outside-frame comparison uses the retained
EH contact at its actual frame. The tangent cuts are therefore derived
from the original contact, rather than imposed on E. Reflection exchanges
the two endpoint contacts and covers both signs of the original tangent.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ENegativePairMinimum
open CoreECharge

abbrev K : ℝ := 847/800

theorem pair_negate_angles (a b u v : ℝ) :
    pairDeficit a b (-u) (-v)=pairDeficit (-a) b u v := by
  simp only [pairDeficit,edgeWidth_neg,Real.sin_neg,Real.cos_neg]
  ring

theorem pair_reflect (a b u v : ℝ) :
    pairDeficit a (-b) v u=pairDeficit a b u v := by
  dsimp [pairDeficit]
  ring

theorem half_frame_trig {x : ℝ} (hx : x∈Icc 0 (frameCap/2)) :
    15/16≤Real.cos x ∧ 0≤Real.sin x ∧ Real.sin x≤7/20 ∧
      47/80≤Real.cos x-Real.sin x := by
  have hxu : x≤7/20 := by have h2 := hx.2; norm_num [frameCap] at h2; linarith
  have hs := Real.sin_le hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hx2 := pow_le_pow_left₀ hx.1 hxu 2
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,by norm_num [frameCap]; linarith⟩
  have hs0 := (transport_trig hx').2.2.1
  exact ⟨by linarith,hs0,by linarith,by linarith⟩

theorem projection_mono {a b : ℝ} (ha : 0≤a) (hba : b≤a) :
    MonotoneOn (fun x => a*Real.sin x+b*Real.cos x) (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · fun_prop
  · intro x _
    exact ((Real.hasDerivAt_sin x).const_mul a).add ((Real.hasDerivAt_cos x).const_mul b)
  · intro x hx
    have ht := transport_trig (Ioo_subset_Icc_self hx)
    have hmul := mul_le_mul_of_nonneg_right hba ht.2.2.1
    have hpos := mul_nonneg ha (sub_nonneg.mpr ht.2.2.2.2.le)
    nlinarith

theorem negative_same_minimum {a b e u : ℝ} (ha : 0≤a)
    (hb : 0≤b ∧ b≤9/10) (he : e∈Icc 0 frameCap) (hu : u∈Icc 0 e) :
    ehCharge (-a) b e≤pairDeficit a b (-u) (-(e-u)) := by
  have ht := transport_trig he
  have he2 : e≤7/10 := he.2
  have hloss := sub_nonneg.mpr ht.2.1
  have hmul := mul_le_mul_of_nonneg_right (show 1/2+b≤(7/5 : ℝ) by linarith) hloss
  have hsin := mul_nonneg (show 0≤a+1/2 by linarith) ht.2.2.1
  have hA : 0≤cosineCoefficient (-a) b e := by
    dsimp [cosineCoefficient]
    linarith [ht.1]
  have hB : 0≤ sameSineCoefficient (-a) b e := by
    dsimp [sameSineCoefficient]
    have h1 := mul_nonneg (show 0≤1/2+b by linarith) ht.2.2.1
    have h2 := mul_nonneg (show 0≤a+1/2 by linarith) hloss
    linarith
  have hconc : ConcaveOn ℝ (Icc 0 e)
      (harmonic (cosineCoefficient (-a) b e) (sameSineCoefficient (-a) b e)) := by
    apply harmonic_concave
    intro x hx
    exact harmonic_nonneg hA hB
      ⟨hx.1,by linarith [hx.2,Real.pi_gt_three]⟩
  have hmin := hconc.min_le_of_mem_Icc (left_mem_Icc.mpr he.1)
    (right_mem_Icc.mpr he.1) hu
  have hend := same_endpoint_comparison (a := -a) (e := e) hb.1
  rw [min_eq_left (by simpa [harmonic] using hend)] at hmin
  simp only [harmonic,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero] at hmin
  have hceq : ehCharge (-a) b e=cosineCoefficient (-a) b e-1 := by
    simp only [ehCharge,cosineCoefficient]; ring
  rw [pair_negate_angles,same_harmonic_identity he hu,hceq]
  simp only [harmonic]
  linarith

def outsideBracket (a b e n : ℝ) : ℝ :=
  Real.cos (e/2)*(Real.cos ((e+n)/2)-Real.sin ((e+n)/2))-
    2*Real.sin (e/2)*(a*Real.sin ((e+n)/2)+b*Real.cos ((e+n)/2))

theorem harmonic_half_difference (A B n : ℝ) :
    harmonic A B n-A=2*Real.sin (n/2)*(B*Real.cos (n/2)-A*Real.sin (n/2)) := by
  have hsn := Real.sin_two_mul (n/2)
  have hcn := Real.cos_two_mul (n/2)
  rw [show 2*(n/2)=n by ring] at hsn hcn
  rw [harmonic,hsn,hcn]
  linear_combination 2*A*(Real.sin_sq_add_cos_sq (n/2))

theorem outside_coefficient_identity (a b e n : ℝ) :
    oppositeSineCoefficient (-a) b e*Real.cos (n/2)-
      cosineCoefficient (-a) b e*Real.sin (n/2)=outsideBracket a b e n := by
  have hse := Real.sin_two_mul (e/2)
  have hce := Real.cos_two_mul (e/2)
  rw [show 2*(e/2)=e by ring] at hse hce
  have hm : (e+n)/2=e/2+n/2 := by ring
  dsimp [oppositeSineCoefficient,cosineCoefficient,outsideBracket]
  rw [hse,hce,hm,Real.sin_add,Real.cos_add]
  linear_combination 2*(a*Real.cos (n/2)-b*Real.sin (n/2))*
    (Real.sin_sq_add_cos_sq (e/2))

theorem outside_difference {a b e n : ℝ} (he : e∈Icc 0 frameCap)
    (hn : n∈Icc 0 (frameCap-e)) :
    pairDeficit a b n (-(e+n))-ehCharge (-a) b e=
      2*Real.sin (n/2)*outsideBracket a b e n := by
  have hp : pairDeficit a b n (-(e+n))=pairDeficit (-a) b (-n) (e+n) := by
    simpa only [neg_neg] using pair_negate_angles a b (-n) (e+n)
  rw [hp,opposite_harmonic_identity he hn]
  have hc : ehCharge (-a) b e=cosineCoefficient (-a) b e-1 := by
    dsimp [ehCharge,cosineCoefficient]
    ring
  rw [hc]
  have hh := harmonic_half_difference (cosineCoefficient (-a) b e)
    (oppositeSineCoefficient (-a) b e) n
  rw [outside_coefficient_identity] at hh
  linarith

theorem outside_bracket_nonneg {a b e n : ℝ} (he : e∈Icc 0 frameCap)
    (hn : n∈Icc 0 (frameCap-e))
    (hproj : a*Real.sin ((e+n)/2)+b*Real.cos ((e+n)/2)≤1/2) :
    0≤outsideBracket a b e n := by
  have he' : e∈Icc 0 (7/10:ℝ) := he
  have hn' : n∈Icc 0 (7/10-e:ℝ) := hn
  have hw : e/2∈Icc 0 (7/10/2:ℝ) := ⟨by linarith [he'.1],by linarith [he'.2]⟩
  have hm : (e+n)/2∈Icc 0 (7/10/2:ℝ) := ⟨by linarith [he'.1,hn'.1],by linarith [hn'.2]⟩
  have hc := half_frame_trig hw
  have ht := half_frame_trig hm
  have hfirst := mul_le_mul hc.1 ht.2.2.2 (by norm_num : (0:ℝ)≤47/80)
    (show 0≤Real.cos (e/2) by linarith)
  have hsecond := mul_le_mul_of_nonneg_left hproj (show 0≤2*Real.sin (e/2) by linarith [hc.2.1])
  dsimp [outsideBracket]
  linarith [hc.2.2.1]

theorem outside_minimum {a b e n : ℝ} (he : e∈Icc 0 frameCap)
    (hn : n∈Icc 0 (frameCap-e))
    (hproj : a*Real.sin ((e+n)/2)+b*Real.cos ((e+n)/2)≤1/2) :
    ehCharge (-a) b e≤pairDeficit a b n (-(e+n)) := by
  have he' : e∈Icc 0 (7/10:ℝ) := he
  have hn' : n∈Icc 0 (7/10-e:ℝ) := hn
  have hangle : n/2∈Icc 0 (7/10/2:ℝ) :=
    ⟨by linarith [hn'.1],by linarith [hn'.2,he'.1]⟩
  have hp := mul_nonneg (show 0≤2*Real.sin (n/2) by linarith [(half_frame_trig hangle).2.1])
    (outside_bracket_nonneg he hn hproj)
  rw [← outside_difference he hn] at hp
  linarith

theorem zero_tangent_outside {a e n : ℝ} (ha : 0≤a ∧ a≤283/200)
    (he : e∈Icc 0 frameCap) (hn : n∈Icc 0 (frameCap-e)) :
    ehCharge (-a) 0 e≤pairDeficit a 0 n (-(e+n)) := by
  apply outside_minimum he hn
  have he' : e∈Icc 0 (7/10:ℝ) := he
  have hn' : n∈Icc 0 (7/10-e:ℝ) := hn
  have hm : (e+n)/2∈Icc 0 (7/10/2:ℝ) :=
    ⟨by linarith [he'.1,hn'.1],by linarith [hn'.2]⟩
  have ht := half_frame_trig hm
  have hp := mul_le_mul ha.2 ht.2.2.1 ht.2.1 (by norm_num : (0:ℝ)≤283/200)
  linarith

theorem zero_tangent_minimum {a u v e : ℝ} (ha : 0≤a ∧ a≤283/200)
    (hu : |u|≤frameCap) (hv : |v|≤frameCap) (he : e∈Icc 0 frameCap)
    (hsum : u+v= -e) : ehCharge (-a) 0 e≤pairDeficit a 0 u v := by
  have hu' : |u|≤7/10 := hu
  have hv' : |v|≤7/10 := hv
  by_cases hu0 : u≤0
  · by_cases hv0 : v≤0
    · have hmu : -u∈Icc 0 e := ⟨by linarith,by linarith⟩
      have hh := negative_same_minimum (b := 0) ha.1 ⟨le_refl 0,by norm_num⟩ he hmu
      have h1 : -(-u)=u := by ring
      have h2 : -(e-(-u))=v := by linarith
      simpa only [h1,h2] using hh
    · have hn : v∈Icc 0 (frameCap-e) :=
        ⟨(lt_of_not_ge hv0).le,
          show v≤7/10-e by linarith [(neg_le_abs u).trans hu']⟩
      have hh := zero_tangent_outside ha he hn
      have heq : -(e+v)=u := by linarith
      rw [heq] at hh
      have hswap : pairDeficit a 0 v u=pairDeficit a 0 u v := by dsimp [pairDeficit]; ring
      rw [hswap] at hh
      exact hh
  · have hn : u∈Icc 0 (frameCap-e) :=
      ⟨(lt_of_not_ge hu0).le,show u≤7/10-e by linarith [(neg_le_abs v).trans hv']⟩
    have hh := zero_tangent_outside ha he hn
    have heq : -(e+u)=v := by linarith
    simpa only [heq] using hh

theorem good_sector_minimum {a b u v e : ℝ} (ha : 0≤a ∧ a≤283/200)
    (hb : 0≤b) (hu : |u|≤frameCap) (hv : |v|≤frameCap)
    (he : e∈Icc 0 frameCap) (hsum : u+v= -e) (hsector : u≤v) :
    ehCharge (-a) 0 e≤pairDeficit a b u v := by
  have hmin := zero_tangent_minimum ha hu hv he hsum
  have hu0 : u≤0 := by linarith [he.1]
  have hu' : |u|≤7/10 := hu
  have habs : |v|≤|u| := by
    rw [abs_of_nonpos hu0]
    exact abs_le.mpr ⟨by linarith,by linarith [he.1]⟩
  have hcos : Real.cos u≤Real.cos v := by
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg v)
      (by linarith [Real.pi_gt_three]) habs
    simpa only [Real.cos_abs] using hc
  have hp := mul_nonneg hb (sub_nonneg.mpr hcos)
  dsimp only [pairDeficit] at hmin ⊢
  linarith

theorem bad_sector_minimum {a b u v e H : ℝ} (ha : 0≤a)
    (hb : 0≤b ∧ b≤9/10) (hba : b≤a)
    (hH : H≤283/200) (hu : |u|≤frameCap) (hv : |v|≤frameCap)
    (he : e∈Icc 0 frameCap) (hsum : u+v= -e) (hsector : v≤u)
    (hEH : edgeWidth v≤H+a*Real.sin v-b*Real.cos v) :
    ehCharge (-a) b e≤pairDeficit a b u v := by
  have hv0 : v≤0 := by linarith [he.1]
  have ht : -v∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs v).trans hv⟩
  have hproj : a*Real.sin (-v)+b*Real.cos (-v)≤83/200 := by
    have hw := edgeWidth_ge_one v
    rw [Real.sin_neg,Real.cos_neg]
    linarith
  by_cases hu0 : u≤0
  · have hmu : -u∈Icc 0 e := ⟨by linarith,by linarith⟩
    have hh := negative_same_minimum ha hb he hmu
    have h1 : -(-u)=u := by ring
    have h2 : -(e-(-u))=v := by linarith
    simpa only [h1,h2] using hh
  · have hn : u∈Icc 0 (frameCap-e) :=
      ⟨(lt_of_not_ge hu0).le,by linarith [ht.2]⟩
    have hm : (e+u)/2∈Icc 0 frameCap :=
      ⟨by linarith [he.1,hn.1],by dsimp [frameCap] at *; linarith [hn.2]⟩
    have hp := projection_mono ha hba hm ht (by linarith [ht.1])
    have hh := outside_minimum he hn (show a*Real.sin ((e+u)/2)+
        b*Real.cos ((e+u)/2)≤1/2 by linarith)
    have heq : -(e+u)=v := by linarith
    simpa only [heq] using hh

theorem tangent_cut {a b t H : ℝ} (ha : 0≤a) (hba : b≤a)
    (hH : H≤283/200) (ht : t∈Icc 0 frameCap)
    (hEH : edgeWidth (-t)+a*Real.sin t+b*Real.cos t≤H) : b≤83/200 := by
  have hm := projection_mono ha hba
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) ht ht.1
  simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,zero_add] at hm
  linarith [edgeWidth_ge_one (-t)]

theorem endpoint_harmonic_mono :
    MonotoneOn (fun t : ℝ => (1/2)+K*Real.sin t+(4/5)*Real.cos t) (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · fun_prop
  · intro t _
    exact (((Real.hasDerivAt_sin t).const_mul K).const_add (1/2)).add
      ((Real.hasDerivAt_cos t).const_mul (4/5 : ℝ))
  · intro t ht
    have hh := transport_trig_coarse (Ioo_subset_Icc_self ht)
    dsimp [K]
    linarith

theorem large_tangent_cut {a b t H : ℝ} (ha : 447/800≤a)
    (hH : H≤283/200) (ht : t∈Icc (3/25) frameCap)
    (hEH : edgeWidth (-t)+a*Real.sin t+b*Real.cos t≤H) : b<3/10 := by
  by_contra! hb
  have ht' : t∈Icc 0 frameCap := ⟨by linarith [ht.1],ht.2⟩
  have htrig := transport_trig ht'
  have hsin := mul_le_mul_of_nonneg_right (show K≤a+1/2 by dsimp [K]; linarith) htrig.2.2.1
  have hcos := mul_le_mul_of_nonneg_right (show 4/5≤b+1/2 by linarith)
    (show 0≤Real.cos t by linarith [htrig.1])
  rw [edgeWidth_negative_formula ht'] at hEH
  have hm := endpoint_harmonic_mono
    (show (3/25 : ℝ)∈Icc 0 frameCap by norm_num [frameCap]) ht' ht.1
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤3/25 by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (3/25 : ℝ))
  norm_num at hs hc
  dsimp only [K] at hsin hm
  linarith

theorem canonical_negative_total {a b H D u v e : ℝ}
    (ha : 447/800≤a ∧ a≤283/200) (hb : 0≤b ∧ b≤9/10) (hba : b≤a)
    (hH : H≤283/200) (hD : D≤283/200)
    (hu : |u|≤frameCap) (hv : |v|≤frameCap)
    (he : e∈Icc 0 frameCap) (hsum : u+v= -e)
    (hDE : edgeWidth u≤D+a*Real.sin u+b*Real.cos u)
    (hEH : edgeWidth v≤H+a*Real.sin v-b*Real.cos v) :
    2+K*Real.sin e-(183/200)*(1-Real.cos e)≤H+D ∧
    (6/25≤e → 2+K*Real.sin e-(4/5)*(1-Real.cos e)≤H+D) := by
  have ha0 : 0≤a := by linarith [ha.1]
  have hsumBound : 2+pairDeficit a b u v≤H+D := by dsimp [pairDeficit]; linarith
  have ht := transport_trig he
  have hsin := mul_le_mul_of_nonneg_right (show K≤a+1/2 by dsimp [K]; linarith [ha.1]) ht.2.2.1
  have hloss := sub_nonneg.mpr ht.2.1
  rcases le_total u v with hsector | hsector
  · have hmin := good_sector_minimum ⟨ha0,ha.2⟩ hb.1 hu hv he hsum hsector
    dsimp [ehCharge] at hmin
    exact ⟨by nlinarith,by intro _; nlinarith⟩
  · have hmin := bad_sector_minimum ha0 hb hba hH hu hv he hsum hsector hEH
    have hv0 : v≤0 := by linarith [he.1]
    have hvt : -v∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs v).trans hv⟩
    have hcontact : edgeWidth (-(-v))+a*Real.sin (-v)+b*Real.cos (-v)≤H := by
      simp only [neg_neg,Real.sin_neg,Real.cos_neg]
      linarith
    have hcut := tangent_cut ha0 hba hH hvt hcontact
    have hsmall := mul_le_mul_of_nonneg_right (show 1/2+b≤(183/200 : ℝ) by linarith) hloss
    dsimp [ehCharge] at hmin
    refine ⟨by nlinarith,?_⟩
    intro hlarge
    have hvlarge : -v∈Icc (3/25) frameCap := ⟨by linarith,hvt.2⟩
    have hcut' := large_tangent_cut ha.1 hH hvlarge hcontact
    have hbig := mul_le_mul_of_nonneg_right (show 1/2+b≤(4/5 : ℝ) by linarith) hloss
    nlinarith

theorem actual_negative_total {q u v e : ℝ} {H D E : SignedPoint}
    (hHs : H.Sorted) (hDs : D.Sorted) (hEs : E.Sorted)
    (hHc : H.AvoidsCore) (hDc : D.AvoidsCore) (hEc : E.AvoidsCore)
    (hHcont : H.Contained q) (hDcont : D.Contained q) (hEcont : E.Contained q)
    (hq : q≤qCap) (hu : |u|≤frameCap) (hv : |v|≤frameCap)
    (he : e∈Icc 0 frameCap) (hsum : u+v= -e)
    (hDE : quarterFeasible D E u 3) (hEH : quarterFeasible E H v 1) :
    2+K*Real.sin e-(183/200)*(1-Real.cos e)≤H.a+D.a ∧
    (6/25≤e → 2+K*Real.sin e-(4/5)*(1-Real.cos e)≤H.a+D.a) := by
  have hH := SignedPoint.coordinate_bounds hHs hHc hHcont hq
  have hD := SignedPoint.coordinate_bounds hDs hDc hDcont hq
  have hE := SignedPoint.coordinate_bounds hEs hEc hEcont hq
  have hDE' : edgeWidth u≤D.a+E.a*Real.sin u-E.y*Real.cos u := by
    simpa [quarterFeasible,quarterProjection] using hDE
  have hEH' : edgeWidth v≤H.a+E.a*Real.sin v+E.y*Real.cos v := by
    simpa [quarterFeasible,quarterProjection] using hEH
  by_cases hy : E.y≤0
  · have hb : 0≤-E.y ∧ -E.y≤9/10 :=
      ⟨by linarith,by simpa [abs_of_nonpos hy] using hE.2.2.le⟩
    have hba : -E.y≤E.a := by simpa [abs_of_nonpos hy] using hEs.2
    exact canonical_negative_total ⟨hE.1.le,hE.2.1.le⟩ hb hba hH.2.1.le hD.2.1.le
      hu hv he hsum (by nlinarith only [hDE']) (by nlinarith only [hEH'])
  · have hy' : 0≤E.y := (lt_of_not_ge hy).le
    have hb : 0≤E.y ∧ E.y≤9/10 := ⟨hy',by simpa [abs_of_nonneg hy'] using hE.2.2.le⟩
    have hba : E.y≤E.a := by simpa [abs_of_nonneg hy'] using hEs.2
    have hh := canonical_negative_total ⟨hE.1.le,hE.2.1.le⟩ hb hba hD.2.1.le hH.2.1.le
      hv hu he (by linarith : v+u= -e) hEH' hDE'
    simpa only [add_comm D.a H.a] using hh

end SquaresInCircles.Eight.TableFree.ENegativePairMinimum
