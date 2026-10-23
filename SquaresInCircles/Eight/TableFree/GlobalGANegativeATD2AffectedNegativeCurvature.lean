module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2AffectedNegativeCurves

/-!
# Curvature through the affected AB coefficient transition

Uncompiled transcription of (64)--(65). On the lower-secant branch the
non-norm curvature is below `.225` and the norm curvature exceeds `.348`.
The exact coefficient equality is the only split, and its derivative
jump has the direction prescribed in the hand proof.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.AffectedNegativeCurvature
open Candidate Secondary SecantCoordinate SecantBounds AffectedNegativeCurves

theorem small_z_trig {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    (31/32:ℝ)≤Real.cos z ∧ Real.sin z∈Icc 0 (1/4:ℝ) := by
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hc := cos_lower_six hz.1
  have ht : 0≤z^4/24-z^6/720 := by
    have hh := mul_nonneg (pow_nonneg hz.1 4) (show 0≤30-z^2 by nlinarith)
    nlinarith only [hh]
  have hframe : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  exact ⟨by linarith,⟨(transport_trig hframe).2.2.1,(Real.sin_le_self hz.1).trans hz.2⟩⟩

theorem nonnorm_upper {r z x : ℝ} (hr : 1≤r)
    (hz : z∈Icc 0 (1/4:ℝ)) (hx : x∈Icc 0 (32/125:ℝ)) :
    1/(radical 1 x)^3+
      r*(-Real.cos z*(1-2*x^2)-3*x*Real.sin z)/(radical 1 x)^5<(9/40:ℝ) := by
  have ht := small_z_trig hz
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hW := radical_positive (A:=1) (x:=x) (by norm_num)
  have hW2 := radical_square (A:=1) (x:=x) (by norm_num)
  have hW1 : 1≤radical 1 x := by nlinarith [sq_nonneg x]
  have hW5 : 1≤(radical 1 x)^5 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hW1 5
  have hfactor : 0≤1-2*x^2 := by nlinarith
  have hcos := mul_le_mul_of_nonneg_right ht.1 hfactor
  have hsin := mul_nonneg (show 0≤3*x by linarith [hx.1]) ht.2.1
  have hbr : -Real.cos z*(1-2*x^2)-3*x*Real.sin z≤-(31/32)*(1-2*x^2) := by
    linarith
  have hbr0 : -Real.cos z*(1-2*x^2)-3*x*Real.sin z≤0 := by
    nlinarith only [hbr,hfactor]
  have hscale := mul_le_mul_of_nonpos_right hr hbr0
  have hn : (radical 1 x)^2+
      r*(-Real.cos z*(1-2*x^2)-3*x*Real.sin z)<(9/40)*(radical 1 x)^5 := by
    nlinarith only [hW2,hx2,hbr,hscale,hW5]
  have he : 1/(radical 1 x)^3+
      r*(-Real.cos z*(1-2*x^2)-3*x*Real.sin z)/(radical 1 x)^5=
      ((radical 1 x)^2+r*(-Real.cos z*(1-2*x^2)-3*x*Real.sin z))/(radical 1 x)^5 := by
    field_simp [hW.ne']
    ring
  rw [he]
  exact (div_lt_iff₀ (pow_pos hW 5)).2 hn

theorem norm_lower {r z x : ℝ} (hr : r∈Icc 1 (129/125:ℝ))
    (hz : z∈Icc 0 (1/4:ℝ)) (hx : x∈Icc 0 (Real.tan z))
    (hw : radical 1 x≤r) : (87/250:ℝ)<R*AffectedNorm.second r z x := by
  have ht := small_z_trig hz
  have hc : 0<Real.cos z := by linarith [ht.1]
  have hW := radical_positive (A:=1) (x:=x) (by norm_num)
  have hW2 := radical_square (A:=1) (x:=x) (by norm_num)
  have hv : (371/500:ℝ)≤1-r*Real.sin z := by
    have hp := mul_le_mul hr.2 ht.2.2 ht.2.1 (by norm_num : (0:ℝ)≤129/125)
    linarith
  have hn := AffectedNorm.norm_pos (x:=x) (show 0<1-r*Real.sin z by linarith)
  have hnx := AffectedNorm.norm_sq_expanded r z x
  have hxc : x*Real.cos z≤Real.sin z := by
    have hh := mul_le_mul_of_nonneg_right hx.2 hc.le
    have he := (AffectedNorm.tan_identity hc).1
    linarith
  have hterm := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤2*r by linarith [hr.1]) (sub_nonpos.mpr hxc)
  have hw2 := pow_le_pow_left₀ hW.le hw 2
  have hr2 := pow_le_pow_left₀ (by linarith [hr.1] : 0≤r) hr.2 2
  have hn2 : (AffectedNorm.norm r z x)^2≤2*(129/125:ℝ)^2 := by
    nlinarith only [hnx,hterm,hw2,hW2,hr2]
  have hn6 := pow_le_pow_left₀ (sq_nonneg (AffectedNorm.norm r z x)) hn2 3
  have hn3 : (AffectedNorm.norm r z x)^3<(311/100:ℝ) := by
    have he : ((AffectedNorm.norm r z x)^2)^3=((AffectedNorm.norm r z x)^3)^2 := by ring
    rw [he] at hn6
    norm_num at hn6
    nlinarith [pow_nonneg hn.le 3]
  have hv2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤371/500) hv 2
  have hR := Curvature.radius_bounds.1
  have hprod := mul_lt_mul_of_pos_right hR (sq_pos_of_pos (show 0<1-r*Real.sin z by linarith))
  have hscale := mul_le_mul_of_nonneg_left hv2 (by norm_num : (0:ℝ)≤197/100)
  dsimp [AffectedNorm.second]
  rw [←mul_div_assoc]
  apply (lt_div_iff₀ (pow_pos hn 3)).2
  nlinarith only [hn3,hprod,hscale]

theorem lower_curvature {r z x : ℝ} (hr : r∈Icc 1 (129/125:ℝ))
    (hz : z∈Icc 0 (1/4:ℝ)) (hx : x∈Icc 0 (Real.tan z))
    (hw : radical 1 x≤r) : lowerSecond r z x<-(123/1000:ℝ) := by
  have ht := tan_monotone
    (show z∈Icc 0 frameCap from ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩)
    (show (1/4:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz.2
  have hx' : x∈Icc 0 (32/125:ℝ) := ⟨hx.1,by linarith [hx.2,tan_GA_cut]⟩
  have hnon := nonnorm_upper hr.1 hz hx'
  have hnorm := norm_lower hr hz hx hw
  dsimp [lowerSecond]
  linarith

def switch (r : ℝ) : ℝ := Real.sqrt (r^2-1)

theorem switch_data {r : ℝ} (hr : 1≤r) :
    0≤switch r ∧ (switch r)^2=r^2-1 ∧ radical 1 (switch r)=r := by
  have hr0 : 0≤r := by linarith
  have hh : 0≤r^2-1 := by nlinarith
  have hs := Real.sq_sqrt hh
  have hW := radical_positive (A:=1) (x:=switch r) (by norm_num)
  have hW2 := radical_square (A:=1) (x:=switch r) (by norm_num)
  exact ⟨Real.sqrt_nonneg _,hs,by dsimp [switch] at hW2; nlinarith⟩

theorem switch_order {r x : ℝ} (hr : 1≤r) (hx : 0≤x) :
    x≤switch r ↔ radical 1 x≤r := by
  obtain ⟨hs,hs2,he⟩ := switch_data hr
  have hW := radical_positive (A:=1) (x:=x) (by norm_num)
  have hW2 := radical_square (A:=1) (x:=x) (by norm_num)
  constructor <;> intro hh <;> nlinarith

theorem lower_concave {r z a : ℝ} (hr : r∈Icc 1 (129/125:ℝ))
    (hz : z∈Icc 0 (1/4:ℝ)) (ha : a∈Icc 0 (Real.tan z)) (has : a≤switch r) :
    ConcaveOn ℝ (Icc 0 a) (lower r z) := by
  have hzframe : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hv := AffectedNorm.second_coordinate_pos
    (show r∈Icc (0:ℝ) (71/50:ℝ) from ⟨by linarith [hr.1],by linarith [hr.2]⟩) hzframe
  apply concave_of_deriv2 (fun x _ => lower_hasDerivAt hv)
    (fun x _ => lowerFirst_hasDerivAt hv)
  intro x hx
  have hx' : x∈Icc 0 (Real.tan z) := ⟨hx.1,hx.2.trans ha.2⟩
  exact (lower_curvature hr hz hx' ((switch_order hr.1 hx.1).1 (hx.2.trans has))).le.trans
    (by norm_num)

theorem minimum_concave {r z : ℝ} (hr : r∈Icc 0 (129/125:ℝ))
    (hz : z∈Icc 0 frameCap) (hlarge : 1<r→z≤1/4) :
    ConcaveOn ℝ (Icc 0 (Real.tan z))
      (fun x => min (upper r z x) (lower r z x)) := by
  have hv := AffectedNorm.second_coordinate_pos
    (show r∈Icc (0:ℝ) (71/50:ℝ) from ⟨hr.1,by linarith [hr.2]⟩) hz
  have hu := upper_concave (a:=0) (b:=Real.tan z) hv
  have htan := tan_nonnegative hz
  by_cases hr1 : r≤1
  · have he (x : ℝ) (hx : x∈Icc 0 (Real.tan z)) :
        min (upper r z x) (lower r z x)=upper r z x := by
      have hw := radical_positive (A:=1) (x:=x) (by norm_num)
      have hw2 := radical_square (A:=1) (x:=x) (by norm_num)
      have hwr : r≤radical 1 x := by nlinarith [sq_nonneg x]
      have hh := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hwr)
        (sub_nonpos.mpr (cosine_le_one z x))
      rw [←branch_difference] at hh
      exact min_eq_left (by linarith)
    refine ⟨convex_Icc _ _,?_⟩
    intro x hx y hy a b ha hb hab
    rw [he x hx,he y hy,he _ (hu.1 hx hy ha hb hab)]
    exact hu.2 hx hy ha hb hab
  have hr' : r∈Icc 1 (129/125:ℝ) := ⟨(lt_of_not_ge hr1).le,hr.2⟩
  have hz' : z∈Icc 0 (1/4:ℝ) := ⟨hz.1,hlarge (lt_of_not_ge hr1)⟩
  have hc := switch_data hr'.1
  have he (x : ℝ) (hx : x∈Icc 0 (Real.tan z)) :
      min (upper r z x) (lower r z x)=
        if x≤switch r then lower r z x else upper r z x := by
    by_cases hxc : x≤switch r
    · rw [if_pos hxc]
      have hw := (switch_order hr'.1 hx.1).1 hxc
      have hh := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hw)
        (sub_nonpos.mpr (cosine_le_one z x))
      rw [←branch_difference] at hh
      exact min_eq_right (by linarith)
    · rw [if_neg hxc]
      have hw : r≤radical 1 x := by
        have hn : ¬radical 1 x≤r := by
          intro hh
          exact hxc ((switch_order hr'.1 hx.1).2 hh)
        exact (lt_of_not_ge hn).le
      have hh := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hw)
        (sub_nonpos.mpr (cosine_le_one z x))
      rw [←branch_difference] at hh
      exact min_eq_left (by linarith)
  have hconc : ConcaveOn ℝ (Icc 0 (Real.tan z))
      (fun x => if x≤switch r then lower r z x else upper r z x) := by
    by_cases hcut : switch r≤Real.tan z
    · apply AffectedJoin.downward ⟨hc.1,hcut⟩
        (lower_concave hr' hz' ⟨hc.1,hcut⟩ le_rfl)
        (upper_concave hv)
      · have hd := branch_difference r z (switch r)
        rw [hc.2.2,sub_self,zero_mul] at hd
        linarith
      · exact lower_hasDerivAt hv
      · exact upper_hasDerivAt hv
      · exact downward_derivative hc.1 hc.2.2
    · have hl := lower_concave hr' hz' ⟨htan,le_rfl⟩ (le_of_not_ge hcut)
      refine ⟨convex_Icc _ _,?_⟩
      intro x hx y hy a b ha hb hab
      have hxy := hl.1 hx hy ha hb hab
      simp only [if_pos (hx.2.trans (le_of_not_ge hcut)),
        if_pos (hy.2.trans (le_of_not_ge hcut)),
        if_pos (hxy.2.trans (le_of_not_ge hcut))]
      exact hl.2 hx hy ha hb hab
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  rw [he x hx,he y hy,he _ (hconc.1 hx hy ha hb hab)]
  exact hconc.2 hx hy ha hb hab

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.AffectedNegativeCurvature
