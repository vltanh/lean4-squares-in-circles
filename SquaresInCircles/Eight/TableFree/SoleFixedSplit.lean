module

public import SquaresInCircles.Eight.TableFree.SoleResiduals

/-!
# A continuous fixed-total split before anchor maximization

Uncompiled source. The four anchor coordinates and all ordinary angles
are held fixed. The primary total is split over its complete interval.
The two endpoints are scalar evaluations, not asserted packing motions.
The high-family expression keeps the original unsigned E coordinates.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SoleFixedSplit
open SoleResiduals

def harmonic (a b c d t x : ℝ) : ℝ :=
  a*Real.cos x+b*Real.sin x+c*Real.cos (t-x)+d*Real.sin (t-x)

def harmonicDeriv (a b c d t x : ℝ) : ℝ :=
  -a*Real.sin x+b*Real.cos x+c*Real.sin (t-x)-d*Real.cos (t-x)

theorem harmonic_hasDerivAt (a b c d t x : ℝ) :
    HasDerivAt (harmonic a b c d t) (harmonicDeriv a b c d t x) x := by
  have he := (hasDerivAt_const x t).sub (hasDerivAt_id x)
  convert ((((Real.hasDerivAt_cos x).const_mul a).add
    ((Real.hasDerivAt_sin x).const_mul b)).add
    ((he.cos).const_mul c)).add ((he.sin).const_mul d) using 1 <;>
    dsimp [harmonic,harmonicDeriv] <;> ring

theorem harmonicDeriv_hasDerivAt (a b c d t x : ℝ) :
    HasDerivAt (harmonicDeriv a b c d t) (-harmonic a b c d t x) x := by
  have he := (hasDerivAt_const x t).sub (hasDerivAt_id x)
  convert ((((Real.hasDerivAt_sin x).const_mul (-a)).add
    ((Real.hasDerivAt_cos x).const_mul b)).add
    ((he.sin).const_mul c)).sub ((he.cos).const_mul d) using 1 <;>
    dsimp [harmonic,harmonicDeriv] <;> ring

theorem harmonic_sine_interpolation (a b c d t x : ℝ) :
    harmonic a b c d t x*Real.sin t=
      harmonic a b c d t 0*Real.sin (t-x)+
        harmonic a b c d t t*Real.sin x := by
  simp only [harmonic,Real.sin_zero,Real.cos_zero,sub_zero,sub_self,
    Real.sin_sub,Real.cos_sub]
  linear_combination c*Real.sin x*(Real.sin_sq_add_cos_sq t)

theorem harmonic_endpoint_upper {a b c d t x κ : ℝ}
    (ht : t∈Icc 0 frameCap) (hx : x∈Icc 0 t) (hκ : 0≤κ)
    (h0 : harmonic a b c d t 0≤-κ) (h1 : harmonic a b c d t t≤-κ) :
    harmonic a b c d t x≤-κ := by
  by_cases ht0 : t=0
  · have hx0 : x=0 := by linarith [hx.1,hx.2]
    simpa [ht0,hx0] using h0
  have htpos : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hst : 0<Real.sin t := Real.sin_pos_of_pos_of_lt_pi htpos
    (by dsimp [frameCap] at ht; linarith [ht.2,Real.pi_gt_three])
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans ht.2⟩
  have he : t-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [ht.2,hx.1]⟩
  have hsx := (transport_trig hx').2.2.1
  have hse := (transport_trig he).2.2.1
  have hsadd : Real.sin t≤Real.sin x+Real.sin (t-x) := by
    have hi : Real.sin t=Real.sin x*Real.cos (t-x)+Real.cos x*Real.sin (t-x) := by
      have harg : x+(t-x)=t := by ring
      simpa only [harg] using Real.sin_add x (t-x)
    have h1 := mul_le_mul_of_nonneg_left (Real.cos_le_one (t-x)) hsx
    have h2 := mul_le_mul_of_nonneg_right (Real.cos_le_one x) hse
    linarith
  have hb0 := mul_le_mul_of_nonneg_right h0 hse
  have hb1 := mul_le_mul_of_nonneg_right h1 hsx
  have hb2 := mul_le_mul_of_nonpos_left hsadd (neg_nonpos.mpr hκ)
  have hi := harmonic_sine_interpolation a b c d t x
  nlinarith

theorem short_trig {x : ℝ} (hx : x∈Icc 0 (7/20 : ℝ)) :
    9393/10000<Real.cos x ∧ 0≤Real.sin x ∧ Real.sin x<343/1000 := by
  have hh := trig_bracket (l := 0) (u := (7/20 : ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) hx
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_gt_three])
  refine ⟨?_,hs,?_⟩ <;> norm_num at hh ⊢ <;> linarith [hh.2.1,hh.2.2.1]

theorem low_middle_harmonic {k t x : ℝ} (hk : 431/500≤k)
    (ht : t∈Icc 0 (7/20 : ℝ)) (hx : x∈Icc 0 t) :
    harmonic (-(87/200)*k) ((239/250)*k) (-(17/200)) (2411/2000) t x≤-1/25 := by
  obtain ⟨hc,hs0,hs⟩ := short_trig ht
  have hk0 : 0≤k := by linarith
  apply harmonic_endpoint_upper ⟨ht.1,by dsimp [frameCap]; linarith [ht.2]⟩ hx (by norm_num)
  · simp only [harmonic,Real.cos_zero,Real.sin_zero,sub_zero,mul_one,mul_zero,add_zero,zero_add]
    nlinarith
  · have hb : -(87/200)*Real.cos t+(239/250)*Real.sin t≤0 := by linarith
    have hm := mul_nonpos_of_nonneg_of_nonpos hk0 hb
    simp only [harmonic,sub_self,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero]
    nlinarith

theorem high_harmonic {k t x : ℝ} (hk : k∈Icc (1003/1000 : ℝ) (101/100))
    (ht : t∈Icc 0 frameCap) (hx : x∈Icc 0 t) :
    harmonic (-(87/200)*k) ((961/1000)*k) (-(1/2)) (183/200) t x≤-1/5 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig ht
  have hcos := mul_le_mul_of_nonneg_right hk.1 (show 0≤Real.cos t by linarith)
  have hsin := mul_le_mul_of_nonneg_right hk.2 hs0
  have hcos' := mul_le_mul_of_nonneg_left hc.le (by norm_num : (0:ℝ)≤1003/1000)
  have hsin' := mul_le_mul_of_nonneg_left hs.le (by norm_num : (0:ℝ)≤101/100)
  apply harmonic_endpoint_upper ht hx (by norm_num)
  · simp only [harmonic,Real.cos_zero,Real.sin_zero,sub_zero,mul_one,mul_zero,add_zero,zero_add]
    nlinarith [hk.1]
  · simp only [harmonic,sub_self,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero]
    nlinarith

def tilted (K MH MX k g v σG σE t x : ℝ) : ℝ :=
  K+k/2+1/2+harmonic (k*MH+k/2) (k*g*MH+k/2-k*σG)
    (MX+1/2) (v*MX+1/2-σE) t x

theorem tilted_formula (K MH MX k g v σG σE t x : ℝ) :
    tilted K MH MX k g v σG σE t x=
      K+k*(Real.cos x+g*Real.sin x)*MH+
      k*(1+Real.cos x+Real.sin x)/2-k*σG*Real.sin x+
      (Real.cos (t-x)+v*Real.sin (t-x))*MX+
      (1+Real.cos (t-x)+Real.sin (t-x))/2-σE*Real.sin (t-x) := by
  dsimp [tilted,harmonic]
  ring

theorem tilted_curvature {MH MX k g v σG σE t x : ℝ}
    (hMH : -(13/200 : ℝ)≤MH) (hMX : -(83/200 : ℝ)≤MX)
    (hk : 431/500≤k) (hg : g∈Icc 0 (8/25 : ℝ)) (hv : 0≤v)
    (hG : σG-1/2≤187/200) (hE : σE-1/2+(83/200)*v≤2411/2000)
    (ht : t∈Icc 0 (7/20 : ℝ)) (hx : x∈Icc 0 t) :
    -harmonic (k*MH+k/2) (k*g*MH+k/2-k*σG)
      (MX+1/2) (v*MX+1/2-σE) t x≤-1/25 := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,by dsimp [frameCap]; linarith [hx.2,ht.2]⟩
  have he : t-x∈Icc 0 frameCap :=
    ⟨by linarith [hx.2],by dsimp [frameCap]; linarith [ht.2,hx.1]⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hx'
  obtain ⟨hce,hce1,hse0,hse,hsce⟩ := transport_trig he
  have hk0 : 0≤k := by linarith
  have hn : 0≤k*(Real.cos x+g*Real.sin x) :=
    mul_nonneg hk0 (by nlinarith [mul_nonneg hg.1 hs0])
  have hp : 0≤Real.cos (t-x)+v*Real.sin (t-x) := by
    nlinarith [mul_nonneg hv hse0]
  have hmH := mul_le_mul_of_nonneg_right hMH hn
  have hmX := mul_le_mul_of_nonneg_right hMX hp
  have hcoef : σG-1/2+(13/200)*g≤239/250 := by linarith [hg.2]
  have hcoefG := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hk0 hs0)
  have hcoefE := mul_le_mul_of_nonneg_right hE hse0
  have hmajor : -harmonic (k*MH+k/2) (k*g*MH+k/2-k*σG)
      (MX+1/2) (v*MX+1/2-σE) t x≤
      harmonic (-(87/200)*k) ((239/250)*k) (-(17/200)) (2411/2000) t x := by
    dsimp [harmonic]
    nlinarith
  exact hmajor.trans (low_middle_harmonic hk ht hx)

theorem tilted_concave {K MH MX k g v σG σE t : ℝ}
    (hMH : -(13/200 : ℝ)≤MH) (hMX : -(83/200 : ℝ)≤MX)
    (hk : 431/500≤k) (hg : g∈Icc 0 (8/25 : ℝ)) (hv : 0≤v)
    (hG : σG-1/2≤187/200) (hE : σE-1/2+(83/200)*v≤2411/2000)
    (ht : t∈Icc 0 (7/20 : ℝ)) :
    ConcaveOn ℝ (Icc 0 t) (tilted K MH MX k g v σG σE t) := by
  apply concave_of_deriv2
    (f' := harmonicDeriv (k*MH+k/2) (k*g*MH+k/2-k*σG)
      (MX+1/2) (v*MX+1/2-σE) t)
    (f'' := fun x => -harmonic (k*MH+k/2) (k*g*MH+k/2-k*σG)
      (MX+1/2) (v*MX+1/2-σE) t x)
  · intro x hx
    exact (harmonic_hasDerivAt _ _ _ _ _ _).const_add _
  · intro x hx
    exact harmonicDeriv_hasDerivAt _ _ _ _ _ _
  · intro x hx
    exact (tilted_curvature hMH hMX hk hg hv hG hE ht hx).trans (by norm_num)

def high (K MH k g σG a b t x : ℝ) : ℝ :=
  K+k/2+1/2-b+harmonic (k*MH+k/2) (k*g*MH+k/2-k*σG)
    (1/2+b) (1/2-a) t x

theorem high_formula (K MH k g σG a b t x : ℝ) :
    high K MH k g σG a b t x=
      K+k*(Real.cos x+g*Real.sin x)*MH+
      k*(1+Real.cos x+Real.sin x)/2-k*σG*Real.sin x+
      (1+Real.cos (t-x)+Real.sin (t-x))/2-
        a*Real.sin (t-x)-b*(1-Real.cos (t-x)) := by
  dsimp [high,harmonic]
  ring

theorem high_curvature {MH k g σG a b t x : ℝ}
    (hMH : -(13/200 : ℝ)≤MH) (hk : k∈Icc (1003/1000 : ℝ) (101/100))
    (hg : g∈Icc 0 (163/500 : ℝ)) (hG : σG-1/2≤187/200)
    (ha : a≤283/200) (hb : 0≤b) (ht : t∈Icc 0 frameCap) (hx : x∈Icc 0 t) :
    -harmonic (k*MH+k/2) (k*g*MH+k/2-k*σG)
      (1/2+b) (1/2-a) t x≤-1/5 := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans ht.2⟩
  have he : t-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [ht.2,hx.1]⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hx'
  obtain ⟨hce,hce1,hse0,hse,hsce⟩ := transport_trig he
  have hk0 : 0≤k := by linarith [hk.1]
  have hn : 0≤k*(Real.cos x+g*Real.sin x) :=
    mul_nonneg hk0 (by nlinarith [mul_nonneg hg.1 hs0])
  have hmH := mul_le_mul_of_nonneg_right hMH hn
  have hcoef : σG-1/2+(13/200)*g≤961/1000 := by linarith [hg.2]
  have hcoefG := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hk0 hs0)
  have hcoefE := mul_le_mul_of_nonneg_right ha hse0
  have hminor := mul_nonneg hb (show 0≤Real.cos (t-x) by linarith)
  have hmajor : -harmonic (k*MH+k/2) (k*g*MH+k/2-k*σG)
      (1/2+b) (1/2-a) t x≤
      harmonic (-(87/200)*k) ((961/1000)*k) (-(1/2)) (183/200) t x := by
    dsimp [harmonic]
    nlinarith
  exact hmajor.trans (high_harmonic hk ht hx)

theorem high_concave {K MH k g σG a b t : ℝ}
    (hMH : -(13/200 : ℝ)≤MH) (hk : k∈Icc (1003/1000 : ℝ) (101/100))
    (hg : g∈Icc 0 (163/500 : ℝ)) (hG : σG-1/2≤187/200)
    (ha : a≤283/200) (hb : 0≤b) (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 t) (high K MH k g σG a b t) := by
  apply concave_of_deriv2
    (f' := harmonicDeriv (k*MH+k/2) (k*g*MH+k/2-k*σG) (1/2+b) (1/2-a) t)
    (f'' := fun x => -harmonic (k*MH+k/2) (k*g*MH+k/2-k*σG) (1/2+b) (1/2-a) t x)
  · intro x hx
    exact (harmonic_hasDerivAt _ _ _ _ _ _).const_add _
  · intro x hx
    exact harmonicDeriv_hasDerivAt _ _ _ _ _ _
  · intro x hx
    exact (high_curvature hMH hk hg hG ha hb ht hx).trans (by norm_num)

end SquaresInCircles.Eight.TableFree.SoleFixedSplit
