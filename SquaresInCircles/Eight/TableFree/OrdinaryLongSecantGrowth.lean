module

public import SquaresInCircles.Eight.TableFree.OrdinaryShortSecantGrowth
public import SquaresInCircles.Eight.TableFree.NegativeEOneAngle

/-!
# Negative-angle growth for the full removed-primary interval

Uncompiled source. The fixed ratio 2/3 has the two exact reserves
.6744 and .25823. They compensate the largest possible E secant on
the entire interval 0≤s≤h, using a single concave affine-cosine product.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.OrdinaryLongSecantGrowth
open PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope VaryingBFunctions
open PositiveStressCoefficients NegativeEOneAngle

theorem cap_trig :
    (644217687/1000000000 : ℝ)≤Real.sin frameCap ∧
      Real.sin frameCap≤644217688/1000000000 ∧
      (764842187/1000000000 : ℝ)≤Real.cos frameCap := by
  have hsL := HighOrderTaylor.S11_le_sin (show 0≤frameCap by norm_num [frameCap])
  have hsU := Arithmetic.sin_le_sin9 (show 0≤frameCap by norm_num [frameCap])
  have hcL := Arithmetic.cos10_le_cos (show 0≤frameCap by norm_num [frameCap])
  norm_num [frameCap,HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.cos10] at hsL hsU hcL ⊢
  exact ⟨by linarith,by linarith,by linarith⟩

theorem endpoint_slope :
    (843/1250 : ℝ)<Vd (Real.sqrt qCap) (2/3) 1 frameCap := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hN := root_pos (2/3) (sin_mem hh)
  have hN2 := root_sq (2/3) (sin_mem hh)
  have hNupper : root (2/3) (Real.sin frameCap)≤76517157/100000000 := by
    nlinarith [cap_trig.1]
  have hR := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hR0 := Real.sqrt_nonneg qCap
  have hRlower : (19787875/10000000 : ℝ)≤Real.sqrt qCap := by
    norm_num [qCap] at hR
    nlinarith
  have hleft : ((843/1250 : ℝ)+Real.sin frameCap)*root (2/3) (Real.sin frameCap)≤
      (843/1250+644217688/1000000000)*(76517157/100000000) :=
    mul_le_mul (add_le_add_left cap_trig.2.1 _) hNupper hN.le (by norm_num)
  have hright : (19787875/10000000 : ℝ)*(2/3)*(764842187/1000000000)≤
      Real.sqrt qCap*(2/3)*Real.cos frameCap :=
    mul_le_mul (mul_le_mul_of_nonneg_right hRlower (by norm_num)) cap_trig.2.2
      (by norm_num) (by positivity)
  have hreserve : ((843/1250 : ℝ)+644217688/1000000000)*(76517157/100000000)<
      (19787875/10000000)*(2/3)*(764842187/1000000000) := by norm_num
  have hcross := hleft.trans_lt (hreserve.trans_le hright)
  have hdiv := (lt_div_iff₀ hN).2 hcross
  rw [Vd_normalized (by norm_num : (0:ℝ)<1)]
  simp only [div_one,one_mul]
  linarith

theorem fixed_second_upper {t : ℝ} (ht : t∈Icc 0 frameCap) :
    curvature (Real.sqrt qCap) (2/3) 1 (-t)-Real.cos t≤ -(25823/100000) := by
  let N := pairNorm (2/3) 1 0
  have hN : 0<N := pairNorm_pos (by norm_num) (by norm_num) (by norm_num [frameCap])
  have hN2 : N^2=13/9 := by
    have hh := pairNorm_sq (p := (2/3:ℝ)) (q := 1) (t := 0)
      (by norm_num) (by norm_num) (by norm_num [frameCap])
    simpa [N,pairEnergy,pairProduct] using hh
  have hN6 : (N^3)^2=(13/9 : ℝ)^3 := by
    calc (N^3)^2=(N^2)^3 := by ring
         _=_ := by rw [hN2]
  have hR := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hR0 := Real.sqrt_nonneg qCap
  have hcross : Real.sqrt qCap*(4/9)<(50661/100000)*N^3 := by
    have hreserve : qCap*(4/9 : ℝ)^2<(50661/100000)^2*(13/9)^3 := by norm_num [qCap]
    have hright0 : 0<(50661/100000 : ℝ)*N^3 := by positivity
    have hright2 : ((50661/100000 : ℝ)*N^3)^2=(50661/100000)^2*(13/9)^3 := by
      rw [mul_pow,hN6]
    have hleft2 : (Real.sqrt qCap*(4/9))^2=qCap*(4/9 : ℝ)^2 := by rw [mul_pow,hR]
    nlinarith
  have hzero : curvatureZero (Real.sqrt qCap) (2/3) 1<50661/100000 := by
    change Real.sqrt qCap*(4/9)/N^3<50661/100000
    exact (div_lt_iff₀ (pow_pos hN 3)).2 hcross
  have hcurv := curvature_negative_upper (Real.sqrt_nonneg qCap)
    (by norm_num : (0:ℝ)<2/3) (by norm_num : (0:ℝ)<1)
    (show -t∈Icc (-frameCap) 0 from ⟨by linarith [ht.2],by linarith [ht.1]⟩)
  have hcosmono := Real.cos_le_cos_of_nonneg_of_le_pi ht.1
    (by norm_num [frameCap]; linarith [Real.pi_gt_three]) ht.2
  have hcos : (19121/25000 : ℝ)<Real.cos t := by linarith [cap_trig.2.2]
  linarith

theorem fixed_slope_lower {t : ℝ} (ht : t∈Icc 0 frameCap) :
    843/1250+(25823/100000)*(frameCap-t)<Vd (Real.sqrt qCap) (2/3) 1 t := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have h := derivative_reserve
    (f := fun x => -Vd (Real.sqrt qCap) (2/3) 1 x)
    (df := fun x => -(curvature (Real.sqrt qCap) (2/3) 1 (-x)-Real.cos x))
    (k := (25823/100000 : ℝ))
    (fun x hx => (Vd_hasDerivAt (by norm_num : (0:ℝ)<2/3)
      (by norm_num : (0:ℝ)<1) hx).neg.continuousAt.continuousWithinAt)
    (fun x hx => (Vd_hasDerivAt (by norm_num : (0:ℝ)<2/3)
      (by norm_num : (0:ℝ)<1) (Ioo_subset_Icc_self hx)).neg)
    (fun x hx => by linarith [fixed_second_upper (Ioo_subset_Icc_self hx)]) ht hh ht.2
  linarith [endpoint_slope]

theorem shortened_slope {p q s t : ℝ} (hp : 0<p) (hpq : p≤q)
    (hratio : (2/3)*q≤p) (hs : 0≤s) (ht : t∈Icc 0 (frameCap-s)) :
    (843/1250+(25823/100000)*s)*q≤Vd (Real.sqrt qCap) p q t := by
  have hq := hp.trans_le hpq
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by linarith [ht.2]⟩
  have hfrac := normalized_fraction_mono (by norm_num : (0:ℝ)≤2/3)
    ((le_div_iff₀ hq).2 hratio) ((div_le_one hq).2 hpq) (sin_mem ht')
  have hcoef : 0≤Real.sqrt qCap*Real.cos t := mul_nonneg (Real.sqrt_nonneg _)
    (by linarith [(transport_trig ht').1])
  have hmul := mul_le_mul_of_nonneg_left hfrac hcoef
  have hbase := fixed_slope_lower ht'
  rw [Vd_normalized (by norm_num : (0:ℝ)<1)] at hbase
  simp only [div_one,one_mul] at hbase
  have hnormal : 843/1250+(25823/100000)*s≤ -Real.sin t+
      Real.sqrt qCap*(p/q)*Real.cos t/root (p/q) (Real.sin t) := by
    nlinarith only [hbase,hmul,ht.2]
  rw [Vd_normalized hq]
  nlinarith only [mul_le_mul_of_nonneg_left hnormal hq.le]

theorem affine_cos_concave {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun t => (a+b*t)*Real.cos t) := by
  apply concave_of_deriv2
    (f' := fun t => b*Real.cos t-(a+b*t)*Real.sin t)
    (f'' := fun t => -2*b*Real.sin t-(a+b*t)*Real.cos t)
  · intro t _
    convert (((hasDerivAt_id t).const_mul b).const_add a).mul
      (Real.hasDerivAt_cos t) using 1 <;> ring
  · intro t _
    convert ((Real.hasDerivAt_cos t).const_mul b).sub
      ((((hasDerivAt_id t).const_mul b).const_add a).mul
        (Real.hasDerivAt_sin t)) using 1 <;> ring
  · intro t ht
    have hs := (transport_trig ht).2.2.1
    have hc : 0≤Real.cos t := by linarith [(transport_trig ht).1]
    have h1 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hb) hs
    have h2 := mul_nonneg (add_nonneg ha (mul_nonneg hb ht.1)) hc
    linarith

theorem secant_chord {s : ℝ} (hs : s∈Icc 0 frameCap) :
    1/Real.cos s≤1+(11/25)*s := by
  have hc := affine_cos_concave (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤11/25)
  have hmin := hc.min_le_of_mem_Icc (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hs
  have hend : 1≤(1+(11/25)*frameCap)*Real.cos frameCap := by
    have hcos := cos_lower_six (show 0≤frameCap by norm_num [frameCap])
    norm_num [frameCap] at hcos ⊢
    linarith
  have hval : 1≤(1+(11/25)*s)*Real.cos s := by
    simpa [min_eq_left hend] using hmin
  exact (div_le_iff₀ (by linarith [(transport_trig hs).1] : 0<Real.cos s)).2 hval

theorem secant_compensation {s : ℝ} (hs : s∈Icc 0 frameCap) :
    gamma s≤k*(843/1250+(25823/100000)*s) := by
  have hc := affine_cos_concave
    (a := k*(843/1250)) (b := k*(25823/100000)) (by norm_num [k]) (by norm_num [k])
  have hmin := hc.min_le_of_mem_Icc (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hs
  have hzero : (109/200 : ℝ)*(2069/2000)≤k*(843/1250) := by norm_num [k]
  have hend : (109/200 : ℝ)*(2069/2000)≤
      (k*(843/1250)+k*(25823/100000)*frameCap)*Real.cos frameCap := by
    have hh := cap_trig.2.2
    norm_num [frameCap,k] at hh ⊢
    linarith
  have hval : (109/200 : ℝ)*(2069/2000)≤
      (k*(843/1250)+k*(25823/100000)*s)*Real.cos s := by
    have hz : (109/200 : ℝ)*(2069/2000)≤
        (k*(843/1250)+k*(25823/100000)*0)*Real.cos 0 := by simpa using hzero
    exact (le_min hz hend).trans hmin
  dsimp [gamma]
  apply (div_le_iff₀ (by linarith [(transport_trig hs).1] : 0<Real.cos s)).2
  nlinarith

theorem growth {p q s t u : ℝ} (hp : 0<p) (hpq : p≤q)
    (hratio : (2/3)*q≤p) (hq : k≤q) (hs : s∈Icc 0 frameCap)
    (ht : t∈Icc 0 (frameCap-s)) (hu : u∈Icc 0 (frameCap-s)) (htu : t≤u) :
    gamma s*(u-t)≤V (Real.sqrt qCap) p q u-V (Real.sqrt qCap) p q t := by
  have hq0 := hp.trans_le hpq
  have hmem {x : ℝ} (hx : x∈Icc 0 (frameCap-s)) : x∈Icc 0 frameCap :=
    ⟨hx.1,by linarith [hx.2,hs.1]⟩
  apply derivative_reserve
    (fun x hx => (V_hasDerivAt hp hq0 (hmem hx)).continuousAt.continuousWithinAt)
    (fun x hx => V_hasDerivAt hp hq0 (hmem (Ioo_subset_Icc_self hx)))
    (fun x hx => ?_) ht hu htu
  have hbase := shortened_slope hp hpq hratio hs.1 (Ioo_subset_Icc_self hx)
  have hmul := mul_le_mul_of_nonneg_left hq
    (show 0≤843/1250+(25823/100000)*s by linarith [hs.1])
  have hcomp := secant_compensation hs
  nlinarith

end SquaresInCircles.Eight.TableFree.OrdinaryLongSecantGrowth
