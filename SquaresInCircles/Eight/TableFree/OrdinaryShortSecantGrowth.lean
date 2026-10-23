module

public import SquaresInCircles.Eight.TableFree.OrdinaryNegativeSlope
public import SquaresInCircles.Eight.TableFree.PositiveStressCoefficients

/-!
# Negative-angle growth after a short negative primary is removed

Uncompiled source draft. The available negative angle is at most `h-s`.
The fixed ratio `2/3` gains at least `s/4` in its derivative on this
shortened interval. This compensates the actual secant enlargement of
the other block's coefficient for every `0 ≤ s ≤ .3`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.OrdinaryShortSecantGrowth
open PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope VaryingBFunctions
open PositiveStressCoefficients

theorem fixed_second_upper {t : ℝ} (ht : t∈Icc 0 frameCap) :
    curvature (Real.sqrt qCap) (2/3) 1 (-t)-Real.cos t≤ -(1/4) := by
  have hN := pairNorm_pos (p := (2/3 : ℝ)) (q := 1) (t := 0)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  have hN2 := pairNorm_sq (p := (2/3 : ℝ)) (q := 1) (t := 0)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  norm_num [pairEnergy,pairProduct] at hN2
  have hNlo : (6/5 : ℝ)≤pairNorm (2/3) 1 0 := by nlinarith
  have hN3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤6/5) hNlo 3
  have hR2 := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hR : Real.sqrt qCap≤2 := by norm_num [qCap] at hR2; nlinarith
  have hC : curvatureZero (Real.sqrt qCap) (2/3) 1≤125/243 := by
    dsimp [curvatureZero,pairProduct]
    apply (div_le_iff₀ (pow_pos hN 3)).2
    nlinarith
  have hneg := curvature_negative_upper (Real.sqrt_nonneg qCap)
    (by norm_num : (0:ℝ)<2/3) (by norm_num : (0:ℝ)<1)
    (show -t∈Icc (-frameCap) 0 from ⟨by linarith [ht.2],by linarith [ht.1]⟩)
  linarith [(transport_trig ht).1]

theorem fixed_slope_lower {t : ℝ} (ht : t∈Icc 0 frameCap) :
    2/3+(frameCap-t)/4<Vd (Real.sqrt qCap) (2/3) 1 t := by
  have hh : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have h := derivative_reserve
    (f := fun x => -Vd (Real.sqrt qCap) (2/3) 1 x)
    (df := fun x => -(curvature (Real.sqrt qCap) (2/3) 1 (-x)-Real.cos x))
    (k := (1/4 : ℝ))
    (fun x hx => (Vd_hasDerivAt (by norm_num : (0:ℝ)<2/3)
      (by norm_num : (0:ℝ)<1) hx).neg.continuousAt.continuousWithinAt)
    (fun x hx => (Vd_hasDerivAt (by norm_num : (0:ℝ)<2/3)
      (by norm_num : (0:ℝ)<1) (Ioo_subset_Icc_self hx)).neg)
    (fun x hx => by linarith [fixed_second_upper (Ioo_subset_Icc_self hx)]) ht hh ht.2
  have hend := endpoint_normalized_slope
  have he : Vd (Real.sqrt qCap) (2/3) 1 frameCap=
      -Real.sin frameCap+Real.sqrt qCap*(2/3)*Real.cos frameCap/
        root (2/3) (Real.sin frameCap) := by
    rw [Vd_normalized (by norm_num : (0:ℝ)<1)]
    simp
  rw [← he] at hend
  linarith

theorem shortened_slope {p q s t : ℝ} (hp : 0<p) (hpq : p≤q)
    (hratio : (2/3)*q≤p) (hs : 0≤s) (ht : t∈Icc 0 (frameCap-s)) :
    (2/3+s/4)*q≤Vd (Real.sqrt qCap) p q t := by
  have hq := hp.trans_le hpq
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by linarith [ht.2]⟩
  have hrlo : 2/3≤p/q := (le_div_iff₀ hq).2 hratio
  have hrhi : p/q≤1 := (div_le_one hq).2 hpq
  have hfrac := normalized_fraction_mono (by norm_num : (0:ℝ)≤2/3)
    hrlo hrhi (sin_mem ht')
  have hcoef : 0≤Real.sqrt qCap*Real.cos t :=
    mul_nonneg (Real.sqrt_nonneg _) (by linarith [(transport_trig ht').1])
  have hmul := mul_le_mul_of_nonneg_left hfrac hcoef
  have hbase := fixed_slope_lower ht'
  rw [Vd_normalized (by norm_num : (0:ℝ)<1)] at hbase
  simp only [div_one,one_mul] at hbase
  have hnormal : 2/3+s/4≤ -Real.sin t+
      Real.sqrt qCap*(p/q)*Real.cos t/root (p/q) (Real.sin t) := by
    nlinarith only [hbase,hmul,ht.2]
  rw [Vd_normalized hq]
  nlinarith only [mul_le_mul_of_nonneg_left hnormal hq.le]

theorem shortened_growth {p q s t u : ℝ} (hp : 0<p) (hpq : p≤q)
    (hratio : (2/3)*q≤p) (hs : 0≤s)
    (ht : t∈Icc 0 (frameCap-s)) (hu : u∈Icc 0 (frameCap-s)) (htu : t≤u) :
    (2/3+s/4)*q*(u-t)≤V (Real.sqrt qCap) p q u-V (Real.sqrt qCap) p q t := by
  have hq := hp.trans_le hpq
  have hmem {x : ℝ} (hx : x∈Icc 0 (frameCap-s)) : x∈Icc 0 frameCap :=
    ⟨hx.1,by linarith [hx.2]⟩
  exact derivative_reserve
    (fun x hx => (V_hasDerivAt hp hq (hmem hx)).continuousAt.continuousWithinAt)
    (fun x hx => V_hasDerivAt hp hq (hmem (Ioo_subset_Icc_self hx)))
    (fun x hx => shortened_slope hp hpq hratio hs (Ioo_subset_Icc_self hx)) ht hu htu

theorem secant_compensation {s : ℝ} (hs : s∈Icc 0 (3/10)) :
    (109/200)*(2069/2000)/Real.cos s≤k*(2/3+s/4) := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hc : 0<Real.cos s := by linarith [(transport_trig hs').1]
  have hc2 := cos_lower_two hs.1
  have hs2 : s^2≤(3/10)*s := by nlinarith [hs.1,hs.2]
  have hs3 : s^3≤(9/100)*s := by nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hs2)]
  have hcoef : 0≤k*(2/3+s/4) := by dsimp [k]; positivity
  have hmul := mul_le_mul_of_nonneg_left hc2 hcoef
  apply (div_le_iff₀ hc).2
  norm_num [k] at *
  nlinarith

end SquaresInCircles.Eight.TableFree.OrdinaryShortSecantGrowth
