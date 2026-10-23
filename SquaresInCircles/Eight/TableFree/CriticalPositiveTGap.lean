module

public import SquaresInCircles.Eight.TableFree.CriticalPositiveTCoefficients

/-!
# The canonical B chord on the positive-T critical strip

Uncompiled transcription of (28). The fixed ratio is .61, the scale
is .8402, and the chord has slope .75 on the whole interval [0,.16].
The endpoint comparison uses positive radical squaring; monotonicity
of the exact derivative extends it to every smaller left endpoint.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalPositiveTGap
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope
open OrdinaryNegativeEnvelope VaryingBFunctions VaryingBComparison SoleLowGap

def ratio : ℝ := 61/100
def scale : ℝ := 4201/5000

theorem short_right_slope {R : ℝ} (hR : 0≤R) (hQL : qLow≤R^2) :
    3/4<Vd R ratio 1 (4/25) := by
  have hs : (4/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hN := root_pos ratio (sin_mem hs)
  have hN2 := root_sq ratio (sin_mem hs)
  have hsn := (transport_trig hs).2.2.1
  have hNu : root ratio (Real.sin (4/25))≤6/5 := by dsimp [ratio] at *; nlinarith
  have hsu := Real.sin_le (show (0:ℝ)≤4/25 by norm_num)
  have hco := SoleBalancedCoefficients.cosine_quadratic (show (0:ℝ)≤4/25 by norm_num)
  have hrad := SoleAngleGrowth.radius_lower hR hQL
  have hCpos : 0<Real.cos (4/25:ℝ) := by linarith
  have hnum := mul_lt_mul_of_pos_right hrad hCpos
  have hcross : (3/4+Real.sin (4/25))*root ratio (Real.sin (4/25))<
      R*ratio*Real.cos (4/25) := by
    have hm := mul_le_mul hNu (show 3/4+Real.sin (4/25)≤91/100 by linarith)
      (by linarith : 0≤3/4+Real.sin (4/25)) (by norm_num : (0:ℝ)≤6/5)
    dsimp [ratio] at *
    nlinarith
  have hdiv := (lt_div_iff₀ hN).2 hcross
  rw [Vd_normalized (by norm_num : (0:ℝ)<1)]
  simpa only [div_one,one_mul] using (show 3/4< -Real.sin (4/25)+
    R*ratio*Real.cos (4/25)/root ratio (Real.sin (4/25)) by linarith)

theorem right_gap {R : ℝ} (hR : 0≤R) (hQL : qLow≤R^2) :
    (3/4)*(frameCap-4/25)<V R ratio 1 frameCap-V R ratio 1 (4/25) := by
  have hs : (4/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hX0 : 0≤pairNorm ratio 1 (-4/25) := Real.sqrt_nonneg _
  have hY0 : 0≤pairNorm ratio 1 (-frameCap) := Real.sqrt_nonneg _
  have hX2 := negative_norm_square (by norm_num [ratio] : 0<ratio) (by norm_num : (0:ℝ)<1) hs
  have hY2 := negative_norm_square (by norm_num [ratio] : 0<ratio) (by norm_num : (0:ℝ)<1) hh
  have hsu := sin_upper_five (show (0:ℝ)≤4/25 by norm_num)
  have hX : (2713/2500:ℝ)<pairNorm ratio 1 (-4/25) := by
    dsimp [ratio] at hX2
    norm_num at hsu
    nlinarith
  have hY : pairNorm ratio 1 (-frameCap)<76563/100000 := by
    dsimp [ratio] at hY2
    nlinarith [cap_sin_lower]
  have hgap : (31957/100000:ℝ)<pairNorm ratio 1 (-4/25)-pairNorm ratio 1 (-frameCap) := by
    linarith
  have hrad := SoleAngleGrowth.radius_lower hR hQL
  have hmul := mul_lt_mul hrad hgap (by norm_num : (0:ℝ)≤31957/100000) (by linarith : 0<R)
  have hcosh := (transport_trig hh).1
  have hcost := cos_upper_four (show (0:ℝ)≤4/25 by norm_num)
  norm_num at hcost
  dsimp [V,frameCap]
  nlinarith

theorem fixed_gap {R t : ℝ} (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈Icc 0 (4/25:ℝ)) :
    (3/4)*(frameCap-t)<V R ratio 1 frameCap-V R ratio 1 t := by
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap] at *; linarith [ht.2]⟩
  have hr : (4/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hanti := Vd_antitone hR hQU (by norm_num [ratio] : 0<ratio)
    (by norm_num [ratio] : ratio≤1) (by norm_num [ratio] : (1:ℝ)≤2*ratio)
  have hlow (s : ℝ) (hs : s∈Icc 0 (4/25:ℝ)) : 3/4≤Vd R ratio 1 s :=
    (short_right_slope hR hQL).le.trans
      (hanti ⟨hs.1,hs.2.trans hr.2⟩ hr hs.2)
  have hd := derivative_reserve
    (f := V R ratio 1) (df := Vd R ratio 1) (k := 3/4)
    (fun s hs => (V_hasDerivAt (by norm_num [ratio]) (by norm_num)
      ⟨hs.1,hs.2.trans hr.2⟩).continuousAt.continuousWithinAt)
    (fun s hs => V_hasDerivAt (by norm_num [ratio]) (by norm_num)
      ⟨hs.1.le,hs.2.le.trans hr.2⟩)
    (fun s hs => hlow s (Ioo_subset_Icc_self hs)) ht (by norm_num) ht.2
  have he := right_gap hR hQL
  linarith

theorem derivative_ratio {R p q s : ℝ} (hR : 0≤R) (hq : 0<q)
    (hpq : p≤q) (hratio : ratio*q≤p) (hs : s∈Icc 0 frameCap) :
    q*Vd R ratio 1 s≤Vd R p q s := by
  have hrlo : ratio≤p/q := (le_div_iff₀ hq).2 hratio
  have hrhi : p/q≤1 := (div_le_one hq).2 hpq
  have hf := normalized_fraction_mono (by norm_num [ratio] : 0≤ratio) hrlo hrhi (sin_mem hs)
  have hc : 0≤Real.cos s := by linarith [(transport_trig hs).1]
  have hm := mul_le_mul_of_nonneg_left hf (mul_nonneg hR hc)
  have hm' := mul_le_mul_of_nonneg_left hm hq.le
  rw [Vd_normalized hq,Vd_normalized (by norm_num : (0:ℝ)<1)]
  simp only [div_one,one_mul]
  nlinarith

theorem scaled_gap {R p q t : ℝ} (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hq : scale≤q) (hpq : p≤q) (hratio : ratio*q≤p) (ht : t∈Icc 0 (4/25:ℝ)) :
    scale*(3/4)*(frameCap-t)<V R p q frameCap-V R p q t := by
  have hq0 : 0<q := by dsimp [scale] at hq; linarith
  have hp : 0<p := by dsimp [ratio] at hratio; nlinarith
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by dsimp [frameCap]; linarith [ht.2]⟩
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hd := derivative_reserve
    (f := fun s => V R p q s-q*V R ratio 1 s)
    (df := fun s => Vd R p q s-q*Vd R ratio 1 s) (k := 0)
    (fun s hs => ((V_hasDerivAt hp hq0 hs).sub
      ((V_hasDerivAt (by norm_num [ratio]) (by norm_num) hs).const_mul q)).continuousAt.continuousWithinAt)
    (fun s hs => (V_hasDerivAt hp hq0 (Ioo_subset_Icc_self hs)).sub
      ((V_hasDerivAt (by norm_num [ratio]) (by norm_num) (Ioo_subset_Icc_self hs)).const_mul q))
    (fun s hs => sub_nonneg.mpr (derivative_ratio hR hq0 hpq hratio (Ioo_subset_Icc_self hs)))
    ht' hh ht'.2
  have hbase := mul_lt_mul_of_pos_left (fixed_gap hR hQL hQU ht) hq0
  have hlen : 0≤(3/4)*(frameCap-t) := by dsimp [frameCap]; nlinarith [ht.2]
  have hm := mul_le_mul_of_nonneg_right hq hlen
  nlinarith

end SquaresInCircles.Eight.TableFree.CriticalPositiveTGap
