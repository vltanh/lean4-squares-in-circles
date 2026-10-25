module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Frames.Ordinary.NegativeSlope
public import SquaresInCircles.Eight.Owners.GA.ClippedCircle
public import SquaresInCircles.Eight.Owners.GA.One.AngleFunctions
public import SquaresInCircles.Eight.Owners.GA.Sorted.Support

/-!
# Eight squares: the variable-coefficient D minorant at the unchanged original anchor

The baseline is the exact diagonal/full-circle support
at `(1,c)`.  The negative-angle comparison joins its two continuous support
formulas at equality.  The positive-angle comparison follows from an
explicit support point and the original circle inequality.
-/

section
/-!
## Variable D-support comparison on the whole negative-angle interval

The reference coefficient satisfies `.5 ≤ k ≤ .85`
and the actual transverse coefficient satisfies `k ≤ c ≤ 2`.  The
diagonal derivative and the full-circle derivative both dominate the
same ordinary H increment.  Only their exact equality switch is needed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PositiveTD
open Secondary PositiveAngularEnvelope PairNormCalculus
open OrdinaryAngleConcavity OrdinaryNegativeSlope

theorem reference_slope_zero {k : ℝ} (hk : k∈Icc (1/2) (17/20)) :
    Vd R k 1 0<1283/1000 := by
  have hk0 : 0<k := by linarith [hk.1]
  have hN := pairNorm_pos (q:=1) (t:=0) hk0 (by norm_num) (by norm_num [frameCap])
  have hN2 := pairNorm_sq (q:=1) (t:=0) hk0 (by norm_num) (by norm_num [frameCap])
  have hk2 := pow_le_pow_left₀ hk0.le hk.2 2
  have hRk : (R*k)^2=qCap*k^2 := by rw [mul_pow,radius_sq]
  have hreserve : qCap*(17/20:ℝ)^2<
      (1283/1000:ℝ)^2*(1+(17/20:ℝ)^2) := by norm_num [qCap]
  have hsq : (R*k)^2<(1283/1000:ℝ)^2*(pairNorm k 1 0)^2 := by
    norm_num [pairEnergy,pairProduct] at hN2
    rw [hRk]
    norm_num [qCap] at hreserve ⊢
    nlinarith
  have hcross : R*k<(1283/1000)*pairNorm k 1 0 := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg qCap) hk0.le]
  have he : Vd R k 1 0=R*k/pairNorm k 1 0 := by
    simp [Vd,mixedNDerivative,normD1,pairProduct]
    ring
  rw [he]
  exact (div_lt_iff₀ hN).2 hcross

theorem reference_slope_upper {k s : ℝ}
    (hk : k∈Icc (1/2) (17/20)) (hs : s∈Icc 0 frameCap) :
    Vd R k 1 s<1283/1000 := by
  have hanti := Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le
    (show 0<k by linarith [hk.1])
    (show k≤1 by linarith [hk.2]) (show 1≤2*k by linarith [hk.1])
  exact (hanti (by norm_num [frameCap]) hs hs.1).trans_lt (reference_slope_zero hk)

theorem diagonal_slope_lower {s : ℝ} (hs : s∈Icc 0 frameCap) :
    (1327/1000:ℝ)<(GlobalGA.Secondary.diagonal-1/2)*Real.sin s+(GlobalGA.Secondary.diagonal+1/2)*Real.cos s := by
  have hsin : (6442/10000:ℝ)≤Real.sin frameCap := by
    have h := cap_trig.1
    norm_num [Arithmetic.sin7,frameCap] at h
    linarith
  have hcos := (transport_trig (x:=frameCap) (by norm_num [frameCap])).1
  have hm₁ := mul_le_mul
    (show (3992/10000:ℝ)≤GlobalGA.Secondary.diagonal-1/2 by linarith [diagonal_bounds.1])
    hsin (by norm_num : (0:ℝ)≤6442/10000) (by linarith [diagonal_bounds.1])
  have hm₂ := mul_le_mul
    (show (13992/10000:ℝ)≤GlobalGA.Secondary.diagonal+1/2 by linarith [diagonal_bounds.1])
    hcos.le (by norm_num : (0:ℝ)≤7648/10000) (by linarith [diagonal_bounds.1])
  have h := trig_concave_gt (α:=0) (A:=GlobalGA.Secondary.diagonal-1/2) (B:=GlobalGA.Secondary.diagonal+1/2)
    (m:=(1327/1000:ℝ)) (by linarith [diagonal_bounds.1])
    (by linarith [diagonal_bounds.1]) (by norm_num : (0:ℝ)≤0)
    (show frameCap≤Real.pi/2 by norm_num [frameCap]; linarith [Real.pi_gt_three]) hs
    (by norm_num; linarith [diagonal_bounds.1]) (by nlinarith)
  simpa using h

theorem negative_norm_fraction_mono {k c s : ℝ}
    (hk : k∈Icc (1/2) (17/20)) (hc : c∈Icc k 2)
    (hs : s∈Icc 0 frameCap) :
    k/pairNorm k 1 (-s)≤c/pairNorm c 1 (-s) := by
  have hk0 : 0<k := by linarith [hk.1]
  have hc0 : 0<c := hk0.trans_le hc.1
  have habs : |-s|≤frameCap := by rw [abs_neg,abs_of_nonneg hs.1]; exact hs.2
  have hNk := pairNorm_pos hk0 (by norm_num : (0:ℝ)<1) habs
  have hNc := pairNorm_pos hc0 (by norm_num : (0:ℝ)<1) habs
  have hNk2 := pairNorm_sq hk0 (by norm_num : (0:ℝ)<1) habs
  have hNc2 := pairNorm_sq hc0 (by norm_num : (0:ℝ)<1) habs
  have hsU : Real.sin s≤7/10 := (Real.sin_le hs.1).trans (by simpa [frameCap] using hs.2)
  have hsin := mul_le_mul_of_nonneg_left hsU (mul_nonneg hc0.le hk0.le)
  have hkU := mul_nonneg (sub_nonneg.mpr hk.2) hc0.le
  have hcU := mul_nonneg (sub_nonneg.mpr hc.2) hk0.le
  have hfactor : 0≤c+k-2*c*k*Real.sin s := by nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr hc.1) hfactor
  have hid : (c*pairNorm k 1 (-s))^2-(k*pairNorm c 1 (-s))^2=
      (c-k)*(c+k-2*c*k*Real.sin s) := by
    rw [mul_pow,mul_pow,hNk2,hNc2]
    simp only [pairEnergy,pairProduct,Real.sin_neg]
    ring
  have hcross : k*pairNorm c 1 (-s)≤c*pairNorm k 1 (-s) := by
    rw [← hid] at hprod
    nlinarith [mul_nonneg hk0.le hNc.le,mul_nonneg hc0.le hNk.le]
  exact (div_le_div_iff₀ hNk hNc).2 hcross

theorem negative_full_slope_nonneg {k c s : ℝ}
    (hk : k∈Icc (1/2) (17/20)) (hc : c∈Icc k 2)
    (hs : s∈Icc 0 frameCap) : 0≤Vd R c 1 s-Vd R k 1 s := by
  have hcos : 0≤Real.cos s := by linarith [(transport_trig hs).1]
  have h := mul_le_mul_of_nonneg_left (negative_norm_fraction_mono hk hc hs)
    (mul_nonneg (Real.sqrt_nonneg qCap) hcos)
  have he (p : ℝ) : Vd R p 1 s=
      -Real.sin s+(R*Real.cos s)*(p/pairNorm p 1 (-s)) := by
    simp [Vd,mixedNDerivative,normD1,pairProduct]
    ring
  rw [he,he]
  linarith

def negativeDiagonalResidual (k c s : ℝ) : ℝ :=
  (Real.cos s+Real.sin s-1)/2-GlobalGA.Secondary.diagonal*(Real.cos s+c-Real.sin s)+
    clippedSupport 1 c-V R k 1 s

def negativeFullResidual (k c s : ℝ) : ℝ :=
  V R c 1 s+clippedSupport 1 c-fullSupport 1 c-V R k 1 s

theorem negativeDiagonalResidual_hasDerivAt {k c s : ℝ}
    (hk : 0<k) (hs : s∈Icc 0 frameCap) :
    HasDerivAt (negativeDiagonalResidual k c)
      ((GlobalGA.Secondary.diagonal-1/2)*Real.sin s+(GlobalGA.Secondary.diagonal+1/2)*Real.cos s-Vd R k 1 s) s := by
  have hfirst := (((Real.hasDerivAt_cos s).fun_add (Real.hasDerivAt_sin s)).sub_const 1).div_const 2
  have hsecond := (((Real.hasDerivAt_cos s).add_const c).fun_sub
    (Real.hasDerivAt_sin s)).const_mul GlobalGA.Secondary.diagonal
  have h := ((hfirst.fun_sub hsecond).add_const (clippedSupport 1 c)).fun_sub
    (V_hasDerivAt (R:=R) (q:=1) hk (by norm_num) hs)
  exact h.congr_deriv (by ring)

theorem negativeFullResidual_hasDerivAt {k c s : ℝ}
    (hk : 0<k) (hc : 0<c) (hs : s∈Icc 0 frameCap) :
    HasDerivAt (negativeFullResidual k c) (Vd R c 1 s-Vd R k 1 s) s := by
  exact (((V_hasDerivAt hc (by norm_num) hs).add_const
    (clippedSupport 1 c)).sub_const (fullSupport 1 c)).sub
      (V_hasDerivAt hk (by norm_num) hs)

theorem negativeDiagonalResidual_monotone {k c : ℝ}
    (hk : k∈Icc (1/2) (17/20)) :
    MonotoneOn (negativeDiagonalResidual k c) (Icc 0 frameCap) := by
  have hk0 : 0<k := by linarith [hk.1]
  apply monoOn_of_hasDeriv_nonneg
  · intro s hs
    exact (negativeDiagonalResidual_hasDerivAt hk0 hs).continuousAt.continuousWithinAt
  · intro s hs
    exact negativeDiagonalResidual_hasDerivAt hk0 (Ioo_subset_Icc_self hs)
  · intro s hs
    have hsd := diagonal_slope_lower (Ioo_subset_Icc_self hs)
    have hsv := reference_slope_upper hk (Ioo_subset_Icc_self hs)
    linarith

theorem negativeFullResidual_monotone {k c : ℝ}
    (hk : k∈Icc (1/2) (17/20)) (hc : c∈Icc k 2) :
    MonotoneOn (negativeFullResidual k c) (Icc 0 frameCap) := by
  have hk0 : 0<k := by linarith [hk.1]
  have hc0 : 0<c := hk0.trans_le hc.1
  apply monoOn_of_hasDeriv_nonneg
  · intro s hs
    exact (negativeFullResidual_hasDerivAt hk0 hc0 hs).continuousAt.continuousWithinAt
  · intro s hs
    exact negativeFullResidual_hasDerivAt hk0 hc0 (Ioo_subset_Icc_self hs)
  · intro s hs
    exact negative_full_slope_nonneg hk hc (Ioo_subset_Icc_self hs)

end SquaresInCircles.Eight.GlobalGA.PositiveTD
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PositiveTD
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def dSupportIncrement (c x : ℝ) : ℝ :=
  edgeWidth x-1-clippedSupport (Real.cos x) (c+Real.sin x)+clippedSupport 1 c

def actualDIncrement (c x : ℝ) (P : SignedPoint) : ℝ :=
  edgeWidth x-1-(Real.cos x*P.a+(c+Real.sin x)*P.y)+clippedSupport 1 c

@[simp] theorem dSupportIncrement_zero (c : ℝ) : dSupportIncrement c 0=0 := by
  simp [dSupportIncrement,edgeWidth,pairWidth]

theorem negative_diagonal_identity {k c s : ℝ} (hs : s∈Icc 0 frameCap) :
    negativeDiagonalResidual k c s=
      edgeWidth (-s)-1-diagonalSupport (Real.cos s) (c-Real.sin s)+
        clippedSupport 1 c-V R k 1 s := by
  rw [edgeWidth_negative_formula hs]
  dsimp [negativeDiagonalResidual,diagonalSupport]
  ring

theorem negative_full_identity {k c s : ℝ} (hs : s∈Icc 0 frameCap) :
    negativeFullResidual k c s=
      edgeWidth (-s)-1-fullSupport (Real.cos s) (c-Real.sin s)+
        clippedSupport 1 c-V R k 1 s := by
  have hnorm : Real.sqrt ((Real.cos s)^2+(c-Real.sin s)^2)=pairNorm c 1 (-s) := by
    simpa only [Real.cos_neg,Real.sin_neg,one_mul,← sub_eq_add_neg] using
      one_force_norm c 1 (-s)
  have hsupport : fullSupport (Real.cos s) (c-Real.sin s)=
      R*pairNorm c 1 (-s)-(Real.cos s+c-Real.sin s)/2 := by
    dsimp [fullSupport]
    rw [hnorm]
    ring
  rw [edgeWidth_negative_formula hs,hsupport]
  dsimp [negativeFullResidual]
  rw [fullSupport_pair c 1]
  dsimp [V]
  ring

theorem negative_switch_identity {k c s : ℝ} (hs : s∈Icc 0 frameCap) :
    (if Real.cos s-(c-Real.sin s)≤0 then negativeDiagonalResidual k c s
      else negativeFullResidual k c s)=dSupportIncrement c (-s)-V R k 1 s := by
  by_cases h : Real.cos s≤c-Real.sin s
  · have h' : Real.cos s-(c-Real.sin s)≤0 := sub_nonpos.mpr h
    simp only [h',↓reduceIte]
    rw [negative_diagonal_identity hs,dSupportIncrement]
    simp only [Real.cos_neg,Real.sin_neg,← sub_eq_add_neg,clippedSupport,h,↓reduceIte]
  · have h' : ¬Real.cos s-(c-Real.sin s)≤0 := by simpa only [sub_nonpos] using h
    simp only [h',↓reduceIte]
    rw [negative_full_identity hs,dSupportIncrement]
    simp only [Real.cos_neg,Real.sin_neg,← sub_eq_add_neg,clippedSupport,h,↓reduceIte]

theorem negative_D_support_minorant {k c s : ℝ}
    (hk : k∈Icc (1/2) (17/20)) (hc : c∈Icc k 2)
    (hs : s∈Icc 0 frameCap) : V R k 1 s≤dSupportIncrement c (-s) := by
  have hmono := monotone_continuous_switch
    (e:=fun x => Real.cos x-(c-Real.sin x))
    (by fun_prop) (negativeDiagonalResidual_monotone hk)
    (negativeFullResidual_monotone hk hc)
    (fun x hx he => by
      rw [negative_diagonal_identity hx,negative_full_identity hx]
      have heq : Real.cos x=c-Real.sin x := by linarith
      have hsum : 0≤Real.cos x+(c-Real.sin x) := by
        rw [← heq]
        linarith [(transport_trig hx).1]
      rw [full_at_diagonal heq hsum])
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have h := hmono hz hs hs.1
  simp only at h
  rw [negative_switch_identity hz,negative_switch_identity hs] at h
  simp only [neg_zero,dSupportIncrement_zero,V_zero,sub_zero] at h
  linarith

theorem positive_D_support_minorant {c s : ℝ}
    (hc : 1/2≤c) (hs : s∈Icc 0 frameCap) :
    -(GlobalGA.Secondary.diagonal-1/2)*s≤dSupportIncrement c s := by
  obtain ⟨hcos,_,hsin,_,_⟩ := transport_trig hs
  have hg : 0<c+Real.sin s := by linarith
  have hsum : 0≤Real.cos s+(c+Real.sin s) := by linarith
  let K := clippedPoint hsum hg
  have hbase := raw_clipped_support (f:=1) (g:=c) K.circle.le K.sorted
    (by linarith [K.corners_nonneg.1,K.corners_nonneg.2]) (by linarith)
  have hfirst := mul_nonneg
    (show 0≤K.a-1/2 by linarith [K.primary_lower,diagonal_bounds.1])
    (sub_nonneg.mpr (Real.cos_le_one s))
  have hsecond := mul_le_mul_of_nonneg_right K.tangent_upper hsin
  have hthird := mul_le_mul_of_nonneg_left (Real.sin_le hs.1)
    (show 0≤GlobalGA.Secondary.diagonal-1/2 by linarith [diagonal_bounds.1])
  rw [dSupportIncrement,edgeWidth_positive_formula hs,K.supports]
  nlinarith

theorem actual_D_increment_lower {q c x : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : 0≤P.y) (hc : P.Contained q) (hq : q≤qCap)
    (hcoef : 1/2≤c) (hx : |x|≤frameCap) :
    dSupportIncrement c x≤actualDIncrement c x P := by
  have ht := small_angle hx
  have hsum : 0≤Real.cos x+(c+Real.sin x) := by
    have hsin := (abs_le.mp ht.2).1
    norm_num [frameCap] at ht hsin
    linarith [ht.1]
  have hsupport := actual_clipped_support hs hy hc hq hsum
  dsimp [dSupportIncrement,actualDIncrement]
  linarith

/-- The fourth ordinary block has a linear positive part and the actual
ordinary H negative part.  Both arguments are the original signed error. -/
theorem actual_D_signed_minorant {q k c x : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : 0≤P.y) (hc : P.Contained q) (hq : q≤qCap)
    (hk : k∈Icc (1/2) (17/20)) (hcoef : c∈Icc k 2)
    (hx : |x|≤frameCap) :
    -(GlobalGA.Secondary.diagonal-1/2)*positivePart x+V R k 1 (negativePart x)≤actualDIncrement c x P := by
  have hc0 : 1/2≤c := hk.1.trans hcoef.1
  have hactual := actual_D_increment_lower hs hy hc hq hc0 hx
  by_cases hp : 0≤x
  · have h := positive_D_support_minorant hc0
      ⟨hp,by simpa only [abs_of_nonneg hp] using hx⟩
    simpa [positivePart,negativePart,max_eq_left hp,
      max_eq_right (by linarith : -x≤0)] using h.trans hactual
  · have hn : x≤0 := (lt_of_not_ge hp).le
    have hs' : -x∈Icc 0 frameCap :=
      ⟨neg_nonneg.mpr hn,(neg_le_abs x).trans hx⟩
    have h := negative_D_support_minorant hk hcoef hs'
    simp only [neg_neg] at h
    simpa [positivePart,negativePart,max_eq_right hn,
      max_eq_left (neg_nonneg.mpr hn)] using h.trans hactual

end SquaresInCircles.Eight.GlobalGA.PositiveTD
end
end
end
