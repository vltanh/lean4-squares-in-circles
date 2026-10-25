module

public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LargeEndpoints
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveSplit

/-!
# Eight squares: concavity of the complete positive-BT3 split

In the large case the D coefficient
function has derivative above -21/1000. Its compensating term is
paid by the exact two-angle cosine bound, giving the stated negative
curvature reserve. The actual A support branches join with matching
value and first derivative, including the closed transition tie.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3.Analytic
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open NonnegativeTotals SplitConcavityTools
open TwoPositive

theorem cosine_sum {t a : ℝ} (ht : t∈Icc 0 frameCap) (ha : a∈Icc 0 t) :
    (1103/625:ℝ)<Real.cos a+Real.cos (t-a) := by
  have hh := ActualOrdinaryBlocks.concave_zero_subadditive
    ActualOrdinaryBlocks.cosine_increment_concave (by simp)
    ha.1 (show 0≤t-a by linarith [ha.2]) (show a+(t-a)≤frameCap by linarith [ht.2])
  rw [show a+(t-a)=t by ring] at hh
  linarith [(transport_trig ht).1]

theorem strong_rest_curvature {m l t a d : ℝ}
    (hl : 0<l) (hmLow : (9/10)*l≤ m) (hmHigh : m≤(11/10)*l)
    (ht : t∈Icc 0 frameCap) (ha : a∈Icc 0 t)
    (hd : d≤-Real.cos a/2+(23/25)*Real.sin a) :
    TwoPositive.Split.smoothDD m t a+l*d< -(268/3125)*l := by
  have hm : 0 < m := by linarith
  have hdom := TwoPositive.Split.split_domain ht ha
  have hsa := (transport_trig hdom.1).2.2.1
  have hsu := (transport_trig hdom.2).2.2.1
  have hca : 0≤Real.cos a := by linarith [(transport_trig hdom.1).1]
  have hcu : 0≤Real.cos (t-a) := by linarith [(transport_trig hdom.2).1]
  have hcm := mul_le_mul_of_nonneg_right hmLow hcu
  have hcl := mul_nonneg (show (0:ℝ)≤l/10 by positivity) hca
  have hsig := mul_le_mul_of_nonneg_right
    (show PositiveTD.sigma-1/2≤229/250 by linarith [TwoPositive.Split.sigma_bound]) hsu
  have hsigM := mul_le_mul_of_nonneg_left hsig hm.le
  have hsM := mul_le_mul_of_nonneg_right hmHigh hsu
  have hcharge := mul_le_mul_of_nonneg_left hd hl.le
  have hcos := mul_lt_mul_of_pos_left (cosine_sum ht ha) hl
  have hsin : Real.sin a+Real.sin (t-a)≤frameCap := by
    linarith [Real.sin_le ha.1,Real.sin_le hdom.2.1,ht.2]
  have hsinL := mul_le_mul_of_nonneg_left hsin hl.le
  have hsinAL := mul_nonneg hl.le hsa
  dsimp [TwoPositive.Split.smoothDD,frameCap] at *
  nlinarith only [hcm,hcl,hsigM,hsM,hcharge,hcos,hsinL,hsinAL,hl]

/-- Equation (23), proved from its exact positive-square reserve. -/
theorem D_slope {c : ℝ} (hc : c∈Icc 0 (6/5:ℝ)) :
    R*TwoPositive.Coefficient.normD 1 0 c<(1521/1000:ℝ) := by
  have hn : 0<pairNorm 1 c 0 := by rw [pairNorm_zero]; positivity
  have hn2 := NonnegativeTotals.Analytic.norm_zero_square 1 c
  have hc2 := pow_le_pow_left₀ hc.1 hc.2 2
  have hsquare : (R*c)^2<(1521/1000:ℝ)^2*(pairNorm 1 c 0)^2 := by
    rw [mul_pow,radius_sq,hn2]
    norm_num [qCap] at *
    nlinarith only [hc2]
  have hh := OrdinaryCurvatureBounds.quotient_lt_of_square hn
    (by norm_num : (0:ℝ)<1521/1000) hsquare
  have he : R*TwoPositive.Coefficient.normD 1 0 c=R*c/pairNorm 1 c 0 := by
    simp only [TwoPositive.Coefficient.normD,Real.sin_zero,mul_zero,add_zero]
    ring
  rw [he]
  exact hh

def shiftedD (c : ℝ) : ℝ := TwoPositive.Coefficient.affineBranch 1 0 (21/1000) 0 c

theorem shiftedD_concave {L : ℝ} (hL : 0<L) :
    ConcaveOn ℝ (Icc L (6/5:ℝ)) shiftedD := by
  exact TwoPositive.Coefficient.affine_concave (by norm_num) hL (by norm_num [frameCap])

theorem shiftedD_monotone {L : ℝ} (hL : 0<L) :
    MonotoneOn shiftedD (Icc L (6/5:ℝ)) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro c hc
    exact (TwoPositive.Coefficient.affine_derivative (w:=21/1000) (b:=0)
      (by norm_num) (hL.trans_le hc.1) (by norm_num [frameCap])).continuousAt.continuousWithinAt
  · intro c hc
    exact TwoPositive.Coefficient.affine_derivative (by norm_num)
      (hL.trans hc.1) (by norm_num [frameCap])
  · intro c hc
    have hh := D_slope (show c∈Icc 0 (6/5:ℝ) from ⟨(hL.trans hc.1).le,hc.2.le⟩)
    dsimp [TwoPositive.Coefficient.affineD]
    linarith

def shiftedRest (m l t a : ℝ) : ℝ :=
  TwoPositive.Split.rest m l t a-(21/1000)*PositiveTD.tilted m (t-a)

theorem shifted_rest_curvature {m l t a d : ℝ}
    (hl : 0<l) (hmLow : (9/10)*l≤ m) (hmHigh : m≤(11/10)*l)
    (ht : t∈Icc 0 frameCap) (ha : a∈Icc 0 t)
    (hrot : PositiveTD.tilted m (t-a)≤(23/20)*l)
    (hd : d≤-Real.cos a/2+(23/25)*Real.sin a) :
    TwoPositive.Split.smoothDD m t a+l*d+(21/1000)*PositiveTD.tilted m (t-a)<
      -(6161/100000)*l := by
  have hh := strong_rest_curvature hl hmLow hmHigh ht ha hd
  linarith

theorem shiftedRest_concave {m l t : ℝ}
    (hl : 0<l) (hmLow : (9/10)*l≤ m) (hmHigh : m≤(11/10)*l)
    (ht : t∈Icc 0 frameCap)
    (hrot : ∀a∈Icc 0 t,PositiveTD.tilted m (t-a)≤(23/20)*l) :
    ConcaveOn ℝ (Icc 0 t) (shiftedRest m l t) := by
  have hax {L U : ℝ} (hL : 0≤L) (hU : U≤t) :
      ConcaveOn ℝ (Icc L U) (TwoPositive.Split.axialRest (21/1000) m l t) := by
    apply concave_of_deriv2
      (fun a _ => TwoPositive.Split.axial_derivative (21/1000) m l t a)
      (fun a _ => TwoPositive.Split.axial_second (21/1000) m l t a)
    intro a ha
    have ha' : a∈Icc 0 t := ⟨hL.trans ha.1,ha.2.trans hU⟩
    have hh := shifted_rest_curvature hl hmLow hmHigh ht ha' (hrot a ha')
      (TwoPositive.Split.high_axial_bound (TwoPositive.Split.split_domain ht ha').1)
    exact hh.le.trans (by linarith)
  by_cases hcut : t≤ASupport.alpha
  · have hh := hax (L:=0) (U:=t) le_rfl le_rfl
    have heq {a : ℝ} (ha : a∈Icc 0 t) :
        TwoPositive.Split.axialRest (21/1000) m l t a=shiftedRest m l t a := by
      simp [TwoPositive.Split.axialRest,shiftedRest,TwoPositive.Split.rest,
        ASupport.charge,ha.2.trans hcut]
    refine ⟨hh.1,?_⟩
    intro x hx y hy r v hr hv hrv
    have h := hh.2 hx hy hr hv hrv
    rw [heq hx,heq hy,heq (hh.1 hx hy hr hv hrv)] at h
    exact h
  · have halpha : ASupport.alpha∈Icc 0 t :=
      ⟨by linarith [ASupport.alpha_bounds.1],(lt_of_not_ge hcut).le⟩
    have hcirc : ConcaveOn ℝ (Icc ASupport.alpha t)
        (TwoPositive.Split.circleRest (21/1000) m l t) := by
      apply concave_of_deriv2
        (fun a _ => TwoPositive.Split.circle_derivative (21/1000) m l t a)
        (fun a _ => TwoPositive.Split.circle_second (21/1000) m l t a)
      intro a ha
      have ha' : a∈Icc 0 t := ⟨halpha.1.trans ha.1,ha.2⟩
      have haf := (TwoPositive.Split.split_domain ht ha').1
      have hmajor := ASupport.high_curvature_majorant
        (show a∈Icc (1/2:ℝ) frameCap from
          ⟨by linarith [ha.1,ASupport.alpha_bounds.1],haf.2⟩)
      have hh := shifted_rest_curvature hl hmLow hmHigh ht ha' (hrot a ha')
        ((ASupport.circle_curvature haf).trans hmajor)
      exact hh.le.trans (by linarith)
    have he : TwoPositive.Split.axialRest (21/1000) m l t ASupport.alpha=
        TwoPositive.Split.circleRest (21/1000) m l t ASupport.alpha := by
      simp only [TwoPositive.Split.axialRest,TwoPositive.Split.circleRest,ASupport.transition_value]
    have hleft := TwoPositive.Split.axial_derivative (21/1000) m l t ASupport.alpha
    have hright := TwoPositive.Split.circle_derivative (21/1000) m l t ASupport.alpha
    rw [←ASupport.transition_derivative] at hright
    have hj := join halpha (hax le_rfl halpha.2) hcirc he hleft hright
    convert hj using 1
    funext x
    simp only [TwoPositive.Split.axialRest,TwoPositive.Split.circleRest,shiftedRest,
      TwoPositive.Split.rest,ASupport.charge]
    split_ifs <;> ring

def fixedPart (k l m theta e : ℝ) (i : Fin 3) : ℝ :=
  k+2*l+5/2-fullSupport 1 k-fullSupport l k-fullSupport m l+
    ASupport.charge e+negative k l m (theta+e) i

theorem large_split_form {k l m theta e a : ℝ} (i : Fin 3)
    (ht : theta∈Icc 0 frameCap) (ha : a∈Icc 0 theta) :
    largeScalar k l m theta e a i=fixedPart k l m theta e i+
      (shiftedD (PositiveTD.tilted m (theta-a))+shiftedRest m l theta a) := by
  have hz := (TwoPositive.Split.split_domain ht ha).2
  have hs := TwoPositive.Split.smooth_actual (c:=m) hz
  rw [largeScalar,fullBaseline,fullSupport_pair (tilted m (theta-a)) 1,
    pairNorm_symm (tilted m (theta-a)) 1]
  dsimp [fixedPart,shiftedD,TwoPositive.Coefficient.affineBranch,shiftedRest,
    TwoPositive.Split.rest]
  rw [hs,tilted_eq]
  ring

theorem largeScalar_concave (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) :
    ConcaveOn ℝ (Icc 0 (Explicit.theta r x y))
      (fun a => largeScalar (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
        (Explicit.theta r x y) (Explicit.e r x y) a i) := by
  have hb := Explicit.base_bounds r hd
  have ht := (Explicit.domains hd).1
  have hk : 0<Explicit.k r x y := by linarith [hb.k_lower]
  have hm (a : ℝ) (ha : a∈Icc 0 (Explicit.theta r x y)) :
      PositiveTD.tilted (Explicit.c r x y) (Explicit.theta r x y-a)∈
        Icc (Explicit.k r x y) (6/5:ℝ) := by
    have hu : Explicit.theta r x y-a∈Icc 0 (Explicit.theta r x y) :=
      ⟨by linarith [ha.2],by linarith [ha.1]⟩
    exact ⟨(Explicit.tilted_lower r hd hu).le,(Explicit.tilted_upper r hd hu).le⟩
  have hrot (a : ℝ) (ha : a∈Icc 0 (Explicit.theta r x y)) :
      PositiveTD.tilted (Explicit.c r x y) (Explicit.theta r x y-a)≤(23/20)*Explicit.l r x y := by
    exact (Explicit.tilted_ratio r hd
      (show Explicit.theta r x y-a∈Icc 0 (Explicit.theta r x y) from
        ⟨by linarith [ha.2],by linarith [ha.1]⟩)).2.le
  have hc := (compose (shiftedD_concave hk) (shiftedD_monotone hk)
    (TwoPositive.Split.tilted_concave hb.c_positive ht) hm).add
      (shiftedRest_concave hb.l_positive hb.c_lower_ratio hb.c_upper_ratio ht hrot)
  refine ⟨hc.1,?_⟩
  intro a ha b hb' u v hu hv huv
  have hcomb := hc.1 ha hb' hu hv huv
  have hh := hc.2 ha hb' hu hv huv
  simp only [smul_eq_mul,Pi.add_apply] at hh hcomb ⊢
  rw [large_split_form i ht ha,large_split_form i ht hb',large_split_form i ht hcomb]
  have hconst := congrArg (fun z : ℝ => z*fixedPart
    (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
    (Explicit.theta r x y) (Explicit.e r x y) i) huv
  nlinarith only [hh,hconst]

theorem large_scalar_positive (r : Region) (i : Fin 3) {x y a : ℝ}
    (hd : Explicit.Domain r x y) (ha : a∈Icc 0 (Explicit.theta r x y)) :
    0<largeScalar (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
      (Explicit.theta r x y) (Explicit.e r x y) a i := by
  have hleft : 0<largeScalar (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
      (Explicit.theta r x y) (Explicit.e r x y) 0 i := by
    simpa only [largeEndpoint,NonnegativeTotals.Analytic.aAt] using T_endpoint_positive r i hd
  have hright : 0<largeScalar (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
      (Explicit.theta r x y) (Explicit.e r x y) (Explicit.theta r x y) i := by
    simpa only [largeEndpoint,NonnegativeTotals.Analytic.aAt] using A_endpoint_positive r i hd
  have h := concave_gt_of_endpoints (largeScalar_concave r i hd) ha hleft hright
  exact h

end SquaresInCircles.Eight.GlobalGA.PositiveBT3.Analytic
