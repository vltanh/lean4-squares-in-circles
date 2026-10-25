module

public import SquaresInCircles.Eight.TableFree.SecantNormCurvature
public import SquaresInCircles.Eight.TableFree.CriticalNegativeTGain

/-!
# Whole-interval critical negative-T interpolation

Uncompiled source. TD's small positive gain curvature is dominated by
the ordinary negative charge curvature. The BT gain is already concave.
The two actual endpoint charges are kept separate throughout; neither
the small shifted A charge nor the larger coefficient is replaced by B.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalNegativeTCurvature
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open OrdinaryCurvatureBounds SingleAngleConcavity CriticalECoefficients
open SecantNormCurvature FlatTStress CriticalEExclusion

theorem TD_root_ratio {R c : ℝ} (hR : 0≤R) (hq : qLow≤R^2)
    (hc : 37/40<c) : (1343/1000:ℝ)<R/Real.sqrt ((1/c)^2+1) := by
  have hc0 : 0<c := by linarith
  have ha : 0≤1/c := by positivity
  have hau : 1/c≤40/37 := (div_le_iff₀ hc0).2 (by linarith)
  have ha2 := pow_le_pow_left₀ ha hau 2
  have hn : 0<Real.sqrt ((1/c)^2+1) := Real.sqrt_pos.mpr (by positivity)
  have hn2 := Real.sq_sqrt (show 0≤(1/c)^2+1 by positivity)
  have hnu : Real.sqrt ((1/c)^2+1)<1473/1000 := by nlinarith
  have hr := SoleAngleGrowth.radius_lower hR hq
  apply (lt_div_iff₀ hn).2
  nlinarith

theorem BT_root_ratio {R a : ℝ} (hR : 0≤R) (hq : qLow≤R^2)
    (ha : a∈Icc 0 (17/25:ℝ)) : (163/100:ℝ)<R/Real.sqrt (a^2+1) := by
  have ha2 := pow_le_pow_left₀ ha.1 ha.2 2
  have hn : 0<Real.sqrt (a^2+1) := Real.sqrt_pos.mpr (by positivity)
  have hn2 := Real.sq_sqrt (show 0≤a^2+1 by positivity)
  have hnu : Real.sqrt (a^2+1)<121/100 := by nlinarith
  have hr := SoleAngleGrowth.radius_lower hR hq
  apply (lt_div_iff₀ hn).2
  nlinarith

theorem TD_second {R t k l c eta s : ℝ} (hR : 0≤R) (hq : qLow≤R^2)
    (h : Bounds t k l c eta) (hs : s∈Icc 0 (4/25:ℝ)) :
    c*gainSecond R (1/c) s<41/500 := by
  have hc : 0<c := by linarith [h.c_lower]
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; linarith [hs.2])
  have hn := mul_le_mul_of_nonneg_left (normSecond_lower (a := 1/c) hcos) hR
  rw [mul_one_div] at hn
  have hr := TD_root_ratio hR hq h.c_lower
  have hs2 := commonSecond_critical hs
  have hh : gainSecond R (1/c) s<41/500 := by
    dsimp [gainSecond]
    linarith
  have hm := mul_lt_mul_of_pos_left hh hc
  nlinarith [h.c_upper]

theorem BT_second {R t k l c eta s : ℝ} (hR : 0≤R) (hq : qLow≤R^2)
    (h : Bounds t k l c eta) (hs : s∈Icc 0 (9/100:ℝ)) :
    c*gainSecond R (l/c) s< -(41/100)*c := by
  have hc : 0<c := by linarith [h.c_lower]
  have ha : l/c∈Icc 0 (17/25:ℝ) :=
    ⟨div_nonneg h.ell_pos.le hc.le,(div_le_iff₀ hc).2 h.ell_c_upper.le⟩
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; linarith [hs.2])
  have hn := mul_le_mul_of_nonneg_left (normSecond_lower (a := l/c) hcos) hR
  rw [mul_one_div] at hn
  have hr := BT_root_ratio hR hq ha
  have hs2 := commonSecond_BT hs
  have hh : gainSecond R (l/c) s< -(41/100) := by dsimp [gainSecond]; linarith
  simpa only [mul_comm] using mul_lt_mul_of_pos_left hh hc

theorem ordinary_short_second {R p q nu s : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (hp : (2331/4000:ℝ)<p)
    (hpq : p≤q) (hqp : q≤2*p) (hnu : p≤nu) (hs : s∈Icc 0 (4/25:ℝ)) :
    curvature R p q (-s)-nu*Real.cos s< -(131/1000) := by
  have hp0 : 0<p := by linarith
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hb := trig_bracket (l := 0) (u := (4/25:ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) hs
  have hc : (987/1000:ℝ)<Real.cos s := by norm_num at hb; linarith [hb.2.2.1]
  have hzero := (curvature_constant_bounds hR hQ hp0 hpq hqp).1
  have hneg := curvature_negative_upper hR hp0 (hp0.trans_le hpq)
    (show -s∈Icc (-frameCap) 0 by constructor <;> linarith [hs'.1,hs'.2])
  have hnu' := mul_le_mul_of_nonneg_right hnu (by linarith : 0≤Real.cos s)
  have hp' := mul_lt_mul_of_pos_left hc hp0
  nlinarith

def pairValue (R c a p q nu t s : ℝ) : ℝ :=
  secantCharge R c a s+Vnu R p q nu (t-s)
def pairFirst (R c a p q nu t s : ℝ) : ℝ :=
  c*gainFirst R (a/c) s-VnuDeriv R p q nu (t-s)
def pairSecond (R c a p q nu t s : ℝ) : ℝ :=
  c*gainSecond R (a/c) s+curvature R p q (-(t-s))-nu*Real.cos (t-s)

theorem pair_hasDerivAt {R c a p q nu t s : ℝ} (hc : 0<c) (hp : 0<p) (hq : 0<q)
    (hcos : 0<Real.cos s) (hd : t-s∈Icc 0 frameCap) :
    HasDerivAt (pairValue R c a p q nu t) (pairFirst R c a p q nu t s) s := by
  have hv := (Vnu_hasDerivAt (R := R) (nu := nu) hp hq hd).comp s
    ((hasDerivAt_const s t).sub (hasDerivAt_id s))
  convert (charge_hasDerivAt (R := R) (a := a) hc hcos).add hv using 1
  · rfl
  · dsimp [pairFirst]
    ring

theorem pairFirst_hasDerivAt {R c a p q nu t s : ℝ} (hp : 0<p) (hq : 0<q)
    (hcos : 0<Real.cos s) (hd : t-s∈Icc 0 frameCap) :
    HasDerivAt (pairFirst R c a p q nu t) (pairSecond R c a p q nu t s) s := by
  have hv := (VnuDeriv_hasDerivAt (R := R) (nu := nu) hp hq hd).comp s
    ((hasDerivAt_const s t).sub (hasDerivAt_id s))
  convert (charge_derivative_hasDerivAt (R := R) (c := c) (a := a) hcos).sub hv using 1
  · rfl
  · dsimp [pairSecond]
    ring

theorem TD_concave {R t k l c eta q nu : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (h : Bounds t k l c eta)
    (hlq : l≤q) (hql : q≤2*l) (hnu : l≤nu) :
    ConcaveOn ℝ (Icc 0 t) (pairValue R c 1 l q nu t) := by
  have hc : 0<c := by linarith [h.c_lower]
  have hq : 0<q := h.ell_pos.trans_le hlq
  have hd (s : ℝ) (hs : s∈Icc 0 t) : t-s∈Icc 0 (4/25:ℝ) :=
    ⟨sub_nonneg.mpr hs.2,by linarith [h.angle_upper,hs.1]⟩
  have hd' (s : ℝ) (hs : s∈Icc 0 t) : t-s∈Icc 0 frameCap :=
    ⟨(hd s hs).1,by dsimp [frameCap]; linarith [(hd s hs).2]⟩
  have hcos (s : ℝ) (hs : s∈Icc 0 t) : 0<Real.cos s :=
    transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2.trans h.angle.2)
  apply concave_of_deriv2
    (fun s hs => pair_hasDerivAt hc h.ell_pos hq (hcos s hs) (hd' s hs))
    (fun s hs => pairFirst_hasDerivAt h.ell_pos hq (hcos s hs) (hd' s hs))
  intro s hs
  have hG := TD_second hR hQL h ⟨hs.1,hs.2.trans h.angle_upper⟩
  have hV := ordinary_short_second hR hQU
    (show (2331/4000:ℝ)<l by nlinarith [h.ell_c_lower,h.c_lower]) hlq hql hnu (hd s hs)
  dsimp [pairSecond]
  linarith

theorem BT_concave {R t k l c eta q nu : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (h : Bounds t k l c eta)
    (hlq : l≤q) (hql : q≤2*l) (hnu : l≤nu) :
    ConcaveOn ℝ (Icc 0 (9/100:ℝ)) (pairValue R c l l q nu t) := by
  have hc : 0<c := by linarith [h.c_lower]
  have hq : 0<q := h.ell_pos.trans_le hlq
  have hd (s : ℝ) (hs : s∈Icc 0 (9/100:ℝ)) : t-s∈Icc 0 frameCap :=
    ⟨by linarith [h.angle_lower,hs.2],by show t-s≤7/10; linarith [h.angle_upper,hs.1]⟩
  have hcos (s : ℝ) (hs : s∈Icc 0 (9/100:ℝ)) : 0<Real.cos s :=
    transport_cos_pos (by rw [abs_of_nonneg hs.1]; linarith [hs.2])
  apply concave_of_deriv2
    (fun s hs => pair_hasDerivAt hc h.ell_pos hq (hcos s hs) (hd s hs))
    (fun s hs => pairFirst_hasDerivAt h.ell_pos hq (hcos s hs) (hd s hs))
  intro s hs
  have hG := BT_second hR hQL h hs
  have hV := Vnu_second_lt hR hQU h.ell_pos hlq hql hnu (hd s hs)
  dsimp [pairSecond]
  nlinarith

theorem charge_eq_gain {q c a s : ℝ} (hc : 0<c) (hs : s∈Icc 0 frameCap) :
    secantCharge (Real.sqrt q) c a s=c*GlobalGA.secantGain q (a/c) s := by
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  rw [charge_scale hc,GlobalGA.secantGain_eq_secant_expression q (a/c) hcos]
  simp only [normalized,supportNorm,secant]
  rw [show (a/c)^2+(1/Real.cos s)^2=(1/Real.cos s)^2+(a/c)^2 by ring,
    show (a/c)^2+1=1+(a/c)^2 by ring]
  ring

/-- The existing full-domain first derivative is stronger than the cost
of every ordinary positive surplus on the critical strip. -/
theorem TD_late_growth {q t k l c eta s : ℝ} (hq : q∈Icc qLow qTrial)
    (h : Bounds t k l c eta) (hs : s∈Icc t (3/10:ℝ)) :
    (17/20)*(s-t)≤ secantCharge (Real.sqrt q) c 1 s-secantCharge (Real.sqrt q) c 1 t := by
  have hc : 0<c := by linarith [h.c_lower]
  have hq0 : 0≤q := by norm_num [qLow] at hq; linarith [hq.1]
  have hQU : q≤qCap := hq.2.trans uniform_radius_order.2.2.1.le
  have ha : (13/20:ℝ)≤1/c := (le_div_iff₀ hc).2 (by linarith [h.c_upper])
  have hs' : s∈Icc 0 frameCap :=
    ⟨by linarith [h.angle_lower,hs.1],by show s≤7/10; linarith [hs.2]⟩
  have hd := derivative_reserve
    (fun v hv => (GlobalGA.secantGain_hasDerivAt q (1/c)
      (transport_cos_pos (by rw [abs_of_nonneg hv.1]; exact hv.2)).ne').continuousAt.continuousWithinAt)
    (fun v hv => GlobalGA.secantGain_hasDerivAt q (1/c)
      (transport_cos_pos (by rw [abs_of_nonneg hv.1.le]; exact hv.2.le)).ne')
    (fun v hv => (GlobalGA.secantGainDeriv_gt hq0 hQU ha (Ioo_subset_Icc_self hv)).le)
    h.angle hs' hs.1
  have hm := mul_le_mul_of_nonneg_left hd hc.le
  rw [charge_eq_gain hc hs',charge_eq_gain hc h.angle]
  nlinarith [h.c_lower,sub_nonneg.mpr hs.1]

end SquaresInCircles.Eight.TableFree.CriticalNegativeTCurvature
