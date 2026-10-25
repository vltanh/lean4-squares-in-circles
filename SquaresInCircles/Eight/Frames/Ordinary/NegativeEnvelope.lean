module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.Varying.BComparison

/-!
# Eight squares: uniform negative ordinary-angle bounds

Concavity in the larger coefficient reduces the
complete ratio interval to its two intrinsic endpoints. Direct rational
square comparisons prove `V(h) > .87 p`; the angular chord then gives a
positive lower bound at every nonnegative angle. The same exact derivative
identities prove monotonicity in the smaller coefficient.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OrdinaryNegativeEnvelope
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity VaryingBFunctions VaryingBComparison

theorem D_quotient_hasDerivAt {R p q t : ℝ} (hq : 0<q)
    (ht : t∈Icc 0 frameCap) :
    HasDerivAt (fun x => D R (p/x) t) (Dr R (p/q) t*(-p/q^2)) q := by
  have harg : HasDerivAt (fun x : ℝ => p/x) (-p/q^2) q := by
    have h := (hasDerivAt_inv hq.ne').const_mul p
    convert h using 1
    · funext x
      rw [div_eq_mul_inv]
    · rw [neg_div, div_eq_mul_inv, mul_neg]
  exact (D_hasDerivAt_r (R := R) (r := p/q) ht).comp q harg

theorem V_concave_larger {R p t : ℝ} (hR : 0≤R) (hp : 0<p)
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc p (2*p)) (fun q => V R p q t) := by
  apply concave_of_deriv2
    (f' := fun q => D R (p/q) t)
    (f'' := fun q => Dr R (p/q) t*(-p/q^2))
  · intro q hq
    exact V_hasDerivAt_q hp (hp.trans_le hq.1) ht
  · intro q hq
    exact D_quotient_hasDerivAt (hp.trans_le hq.1) ht
  · intro q hq
    have hq0 := hp.trans_le hq.1
    have hr : p/q∈Icc (1/2) 1 :=
      ⟨(le_div_iff₀ hq0).2 (by linarith [hq.2]),(div_le_one hq0).2 hq.1⟩
    exact mul_nonpos_of_nonneg_of_nonpos (Dr_nonneg hR hr ht)
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp.le) (sq_nonneg q))

theorem cap_sin_lower : (3221/5000 : ℝ)<Real.sin frameCap := by
  have h := sin_lower_seven (show 0≤frameCap by norm_num [frameCap])
  norm_num [frameCap] at h ⊢
  linarith

theorem endpoint_one {R : ℝ} (hR : (19787/10000 : ℝ)<R) :
    (87/100 : ℝ)<V R 1 1 frameCap := by
  have ht : |-frameCap|≤frameCap := by norm_num [frameCap]
  have hN := pairNorm_pos (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1) ht
  have hN2 := pairNorm_sq (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1) ht
  have hZ := pairNorm_pos (p := 1) (q := 1) (t := 0) (by norm_num) (by norm_num)
    (by norm_num [frameCap])
  have hZ2 := pairNorm_sq (p := 1) (q := 1) (t := 0) (by norm_num) (by norm_num)
    (by norm_num [frameCap])
  simp only [pairEnergy,pairProduct,Real.sin_neg,Real.sin_zero] at hN2 hZ2
  have hZlo : (7071/5000 : ℝ)<pairNorm 1 1 0 := by nlinarith
  have hNhi : pairNorm 1 1 (-frameCap)<2109/2500 := by nlinarith [cap_sin_lower]
  have hgap : (2853/5000 : ℝ)<pairNorm 1 1 0-pairNorm 1 1 (-frameCap) := by linarith
  have hmul1 := mul_lt_mul_of_pos_left hgap (by norm_num : (0:ℝ)<19787/10000)
  have hmul2 := mul_lt_mul_of_pos_right hR
    (show 0<pairNorm 1 1 0-pairNorm 1 1 (-frameCap) by linarith)
  have hc := (transport_trig (show frameCap∈Icc 0 frameCap by
    constructor; norm_num [frameCap]; rfl)).1
  dsimp [V]
  nlinarith

theorem endpoint_two {R : ℝ} (hR : (19787/10000 : ℝ)<R) :
    (87/100 : ℝ)<V R 1 2 frameCap := by
  have ht : |-frameCap|≤frameCap := by norm_num [frameCap]
  have hN := pairNorm_pos (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<2) ht
  have hN2 := pairNorm_sq (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<2) ht
  have hZ := pairNorm_pos (p := 1) (q := 2) (t := 0) (by norm_num) (by norm_num)
    (by norm_num [frameCap])
  have hZ2 := pairNorm_sq (p := 1) (q := 2) (t := 0) (by norm_num) (by norm_num)
    (by norm_num [frameCap])
  simp only [pairEnergy,pairProduct,Real.sin_neg,Real.sin_zero] at hN2 hZ2
  have hZlo : (559/250 : ℝ)<pairNorm 1 2 0 := by nlinarith
  have hNhi : pairNorm 1 2 (-frameCap)<15567/10000 := by nlinarith [cap_sin_lower]
  have hgap : (6793/10000 : ℝ)<pairNorm 1 2 0-pairNorm 1 2 (-frameCap) := by linarith
  have hmul1 := mul_lt_mul_of_pos_left hgap (by norm_num : (0:ℝ)<19787/10000)
  have hmul2 := mul_lt_mul_of_pos_right hR
    (show 0<pairNorm 1 2 0-pairNorm 1 2 (-frameCap) by linarith)
  have hc := (transport_trig (show frameCap∈Icc 0 frameCap by
    constructor; norm_num [frameCap]; rfl)).1
  dsimp [V]
  nlinarith

theorem pairNorm_homogeneous {a : ℝ} (ha : 0≤a) (p q t : ℝ) :
    pairNorm (a*p) (a*q) t=a*pairNorm p q t := by
  unfold pairNorm
  have he : (a*p)^2+(a*q)^2+2*(a*p)*(a*q)*Real.sin t=
      a^2*(p^2+q^2+2*p*q*Real.sin t) := by ring
  rw [he,Real.sqrt_mul (sq_nonneg a),Real.sqrt_sq ha]

theorem V_homogeneous {a : ℝ} (ha : 0≤a) (R p q t : ℝ) :
    V R (a*p) (a*q) t=a*V R p q t := by
  dsimp [V]
  rw [pairNorm_homogeneous ha,pairNorm_homogeneous ha]
  ring

/-- The far negative endpoint is uniform over the full coefficient ratio
interval. Its proof needs only the displayed lower radius bound. -/
theorem V_endpoint_lower {R p q : ℝ} (hR : (19787/10000 : ℝ)<R)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) :
    (87/100)*p<V R p q frameCap := by
  have hu : 1≤q/p ∧ q/p≤2 :=
    ⟨(one_le_div hp).2 hpq,(div_le_iff₀ hp).2 hqp⟩
  have hconc := V_concave_larger (R := R) (p := 1) (by linarith) (by norm_num)
    (show frameCap∈Icc 0 frameCap by constructor; norm_num [frameCap]; rfl)
  rw [mul_one] at hconc
  have hsingle : (87/100 : ℝ)<V R 1 (q/p) frameCap :=
    concave_gt_of_endpoints (f := fun x => V R 1 x frameCap) hconc hu
      (endpoint_one hR) (endpoint_two hR)
  have hscaled := mul_lt_mul_of_pos_left hsingle hp
  have he : V R p q frameCap=p*V R 1 (q/p) frameCap := by
    have hmul : p*(q/p)=q := by field_simp
    simpa only [mul_one,hmul] using V_homogeneous hp.le R 1 (q/p) frameCap
  rw [he]
  nlinarith only [hscaled]

theorem sqrt_cap_lower : (19787/10000 : ℝ)<Real.sqrt qCap := by
  have h := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hn := Real.sqrt_nonneg qCap
  dsimp [qCap] at h
  nlinarith

theorem V_chord_lower {p q t : ℝ} (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (ht : t∈Icc 0 frameCap) :
    (87/70)*p*t≤V (Real.sqrt qCap) p q t := by
  have hh : 0<frameCap := by norm_num [frameCap]
  have hα : 0≤t/frameCap ∧ t/frameCap≤1 :=
    ⟨div_nonneg ht.1 hh.le,(div_le_one hh).2 ht.2⟩
  have hconc := V_concave (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hp hpq hqp
  have h := hconc.2 ⟨le_rfl,hh.le⟩ ⟨hh.le,le_rfl⟩
    (sub_nonneg.mpr hα.2) hα.1 (by ring)
  simp only [smul_eq_mul,V_zero,mul_zero,zero_add] at h
  rw [div_mul_cancel₀ t hh.ne'] at h
  have hmul := mul_le_mul_of_nonneg_left (V_endpoint_lower sqrt_cap_lower hp hpq hqp).le hα.1
  have hid : (t/frameCap)*((87/100)*p)=(87/70)*p*t := by dsimp [frameCap]; ring
  rw [hid] at hmul
  exact hmul.trans h

def smallerD (R r t : ℝ) : ℝ :=
  R*(r/shape r-(r-Real.sin t)/root r (Real.sin t))

theorem smallerD_nonneg {R r t : ℝ} (hR : 0≤R) (hr : r∈Icc (1/2) 1)
    (ht : t∈Icc 0 frameCap) : 0≤ smallerD R r t := by
  let u : ℝ := Real.sin t
  have hu : u∈Icc 0 frameCap := sin_mem ht
  have huSmall : u<129/200 := by dsimp [u]; linarith [(transport_trig ht).2.2.2.1]
  have hr0 : 0≤r := by linarith [hr.1]
  have hratio : (4/5)*(1+r^2)≤2*r := by
    have h := mul_nonneg (show 0≤r-1/2 by linarith [hr.1])
      (show 0≤2-r by linarith [hr.2])
    nlinarith
  have hfactor : 0≤2*r-(1+r^2)*u := by
    have h := mul_le_mul_of_nonneg_left huSmall.le (show 0≤1+r^2 by positivity)
    nlinarith [sq_nonneg r]
  have hS := shape_pos r
  have hN := root_pos r hu
  have hS2 := shape_sq r
  have hN2 := root_sq r hu
  have hfrac : (r-u)/root r u≤r/shape r := by
    apply (div_le_div_iff₀ hN hS).2
    by_cases hru : r-u≤0
    · exact (mul_nonpos_of_nonpos_of_nonneg hru hS.le).trans (mul_nonneg hr0 hN.le)
    · have hsquare : ((r-u)*shape r)^2≤(r*root r u)^2 := by
        have he : (r*root r u)^2-((r-u)*shape r)^2=u*(2*r-(1+r^2)*u) := by
          calc
            (r*root r u)^2-((r-u)*shape r)^2=r^2*(root r u)^2-(r-u)^2*(shape r)^2 := by ring
            _=u*(2*r-(1+r^2)*u) := by rw [hN2,hS2]; ring
        have h := mul_nonneg hu.1 hfactor
        rw [← he] at h
        linarith
      nlinarith [mul_nonneg hr0 hN.le,mul_nonneg (lt_of_not_ge hru).le hS.le]
  dsimp [smallerD]
  exact mul_nonneg hR (sub_nonneg.mpr hfrac)

theorem V_hasDerivAt_p {R p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : t∈Icc 0 frameCap) :
    HasDerivAt (fun x => V R x q t) (smallerD R (p/q) t) p := by
  have hN' : HasDerivAt (fun x => pairNorm x q (-t))
      ((p-q*Real.sin t)/pairNorm p q (-t)) p := by
    simpa only [pairNorm_symm] using negativeNorm_hasDerivAt_q (l := q) (q := p) hq hp ht
  have hZ' : HasDerivAt (fun x => pairNorm x q 0) (p/pairNorm p q 0) p := by
    simpa only [neg_zero,Real.sin_zero,mul_zero,sub_zero,pairNorm_symm] using
      negativeNorm_hasDerivAt_q (l := q) (q := p) hq hp
        (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have hraw := (hasDerivAt_const p (q*(Real.cos t-1))).sub ((hN'.sub hZ').const_mul R)
  have hnorm := negativeNorm_normalized (l := p) (t := t) hq
  have hzero : pairNorm p q 0=q*shape (p/q) := by
    simpa using negativeNorm_normalized (l := p) (t := 0) hq
  have hS := (shape_pos (p/q)).ne'
  have hNn := (root_pos (p/q) (sin_mem ht)).ne'
  convert hraw using 1
  · rfl
  · dsimp [smallerD]
    rw [hnorm,hzero]
    field_simp [hq.ne',hS,hNn]
    ring

theorem V_monotone_smaller {R q t : ℝ} (hR : 0≤R) (hq : 0<q)
    (ht : t∈Icc 0 frameCap) :
    MonotoneOn (fun p => V R p q t) (Icc (q/2) q) := by
  have hp0 (p : ℝ) (hp : p∈Icc (q/2) q) : 0<p := by linarith [hp.1]
  apply monoOn_of_hasDeriv_nonneg
  · intro p hp
    exact (V_hasDerivAt_p (hp0 p hp) hq ht).continuousAt.continuousWithinAt
  · intro p hp
    exact V_hasDerivAt_p (hp0 p (Ioo_subset_Icc_self hp)) hq ht
  · intro p hp
    have hr : p/q∈Icc (1/2) 1 :=
      ⟨(le_div_iff₀ hq).2 (by linarith [hp.1]),(div_le_one hq).2 hp.2.le⟩
    exact smallerD_nonneg hR hr ht

/-- The near-equal comparison follows from the stronger correlated
larger-coefficient theorem at `d=h`. -/
theorem near_equal_chain {k n l t : ℝ}
    (hk : (43/50 : ℝ)≤k) (hkn : k≤n) (hn : n≤1)
    (hl : k/2≤l) (hlk : l≤k) (ht : t∈Icc 0 frameCap) :
    V (Real.sqrt qCap) l k t≤V (Real.sqrt qCap) k k t ∧
    V (Real.sqrt qCap) k k t≤V (Real.sqrt qCap) k 1 t ∧
    V (Real.sqrt qCap) k 1 t≤V (Real.sqrt qCap) n 1 t := by
  have hk0 : 0<k := by linarith
  have hk1 : k≤1 := hkn.trans hn
  refine ⟨?_,?_,?_⟩
  · exact V_monotone_smaller (Real.sqrt_nonneg qCap) hk0 ht
      ⟨hl,hlk⟩ ⟨by linarith,le_rfl⟩ hlk
  · exact V_larger_coefficient hk0 le_rfl hk1
      (by dsimp [PositiveStressCoefficients.ratio,frameCap]; linarith)
      ⟨by norm_num [frameCap],le_rfl⟩ ht
  · exact V_monotone_smaller (Real.sqrt_nonneg qCap) (by norm_num) ht
      ⟨by linarith,hk1⟩ ⟨by linarith,hn⟩ hkn

end SquaresInCircles.Eight.OrdinaryNegativeEnvelope
