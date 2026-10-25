module

public import SquaresInCircles.Eight.Frames.Ordinary.NegativeSlope
public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts

/-!
# Eight squares: negative-angle growth after a short negative primary is removed

The available negative angle is at most `h-s`.
The fixed ratio `2/3` gains at least `s/4` in its derivative on this
shortened interval. This compensates the actual secant enlargement of
the other block's coefficient for every `0 ≤ s ≤ .3`.
-/

section
/-!
## Quantitative reserves on the complete short negative-angle interval

The interval is the whole closed interval [0,3/5]. A single
quartic identity proves the normalized endpoint slope for every ratio
in [3/5,1]; concavity transports that bound to every smaller angle.
The same-block comparison retains both signed masses and pays a
uniform positive charge, including the zero-mass boundary.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OrdinaryNegativeShortSlope
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope OrdinaryNegativeSlope
open VaryingBFunctions VaryingBComparison Arithmetic SecondWord.ReferenceTrig

def domain : Set ℝ := Icc 0 (3/5)

lemma subset_frame {t : ℝ} (ht : t∈domain) : t∈Icc 0 frameCap :=
  ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩

lemma cap_trig :
    (3529/6250:ℝ)<Real.sin (3/5) ∧ Real.sin (3/5)<11293/20000 ∧
      (82533/100000:ℝ)<Real.cos (3/5) := by
  have hs := sin11_le_sin (show (0:ℝ)≤3/5 by norm_num)
  have hsu := sin_le_sin9 (show (0:ℝ)≤3/5 by norm_num)
  have hc := cos10_le_cos (show (0:ℝ)≤3/5 by norm_num)
  norm_num [sin11,sin9,sin7,cos10,cos8] at hs hsu hc
  exact ⟨by linarith,by linarith,by linarith⟩

lemma sine_monotone : MonotoneOn Real.sin (Icc 0 frameCap) :=
  monoOn_of_hasDeriv_nonneg
    (fun t _ => (Real.hasDerivAt_sin t).continuousAt.continuousWithinAt)
    (fun t _ => Real.hasDerivAt_sin t)
    (fun t ht => by linarith [(transport_trig (Ioo_subset_Icc_self ht)).1])

lemma cosine_antitone : AntitoneOn Real.cos (Icc 0 frameCap) :=
  antiOn_of_hasDeriv_nonpos
    (fun t _ => (Real.hasDerivAt_cos t).continuousAt.continuousWithinAt)
    (fun t _ => Real.hasDerivAt_cos t)
    (fun _t ht => neg_nonpos.mpr (transport_trig (Ioo_subset_Icc_self ht)).2.2.1)

lemma trig_bounds {t : ℝ} (ht : t∈domain) :
    (41/50:ℝ)≤Real.cos t ∧ Real.sin t≤113/200 ∧ (47/50)*t≤Real.sin t := by
  have ht2 := pow_le_pow_left₀ ht.1 ht.2 2
  have ht3 := mul_le_mul_of_nonneg_right ht2 ht.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have hs := Real.sin_ge_sub_cube ht.1
  have hm := sine_monotone (subset_frame ht)
    (show (3/5:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) ht.2
  refine ⟨by linarith,by linarith [cap_trig.2.1],by nlinarith⟩

def endpointPolynomial (r : ℝ) : ℝ :=
  qCap*r^2*(82533/100000)^2-
    ((103/100)*r+11293/20000)^2*(1+r^2-2*r*(3529/6250))

lemma endpoint_expansion (x : ℝ) :
    endpointPolynomial (3/5+x)=
      3560337820289/625000000000000+
      (89945678458213/62500000000000)*x+
      (9306058820721/25000000000000)*x^2-
      (313910731/125000000)*x^3-(10609/10000)*x^4 := by
  norm_num [endpointPolynomial,qCap]
  ring

lemma endpoint_polynomial_positive {r : ℝ} (hr : r∈Icc (3/5:ℝ) 1) :
    0<endpointPolynomial r := by
  let x := r-3/5
  have hx : x∈Icc (0:ℝ) (2/5) := by
    dsimp [x]
    exact ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have h2 := pow_le_pow_left₀ hx.1 hx.2 2
  have h3 := pow_le_pow_left₀ hx.1 hx.2 3
  have hlinear : 0≤89945678458213/62500000000000-
      (313910731/125000000)*x^2-(10609/10000)*x^3 := by nlinarith
  have hpaid := mul_nonneg hx.1 hlinear
  have he := endpoint_expansion x
  rw [show 3/5+x=r by dsimp [x]; ring] at he
  nlinarith [sq_nonneg x]

lemma endpoint_normalized {r : ℝ} (hr : r∈Icc (3/5:ℝ) 1) :
    (103/100)*r< -Real.sin (3/5)+
      Real.sqrt qCap*r*Real.cos (3/5)/root r (Real.sin (3/5)) := by
  have ht : (3/5:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hN := root_pos r (sin_mem ht)
  have hN2 := root_sq r (sin_mem ht)
  have hr0 : 0<r := by linarith [hr.1]
  have hs0 := (transport_trig ht).2.2.1
  have hc0 : 0<Real.cos (3/5) := by linarith [cap_trig.2.2]
  have hR0 : 0<Real.sqrt qCap := by linarith [sqrt_cap_lower]
  have hR2 := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hroot : (root r (Real.sin (3/5)))^2≤1+r^2-2*r*(3529/6250) := by
    rw [hN2]
    linarith only [mul_le_mul_of_nonneg_left cap_trig.1.le hr0.le]
  have hleft0 : 0≤(103/100)*r+Real.sin (3/5) := by positivity
  have hleft : (103/100)*r+Real.sin (3/5)≤(103/100)*r+11293/20000 := by
    linarith [cap_trig.2.1]
  have hleft2 := pow_le_pow_left₀ hleft0 hleft 2
  have hprod := mul_le_mul hleft2 hroot (sq_nonneg _) (sq_nonneg _)
  have hc2 := pow_le_pow_left₀
    (by norm_num : (0:ℝ)≤82533/100000) cap_trig.2.2.le 2
  have hright := mul_le_mul_of_nonneg_left hc2
    (mul_nonneg (by norm_num [qCap] : 0≤qCap) (sq_nonneg r))
  have hright0 : 0<Real.sqrt qCap*r*Real.cos (3/5) := by positivity
  have he : (Real.sqrt qCap*r*Real.cos (3/5))^2=
      qCap*r^2*(Real.cos (3/5))^2 := by
    calc
      _=(Real.sqrt qCap)^2*r^2*(Real.cos (3/5))^2 := by ring
      _=_ := by rw [hR2]
  have hpoly := endpoint_polynomial_positive hr
  dsimp [endpointPolynomial] at hpoly
  have hsq : (((103/100)*r+Real.sin (3/5))*root r (Real.sin (3/5)))^2<
      (Real.sqrt qCap*r*Real.cos (3/5))^2 := by
    rw [he,mul_pow]
    simp only [qCap] at hpoly hright ⊢
    linarith only [hprod,hpoly,hright]
  have hcross := lt_of_pow_lt_pow_left₀ 2 hright0.le hsq
  have hdiv := (lt_div_iff₀ hN).2 hcross
  linarith only [hdiv]

lemma Vd_lower {p q t : ℝ} (hp : 0<p) (hpq : p≤q)
    (hratio : (3/5)*q≤p) (ht : t∈domain) :
    (103/100)*p<Vd (Real.sqrt qCap) p q t := by
  have hq := hp.trans_le hpq
  have hr : p/q∈Icc (3/5:ℝ) 1 :=
    ⟨(le_div_iff₀ hq).2 hratio,(div_le_one hq).2 hpq⟩
  have hh := mul_lt_mul_of_pos_left (endpoint_normalized hr) hq
  have hcancel : q*(p/q)=p := by field_simp [hq.ne']
  have hend : (103/100)*p<Vd (Real.sqrt qCap) p q (3/5) := by
    rw [Vd_normalized hq]
    nlinarith only [hh,hcancel]
  have hm := Vd_antitone (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hp hpq
    (by linarith : q≤2*p)
  exact hend.trans_le (hm (subset_frame ht)
    (show (3/5:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) ht.2)

theorem V_growth {p q t u : ℝ} (hp : 0<p) (hpq : p≤q)
    (hratio : (3/5)*q≤p) (ht : t∈domain) (hu : u∈domain) (htu : t≤u) :
    (103/100)*p*(u-t)≤V (Real.sqrt qCap) p q u-V (Real.sqrt qCap) p q t := by
  have hq := hp.trans_le hpq
  exact derivative_reserve
    (fun x hx => (V_hasDerivAt hp hq (subset_frame hx)).continuousAt.continuousWithinAt)
    (fun x hx => V_hasDerivAt hp hq (subset_frame (Ioo_subset_Icc_self hx)))
    (fun x hx => (Vd_lower hp hpq hratio (Ioo_subset_Icc_self hx)).le) ht hu htu

lemma same_difference (R p q P N : ℝ) :
    mixedBlock R p q P N-V R p q (N-P)=
      p*(Real.cos P+Real.sin P-1)+q*(Real.cos N-Real.cos (N-P)) := by
  simp only [mixedBlock,V,PositiveAngularEnvelope.phi,show -(N-P)=P-N by ring]
  ring

/-- The reserve is charged only against the actual common positive mass. -/
theorem same_reserve {R p q P N : ℝ}
    (hp : (3/5:ℝ)≤p) (hqp : q≤(5/3)*p)
    (hP : 0≤P) (hPN : P≤N) (hN : N≤3/5) :
    V R p q (N-P)+(3/100)*P≤ mixedBlock R p q P N := by
  have hPd : P∈domain := ⟨hP,hPN.trans hN⟩
  have hNd : N∈domain := ⟨hP.trans hPN,hN⟩
  have hdiff : N-P∈Icc 0 frameCap :=
    ⟨by linarith,by norm_num [frameCap]; linarith⟩
  have hm := cosine_antitone hdiff (subset_frame hNd) (by linarith)
  have hqterm := mul_le_mul_of_nonpos_right hqp (sub_nonpos.mpr hm)
  have htP := trig_bounds hPd
  have htN := trig_bounds hNd
  have hsP := (transport_trig (subset_frame hPd)).2.2.1
  have hfirst := mul_nonneg
    (show 0≤(5/3)*Real.cos N-1 by linarith [htN.1])
    (sub_nonneg.mpr (Real.cos_le_one P))
  have hsecond := mul_le_mul_of_nonneg_right
    (show (7/120:ℝ)≤1-(5/3)*Real.sin N by linarith [htN.2.1]) hsP
  have hslope := mul_le_mul_of_nonneg_left htP.2.2
    (by norm_num : (0:ℝ)≤7/120)
  have hunit : (329/6000)*P≤Real.cos P+Real.sin P-1+
      (5/3)*(Real.cos N-Real.cos (N-P)) := by
    rw [Real.cos_sub]
    linarith only [hfirst,hsecond,hslope]
  have hpaid := mul_le_mul_of_nonneg_left hunit (show 0≤p by linarith)
  have hscale := mul_nonneg (sub_nonneg.mpr hp) hP
  have he := same_difference R p q P N
  linarith only [he,hqterm,hpaid,hscale,hP]

end SquaresInCircles.Eight.OrdinaryNegativeShortSlope
end
end
end

section
/-!
## The positive-surplus companion of the short same-block reserve

The positive angle may range up to the original frame cap; only the
common negative mass is bounded by .6. Monotonicity moves the positive
angle to the true cap before its trigonometric coefficients are bounded.
In particular no false separate lower bound for phi(P) is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OrdinaryMixedShortReserve
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeShortSlope

lemma constant_add {f : ℝ→ℝ} {l u : ℝ}
    (hf : ConcaveOn ℝ (Icc l u) f) (C : ℝ) :
    ConcaveOn ℝ (Icc l u) (fun t => C+f t) := by
  refine ⟨hf.1,?_⟩
  intro x hx y hy r v hr hv hrv
  have hh := hf.2 hx hy hr hv hrv
  have he := congrArg (fun w : ℝ => w*C) hrv
  simp only [smul_eq_mul] at hh ⊢
  nlinarith only [hh,he]

def phiD (t : ℝ) : ℝ := Real.cos t-Real.sin t

lemma phi_hasDerivAt (t : ℝ) : HasDerivAt PositiveAngularEnvelope.phi (phiD t) t := by
  have h := (Real.hasDerivAt_cos t).fun_add (Real.hasDerivAt_sin t)
  exact h.congr_deriv (by unfold phiD; ring)

end SquaresInCircles.Eight.OrdinaryMixedShortReserve
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OrdinaryShortSecantGrowth
open PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope VaryingBFunctions
open PositiveStressCoefficients

theorem fixed_second_upper {t : ℝ} (ht : t∈Icc 0 frameCap) :
    curvature (Real.sqrt qCap) (2/3) 1 (-t)-Real.cos t≤ -(1/4) := by
  have hN := pairNorm_pos (p := (2/3 : ℝ)) (q := 1) (t := 0)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  have hN2 := pairNorm_sq (p := (2/3 : ℝ)) (q := 1) (t := 0)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  simp only [pairEnergy,pairProduct,Real.sin_zero,mul_zero,add_zero] at hN2
  have hNlo : (6/5 : ℝ)≤pairNorm (2/3) 1 0 := by nlinarith
  have hN3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤6/5) hNlo 3
  have hR2 : (Real.sqrt qCap)^2=9789/2500 := Real.sq_sqrt (by norm_num [qCap])
  have hR : Real.sqrt qCap≤2 := by nlinarith [Real.sqrt_nonneg qCap]
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
  have hd (x : ℝ) (hx : x∈Icc 0 frameCap) :
      HasDerivAt (fun x => -Vd (Real.sqrt qCap) (2/3) 1 x)
        (-(curvature (Real.sqrt qCap) (2/3) 1 (-x)-Real.cos x)) x := by
    have h := (Vd_hasDerivAt (R := Real.sqrt qCap) (by norm_num : (0:ℝ)<2/3)
      (by norm_num : (0:ℝ)<1) hx).neg
    rw [one_mul] at h
    exact h
  have h := derivative_reserve
    (f := fun x => -Vd (Real.sqrt qCap) (2/3) 1 x)
    (df := fun x => -(curvature (Real.sqrt qCap) (2/3) 1 (-x)-Real.cos x))
    (k := (1/4 : ℝ))
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => hd x (Ioo_subset_Icc_self hx))
    (fun x hx => by linarith [fixed_second_upper (Ioo_subset_Icc_self hx)]) ht hh ht.2
  have hend := endpoint_normalized_slope
  have he : Vd (Real.sqrt qCap) (2/3) 1 frameCap=
      -Real.sin frameCap+Real.sqrt qCap*(2/3)*Real.cos frameCap/
        root (2/3) (Real.sin frameCap) := by
    rw [Vd_normalized (by norm_num : (0:ℝ)<1)]
    simp only [div_one,one_mul]
  rw [← he] at hend
  linarith

theorem shortened_slope {p q s t : ℝ} (hp : 0<p) (hpq : p≤q)
    (hratio : (2/3)*q≤p) (hs : 0≤ s) (ht : t∈Icc 0 (frameCap-s)) :
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
    have e1 : Real.sqrt qCap*(2/3)*Real.cos t/root (2/3) (Real.sin t)=
        Real.sqrt qCap*Real.cos t*(2/3/root (2/3) (Real.sin t)) := by ring
    have e2 : Real.sqrt qCap*(p/q)*Real.cos t/root (p/q) (Real.sin t)=
        Real.sqrt qCap*Real.cos t*(p/q/root (p/q) (Real.sin t)) := by ring
    rw [e1] at hbase
    rw [e2]
    have ht2 : t≤7/10-s := ht.2
    have hbase' : 2/3+(7/10-t)/4< -Real.sin t+
        Real.sqrt qCap*Real.cos t*(2/3/root (2/3) (Real.sin t)) := hbase
    linarith
  rw [Vd_normalized hq]
  nlinarith only [mul_le_mul_of_nonneg_left hnormal hq.le]

theorem shortened_growth {p q s t u : ℝ} (hp : 0<p) (hpq : p≤q)
    (hratio : (2/3)*q≤p) (hs : 0≤ s)
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
  have hc2 := Real.one_sub_sq_div_two_le_cos (x := s)
  have hs2 : s^2≤(3/10)*s := by nlinarith [hs.1,hs.2]
  have hs3 : s^3≤(9/100)*s := by nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hs2)]
  have hcoef : 0≤k*(2/3+s/4) := by dsimp [k]; linarith [hs.1]
  have hmul := mul_le_mul_of_nonneg_left hc2 hcoef
  rw [div_le_iff₀ hc]
  simp only [k] at hmul ⊢
  nlinarith [hs.1]

end SquaresInCircles.Eight.OrdinaryShortSecantGrowth
end
end
end
