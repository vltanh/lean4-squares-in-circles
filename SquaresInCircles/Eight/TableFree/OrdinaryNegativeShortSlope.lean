module

public import SquaresInCircles.Eight.TableFree.OrdinaryNegativeSlope
public import SquaresInCircles.Eight.TableFree.SecondOuterReferenceTrig

/-!
# Quantitative reserves on the complete short negative-angle interval

Uncompiled source draft of (22)--(26) in the remaining genuine-EH
companion. The interval is the whole closed interval [0,3/5]. A single
quartic identity proves the normalized endpoint slope for every ratio
in [3/5,1]; concavity transports that bound to every smaller angle.
The same-block comparison retains both signed masses and pays a
uniform positive charge, including the zero-mass boundary.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.OrdinaryNegativeShortSlope
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
    (fun t ht => neg_nonpos.mpr (transport_trig (Ioo_subset_Icc_self ht)).2.2.1)

lemma trig_bounds {t : ℝ} (ht : t∈domain) :
    (41/50:ℝ)≤Real.cos t ∧ Real.sin t≤113/200 ∧ (47/50)*t≤Real.sin t := by
  have ht2 := pow_le_pow_left₀ ht.1 ht.2 2
  have ht3 := mul_le_mul_of_nonneg_right ht2 ht.1
  have hc := cos_lower_two ht.1
  have hs := Real.sin_ge_sub_cube ht.1
  have hm := sine_monotone (subset_frame ht)
    (show (3/5:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) ht.2
  refine ⟨by nlinarith,by linarith [cap_trig.2.1],by nlinarith⟩

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
    nlinarith [cap_trig.1]
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
  have hcross : ((103/100)*r+Real.sin (3/5))*root r (Real.sin (3/5))<
      Real.sqrt qCap*r*Real.cos (3/5) := by
    nlinarith [mul_nonneg hleft0 hN.le]
  have hdiv := (lt_div_iff₀ hN).2 hcross
  linarith

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
  simp only [mixedBlock,V,phi,show -(N-P)=P-N by ring]
  ring

/-- The reserve is charged only against the actual common positive mass. -/
theorem same_reserve {R p q P N : ℝ}
    (hp : (3/5:ℝ)≤p) (hqp : q≤(5/3)*p)
    (hP : 0≤P) (hPN : P≤N) (hN : N≤3/5) :
    V R p q (N-P)+(3/100)*P≤mixedBlock R p q P N := by
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
    nlinarith
  have hpaid := mul_le_mul_of_nonneg_left hunit (show 0≤p by linarith)
  have hscale := mul_nonneg (sub_nonneg.mpr hp) hP
  have he := same_difference R p q P N
  nlinarith

end SquaresInCircles.Eight.TableFree.OrdinaryNegativeShortSlope
