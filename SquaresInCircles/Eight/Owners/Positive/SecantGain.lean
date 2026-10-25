module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.SecantGainPolynomial
public import SquaresInCircles.Eight.Words.Short.SecantGain

/-!
# Eight squares: the uniform common secant gain for actual negative primaries

The polynomial reserve is transferred through a proved
second-order radical bound to the original trigonometric gain. Monotonicity
then covers every actual q≤qCap and every coefficient at least .863.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveSecantGain
open GlobalGA PositiveStressCoefficients

/-- A positive-square proof of the second-order radical upper bound. -/
theorem sqrt_sub_upper {v u : ℝ} (hv : 0<v) (hu : 0≤u) (huv : u≤v^2) :
    Real.sqrt (v^2-u)≤v-u/(2*v)-u^2/(8*v^3) := by
  let m := v-u/(2*v)-u^2/(8*v^3)
  have hu2 := pow_le_pow_left₀ hu huv 2
  have hprod := mul_le_mul_of_nonneg_right huv (sq_nonneg v)
  have hmId : 8*v^3*m=8*v^4-4*u*v^2-u^2 := by
    dsimp [m]
    field_simp [hv.ne']
    ring
  have hm : 0< m := by
    have hv4 : 0<v^4 := pow_pos hv 4
    have hprodpos : 0<8*v^3*m := by nlinarith
    exact (mul_pos_iff_of_pos_left (by positivity : 0<8*v^3)).1 hprodpos
  have hid : m^2-(v^2-u)=u^3*(8*v^2+u)/(64*v^6) := by
    dsimp [m]
    field_simp [hv.ne']
    ring
  have hrest : 0≤u^3*(8*v^2+u)/(64*v^6) := by positivity
  have hsq := Real.sq_sqrt (sub_nonneg.mpr huv)
  have hs0 := Real.sqrt_nonneg (v^2-u)
  nlinarith

theorem coefficient_squares :
    qCap*(1+k^2)<(104551/40000 : ℝ)^2 ∧
      4*(111571/200000 : ℝ)^2*(1+k^2)<qCap*k^4 ∧
      64*(59531/1000000 : ℝ)^2*(1+k^2)^3<qCap*k^8 := by
  norm_num [qCap,k]

theorem radical_coefficients :
    Real.sqrt qCap*Real.sqrt (1+k^2)-1<64551/40000 ∧
      (111571/200000 : ℝ)<Real.sqrt qCap*k^2/(2*Real.sqrt (1+k^2)) ∧
      (59531/1000000 : ℝ)<Real.sqrt qCap*k^4/(8*(Real.sqrt (1+k^2))^3) := by
  have hR0 : 0<Real.sqrt qCap := Real.sqrt_pos.mpr (by norm_num [qCap])
  have hV0 : 0<Real.sqrt (1+k^2) := Real.sqrt_pos.mpr (by positivity)
  have hR := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hV := Real.sq_sqrt (show 0≤1+k^2 by positivity)
  have h1 : (Real.sqrt qCap*Real.sqrt (1+k^2))^2=qCap*(1+k^2) := by rw [mul_pow,hR,hV]
  have h2 : (Real.sqrt qCap*k^2)^2=qCap*k^4 := by rw [mul_pow,hR]; ring
  have h3 : (Real.sqrt qCap*k^4)^2=qCap*k^8 := by rw [mul_pow,hR]; ring
  have hD2 : (2*Real.sqrt (1+k^2)*(111571/200000 : ℝ))^2=
      4*(111571/200000 : ℝ)^2*(1+k^2) := by
    nlinarith [hV]
  have hV6 : (Real.sqrt (1+k^2))^6=(1+k^2)^3 := by
    rw [show (Real.sqrt (1+k^2))^6=((Real.sqrt (1+k^2))^2)^3 by ring,hV]
  have hD3 : (8*(Real.sqrt (1+k^2))^3*(59531/1000000 : ℝ))^2=
      64*(59531/1000000 : ℝ)^2*(1+k^2)^3 := by
    calc
      _ = 64*(59531/1000000 : ℝ)^2*(Real.sqrt (1+k^2))^6 := by ring
      _ = _ := by rw [hV6]
  refine ⟨?_,?_,?_⟩
  · have hm := mul_pos hR0 hV0
    have := lt_of_pow_lt_pow_left₀ 2 (by norm_num)
      (show (Real.sqrt qCap*Real.sqrt (1+k^2))^2<(104551/40000 : ℝ)^2 by
        rw [h1]; exact coefficient_squares.1)
    linarith
  · apply (lt_div_iff₀ (by positivity : 0<2*Real.sqrt (1+k^2))).2
    have hm : 0≤Real.sqrt qCap*k^2 := by positivity
    have := lt_of_pow_lt_pow_left₀ 2 hm
      (show (2*Real.sqrt (1+k^2)*(111571/200000 : ℝ))^2<(Real.sqrt qCap*k^2)^2 by
        rw [hD2,h2]; exact coefficient_squares.2.1)
    linarith
  · apply (lt_div_iff₀ (by positivity : 0<8*(Real.sqrt (1+k^2))^3)).2
    have hm : 0≤Real.sqrt qCap*k^4 := by positivity
    have := lt_of_pow_lt_pow_left₀ 2 hm
      (show (8*(Real.sqrt (1+k^2))^3*(59531/1000000 : ℝ))^2<(Real.sqrt qCap*k^4)^2 by
        rw [hD3,h3]; exact coefficient_squares.2.2)
    linarith

theorem radical_gain_lower {s : ℝ} (_hs : s∈Icc 0 frameCap) :
    (111571/200000)*(Real.sin s)^2+(59531/1000000)*(Real.sin s)^4≤
      Real.sqrt qCap*(Real.sqrt (1+k^2)-Real.sqrt (gainRadicand k s)) := by
  have hV := Real.sq_sqrt (show 0≤1+k^2 by positivity)
  have hV0 : 0<Real.sqrt (1+k^2) := Real.sqrt_pos.mpr (by positivity)
  have hu : 0≤k^2*(Real.sin s)^2 := by positivity
  have hsin2 : (Real.sin s)^2≤1 := by nlinarith [Real.sin_sq_add_cos_sq s,sq_nonneg (Real.cos s)]
  have huv : k^2*(Real.sin s)^2≤(Real.sqrt (1+k^2))^2 := by
    have hm := mul_le_mul_of_nonneg_left hsin2 (sq_nonneg k)
    nlinarith
  have hsqrt := sqrt_sub_upper hV0 hu huv
  have he : (Real.sqrt (1+k^2))^2-k^2*(Real.sin s)^2=gainRadicand k s := by
    rw [hV]
    dsimp [gainRadicand]
    linear_combination (-k^2)*(Real.sin_sq_add_cos_sq s)
  rw [he] at hsqrt
  have hm := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg qCap)
  have h2 := mul_le_mul_of_nonneg_right radical_coefficients.2.1.le (sq_nonneg (Real.sin s))
  have h4 := mul_le_mul_of_nonneg_right radical_coefficients.2.2.le (by positivity : (0:ℝ)≤(Real.sin s)^4)
  have hid : Real.sqrt qCap*(k^2*(Real.sin s)^2/(2*Real.sqrt (1+k^2)))=
      (Real.sqrt qCap*k^2/(2*Real.sqrt (1+k^2)))*(Real.sin s)^2 := by ring
  have hid2 : Real.sqrt qCap*((k^2*(Real.sin s)^2)^2/(8*(Real.sqrt (1+k^2))^3))=
      (Real.sqrt qCap*k^4/(8*(Real.sqrt (1+k^2))^3))*(Real.sin s)^4 := by ring
  nlinarith [hid,hid2]

theorem base_strict_gain {s : ℝ} (hs : s∈Ioc 0 frameCap) :
    (103/100)*s<secantGain qCap k s := by
  obtain ⟨hc,hc1,hs0,hsu,hsc⟩ := transport_trig (Ioc_subset_Icc_self hs)
  have hcpos : 0<Real.cos s := by linarith
  have hrad := radical_gain_lower (Ioc_subset_Icc_self hs)
  have hcoeff := mul_le_mul_of_nonneg_right radical_coefficients.1.le (sub_nonneg.mpr hc1)
  have htrig := SecantGainPolynomial.trigonometric_positive hs
  have hid : (secantGain qCap k s-(103/100)*s)*Real.cos s=
      (13/12)*Real.sin s-(103/100)*s*Real.cos s-
        (Real.sqrt qCap*Real.sqrt (1+k^2)-1)*(1-Real.cos s)+
          Real.sqrt qCap*(Real.sqrt (1+k^2)-Real.sqrt (gainRadicand k s)) := by
    dsimp [secantGain]
    field_simp [hcpos.ne']
    ring
  have hp : 0<(secantGain qCap k s-(103/100)*s)*Real.cos s := by rw [hid]; linarith
  have := (mul_pos_iff_of_pos_right hcpos).1 hp
  linarith

theorem norm_increment_antitone {a b w : ℝ} (ha : 0≤a) (hab : a≤b) (hw : 1≤w) :
    Real.sqrt (w^2+b^2)-Real.sqrt (1+b^2)≤
      Real.sqrt (w^2+a^2)-Real.sqrt (1+a^2) := by
  have hb : 0≤b := ha.trans hab
  have hab2 := pow_le_pow_left₀ ha hab 2
  have hw2 : 1≤w^2 := by nlinarith
  have hA := Real.sq_sqrt (show 0≤w^2+a^2 by positivity)
  have hB := Real.sq_sqrt (show 0≤1+a^2 by positivity)
  have hC := Real.sq_sqrt (show 0≤w^2+b^2 by positivity)
  have hD := Real.sq_sqrt (show 0≤1+b^2 by positivity)
  have hAB := Real.sqrt_le_sqrt (show 1+a^2≤w^2+a^2 by linarith)
  have hAC := Real.sqrt_le_sqrt (show w^2+a^2≤w^2+b^2 by linarith)
  have hBD := Real.sqrt_le_sqrt (show 1+a^2≤1+b^2 by linarith)
  have hsum := add_le_add hAC hBD
  have hmul := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hAB)
  have hden : 0<Real.sqrt (w^2+b^2)+Real.sqrt (1+b^2) := by positivity
  apply (mul_le_mul_iff_left₀ hden).mp
  nlinarith

/-- Smaller original radii and larger force coefficients only increase
the secant gain. -/
theorem gain_comparison {q a s : ℝ} (_hq : 0≤q) (hQ : q≤qCap)
    (ha : k≤a) (hs : s∈Icc 0 frameCap) :
    secantGain qCap k s≤ secantGain q a s := by
  have hc := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  have hcu := Real.cos_le_one s
  have hw : 1≤1/Real.cos s := (le_div_iff₀ hc).2 (by simpa using hcu)
  have hn := norm_increment_antitone (show 0≤k by norm_num [k]) ha hw
  have hR := Real.sqrt_le_sqrt hQ
  have ha0 : 0≤a := (show 0≤k by norm_num [k]).trans ha
  have hdelta : 0≤Real.sqrt ((1/Real.cos s)^2+a^2)-Real.sqrt (1+a^2) := by
    apply sub_nonneg.mpr
    apply Real.sqrt_le_sqrt
    nlinarith
  have hprod := mul_le_mul hR hn hdelta (Real.sqrt_nonneg qCap)
  rw [secantGain_eq_secant_expression qCap k hc,secantGain_eq_secant_expression q a hc]
  nlinarith

theorem strict_gain {q a s : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (ha : k≤a) (hs : s∈Ioc 0 frameCap) :
    (103/100)*s<secantGain q a s :=
  (base_strict_gain hs).trans_le (gain_comparison hq hQ ha (Ioc_subset_Icc_self hs))

theorem negative_TD_gain {q d t : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (hd : d∈Icc 0 frameCap) (ht : t∈Ioc 0 frameCap) :
    lambdaN d*t<cN d*secantGain q (1/cN d) t := by
  have hc0 : 0<cN d := by
    have hh := coefficient_bounds hd
    dsimp [cN,frameCap] at *
    nlinarith [hd.1,hd.2]
  have hcoeff := ShortSecantGain.negative_family_slopes hd
  have hg := mul_lt_mul_of_pos_left (strict_gain hq hQ hcoeff.2.2.2.1.le ht) hc0
  have hl := mul_lt_mul_of_pos_right hcoeff.2.1 ht.1
  nlinarith

end SquaresInCircles.Eight.PositiveSecantGain
