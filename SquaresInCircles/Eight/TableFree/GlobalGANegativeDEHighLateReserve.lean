module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEHighLateDerivative

/-!
# The strict late-range reserve in the high-DE third derivative

Uncompiled completion of the correlated H comparison. H decreases on
the original late interval and is positive at tan(h). When the ordinary
numerator polynomial is negative its coefficient is bounded by one;
when it is nonnegative the independently proved positive secant third
derivative is used. Both signs and their common zero are retained.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEHighShape.Late
open Candidate Secondary PositiveAngularEnvelope
open NegativeAPositiveTD.SecantCoordinate

def reserveFirst (bt3 : Bool) (x : ℝ) : ℝ :=
  3*(total bt3 x-radical 1 x)+3*x*(totalFirst bt3 x-x/radical 1 x)+9/5-(84/5)*x

theorem reserve_hasDerivAt (bt3 : Bool) (x : ℝ) :
    HasDerivAt (reserve bt3) (reserveFirst bt3 x) x := by
  have h1 : HasDerivAt (fun y => total bt3 y-radical 1 y) (totalFirst bt3 x-x/radical 1 x) x :=
    (total_hasDerivAt bt3 x).sub (radical_hasDerivAt (A:=1) (by norm_num))
  have h2 : HasDerivAt (fun y : ℝ => 3*y) 3 x :=
    ((hasDerivAt_id' x).const_mul (3:ℝ)).congr_deriv (by norm_num)
  have h3 : HasDerivAt (fun y : ℝ => 47/15+(9/5)*y-(42/5)*y^2) (9/5-(42/5)*(2*x)) x :=
    ((((hasDerivAt_id' x).const_mul (9/5:ℝ)).const_add (47/15:ℝ)).sub
      ((hasDerivAt_pow 2 x).const_mul (42/5:ℝ))).congr_deriv (by norm_num)
  have hd := (h2.mul h1).add h3
  have hf : reserve bt3=fun y => 3*y*(total bt3 y-radical 1 y)+(47/15+(9/5)*y-(42/5)*y^2) := by
    funext y
    simp only [reserve,latePolynomial]
  rw [hf]
  exact hd.congr_deriv (by simp only [reserveFirst]; ring)

theorem radical_bounds {x : ℝ} (hx : x∈Icc (613/1000:ℝ) (843/1000)) :
    (117/100:ℝ)<radical 1 x ∧ (13/25:ℝ)<x/radical 1 x := by
  have hw := radical_positive (A:=1) (x:=x) (by norm_num)
  have hw2 := radical_square (A:=1) (x:=x) (by norm_num)
  have hx2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤613/1000) hx.1 2
  constructor
  · nlinarith
  · apply (lt_div_iff₀ hw).2
    nlinarith [hx.1]

theorem reserve_derivative_upper (bt3 : Bool) {x : ℝ}
    (hx : x∈Icc (Real.tan (11/20:ℝ)) (Real.tan frameCap)) :
    reserveFirst bt3 x< -(6/25:ℝ) := by
  have hd := (domain hx).1
  have hw := radical_bounds hd
  have hT := total_upper bt3 hx
  have hD := total_derivative_upper bt3 hx
  have hx0 : 0≤x := by linarith [hd.1]
  have hprod := mul_le_mul_of_nonneg_left
    (show totalFirst bt3 x-x/radical 1 x≤62/25 by linarith) (show 0≤3*x by positivity)
  dsimp [reserveFirst]
  nlinarith [hd.1,hd.2]

theorem reserve_antitone (bt3 : Bool) :
    AntitoneOn (reserve bt3) (Icc (Real.tan (11/20:ℝ)) (Real.tan frameCap)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun x _ => (reserve_hasDerivAt bt3 x).continuousAt.continuousWithinAt)
    (fun x _ => reserve_hasDerivAt bt3 x)
  intro x hx
  linarith [reserve_derivative_upper bt3 (Ioo_subset_Icc_self hx)]

theorem total_cap_lower (bt3 : Bool) :
    (182777/100000:ℝ)<total bt3 (Real.tan frameCap) := by
  rw [total,coefficient_cap]
  exact rational_mass_endpoints.2.trans_le
    (mass_monotone_angle (863/1000) (by norm_num) TrigonometricBounds.cap.1.le)

theorem reserve_cap (bt3 : Bool) : (47/10000:ℝ)<reserve bt3 (Real.tan frameCap) := by
  have ht := TrigonometricBounds.cap
  have hmass := total_cap_lower bt3
  have hw : radical 1 (Real.tan frameCap)<65373/50000 := by
    rw [TrigonometricBounds.radical_tan (show frameCap∈Icc 0 frameCap by norm_num [frameCap])]
    exact ht.2.2
  have hx0 : 0≤Real.tan frameCap := by linarith [ht.1]
  have hx2 := pow_le_pow_left₀ hx0 ht.2.1.le 2
  have hgap : (52031/100000:ℝ)<total bt3 (Real.tan frameCap)-radical 1 (Real.tan frameCap) := by
    linarith
  have hprod := mul_lt_mul'' ht.1 hgap (by norm_num) (by norm_num)
  dsimp [reserve,latePolynomial]
  nlinarith

theorem reserve_positive (bt3 : Bool) {x : ℝ}
    (hx : x∈Icc (Real.tan (11/20:ℝ)) (Real.tan frameCap)) : 0<reserve bt3 x := by
  have hh := reserve_antitone bt3 hx ⟨hx.1.trans hx.2,le_rfl⟩ hx.2
  linarith [reserve_cap bt3]

/-- The positive-square comparison at x=.613, c=.909, propagated in x. -/
theorem upper_coefficient_positive {x : ℝ} (hx : (613/1000:ℝ)≤x) :
    0<baseThird (909/1000) x := by
  let c : ℝ := 909/1000
  let a : ℝ := 1+x^2
  let a0 : ℝ := 1+(613/1000:ℝ)^2
  let w := radical 1 x
  let n := radical (1+c^2) x
  have hw : 0<w := radical_positive (by norm_num : (0:ℝ)<1)
  have hn : 0<n := radical_positive (by positivity : 0<1+c^2)
  have hw2 : w^2=a := radical_square (by norm_num : (0:ℝ)<1)
  have hn2 : n^2=a+c^2 := by
    have hh := radical_square (A:=1+c^2) (x:=x) (by positivity)
    dsimp [a]
    nlinarith only [hh]
  have ha : 0<a := by dsimp [a]; positivity
  have ha0 : 0<a0 := by norm_num [a0]
  have hal : a0≤a := by
    dsimp [a0,a]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤613/1000) hx 2]
  have hfrac := div_le_div_of_nonneg_left (sq_nonneg c) ha0 hal
  have hratio : n^2/a≤(a0+c^2)/a0 := by
    rw [hn2]
    have h₁ : (a+c^2)/a=1+c^2/a := by field_simp [ha.ne']
    have h₂ : (a0+c^2)/a0=1+c^2/a0 := by field_simp [ha0.ne']
    rw [h₁,h₂]
    linarith
  have hpow := pow_le_pow_left₀ (div_nonneg (sq_nonneg n) ha.le) hratio 5
  have hpow' : n^10≤((a0+c^2)/a0)^5*a^5 := by
    rw [div_pow,←pow_mul,show (2:ℕ)*5=10 by norm_num] at hpow
    exact (div_le_iff₀ (pow_pos ha 5)).1 hpow
  have htest : ((a0+c^2)/a0)^5<qCap*(1+c^2)^2 := by
    norm_num [a0,c,qCap]
  have hstrict := mul_lt_mul_of_pos_right htest (pow_pos ha 5)
  have hw10 : w^10=a^5 := by
    rw [show (10:ℕ)=2*5 by norm_num,pow_mul,hw2]
  have hnum : (R*(1+c^2)*w^5)^2=qCap*(1+c^2)^2*a^5 := by
    rw [mul_pow,mul_pow,radius_sq]
    rw [←pow_mul,show (5:ℕ)*2=10 by norm_num,hw10]
  have hR : 0<R := Real.sqrt_pos.mpr (by norm_num [qCap])
  have hcross : n^5<R*(1+c^2)*w^5 := by
    have hnp : 0<R*(1+c^2)*w^5 := by positivity
    have hn10 : (n^5)^2=n^10 := by ring
    apply lt_of_pow_lt_pow_left₀ 2 hnp.le
    rw [hn10,hnum]
    exact hpow'.trans_lt hstrict
  have hquot : 1/w^5<R*(1+c^2)/n^5 := by
    apply (div_lt_div_iff₀ (pow_pos hw 5) (pow_pos hn 5)).2
    simpa only [one_mul] using hcross
  have hx0 : 0<x := by linarith
  change 0<3*x*(R*(1+c^2)/n^5-1/w^5)
  exact mul_pos (by positivity) (sub_pos.mpr hquot)

theorem baseThird_positive {c x : ℝ} (hc : c∈Icc (0:ℝ) (909/1000))
    (hx : x∈Icc (613/1000:ℝ) (843/1000)) : 0<baseThird c x := by
  have hm := baseThird_antitone_parameter hc.1 hc.2 (by linarith [hx.1])
    (by nlinarith [pow_le_pow_left₀ (show 0≤x by linarith [hx.1]) hx.2 2] : 2*x^2≤3)
  exact (upper_coefficient_positive hx.1).trans_le hm

/-- The late shape comparison includes both signs of the ordinary polynomial. -/
theorem combined_positive (bt3 : Bool) {c p q d x : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hq : q≤1)
    (hc : 0≤c) (hcorrelation : c≤coefficient bt3 x)
    (hd : d∈Icc (0:ℝ) (3/20))
    (hx : x∈Icc (Real.tan (11/20:ℝ)) (Real.tan frameCap)) :
    0<baseThird c x+numerator p q d x/(1+x^2)^3 := by
  have hxd := (domain hx).1
  have hcc := coefficient_bounds bt3 hx
  have hq0 := hp.trans_le hpq
  have hn := numerator_late hp hpq hqp hd hxd.1
  have hpositive := baseThird_positive ⟨hc,hcorrelation.trans hcc.2⟩ hxd
  have hden : 0<(1+x^2)^3 := by positivity
  by_cases hsign : 0≤latePolynomial x
  · have hnum : 0≤numerator p q d x :=
      (mul_nonneg hq0.le hsign).trans hn
    exact add_pos_of_pos_of_nonneg hpositive (div_nonneg hnum hden.le)
  · have hqM := mul_le_mul_of_nonpos_right hq (le_of_not_ge hsign)
    have hbase := baseThird_antitone_parameter hc hcorrelation (by linarith [hxd.1])
      (by nlinarith [pow_le_pow_left₀ (show 0≤x by linarith [hxd.1]) hxd.2 2] : 2*x^2≤3)
    have hscaled := mul_le_mul_of_nonneg_left hbase hden.le
    rw [mass_identity] at hscaled
    have hH := reserve_positive bt3 hx
    dsimp [reserve,total] at hH
    have hprod : 0<(1+x^2)^3*baseThird c x+numerator p q d x := by
      simp only [one_mul] at hqM
      linarith
    have hh := div_pos hprod hden
    have he : ((1+x^2)^3*baseThird c x+numerator p q d x)/(1+x^2)^3=
        baseThird c x+numerator p q d x/(1+x^2)^3 := by
      field_simp [hden.ne']
    rwa [he] at hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEHighShape.Late
