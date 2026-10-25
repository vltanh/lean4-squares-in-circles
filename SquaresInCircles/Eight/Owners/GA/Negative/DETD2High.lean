module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Owners.GA.Negative.DEHighLateData
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowSeparated
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2SourceData
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2HighSplit

/-!
# Eight squares: the complete high-total negative-DE / positive-TD2 scalar exclusion

The
actual high coefficient family satisfies the shared third-derivative
domain. Each pure negative function therefore has its minimum at the
two intrinsic E endpoints, whose actual A/TD split bounds were proved
separately. The positive surplus and the common signed mass are then
rejoined, without changing any original angle or coefficient.
-/

section
/-!
## The late correlated radical derivative, with both coefficient lines

The first term uses the quartic certificate (`firstLog_upper`). The second term is bounded by the
monotonicity of its reciprocal bracket (`bracket_bounds`, `secondLog_upper`). The coefficient and
the angle stay correlated in the differentiated function (`total_derivative_upper`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape.Late
open Candidate Secondary PositiveAngularEnvelope
open NegativeAPositiveTD.SecantCoordinate

theorem mass_hasDerivAt (c x : ℝ) :
    HasDerivAt (mass c) (mass c x*firstLog c x) x := by
  have hA : (0:ℝ)<1+c^2 := by positivity
  have hn := radical_positive (A:=1+c^2) (x:=x) hA
  have hn2 := radical_square (A:=1+c^2) (x:=x) hA
  have h1 : HasDerivAt (fun y : ℝ => 1+y^2) (2*x) x :=
    ((hasDerivAt_pow 2 x).const_add 1).congr_deriv (by norm_num)
  have hu : HasDerivAt (fun y : ℝ => R*(1+c^2)*(1+y^2)^3) (R*(1+c^2)*(3*(1+x^2)^2*(2*x))) x :=
    ((h1.pow 3).const_mul (R*(1+c^2))).congr_deriv (by norm_num)
  have hv : HasDerivAt (fun y => (radical (1+c^2) y)^5)
      (5*(radical (1+c^2) x)^4*(x/radical (1+c^2) x)) x :=
    ((radical_hasDerivAt (x:=x) hA).pow 5).congr_deriv (by norm_num)
  have hd := hu.div hv (pow_ne_zero 5 hn.ne')
  have hf : mass c=fun y => R*(1+c^2)*(1+y^2)^3/(radical (1+c^2) y)^5 := rfl
  rw [hf]
  refine hd.congr_deriv ?_
  simp only [firstLog]
  generalize radical (1+c^2) x=N at hn hn2 ⊢
  have hx1 : (0:ℝ)<1+x^2 := by positivity
  calc _=R*(1+c^2)*(1+x^2)^2*x*(6*N^2-5*(1+x^2))/(N^5*N^2) := by
          field_simp
          ring
    _=R*(1+c^2)*(1+x^2)^2*x*(6*(1+c^2+x^2)-5*(1+x^2))/(N^5*(1+c^2+x^2)) := by rw [hn2]
    _=_ := by
          field_simp
          ring

theorem mass_monotone_angle (c : ℝ) {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    mass c x≤ mass c y := by
  have hm : MonotoneOn (mass c) (Icc x y) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun t _ => (mass_hasDerivAt c t).continuousAt.continuousWithinAt)
      (fun t _ => mass_hasDerivAt c t)
    intro t ht
    have ht0 : 0≤t := hx.trans ht.1.le
    have hh : 0≤firstLog c t := by dsimp [firstLog]; positivity
    exact mul_nonneg (mass_pos c t).le hh
  exact hm ⟨le_rfl,hxy⟩ ⟨hxy,le_rfl⟩ hxy

theorem total_upper (bt3 : Bool) {x : ℝ}
    (hx : x∈Icc (Real.tan (11/20:ℝ)) (Real.tan frameCap)) : total bt3 x<183/100 := by
  have hd := (domain hx).1
  have hc := coefficient_bounds bt3 hx
  have hmono := mass_antitone_coefficient
    (by norm_num : (0:ℝ)≤863/1000) hc.1 (by linarith [hd.1])
    (by nlinarith [pow_le_pow_left₀ (show 0≤x by linarith [hd.1]) hd.2 2] : 2*x^2≤3)
  have ht := mass_monotone_angle (863/1000) (by linarith [hd.1]) hd.2
  exact (hmono.trans ht).trans_lt rational_mass_endpoints.1

theorem firstLog_upper {c x : ℝ}
    (hc : c∈Icc (863/1000:ℝ) (909/1000))
    (hx : x∈Icc (613/1000:ℝ) (843/1000)) : firstLog c x<27/20 := by
  have hx0 : 0≤x := by linarith [hx.1]
  have hc0 : 0≤c := by linarith [hc.1]
  have hc2 : c^2≤827/1000 := by
    nlinarith [pow_le_pow_left₀ hc0 hc.2 2]
  have ha : 0<1+x^2 := by positivity
  have hd : 0<1+x^2+c^2 := by positivity
  have hD : 0<1+x^2+827/1000 := by positivity
  have hcompare : firstLog c x≤
      x*(1+x^2+6*(827/1000))/((1+x^2)*(1+x^2+827/1000)) := by
    unfold firstLog
    apply (div_le_div_iff₀ (mul_pos ha hd) (mul_pos ha hD)).2
    have hprod := mul_nonneg (show 0≤5*x*(1+x^2)^2 by positivity)
      (sub_nonneg.mpr hc2)
    nlinarith only [hprod]
  have hpoly := Certificate.late_fraction_lower hx
  have hupper : x*(1+x^2+6*(827/1000))/((1+x^2)*(1+x^2+827/1000))<27/20 := by
    apply (div_lt_iff₀ (mul_pos ha hD)).2
    linarith
  exact hcompare.trans_lt hupper

theorem bracket_hasDerivAt (c x : ℝ) :
    HasDerivAt (fun c => bracket c x)
      (2*c*(2*(1+x^2+c^2)^2-5*(1+c^2)^2)/
        ((1+x^2+c^2)^2*(1+c^2)^2)) c := by
  have h1 : HasDerivAt (fun c : ℝ => 1+x^2+c^2) (2*c) c :=
    ((hasDerivAt_pow 2 c).const_add (1+x^2)).congr_deriv (by norm_num)
  have h2 : HasDerivAt (fun c : ℝ => 1+c^2) (2*c) c :=
    ((hasDerivAt_pow 2 c).const_add 1).congr_deriv (by norm_num)
  have hd := ((hasDerivAt_const c (5:ℝ)).div h1 (by positivity)).sub
    ((hasDerivAt_const c (2:ℝ)).div h2 (by positivity))
  have hf : (fun c => bracket c x)=fun c : ℝ => 5/(1+x^2+c^2)-2/(1+c^2) := rfl
  rw [hf]
  refine hd.congr_deriv ?_
  field_simp
  ring

theorem bracket_antitone_coefficient {c x : ℝ}
    (hc : c∈Icc (863/1000:ℝ) (909/1000))
    (hx : x∈Icc (613/1000:ℝ) (843/1000)) :
    bracket c x≤bracket (863/1000) x := by
  have hx2 := pow_le_pow_left₀ (show 0≤x by linarith [hx.1]) hx.2 2
  have hm : AntitoneOn (fun c => bracket c x) (Icc (863/1000:ℝ) c) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun v _ => (bracket_hasDerivAt v x).continuousAt.continuousWithinAt)
      (fun v _ => bracket_hasDerivAt v x)
    intro v hv
    have hv0 : 0≤v := by linarith [hv.1]
    have hv2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤863/1000) hv.1.le 2
    have hcomparison : 1+x^2+v^2≤(3/2)*(1+v^2) := by nlinarith
    have hsquare := pow_le_pow_left₀ (by positivity : 0≤1+x^2+v^2) hcomparison 2
    have hnum : 2*(1+x^2+v^2)^2-5*(1+v^2)^2≤0 := by
      nlinarith [sq_nonneg (1+v^2)]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) hnum) (by positivity)
  exact hm ⟨le_rfl,hc.1⟩ ⟨hc.1,le_rfl⟩ hc.1

theorem bracket_bounds {c x : ℝ}
    (hc : c∈Icc (863/1000:ℝ) (909/1000))
    (hx : x∈Icc (613/1000:ℝ) (843/1000)) :
    0≤bracket c x ∧ bracket c x≤bracket (863/1000) (613/1000) := by
  have hx0 : 0≤x := by linarith [hx.1]
  have hxl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤613/1000) hx.1 2
  have hxu := pow_le_pow_left₀ hx0 hx.2 2
  constructor
  · unfold bracket
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (by positivity : 0<1+c^2) (by positivity : 0<1+x^2+c^2)).2
    nlinarith [sq_nonneg c]
  · have hangle : bracket (863/1000) x≤bracket (863/1000) (613/1000) := by
      have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤5)
        (by norm_num : (0:ℝ)<1+(613/1000)^2+(863/1000)^2)
        (show 1+(613/1000:ℝ)^2+(863/1000:ℝ)^2≤1+x^2+(863/1000:ℝ)^2 by linarith)
      exact sub_le_sub_right hh _
    exact (bracket_antitone_coefficient hc hx).trans hangle

theorem secondLog_upper (bt3 : Bool) {c x : ℝ}
    (hc : c∈Icc (863/1000:ℝ) (909/1000))
    (hx : x∈Icc (613/1000:ℝ) (843/1000)) : secondLog bt3 c x<63/250 := by
  have hc0 : 0≤c := by linarith [hc.1]
  have hxl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤613/1000) hx.1 2
  have hnum := mul_le_mul (rate_bounds bt3).2 hc.2 hc0 (by norm_num : (0:ℝ)≤61/200)
  have hcoef : rate bt3*c/(1+x^2)≤
      ((61/200:ℝ)*(909/1000))/(1+(613/1000:ℝ)^2) :=
    div_le_div₀ (by norm_num) hnum (by norm_num) (by linarith)
  have hb := bracket_bounds hc hx
  have hh := mul_le_mul hcoef hb.2 hb.1 (by norm_num)
  have hfinal : (((61/200:ℝ)*(909/1000))/(1+(613/1000:ℝ)^2))*
      bracket (863/1000) (613/1000)<63/250 := by norm_num [bracket]
  exact hh.trans_lt hfinal

theorem total_hasDerivAt (bt3 : Bool) (x : ℝ) :
    HasDerivAt (total bt3) (totalFirst bt3 x) x := by
  have hk := coefficient_hasDerivAt bt3 x
  have hx2 : HasDerivAt (fun y : ℝ => y^2) (2*x) x := (hasDerivAt_pow 2 x).congr_deriv (by norm_num)
  have hP : HasDerivAt (fun y => 1+(coefficient bt3 y)^2)
      (2*coefficient bt3 x*(-rate bt3/(1+x^2))) x :=
    ((hk.pow 2).const_add 1).congr_deriv (by norm_num)
  have hQ : HasDerivAt (fun y : ℝ => (1+y^2)^3) (3*(1+x^2)^2*(2*x)) x :=
    ((hx2.const_add 1).pow 3).congr_deriv (by norm_num)
  have hS := hP.add hx2
  have hSpos : 0<1+(coefficient bt3 x)^2+x^2 := by positivity
  have hroot := hS.sqrt hSpos.ne'
  have hNpos : 0<Real.sqrt (1+(coefficient bt3 x)^2+x^2) := Real.sqrt_pos.mpr hSpos
  have hden : HasDerivAt (fun y => (Real.sqrt (1+(coefficient bt3 y)^2+y^2))^5)
      (5*(Real.sqrt (1+(coefficient bt3 x)^2+x^2))^4*
        ((2*coefficient bt3 x*(-rate bt3/(1+x^2))+2*x)/
          (2*Real.sqrt (1+(coefficient bt3 x)^2+x^2)))) x :=
    (hroot.pow 5).congr_deriv (by norm_num)
  have hnum := (hP.mul hQ).const_mul R
  have hd := hnum.div hden (pow_ne_zero 5 hNpos.ne')
  have hf : total bt3=fun y => R*((1+(coefficient bt3 y)^2)*(1+y^2)^3)/
      (Real.sqrt (1+(coefficient bt3 y)^2+y^2))^5 := by
    funext y
    simp only [total,mass,radical]
    ring
  rw [hf]
  refine hd.congr_deriv ?_
  simp only [totalFirst,total,mass,firstLog,secondLog,bracket,radical,Pi.mul_apply]
  have hN2 := Real.sq_sqrt hSpos.le
  generalize Real.sqrt (1+(coefficient bt3 x)^2+x^2)=N at hNpos hN2 ⊢
  generalize coefficient bt3 x=c at hN2 ⊢
  have hx1 : (0:ℝ)<1+x^2 := by positivity
  have hc1 : (0:ℝ)<1+c^2 := by positivity
  calc _=R*(1+x^2)^2*(2*c*(-rate bt3/(1+x^2))*(1+x^2)*N^2+6*x*(1+c^2)*N^2-
          5*(1+c^2)*(1+x^2)*(c*(-rate bt3/(1+x^2))+x))/(N^5*N^2) := by
          field_simp
          ring
    _=R*(1+x^2)^2*(2*c*(-rate bt3/(1+x^2))*(1+x^2)*(1+c^2+x^2)+6*x*(1+c^2)*(1+c^2+x^2)-
          5*(1+c^2)*(1+x^2)*(c*(-rate bt3/(1+x^2))+x))/(N^5*(1+c^2+x^2)) := by rw [hN2]
    _=_ := by
          field_simp
          ring

theorem total_derivative_upper (bt3 : Bool) {x : ℝ}
    (hx : x∈Icc (Real.tan (11/20:ℝ)) (Real.tan frameCap)) : totalFirst bt3 x<3 := by
  have hc := coefficient_bounds bt3 hx
  have hd := (domain hx).1
  have hfirst := firstLog_upper hc hd
  have hsecond := secondLog_upper bt3 hc hd
  have htotal := total_upper bt3 hx
  have hpos : 0<total bt3 x := mass_pos _ _
  have hh := mul_le_mul_of_nonneg_left
    (show firstLog (coefficient bt3 x) x+secondLog bt3 (coefficient bt3 x) x≤
      27/20+63/250 by linarith) hpos.le
  dsimp [totalFirst]
  nlinarith

end SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape.Late
end
end
end

section
/-!
## The strict late-range reserve in the high-DE third derivative

The reserve decreases on the late interval (`reserve_antitone`) and is positive at its right end
`tan frameCap` (`reserve_cap`). When the ordinary numerator polynomial is negative its coefficient
is bounded by one; when it is nonnegative the positive secant third derivative is used
(`baseThird_positive`). Both signs and their common zero are covered (`combined_positive`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape.Late
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

end SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape.Late
end
end
end

section
/-!
## The complete high-DE shape argument on the actual tangent interval

The early
and late estimates are joined at the original angle .55. The early
split at 3x^2=1 is the sign split of the exact derivative formula.
No subdivision of the original geometric angle domain is introduced.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape
open Candidate Secondary PositiveAngularEnvelope
open NegativeAPositiveTD.SecantCoordinate

/-- The original coefficient domain sufficient for either high-DE family.
The correlation and the upper ordinary coefficient are needed only when
the original total reaches the late interval. -/
structure Domain (bt3 : Bool) (c p q θ : ℝ) : Prop where
  total : θ∈Icc 0 frameCap
  coefficient : c∈Icc 0 Early.C
  smaller_pos : 0<p
  ordered : p≤q
  ratio : (2/3)*q≤p
  larger_lower : (431/500:ℝ)<q
  late_correlation : (11/20:ℝ)≤θ → c≤863/1000+Late.rate bt3*(frameCap-θ)
  late_larger : (11/20:ℝ)≤θ → q≤1

theorem early_positive {c p q θ x : ℝ} (bt3 : Bool)
    (H : Domain bt3 c p q θ) (hx : x∈Icc 0 (Real.tan θ))
    (hearly : x≤Real.tan (11/20:ℝ)) :
    0<baseThird c x+numerator p q (θ-Real.arctan x) x/(1+x^2)^3 := by
  have hs := arctan_interval H.total hx
  have hd : θ-Real.arctan x∈Icc 0 frameCap :=
    ⟨by linarith [hs.2],by linarith [H.total.2,hs.1]⟩
  have hxmax : x≤307/500 := hearly.trans TrigonometricBounds.transition.2.le
  have hbase := Early.lower H.coefficient
    (show x∈Icc (0:ℝ) (3/4) from ⟨hx.1,by linarith⟩)
  have hden : 0<(1+x^2)^3 := by positivity
  have hq := H.smaller_pos.trans_le H.ordered
  have hqp : q≤2*p := by linarith [H.ratio]
  have hnum : (6/25)*(1+x^2)^3<numerator p q (θ-Real.arctan x) x := by
    by_cases hsign : 3*x^2≤1
    · have hn := numerator_early_low H.smaller_pos H.ordered H.ratio hd hx.1 hsign
      have hD : (1+x^2)^3≤(64/27:ℝ) := by
        have hh := pow_le_pow_left₀ (by positivity : 0≤1+x^2)
          (show 1+x^2≤(4/3:ℝ) by linarith) 3
        norm_num at hh
        exact hh
      nlinarith [H.larger_lower]
    · have hxlower : (577/1000:ℝ)<x := by
        by_contra h
        have h2 : x^2≤(577/1000)^2 := pow_le_pow_left₀ hx.1 (le_of_not_gt h) 2
        linarith
      have hslow : (523/1000:ℝ)≤Real.arctan x := by
        by_contra hh
        have hstan := tan_monotone
          (show Real.arctan x∈Icc 0 frameCap from ⟨hs.1,hs.2.trans H.total.2⟩)
          (show (523/1000:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
          (lt_of_not_ge hh).le
        rw [Real.tan_arctan] at hstan
        linarith [TrigonometricBounds.middle_left]
      have hdshort : θ-Real.arctan x∈Icc (0:ℝ) (177/1000) :=
        ⟨hd.1,by
          have ht2 := H.total.2
          simp only [frameCap] at ht2
          linarith⟩
      have hn := numerator_early_middle H.smaller_pos H.ordered hqp hdshort
        ⟨hx.1,hxmax⟩ (lt_of_not_ge hsign).le
      have hx2 := pow_le_pow_left₀ hx.1 hxmax 2
      have hD := pow_le_pow_left₀ (by positivity : 0≤1+x^2)
        (show 1+x^2≤1+(307/500:ℝ)^2 by linarith) 3
      norm_num at hD
      nlinarith [H.larger_lower]
  have hquot : (6/25:ℝ)<numerator p q (θ-Real.arctan x) x/(1+x^2)^3 :=
    (lt_div_iff₀ hden).2 hnum
  linarith

theorem third_positive {c p q θ x : ℝ} (bt3 : Bool)
    (H : Domain bt3 c p q θ) (hx : x∈Icc 0 (Real.tan θ)) :
    0<pureThird 1 c p q θ x := by
  have hs := arctan_interval H.total hx
  by_cases hearly : x≤Real.tan (11/20:ℝ)
  · simpa only [pureThird,one_mul] using early_positive bt3 H hx hearly
  · have hlate : x∈Icc (Real.tan (11/20:ℝ)) (Real.tan frameCap) :=
      ⟨(lt_of_not_ge hearly).le,hx.2.trans
        (tan_monotone H.total (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) H.total.2)⟩
    have hsd := (Late.domain hlate).2
    have hθlate : (11/20:ℝ)≤θ := hsd.1.trans hs.2
    have hcorrelation : c≤Late.coefficient bt3 x := by
      have hm := mul_le_mul_of_nonneg_left
        (show frameCap-θ≤frameCap-Real.arctan x by linarith [hs.2]) (Late.rate_bounds bt3).1
      dsimp [Late.coefficient]
      linarith [H.late_correlation hθlate]
    have hd : θ-Real.arctan x∈Icc (0:ℝ) (3/20) :=
      ⟨by linarith [hs.2],by
        have ht2 := H.total.2
        simp only [frameCap] at ht2
        linarith [hsd.1]⟩
    have hh := Late.combined_positive bt3 H.smaller_pos H.ordered
      (show q≤2*p by linarith [H.ratio,H.smaller_pos]) (H.late_larger hθlate)
      H.coefficient.1 hcorrelation hd hlate
    simpa only [pureThird,one_mul] using hh

/-- A convex first derivative which is nonpositive at its right endpoint
makes the original function attain its minimum at an endpoint. -/
theorem endpoint_of_convex_first {f u : ℝ→ℝ} {t s : ℝ}
    (ht : 0≤t) (hs : s∈Icc 0 t)
    (hf : ∀x∈Icc 0 t,HasDerivAt f (u x) x)
    (hu : ConcaveOn ℝ (Icc 0 t) (fun x => -u x)) (hut : u t≤0) :
    min (f 0) (f t)≤f s := by
  have hright {a b : ℝ} (ha : a∈Icc 0 t) (hb : b∈Icc a t)
      (hderiv : u a≤0) : u b≤0 := by
    have hh := hu.min_le_of_mem_Icc ha ⟨ht,le_rfl⟩ hb
    have hlo : 0≤ min (-u a) (-u t) := le_min (by linarith) (by linarith)
    linarith
  by_cases hsign : u s≤0
  · have hm : AntitoneOn f (Icc s t) := by
      apply antiOn_of_hasDeriv_nonpos
      · intro x hx
        exact (hf x ⟨hs.1.trans hx.1,hx.2⟩).continuousAt.continuousWithinAt
      · intro x hx
        exact hf x ⟨hs.1.trans hx.1.le,hx.2.le⟩
      · intro x hx
        exact hright hs (Ioo_subset_Icc_self hx) hsign
    exact (min_le_right _ _).trans (hm ⟨le_rfl,hs.2⟩ ⟨hs.2,le_rfl⟩ hs.2)
  · have hm : MonotoneOn f (Icc 0 s) := by
      apply monoOn_of_hasDeriv_nonneg
      · intro x hx
        exact (hf x ⟨hx.1,hx.2.trans hs.2⟩).continuousAt.continuousWithinAt
      · intro x hx
        exact hf x ⟨hx.1.le,hx.2.le.trans hs.2⟩
      · intro x hx
        by_contra hh
        have hnon : u x≤0 := (lt_of_not_ge hh).le
        exact hsign (hright ⟨hx.1.le,hx.2.le.trans hs.2⟩ ⟨hx.2.le,hs.2⟩ hnon)
    exact (min_le_left _ _).trans (hm ⟨le_rfl,hs.1⟩ ⟨hs.1,le_rfl⟩ hs.1)

/-- Both original high-DE coefficient families have the same two intrinsic
secant-coordinate endpoints once their right derivative is nonpositive. -/
theorem pure_endpoint_minimum {B c p q θ x : ℝ} (bt3 : Bool)
    (H : Domain bt3 c p q θ) (hx : x∈Icc 0 (Real.tan θ))
    (hright : pureFirst 1 c p q θ (Real.tan θ)≤0) :
    min (pure B 1 c p q θ 0) (pure B 1 c p q θ (Real.tan θ))≤
      pure B 1 c p q θ x := by
  have hd {x : ℝ} (hx : x∈Icc 0 (Real.tan θ)) : θ-Real.arctan x∈Icc 0 frameCap := by
    have hs := arctan_interval H.total hx
    exact ⟨by linarith [hs.2],by linarith [hs.1,H.total.2]⟩
  have hq := H.smaller_pos.trans_le H.ordered
  have hconvex : ConcaveOn ℝ (Icc 0 (Real.tan θ))
      (fun x => -pureFirst 1 c p q θ x) := by
    apply concave_of_deriv2
      (fun x hx => (pureFirst_hasDerivAt H.smaller_pos hq (hd hx)).neg)
      (fun x hx => (pureSecond_hasDerivAt H.smaller_pos hq (hd hx)).neg)
    intro x hx
    linarith [third_positive bt3 H hx]
  exact endpoint_of_convex_first (tan_nonnegative H.total) hx
    (fun x hx => pure_hasDerivAt H.smaller_pos hq (hd hx)) hconvex hright

end SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.High
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open NegativeAPositiveTD.SecantCoordinate

/-- Concrete coefficient hypotheses, including the original late correlation. -/
theorem shape_domain {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (i : Fin 3) :
    NegativeDEHighShape.Domain false (Explicit.c .high θ)
      (Explicit.p .high θ z i) (Explicit.q .high θ z i) θ := by
  have hc := Explicit.high_ranges hθ
  have hp := Explicit.high_pairs hθ hz i
  refine ⟨⟨by linarith [hθ.1],hθ.2⟩,?_,hp.1,hp.2.1,
    hp.2.2.1.le,?_,?_,?_⟩
  · constructor
    · linarith [hc.2.2.2.2.1]
    · dsimp [NegativeDEHighShape.Early.C]
      linarith [hc.2.2.2.2.2.1]
  · linarith [hp.2.2.2.1]
  · intro _
    dsimp [NegativeDEHighShape.Late.rate,frameCap]
    linarith [hc.2.2.2.2.2.2.2]
  · intro hlate
    exact Explicit.high_late_q_le_one hθ hz hlate i

theorem negative_endpoint_minimum {a z s : ℝ}
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 (a+z)) (i : Fin 3) :
    min (Explicit.fullBaseline .high a z 0+Explicit.V .high (a+z) z i (a+z))
        (Explicit.fullBaseline .high a z (a+z))≤
      Explicit.fullBaseline .high a z s+Explicit.V .high (a+z) z i (a+z-s) := by
  have hf : a+z∈Icc 0 frameCap := ⟨by linarith [hθ.1],hθ.2⟩
  have hzf : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans hf.2⟩
  have hx : Real.tan s∈Icc 0 (Real.tan (a+z)) :=
    ⟨tan_nonnegative hsf,tan_monotone hsf hf hs.2⟩
  have hh := NegativeDEHighShape.pure_endpoint_minimum
    (B:=Explicit.fullBaseline .high a z 0) false (shape_domain hθ hzf i) hx
    (HighDerivative.high_pure_first_right_negative hθ hzf i).le
  have hleft : pure (Explicit.fullBaseline .high a z 0) 1
      (Explicit.c .high (a+z)) (Explicit.p .high (a+z) z i)
      (Explicit.q .high (a+z) z i) (a+z) 0=
        Explicit.fullBaseline .high a z 0+Explicit.V .high (a+z) z i (a+z) := by
    simp only [NegativeAPositiveTD.SecantCoordinate.pure,Explicit.V,Real.arctan_zero,sub_zero,
      sub_self,mul_zero,add_zero]
  have hright := HighSecant.pure_at_original (a:=a) (z:=z) hf i
  simp only [sub_self,Explicit.V,V_zero,add_zero] at hright
  rw [hleft,hright,HighSecant.pure_at_original hsf i] at hh
  exact hh

theorem negative_positive {a z s : ℝ}
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 (a+z)) (i : Fin 3) :
    0<Explicit.fullBaseline .high a z s+Explicit.V .high (a+z) z i (a+z-s) := by
  have h0 := HighSplit.original_pure_at_zero_positive hθ ha hz i
  have h1 := HighSplit.original_equal_positive hθ ha hz
  exact (lt_min h0 h1).trans_le (negative_endpoint_minimum hθ ha hz hs i)

theorem pure_positive {a z s : ℝ}
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 frameCap) (i : Fin 3) :
    0<Explicit.fullBaseline .high a z s+HighConcentration.pure (a+z) z s i := by
  by_cases horder : s≤a+z
  · simpa only [HighConcentration.pure,ite_eq_left horder] using
      negative_positive hθ ha hz ⟨hs.1,horder⟩ i
  · have hθs : a+z≤ s := (lt_of_not_ge horder).le
    have hcompare := HighSecant.high_equal_le_positive_surplus hθ
      (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩) ⟨hθs,hs.2⟩ i
    simpa only [HighConcentration.pure,ite_eq_right horder] using
      (HighSplit.original_equal_positive hθ ha hz).trans_le hcompare

/-- Every original high-total allocation has strictly positive scalar
stress; no endpoint-minimum or derivative premise remains. -/
theorem scalar_positive {a z s : ℝ} (P N : Fin 3→ℝ)
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 frameCap) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.fullBaseline .high a z s+
      ∑i,mixedBlock R (Explicit.p .high (a+z) z i)
        (Explicit.q .high (a+z) z i) (P i) (N i) := by
  obtain ⟨i,hi⟩ := HighConcentration.sum_to_pure P N hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩) hs hP hN hPb hNb hbalance
  have hp := pure_positive hθ ha hz hs i
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.High
end
end
end
