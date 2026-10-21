module

public import SquaresInCircles.Eight.TableFree.ExceptionalNegativeTTaylor
public import SquaresInCircles.Eight.TableFree.ExceptionalNegativeTStress
public import SquaresInCircles.Eight.TableFree.SoleNegativeTDSupport

/-!
# The sorted-D secant gain in the exceptional outside-strip proof

Uncompiled source. The original D is bounded by its sorted support at
the same q. The useful quadratic lower slope is obtained by the hand
proof's S7/C6/C4 identity. Its decreasing slope is used only up to the
intrinsic cap; the later positive-net part uses the actual derivative.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ExceptionalNegativeTSortedGain
open GlobalGA ActualSortedSupport ExceptionalECoefficients
open ExceptionalNegativeTScalarModel (g)

def J (s : ℝ) : ℝ := (13/12)*Real.tan s-(2/5)*(1/Real.cos s-1)
def Jd (s : ℝ) : ℝ := (13/12-(2/5)*Real.sin s)/(Real.cos s)^2
def sortedGain (q c s : ℝ) : ℝ :=
  c*((13/12)*Real.tan s+(1/Real.cos s-1)/2)-support q 1 (c/Real.cos s)+support q 1 c
def correction (b : Band) (td : Bool) (t : ℝ) : ℝ :=
  if td && decide (b≠.low) then (8/25)*(c b t-1)^2 else 0
def lowerGain (b : Band) (td : Bool) (t s : ℝ) : ℝ :=
  if td then c b t*J s else (21/20)*c b t*s

@[simp] theorem J_zero : J 0=0 := by norm_num [J]
@[simp] theorem sortedGain_zero (q c : ℝ) : sortedGain q c 0=0 := by simp [sortedGain]

theorem g_decreasing {s a : ℝ} (hs : s∈Icc 0 a) (ha : a≤3/10) : g a≤g s := by
  have hp := mul_nonneg (sub_nonneg.mpr hs.2)
    (show 0≤(1/5:ℝ)-(8/25)*(a+s) by linarith [hs.1,hs.2])
  dsimp [g]
  nlinarith

theorem g_lower {a : ℝ} (ha : a∈Icc 0 (3/10:ℝ)) : 10521/10000<g a := by
  have hh := g_decreasing ha (by norm_num : (3/10:ℝ)≤3/10)
  norm_num [g] at hh ⊢
  linarith

theorem J_quadratic {s : ℝ} (hs : s∈Ioc 0 (3/10:ℝ)) : s*g s<J s := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1.le,by norm_num [frameCap]; linarith [hs.2]⟩
  have hc : 0<Real.cos s := transport_cos_pos (by rw [abs_of_nonneg hs.1.le]; exact hs'.2)
  have hsin := mul_le_mul_of_nonneg_left (sin_lower_seven hs.1.le) (by norm_num : (0:ℝ)≤13/12)
  have hcosL := mul_le_mul_of_nonneg_left (cos_lower_six hs.1.le) (by norm_num : (0:ℝ)≤2/5)
  have hgpos : 0≤s*g s := mul_nonneg hs.1.le (by linarith [g_lower (Ioc_subset_Icc_self hs)])
  have hcosU := mul_le_mul_of_nonneg_left (cos_upper_four hs.1.le) hgpos
  let reserve : ℝ := 37/900-s/12+(223/1800)*s^2+(7/900)*s^3-(4097/302400)*s^4
  have hs4 := pow_le_pow_left₀ hs.1.le hs.2 4
  have hreserve : (2/125:ℝ)<reserve := by
    dsimp [reserve]
    norm_num at hs4
    nlinarith [sq_nonneg s,pow_nonneg hs.1.le 3]
  have hnum : s^3*reserve≤
      (13/12)*Real.sin s-(2/5)*(1-Real.cos s)-s*g s*Real.cos s := by
    dsimp [g,reserve] at *
    nlinarith
  have hnum0 : 0<(13/12)*Real.sin s-(2/5)*(1-Real.cos s)-s*g s*Real.cos s := by
    have hp := mul_pos (pow_pos hs.1 3) (show 0<reserve by linarith)
    linarith
  have hid : (J s-s*g s)*Real.cos s=
      (13/12)*Real.sin s-(2/5)*(1-Real.cos s)-s*g s*Real.cos s := by
    dsimp [J]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
    ring
  rw [← hid] at hnum0
  have hh := (mul_pos_iff_of_pos_right hc).1 hnum0
  linarith

theorem J_linear {s a : ℝ} (ha : a∈Icc 0 (3/10:ℝ)) (hs : s∈Icc 0 a) :
    g a*s≤J s := by
  by_cases hz : s=0
  · simp [hz]
  · have hs0 : 0<s := lt_of_le_of_ne hs.1 (Ne.symm hz)
    have hh := J_quadratic ⟨hs0,hs.2.trans ha.2⟩
    have hm := mul_le_mul_of_nonneg_right (g_decreasing hs ha.2) hs.1
    nlinarith

theorem J_hasDerivAt {s : ℝ} (hc : Real.cos s≠0) : HasDerivAt J (Jd s) s := by
  have ht := (Real.hasDerivAt_tan hc).const_mul (13/12:ℝ)
  have hs := ((Real.hasDerivAt_cos s).inv hc).sub_const 1
  convert ht.sub (hs.const_mul (2/5:ℝ)) using 1
  · rfl
  · dsimp [Jd]
    field_simp [hc]
    ring

theorem derivative_lower {b : Band} {t s : ℝ} (ht : t∈domain b)
    (hs : s∈Icc 0 (3/10:ℝ)) : (83/100:ℝ)<c b t*Jd s := by
  have hc0 : 17253/20000≤c b t := by
    by_cases hb : b=.low
    · subst b
      exact (low_bounds ht).1.trans (low_bounds ht).2.2.1
    · linarith [(balanced_bounds hb ht).2.2.2.1]
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs'.2)
  have hsin := (Real.sin_le hs.1).trans hs.2
  have hcos2 : (Real.cos s)^2≤1 := by nlinarith [(transport_trig hs').1,Real.cos_le_one s]
  have hnum : (83/100:ℝ)<c b t*(13/12-(2/5)*Real.sin s) := by
    have hm := mul_le_mul hc0 (show (289/300:ℝ)≤13/12-(2/5)*Real.sin s by linarith)
      (by norm_num) (by linarith)
    nlinarith
  dsimp [Jd]
  rw [mul_div_assoc]
  apply (lt_div_iff₀ (sq_pos_of_pos hcos)).2
  nlinarith

theorem late_growth {b : Band} {t a s : ℝ} (ht : t∈domain b)
    (ha : a∈Icc 0 (3/10:ℝ)) (hs : s∈Icc a (3/10:ℝ)) :
    (83/100)*(s-a)≤c b t*(J s-J a) := by
  let f : ℝ → ℝ := fun x => c b t*J x-(83/100)*x
  have hd (x : ℝ) (hx : x∈Icc 0 (3/10:ℝ)) :
      HasDerivAt f (c b t*Jd x-83/100) x := by
    have hc := transport_cos_pos (by rw [abs_of_nonneg hx.1]; norm_num [frameCap]; linarith [hx.2])
    exact ((J_hasDerivAt hc.ne').const_mul _).sub ((hasDerivAt_id x).const_mul _)
  have hm : MonotoneOn f (Icc 0 (3/10:ℝ)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => hd x (Ioo_subset_Icc_self hx)
    · intro x hx
      linarith [derivative_lower ht (Ioo_subset_Icc_self hx)]
  have hh := hm ha ⟨ha.1.trans hs.1,hs.2⟩ hs.1
  dsimp [f] at hh
  linarith

theorem sorted_gain_lower {q c s : ℝ} (hL : qLow≤q) (hQ : q≤qCap)
    (hc : 0<c) (hs : s∈Icc 0 (3/10:ℝ)) : c*J s≤sortedGain q c s := by
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; norm_num [frameCap]; linarith [hs.2])
  have hsec : c≤c/Real.cos s := (le_div_iff₀ hcos).2 (by nlinarith [Real.cos_le_one s])
  have hlip := second_lipschitz_nine_tenths hL hQ
    (show 0≤1+c by positivity) (show 0≤1+c/Real.cos s by positivity)
    (div_pos hc hcos) hsec
  have hid : c/Real.cos s-c=c*(1/Real.cos s-1) := by ring
  rw [hid] at hlip
  dsimp [J,sortedGain]
  nlinarith

theorem correction_lower {q t : ℝ} {b : Band} (hL : qLow≤q) (hQ : q≤qCap)
    (ht : t∈domain b) :
    correction b true t≤full q 1 (c b t)-support q 1 (c b t) := by
  have hc := (ranges ht).2.2.2.1
  by_cases hb : b=.low
  · subst b
    have hh := support_le_full (show 0≤q by norm_num [qLow] at hL; linarith)
      (show 0≤1+c .low t by positivity)
    simp only [correction,Bool.true_and,ne_eq,not_true_eq_false,decide_false,if_false]
    linarith
  · have hbnd := balanced_bounds hb ht
    have hN : Real.sqrt (1+(c b t)^2)≤307/200 := by
      have hroot := Real.sq_sqrt (show 0≤1+(c b t)^2 by positivity)
      have h0 := Real.sqrt_nonneg (1+(c b t)^2)
      nlinarith [hbnd.2.2.2.1,hbnd.2.2.2.2.1]
    have hh := SoleNegativeTDSupport.sorted_correction hL hQ
      (by norm_num : (0:ℝ)≤1) hc.le hbnd.2.2.2.1.le (by simpa using hN)
    simpa [correction,hb] using hh

theorem corrected_gain {q t s : ℝ} {b : Band}
    (hL : qLow≤q) (hQ : q≤qCap) (ht : t∈domain b)
    (hs : s∈Icc 0 (3/10:ℝ)) :
    correction b true t+c b t*J s≤
      ExceptionalNegativeTStress.gain true (Real.sqrt q) (ell b t) (c b t) s+
        full q 1 (c b t/Real.cos s)-support q 1 (c b t/Real.cos s) := by
  have hb := correction_lower hL hQ ht
  have hg := sorted_gain_lower hL hQ (ranges ht).2.2.2.1 hs
  have hid : full q 1 (c b t)-support q 1 (c b t)+sortedGain q (c b t) s=
      ExceptionalNegativeTStress.gain true (Real.sqrt q) (ell b t) (c b t) s+
        full q 1 (c b t/Real.cos s)-support q 1 (c b t/Real.cos s) := by
    dsimp [full,sortedGain,ExceptionalNegativeTStress.gain,FlatTStress.secantCharge]
    simp only [if_true,one_pow]
    ring
  rw [← hid]
  linarith

end SquaresInCircles.Eight.TableFree.ExceptionalNegativeTSortedGain
