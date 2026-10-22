module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEHighBaseThird
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2NegativeSlopes

/-!
# The original correlated late-range comparison for negative DE

Uncompiled late-range data for the TD2 and BT3 companions. The two
coefficient lines have their original slopes .3 and .305 and the common
right endpoint .863. The tangent and radical enclosures are proved by
alternating Taylor bounds and positive squaring at the stated endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEHighShape
open Candidate Secondary PositiveAngularEnvelope
open NegativeAPositiveTD.SecantCoordinate

namespace TrigonometricBounds
open NegativeAPositiveTD.NegativeSlope

theorem transition : (613/1000:ℝ)<Real.tan (11/20:ℝ) ∧
    Real.tan (11/20:ℝ)<307/500 := by
  have ht := rational_taylor (t:=11/20)
    (by norm_num [frameCap] : (11/20:ℝ)∈Icc 0 frameCap)
  have hc : 0<Real.cos (11/20:ℝ) := by
    linarith [(transport_trig (show (11/20:ℝ)∈Icc 0 frameCap by norm_num [frameCap])).1]
  rw [Real.tan_eq_sin_div_cos]
  constructor
  · apply (lt_div_iff₀ hc).2
    norm_num [sinLo,cosHi,PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,
      PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,
      PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at ht
    linarith [ht.1,ht.2.2.2]
  · apply (div_lt_iff₀ hc).2
    norm_num [sinHi,cosLo,PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,
      PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at ht
    linarith [ht.2.1,ht.2.2.1]

theorem middle_left : Real.tan (523/1000:ℝ)<577/1000 := by
  have ht := rational_taylor (t:=523/1000)
    (by norm_num [frameCap] : (523/1000:ℝ)∈Icc 0 frameCap)
  have hc : 0<Real.cos (523/1000:ℝ) := by
    linarith [(transport_trig (show (523/1000:ℝ)∈Icc 0 frameCap by norm_num [frameCap])).1]
  rw [Real.tan_eq_sin_div_cos]
  apply (div_lt_iff₀ hc).2
  norm_num [sinHi,cosLo,PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,
    PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at ht
  linarith [ht.2.1,ht.2.2.1]

theorem cap : (105286/125000:ℝ)<Real.tan frameCap ∧
    Real.tan frameCap<(842289/1000000:ℝ) ∧
    1/Real.cos frameCap<(65373/50000:ℝ) := by
  have ht := rational_taylor (t:=7/10)
    (by norm_num [frameCap] : (7/10:ℝ)∈Icc 0 frameCap)
  have hc : 0<Real.cos frameCap := by
    linarith [(transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).1]
  norm_num [sinLo,sinHi,cosLo,cosHi,PositiveTD.Certificate.S11,
    PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,
    PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at ht
  refine ⟨?_,?_,?_⟩
  · rw [Real.tan_eq_sin_div_cos]
    apply (lt_div_iff₀ hc).2
    dsimp [frameCap] at *
    linarith [ht.1,ht.2.2.2]
  · rw [Real.tan_eq_sin_div_cos]
    apply (div_lt_iff₀ hc).2
    dsimp [frameCap] at *
    linarith [ht.2.1,ht.2.2.1]
  · apply (div_lt_iff₀ hc).2
    dsimp [frameCap] at *
    linarith [ht.2.2.1]

theorem radical_tan {s : ℝ} (hs : s∈Icc 0 frameCap) :
    radical 1 (Real.tan s)=1/Real.cos s := by
  have hh := Real.cos_arctan (Real.tan s)
  rw [arctan_tan hs] at hh
  rw [hh]
  simp [radical]

end TrigonometricBounds

namespace Late

def rate : Bool→ℝ | false=>3/10 | true=>61/200
def coefficient (bt3 : Bool) (x : ℝ) : ℝ :=
  863/1000+rate bt3*(frameCap-Real.arctan x)
def mass (c x : ℝ) : ℝ :=
  R*(1+c^2)*(1+x^2)^3/(radical (1+c^2) x)^5
def firstLog (c x : ℝ) : ℝ :=
  x*(1+x^2+6*c^2)/((1+x^2)*(1+x^2+c^2))
def bracket (c x : ℝ) : ℝ := 5/(1+x^2+c^2)-2/(1+c^2)
def secondLog (bt3 : Bool) (c x : ℝ) : ℝ := rate bt3*c/(1+x^2)*bracket c x
def total (bt3 : Bool) (x : ℝ) : ℝ := mass (coefficient bt3 x) x
def totalFirst (bt3 : Bool) (x : ℝ) : ℝ :=
  total bt3 x*(firstLog (coefficient bt3 x) x+secondLog bt3 (coefficient bt3 x) x)
def reserve (bt3 : Bool) (x : ℝ) : ℝ :=
  3*x*(total bt3 x-radical 1 x)+latePolynomial x

theorem rate_bounds (bt3 : Bool) : 0≤rate bt3 ∧ rate bt3≤61/200 := by
  cases bt3 <;> norm_num [rate]

theorem domain {x : ℝ} (hx : x∈Icc (Real.tan (11/20:ℝ)) (Real.tan frameCap)) :
    x∈Icc (613/1000:ℝ) (843/1000) ∧ Real.arctan x∈Icc (11/20:ℝ) frameCap := by
  have h0 : 0≤x := by linarith [hx.1,TrigonometricBounds.transition.1]
  have ha := arctan_interval (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ⟨h0,hx.2⟩
  have hlo := Real.arctan_le_arctan hx.1
  rw [arctan_tan (show (11/20:ℝ)∈Icc 0 frameCap by norm_num [frameCap])] at hlo
  exact ⟨⟨by linarith [hx.1,TrigonometricBounds.transition.1],
    by linarith [hx.2,TrigonometricBounds.cap.2.1]⟩,⟨hlo,ha.2⟩⟩

theorem coefficient_bounds (bt3 : Bool) {x : ℝ}
    (hx : x∈Icc (Real.tan (11/20:ℝ)) (Real.tan frameCap)) :
    coefficient bt3 x∈Icc (863/1000:ℝ) (909/1000) := by
  have ha := (domain hx).2
  cases bt3 <;> dsimp [coefficient,rate,frameCap] at * <;>
    exact ⟨by linarith [ha.2],by linarith [ha.1]⟩

theorem coefficient_hasDerivAt (bt3 : Bool) (x : ℝ) :
    HasDerivAt (coefficient bt3) (-rate bt3/(1+x^2)) x := by
  convert (((Real.hasDerivAt_arctan x).const_sub frameCap).const_mul (rate bt3)).const_add
    (863/1000:ℝ) using 1 <;> dsimp [coefficient] <;> ring

theorem coefficient_cap (bt3 : Bool) : coefficient bt3 (Real.tan frameCap)=863/1000 := by
  simp [coefficient,arctan_tan (show frameCap∈Icc 0 frameCap by norm_num [frameCap])]

theorem mass_pos (c x : ℝ) : 0<mass c x := by
  have hR : 0<R := Real.sqrt_pos.mpr (by norm_num [qCap])
  have hn := radical_positive (A:=1+c^2) (x:=x) (by positivity)
  dsimp [mass]
  positivity

theorem mass_upper_of_square {c x b : ℝ} (hb : 0<b)
    (h : qCap*(1+c^2)^2*(1+x^2)^6<b^2*(1+c^2+x^2)^5) : mass c x<b := by
  have hn := radical_positive (A:=1+c^2) (x:=x) (by positivity)
  have hn2 := radical_square (A:=1+c^2) (x:=x) (by positivity)
  have hp : ((radical (1+c^2) x)^5)^2=(1+c^2+x^2)^5 := by
    rw [←pow_mul,show (5:ℕ)*2=2*5 by norm_num,pow_mul,hn2]
  have hnum : (R*(1+c^2)*(1+x^2)^3)^2=qCap*(1+c^2)^2*(1+x^2)^6 := by
    rw [mul_pow,mul_pow,radius_sq]
    ring
  apply (div_lt_iff₀ (pow_pos hn 5)).2
  have hden : 0<b*(radical (1+c^2) x)^5 := mul_pos hb (pow_pos hn 5)
  nlinarith [mul_pow b ((radical (1+c^2) x)^5) 2]

theorem mass_lower_of_square {c x b : ℝ} (hb : 0≤b)
    (h : b^2*(1+c^2+x^2)^5<qCap*(1+c^2)^2*(1+x^2)^6) : b<mass c x := by
  have hn := radical_positive (A:=1+c^2) (x:=x) (by positivity)
  have hn2 := radical_square (A:=1+c^2) (x:=x) (by positivity)
  have hp : ((radical (1+c^2) x)^5)^2=(1+c^2+x^2)^5 := by
    rw [←pow_mul,show (5:ℕ)*2=2*5 by norm_num,pow_mul,hn2]
  have hnum : (R*(1+c^2)*(1+x^2)^3)^2=qCap*(1+c^2)^2*(1+x^2)^6 := by
    rw [mul_pow,mul_pow,radius_sq]
    ring
  apply (lt_div_iff₀ (pow_pos hn 5)).2
  have hR : 0<R := Real.sqrt_pos.mpr (by norm_num [qCap])
  have hright : 0<R*(1+c^2)*(1+x^2)^3 := by positivity
  nlinarith [mul_pow b ((radical (1+c^2) x)^5) 2]

theorem rational_mass_endpoints : mass (863/1000) (843/1000)<183/100 ∧
    (182777/100000:ℝ)<mass (863/1000) (105286/125000) := by
  constructor
  · apply mass_upper_of_square (by norm_num)
    norm_num [qCap]
  · apply mass_lower_of_square (by norm_num)
    norm_num [qCap]

/-- Multiplication by the actual positive denominator, not a changed coefficient. -/
theorem mass_identity (c x : ℝ) :
    (1+x^2)^3*baseThird c x=3*x*(mass c x-radical 1 x) := by
  have hw := radical_positive (A:=1) (x:=x) (by norm_num)
  have hn := radical_positive (A:=1+c^2) (x:=x) (by positivity)
  have hw2 := radical_square (A:=1) (x:=x) (by norm_num)
  have hw6 : (1+x^2)^3=(radical 1 x)^6 := by
    rw [←hw2,←pow_mul]
    norm_num
  dsimp [baseThird,mass]
  rw [hw6]
  field_simp [hw.ne',hn.ne']
  ring

theorem mass_antitone_coefficient {c C x : ℝ}
    (hc : 0≤c) (hC : c≤C) (hx : 0<x) (hx2 : 2*x^2≤3) : mass C x≤mass c x := by
  have hh := mul_le_mul_of_nonneg_left
    (baseThird_antitone_parameter hc hC hx.le hx2) (by positivity : 0≤(1+x^2)^3)
  rw [mass_identity,mass_identity] at hh
  nlinarith

end Late
end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEHighShape
