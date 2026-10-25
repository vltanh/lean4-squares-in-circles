module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2SameBlock
public import SquaresInCircles.Eight.TableFree.OrdinaryNegativeSlope

/-!
# The seven negative-angle derivative endpoints

Uncompiled transcription of (24)--(25) in the negative-A angle companion.
Every square-root bound is the stated rational bound, established by
squaring the alternating Taylor inequalities. Monotonicity then gives
the full angle and coefficient intervals required by the proof.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.NegativeSlope
open Candidate Secondary Polynomial PositiveAngularEnvelope PairNormCalculus
open OrdinaryAngleConcavity OrdinaryNegativeSlope OrdinaryNegativeEnvelope
open VaryingBFunctions VaryingBComparison
open PositiveTD.Certificate (S5 S9 S11 C4 C10 C12)

def sinLo (t : ℚ) : ℚ := S11.eval t
def sinHi (t : ℚ) : ℚ := S9.eval t
def cosLo (t : ℚ) : ℚ := C10.eval t
def cosHi (t : ℚ) : ℚ := C12.eval t

theorem taylor_cast (t : ℚ) :
    (sinLo t:ℝ)=aeval (t:ℝ) S11 ∧ (sinHi t:ℝ)=aeval (t:ℝ) S9 ∧
    (cosLo t:ℝ)=aeval (t:ℝ) C10 ∧ (cosHi t:ℝ)=aeval (t:ℝ) C12 := by
  norm_num [sinLo,sinHi,cosLo,cosHi,S11,S9,S5,C12,C10,C4]

theorem rational_taylor {t : ℚ} (ht : (t:ℝ)∈Icc 0 frameCap) :
    (sinLo t:ℝ)≤Real.sin t ∧ Real.sin t≤(sinHi t:ℝ) ∧
    (cosLo t:ℝ)≤Real.cos t ∧ Real.cos t≤(cosHi t:ℝ) := by
  have hh := PositiveTD.Certificate.taylor_bounds ht
  obtain ⟨hslo,hshi,hclo,hchi⟩ := taylor_cast t
  rw [hslo,hshi,hclo,hchi]
  exact ⟨hh.2.1,hh.2.2.1,hh.2.2.2.2.1,hh.2.2.2.2.2⟩

theorem radius_tight : (1978787/1000000:ℝ)<R ∧ R<(494697/250000:ℝ) := by
  have hR0 : 0≤R := Real.sqrt_nonneg qCap
  have hR2 : R^2=9789/2500 := Real.sq_sqrt (by norm_num)
  constructor <;> nlinarith

inductive Upper where
  | G32 | H32 | H45
  deriving DecidableEq

instance : Fintype Upper where
  elems := {.G32, .H32, .H45}
  complete x := by cases x <;> decide
def upperRatio : Upper→ℚ | .G32=>33/50 | .H32=>187/250 | .H45=>187/250
def upperAngle : Upper→ℚ | .G32=>8/25 | .H32=>8/25 | .H45=>9/20
def upperValue : Upper→ℚ | .G32=>913/1000 | .H32=>129/125 | .H45=>241/250
def normLower : Upper→ℚ | .G32=>505067/500000 | .H32=>1043509/1000000 | .H45=>953307/1000000

theorem upper_reserves (e : Upper) :
    (0:ℚ)<upperRatio e ∧ upperRatio e≤1 ∧ 0<upperValue e ∧ 0<normLower e ∧
    0≤ sinLo (upperAngle e) ∧ 0<cosHi (upperAngle e) ∧
    (normLower e)^2<1+(upperRatio e)^2-2*upperRatio e*sinHi (upperAngle e) ∧
    (494697/250000:ℚ)*upperRatio e*cosHi (upperAngle e)<
      (upperValue e+sinLo (upperAngle e))*normLower e := by
  cases e <;> norm_num [upperRatio,upperAngle,upperValue,normLower,
    sinLo,sinHi,cosHi,S11,S9,S5,C12,C10,C4]

theorem upper_angle_domain (e : Upper) : (upperAngle e:ℝ)∈Icc 0 frameCap := by
  cases e <;> norm_num [upperAngle,frameCap]

theorem upper_endpoint (e : Upper) :
    Vd R (upperRatio e) 1 (upperAngle e)<(upperValue e:ℝ) := by
  obtain ⟨hr,hr1,hd,hL,hs0,hc0,hNreserve,hreserve⟩ := upper_reserves e
  have hr' : (0:ℝ)<(upperRatio e:ℝ) := by exact_mod_cast hr
  have hL' : (0:ℝ)<(normLower e:ℝ) := by exact_mod_cast hL
  have ht := upper_angle_domain e
  have htt := transport_trig ht
  obtain ⟨hsl,hsh,hcl,hch⟩ := rational_taylor ht
  have hN0 := pairNorm_pos hr' (by norm_num : (0:ℝ)<1)
    (show |-(upperAngle e:ℝ)|≤frameCap by simpa [abs_of_nonneg ht.1] using ht.2)
  have hN2 := pairNorm_sq hr' (by norm_num : (0:ℝ)<1)
    (show |-(upperAngle e:ℝ)|≤frameCap by simpa [abs_of_nonneg ht.1] using ht.2)
  norm_num only [pairEnergy,pairProduct,one_pow,mul_one,Real.sin_neg] at hN2
  have hn : (normLower e:ℝ)<pairNorm (upperRatio e) 1 (-(upperAngle e:ℝ)) := by
    have hs := mul_le_mul_of_nonneg_left hsh (show 0≤2*(upperRatio e:ℝ) by positivity)
    have hres : (normLower e:ℝ)^2<1+(upperRatio e:ℝ)^2-
        2*(upperRatio e:ℝ)*(sinHi (upperAngle e):ℝ) := by exact_mod_cast hNreserve
    nlinarith
  have hnum : R*(upperRatio e:ℝ)*Real.cos (upperAngle e)≤
      (494697/250000:ℝ)*(upperRatio e:ℝ)*(cosHi (upperAngle e):ℝ) := by
    have hcos0 : 0≤Real.cos (upperAngle e:ℝ) := by linarith [htt.1]
    exact mul_le_mul (mul_le_mul_of_nonneg_right radius_tight.2.le hr'.le)
      hch hcos0 (by positivity)
  have hres : (494697/250000:ℝ)*(upperRatio e:ℝ)*(cosHi (upperAngle e):ℝ)<
      ((upperValue e:ℝ)+(sinLo (upperAngle e):ℝ))*(normLower e:ℝ) := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr hreserve
    push_cast at h
    exact h
  have hfirst := mul_le_mul_of_nonneg_right hsl hL'.le
  have hsecond := mul_lt_mul_of_pos_left hn
    (show 0<(upperValue e:ℝ)+Real.sin (upperAngle e) by
      have hd' : (0:ℝ)<(upperValue e:ℝ) := by exact_mod_cast hd
      linarith [htt.2.2.1])
  have hcross : R*(upperRatio e:ℝ)*Real.cos (upperAngle e)<
      ((upperValue e:ℝ)+Real.sin (upperAngle e))*
        pairNorm (upperRatio e) 1 (-(upperAngle e:ℝ)) := by nlinarith
  have hh := (div_lt_iff₀ hN0).2 hcross
  have he : Vd R (upperRatio e) 1 (upperAngle e)=
      -Real.sin (upperAngle e)+R*(upperRatio e:ℝ)*Real.cos (upperAngle e)/
        pairNorm (upperRatio e) 1 (-(upperAngle e:ℝ)) := by
    simp only [Vd,mixedNDerivative,normD1,pairProduct,zero_sub,Real.cos_neg,mul_one]
    ring
  rw [he]
  linarith

inductive Lower where
  | GAfull | ABfull | GAhalf | ABhalf
  deriving DecidableEq

instance : Fintype Lower where
  elems := {.GAfull, .ABfull, .GAhalf, .ABhalf}
  complete x := by cases x <;> decide
def lowerRatio : Lower→ℚ | .GAfull=>51/80 | .ABfull=>13/20 | .GAhalf=>51/80 | .ABhalf=>13/20
def lowerAngle : Lower→ℚ | .GAfull=>7/10 | .ABfull=>7/10 | .GAhalf=>1/2 | .ABhalf=>1/2
def lowerValue : Lower→ℚ | .GAfull=>61/100 | .ABfull=>16/25 | .GAhalf=>19/25 | .ABhalf=>39/50
def normUpper : Lower→ℚ | .GAfull=>95609/125000 | .ABfull=>152973/200000 | .GAhalf=>445853/500000 | .ABhalf=>894007/1000000

theorem lower_reserves (e : Lower) :
    (0:ℚ)<lowerRatio e ∧ lowerRatio e≤1 ∧ 0<lowerValue e ∧ 0<normUpper e ∧
    0<cosLo (lowerAngle e) ∧
    1+(lowerRatio e)^2-2*lowerRatio e*sinLo (lowerAngle e)<(normUpper e)^2 ∧
    (lowerValue e+sinHi (lowerAngle e))*normUpper e<
      (1978787/1000000:ℚ)*lowerRatio e*cosLo (lowerAngle e) := by
  cases e <;> norm_num [lowerRatio,lowerAngle,lowerValue,normUpper,
    sinLo,sinHi,cosLo,S11,S9,S5,C10,C4]

theorem lower_angle_domain (e : Lower) : (lowerAngle e:ℝ)∈Icc 0 frameCap := by
  cases e <;> norm_num [lowerAngle,frameCap]

theorem lower_endpoint (e : Lower) :
    (lowerValue e:ℝ)<Vd R (lowerRatio e) 1 (lowerAngle e) := by
  obtain ⟨hr,hr1,hd,hL,hc0,hNreserve,hreserve⟩ := lower_reserves e
  have hr' : (0:ℝ)<(lowerRatio e:ℝ) := by exact_mod_cast hr
  have hL' : (0:ℝ)<(normUpper e:ℝ) := by exact_mod_cast hL
  have ht := lower_angle_domain e
  have htt := transport_trig ht
  obtain ⟨hsl,hsh,hcl,hch⟩ := rational_taylor ht
  have hN0 := pairNorm_pos hr' (by norm_num : (0:ℝ)<1)
    (show |-(lowerAngle e:ℝ)|≤frameCap by simpa [abs_of_nonneg ht.1] using ht.2)
  have hN2 := pairNorm_sq hr' (by norm_num : (0:ℝ)<1)
    (show |-(lowerAngle e:ℝ)|≤frameCap by simpa [abs_of_nonneg ht.1] using ht.2)
  norm_num only [pairEnergy,pairProduct,one_pow,mul_one,Real.sin_neg] at hN2
  have hn : pairNorm (lowerRatio e) 1 (-(lowerAngle e:ℝ))<(normUpper e:ℝ) := by
    have hs := mul_le_mul_of_nonneg_left hsl (show 0≤2*(lowerRatio e:ℝ) by positivity)
    have hres : 1+(lowerRatio e:ℝ)^2-
        2*(lowerRatio e:ℝ)*(sinLo (lowerAngle e):ℝ)<(normUpper e:ℝ)^2 := by
      exact_mod_cast hNreserve
    nlinarith
  have hnum : (1978787/1000000:ℝ)*(lowerRatio e:ℝ)*(cosLo (lowerAngle e):ℝ)≤
      R*(lowerRatio e:ℝ)*Real.cos (lowerAngle e) := by
    have hc0' : 0≤(cosLo (lowerAngle e):ℝ) := by exact_mod_cast hc0.le
    exact mul_le_mul (mul_le_mul_of_nonneg_right radius_tight.1.le hr'.le)
      hcl hc0' (by have hR := Curvature.radius_bounds.1; positivity)
  have hres : ((lowerValue e:ℝ)+(sinHi (lowerAngle e):ℝ))*(normUpper e:ℝ)<
      (1978787/1000000:ℝ)*(lowerRatio e:ℝ)*(cosLo (lowerAngle e):ℝ) := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr hreserve
    push_cast at h
    exact h
  have hfirst := mul_le_mul_of_nonneg_right hsh hL'.le
  have hsecond := mul_lt_mul_of_pos_left hn
    (show 0<(lowerValue e:ℝ)+Real.sin (lowerAngle e) by
      have hd' : (0:ℝ)<(lowerValue e:ℝ) := by exact_mod_cast hd
      linarith [htt.2.2.1])
  have hcross : ((lowerValue e:ℝ)+Real.sin (lowerAngle e))*
        pairNorm (lowerRatio e) 1 (-(lowerAngle e:ℝ))<
      R*(lowerRatio e:ℝ)*Real.cos (lowerAngle e) := by nlinarith
  have hh := (lt_div_iff₀ hN0).2 hcross
  have he : Vd R (lowerRatio e) 1 (lowerAngle e)=
      -Real.sin (lowerAngle e)+R*(lowerRatio e:ℝ)*Real.cos (lowerAngle e)/
        pairNorm (lowerRatio e) 1 (-(lowerAngle e:ℝ)) := by
    simp only [Vd,mixedNDerivative,normD1,pairProduct,zero_sub,Real.cos_neg,mul_one]
    ring
  rw [he]
  linarith

theorem normalized_slope_mono {r₁ r₂ t : ℝ}
    (hr₁ : 0≤r₁) (hrr : r₁≤r₂) (hr₂ : r₂≤1) (ht : t∈Icc 0 frameCap) :
    Vd R r₁ 1 t≤Vd R r₂ 1 t := by
  have hm := normalized_fraction_mono hr₁ hrr hr₂ (sin_mem ht)
  have hc : 0≤R*Real.cos t :=
    mul_nonneg (Real.sqrt_nonneg qCap) (by linarith [(transport_trig ht).1])
  have hh := mul_le_mul_of_nonneg_left hm hc
  rw [Vd_normalized (by norm_num : (0:ℝ)<1),
    Vd_normalized (by norm_num : (0:ℝ)<1)]
  norm_num only [div_one,one_mul]
  have e1 : R*r₁*Real.cos t/root r₁ (Real.sin t)=R*Real.cos t*(r₁/root r₁ (Real.sin t)) := by ring
  have e2 : R*r₂*Real.cos t/root r₂ (Real.sin t)=R*Real.cos t*(r₂/root r₂ (Real.sin t)) := by ring
  rw [e1,e2]
  linarith only [hh]

theorem upper_bound (e : Upper) {p q t : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hpr : p≤(upperRatio e:ℝ)*q)
    (ht : t∈Icc (upperAngle e:ℝ) frameCap) :
    Vd R p q t<(upperValue e:ℝ)*q := by
  have hq := hp.trans_le hpq
  have hu := upper_angle_domain e
  have ht' : t∈Icc 0 frameCap := ⟨hu.1.trans ht.1,ht.2⟩
  have ha := Vd_antitone (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (by norm_num [qCap])).le hp hpq hqp hu ht' ht.1
  have hr : p/q≤(upperRatio e:ℝ) := (div_le_iff₀ hq).2 hpr
  have hmono := normalized_slope_mono (div_nonneg hp.le hq.le) hr
    (by exact_mod_cast (upper_reserves e).2.1) hu
  have hscale : Vd R p q (upperAngle e)=q*Vd R (p/q) 1 (upperAngle e) := by
    rw [Vd_normalized hq,Vd_normalized (by norm_num : (0:ℝ)<1)]
    norm_num
  have hh := mul_lt_mul_of_pos_left (hmono.trans_lt (upper_endpoint e)) hq
  rw [←hscale] at hh
  exact ha.trans_lt (by simpa [mul_comm] using hh)

theorem lower_bound (e : Lower) {p q t : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hpr : (lowerRatio e:ℝ)*q≤p)
    (ht : t∈Icc 0 (lowerAngle e:ℝ)) :
    (lowerValue e:ℝ)*q<Vd R p q t := by
  have hq := hp.trans_le hpq
  have hu := lower_angle_domain e
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hu.2⟩
  have ha := Vd_antitone (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (by norm_num [qCap])).le hp hpq hqp ht' hu ht.2
  have hr : (lowerRatio e:ℝ)≤p/q := (le_div_iff₀ hq).2 hpr
  have hmono := normalized_slope_mono
    (by exact_mod_cast (lower_reserves e).1.le) hr ((div_le_one hq).2 hpq) hu
  have hscale : Vd R p q (lowerAngle e)=q*Vd R (p/q) 1 (lowerAngle e) := by
    rw [Vd_normalized hq,Vd_normalized (by norm_num : (0:ℝ)<1)]
    norm_num
  have hh := mul_lt_mul_of_pos_left ((lower_endpoint e).trans_le hmono) hq
  rw [←hscale] at hh
  have h2 : (lowerValue e:ℝ)*q<Vd R p q (lowerAngle e) := by simpa [mul_comm] using hh
  exact h2.trans_le ha

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.NegativeSlope
