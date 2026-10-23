module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeALongEPolynomial
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeAShortEComparison
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeAEntry

/-!
# The actual negative-A gain and the small-total comparison

Uncompiled transcription of Sections 2--3 and of the cited sharp EH1
contact cut. The strict GA contact comparison is used on the original
G/A pair. The common gain is concave on the full analytic interval,
including values beyond the smaller genuine GA cut.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE
open Candidate Secondary

def gain (s : ℝ) : ℝ :=
  (13/12)*Real.sin s-(82/125-(63/100)*s)*(1-Real.cos s)
def gainD (s : ℝ) : ℝ :=
  (13/12-63/100)*Real.cos s+63/100-(82/125-(63/100)*s)*Real.sin s
def gainDD (s : ℝ) : ℝ :=
  (53/300)*Real.sin s+((63/100)*s-82/125)*Real.cos s

@[simp] theorem gain_zero : gain 0=0 := by simp [gain]

theorem gain_hasDerivAt (s : ℝ) : HasDerivAt gain (gainD s) s := by
  convert ((Real.hasDerivAt_sin s).const_mul (13/12)).sub
    (((hasDerivAt_const s (82/125)).sub ((hasDerivAt_id s).const_mul (63/100))).mul
      ((hasDerivAt_const s 1).sub (Real.hasDerivAt_cos s))) using 1 <;>
    dsimp [gain,gainD] <;> ring

theorem gainD_hasDerivAt (s : ℝ) : HasDerivAt gainD (gainDD s) s := by
  convert (((Real.hasDerivAt_cos s).const_mul (13/12-63/100)).add_const (63/100)).sub
    (((hasDerivAt_const s (82/125)).sub ((hasDerivAt_id s).const_mul (63/100))).mul
      (Real.hasDerivAt_sin s)) using 1 <;> dsimp [gainD,gainDD] <;> ring

theorem gain_curvature {s : ℝ} (hs : s∈Icc 0 (19/50:ℝ)) : gainDD s< -31/100 := by
  have hsin := Real.sin_le hs.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=s)
  have hsq := pow_le_pow_left₀ hs.1 hs.2 2
  have hc : (1:ℝ)-(19/50)^2/2≤Real.cos s := by linarith
  have hb : (82/125:ℝ)-(63/100)*(19/50)≤82/125-(63/100)*s := by linarith [hs.2]
  have hprod := mul_le_mul hb hc (by norm_num : (0:ℝ)≤1-(19/50)^2/2)
    (by linarith [hs.2] : (0:ℝ)≤82/125-(63/100)*s)
  dsimp [gainDD]
  nlinarith only [hprod,hs.2,hsin]

theorem gain_concave : ConcaveOn ℝ (Icc (0:ℝ) (19/50)) gain := by
  apply concave_of_deriv2 (fun s _ => gain_hasDerivAt s) (fun s _ => gainD_hasDerivAt s)
  intro s hs
  linarith [gain_curvature hs]

namespace Contact

def root (s : ℝ) : ℝ := Real.sqrt (qCap-(13/12+Real.sin s)^2)
def cap (s : ℝ) : ℝ := root s-Real.cos s-1/2
def slope (s : ℝ) : ℝ := Real.sin s-(13/12+Real.sin s)*Real.cos s/root s
def P (y : ℝ) : ℝ := 76784149/900000000-(321217/750000)*y+
  (2113/10000)*y^2+(63/50)*y^3
def PD (y : ℝ) : ℝ := -321217/750000+(2113/5000)*y+(189/50)*y^2

theorem P_hasDerivAt (y : ℝ) : HasDerivAt P (PD y) y := by
  have hd : Differentiable ℝ P := by dsimp [P]; fun_prop
  convert (hd y).hasDerivAt using 1
  simp (disch := fun_prop) [P,PD]
  ring

theorem P_positive {y : ℝ} (hy : y∈Icc 0 (1/4:ℝ)) : 0<P y := by
  have hm : AntitoneOn P (Icc (0:ℝ) (1/4)) := by
    apply antiOn_of_hasDeriv_nonpos (by dsimp [P]; fun_prop)
      (fun y _ => P_hasDerivAt y)
    intro t ht
    have hs := pow_le_pow_left₀ ht.1.le ht.2.le 2
    dsimp [PD]
    nlinarith only [ht.2,hs]
  have hh := hm hy (show (1/4:ℝ)∈Icc 0 (1/4) by norm_num) hy.2
  have hp : (0:ℝ)<P (1/4) := by norm_num [P]
  exact hp.trans_le hh

theorem root_data {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    0<root s ∧ (root s)^2=qCap-(13/12+Real.sin s)^2 := by
  have hsin0 := (transport_trig (show s∈Icc 0 frameCap by
    constructor <;> dsimp [frameCap] <;> linarith [hs.1,hs.2])).2.2.1
  have hsin := Real.sin_le hs.1
  have hsq := pow_le_pow_left₀ (by linarith : (0:ℝ)≤13/12+Real.sin s)
    (show 13/12+Real.sin s≤13/12+1/4 by linarith) 2
  have hrad : 0<qCap-(13/12+Real.sin s)^2 := by dsimp [qCap]; nlinarith only [hsq]
  exact ⟨Real.sqrt_pos.2 hrad,Real.sq_sqrt hrad.le⟩

theorem cap_hasDerivAt {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    HasDerivAt cap (slope s) s := by
  have hr := root_data hs
  have hrad : qCap-(13/12+Real.sin s)^2≠0 := by rw [←hr.2]; positivity
  have hd := ((hasDerivAt_const s qCap).sub
    (((Real.hasDerivAt_sin s).const_add (13/12)).pow 2)).sqrt hrad
  convert ((hd.sub (Real.hasDerivAt_cos s)).sub_const (1/2)) using 1 <;>
    dsimp [root,cap,slope] <;> ring

theorem slope_upper {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) : slope s< -63/100 := by
  have ht := transport_trig (show s∈Icc 0 frameCap by
    constructor <;> dsimp [frameCap] <;> linarith [hs.1,hs.2])
  have hy : Real.sin s∈Icc 0 (1/4:ℝ) := ⟨ht.2.2.1,(Real.sin_le hs.1).trans hs.2⟩
  have hp := P_positive hy
  have hr := root_data hs
  have hid : ((13/12+Real.sin s)*Real.cos s)^2-
      ((Real.sin s+63/100)*root s)^2=P (Real.sin s) := by
    rw [mul_pow,mul_pow,hr.2]
    dsimp [P,qCap]
    nlinarith [Real.sin_sq_add_cos_sq s,
      congrArg (fun t : ℝ => (13/12+Real.sin s)^2*t) (Real.sin_sq_add_cos_sq s)]
  have hleft : 0≤(Real.sin s+63/100)*root s := by positivity
  have hright : 0≤(13/12+Real.sin s)*Real.cos s :=
    mul_nonneg (by linarith [hy.1]) (by linarith [ht.1])
  have hstrict : (Real.sin s+63/100)*root s<(13/12+Real.sin s)*Real.cos s := by
    nlinarith only [hid,hp,hleft,hright]
  have hquot := (lt_div_iff₀ hr.1).2 hstrict
  dsimp [slope]
  linarith

theorem cap_linear {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    cap s<39/250-(63/100)*s := by
  have hm : AntitoneOn (fun t => cap t+(63/100)*t) (Icc (0:ℝ) (1/4)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun t ht => ((cap_hasDerivAt ht).add ((hasDerivAt_id t).const_mul (63/100))).continuousAt.continuousWithinAt)
      (fun t ht => (cap_hasDerivAt (Ioo_subset_Icc_self ht)).add ((hasDerivAt_id t).const_mul (63/100)))
    intro t ht
    linarith [slope_upper (Ioo_subset_Icc_self ht)]
  have hh := hm (show (0:ℝ)∈Icc 0 (1/4) by norm_num) hs hs.1
  have hr := root_data (show (0:ℝ)∈Icc 0 (1/4) by norm_num)
  have hzero : cap 0<39/250 := by
    simp only [cap,Real.cos_zero] at ⊢
    simp only [Real.sin_zero,add_zero] at hr
    dsimp [qCap] at hr
    nlinarith only [hr.1,hr.2]
  simp only [mul_zero,add_zero] at hh
  linarith

theorem corner_cut {b s : ℝ} (hb : 0≤b) (hs : s∈Icc 0 (1/4:ℝ))
    (hcorner : (b+1/2+Real.cos s)^2+(13/12+Real.sin s)^2<qCap) :
    b<39/250-(63/100)*s ∧ s<61/250 := by
  have ht := transport_trig (show s∈Icc 0 frameCap by
    constructor <;> dsimp [frameCap] <;> linarith [hs.1,hs.2])
  have hr := root_data hs
  have hroot : b+1/2+Real.cos s<root s := by
    have hbpos : 0≤b+1/2+Real.cos s := by linarith [ht.1]
    nlinarith only [hcorner,hr.1,hr.2,hbpos]
  have hcap : b<cap s := by dsimp [cap]; linarith
  refine ⟨hcap.trans (cap_linear hs),?_⟩
  by_contra! hlarge
  have hm := PrimaryCap.contactHeight_strictMono.monotoneOn
    (show (61/250:ℝ)∈Icc 0 (7/10) by norm_num)
    (show s∈Icc 0 (7/10) from ⟨hs.1,by linarith [hs.2]⟩) hlarge
  have t := PositiveTD.Certificate.taylor_bounds
    (show (61/250:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have hsingle : qCap<(13/12:ℝ)^2+5/4+
      aeval (61/250:ℝ) PositiveTD.Certificate.C10+
        (13/6)*aeval (61/250:ℝ) PositiveTD.Certificate.S11 := by
    norm_num [qCap,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4,
      PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,PositiveTD.Certificate.S5]
  have hdrop := mul_nonneg hb (by linarith [ht.1] : 0≤1+2*Real.cos s+b)
  dsimp [PrimaryCap.contactHeight,PrimaryCap.K] at hm
  nlinarith [Real.sin_sq_add_cos_sq s]

end Contact

/-- The sharper cut uses the actual GA3 contact and the strict failure
of the actual GA2 contact, on the unchanged two original states. -/
theorem GA_sharp_cut {q s : ℝ} {G A : SignedPoint}
    (hGs : G.Sorted) (hGc : G.Contained q) (hAs : A.Sorted) (hq : q≤qCap)
    (hGy : G.y≤0) (hAy : 0≤A.y) (hAa : A.a=7/12)
    (hs : s∈Ioc 0 (1/4:ℝ))
    (hGA : quarterFeasible G A (-s) 3) (hnot : ¬quarterFeasible G A (-s) 2) :
    A.y<39/250-(63/100)*s ∧ s<61/250 := by
  have hv := negative_primary_contact_vector (a:=A.a) (g:=A.y) (A:=G.a) (b:=-G.y) (z:=s) hAs.1 hAy
    (by simpa [abs_of_nonneg hAy] using hAs.2)
    ⟨hs.1,by linarith [hs.2]⟩
    (by simpa [quarterFeasible,quarterProjection,Real.sin_neg,Real.cos_neg] using hGA)
    (by simpa [quarterFeasible,quarterProjection,Real.sin_neg,Real.cos_neg] using lt_of_not_ge hnot)
  have hc : (G.a+1/2)^2+(-G.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos hGy] using hGc.trans hq
  have hcorner : (A.y+1/2+Real.cos s)^2+(13/12+Real.sin s)^2<qCap := by
    rw [hAa] at hv
    nlinarith [Real.sin_sq_add_cos_sq s]
  exact Contact.corner_cut hAy ⟨hs.1.le,hs.2⟩ hcorner

theorem gain_le_GA {b s : ℝ} (hb : b≤39/250-(63/100)*s) :
    gain s≤ShortE.gain (b+1/2) s := by
  have hh := mul_le_mul_of_nonneg_right
    (show b+1/2≤82/125-(63/100)*s by linarith) (sub_nonneg.mpr (Real.cos_le_one s))
  dsimp [gain,ShortE.gain]
  linarith

theorem gain_le_AB {b s : ℝ} (hb : 1/10≤b) (hs : s≤19/50) :
    gain s≤ShortE.gain (1/2-b) s := by
  have hh := mul_le_mul_of_nonneg_right
    (show 1/2-b≤82/125-(63/100)*s by linarith) (sub_nonneg.mpr (Real.cos_le_one s))
  dsimp [gain,ShortE.gain]
  linarith

theorem gain_small {s : ℝ} (hs : s∈Icc 0 (1/6:ℝ)) : s≤gain s := by
  have hsin := Real.sin_ge_sub_cube hs.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=s)
  have hcos1 := Real.cos_le_one s
  have hpositive := mul_nonneg hs.1 (sub_nonneg.mpr hcos1)
  have hsq := mul_le_mul_of_nonneg_right hs.2 hs.1
  have hcub := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.1 hs.2 2) hs.1
  dsimp [gain]
  nlinarith only [hsin,hcos,hpositive,hsq,hcub,hs.1]

theorem charge_small_slope {u : ℝ} (hu : u∈Icc 0 (1/6:ℝ)) :
    -(599/600:ℝ)≤TwoPositive.ASupport.axialD u := by
  have hsin := Real.sin_le hu.1
  have hcos := Real.cos_le_one u
  have hb : 0≤axial-1/2 := by linarith [axial_bounds.1]
  have hh := mul_le_mul_of_nonneg_left hcos hb
  have ha : axial-1/2<183/200 := by linarith [axial_bounds.2]
  dsimp [TwoPositive.ASupport.axialD]
  linarith [hu.2]

theorem small_transfer {l s e : ℝ} (hl : 1≤l)
    (hs : 0≤s) (hse : s≤e) (he : e≤1/6) :
    TwoPositive.ASupport.charge (e-s)+s/600≤l*gain s+TwoPositive.ASupport.charge e := by
  have hm : MonotoneOn
      (fun u => TwoPositive.ASupport.axialCharge u+(599/600)*u) (Icc (0:ℝ) (1/6)) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun u _ => ((TwoPositive.ASupport.axial_derivative u).add
        ((hasDerivAt_id u).const_mul (599/600))).continuousAt.continuousWithinAt)
      (fun u _ => (TwoPositive.ASupport.axial_derivative u).add
        ((hasDerivAt_id u).const_mul (599/600)))
    intro u hu
    linarith [charge_small_slope (Ioo_subset_Icc_self hu)]
  have hh := hm (show e-s∈Icc 0 (1/6:ℝ) by constructor <;> linarith)
    (show e∈Icc 0 (1/6:ℝ) by constructor <;> linarith) (by linarith)
  have hg := gain_small (show s∈Icc 0 (1/6:ℝ) by constructor <;> linarith)
  have hprod := mul_le_mul_of_nonneg_right hl (hs.trans hg)
  rw [TwoPositive.ASupport.charge_low he,
    TwoPositive.ASupport.charge_low (show e-s≤1/6 by linarith)]
  linarith

theorem polynomial_gain_lower {s : ℝ} (hs : s∈Icc 0 (8/15:ℝ)) :
    (13/12)*aeval s PositiveTD.Certificate.S11+
      (82/125-(63/100)*s)*(aeval s PositiveTD.Certificate.C10-1)≤gain s := by
  have ht := PositiveTD.Certificate.taylor_bounds
    (show s∈Icc 0 frameCap by constructor <;> dsimp [frameCap] <;> linarith [hs.1,hs.2])
  have hb : 0≤82/125-(63/100)*s := by linarith [hs.2]
  have hh := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1) hb
  dsimp [gain]
  linarith [ht.2.1]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE
