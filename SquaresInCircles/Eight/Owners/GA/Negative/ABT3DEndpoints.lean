module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Owners.GA.Negative.EHSlopes
public import SquaresInCircles.Eight.Owners.GA.Positive.ATD0DVelocity
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3Data

/-!
# Eight squares: strict sorted-D endpoint positivity at c=1 and c=1.2

The full-circle comparison is used on its two certified domains; the
remaining c=1 domain uses the proved tangent-zero support formula.
These endpoints are independent of the later signed-D minorant.
-/

section
/-!
## The wider signed D envelope required by negative A and positive BT3

The actual sorted
support is unchanged.  Its new constants are k*=.68, alpha=.67 and
C*=1.2.  Positivity is proved only on the branches where it is used;
the reversed mixed quadrant is handled directly by diagonal support.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.DEnvelope
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3

abbrev K : ℝ := 17/25
abbrev Cmax : ℝ := 6/5
abbrev slope : ℝ := 67/100
def vstar (n : ℝ) : ℝ := V R K 1 n

theorem forward_force_positive {c t n : ℝ} (hc : c∈Icc 1 Cmax)
    (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    0<forceA c t (-n) ∧ 0<forceB c t (-n) := by
  have ht' := transport_trig ht
  have hn' := transport_trig hn
  have hs := mul_nonneg (by linarith [hc.1] : 0≤c) ht'.2.2.1
  have hcos := mul_le_mul_of_nonneg_right hc.1 (by linarith [ht'.1] : 0≤Real.cos t)
  dsimp [forceA,forceB]
  rw [Real.cos_neg,Real.sin_neg]
  constructor <;> linarith [ht'.1,hn'.1,hn'.2.2.2.1]

theorem positive_force_positive {c x y : ℝ} (hc : c∈Icc 1 Cmax)
    (hx : x∈Icc 0 frameCap) (hy : y∈Icc 0 frameCap) :
    0<forceA c x y ∧ 0<forceB c x y := by
  have hx' := transport_trig hx
  have hy' := transport_trig hy
  have hs := mul_nonneg (by linarith [hc.1] : 0≤c) hx'.2.2.1
  have hcos := mul_pos (by linarith [hc.1] : 0<c) (by linarith [hx'.1] : 0<Real.cos x)
  dsimp [forceA,forceB]
  constructor <;> linarith [hy'.1,hy'.2.2.1]

theorem negative_force_positive {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) :
    0<forceA c (-t) (-(n-t)) ∧ 0<forceB c (-t) (-(n-t)) := by
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hn.2⟩
  have hy : n-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1,hn.2]⟩
  have hnt := transport_trig hn
  have htt := transport_trig ht'
  have hyt := transport_trig hy
  have hcos := mul_le_mul_of_nonneg_right hc.1 (by linarith [htt.1] : 0≤Real.cos t)
  have hlast : 0<1-c*Real.sin n := by
    have hm := mul_le_mul_of_nonneg_right hc.2 hnt.2.2.1
    dsimp [Cmax] at hm
    linarith [hnt.2.2.2.1]
  have hf : 0<Real.cos (n-t)-c*Real.sin t := by
    by_cases ht0 : t=0
    · simpa [ht0] using (show 0<Real.cos n by linarith [hnt.1])
    have hst : 0<Real.sin t := Real.sin_pos_of_pos_of_lt_pi
      (lt_of_le_of_ne ht.1 (Ne.symm ht0))
      (by dsimp [frameCap] at ht'; linarith [ht'.2,Real.pi_gt_three])
    have hsn : 0<Real.sin n := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [ht.2,lt_of_le_of_ne ht.1 (Ne.symm ht0)])
      (by dsimp [frameCap] at hn; linarith [hn.2,Real.pi_gt_three])
    have hid : Real.sin n*(Real.cos (n-t)-c*Real.sin t)=
        Real.cos n*Real.sin (n-t)+(1-c*Real.sin n)*Real.sin t := by
      rw [Real.cos_sub,Real.sin_sub]
      nlinarith [congrArg (fun z : ℝ => z*Real.sin t) (Real.sin_sq_add_cos_sq n)]
    have hfirst := mul_nonneg (by linarith [hnt.1] : 0≤Real.cos n) hyt.2.2.1
    have hsecond := mul_pos hlast hst
    have hprod : 0<Real.sin n*(Real.cos (n-t)-c*Real.sin t) := by linarith
    by_contra hh
    have hm := mul_nonpos_of_nonneg_of_nonpos hsn.le (le_of_not_gt hh)
    linarith
  dsimp [forceA,forceB]
  simp only [Real.sin_neg,Real.cos_neg]
  exact ⟨by linarith,by linarith [htt.1,hyt.2.2.2.1]⟩

theorem one_angle_lower {c n : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) : vstar n≤D c 0 (-n) := by
  have hp := forward_force_positive (t:=0) hc (by norm_num [frameCap]) hn
  have hsup := sortedSupport_le_clipped hp.1.le hp.2.le
  have hminor := PositiveTD.negative_D_support_minorant
    (k:=K) (c:=c) (by norm_num [K])
    (by constructor <;> dsimp [Cmax,K] at hc ⊢ <;> linarith [hc.1,hc.2]) hn
  have hA : forceA c 0 (-n)=Real.cos n := by
    simp only [forceA,Real.sin_zero,mul_zero,zero_add,Real.cos_neg]
  have hB : forceB c 0 (-n)=c-Real.sin n := by
    simp only [forceB,Real.cos_zero,mul_one,Real.sin_neg]
    ring
  rw [hA,hB] at hsup
  have hclip : clippedSupport 1 c=(1+c)*GlobalGA.Secondary.diagonal := by
    simp only [clippedSupport,hc.1,↓reduceIte,diagonalSupport]
  simp only [PositiveTD.dSupportIncrement,Real.cos_neg,Real.sin_neg,← sub_eq_add_neg,
    hclip] at hminor
  simp only [DEnvelope.vstar,PositiveBT3.D,hA,hB,edgeWidth_zero,sub_self,mul_zero,zero_add]
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.DEnvelope
end
end
end

section
/-!
## The radical and tangent-zero bounds at the sorted-D endpoint

The change at n=3/8 is justified by the actual force
ratio and its derivative. All radical bounds follow from positive
squaring of the displayed rational constants.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.DEnvelope.DEndpoint
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open PositiveBT3
open PositiveTD.Certificate (S9 S11 C10 C12 taylor_bounds)

theorem coefficient_domain (e : End) : (coefficient e:ℝ)∈Icc 1 Cmax := by
  cases e <;> norm_num [coefficient,Cmax]

theorem radical_bounds : (cLower:ℝ)<GlobalGA.Secondary.diagonal ∧ axial<(aUpper:ℝ) ∧
    R*pairNorm K 1 0<(Tzero:ℝ) := by
  have hdb := diagonal_bounds
  have hN2 : (pairNorm K 1 0)^2=K^2+1 := by
    rw [pairNorm_zero,Real.sq_sqrt (by positivity)]
    ring
  have hprod : (R*pairNorm K 1 0)^2=qCap*(K^2+1) := by
    rw [mul_pow,radius_sq,hN2]
  have hax : Real.sqrt (qCap-1/4)<(aUpper:ℝ)+1/2 :=
    (Real.sqrt_lt' (by norm_num [aUpper])).mpr (by norm_num [qCap,aUpper])
  refine ⟨?_,?_,?_⟩
  · norm_num [cLower]
    linarith [hdb.1]
  · dsimp only [axial]
    linarith
  · apply lt_of_pow_lt_pow_left₀ 2 (by norm_num [Tzero])
    rw [hprod]
    norm_num [qCap,K,Tzero]

theorem sine9_hasDerivAt (x : ℝ) : HasDerivAt Arithmetic.sin9 (Arithmetic.cos8 x) x := by
  have h := ((((hasDerivAt_id' x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
    ((hasDerivAt_pow 5 x).div_const 120)).sub ((hasDerivAt_pow 7 x).div_const 5040)).add
    ((hasDerivAt_pow 9 x).div_const 362880)
  refine h.congr_deriv ?_
  rw [Arithmetic.cos8]
  push_cast
  ring

theorem sine9_range {x : ℝ} (hx : x∈Icc 0 frameCap) :
    0≤aeval x S9 ∧ aeval x S9<(129/200:ℝ) := by
  have hm : MonotoneOn Arithmetic.sin9 (Icc (0:ℝ) frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun x _ => (sine9_hasDerivAt x).continuousAt.continuousWithinAt)
      (fun x _ => sine9_hasDerivAt x)
    intro x hx
    have hh := Arithmetic.cos_le_cos8 hx.1.le
    have hc := (transport_trig (Ioo_subset_Icc_self hx)).1
    linarith
  have h0 := hm (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hx hx.1
  have h1 := hm hx (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hx.2
  have he : Arithmetic.sin9 frameCap<(129/200:ℝ) := by
    norm_num [Arithmetic.sin9,Arithmetic.sin7,frameCap]
  simp only [PositiveTD.Certificate.S9_eval]
  exact ⟨by simpa [Arithmetic.sin9,Arithmetic.sin7] using h0,h1.trans_lt he⟩

theorem norm_polynomial_bounds (e : End) {n : ℝ} (hn : n∈Icc 0 frameCap) :
    0≤aeval n (P e) ∧ (29/50:ℝ)<aeval n H ∧
    pairNorm 1 (coefficient e:ℝ) (frameCap-n)≤Real.sqrt (aeval n (P e)) ∧
    Real.sqrt (aeval n H)≤pairNorm K 1 (-n) := by
  have hother : frameCap-n∈Icc 0 frameCap := ⟨by linarith [hn.2],by linarith [hn.1]⟩
  have hs := sine9_range hn
  have hso := sine9_range hother
  have hta := (taylor_bounds hother).2.2.1
  have htn := (taylor_bounds hn).2.2.1
  have hc := coefficient_domain e
  have hP : aeval n (P e)=1+(coefficient e:ℝ)^2+
      2*(coefficient e:ℝ)*aeval (frameCap-n) S9 := by
    simp [P,aeval_comp,h,frameCap]
  have hH : aeval n H=1+K^2-2*K*aeval n S9 := by simp [H,kstar,K]
  have hP0 : 0≤aeval n (P e) := by
    rw [hP]
    have := mul_nonneg (show 0≤2*(coefficient e:ℝ) by linarith [hc.1]) hso.1
    nlinarith [sq_nonneg (coefficient e:ℝ)]
  have hH0 : (29/50:ℝ)<aeval n H := by
    rw [hH]
    have hs2 := hs.2
    norm_num [K] at hs2 ⊢
    linarith
  refine ⟨hP0,hH0,?_,?_⟩
  · apply Real.sqrt_le_sqrt
    rw [hP]
    have hh := mul_le_mul_of_nonneg_left hta
      (show 0≤2*(coefficient e:ℝ) by linarith [hc.1])
    linarith
  · apply Real.sqrt_le_sqrt
    rw [hH]
    simp only [Real.sin_neg]
    have hh := mul_le_mul_of_nonneg_left htn (by norm_num [K] : (0:ℝ)≤2*K)
    linarith

def axisRatio (n : ℝ) : ℝ := forceB 1 frameCap (-n)/forceA 1 frameCap (-n)

theorem axisRatio_hasDerivAt {n : ℝ} (hn : n∈Icc 0 frameCap) :
    HasDerivAt axisRatio ((-1+Real.sin (n-frameCap))/(forceA 1 frameCap (-n))^2) n := by
  have hp := PositiveBT3.force_positive (c:=1) (x:=frameCap) (y:=-n)
    (by norm_num [PositiveBT3.Cmax])
    (by norm_num [frameCap]) (by rw [abs_neg,abs_of_nonneg hn.1]; exact hn.2)
  have hden : forceA 1 frameCap (-n)≠0 := hp.1.ne'
  have hF : HasDerivAt (fun n => forceA 1 frameCap (-n)) (-Real.sin n) n := by
    simpa [forceA] using (Real.hasDerivAt_cos n).const_add (Real.sin frameCap)
  have hG : HasDerivAt (fun n => forceB 1 frameCap (-n)) (-Real.cos n) n := by
    have hfun : (fun n => forceB 1 frameCap (-n))=fun n => Real.cos frameCap-Real.sin n := by
      funext m
      simp only [forceB,one_mul,Real.sin_neg,sub_eq_add_neg]
    rw [hfun]
    exact (Real.hasDerivAt_sin n).const_sub (Real.cos frameCap)
  convert hG.div hF hden using 1
  · funext m
    rfl
  rw [div_left_inj' (pow_ne_zero 2 hden)]
  simp only [forceA,forceB,Real.cos_neg,Real.sin_neg,one_mul,Real.sin_sub]
  linear_combination Real.sin_sq_add_cos_sq n

theorem axisRatio_antitone : AntitoneOn axisRatio (Icc (0:ℝ) frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun n hn => (axisRatio_hasDerivAt hn).continuousAt.continuousWithinAt)
    (fun n hn => axisRatio_hasDerivAt (Ioo_subset_Icc_self hn))
  intro n hn
  have hs : Real.sin (n-frameCap)≤0 := by
    have hh := (transport_trig
      (show frameCap-n∈Icc 0 frameCap from ⟨by linarith [hn.2],by linarith [hn.1]⟩)).2.2.1
    rw [show n-frameCap=-(frameCap-n) by ring,Real.sin_neg]
    linarith
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)

theorem axis_transition_reserve :
    (121/5000:ℚ)<(C10.eval cut+S11.eval h)/2-
      (aUpper+1/2)*(C12.eval h-S11.eval cut) := by
  norm_num [C10,PositiveTD.Certificate.C4,S11,S9,PositiveTD.Certificate.S5,C12,cut,h,aUpper]

theorem axis_at_cut :
    (axial+1/2)*forceB 1 frameCap (-(3/8))<forceA 1 frameCap (-(3/8))/2 := by
  have hh := taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hb := taylor_bounds (show (3/8:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have hp := PositiveBT3.force_positive (c:=1) (x:=frameCap) (y:=-(3/8))
    (by norm_num [PositiveBT3.Cmax])
    (by norm_num [frameCap]) (by norm_num [frameCap] : |-(3/8:ℝ)|≤frameCap)
  have hcut : ((cut:ℚ):ℝ)=3/8 := by norm_num [cut]
  have hhh : ((h:ℚ):ℝ)=frameCap := by norm_num [h,frameCap]
  have hflow : ((C10.eval cut+S11.eval h:ℚ):ℝ)≤forceA 1 frameCap (-(3/8)) := by
    rw [Rat.cast_add,← rational_aeval,← rational_aeval,hcut,hhh]
    simp only [forceA,one_mul,Real.cos_neg]
    linarith [hb.2.2.2.2.1,hh.2.1]
  have hghi : forceB 1 frameCap (-(3/8))≤((C12.eval h-S11.eval cut:ℚ):ℝ) := by
    rw [Rat.cast_sub,← rational_aeval,← rational_aeval,hcut,hhh]
    simp only [forceB,one_mul,Real.sin_neg]
    linarith [hh.2.2.2.2.2,hb.2.1]
  have hfirst := mul_le_mul_of_nonneg_right radical_bounds.2.1.le hp.2.le
  have hsecond := mul_le_mul_of_nonneg_left hghi
    (show 0≤(aUpper:ℝ)+1/2 by norm_num [aUpper])
  have hr : (121/5000:ℝ)<((C10.eval cut+S11.eval h:ℚ):ℝ)/2-
      ((aUpper:ℝ)+1/2)*((C12.eval h-S11.eval cut:ℚ):ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr axis_transition_reserve
    push_cast at hh ⊢
    linarith
  nlinarith

theorem axis_force {n : ℝ} (hn : n∈Icc (3/8:ℝ) frameCap) :
    (axial+1/2)*forceB 1 frameCap (-n)≤forceA 1 frameCap (-n)/2 := by
  have hn0 : n∈Icc 0 frameCap := ⟨by linarith [hn.1],hn.2⟩
  have hb : (3/8:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hp := PositiveBT3.force_positive (c:=1) (x:=frameCap) (y:=-n)
    (by norm_num [PositiveBT3.Cmax])
    (by norm_num [frameCap]) (by rw [abs_neg,abs_of_nonneg hn0.1]; exact hn0.2)
  have hpb := PositiveBT3.force_positive (c:=1) (x:=frameCap) (y:=-(3/8))
    (by norm_num [PositiveBT3.Cmax])
    (by norm_num [frameCap]) (by norm_num [frameCap] : |-(3/8:ℝ)|≤frameCap)
  have hm := axisRatio_antitone hb hn0 hn.1
  have hA : 0<axial+1/2 := by linarith [axial_bounds.1]
  have hscaled := mul_le_mul_of_nonneg_left hm hA.le
  have hcut : (axial+1/2)*axisRatio (3/8)<1/2 := by
    dsimp [axisRatio]
    rw [← mul_div_assoc,div_lt_iff₀ hpb.1]
    linarith [axis_at_cut]
  have hbound : (axial+1/2)*axisRatio n≤1/2 := by linarith
  dsimp [axisRatio] at hbound
  rw [← mul_div_assoc,div_le_iff₀ hp.1] at hbound
  linarith

theorem axis_support {n : ℝ} (hn : n∈Icc (3/8:ℝ) frameCap) :
    sortedSupport (forceA 1 frameCap (-n)) (forceB 1 frameCap (-n))=
      axial*forceA 1 frameCap (-n) := by
  have hn0 : n∈Icc 0 frameCap := ⟨by linarith [hn.1],hn.2⟩
  have hp := PositiveBT3.force_positive (c:=1) (x:=frameCap) (y:=-n)
    (by norm_num [PositiveBT3.Cmax])
    (by norm_num [frameCap]) (by rw [abs_neg,abs_of_nonneg hn0.1]; exact hn0.2)
  simpa only [mul_comm] using sortedSupport_axis hp.2 (axis_force hn)

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.DEnvelope.DEndpoint
end
end
end

section
/-!
## The charged H circle with a negative EH1 secant

The secant multiplier varies on the whole interval `[1, 1.033]`. The general curvature bound of
the ordinary norms gives concavity on each sign of the angle (`positive_concave`,
`negative_concave`). At the two intrinsic angle endpoints the H block itself has ample reserve:
positive-square bounds on its three norms suffice uniformly in the multiplier (`positive_cap`,
`negative_cap`). The final statement keeps the whole support of the H circle (`actual_lower`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHSecant
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity Secondary

abbrev k : ℝ := 39/50
abbrev L : ℝ := 103/100

def charged (u v : ℝ) : ℝ :=
  k*psi v-R*(pairNorm k u v-pairNorm k u 0)+L*v

def negative (u w : ℝ) : ℝ :=
  k*(Real.cos w-1)-R*(pairNorm k u (-w)-pairNorm k u 0)-L*w

def negativeD (u w : ℝ) : ℝ :=
  -k*Real.sin w+R*normD1 k u (-w)-L

theorem coefficient_range {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    0<k ∧ k≤u ∧ u≤2*k := by
  dsimp [k]
  exact ⟨by norm_num,by linarith [hu.1],by linarith [hu.2]⟩

theorem positive_concave {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    ConcaveOn ℝ (Icc 0 frameCap)
      (fun v => k*(PositiveAngularEnvelope.phi v-1)-R*(pairNorm k u v-pairNorm k u 0)+L*v) := by
  have hc := coefficient_range hu
  have hh := PositiveATD0.chargedMixed_concave_P hc.1 hc.2.1 hc.2.2
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
  simpa [PositiveATD0.chargedMixed,mixedBlock,PositiveATD0.charge,L] using hh

theorem negative_hasDerivAt {u w : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ))
    (hw : w∈Icc 0 frameCap) : HasDerivAt (negative u) (negativeD u w) w := by
  have hc := coefficient_range hu
  have hn := (pairNorm_hasDerivAt hc.1 (hc.1.trans_le hc.2.1)
    (t := -w) (by simpa [abs_of_nonneg hw.1] using hw.2)).comp w
      (hasDerivAt_id w).neg
  convert (((((Real.hasDerivAt_cos w).sub_const 1).const_mul k).sub
    ((hn.sub_const (pairNorm k u 0)).const_mul R)).sub
      ((hasDerivAt_id w).const_mul L)) using 1
  · rfl
  · dsimp [negativeD]
    ring

theorem negativeD_hasDerivAt {u w : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ))
    (hw : w∈Icc 0 frameCap) :
    HasDerivAt (negativeD u) (curvature R k u (-w)-k*Real.cos w) w := by
  have hc := coefficient_range hu
  have hn := (normD1_hasDerivAt hc.1 (hc.1.trans_le hc.2.1)
    (t := -w) (by simpa [abs_of_nonneg hw.1] using hw.2)).comp w
      (hasDerivAt_id w).neg
  convert ((((Real.hasDerivAt_sin w).const_mul (-k)).add
    (hn.const_mul R)).sub_const L) using 1
  · rfl
  · dsimp [curvature]
    ring

theorem negative_concave {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    ConcaveOn ℝ (Icc 0 frameCap) (negative u) := by
  have hc := coefficient_range hu
  apply concave_of_deriv2 (fun w hw => negative_hasDerivAt hu hw)
    (fun w hw => negativeD_hasDerivAt hu hw)
  intro w hw
  have hupper := curvature_negative_upper (Real.sqrt_nonneg qCap)
    hc.1 (hc.1.trans_le hc.2.1)
    (show -w∈Icc (-frameCap) 0 by constructor <;> linarith [hw.1,hw.2])
  have hconstants := curvature_constant_bounds (R := R) (Real.sqrt_nonneg qCap)
    (by rw [radius_sq]) hc.1 hc.2.1 hc.2.2
  have hcos := (transport_trig hw).1
  dsimp [k] at *
  linarith [hconstants.1]

theorem norm_zero_lower {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    (6341/5000:ℝ)<pairNorm k u 0 := by
  have hc := coefficient_range hu
  have hs := pairNorm_sq hc.1 (hc.1.trans_le hc.2.1)
    (t := 0) (by norm_num [frameCap])
  have hp := pairNorm_pos hc.1 (hc.1.trans_le hc.2.1)
    (t := 0) (by norm_num [frameCap])
  have hu2 : (1:ℝ)≤u^2 := by nlinarith [hu.1]
  simp only [pairEnergy,pairProduct,Real.sin_zero,mul_zero,add_zero] at hs
  apply lt_of_pow_lt_pow_left₀ 2 hp.le
  rw [hs]
  norm_num [k]
  linarith

theorem norm_positive_upper {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    pairNorm k u frameCap<(33/20:ℝ) := by
  have hc := coefficient_range hu
  have hs := pairNorm_sq hc.1 (hc.1.trans_le hc.2.1)
    (t := frameCap) (by norm_num [frameCap])
  have hp := pairNorm_pos hc.1 (hc.1.trans_le hc.2.1)
    (t := frameCap) (by norm_num [frameCap])
  have ht := transport_trig (by norm_num [frameCap] : frameCap∈Icc 0 frameCap)
  have hu0 : 0≤u := by linarith [hu.1]
  have hu2 := pow_le_pow_left₀ hu0 hu.2 2
  have hm := mul_le_mul hu.2 ht.2.2.2.1.le ht.2.2.1
    (by norm_num : (0:ℝ)≤1033/1000)
  norm_num [pairEnergy,pairProduct,k] at hs
  nlinarith

theorem norm_negative_upper {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    pairNorm k u (-frameCap)<(799/1000:ℝ) := by
  have hc := coefficient_range hu
  have hs := pairNorm_sq hc.1 (hc.1.trans_le hc.2.1)
    (t := -frameCap) (by norm_num [frameCap])
  have hp := pairNorm_pos hc.1 (hc.1.trans_le hc.2.1)
    (t := -frameCap) (by norm_num [frameCap])
  have ht := transport_trig (by norm_num [frameCap] : frameCap∈Icc 0 frameCap)
  have hsin : (3221/5000:ℝ)<Real.sin frameCap := by
    have hh := cap_trig.1
    norm_num [Arithmetic.sin7,frameCap] at hh
    linarith
  have hfactor : 0≤(1033/1000:ℝ)+u-2*k*Real.sin frameCap := by
    dsimp [k]
    linarith [hu.1,ht.2.2.2.1]
  have hm := mul_nonneg (sub_nonneg.mpr hu.2) hfactor
  norm_num [pairEnergy,pairProduct,k,Real.sin_neg] at hs
  dsimp [k] at hm
  nlinarith

theorem positive_cap {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    0<k*(PositiveAngularEnvelope.phi frameCap-1)-R*(pairNorm k u frameCap-pairNorm k u 0)+L*frameCap := by
  have hn0 := radius_norm_lower (by norm_num : (0:ℝ)<6341/5000) (norm_zero_lower hu)
  have hnp := radius_norm_upper (by norm_num : (0:ℝ)<33/20) (norm_positive_upper hu)
  have hphi := phi_cap_lower
  dsimp [k,L,frameCap] at *
  nlinarith

theorem negative_cap {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    0<negative u frameCap := by
  have hn0 := radius_norm_lower (by norm_num : (0:ℝ)<6341/5000) (norm_zero_lower hu)
  have hnn := radius_norm_upper (by norm_num : (0:ℝ)<799/1000) (norm_negative_upper hu)
  have hcos := (transport_trig
    (by norm_num [frameCap] : frameCap∈Icc 0 frameCap)).1
  dsimp [negative,k,L,frameCap]
  nlinarith

theorem charged_nonneg {u v : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ))
    (hv : |v|≤frameCap) : 0≤charged u v := by
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  by_cases hpos : 0≤v
  · have hvi : v∈Icc 0 frameCap := ⟨hpos,by simpa [abs_of_nonneg hpos] using hv⟩
    have hm := (positive_concave hu).min_le_of_mem_Icc hz hh hvi
    have hmin : 0 ≤ min
        (k*(PositiveAngularEnvelope.phi 0-1)-R*(pairNorm k u 0-pairNorm k u 0)+L*0)
        (k*(PositiveAngularEnvelope.phi frameCap-1)-R*(pairNorm k u frameCap-pairNorm k u 0)+
          L*frameCap) :=
      le_min (by simp [PositiveAngularEnvelope.phi]) (positive_cap hu).le
    have hval := hmin.trans hm
    simpa [charged,psi_positive hvi] using hval
  · have hvi : -v∈Icc 0 frameCap :=
      ⟨by linarith,by simpa [abs_of_neg (lt_of_not_ge hpos)] using hv⟩
    have hm := (negative_concave hu).min_le_of_mem_Icc hz hh hvi
    have hmin : 0 ≤ min (negative u 0) (negative u frameCap) :=
      le_min (by simp [negative]) (negative_cap hu).le
    have hval := hmin.trans hm
    have he : charged u v=negative u (-v) := by
      have hpsi := psi_negative hvi
      simp only [neg_neg] at hpsi
      simp only [charged,negative,hpsi,Real.cos_neg,neg_neg]
      ring
    rw [he]
    exact hval

/-- The support identity includes the secant H coefficient and the signed HG angle. -/
theorem support_lower {u v : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ))
    (hv : |v|≤frameCap) :
    k+u-fullSupport u k≤
      k*edgeWidth v+u-fullSupport (u+k*Real.sin v) (k*Real.cos v)+L*v := by
  have h := charged_nonneg hu hv
  have he := pair_full_identity (p := k) (q := u) (a := v) (b := 0)
    hv (by norm_num [frameCap])
  simp only [Secondary.chargedPair,pairF,pairG,Real.cos_zero,Real.sin_zero,mul_one,
    mul_zero,add_zero,edgeWidth_zero,sub_self,psi_zero] at he
  dsimp [charged] at h
  linarith

/-- The bound holds at the point H of the cycle, contained in the disk; no support maximizer
takes its place. -/
theorem actual_lower {q u v : ℝ} {H : SignedPoint}
    (hy : 0≤H.y) (hc : H.Contained q) (hq : q≤qCap)
    (hu : u∈Icc 1 (1033/1000:ℝ)) (hv : |v|≤frameCap) :
    k+u-fullSupport u k≤
      k*edgeWidth v+u-((u+k*Real.sin v)*H.a+k*Real.cos v*H.y)+L*v := by
  have hsup := actual_full_support (f := u+k*Real.sin v) (g := k*Real.cos v) hy hc hq
  have hlow := support_lower hu hv
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeEHSecant
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.DEnvelope.DEndpoint
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity
open PositiveBT3
open PositiveTD.Certificate (S9 S11 C10 C12 taylor_bounds)

theorem phi_lower : (phiLower:ℝ)≤Real.cos frameCap+Real.sin frameCap := by
  have hh := taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hhh : ((h:ℚ):ℝ)=frameCap := by norm_num [h,frameCap]
  rw [phiLower,Rat.cast_add,← rational_aeval,← rational_aeval,hhh]
  linarith [hh.2.2.2.2.1,hh.2.1]

theorem full_lower (e : End) {n : ℝ} (hn : n∈Icc 0 frameCap) :
    (constant e:ℝ)-R*Real.sqrt (aeval n (P e))+R*Real.sqrt (aeval n H)≤
      D (coefficient e:ℝ) frameCap (-n)+slope*frameCap-vstar n := by
  have hc := coefficient_domain e
  have hR : 0≤R := Real.sqrt_nonneg qCap
  have hnpoly := norm_polynomial_bounds e hn
  have hnormP := mul_le_mul_of_nonneg_left hnpoly.2.2.1 hR
  have hnormH := mul_le_mul_of_nonneg_left hnpoly.2.2.2 hR
  have hphi := mul_le_mul_of_nonneg_left phi_lower (by linarith [hc.1] : 0≤(coefficient e:ℝ))
  have hd := mul_le_mul_of_nonneg_left radical_bounds.1.le
    (by linarith [hc.1] : 0≤1+(coefficient e:ℝ))
  have hzero := radical_bounds.2.2
  have hfull := fullD_lower (c:=(coefficient e:ℝ)) (x:=frameCap) (y:=-n)
    (by norm_num [frameCap]) (by rw [abs_neg,abs_of_nonneg hn.1]; exact hn.2)
  rw [fullD_mixed (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hn] at hfull
  have hcst : (constant e:ℝ)=
      (coefficient e:ℝ)*(phiLower:ℝ)+1+
        ((coefficient e:ℝ)+1)*((cLower:ℝ)-1/2)+slope*frameCap-(Tzero:ℝ) := by
    simp [constant,slope,h,frameCap]
  rw [hcst]
  dsimp only [DEnvelope.vstar,V]
  have hcL : (cLower:ℝ)=449607/500000 := by norm_num [cLower]
  have hT : (Tzero:ℝ)=2392942424/1000000000 := by norm_num [Tzero]
  rw [hcL] at hd ⊢
  rw [hT] at hzero ⊢
  generalize slope*frameCap=sf
  linarith

/-- The squared comparison does not require a sign on the isolated
polynomial difference Q(P-H)-A². -/
theorem radical_gap_positive {A P H : ℝ} (hA : 0<A) (hP : 0≤P) (hH : 0<H)
    (hZ : 0<4*A^2*qCap*H-(qCap*(P-H)-A^2)^2) :
    0<A-R*Real.sqrt P+R*Real.sqrt H := by
  have hR : 0<R := by linarith [radius_bounds.1]
  have hX : 0≤R*Real.sqrt P := mul_nonneg hR.le (Real.sqrt_nonneg _)
  have hY : 0<R*Real.sqrt H := mul_pos hR (Real.sqrt_pos.mpr hH)
  have hX2 : (R*Real.sqrt P)^2=qCap*P := by rw [mul_pow,radius_sq,Real.sq_sqrt hP]
  have hY2 : (R*Real.sqrt H)^2=qCap*H := by rw [mul_pow,radius_sq,Real.sq_sqrt hH.le]
  have hright : 0≤2*A*(R*Real.sqrt H) := by positivity
  have hright2 : (2*A*(R*Real.sqrt H))^2=4*A^2*qCap*H := by
    rw [mul_pow,mul_pow,hY2]
    ring
  have hmiddle : qCap*(P-H)-A^2<2*A*(R*Real.sqrt H) := by
    by_contra hh
    have hs := pow_le_pow_left₀ hright (le_of_not_gt hh) 2
    nlinarith only [hs,hright2,hZ]
  have hsum : 0≤A+R*Real.sqrt H := by linarith
  have hcross : R*Real.sqrt P<A+R*Real.sqrt H := by
    by_contra hh
    have hs := pow_le_pow_left₀ hsum (le_of_not_gt hh) 2
    nlinarith only [hs,hX2,hY2,hmiddle]
  linarith

theorem axis_gap_positive {A H : ℝ} (hH : 0<H) (hY : 0<qCap*H-A^2) :
    0<A+R*Real.sqrt H := by
  have hR : 0<R := by linarith [radius_bounds.1]
  have hroot : 0<R*Real.sqrt H := mul_pos hR (Real.sqrt_pos.mpr hH)
  have hsquare : (R*Real.sqrt H)^2=qCap*H := by
    rw [mul_pow,radius_sq,Real.sq_sqrt hH.le]
  by_contra hh
  have hle : R*Real.sqrt H≤-A := by linarith
  have hpow := pow_le_pow_left₀ hroot.le hle 2
  nlinarith

theorem full_certificate_positive (e : End) {n : ℝ}
    (hn : n∈Icc 0 frameCap) (hZ : 0<aeval n (Z e)) :
    0<D (coefficient e:ℝ) frameCap (-n)+slope*frameCap-vstar n := by
  have hA : (0:ℝ)<(constant e:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr (positive_constants e)
    push_cast at hh
    linarith
  have hpoly := norm_polynomial_bounds e hn
  have hZ' : 0<4*(constant e:ℝ)^2*qCap*aeval n H-
      (qCap*(aeval n (P e)-aeval n H)-(constant e:ℝ)^2)^2 := by
    simpa [Z,Q,qCap] using hZ
  exact (radical_gap_positive hA hpoly.1 (by linarith [hpoly.2.1]) hZ').trans_le
    (full_lower e hn)

theorem axis_identity {n : ℝ} (hn : n∈Icc (3/8:ℝ) frameCap) :
    D 1 frameCap (-n)+slope*frameCap-vstar n=
      (Real.cos frameCap+Real.sin frameCap-1)/2-axial*Real.sin frameCap+
      2*GlobalGA.Secondary.diagonal+slope*frameCap+1/2-R*pairNorm K 1 0-
      (axial+1/2)*Real.cos n+(1/2)*Real.sin n+R*pairNorm K 1 (-n) := by
  have hn0 : n∈Icc 0 frameCap := ⟨by linarith [hn.1],hn.2⟩
  rw [PositiveBT3.D,axis_support hn,edgeWidth_positive_formula
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]),edgeWidth_negative_formula hn0]
  simp only [forceA,Real.cos_neg,one_mul]
  dsimp only [DEnvelope.vstar,V]
  ring

theorem axis_lower {n : ℝ} (hn : n∈Icc (3/8:ℝ) frameCap) :
    aeval n axisA+R*Real.sqrt (aeval n H)≤
      D 1 frameCap (-n)+slope*frameCap-vstar n := by
  have hn0 : n∈Icc 0 frameCap := ⟨by linarith [hn.1],hn.2⟩
  have hh := taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hnT := taylor_bounds hn0
  have hR : 0≤R := Real.sqrt_nonneg qCap
  have hnorm := mul_le_mul_of_nonneg_left (norm_polynomial_bounds .one hn0).2.2.2 hR
  have hsinH := (transport_trig
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).2.2.1
  have hcosN : 0≤Real.cos n := by linarith [(transport_trig hn0).1]
  have haSin := mul_le_mul_of_nonneg_right radical_bounds.2.1.le hsinH
  have hSin := mul_le_mul_of_nonneg_left hh.2.2.1
    (show 0≤(aUpper:ℝ) by norm_num [aUpper])
  have haCos := mul_le_mul_of_nonneg_right radical_bounds.2.1.le hcosN
  have hCos := mul_le_mul_of_nonneg_left hnT.2.2.2.2.2
    (show 0≤(aUpper:ℝ)+1/2 by norm_num [aUpper])
  have heval : aeval n axisA=(axisConstant:ℝ)-
      ((aUpper:ℝ)+1/2)*aeval n C12+(1/2)*aeval n S11 := by simp [axisA]
  have hconst : (axisConstant:ℝ)=((phiLower:ℝ)-1)/2-
      (aUpper:ℝ)*aeval frameCap S9+2*(cLower:ℝ)+slope*frameCap+1/2-(Tzero:ℝ) := by
    have hhh : ((h:ℚ):ℝ)=frameCap := by norm_num [h,frameCap]
    rw [axisConstant]
    push_cast
    rw [← rational_aeval,hhh]
  rw [heval,hconst,axis_identity hn]
  have h1 := phi_lower
  have h2 := radical_bounds.1
  have h3 := radical_bounds.2.2
  have hcL : (cLower:ℝ)=449607/500000 := by norm_num [cLower]
  have hT : (Tzero:ℝ)=2392942424/1000000000 := by norm_num [Tzero]
  have hU : (aUpper:ℝ)=1414575672/1000000000 := by norm_num [aUpper]
  rw [hcL] at h2 ⊢
  rw [hT] at h3 ⊢
  rw [hU] at haSin hSin haCos hCos ⊢
  generalize slope*frameCap=sf
  linarith [hnT.2.1]

theorem axis_certificate_positive {n : ℝ} (hn : n∈Icc (3/8:ℝ) frameCap) :
    0<D 1 frameCap (-n)+slope*frameCap-vstar n := by
  have hn0 : n∈Icc 0 frameCap := ⟨by linarith [hn.1],hn.2⟩
  have hpoly := axis_positive hn
  have hH := (norm_polynomial_bounds .one hn0).2.1
  have hY : 0<qCap*aeval n H-(aeval n axisA)^2 := by
    have hh : 0<aeval n Y := by linarith
    simpa [Y,Q,qCap] using hh
  exact (axis_gap_positive (by linarith) hY).trans_le (axis_lower hn)

/-- The two intrinsic endpoints of the c-concavity argument, including
the complete closed n interval and the tangent-zero transition. -/
theorem endpoint (e : End) {n : ℝ} (hn : n∈Icc 0 frameCap) :
    0<D (coefficient e:ℝ) frameCap (-n)+slope*frameCap-vstar n := by
  cases e
  · by_cases hcut : n≤3/8
    · exact full_certificate_positive .one hn (by linarith [one_positive ⟨hn.1,hcut⟩])
    · have h1 : (coefficient .one:ℝ)=1 := by norm_num [coefficient]
      rw [h1]
      exact axis_certificate_positive ⟨(le_of_not_ge hcut),hn.2⟩
  · exact full_certificate_positive .upper hn (by linarith [upper_positive hn])

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.DEnvelope.DEndpoint
end
end
end
