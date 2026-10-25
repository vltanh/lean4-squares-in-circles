module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Arithmetic.HighOrderTaylor
public import SquaresInCircles.Eight.Frames.Core.LowCancellation
public import SquaresInCircles.Eight.Frames.Mid.Arc

/-!
# Eight squares: exact contact data for the core/middle cancellation support

All numbers refer to the single intrinsic contact angle `27/25`.
The sine and cosine bounds are alternating Taylor inequalities; both
radical bounds follow by squaring.  The support and its derivative are
then enclosed by sign-aware rational substitutions.  No sample of a
continuous curvature or covering interval is used.
-/

section
/-!
## The actual high-endpoint primary continuation for core/middle pairs

The complete interval from `1.2` to `1.94` is treated analytically.
Before the quarter turn the derivative is concave and initially positive,
which rules out an interior minimum.  After the quarter turn the actual
derivative has a uniform positive lower bound.  Both sides meet at the
same exact scalar value, with its proved strict reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreMidPrimaryContinuation
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FramePairCalculus FrameCoreMidScalars

def dh : ℝ := a2-1/2
def k : ℝ := 13/12
def G1 (x : ℝ) : ℝ :=
  x-(9/100)*(Real.sin x+Real.cos x-1)-M2+g/2+
    g*(k*Real.cos x-dh)/Real.sin x
def G1d (x : ℝ) : ℝ :=
  1+(9/100)*(Real.sin x-Real.cos x)+
    g*(dh*Real.cos x-k)/(Real.sin x)^2
def G1dd (x : ℝ) : ℝ :=
  (9/100)*(Real.cos x+Real.sin x)+
    g*(2*k*Real.cos x-dh*(1+(Real.cos x)^2))/(Real.sin x)^3
def G1ddd (x : ℝ) : ℝ :=
  (9/100)*(Real.cos x-Real.sin x)+
    g*(dh*Real.cos x*(5+(Real.cos x)^2)-2*k*(1+2*(Real.cos x)^2))/(Real.sin x)^4

def G2 (x : ℝ) : ℝ :=
  x-(9/100)*(Real.sin x-Real.cos x-1)-M2+g/2+
    g*((1/12)*Real.cos x-dh)/Real.sin x
def G2d (x : ℝ) : ℝ :=
  1-(9/100)*(Real.sin x+Real.cos x)+
    g*(dh*Real.cos x-1/12)/(Real.sin x)^2

def G (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x-M2+
    (g/Real.sin x)*(pairWidth x-a2+ac*Real.cos x)

theorem G1_deriv {x : ℝ} (hs : Real.sin x≠0) : HasDerivAt G1 (G1d x) x := by
  have hbase := ((((hasDerivAt_id' x).fun_sub
    ((((Real.hasDerivAt_sin x).fun_add (Real.hasDerivAt_cos x)).sub_const 1).const_mul
      (9/100))).sub_const M2).add_const (g/2))
  have hquot := ((((Real.hasDerivAt_cos x).const_mul k).sub_const dh).const_mul g).fun_div
    (Real.hasDerivAt_sin x) hs
  refine (hbase.fun_add hquot).congr_deriv ?_
  have hpy := Real.sin_sq_add_cos_sq x
  dsimp only [G1d]
  field_simp
  linear_combination (-100*g*k)*hpy

theorem G1d_deriv {x : ℝ} (hs : Real.sin x≠0) : HasDerivAt G1d (G1dd x) x := by
  have hbase := (((Real.hasDerivAt_sin x).fun_sub (Real.hasDerivAt_cos x)).const_mul
    (9/100)).const_add 1
  have hquot := ((((Real.hasDerivAt_cos x).const_mul dh).sub_const k).const_mul g).fun_div
    ((Real.hasDerivAt_sin x).fun_pow 2) (pow_ne_zero 2 hs)
  refine (hbase.fun_add hquot).congr_deriv ?_
  have hpy := Real.sin_sq_add_cos_sq x
  dsimp only [G1dd]
  field_simp
  linear_combination (-100*Real.sin x*g*dh)*hpy

theorem G1dd_deriv {x : ℝ} (hs : Real.sin x≠0) : HasDerivAt G1dd (G1ddd x) x := by
  have hbase := ((Real.hasDerivAt_cos x).fun_add (Real.hasDerivAt_sin x)).const_mul (9/100)
  have hnum := (((Real.hasDerivAt_cos x).const_mul (2*k)).fun_sub
    ((((Real.hasDerivAt_cos x).fun_pow 2).const_add 1).const_mul dh)).const_mul g
  have hquot := hnum.fun_div ((Real.hasDerivAt_sin x).fun_pow 3) (pow_ne_zero 3 hs)
  refine (hbase.fun_add hquot).congr_deriv ?_
  have hpy := Real.sin_sq_add_cos_sq x
  dsimp only [G1ddd]
  field_simp
  linear_combination (200*(Real.sin x)^2*g*(Real.cos x*dh-k))*hpy

theorem G2_deriv {x : ℝ} (hs : Real.sin x≠0) : HasDerivAt G2 (G2d x) x := by
  have hbase := ((((hasDerivAt_id' x).fun_sub
    ((((Real.hasDerivAt_sin x).fun_sub (Real.hasDerivAt_cos x)).sub_const 1).const_mul
      (9/100))).sub_const M2).add_const (g/2))
  have hquot := ((((Real.hasDerivAt_cos x).const_mul (1/12)).sub_const dh).const_mul g).fun_div
    (Real.hasDerivAt_sin x) hs
  refine (hbase.fun_add hquot).congr_deriv ?_
  have hpy := Real.sin_sq_add_cos_sq x
  dsimp only [G2d]
  field_simp
  linear_combination (-100*g)*hpy

theorem interval_sine {x : ℝ} (hx : x∈Icc (6/5:ℝ) (97/50)) :
    (233/250:ℝ)<Real.sin x := by
  exact sin_endpoint_lower (by norm_num)
    (by linarith [FrameLowPair.pi_lower] : (97/50:ℝ)≤Real.pi) hx
    (by linarith [trig_six_fifths.1]) trig_primary_cut.1

theorem first_trig {x : ℝ} (hx : x∈Icc (6/5:ℝ) (Real.pi/2)) :
    (233/250:ℝ)<Real.sin x ∧ 0≤Real.cos x ∧ Real.cos x<363/1000 := by
  have hq := FrameLowPair.quadrant ⟨by linarith [hx.1],hx.2⟩
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(6/5:ℝ)) hx.2 hx.1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤6/5)
    (by linarith [hx.2,Real.pi_pos]) hx.1
  exact ⟨by linarith [trig_six_fifths.1],hq.2.2.1,by linarith [trig_six_fifths.2.2.2]⟩

theorem G1ddd_negative {x : ℝ} (hx : x∈Icc (6/5:ℝ) (Real.pi/2)) : G1ddd x<0 := by
  have ht := first_trig hx
  have hd : 0<dh ∧ dh<7/10 := by dsimp [dh]; constructor <;> linarith [a2_bounds.1,a2_bounds.2]
  have hc2 := pow_le_pow_left₀ ht.2.1 ht.2.2.le 2
  have hdc := mul_le_mul hd.2.le ht.2.2.le ht.2.1 (by norm_num : (0:ℝ)≤7/10)
  have hprod := mul_le_mul hdc (show 5+(Real.cos x)^2≤5+(363/1000:ℝ)^2 by linarith)
    (by positivity : 0≤5+(Real.cos x)^2) (by norm_num : (0:ℝ)≤(7/10)*(363/1000))
  have hnum : dh*Real.cos x*(5+(Real.cos x)^2)-2*k*(1+2*(Real.cos x)^2)<0 := by
    dsimp [k]
    nlinarith [sq_nonneg (Real.cos x)]
  have hquot := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num [g] : 0<g) hnum)
    (pow_pos (by linarith [ht.1] : 0<Real.sin x) 4)
  dsimp [G1ddd]
  linarith [ht.1,ht.2.2]

theorem G1d_concave : ConcaveOn ℝ (Icc (6/5:ℝ) (Real.pi/2)) G1d := by
  apply concave_of_deriv2
    (fun x hx => G1d_deriv (by linarith [(first_trig hx).1]))
    (fun x hx => G1dd_deriv (by linarith [(first_trig hx).1]))
    (fun x hx => (G1ddd_negative hx).le)

theorem G1_start : (451/500:ℝ)<G1 (6/5) ∧ 0<G1d (6/5) := by
  have ht := trig_six_fifths
  have hdL : (59962803/50000000:ℝ)-1/2≤dh := by dsimp [dh]; linarith [a2_bounds.1]
  have hdU : dh≤(599628031/500000000:ℝ)-1/2 := by dsimp [dh]; linarith [a2_bounds.2]
  have hn : (13/12)*(7247/20000)-((599628031/500000000)-1/2)≤k*Real.cos (6/5:ℝ)-dh := by
    dsimp [k]; linarith [ht.2.2.1]
  have hm : ((59962803/50000000)-1/2)*(7247/20000)-13/12≤dh*Real.cos (6/5:ℝ)-k := by
    have hh := mul_le_mul hdL ht.2.2.1.le
      (by norm_num : (0:ℝ)≤7247/20000) (by linarith : 0≤dh)
    dsimp [k]
    linarith
  have hquot := negative_div_lower hn (by norm_num)
    (by norm_num : (0:ℝ)<93203/100000) ht.1.le
  have hs2 := pow_le_pow_left₀ (show (0:ℝ)≤93203/100000 by norm_num) ht.1.le 2
  have hdquot := negative_div_lower hm (by norm_num)
    (by norm_num : (0:ℝ)<(93203/100000)^2) hs2
  have hq1 : (-329078/1000000:ℝ)≤(k*Real.cos (6/5:ℝ)-dh)/Real.sin (6/5:ℝ) :=
    le_trans (by norm_num) hquot
  have hq2 : (-95543/100000:ℝ)≤(dh*Real.cos (6/5:ℝ)-k)/Real.sin (6/5:ℝ)^2 :=
    le_trans (by norm_num) hdquot
  have hqg := mul_le_mul_of_nonneg_left hq1 (show 0≤g by norm_num [g])
  have hdg := mul_le_mul_of_nonneg_left hq2 (show 0≤g by norm_num [g])
  have hg : g=269343/250000 := rfl
  dsimp only [G1,G1d]
  simp only [mul_div_assoc]
  constructor <;> linarith [M_endpoints.2.2.2,ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]

theorem G1_quarter : G1 (Real.pi/2)=quarterValue := by
  simp [G1,quarterValue,dh,k]
  ring

theorem G1_lower {x : ℝ} (hx : x∈Icc (6/5:ℝ) (Real.pi/2)) :
    (4503/5000:ℝ)<G1 x := by
  have hh := endpoint_minimum_of_concave_derivative hx
    (fun x hx => G1_deriv (by linarith [(first_trig hx).1])) G1d_concave G1_start.2.le
  have hL : (4503/5000:ℝ)<G1 (6/5) := by linarith [G1_start.1]
  have hU : (4503/5000:ℝ)<G1 (Real.pi/2) := by rw [G1_quarter]; exact quarter_lower
  exact (lt_min hL hU).trans_le hh

theorem G2d_positive {x : ℝ} (hx : x∈Icc (Real.pi/2) (97/50:ℝ)) : 0<G2d x := by
  have hs := interval_sine ⟨by linarith [hx.1,FrameLowPair.pi_lower],hx.2⟩
  have hq := second_signs ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx.1,Real.pi_pos] : 0≤x)
    (by linarith [FrameLowPair.pi_lower] : (97/50:ℝ)≤Real.pi) hx.2
  have hcL : -(181/500:ℝ)≤Real.cos x := by linarith [trig_primary_cut.2]
  have hd : 0≤dh ∧ dh≤7/10 := by
    dsimp [dh]; constructor <;> linarith [a2_bounds.1,a2_bounds.2]
  have hdc := mul_le_mul_of_nonneg_left hcL hd.1
  have hn : -(7/10)*(181/500)-1/12≤dh*Real.cos x-1/12 := by nlinarith
  have hs2 := pow_le_pow_left₀ (show (0:ℝ)≤233/250 by norm_num) hs.le 2
  have hquot := negative_div_lower hn (by norm_num : -(7/10:ℝ)*(181/500)-1/12≤0)
    (by norm_num : (0:ℝ)<(233/250)^2) hs2
  have hscaled := mul_le_mul_of_nonneg_left hquot (show 0≤g by norm_num [g])
  have hnum : 0<(91/100:ℝ)+g*((-(7/10)*(181/500)-1/12)/(233/250)^2) := by norm_num [g]
  dsimp only [G2d]
  rw [mul_div_assoc]
  linarith [Real.sin_le_one x,hq.2]

theorem G2_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (97/50:ℝ)) :
    (4503/5000:ℝ)<G2 x := by
  have hm : MonotoneOn G2 (Icc (Real.pi/2) (97/50:ℝ)) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      have hsx := interval_sine
        (show x∈Icc (6/5:ℝ) (97/50) from ⟨by linarith [hx.1,FrameLowPair.pi_lower],hx.2⟩)
      exact (G2_deriv (by linarith)).continuousAt.continuousWithinAt
    · intro x hx
      have hsx := interval_sine
        (show x∈Icc (6/5:ℝ) (97/50) from ⟨by linarith [hx.1,FrameLowPair.pi_lower],hx.2.le⟩)
      exact G2_deriv (by linarith)
    · exact fun x hx => (G2d_positive (Ioo_subset_Icc_self hx)).le
  have he : G2 (Real.pi/2)=quarterValue := by
    simp [G2,quarterValue,dh]
    ring
  have hh := hm ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1
  rw [he] at hh
  exact quarter_lower.trans_le hh

theorem G_lower {x : ℝ} (hx : x∈Icc (6/5:ℝ) (97/50)) :
    (4503/5000:ℝ)<G x := by
  have hs : Real.sin x≠0 := by linarith [interval_sine hx]
  by_cases hxQ : x≤Real.pi/2
  · have he : G x=G1 x := by
      dsimp [G,G1,dh,k,ac]
      rw [(first_width ⟨by linarith [hx.1],hxQ⟩).1,
        (first_width ⟨by linarith [hx.1],hxQ⟩).2]
      field_simp [hs]
      ring
    rw [he]
    exact G1_lower ⟨hx.1,hxQ⟩
  · have he : G x=G2 x := by
      dsimp [G,G2,dh,ac]
      have hx' : x∈Icc (Real.pi/2) Real.pi :=
        ⟨(lt_of_not_ge hxQ).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩
      rw [(second_width hx').1,(second_width hx').2]
      field_simp [hs]
      ring
    rw [he]
    exact G2_lower ⟨(lt_of_not_ge hxQ).le,hx.2⟩

end SquaresInCircles.Eight.FrameCoreMidPrimaryContinuation
end
end
end

section
/-!
## Core/low endpoint supports on both physical quadrants

The axial negative-target support has an elementary initial bound and
one strong-convexity estimate.  The positive cut support uses one tangent
parabola on its whole interval.  Their actual second-quadrant continuations
are increasing, including all angle endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreLowEndpoint
open FramePair FrameCircleArc FrameLowArc FrameCoreArc FramePairCalculus
open FrameMidArc (g)
open FrameCoreMidScalars (ap cp trigAffine trigAffine_deriv trigAffine_monotone)

def axialB : ℝ := g*a0-cp
def cutB : ℝ := g*a1-cp
def axial (x : ℝ) : ℝ := x+ap+cp*Real.cos x-axialB*Real.sin x
def axialD (x : ℝ) : ℝ := 1-cp*Real.sin x-axialB*Real.cos x
def axialDD (x : ℝ) : ℝ := -cp*Real.cos x+axialB*Real.sin x
def negativeCut (x : ℝ) : ℝ :=
  x+ap+L1+(cp-g*b1)*Real.cos x-cutB*Real.sin x
def positiveCut (x : ℝ) : ℝ :=
  x+ap-L1+(cp+g*b1)*Real.cos x-cutB*Real.sin x
def axialSecond (x : ℝ) : ℝ := x+ap-cp*Real.cos x-axialB*Real.sin x
def negativeCutSecond (x : ℝ) : ℝ :=
  x+ap+L1+(-cp-g*b1)*Real.cos x-cutB*Real.sin x
def positiveCutSecond (x : ℝ) : ℝ :=
  x+ap-L1+(-cp+g*b1)*Real.cos x-cutB*Real.sin x

theorem coefficient_bounds :
    (107/100:ℝ)<axialB ∧ axialB<(269/250:ℝ) ∧
      0<cp-g*b1 ∧ cp-g*b1<1/10 ∧
        (19/20:ℝ)<cutB ∧ cutB<119/125 ∧ -cp+g*b1<0 := by
  have h0 := a0_bounds
  have h1 := a1_bounds
  have hb := b1_bounds
  dsimp [axialB,cutB,cp,g]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem axial_deriv (x : ℝ) : HasDerivAt axial (axialD x) x := by
  have h := ((((hasDerivAt_id' x).add_const ap).fun_add
    ((Real.hasDerivAt_cos x).const_mul cp)).fun_sub
    ((Real.hasDerivAt_sin x).const_mul axialB))
  have e : axialD x=1+cp*-Real.sin x-axialB*Real.cos x := by dsimp [axialD]; ring
  rw [e]
  exact h

theorem axialD_deriv (x : ℝ) : HasDerivAt axialD (axialDD x) x := by
  have h := (((Real.hasDerivAt_sin x).const_mul cp).const_sub 1).fun_sub
    ((Real.hasDerivAt_cos x).const_mul axialB)
  have e : axialDD x=-(cp*Real.cos x)-axialB*-Real.sin x := by dsimp [axialDD]; ring
  rw [e]
  exact h

theorem axial_initial {x : ℝ} (hx : x∈Icc (0:ℝ) (1/2)) : (91/100:ℝ)<axial x := by
  have hs := Real.sin_le hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsin := mul_le_mul_of_nonneg_left hs (by linarith [coefficient_bounds.1] : 0≤axialB)
  have hB := mul_le_mul_of_nonneg_right coefficient_bounds.2.1.le hx.1
  have hcos := mul_le_mul_of_nonneg_left hc (show (0:ℝ)≤cp by norm_num [cp,g])
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  dsimp [axial,ap,cp,g] at *
  nlinarith

theorem axial_curvature {x : ℝ} (hx : x∈Icc (1/2:ℝ) (Real.pi/2)) :
    (1/20:ℝ)<axialDD x := by
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(1/2:ℝ)) hx.2 hx.1
  have hs0 := Real.sin_ge_sub_cube (show (0:ℝ)≤1/2 by norm_num)
  norm_num at hs0
  have hsin : (23/48:ℝ)≤Real.sin x := by linarith
  have hB := mul_le_mul_of_nonneg_right coefficient_bounds.1.le
    (show 0≤Real.sin x by linarith)
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one x)
    (show (0:ℝ)≤cp by norm_num [cp,g])
  dsimp [axialDD,cp,g] at hcos ⊢
  linarith

theorem unit_trig :
    (4207/5000:ℝ)<Real.sin (1:ℝ) ∧ Real.sin (1:ℝ)<1683/2000 ∧
      (5403/10000:ℝ)<Real.cos (1:ℝ) ∧ Real.cos (1:ℝ)<1351/2500 := by
  have hsL := sin_lower_seven (show (0:ℝ)≤1 by norm_num)
  have hsU := Arithmetic.sin_le_sin9 (show (0:ℝ)≤1 by norm_num)
  have hcL := Arithmetic.cos10_le_cos (show (0:ℝ)≤1 by norm_num)
  have hcU := Arithmetic.cos_le_cos8 (show (0:ℝ)≤1 by norm_num)
  norm_num [Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem axial_contact : (24/25:ℝ)<axial 1 ∧ |axialD 1|<(1/20:ℝ) := by
  have ht := unit_trig
  have hb := coefficient_bounds
  have hsin := mul_le_mul_of_nonneg_right hb.2.1.le
    (show 0≤Real.sin (1:ℝ) by linarith [ht.1])
  have hcL := mul_le_mul_of_nonneg_right hb.1.le
    (show 0≤Real.cos (1:ℝ) by linarith [ht.2.2.1])
  have hcU := mul_le_mul_of_nonneg_right hb.2.1.le
    (show 0≤Real.cos (1:ℝ) by linarith [ht.2.2.1])
  dsimp [axial,axialD,ap,cp,g]
  refine ⟨by nlinarith,abs_lt.mpr ⟨by nlinarith,by nlinarith⟩⟩

theorem axial_lower {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) : (91/100:ℝ)<axial x := by
  by_cases hsmall : x≤1/2
  · exact axial_initial ⟨hx.1,hsmall⟩
  · have hx' : x∈Icc (1/2:ℝ) (Real.pi/2) := ⟨(lt_of_not_ge hsmall).le,hx.2⟩
    have ht : (1:ℝ)∈Icc (1/2:ℝ) (Real.pi/2) :=
      ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩
    have hd2 : (axialD 1)^2<(1/20:ℝ)^2 := by
      obtain ⟨hl,hu⟩ := abs_lt.mp axial_contact.2
      nlinarith
    have hh := positive_of_curvature (f := fun z => axial z-91/100)
      (d := axialD) (dd := axialDD) (κ := (1/20:ℝ)) (by norm_num) hx' ht
      (fun z _ => (axial_deriv z).sub_const (91/100))
      (fun z _ => axialD_deriv z) (fun z hz => (axial_curvature hz).le)
      (by nlinarith [axial_contact.1])
    linarith

theorem negativeCut_lower {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    (91/100:ℝ)<negativeCut x := by
  have hb := coefficient_bounds
  have hamp : (cp-g*b1)^2+(-cutB)^2<(1:ℝ)^2 := by
    nlinarith [sq_nonneg (1/10-(cp-g*b1)),sq_nonneg (119/125-cutB)]
  have hm := trigAffine_monotone (k := ap+L1) (l := (0:ℝ)) (u := Real.pi/2)
    (a := cp-g*b1) (b := -cutB) (by norm_num : (0:ℝ)<1) hamp
  have hh := hm ⟨le_rfl,by positivity⟩ hx hx.1
  have he : (103/100:ℝ)<negativeCut 0 := by
    dsimp [negativeCut,ap,cp,g]
    simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,zero_add]
    linarith [L1_bounds.1,b1_bounds.2]
  have hid (z : ℝ) : trigAffine 1 (ap+L1) (cp-g*b1) (-cutB) z=negativeCut z := by
    dsimp [trigAffine,negativeCut]
    ring
  rw [hid,hid] at hh
  linarith

def D : ℝ := cp+g*(12987/10000)/4
def B : ℝ := g*(3247/2500)-cp
def cutModel (x : ℝ) : ℝ := x+ap-307/1000+D*Real.cos x-B*Real.sin x
def cutModelD (x : ℝ) : ℝ := 1-D*Real.sin x-B*Real.cos x
def cutModelDD (x : ℝ) : ℝ := -D*Real.cos x+B*Real.sin x

theorem model_coefficients : 0<D ∧ D<4/5 ∧ (19/20:ℝ)<B ∧ B<1 := by
  norm_num [D,B,cp,g]

theorem cutModel_deriv (x : ℝ) : HasDerivAt cutModel (cutModelD x) x := by
  have h := (((((hasDerivAt_id' x).add_const ap).sub_const (307/1000)).fun_add
    ((Real.hasDerivAt_cos x).const_mul D)).fun_sub
    ((Real.hasDerivAt_sin x).const_mul B))
  have e : cutModelD x=1+D*-Real.sin x-B*Real.cos x := by dsimp [cutModelD]; ring
  rw [e]
  exact h

theorem cutModelD_deriv (x : ℝ) : HasDerivAt cutModelD (cutModelDD x) x := by
  have h := (((Real.hasDerivAt_sin x).const_mul D).const_sub 1).fun_sub
    ((Real.hasDerivAt_cos x).const_mul B)
  have e : cutModelDD x=-(D*Real.cos x)-B*-Real.sin x := by dsimp [cutModelDD]; ring
  rw [e]
  exact h

theorem cutModel_curvature {x : ℝ} (hx : x∈Icc (6/5:ℝ) (Real.pi/2)) :
    (1/2:ℝ)<cutModelDD x := by
  have ht := FrameCoreMidPrimaryContinuation.first_trig hx
  have hcos := mul_le_mul model_coefficients.2.1.le ht.2.2.le ht.2.1 (by norm_num)
  have hsin := mul_le_mul model_coefficients.2.2.1.le ht.1.le (by norm_num)
    (by linarith [model_coefficients.2.2.1] : 0≤B)
  dsimp [cutModelDD]
  nlinarith

theorem cut_contact_trig :
    (97193/100000:ℝ)<Real.sin (4/3:ℝ) ∧ Real.sin (4/3:ℝ)<19439/20000 ∧
      (23523/100000:ℝ)<Real.cos (4/3:ℝ) ∧ Real.cos (4/3:ℝ)<941/4000 := by
  have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤4/3 by norm_num)
  have hsU := Arithmetic.sin_le_sin9 (show (0:ℝ)≤4/3 by norm_num)
  have hcL := Arithmetic.cos10_le_cos (show (0:ℝ)≤4/3 by norm_num)
  have hcU := Arithmetic.cos_le_cos8 (show (0:ℝ)≤4/3 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,
    Arithmetic.cos8] at *
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem cut_contact : (459/500:ℝ)<cutModel (4/3:ℝ) ∧
    |cutModelD (4/3:ℝ)|<(1/1000:ℝ) := by
  have ht := cut_contact_trig
  dsimp [cutModel,cutModelD,D,B,ap,cp,g]
  refine ⟨by linarith,abs_lt.mpr ⟨by linarith,by linarith⟩⟩

theorem cutModel_lower {x : ℝ} (hx : x∈Icc (6/5:ℝ) (Real.pi/2)) :
    (91/100:ℝ)<cutModel x := by
  have ht : (4/3:ℝ)∈Icc (6/5:ℝ) (Real.pi/2) :=
    ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩
  have hd2 : (cutModelD (4/3:ℝ))^2<(1/1000:ℝ)^2 := by
    obtain ⟨hl,hu⟩ := abs_lt.mp cut_contact.2
    nlinarith
  have hh := positive_of_curvature (f := fun z => cutModel z-91/100)
    (d := cutModelD) (dd := cutModelDD) (κ := (1/2:ℝ)) (by norm_num) hx ht
    (fun z _ => (cutModel_deriv z).sub_const (91/100))
    (fun z _ => cutModelD_deriv z) (fun z hz => (cutModel_curvature hz).le)
    (by nlinarith [cut_contact.1])
  linarith

theorem positiveCut_lower {x : ℝ} (hx : x∈Icc (6/5:ℝ) (Real.pi/2)) :
    (91/100:ℝ)<positiveCut x := by
  have ht := FrameLowPair.quadrant
    (show x∈Icc 0 (Real.pi/2) from ⟨by linarith [hx.1],hx.2⟩)
  have hD : D≤cp+g*b1 := by dsimp [D,b1,g]; linarith [a1_bounds.1]
  have hB : cutB≤B := by dsimp [cutB,B,g]; linarith [a1_bounds.2]
  have hcos := mul_le_mul_of_nonneg_right hD ht.2.2.1
  have hsin := mul_le_mul_of_nonneg_right hB ht.1
  have hh := cutModel_lower hx
  dsimp [positiveCut,cutModel] at *
  linarith [L1_bounds.2]

theorem second_monotone {k a b : ℝ} (ha : a≤0) (hb : b≤0) :
    MonotoneOn (trigAffine 1 k a b) (Icc (Real.pi/2) Real.pi) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (trigAffine_deriv 1 k a b x).continuousAt.continuousWithinAt
  · exact fun x _ => trigAffine_deriv 1 k a b x
  · intro x hx
    have ht := second_signs (Ioo_subset_Icc_self hx)
    have h1 := mul_nonpos_of_nonpos_of_nonneg ha ht.1
    have h2 := mul_nonneg_of_nonpos_of_nonpos hb ht.2
    linarith

theorem axialSecond_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) Real.pi) :
    (91/100:ℝ)<axialSecond x := by
  have hm := second_monotone (k := ap) (a := -cp) (b := -axialB)
    (by norm_num [cp,g]) (by linarith [coefficient_bounds.1])
  have hh := hm ⟨le_rfl,by linarith [Real.pi_pos]⟩ hx hx.1
  have he := axial_lower
    (show Real.pi/2∈Icc (0:ℝ) (Real.pi/2) from ⟨by positivity,le_rfl⟩)
  dsimp [trigAffine,axial,axialSecond] at *
  simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,mul_zero] at *
  linarith

theorem negativeCutSecond_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) Real.pi) :
    (91/100:ℝ)<negativeCutSecond x := by
  have hm := second_monotone (k := ap+L1) (a := -cp-g*b1) (b := -cutB)
    (by dsimp [cp,g]; linarith [b1_bounds.1])
    (by linarith [coefficient_bounds.2.2.2.2.1])
  have hh := hm ⟨le_rfl,by linarith [Real.pi_pos]⟩ hx hx.1
  have he := negativeCut_lower
    (show Real.pi/2∈Icc (0:ℝ) (Real.pi/2) from ⟨by positivity,le_rfl⟩)
  dsimp [trigAffine,negativeCut,negativeCutSecond] at *
  simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,mul_zero] at *
  linarith

theorem positiveCutSecond_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) Real.pi) :
    (91/100:ℝ)<positiveCutSecond x := by
  have hm := second_monotone (k := ap-L1) (a := -cp+g*b1) (b := -cutB)
    coefficient_bounds.2.2.2.2.2.2.le
    (by linarith [coefficient_bounds.2.2.2.2.1])
  have hh := hm ⟨le_rfl,by linarith [Real.pi_pos]⟩ hx hx.1
  have he := positiveCut_lower
    (show Real.pi/2∈Icc (6/5:ℝ) (Real.pi/2) from
      ⟨by linarith [FrameLowPair.pi_lower],le_rfl⟩)
  dsimp [trigAffine,positiveCut,positiveCutSecond] at *
  simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,mul_zero] at *
  linarith

end SquaresInCircles.Eight.FrameCoreLowEndpoint
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreMidContact
open FramePair FrameCircleArc FrameMidArc

def w (t : ℝ) : ℝ := Real.sqrt (1+t^2)
def wd (t : ℝ) : ℝ := t/w t
def N (z : ℝ) : ℝ := Real.sqrt ((p+g*z)^2+q^2)
def Nd (z : ℝ) : ℝ := g*(p+g*z)/N z
def Ndd (z : ℝ) : ℝ := g^2*q^2/(N z)^3

theorem w_pos (t : ℝ) : 0<w t := Real.sqrt_pos.mpr (by positivity)
theorem w_sq (t : ℝ) : (w t)^2=1+t^2 := Real.sq_sqrt (by positivity)
theorem w_power (t : ℝ) (n : ℕ) : (w t)^(n+2)=(w t)^n*(1+t^2) := by
  rw [pow_add,w_sq]

theorem w_deriv (t : ℝ) : HasDerivAt w (wd t) t := by
  have hh := ((hasDerivAt_const t (1:ℝ)).fun_add ((hasDerivAt_id' t).fun_pow 2)).sqrt
    (show 1+t^2≠0 by positivity)
  show HasDerivAt (fun y => Real.sqrt (1+y^2)) _ t
  convert hh using 1
  have hn : Real.sqrt (1+t^2)≠0 := (w_pos t).ne'
  dsimp [wd,w]
  field_simp
  ring

theorem N_pos (z : ℝ) : 0<N z := by
  apply Real.sqrt_pos.mpr
  have hq : 0<q^2 := by norm_num [q]
  linarith [sq_nonneg (p+g*z)]

theorem N_sq (z : ℝ) : (N z)^2=(p+g*z)^2+q^2 := Real.sq_sqrt (by positivity)

theorem N_deriv (z : ℝ) : HasDerivAt N (Nd z) z := by
  have hpos : (p+g*z)^2+q^2≠0 := by
    have hq : 0<q^2 := by norm_num [q]
    nlinarith [sq_nonneg (p+g*z)]
  have hh := (((((hasDerivAt_id' z).const_mul g).const_add p).fun_pow 2).add_const
    (q^2)).sqrt hpos
  show HasDerivAt (fun y => Real.sqrt ((p+g*y)^2+q^2)) _ z
  convert hh using 1
  have hn : Real.sqrt ((p+g*z)^2+q^2)≠0 := (N_pos z).ne'
  dsimp [Nd,N]
  field_simp

theorem Nd_deriv (z : ℝ) : HasDerivAt Nd (Ndd z) z := by
  have hn := (N_pos z).ne'
  have hh := ((((hasDerivAt_id' z).const_mul g).const_add p).const_mul g).fun_div
    (N_deriv z) hn
  convert hh using 1
  · rfl
  · have hN2 := N_sq z
    dsimp [Nd,Ndd]
    field_simp
    rw [hN2]
    ring

def x0 : ℝ := 27/25
def s0 : ℝ := Real.sin x0
def c0 : ℝ := Real.cos x0
def t0 : ℝ := c0/s0
def w0 : ℝ := 1/s0
def N0 : ℝ := N w0
def a : ℝ := g-R*Nd w0+(R/10)*w0

def sLo : ℝ := 440978903/500000000
def sHi : ℝ := 881957807/1000000000
def cLo : ℝ := 117832091/250000000
def cHi : ℝ := 94265673/200000000
def rLo : ℝ := 1978787507/1000000000
def rHi : ℝ := 494696877/250000000
def nLo : ℝ := 784517747/250000000
def nHi : ℝ := 3138070991/1000000000

theorem contact_trig : sLo<s0 ∧ s0<sHi ∧ cLo<c0 ∧ c0<cHi := by
  have hsL := HighOrderTaylor.S15_le_sin (show 0≤x0 by norm_num [x0])
  have hsU := HighOrderTaylor.sin_le_S17 (show 0≤x0 by norm_num [x0])
  have hcL := HighOrderTaylor.C18_le_cos (show 0≤x0 by norm_num [x0])
  have hcU := HighOrderTaylor.cos_le_C16 (show 0≤x0 by norm_num [x0])
  norm_num [x0,HighOrderTaylor.S17,HighOrderTaylor.S15,HighOrderTaylor.S13,
    HighOrderTaylor.S11,HighOrderTaylor.C18,HighOrderTaylor.C16,HighOrderTaylor.C14,
    HighOrderTaylor.C12,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,
    Arithmetic.cos8] at hsL hsU hcL hcU
  dsimp [s0,c0,x0,sLo,sHi,cLo,cHi]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem contact_signs : 0<s0 ∧ 0<c0 ∧ 0<w0 ∧ 0<N0 := by
  have hs : 0<s0 := by linarith [contact_trig.1,show (0:ℝ)<sLo by norm_num [sLo]]
  have hc : 0<c0 := by linarith [contact_trig.2.2.1,show (0:ℝ)<cLo by norm_num [cLo]]
  exact ⟨hs,hc,one_div_pos.mpr hs,N_pos w0⟩

theorem contact_radius : rLo<R ∧ R<rHi := by
  have he := R_sq
  have hn := R_pos
  dsimp [rLo,rHi,Q0] at *
  constructor <;> nlinarith

theorem contact_w_bounds : 1/sHi<w0 ∧ w0<1/sLo := by
  have hs := contact_signs.1
  dsimp [w0]
  constructor
  · apply (div_lt_div_iff₀ (by norm_num [sHi] : 0<sHi) hs).2
    nlinarith [contact_trig.2.1]
  · apply (div_lt_div_iff₀ hs (by norm_num [sLo] : 0<sLo)).2
    nlinarith [contact_trig.1]

theorem contact_norm : nLo<N0 ∧ N0<nHi := by
  have hw := contact_w_bounds
  have he := N_sq w0
  change N0^2=(p+g*w0)^2+q^2 at he
  have hx0 : 0<p+g*w0 := by dsimp [p,g]; linarith [contact_signs.2.2.1]
  have hxL : p+g/sHi<p+g*w0 := by
    have hm := mul_lt_mul_of_pos_left hw.1 (show 0<g by norm_num [g])
    rw [mul_one_div] at hm
    linarith
  have hxU : p+g*w0<p+g/sLo := by
    have hm := mul_lt_mul_of_pos_left hw.2 (show 0<g by norm_num [g])
    rw [mul_one_div] at hm
    linarith
  have hsL := pow_le_pow_left₀ (show 0≤p+g/sHi by norm_num [p,g,sHi]) hxL.le 2
  have hsU := pow_le_pow_left₀ hx0.le hxU.le 2
  have hnumL : nLo^2<(p+g/sHi)^2+q^2 := by norm_num [nLo,p,g,sHi,q]
  have hnumU : (p+g/sLo)^2+q^2<nHi^2 := by norm_num [nHi,p,g,sLo,q]
  have hn := contact_signs.2.2.2
  constructor <;> dsimp [nLo,nHi] at * <;> nlinarith

def zLo : ℝ := rLo*(p+g/sHi)/nHi
def zHi : ℝ := rHi*(p+g/sLo)/nLo
def Z0 : ℝ := R*(p+g*w0)/N0

theorem contact_Z : zLo<Z0 ∧ Z0<zHi := by
  have hr := contact_radius
  have hn := contact_norm
  have hw := contact_w_bounds
  have hR := R_pos
  have hN := contact_signs.2.2.2
  have hx : 0<p+g*w0 := by dsimp [p,g]; linarith [contact_signs.2.2.1]
  have hxL : p+g/sHi≤p+g*w0 := by
    have hm := mul_lt_mul_of_pos_left hw.1 (show 0<g by norm_num [g])
    rw [mul_one_div] at hm
    linarith
  have hxU : p+g*w0≤p+g/sLo := by
    have hm := mul_lt_mul_of_pos_left hw.2 (show 0<g by norm_num [g])
    rw [mul_one_div] at hm
    linarith
  have hpL := mul_le_mul hxL hr.1.le
    (show 0≤rLo by norm_num [rLo]) hx.le
  have hpU := mul_le_mul hxU hr.2.le hR.le
    (show 0≤p+g/sLo by norm_num [p,g,sLo])
  constructor
  · apply (div_lt_div_iff₀ (by norm_num [nHi] : 0<nHi) hN).2
    have hmul := mul_lt_mul_of_pos_left hn.2
      (show 0<rLo*(p+g/sHi) by norm_num [rLo,p,g,sHi])
    have hscaled := mul_le_mul_of_nonneg_left hpL (show 0≤nHi by norm_num [nHi])
    nlinarith
  · apply (div_lt_div_iff₀ hN (by norm_num [nLo] : 0<nLo)).2
    have hmul := mul_lt_mul_of_pos_left hn.1
      (show 0<rHi*(p+g/sLo) by norm_num [rHi,p,g,sLo])
    have hscaled := mul_le_mul_of_nonneg_left hpU (show 0≤nLo by norm_num [nLo])
    nlinarith

theorem a_lower : -(541/1000:ℝ)<a := by
  have hz := contact_Z.2
  have hw := contact_w_bounds.1
  have hr := contact_radius.1
  have hmul := mul_le_mul hw.le hr.le
    (show 0≤rLo by norm_num [rLo]) contact_signs.2.2.1.le
  have hscaled := mul_lt_mul_of_pos_left hz (show 0<g by norm_num [g])
  have hnum : -(541/1000:ℝ)<g-g*zHi+rLo/(10*sHi) := by
    norm_num [g,zHi,rLo,rHi,p,sLo,sHi,nLo]
  have hid : a=g-g*Z0+(R/10)*w0 := by
    dsimp [a,Nd,Z0,N0]
    ring
  have hRw : rLo/(10*sHi)≤(R/10)*w0 := by
    have h1 : rLo/(10*sHi)=(1/sHi*rLo)/10 := by ring
    have h2 : (R/10)*w0=(w0*R)/10 := by ring
    rw [h1,h2]
    linarith
  rw [hid]
  linarith

def scalar (x : ℝ) : ℝ :=
  x-(9/100)*(Real.sin x+Real.cos x-1)-cM+(p+q+g)/2+
    g/Real.sin x+(13*g/12)*(Real.cos x/Real.sin x)-R*N (1/Real.sin x)

def scalarD (x : ℝ) : ℝ :=
  1+(9/100)*(Real.sin x-Real.cos x)+
    g/(Real.sin x)^2*
      (Real.cos x*(R*(p+g/Real.sin x)/N (1/Real.sin x)-1)-13/12)

theorem contact_value : (4503/5000:ℝ)<scalar x0 := by
  have ht := contact_trig
  have hr := contact_radius
  have hn := contact_norm
  have hs := contact_signs.1
  have hc := contact_signs.2.1
  have hR := R_pos
  have hN := contact_signs.2.2.2
  have hw := contact_w_bounds.1
  have hratio : cLo/sHi<c0/s0 := by
    apply (div_lt_div_iff₀ (by norm_num [sHi] : 0<sHi) hs).2
    exact mul_lt_mul ht.2.2.1 ht.2.1.le hs hc.le
  have hroot := mul_le_mul hn.2.le hr.2.le hR.le
    (show 0≤nHi by norm_num [nHi])
  have hwg := mul_lt_mul_of_pos_left hw (show 0<g by norm_num [g])
  have hrc := mul_lt_mul_of_pos_left hratio (show 0<13*g/12 by norm_num [g])
  have hnum : (4503/5000:ℝ)<x0-(9/100)*(sHi+cHi-1)-cM+(p+q+g)/2+
      g/sHi+(13*g/12)*(cLo/sHi)-rHi*nHi := by
    norm_num [x0,sHi,cHi,cLo,cM,p,q,g,rHi,nHi]
  change (4503/5000:ℝ)<x0-(9/100)*(s0+c0-1)-cM+(p+q+g)/2+
    g/s0+(13*g/12)*(c0/s0)-R*N0
  dsimp [w0] at hwg
  rw [mul_one_div,mul_one_div] at hwg
  linarith [ht.2.1,ht.2.2.2]

def bracketLo : ℝ := cLo*(zLo-1)-13/12
def bracketHi : ℝ := cHi*(zHi-1)-13/12

theorem contact_bracket :
    bracketLo<c0*(Z0-1)-13/12 ∧ c0*(Z0-1)-13/12<bracketHi ∧ bracketHi<0 := by
  have hz := contact_Z
  have ht := contact_trig
  have hzL : 0<zLo-1 := by norm_num [zLo,rLo,p,g,sHi,nHi]
  have hzU : 0<zHi-1 := by norm_num [zHi,rHi,p,g,sLo,nLo]
  have hZ0 : 0<Z0-1 := by linarith [hz.1]
  have hlo := mul_lt_mul ht.2.2.1 (show zLo-1≤Z0-1 by linarith)
    hzL contact_signs.2.1.le
  have hhi := mul_lt_mul ht.2.2.2 (show Z0-1≤zHi-1 by linarith)
    hZ0 (by norm_num [cHi] : (0:ℝ)≤cHi)
  refine ⟨by dsimp [bracketLo]; linarith,by dsimp [bracketHi]; linarith,?_⟩
  norm_num [bracketHi,cHi,zHi,rHi,p,g,sLo,nLo]

theorem contact_derivative : |scalarD x0|<(3/10000:ℝ) := by
  have ht := contact_trig
  have hs := contact_signs.1
  have hb := contact_bracket
  have hsL := pow_le_pow_left₀ (show 0≤ sLo by norm_num [sLo]) ht.1.le 2
  have hsU := pow_le_pow_left₀ hs.le ht.2.1.le 2
  have hneg : c0*(Z0-1)-13/12<0 := hb.2.1.trans hb.2.2
  have hL : bracketLo/sLo^2<(c0*(Z0-1)-13/12)/s0^2 := by
    apply (div_lt_div_iff₀ (by norm_num [sLo] : (0:ℝ)<sLo^2) (sq_pos_of_pos hs)).2
    have hm := mul_le_mul_of_nonpos_left hsL (by linarith [hb.1,hneg] : bracketLo≤0)
    have hn := mul_lt_mul_of_pos_right hb.1 (by norm_num [sLo] : (0:ℝ)<sLo^2)
    nlinarith
  have hU : (c0*(Z0-1)-13/12)/s0^2<bracketHi/sHi^2 := by
    apply (div_lt_div_iff₀ (sq_pos_of_pos hs) (by norm_num [sHi] : (0:ℝ)<sHi^2)).2
    have hm := mul_le_mul_of_nonpos_left hsU hneg.le
    have hn := mul_lt_mul_of_pos_right hb.2.1 (sq_pos_of_pos hs)
    nlinarith
  have hLg := mul_lt_mul_of_pos_left hL (show 0<g by norm_num [g])
  have hUg := mul_lt_mul_of_pos_left hU (show 0<g by norm_num [g])
  have hnumL : -(3/10000:ℝ)<1+(9/100)*(sLo-cHi)+g*(bracketLo/sLo^2) := by
    norm_num [sLo,cHi,g,bracketLo,cLo,zLo,rLo,p,sHi,nHi]
  have hnumU : 1+(9/100)*(sHi-cLo)+g*(bracketHi/sHi^2)<(3/10000:ℝ) := by
    norm_num [sHi,cLo,g,bracketHi,cHi,zHi,rHi,p,sLo,nLo]
  have hid : scalarD x0=1+(9/100)*(s0-c0)+g*((c0*(Z0-1)-13/12)/s0^2) := by
    dsimp [scalarD,s0,c0,Z0,N0,w0]
    ring
  rw [hid,abs_lt]
  constructor <;> nlinarith [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]

end SquaresInCircles.Eight.FrameCoreMidContact
end
end
end
