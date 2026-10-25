module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Frames.Core.MidScalars

/-!
# Eight squares: the actual high-endpoint primary continuation for core/middle pairs

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
