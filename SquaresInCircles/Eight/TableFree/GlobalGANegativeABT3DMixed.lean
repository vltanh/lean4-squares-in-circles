module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3DGeometry

/-!
# Both mixed-sign quadrants of the actual sorted-D support

Uncompiled wider constants from Section 3 of the negative-A BT3 note.
The full-circle branch is strictly concave; the tangent-zero expression
decreases to its far endpoint.  Exact branch equality joins these bounds
to the independently proved diagonal and endpoint estimates.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.DEnvelope
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PositiveBT3
open PairNormCalculus OrdinaryCurvatureBounds

theorem mixed_reverse_lower {c t n : ℝ} (hc : c∈Icc 1 Cmax)
    (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    -slope*t+vstar n≤D c (-n) t := by
  have hphi : 1≤Real.cos n+Real.sin n := CorrelatedSameBlock.one_le_phi hn
  have hs := (transport_trig ht).2.2.1
  have hm := mul_le_mul_of_nonneg_left hphi (by linarith [hc.1] : 0≤c)
  have he : forceA c (-n) t≤forceB c (-n) t := by
    dsimp [forceA,forceB]
    rw [Real.sin_neg,Real.cos_neg]
    nlinarith [Real.cos_le_one t,hc.1]
  have hh := diagonal_residual hc (mixed_domain ht hn).2
  dsimp [D]
  rw [sortedSupport_diagonal he]
  simp only [positiveTotal,negativeTotal,positivePart,negativePart,
    max_eq_left ht.1,max_eq_left hn.1,max_eq_right (neg_nonpos.mpr ht.1),
    max_eq_right (neg_nonpos.mpr hn.1),neg_neg,zero_add,add_zero] at hh
  linarith

def mixedBase (c n t : ℝ) : ℝ :=
  c*(Real.cos t+Real.sin t-1)/2+(Real.cos n+Real.sin n-1)/2+
    (1+c)*diagonal+slope*t-vstar n

theorem mixed_base_identity {c t n : ℝ} (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    mixedBase c n t-sortedSupport (forceA c t (-n)) (forceB c t (-n))=
      D c t (-n)+slope*t-vstar n := by
  rw [D,edgeWidth_positive_formula ht,edgeWidth_negative_formula hn]
  dsimp [mixedBase]
  ring

theorem mixed_full_identity (c n t : ℝ) :
    mixedBase c n t-fullSupport (forceA c t (-n)) (forceB c t (-n))=
      c*(Real.cos t+Real.sin t-1)+Real.cos n-1+(1+c)*(diagonal+1/2)-
      R*pairNorm 1 c (t-n)+slope*t-vstar n := by
  rw [fullSupport,force_norm]
  dsimp [mixedBase,forceA,forceB]
  rw [Real.sin_neg,Real.cos_neg]
  ring

theorem uniform_norm_curvature {c s : ℝ} (hc : c∈Icc 1 Cmax)
    (hs : |s|≤frameCap) : curvature R 1 c s<(189/200)*c := by
  have hc0 : 0<c := by linarith [hc.1]
  have hc2 : c≤2*(1:ℝ) := by norm_num [Cmax] at hc ⊢; linarith [hc.2]
  have hmon := curvature_monotone (R:=R) (p:=1) (q:=c)
    (Real.sqrt_nonneg _) (by norm_num) hc0
    (abs_le.mp hs) (show frameCap∈Icc (-frameCap) frameCap by norm_num [frameCap])
    ((le_abs_self s).trans hs)
  have htan := curvature_positive_upper (R:=R) (p:=1) (q:=c)
    (Real.sqrt_nonneg _) (by norm_num) hc.1 hc2
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hconst := (curvature_constant_bounds (R:=R) (p:=1) (q:=c)
    (Real.sqrt_nonneg _) radius_sq.le (by norm_num) hc.1 hc2).2.2.2
  linarith

def mixedDerivative (c n t : ℝ) : ℝ :=
  c*(Real.cos t-Real.sin t)-R*normD1 1 c (t-n)+slope

theorem mixed_full_hasDerivAt {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    HasDerivAt (fun x => mixedBase c n x-
      fullSupport (forceA c x (-n)) (forceB c x (-n))) (mixedDerivative c n t) t := by
  simp_rw [mixed_full_identity]
  have hnorm := (pairNorm_hasDerivAt (p:=1) (q:=c) (by norm_num)
    (by linarith [hc.1]) (mixed_argument_bound ht hn)).comp t ((hasDerivAt_id t).sub_const n)
  convert (((((((Real.hasDerivAt_cos t).add (Real.hasDerivAt_sin t)).sub_const 1).const_mul c).add_const
    (Real.cos n-1+(1+c)*(diagonal+1/2))).sub (hnorm.const_mul R)).add
    ((hasDerivAt_id t).const_mul slope)).sub_const (vstar n) using 1 <;>
    dsimp [mixedDerivative] <;> ring

theorem mixed_derivative_hasDerivAt {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    HasDerivAt (mixedDerivative c n)
      (curvature R 1 c (t-n)-c*phi t) t := by
  have hnorm := (normD1_hasDerivAt (p:=1) (q:=c) (by norm_num)
    (by linarith [hc.1]) (mixed_argument_bound ht hn)).comp t ((hasDerivAt_id t).sub_const n)
  convert ((((Real.hasDerivAt_cos t).sub (Real.hasDerivAt_sin t)).const_mul c).sub
    (hnorm.const_mul R)).add_const slope using 1 <;>
    dsimp [mixedDerivative,curvature,phi] <;> ring

theorem mixed_curvature {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    curvature R 1 c (t-n)-c*phi t< -(11/200)*c := by
  have hh := uniform_norm_curvature hc (mixed_argument_bound ht hn)
  have hp := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.one_le_phi ht)
    (by linarith [hc.1] : 0≤c)
  linarith

theorem mixed_axis_hasDerivAt (c n t : ℝ) :
    HasDerivAt (fun x => mixedBase c n x-forceA c x (-n)*axial)
      (slope-c*((axial-1/2)*Real.cos t+(1/2)*Real.sin t)) t := by
  have hb := (((((Real.hasDerivAt_cos t).add (Real.hasDerivAt_sin t)).sub_const 1).const_mul c).div_const 2).add_const
    ((Real.cos n+Real.sin n-1)/2+(1+c)*diagonal-vstar n)
  have hf := ((Real.hasDerivAt_sin t).const_mul c).add_const (Real.cos (-n))
  convert (hb.add ((hasDerivAt_id t).const_mul slope)).sub (hf.mul_const axial) using 1 <;>
    dsimp [mixedBase,forceA] <;> ring

theorem mixed_axis_antitone {c n : ℝ} (hc : c∈Icc 1 Cmax) :
    AntitoneOn (fun x => mixedBase c n x-forceA c x (-n)*axial) (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro t ht
    exact (mixed_axis_hasDerivAt c n t).continuousAt.continuousWithinAt
  · intro t ht
    exact mixed_axis_hasDerivAt c n t
  · intro t ht
    have hb := axis_bracket_lower (Ioo_subset_Icc_self ht)
    have hm := mul_le_mul_of_nonneg_right hc.1 (by linarith :
      0≤(axial-1/2)*Real.cos t+(1/2)*Real.sin t)
    norm_num [slope] at ⊢
    linarith

theorem mixed_forward_lower {c t n : ℝ} (hc : c∈Icc 1 Cmax)
    (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    -slope*t+vstar n≤D c t (-n) := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hfar : 0≤mixedBase c n frameCap-
      sortedSupport (forceA c frameCap (-n)) (forceB c frameCap (-n)) := by
    rw [mixed_base_identity hh hn]
    exact (mixed_far_endpoint hc hn).le
  have hleft : 0≤mixedBase c n 0-
      sortedSupport (forceA c 0 (-n)) (forceB c 0 (-n)) := by
    rw [mixed_base_identity hz hn]
    linarith [one_angle_lower hc hn]
  have haxis (x : ℝ) (hx : x∈Icc 0 frameCap) :
      0≤mixedBase c n x-forceA c x (-n)*axial := by
    have hanti := mixed_axis_antitone (n:=n) hc hx hh hx.2
    have hpos := forward_force_positive hc (by norm_num [frameCap]) hn
    have hs := axis_support_lower hpos.1 hpos.2
    linarith
  have hbound := support_path_lower
    (base:=mixedBase c n) (f:=fun x => forceA c x (-n)) (g:=fun x => forceB c x (-n))
    (df:=mixedDerivative c n) (ddf:=fun x => curvature R 1 c (x-n)-c*phi x)
    (κ:=11/200) (by dsimp [mixedBase]; fun_prop)
    (by dsimp [forceA]; fun_prop) (by dsimp [forceB]; fun_prop) ht (by norm_num)
    (fun x hx => forward_force_positive hc hx hn)
    (fun x hx => by
      have hd := diagonal_residual hc (mixed_domain hx hn).1
      rw [edgeWidth_positive_formula hx,edgeWidth_negative_formula hn] at hd
      simp only [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left hx.1,max_eq_left hn.1,max_eq_right (neg_nonpos.mpr hx.1),
        max_eq_right (neg_nonpos.mpr hn.1),neg_neg,zero_add,add_zero] at hd
      dsimp [mixedBase]
      linarith)
    (fun x hx _ => haxis x hx) hleft hfar
    (fun x hx => mixed_full_hasDerivAt hc (Ioo_subset_Icc_self hx) hn)
    (fun x hx => mixed_derivative_hasDerivAt hc (Ioo_subset_Icc_self hx) hn)
    (fun x hx => by
      have hh := mixed_curvature hc (Ioo_subset_Icc_self hx) hn
      linarith [hc.1])
  rw [mixed_base_identity ht hn] at hbound
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.DEnvelope
