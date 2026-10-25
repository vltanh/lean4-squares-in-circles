module

public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3DEndpoints
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedPositive
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2Concentration
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2HighAffected
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3High
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedNegativeCurves
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowSeparated
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3DEnvelopeGeometry
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3DMixedEnvelope

/-!
# Eight squares: the complete original negative-flat-A / nonnegative-TD2 exclusion

The two
prescribed coefficient families cover the whole original TD interval.
All concentration endpoints are paid internally. A positive original
stress is exposed independently of the original separator witnesses.
-/

section
/-!
## The signed diagonal charge and the interpolation of the wider D endpoint

The constants are `alpha = .67`, `k* = .68` and `C* = 1.2`; the negative initial slope is below
`1.113`. The interpolation of the support (`D_weight_concave`) is used only in the forward mixed
quadrant, where both forces are strictly positive.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.DEnvelope
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3
open PairNormCalculus OrdinaryNegativeSlope

/-- The sorted support, including its tangent-zero branch, is convex along the interpolation of
the coefficient `c` between `1` and `Cmax`. -/
theorem D_weight_concave {c x n : ℝ} (hc : c∈Icc 1 Cmax)
    (hx : x∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    ((Cmax-c)/(Cmax-1))*D 1 x (-n)+((c-1)/(Cmax-1))*D Cmax x (-n)≤D c x (-n) := by
  have hp := forward_force_positive hc hx hn
  obtain ⟨a,b,ha,hb,hs,hcircle,he⟩ := sortedSupport_attained hp.1 hp.2
  have hp1 := forward_force_positive (show (1:ℝ)∈Icc 1 Cmax by norm_num [Cmax]) hx hn
  have hpC := forward_force_positive (show Cmax∈Icc 1 Cmax by norm_num [Cmax]) hx hn
  have h1 := raw_sorted_support ha hb hs hcircle.le hp1.1.le hp1.2.le
  have hC := raw_sorted_support ha hb hs hcircle.le hpC.1.le hpC.2.le
  have hden : 0<Cmax-1 := by norm_num [Cmax]
  have hα : 0≤(Cmax-c)/(Cmax-1) := div_nonneg (sub_nonneg.mpr hc.2) hden.le
  have hβ : 0≤(c-1)/(Cmax-1) := div_nonneg (sub_nonneg.mpr hc.1) hden.le
  have hh1 := mul_le_mul_of_nonneg_left h1 hα
  have hhC := mul_le_mul_of_nonneg_left hC hβ
  have hbary : (Cmax-c)/(Cmax-1)+(c-1)/(Cmax-1)=1 := by field_simp [hden.ne']; ring
  have hcoef : (Cmax-c)/(Cmax-1)+((c-1)/(Cmax-1))*Cmax=c := by
    field_simp [hden.ne']; ring
  unfold PositiveBT3.D
  rw [he]
  unfold forceA forceB at hh1 hhC ⊢
  linear_combination hh1+hhC+
    (edgeWidth (-n)-1+GlobalGA.Secondary.diagonal-(Real.cos (-n)*a+Real.sin (-n)*b))*hbary+
    (edgeWidth x-1+GlobalGA.Secondary.diagonal-(Real.sin x*a+Real.cos x*b))*hcoef

theorem mixed_far_endpoint {c n : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) :
    0<D c frameCap (-n)+slope*frameCap-vstar n := by
  have h1 := DEndpoint.endpoint .one hn
  have hC := DEndpoint.endpoint .upper hn
  simp only [DEndpoint.coefficient] at h1 hC
  push_cast at h1 hC
  have hw := D_weight_concave (x:=frameCap) hc (by norm_num [frameCap]) hn
  have hden : 0<Cmax-1 := by norm_num [Cmax]
  have hα : 0≤(Cmax-c)/(Cmax-1) := div_nonneg (sub_nonneg.mpr hc.2) hden.le
  have hβ : 0≤(c-1)/(Cmax-1) := div_nonneg (sub_nonneg.mpr hc.1) hden.le
  have hs : (Cmax-c)/(Cmax-1)+(c-1)/(Cmax-1)=1 := by field_simp [hden.ne']; ring
  have hpos : 0<((Cmax-c)/(Cmax-1))*(PositiveBT3.D 1 frameCap (-n)+slope*frameCap-vstar n)+
      ((c-1)/(Cmax-1))*(PositiveBT3.D Cmax frameCap (-n)+slope*frameCap-vstar n) := by
    by_cases hα0 : (Cmax-c)/(Cmax-1)=0
    · have hβ1 : (c-1)/(Cmax-1)=1 := by linarith
      simpa [hα0,hβ1] using hC
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_le_of_ne hα (Ne.symm hα0)) h1) (mul_nonneg hβ hC.le)
  linear_combination hpos+hw+(slope*frameCap-vstar n)*hs

theorem vstar_slope_zero : Vd R K 1 0<1113/1000 := by
  have hN := pairNorm_pos (p:=K) (q:=1) (t:=0) (by norm_num [K])
    (by norm_num) (by norm_num [frameCap])
  have hN2 := pairNorm_sq (p:=K) (q:=1) (t:=0) (by norm_num [K])
    (by norm_num) (by norm_num [frameCap])
  have hR2 : (R*K)^2=qCap*K^2 := by rw [mul_pow,radius_sq]
  have hs : (R*K)^2<((1113/1000)*pairNorm K 1 0)^2 := by
    norm_num [pairEnergy,pairProduct,K] at hN2
    norm_num [qCap,K] at hR2 ⊢
    nlinarith
  have hc : R*K<(1113/1000)*pairNorm K 1 0 := by
    nlinarith [Real.sqrt_nonneg qCap]
  have he : Vd R K 1 0=R*K/pairNorm K 1 0 := by
    simp [Vd,mixedNDerivative,normD1,pairProduct]
    ring
  rw [he]
  exact (div_lt_iff₀ hN).2 hc

theorem vstar_linear_upper {n : ℝ} (hn : n∈Icc 0 frameCap) :
    vstar n≤(1113/1000)*n := by
  have hh := V_tangent_zero (p:=K) (q:=1) (by norm_num [K])
    (by norm_num [K]) (by norm_num [K]) hn
  have hm := mul_le_mul_of_nonneg_right vstar_slope_zero.le hn.1
  exact hh.trans hm

theorem diagonal_increment_lower {w x : ℝ} (hw : w∈Icc 1 Cmax)
    (hx : |x|≤frameCap) :
    -slope*positivePart x+(1327/1000)*negativePart x≤diagonalIncrement w x := by
  by_cases hx0 : 0≤x
  · have ht : x∈Icc 0 frameCap := ⟨hx0,by simpa [abs_of_nonneg hx0] using hx⟩
    have hphi : Real.sin x+Real.cos x-1≤x := by
      linarith [Real.sin_le hx0,Real.cos_le_one x]
    have hwd : w*(GlobalGA.Secondary.diagonal-1/2)≤ slope := by
      have hm := mul_le_mul_of_nonneg_right hw.2
        (by linarith [diagonal_bounds.1] : 0≤GlobalGA.Secondary.diagonal-1/2)
      have hd := mul_lt_mul_of_pos_left
        (show GlobalGA.Secondary.diagonal-1/2<(2/5:ℝ) by linarith [diagonal_bounds.2])
        (show 0<Cmax by norm_num [Cmax])
      norm_num [slope,Cmax] at hm hd ⊢
      linarith
    have hmul := mul_le_mul_of_nonneg_left hphi
      (mul_nonneg (show (0:ℝ)≤w by linarith [hw.1])
        (show 0≤GlobalGA.Secondary.diagonal-1/2 by linarith [diagonal_bounds.1]))
    have hsl := mul_le_mul_of_nonneg_right hwd hx0
    rw [diagonalIncrement,edgeWidth_positive_formula ht]
    simp only [positivePart,negativePart,max_eq_left hx0,
      max_eq_right (neg_nonpos.mpr hx0),mul_zero,add_zero]
    linear_combination hmul+hsl
  · have hn : -x∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs x).trans hx⟩
    have hh := diagonal_negative_growth hn
    have hg : 0≤(GlobalGA.Secondary.diagonal+1/2)*Real.sin (-x)+
        (GlobalGA.Secondary.diagonal-1/2)*(1-Real.cos (-x)) := by
      nlinarith [hn.1]
    have hm := mul_le_mul_of_nonneg_right hw.1 hg
    have he : diagonalIncrement w x=
        w*((GlobalGA.Secondary.diagonal+1/2)*Real.sin (-x)+
          (GlobalGA.Secondary.diagonal-1/2)*(1-Real.cos (-x))) := by
      have hwidth := edgeWidth_negative_formula hn
      simp only [neg_neg] at hwidth
      rw [diagonalIncrement,hwidth,Real.sin_neg,Real.cos_neg]
      ring
    rw [he]
    simp only [positivePart,negativePart,max_eq_right (le_of_not_ge hx0),
      max_eq_left (show 0≤ -x by linarith),mul_zero,zero_add]
    linarith

/-- The diagonal expression is nonnegative on each whole orthant, so integrating it needs no
assumption that a path stays in one branch. -/
theorem diagonal_residual {c x y : ℝ} (hc : c∈Icc 1 Cmax)
    (hxy : SignedDomain x y) :
    0≤c*(edgeWidth x-1)+edgeWidth y-1+(1+c)*GlobalGA.Secondary.diagonal-
      diagonalSupport (forceA c x y) (forceB c x y)+
      slope*positiveTotal x y-vstar (negativeTotal x y) := by
  have hangle := signed_domain_angles hxy
  have hx := diagonal_increment_lower hc hangle.1
  have hy := diagonal_increment_lower
    (show (1:ℝ)∈Icc 1 Cmax by norm_num [Cmax]) hangle.2
  have hN : negativeTotal x y∈Icc 0 frameCap :=
    ⟨add_nonneg (negativePart_nonneg _) (negativePart_nonneg _),hxy.2⟩
  have hv := vstar_linear_upper hN
  have he : c*(edgeWidth x-1)+edgeWidth y-1+(1+c)*GlobalGA.Secondary.diagonal-
      diagonalSupport (forceA c x y) (forceB c x y)=
      diagonalIncrement c x+diagonalIncrement 1 y := by
    dsimp [diagonalSupport,forceA,forceB,diagonalIncrement]
    ring
  rw [he]
  have hN1 := hN.1
  dsimp [positiveTotal,negativeTotal] at hN1 hv ⊢
  simp only [slope] at hx hy ⊢
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.DEnvelope
end
end
end

section
/-!
## Both mixed-sign quadrants of the actual sorted-D support

The full-circle branch is strictly concave; the tangent-zero expression
decreases to its far endpoint.  Exact branch equality joins these bounds
to the independently proved diagonal and endpoint estimates.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.DEnvelope
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
  unfold PositiveBT3.D
  rw [sortedSupport_diagonal he]
  simp only [positiveTotal,negativeTotal,positivePart,negativePart,
    max_eq_left ht.1,max_eq_left hn.1,max_eq_right (neg_nonpos.mpr ht.1),
    max_eq_right (neg_nonpos.mpr hn.1),neg_neg,zero_add,add_zero] at hh
  linarith

def mixedBase (c n t : ℝ) : ℝ :=
  c*(Real.cos t+Real.sin t-1)/2+(Real.cos n+Real.sin n-1)/2+
    (1+c)*GlobalGA.Secondary.diagonal+slope*t-vstar n

theorem mixed_base_identity {c t n : ℝ} (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    mixedBase c n t-sortedSupport (forceA c t (-n)) (forceB c t (-n))=
      D c t (-n)+slope*t-vstar n := by
  rw [PositiveBT3.D,edgeWidth_positive_formula ht,edgeWidth_negative_formula hn]
  dsimp [mixedBase]
  ring

theorem mixed_full_identity (c n t : ℝ) :
    mixedBase c n t-fullSupport (forceA c t (-n)) (forceB c t (-n))=
      c*(Real.cos t+Real.sin t-1)+Real.cos n-1+(1+c)*(GlobalGA.Secondary.diagonal+1/2)-
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
  simp only [frameCap] at hmon htan hconst
  linarith

def mixedDerivative (c n t : ℝ) : ℝ :=
  c*(Real.cos t-Real.sin t)-R*normD1 1 c (t-n)+slope

theorem mixed_full_hasDerivAt {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    HasDerivAt (fun x => mixedBase c n x-
      fullSupport (forceA c x (-n)) (forceB c x (-n))) (mixedDerivative c n t) t := by
  simp_rw [mixed_full_identity]
  have hnorm : HasDerivAt (fun x => pairNorm 1 c (x-n)) (normD1 1 c (t-n)) t :=
    (pairNorm_hasDerivAt (p:=1) (q:=c) one_pos (by linarith [hc.1])
      (mixed_argument_bound ht hn)).comp_sub_const t n
  exact ((((((((((Real.hasDerivAt_cos t).add (Real.hasDerivAt_sin t)).sub_const 1).const_mul c).add_const
    (Real.cos n)).sub_const 1).add_const ((1+c)*(GlobalGA.Secondary.diagonal+1/2))).sub
    (hnorm.const_mul R)).add ((hasDerivAt_id t).const_mul slope)).sub_const (vstar n)).congr_deriv
    (by unfold mixedDerivative; ring)

theorem mixed_derivative_hasDerivAt {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    HasDerivAt (mixedDerivative c n)
      (curvature R 1 c (t-n)-c*PositiveAngularEnvelope.phi t) t := by
  have hnorm : HasDerivAt (fun x => normD1 1 c (x-n)) (normD2 1 c (t-n)) t :=
    (normD1_hasDerivAt (p:=1) (q:=c) one_pos (by linarith [hc.1])
      (mixed_argument_bound ht hn)).comp_sub_const t n
  show HasDerivAt (fun x => c*(Real.cos x-Real.sin x)-R*normD1 1 c (x-n)+slope) _ t
  exact (((((Real.hasDerivAt_cos t).sub (Real.hasDerivAt_sin t)).const_mul c).sub
    (hnorm.const_mul R)).add_const slope).congr_deriv
    (by simp only [curvature,PositiveAngularEnvelope.phi]; ring)

theorem mixed_curvature {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    curvature R 1 c (t-n)-c*PositiveAngularEnvelope.phi t< -(11/200)*c := by
  have hh := uniform_norm_curvature hc (mixed_argument_bound ht hn)
  have hp := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.one_le_phi ht)
    (by linarith [hc.1] : 0≤c)
  linarith

theorem mixed_axis_hasDerivAt (c n t : ℝ) :
    HasDerivAt (fun x => mixedBase c n x-forceA c x (-n)*axial)
      (slope-c*((axial-1/2)*Real.cos t+(1/2)*Real.sin t)) t := by
  have hb := (((((Real.hasDerivAt_cos t).add (Real.hasDerivAt_sin t)).sub_const 1).const_mul c).div_const 2).add_const
    ((Real.cos n+Real.sin n-1)/2+(1+c)*GlobalGA.Secondary.diagonal-vstar n)
  have hf := ((Real.hasDerivAt_sin t).const_mul c).add_const (Real.cos (-n))
  convert (hb.add ((hasDerivAt_id t).const_mul slope)).sub (hf.mul_const axial) using 1
  · funext x
    simp only [mixedBase,forceA,id,Pi.add_apply,Pi.sub_apply]
    ring
  · ring

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
  have hfar : 0 ≤ mixedBase c n frameCap-
      sortedSupport (forceA c frameCap (-n)) (forceB c frameCap (-n)) := by
    rw [mixed_base_identity hh hn]
    exact (mixed_far_endpoint hc hn).le
  have hleft : 0 ≤ mixedBase c n 0-
      sortedSupport (forceA c 0 (-n)) (forceB c 0 (-n)) := by
    rw [mixed_base_identity hz hn]
    linarith [one_angle_lower hc hn]
  have haxis (x : ℝ) (hx : x∈Icc 0 frameCap) :
      0 ≤ mixedBase c n x-forceA c x (-n)*axial := by
    have hanti := mixed_axis_antitone (n:=n) hc hx hh hx.2
    have hpos := forward_force_positive (t:=frameCap) hc hh hn
    have hs := axis_support_lower hpos.1 hpos.2
    simp only at hanti
    linarith
  have hbound := support_path_lower
    (base:=mixedBase c n) (f:=fun x => forceA c x (-n)) (g:=fun x => forceB c x (-n))
    (df:=mixedDerivative c n)
    (ddf:=fun x => curvature R 1 c (x-n)-c*PositiveAngularEnvelope.phi x)
    (κ:=11/200) (by show Continuous (fun x => mixedBase c n x); simp only [mixedBase]; fun_prop)
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

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.DEnvelope
end
end
end

section
/-!
## The signed two-angle sorted-D minorant

At a fixed total of equal signs the force norm is constant. The interior support is concave in the
allocation, and the tangent-zero branch is either decreasing or absent. The endpoint theorems of
the two mixed quadrants therefore cover the two quadrants of equal signs (`positive_path_lower`,
`negative_path_lower`), weak ties included, and `lower` holds on the whole signed domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.DEnvelope
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3

def equalBase (c n t : ℝ) (positive : Bool) : ℝ :=
  c*(Real.cos t+Real.sin t-1)/2+(Real.cos (n-t)+Real.sin (n-t)-1)/2+
    (1+c)*GlobalGA.Secondary.diagonal+(if positive then slope*n else -vstar n)

theorem positive_base_identity {c n t : ℝ}
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) :
    equalBase c n t true-sortedSupport (forceA c t (n-t)) (forceB c t (n-t))=
      D c t (n-t)+slope*n := by
  have h₁ : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hn.2⟩
  have h₂ : n-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1,hn.2]⟩
  rw [PositiveBT3.D,edgeWidth_positive_formula h₁,edgeWidth_positive_formula h₂]
  simp only [equalBase,↓reduceIte]
  ring

theorem negative_base_identity {c n t : ℝ}
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) :
    equalBase c n t false-sortedSupport (forceA c (-t) (-(n-t))) (forceB c (-t) (-(n-t)))=
      D c (-t) (-(n-t))-vstar n := by
  have h₁ : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hn.2⟩
  have h₂ : n-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1,hn.2]⟩
  rw [PositiveBT3.D,edgeWidth_negative_formula h₁,edgeWidth_negative_formula h₂]
  simp only [equalBase,Bool.false_eq_true,↓reduceIte]
  ring

theorem positive_full_identity (c n t : ℝ) :
    equalBase c n t true-fullSupport (forceA c t (n-t)) (forceB c t (n-t))=
      c*(Real.cos t+Real.sin t-1)+Real.cos (n-t)+Real.sin (n-t)-1+
      (1+c)*(GlobalGA.Secondary.diagonal+1/2)-R*pairNorm 1 c n+slope*n := by
  rw [fullSupport,force_norm,show t+(n-t)=n by ring]
  dsimp [equalBase,forceA,forceB]
  ring

theorem negative_full_identity (c n t : ℝ) :
    equalBase c n t false-fullSupport (forceA c (-t) (-(n-t))) (forceB c (-t) (-(n-t)))=
      c*(Real.cos t-1)+Real.cos (n-t)-1+
      (1+c)*(GlobalGA.Secondary.diagonal+1/2)-R*pairNorm 1 c (-n)-vstar n := by
  rw [fullSupport,force_norm,show -t+(-(n-t))= -n by ring]
  dsimp [equalBase,forceA,forceB]
  rw [Real.cos_neg,Real.cos_neg,Real.sin_neg,Real.sin_neg]
  ring

def positiveDerivative (c n t : ℝ) : ℝ :=
  c*(Real.cos t-Real.sin t)-(Real.cos (n-t)-Real.sin (n-t))
def negativeDerivative (c n t : ℝ) : ℝ := -c*Real.sin t+Real.sin (n-t)

theorem positive_full_hasDerivAt (c n t : ℝ) :
    HasDerivAt (fun x => equalBase c n x true-
      fullSupport (forceA c x (n-x)) (forceB c x (n-x))) (positiveDerivative c n t) t := by
  simp_rw [positive_full_identity]
  have hc := (Real.hasDerivAt_cos (n-t)).comp_const_sub n t
  have hs := (Real.hasDerivAt_sin (n-t)).comp_const_sub n t
  exact ((((((((Real.hasDerivAt_cos t).add (Real.hasDerivAt_sin t)).sub_const 1).const_mul c).add
    hc).add hs).sub_const 1).add_const ((1+c)*(GlobalGA.Secondary.diagonal+1/2)) |>.sub_const
    (R*pairNorm 1 c n) |>.add_const (slope*n)).congr_deriv (by unfold positiveDerivative; ring)

theorem positive_derivative_hasDerivAt (c n t : ℝ) :
    HasDerivAt (positiveDerivative c n) (-c*PositiveAngularEnvelope.phi t-PositiveAngularEnvelope.phi (n-t)) t := by
  have hc := (Real.hasDerivAt_cos (n-t)).comp_const_sub n t
  have hs := (Real.hasDerivAt_sin (n-t)).comp_const_sub n t
  show HasDerivAt (fun x => c*(Real.cos x-Real.sin x)-(Real.cos (n-x)-Real.sin (n-x))) _ t
  exact ((((Real.hasDerivAt_cos t).sub (Real.hasDerivAt_sin t)).const_mul c).sub
    (hc.sub hs)).congr_deriv (by simp only [PositiveAngularEnvelope.phi]; ring)

theorem negative_full_hasDerivAt (c n t : ℝ) :
    HasDerivAt (fun x => equalBase c n x false-
      fullSupport (forceA c (-x) (-(n-x))) (forceB c (-x) (-(n-x))))
      (negativeDerivative c n t) t := by
  simp_rw [negative_full_identity]
  have hc := (Real.hasDerivAt_cos (n-t)).comp_const_sub n t
  exact (((((((Real.hasDerivAt_cos t).sub_const 1).const_mul c).add hc).sub_const 1).add_const
    ((1+c)*(GlobalGA.Secondary.diagonal+1/2))).sub_const (R*pairNorm 1 c (-n))).sub_const
    (vstar n) |>.congr_deriv (by unfold negativeDerivative; ring)

theorem negative_derivative_hasDerivAt (c n t : ℝ) :
    HasDerivAt (negativeDerivative c n) (-c*Real.cos t-Real.cos (n-t)) t := by
  have hs := (Real.hasDerivAt_sin (n-t)).comp_const_sub n t
  show HasDerivAt (fun x => -c*Real.sin x+Real.sin (n-x)) _ t
  exact (((Real.hasDerivAt_sin t).const_mul (-c)).add hs).congr_deriv (by ring)

theorem positive_axis_hasDerivAt (c n t : ℝ) :
    HasDerivAt (fun x => equalBase c n x true-forceA c x (n-x)*axial)
      (-c*((axial-1/2)*Real.cos t+(1/2)*Real.sin t)-
        ((axial-1/2)*Real.sin (n-t)+(1/2)*Real.cos (n-t))) t := by
  have hc := (Real.hasDerivAt_cos (n-t)).comp_const_sub n t
  have hs := (Real.hasDerivAt_sin (n-t)).comp_const_sub n t
  have hfun : (fun x => equalBase c n x true-forceA c x (n-x)*axial)=fun x =>
      c*(Real.cos x+Real.sin x-1)/2+(Real.cos (n-x)+Real.sin (n-x)-1)/2+
        ((1+c)*GlobalGA.Secondary.diagonal+slope*n)-(c*Real.sin x+Real.cos (n-x))*axial := by
    funext x
    simp only [equalBase,forceA,↓reduceIte]
    ring
  rw [hfun]
  have hA := ((((Real.hasDerivAt_cos t).add (Real.hasDerivAt_sin t)).sub_const 1).const_mul c).div_const 2
  have hB := ((hc.add hs).sub_const 1).div_const 2
  have hF := (((Real.hasDerivAt_sin t).const_mul c).add hc).mul_const axial
  exact (((hA.add hB).add_const ((1+c)*GlobalGA.Secondary.diagonal+slope*n)).sub hF).congr_deriv
    (by ring)

theorem positive_axis_antitone {c n : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) :
    AntitoneOn (fun x => equalBase c n x true-forceA c x (n-x)*axial) (Icc 0 n) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro t ht
    exact (positive_axis_hasDerivAt c n t).continuousAt.continuousWithinAt
  · intro t ht
    exact positive_axis_hasDerivAt c n t
  · intro t ht
    have ht' : t∈Icc 0 frameCap := ⟨ht.1.le,ht.2.le.trans hn.2⟩
    have hy : n-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1,hn.2]⟩
    have hb := axis_bracket_lower ht'
    have hs := (transport_trig hy).2.2.1
    have hcos : 0≤Real.cos (n-t) := by linarith [(transport_trig hy).1]
    have hp := mul_nonneg (show 0≤axial-1/2 by linarith [axial_bounds.1]) hs
    have hcp := mul_nonneg (show 0≤c by linarith [hc.1]) (show
      0≤(axial-1/2)*Real.cos t+(1/2)*Real.sin t by linarith)
    linarith

theorem equal_domains {n t : ℝ} (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) :
    SignedDomain t (n-t) ∧ SignedDomain (-t) (-(n-t)) := by
  have hy : 0≤n-t := by linarith [ht.2]
  have hz : (0:ℝ)≤frameCap := by norm_num [frameCap]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    simp only [positiveTotal,negativeTotal,positivePart,negativePart,neg_neg,
      max_eq_left ht.1,max_eq_left hy,max_eq_right (neg_nonpos.mpr ht.1),
      max_eq_right (neg_nonpos.mpr hy)] <;>
    linarith [hn.2]

theorem positive_path_lower {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) : -slope*n≤D c t (n-t) := by
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hleft : 0 ≤ equalBase c n 0 true-sortedSupport (forceA c 0 n) (forceB c 0 n) := by
    have hh := positive_base_identity (c:=c) hn (show (0:ℝ)∈Icc 0 n from ⟨le_rfl,hn.1⟩)
    have hs := mixed_reverse_lower hc hn hz
    simp only [sub_zero,neg_zero,vstar,V_zero] at hh hs
    linarith
  have hright : 0 ≤ equalBase c n n true-sortedSupport (forceA c n 0) (forceB c n 0) := by
    have hh := positive_base_identity (c:=c) hn (show n∈Icc 0 n from ⟨hn.1,le_rfl⟩)
    have hs := mixed_forward_lower hc hn hz
    simp only [sub_self,neg_zero,vstar,V_zero] at hh hs
    linarith
  have hbound := support_path_lower
    (base:=fun x => equalBase c n x true) (f:=fun x => forceA c x (n-x))
    (g:=fun x => forceB c x (n-x))
    (df:=positiveDerivative c n)
    (ddf:=fun x => -c*PositiveAngularEnvelope.phi x-PositiveAngularEnvelope.phi (n-x)) (κ:=1)
    (by simp only [equalBase,↓reduceIte]; fun_prop) (by dsimp [forceA]; fun_prop)
    (by dsimp [forceB]; fun_prop) ht (by norm_num)
    (fun x hx => positive_force_positive hc ⟨hx.1,hx.2.trans hn.2⟩
      ⟨by linarith [hx.2],by linarith [hx.1,hn.2]⟩)
    (fun x hx => by
      have h₁ : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans hn.2⟩
      have h₂ : n-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [hx.1,hn.2]⟩
      have hd := diagonal_residual hc (equal_domains hn hx).1
      rw [edgeWidth_positive_formula h₁,edgeWidth_positive_formula h₂] at hd
      simp only [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left h₁.1,max_eq_left h₂.1,max_eq_right (neg_nonpos.mpr h₁.1),
        max_eq_right (neg_nonpos.mpr h₂.1),add_zero,vstar,V_zero,sub_zero] at hd
      simp only [equalBase,↓reduceIte]
      linarith)
    (fun x hx _ => by
      have ha := positive_axis_antitone hc hn hx ⟨hn.1,le_rfl⟩ hx.2
      have hp := positive_force_positive (x:=n) (y:=0) hc hn hz
      have hs := axis_support_lower hp.1 hp.2
      simp only [sub_self] at ha
      linarith)
    (by simpa using hleft) (by simpa using hright)
    (fun x _ => positive_full_hasDerivAt c n x)
    (fun x _ => positive_derivative_hasDerivAt c n x)
    (fun x hx => by
      have h₁ := CorrelatedSameBlock.one_le_phi
        (show x∈Icc 0 frameCap from ⟨hx.1.le,hx.2.le.trans hn.2⟩)
      have h₂ := CorrelatedSameBlock.one_le_phi (show n-x∈Icc 0 frameCap by
        constructor <;> linarith [hx.1,hx.2,hn.2])
      have hm := mul_le_mul_of_nonneg_left h₁ (by linarith [hc.1] : 0≤c)
      linarith [hc.1])
  rw [positive_base_identity hn ht] at hbound
  linarith

def negativeAxisGate (c n t : ℝ) : ℝ :=
  (axial+1/2)*forceB c (-t) (-(n-t))-forceA c (-t) (-(n-t))/2

theorem negative_axis_gate_hasDerivAt (c n t : ℝ) :
    HasDerivAt (negativeAxisGate c n)
      ((axial+1/2)*forceA c (-t) (-(n-t))+forceB c (-t) (-(n-t))/2) t := by
  have hc := (Real.hasDerivAt_cos (n-t)).comp_const_sub n t
  have hs := (Real.hasDerivAt_sin (n-t)).comp_const_sub n t
  have hfun : negativeAxisGate c n=fun x =>
      (axial+1/2)*(c*Real.cos x-Real.sin (n-x))-(-c*Real.sin x+Real.cos (n-x))/2 := by
    funext x
    simp only [negativeAxisGate,forceA,forceB,Real.cos_neg,Real.sin_neg]
    ring
  rw [hfun]
  exact ((((((Real.hasDerivAt_cos t).const_mul c).sub hs).const_mul (axial+1/2)).sub
    ((((Real.hasDerivAt_sin t).const_mul (-c)).add hc).div_const 2))).congr_deriv
    (by simp only [forceA,forceB,Real.cos_neg,Real.sin_neg]; ring)

theorem negative_axis_gate_positive {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) : 0<negativeAxisGate c n t := by
  have hmono : MonotoneOn (negativeAxisGate c n) (Icc 0 n) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      exact (negative_axis_gate_hasDerivAt c n x).continuousAt.continuousWithinAt
    · intro x hx
      exact negative_axis_gate_hasDerivAt c n x
    · intro x hx
      have hp := negative_force_positive hc hn (Ioo_subset_Icc_self hx)
      have hm := mul_nonneg (show 0≤axial+1/2 by linarith [axial_bounds.1]) hp.1.le
      linarith [hp.2]
  have hs := (transport_trig hn).2.2.2.1
  have hA : (19/10:ℝ)<axial+1/2 := by linarith [axial_bounds.1]
  have hpos : 0<c-Real.sin n := by linarith [hc.1]
  have hm := mul_lt_mul_of_pos_right hA hpos
  have hz : 0<negativeAxisGate c n 0 := by
    simp only [negativeAxisGate,forceA,forceB,neg_zero,sub_zero,Real.cos_zero,
      Real.sin_zero,Real.cos_neg,Real.sin_neg,mul_zero,zero_add,mul_one]
    nlinarith [Real.cos_le_one n,hc.1]
  exact hz.trans_le (hmono ⟨le_rfl,hn.1⟩ ht ht.1)

theorem negative_path_lower {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) : vstar n≤D c (-t) (-(n-t)) := by
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hleft : 0≤equalBase c n 0 false-sortedSupport (forceA c 0 (-n)) (forceB c 0 (-n)) := by
    have hh := negative_base_identity (c:=c) hn (show (0:ℝ)∈Icc 0 n from ⟨le_rfl,hn.1⟩)
    have hs := one_angle_lower hc hn
    simp only [sub_zero,neg_zero] at hh
    linarith
  have hright : 0≤equalBase c n n false-sortedSupport (forceA c (-n) 0) (forceB c (-n) 0) := by
    have hh := negative_base_identity (c:=c) hn (show n∈Icc 0 n from ⟨hn.1,le_rfl⟩)
    have hs := mixed_reverse_lower hc hz hn
    simp only [sub_self,neg_zero,mul_zero,neg_zero,zero_add] at hh hs
    linarith
  have hbound := support_path_lower
    (base:=fun x => equalBase c n x false) (f:=fun x => forceA c (-x) (-(n-x)))
    (g:=fun x => forceB c (-x) (-(n-x))) (df:=negativeDerivative c n)
    (ddf:=fun x => -c*Real.cos x-Real.cos (n-x)) (κ:=1/2)
    (by dsimp [equalBase]; fun_prop) (by dsimp [forceA]; fun_prop)
    (by dsimp [forceB]; fun_prop) ht (by norm_num)
    (fun x hx => negative_force_positive hc hn hx)
    (fun x hx => by
      have h₁ : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans hn.2⟩
      have h₂ : n-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [hx.1,hn.2]⟩
      have hd := diagonal_residual hc (equal_domains hn hx).2
      rw [edgeWidth_negative_formula h₁,edgeWidth_negative_formula h₂] at hd
      simp only [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left h₁.1,max_eq_left h₂.1,max_eq_right (neg_nonpos.mpr h₁.1),
        max_eq_right (neg_nonpos.mpr h₂.1),neg_neg,add_zero,mul_zero,
        show x+(n-x)=n by ring] at hd
      dsimp [equalBase]
      linarith)
    (fun x hx ha => by
      have hp := negative_axis_gate_positive hc hn hx
      dsimp [negativeAxisGate] at hp
      linarith)
    (by simpa using hleft) (by simpa using hright)
    (fun x _ => negative_full_hasDerivAt c n x)
    (fun x _ => negative_derivative_hasDerivAt c n x)
    (fun x hx => by
      have h₁ := (transport_trig (show x∈Icc 0 frameCap from ⟨hx.1.le,hx.2.le.trans hn.2⟩)).1
      have h₂ := (transport_trig (show n-x∈Icc 0 frameCap by
        constructor <;> linarith [hx.1,hx.2,hn.2])).1
      have hm := mul_le_mul_of_nonneg_right hc.1 (by linarith : 0≤Real.cos x)
      linarith)
  rw [negative_base_identity hn ht] at hbound
  linarith

/-- The minorant `-slope * positiveTotal x y + vstar (negativeTotal x y) ≤ D c x y` on the whole
signed domain, with the sorted zero-angle support and every equality transition. -/
theorem lower {c x y : ℝ} (hc : c∈Icc 1 Cmax)
    (hxy : SignedDomain x y) :
    -slope*positiveTotal x y+vstar (negativeTotal x y)≤D c x y := by
  have ha := signed_domain_angles hxy
  by_cases hx : 0≤x
  · by_cases hy : 0≤y
    · have hn : x+y∈Icc 0 frameCap := by
        refine ⟨add_nonneg hx hy,?_⟩
        simpa [positiveTotal,positivePart,max_eq_left hx,max_eq_left hy] using hxy.1
      have hh := positive_path_lower hc hn (show x∈Icc 0 (x+y) by constructor <;> linarith)
      simp only [show x+y-x=y by ring] at hh
      simpa [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left hx,max_eq_left hy,max_eq_right (neg_nonpos.mpr hx),
        max_eq_right (neg_nonpos.mpr hy),vstar] using hh
    · have hy' : 0≤ -y := by linarith
      have hh := mixed_forward_lower hc ⟨hx,(le_abs_self x).trans ha.1⟩
        ⟨hy',(neg_le_abs y).trans ha.2⟩
      simpa [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left hx,max_eq_left hy',max_eq_right (neg_nonpos.mpr hx),
        max_eq_right (le_of_not_ge hy)] using hh
  · have hx' : 0≤ -x := by linarith
    by_cases hy : 0≤y
    · have hh := mixed_reverse_lower hc ⟨hy,(le_abs_self y).trans ha.2⟩
        ⟨hx',(neg_le_abs x).trans ha.1⟩
      simpa [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left hy,max_eq_left hx',max_eq_right (neg_nonpos.mpr hy),
        max_eq_right (le_of_not_ge hx)] using hh
    · have hy' : 0≤ -y := by linarith
      have hn : -x+(-y)∈Icc 0 frameCap := by
        refine ⟨add_nonneg hx' hy',?_⟩
        simpa [negativeTotal,negativePart,max_eq_left hx',max_eq_left hy'] using hxy.2
      have hh := negative_path_lower hc hn
        (show -x∈Icc 0 (-x+(-y)) by constructor <;> linarith)
      simp only [neg_neg,show -x+(-y)-(-x)= -y by ring] at hh
      simpa [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left hx',max_eq_left hy',max_eq_right (le_of_not_ge hx),
        max_eq_right (le_of_not_ge hy)] using hh

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.DEnvelope
end
end
end

section
/-!
## The wider D minorant at a sorted outer point

The support of the forces at a sorted point `P` of the disk with `P.y ≤ 0` is at most
`sortedSupport` (`actual_support`). A negative first force in the reversed mixed quadrant is
treated by the diagonal support inequality, which only requires a nonnegative total force. The
other three quadrants use their positive forces.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.DEnvelope
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3

theorem actual_support {Q c x y : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : P.y≤0) (hP : P.Contained Q) (hQ : Q≤qCap)
    (hc : c∈Icc 1 Cmax) (hxy : SignedDomain x y) :
    forceA c x y*P.a+forceB c x y*(-P.y)≤ sortedSupport (forceA c x y) (forceB c x y) := by
  have ha := signed_domain_angles hxy
  have huse (hp : 0<forceA c x y ∧ 0<forceB c x y) :=
    actual_sorted_support hs hy hP hQ hp.1.le hp.2.le
  by_cases hx0 : 0≤x
  · have hx : x∈Icc 0 frameCap := ⟨hx0,(le_abs_self x).trans ha.1⟩
    by_cases hy0 : 0≤y
    · exact huse (positive_force_positive hc hx ⟨hy0,(le_abs_self y).trans ha.2⟩)
    · have hn : -y∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs y).trans ha.2⟩
      apply huse
      simpa only [neg_neg] using forward_force_positive hc hx hn
  · have hn : -x∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs x).trans ha.1⟩
    by_cases hy0 : 0≤y
    · have ht : y∈Icc 0 frameCap := ⟨hy0,(le_abs_self y).trans ha.2⟩
      have hnt := transport_trig hn
      have htt := transport_trig ht
      have hphi := CorrelatedSameBlock.one_le_phi hn
      have hmul := mul_le_mul_of_nonneg_left hphi (by linarith [hc.1] : 0≤c)
      have hfg : forceA c x y≤forceB c x y := by
        dsimp [forceA,forceB,PositiveAngularEnvelope.phi] at *
        rw [Real.cos_neg,Real.sin_neg] at hphi hnt hmul
        nlinarith [Real.cos_le_one y,hc.1,htt.2.2.1]
      have hdiff : 0<Real.cos (-x)-Real.sin (-x) := by
        linarith [hnt.1,hnt.2.2.2.1]
      have hscaled := mul_pos (by linarith [hc.1] : 0<c) hdiff
      have hsum : 0≤forceA c x y+forceB c x y := by
        dsimp [forceA,forceB]
        rw [Real.cos_neg,Real.sin_neg] at hscaled
        linarith [htt.1,htt.2.2.1]
      have hcircle : (P.a+1/2)^2+(-P.y+1/2)^2≤qCap := by
        simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos hy] using hP.trans hQ
      have hb : -P.y≤P.a := by simpa [abs_of_nonpos hy] using hs.2
      have hh := raw_clipped_support hcircle hb (by linarith [hs.1]) hsum
      simpa [clippedSupport,sortedSupport,hfg] using hh
    · have htotal : -x+(-y)∈Icc 0 frameCap := by
        refine ⟨by linarith,?_⟩
        simpa [negativeTotal,negativePart,max_eq_left (show 0≤ -x by linarith),
          max_eq_left (show 0≤ -y by linarith)] using hxy.2
      have hp := negative_force_positive hc htotal
        (show -x∈Icc 0 (-x+(-y)) by constructor <;> linarith)
      apply huse
      simpa only [neg_neg,show -x+(-y)-(-x)= -y by ring] using hp

/-- The wider signed D envelope at the point `P` itself. -/
theorem actual_minorant {Q c x y : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : P.y≤0) (hP : P.Contained Q) (hQ : Q≤qCap)
    (hc : c∈Icc 1 Cmax) (hxy : SignedDomain x y) :
    -slope*positiveTotal x y+vstar (negativeTotal x y)≤
      c*(edgeWidth x-1)+edgeWidth y-1+(1+c)*GlobalGA.Secondary.diagonal-
        (forceA c x y*P.a+forceB c x y*(-P.y)) := by
  have hsupp := actual_support hs hy hP hQ hc hxy
  have hminor := lower hc hxy
  dsimp only [PositiveBT3.D] at hminor
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.DEnvelope
end
end
end

section
/-!
## The complete original negative-A / high positive-TD2 contradiction

Every concentrated
alternative is paid by the actual coefficient family. The final
statement applies directly to the original sorted and contained cycle
and its original owner witnesses.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.HighSource
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem negative_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (hsz : s≤z) (i : Fin 4) :
    0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z+
      V R (Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i)
        (Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i) (z-s) := by
  by_cases hi : HighUnaffected.Unaffected atG i
  · exact HighUnaffected.original atG hz hs hsz i hi
  · have hh := HighAffected.original atG hz hs hsz
    cases atG <;> fin_cases i <;>
      simp [HighUnaffected.Unaffected] at hi <;>
      simpa [HighAffected.value,Source.pWeights,Source.qWeights,lambdaG,lambdaB,Explicit.m] using hh

theorem pure_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (i j : Fin 4) :
    0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z+
      Concentration.pure R (GlobalGA.Secondary.diagonal-1/2)
        (Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s)
        (Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s) 3 i j s z := by
  by_cases hsz : s≤z
  · simpa only [Concentration.pure,hsz,↓reduceIte] using negative_positive atG hz hs hsz j
  · have hz' : z∈Icc (Certificate.left .high:ℝ) (Certificate.right .high:ℝ) := by
      norm_num [Certificate.left,Certificate.right,Certificate.split,PositiveTD.Certificate.h]
      exact hz
    have hp := AffectedPositive.all_positive_reduces_to_equal .high atG hz' hs (le_of_not_ge hsz) i
    have he : 0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z z := by
      cases atG
      · exact (Certificate.high_endpoints hz).2.2.2.2
      · exact (Certificate.high_endpoints hz).2.2.2.1
    simp only [Concentration.pure,hsz,↓reduceIte]
    linarith

theorem intrinsic_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (i j : Fin 4) :
    0<Source.intrinsic atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z i j := by
  rw [HighSaturated.intrinsic_eq_pure atG hz hs i j]
  exact pure_positive atG hz hs i j

theorem original {q s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (ha : Source.aError C atG=-s)
    (hflat : (C.point A).a=7/12)
    (hz : delta C.theta T∈Icc (1/5:ℝ) (7/10:ℝ))
    (hhg : hg=0 ∨ hg=2) (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) : False := by
  have hz' : delta C.theta T∈Icc (Certificate.left .high:ℝ) (Certificate.right .high:ℝ) := by
    norm_num [Certificate.left,Certificate.right,Certificate.split,PositiveTD.Certificate.h]
    exact hz
  obtain ⟨i,j,hh⟩ := Source.original_intrinsic_nonpositive .high atG
    hsorted hcontained hq hHy hGy hBy hDy hvar hs ha hflat hz' hhg hHG hGA hAB hBT hTD hDE hEH
  exact (not_le_of_gt (intrinsic_positive atG hz hs i j)) hh

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.HighSource
end
end
end

section
/-!
## Every low pure endpoint with the original coefficients

Both signs of the remaining total are included. Every
scalar endpoint is discharged by the literal low-family certificate.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowPure
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open SecantCoordinate LowNegativeCurvature

private lemma r71_low_dom {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]
  exact hz

def scalar (atG : Bool) (z x : ℝ) : ℝ :=
  pure (baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) 0 z)
    (Explicit.l .low z)
    (SecantBaseline.basicRatio atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z)
    (Explicit.k .low z) 1 z x

theorem ratio_domain (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    SecantBaseline.basicRatio atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z
      ∈Icc 0 (71/50:ℝ) := by
  obtain ⟨hk,hl,hc,hm⟩ := Explicit.family_positive .low (r71_low_dom hz)
  cases atG
  · change Explicit.m .low z/Explicit.l .low z∈Icc 0 (71/50:ℝ)
    exact ⟨div_nonneg hm.le hl.le,(div_le_iff₀ hl).2 (Explicit.low_tilted hz).2.le⟩
  · change Explicit.k .low z/Explicit.l .low z∈Icc 0 (71/50:ℝ)
    exact ⟨div_nonneg hk.le hl.le,(div_le_iff₀ hl).2
      (by linarith [(Explicit.low_ratio hz).2])⟩

theorem scalar_concave (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    ConcaveOn ℝ (Icc 0 (Real.tan z)) (scalar atG z) := by
  obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi⟩ := Explicit.low_ranges hz
  have hzframe : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  apply pure_concave (by linarith : 0<Explicit.k .low z) (by norm_num : (0:ℝ)<1)
    hzframe le_rfl hzframe.2
  intro x hx
  have hs := arctan_interval hzframe hx
  have hxhi : x≤203/1000 := by
    have ht := tan_monotone hzframe
      (show (1/5:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz.2
    linarith [hx.2,tan_low_cut]
  exact (pure_curvature (by linarith : (1:ℝ)≤Explicit.l .low z)
    (ratio_domain atG hz) ⟨hklo.le,hkhi⟩ ⟨hx.1,hxhi⟩
    ⟨by linarith [hs.2],by linarith [hs.1,hz.2]⟩).le.trans (by norm_num)

theorem scalar_zero (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    0<scalar atG z 0 := by
  have he : scalar atG z 0=PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z)
      (Explicit.c .low z) z+V R (Explicit.k .low z) 1 z := by
    simp only [scalar,SecantCoordinate.pure,sub_self,mul_zero,Real.arctan_zero,sub_zero,add_zero,
      baseline_zero]
  rw [he]
  exact (Certificate.low_endpoints hz).1

theorem scalar_equal (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    0<scalar atG z (Real.tan z) := by
  have hzframe : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hh := pure_at_original (p:=Explicit.k .low z) (q:=1) (k:=Explicit.k .low z)
    (c:=Explicit.c .low z) (z:=z) atG (Explicit.family_positive .low (r71_low_dom hz)).2.1 hzframe
  simpa only [scalar,hh,sub_self,V_zero,add_zero] using LowEqual.original atG hz

theorem H_positive (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/5:ℝ))
    (hs : s∈Icc 0 z) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      V R (Explicit.k .low z) 1 (z-s) := by
  have hzframe : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hsframe : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans hzframe.2⟩
  have hx : Real.tan s∈Icc 0 (Real.tan z) :=
    ⟨tan_nonnegative hsframe,tan_monotone hsframe hzframe hs.2⟩
  have hm := (scalar_concave atG hz).min_le_of_mem_Icc
    ⟨le_rfl,tan_nonnegative hzframe⟩ ⟨tan_nonnegative hzframe,le_rfl⟩ hx
  have hpos : 0<scalar atG z (Real.tan s) :=
    (lt_min (scalar_zero atG hz) (scalar_equal atG hz)).trans_le hm
  rwa [scalar,pure_at_original atG (Explicit.family_positive .low (r71_low_dom hz)).2.1 hsframe]
    at hpos

theorem negative_positive (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/5:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (hsz : s≤z) (i : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      V R (Source.pWeights atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s i)
        (Source.qWeights atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s i) (z-s) := by
  have hh := H_positive atG hz ⟨hs.1,hsz⟩
  have hc := LowNegativeComparison.original (t:=z-s) atG hz hs
    ⟨by linarith,by linarith [hz.2,hs.1]⟩ i
  linarith

theorem original (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/5:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      Concentration.pure R (GlobalGA.Secondary.diagonal-1/2)
        (Source.pWeights atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s)
        (Source.qWeights atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s) 3 i j s z := by
  by_cases hsz : s≤z
  · simpa only [Concentration.pure,hsz,↓reduceIte] using negative_positive atG hz hs hsz j
  · have hp := AffectedPositive.all_positive_reduces_to_equal .low atG (r71_low_dom hz) hs
      (le_of_not_ge hsz) i
    have he := LowEqual.original atG hz
    simp only [Concentration.pure,hsz,↓reduceIte]
    linarith

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowPure
end
end
end

section
/-!
## All low saturated alternatives with the original pairs

The H and B same-block cases
use the displayed ratio `1.5`; G uses its increasing combined curve.
Every separated case, including the D linear term, uses the same
original positive allowance and one of the certified H/G endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowSaturated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveTD.Hybrid

private lemma r71_low_dom {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]
  exact hz

def p (atG : Bool) (s z : ℝ) : Fin 4→ℝ :=
  Source.pWeights atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s
def q (atG : Bool) (s z : ℝ) : Fin 4→ℝ :=
  Source.qWeights atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s
def largerCap (z : ℝ) : ℝ := Explicit.m .low z+(2/5)*z

theorem B_coefficients (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) :
    Explicit.l .low z≤lambdaB atG (Explicit.l .low z) s ∧
      lambdaB atG (Explicit.l .low z) s≤(27/25)*Explicit.l .low z := by
  have hl := (Explicit.family_positive .low (r71_low_dom hz)).2.1
  have hsec := (Explicit.secant_bounds .low atG (r71_low_dom hz) hs).1
  have hcos := Explicit.AB_cut_cosine (Explicit.angle_domain atG hs).1
  have hc : 0<Real.cos s := by linarith
  have hupper : NegativeAPositiveTD.secant (Explicit.l .low z) s≤(27/25)*Explicit.l .low z := by
    apply (div_le_iff₀ hc).2
    nlinarith [mul_lt_mul_of_pos_left hcos hl]
  cases atG <;> simp only [lambdaB,↓reduceIte]
  · exact ⟨hsec,hupper⟩
  · exact ⟨le_rfl,by nlinarith⟩

theorem pair_HB_ratio (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (i : Fin 4) (hi : i=0∨i=2) : q atG s z i≤(3/2)*p atG s z i := by
  obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi⟩ := Explicit.low_ranges hz
  obtain ⟨hB,hBhi⟩ := B_coefficients atG hz hs
  have hm := Explicit.low_tilted hz
  rcases hi with rfl|rfl
  · change 1≤(3/2)*Explicit.k .low z
    linarith
  · change max (lambdaB atG (Explicit.l .low z) s) (Explicit.m .low z)≤
      (3/2)*min (lambdaB atG (Explicit.l .low z) s) (Explicit.m .low z)
    have hmin : Explicit.l .low z≤ min (lambdaB atG (Explicit.l .low z) s) (Explicit.m .low z) :=
      le_min hB hm.1.le
    have hmax : max (lambdaB atG (Explicit.l .low z) s) (Explicit.m .low z)≤(3/2)*Explicit.l .low z := by
      exact max_le (by linarith) (by linarith [hm.2])
    exact hmax.trans (mul_le_mul_of_nonneg_left hmin (by norm_num))

theorem larger_bounds (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i : Fin 4) :
    1≤q atG s z i ∧ q atG s z i≤largerCap z := by
  obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi⟩ := Explicit.low_ranges hz
  have hm := Explicit.low_tilted hz
  have hs' := (Explicit.angle_domain atG hs).1
  have hsec := (Explicit.secant_bounds .low atG (r71_low_dom hz) hs).1
  have hcap := Explicit.low_secant hz hs'
  have hM : Explicit.m .low z≤largerCap z := by dsimp [largerCap]; linarith [hz.1]
  have hL : Explicit.l .low z≤largerCap z := hm.1.le.trans hM
  have hG : Explicit.l .low z≤lambdaG atG (Explicit.l .low z) s ∧
      lambdaG atG (Explicit.l .low z) s≤largerCap z := by
    cases atG <;> simp only [lambdaG,↓reduceIte]
    · exact ⟨le_rfl,hL⟩
    · exact ⟨hsec,hcap.le⟩
  have hB : Explicit.l .low z≤lambdaB atG (Explicit.l .low z) s ∧
      lambdaB atG (Explicit.l .low z) s≤largerCap z := by
    cases atG <;> simp only [lambdaB,↓reduceIte]
    · exact ⟨hsec,hcap.le⟩
    · exact ⟨le_rfl,hL⟩
  fin_cases i
  · change 1≤(1:ℝ) ∧ 1≤largerCap z
    exact ⟨le_rfl,by linarith⟩
  · change 1≤lambdaG atG (Explicit.l .low z) s ∧ lambdaG atG (Explicit.l .low z) s≤largerCap z
    exact ⟨by linarith [hG.1],hG.2⟩
  · change 1≤ max (lambdaB atG (Explicit.l .low z) s) (Explicit.m .low z) ∧
      max (lambdaB atG (Explicit.l .low z) s) (Explicit.m .low z)≤largerCap z
    exact ⟨(by linarith : (1:ℝ)≤lambdaB atG (Explicit.l .low z) s).trans (le_max_left _ _),max_le hB.2 hM⟩
  · change 1≤(1:ℝ) ∧ 1≤largerCap z
    exact ⟨le_rfl,by linarith⟩

theorem positive_allowance (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i : Fin 4) :
    -LowSeparated.allowance z≤positive R (GlobalGA.Secondary.diagonal-1/2) (p atG s z) (q atG s z) 3 i (frameCap-z) := by
  have hc : 0<p atG s z i ∧ p atG s z i≤q atG s z i ∧ q atG s z i≤2*p atG s z i :=
    Explicit.ordered_pair_domain .low atG (r71_low_dom hz) hs i
  have hq := larger_bounds atG hz hs i
  have hP : frameCap-z∈Icc 0 frameCap := by
    dsimp [frameCap]
    constructor <;> linarith [hz.1,hz.2]
  have hu := HighSaturated.positive_lower (p:=p atG s z) (q:=q atG s z) (d:=(3:Fin 4)) (i:=i)
    (a:=GlobalGA.Secondary.diagonal-1/2)
    (by linarith [diagonal_bounds.2]) hc.1 hc.2.1 hc.2.2 hq.1 hP
  have hh := mul_le_mul_of_nonneg_right hq.2 hP.1
  dsimp [LowSeparated.allowance,largerCap] at hh ⊢
  nlinarith only [hu,hh]

theorem separated_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      positive R (GlobalGA.Secondary.diagonal-1/2) (p atG s z) (q atG s z) 3 i (frameCap-z)+
        V R (p atG s z j) (q atG s z j) (frameCap-s) := by
  have hu := positive_allowance atG hz hs i
  have hH := LowSeparated.H_positive atG hz hs
  have hG := LowSeparated.G_positive atG hz hs
  have hsf := (Explicit.angle_domain atG hs).2
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hsf.2],by linarith [hsf.1]⟩
  fin_cases j
  · change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      positive R (GlobalGA.Secondary.diagonal-1/2) (p atG s z) (q atG s z) 3 i (frameCap-z)+
        V R (Explicit.k .low z) 1 (frameCap-s)
    linarith
  · change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      positive R (GlobalGA.Secondary.diagonal-1/2) (p atG s z) (q atG s z) 3 i (frameCap-z)+
        V R (Explicit.k .low z) (lambdaG atG (Explicit.l .low z) s) (frameCap-s)
    linarith
  · have hB := LowNegativeComparison.B_dominates_H atG hz hs hN
    change V R (Explicit.k .low z) 1 (frameCap-s)≤V R (p atG s z 2) (q atG s z 2) (frameCap-s) at hB
    change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      positive R (GlobalGA.Secondary.diagonal-1/2) (p atG s z) (q atG s z) 3 i (frameCap-z)+
        V R (p atG s z 2) (q atG s z 2) (frameCap-s)
    linarith
  · change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      positive R (GlobalGA.Secondary.diagonal-1/2) (p atG s z) (q atG s z) 3 i (frameCap-z)+
        V R (Explicit.k .low z) 1 (frameCap-s)
    linarith

theorem HB_pure_le_same (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (i : Fin 4) (hi : i=0∨i=2) :
    Concentration.pure R (GlobalGA.Secondary.diagonal-1/2) (p atG s z) (q atG s z) 3 i i s z≤
      mixedBlock R (p atG s z i) (q atG s z i) (frameCap-z) (frameCap-s) := by
  have hc : 0<p atG s z i ∧ p atG s z i≤q atG s z i ∧ q atG s z i≤2*p atG s z i :=
    Explicit.ordered_pair_domain .low atG (r71_low_dom hz) hs i
  have hratio := pair_HB_ratio atG hz hs i hi
  have hsf := (Explicit.angle_domain atG hs).2
  have hP : frameCap-z∈Icc 0 frameCap := by
    dsimp [frameCap]
    constructor <;> linarith [hz.1,hz.2]
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hsf.2],by linarith [hsf.1]⟩
  have hid : i≠3 := by rcases hi with rfl|rfl <;> decide
  by_cases hsz : s≤z
  · have hsin := (transport_trig hN).2.2.2.1
    have hq0 : 0≤q atG s z i := (hc.1.trans_le hc.2.1).le
    have hprod := mul_le_mul hratio hsin.le (transport_trig hN).2.2.1
      (show (0:ℝ)≤(3/2)*p atG s z i by exact mul_nonneg (by norm_num) hc.1.le)
    have hpay : q atG s z i*Real.sin (frameCap-s)≤p atG s z i := by
      nlinarith only [hprod,hc.1]
    have hh := SameBlock.negative_surplus hc.1.le
      (show frameCap-z∈Icc 0 (frameCap-s) from ⟨hP.1,by linarith⟩) hN hpay
    simpa only [Concentration.pure,hsz,↓reduceIte,show frameCap-s-(frameCap-z)=z-s by ring] using hh
  · have hh := SameBlock.positive_surplus hc.1.le
      (show q atG s z i≤(17/10)*p atG s z i by nlinarith only [hratio,hc.1]) hP
      (show frameCap-s∈Icc 0 (frameCap-z) from ⟨hN.1,by linarith⟩)
    simpa only [Concentration.pure,hsz,positive,hid,↓reduceIte,
      show frameCap-z-(frameCap-s)=s-z by ring] using hh

theorem original (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      Concentration.saturated R (GlobalGA.Secondary.diagonal-1/2) (p atG s z) (q atG s z) 3 i j s z := by
  by_cases hij : i=j
  · subst j
    by_cases hiD : i=3
    · subst i
      simpa only [Concentration.saturated,block,positive,↓reduceIte,add_assoc] using
        separated_positive atG hz hs 3 3
    by_cases hiG : i=1
    · subst i
      simpa [Concentration.saturated,block,p,q,Source.pWeights,Source.qWeights,
        LowSaturatedG.same] using LowSaturatedG.same_positive atG hz hs
    have hi : i=0∨i=2 := by fin_cases i <;> simp_all
    have hcomp := HB_pure_le_same atG hz hs i hi
    have hpure := LowPure.original atG hz hs i i
    change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      Concentration.pure R (GlobalGA.Secondary.diagonal-1/2) (p atG s z) (q atG s z) 3 i i s z at hpure
    simp only [Concentration.saturated,block,hiD,↓reduceIte]
    linarith
  · simpa only [Concentration.saturated,hij,↓reduceIte,add_assoc] using separated_positive atG hz hs i j

theorem intrinsic_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<Source.intrinsic atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z i j := by
  have hP := LowPure.original atG hz hs i j
  have hS := original atG hz hs i j
  change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
    min (Concentration.pure R (GlobalGA.Secondary.diagonal-1/2) (p atG s z) (q atG s z) 3 i j s z)
      (Concentration.saturated R (GlobalGA.Secondary.diagonal-1/2) (p atG s z) (q atG s z) 3 i j s z)
  rw [add_min]
  exact lt_min hP hS

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowSaturated
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open Certificate (Family)

theorem family_intrinsic_positive (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0< intrinsic atG (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) s z i j := by
  cases f
  · have hz' : z∈Icc 0 (1/5:ℝ) := by
      norm_num [Certificate.left,Certificate.right,Certificate.split] at hz
      exact hz
    exact LowSaturated.intrinsic_positive atG hz' hs i j
  · have hz' : z∈Icc (1/5:ℝ) (7/10:ℝ) := by
      norm_num [Certificate.left,Certificate.right,Certificate.split,
        PositiveTD.Certificate.h] at hz
      exact hz
    exact HighSource.intrinsic_positive atG hz' hs i j

theorem family_stress_positive {q s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (f : Family) (atG : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (ha : aError C atG=-s)
    (hflat : (C.point A).a=7/12)
    (hz : delta C.theta T∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hhg : hg=0 ∨ hg=2) :
    0<actualStress C hg atG (Explicit.k f (delta C.theta T))
      (Explicit.l f (delta C.theta T)) (Explicit.c f (delta C.theta T)) s := by
  let k := Explicit.k f (delta C.theta T)
  let l := Explicit.l f (delta C.theta T)
  let c := Explicit.c f (delta C.theta T)
  have hsf := (Explicit.angle_domain atG hs).2
  have hzf := Explicit.family_frame_domain f hz
  obtain ⟨hk,hG,hB,hc,hm⟩ := Explicit.family_coefficient_domain f atG hz hs
  have hcoeff := Explicit.ordered_pair_domain f atG hz hs
  have hb := original_budgets hg atG k l c hsf.1 ha hvar hzf.1
  have hlo := original_stress_lower atG hsorted hcontained hq hHy hGy hBy hDy
    hvar hsf ha hflat hzf.1 hhg hk hG hB hc hm
  obtain ⟨i,j,hmin⟩ := Concentration.concentrate R (GlobalGA.Secondary.diagonal-1/2)
    (pWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s)
    (qWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s)
    (fun i => (blocks C hg atG k l c s i).P)
    (fun i => (blocks C hg atG k l c s i).N) 3
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hcoeff i).1) (fun i => (hcoeff i).2.1) (fun i => (hcoeff i).2.2)
    (fun i => (blocks C hg atG k l c s i).P_nonneg)
    (fun i => (blocks C hg atG k l c s i).N_nonneg)
    hsf hzf hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2
  have hp := family_intrinsic_positive f atG hz hs i j
  change 0< intrinsic atG k l c s (delta C.theta T) i j at hp
  dsimp [intrinsic] at hp
  change 0<actualStress C hg atG k l c s
  linarith

theorem original {q s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (ha : aError C atG=-s)
    (hflat : (C.point A).a=7/12) (hz : 0≤delta C.theta T)
    (hhg : hg=0 ∨ hg=2) (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) : False := by
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hzframe : delta C.theta T∈Icc 0 frameCap :=
    ⟨hz,(le_abs_self _).trans (original_error_bound hvar hn T)⟩
  have hfamily (f : Family)
      (hf : delta C.theta T∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) : False := by
    have hp := family_stress_positive f atG hsorted hcontained hq hHy hGy hBy hDy
      hvar hs ha hflat hf hhg
    have hweights := Explicit.family_positive f hf
    have hnp := stress_nonpositive atG hweights.1.le hweights.2.1.le hweights.2.2.1
      (Explicit.angle_domain atG hs).2 hzframe hHG hGA hAB hBT hTD hDE hEH
    exact (not_le_of_gt hp) hnp
  by_cases hlow : delta C.theta T≤1/5
  · apply hfamily .low
    norm_num [Certificate.left,Certificate.right,Certificate.split]
    exact ⟨hz,hlow⟩
  · apply hfamily .high
    norm_num [Certificate.left,Certificate.right,Certificate.split,PositiveTD.Certificate.h]
    exact ⟨(lt_of_not_ge hlow).le,hzframe.2⟩

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Source
end
end
end
