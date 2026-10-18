module

public import SquaresInCircles.Eight.ExactFamily.EnvelopeCriticalPosition
public import SquaresInCircles.Eight.ExactFamily.ImplicitEnvelope
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Differentiating the actual five-corner envelope

The four positive circle radicals give joint smoothness of the defect
and its two gradient components. The implicit function theorem, together
with the geometric uniqueness of the position minimum, gives the actual
minimizing-position derivative. Its Schur complement is positive at
every critical tilt, including critical points of positive defect.

All hypotheses below are supplied by the actual circle chain and the
fixed compact minimizing window. No derivative identity, Hessian sign,
or regularity of a separately postulated envelope is assumed.
The Lean source remains uncompiled.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

open Set Filter EnvelopeGeometry
open scoped Topology ContDiff

def jointDefect (q : ℝ) (p : ℝ × ℝ) : ℝ :=
  defect q (Real.cos p.1) (Real.sin p.1) p.2
def jointPosition (q : ℝ) (p : ℝ × ℝ) : ℝ :=
  2*positionHalf q (Real.cos p.1) (Real.sin p.1) p.2
def jointTilt (q : ℝ) (p : ℝ × ℝ) : ℝ :=
  tiltFirst q (Real.cos p.1) (Real.sin p.1) p.2
def minimizingPosition (q t : ℝ) : ℝ :=
  windowMinimizer q (Real.cos t) (Real.sin t)
def tiltInterval : Set ℝ := Ioo 0 (Real.arctan (1/5))

theorem tiltInterval_bounds {t : ℝ} (ht : t∈tiltInterval) :
    0<Real.cos t ∧ 0<Real.sin t ∧ Real.sin t/Real.cos t<1/5 := by
  have hupper := Real.arctan_lt_pi_div_two (1/5:ℝ)
  have hmem : t∈Ioo (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [ht.1,ht.2,Real.pi_pos]
  have htan := Real.strictMonoOn_tan hmem (Real.arctan_mem_Ioo (1/5:ℝ)) ht.2
  rw [Real.tan_arctan,Real.tan_eq_sin_div_cos] at htan
  exact ⟨Real.cos_pos_of_mem_Ioo hmem,
    Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [hmem.2,Real.pi_pos]),htan⟩

theorem trig_unit (t : ℝ) : Real.cos t^2+Real.sin t^2=1 := by
  nlinarith [Real.sin_sq_add_cos_sq t]

private theorem upper_joint_contDiffAt {q : ℝ} {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ 2 f p) (hr : 0<upper q (f p)) :
    ContDiffAt ℝ 2 (fun x => upper q (f x)) p := by
  exact (contDiffAt_const.sub (hf.pow 2)).sqrt (ne_of_gt (Real.sqrt_pos.mp hr))

/-- All three functions are jointly smooth on the actual positive-radical
domain. The circle support estimates have already established those signs. -/
theorem SmoothDomain.joint_contDiffAt {q u : ℝ} (h : SmoothDomain q u) (t : ℝ) :
    ContDiffAt ℝ 2 (jointDefect q) (t,u) ∧
    ContDiffAt ℝ 2 (jointPosition q) (t,u) ∧
    ContDiffAt ℝ 2 (jointTilt q) (t,u) := by
  have dx : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => p.2) (t,u) := contDiffAt_snd
  have dc : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.cos p.1) (t,u) := contDiffAt_fst.cos
  have ds : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.sin p.1) (t,u) := contDiffAt_fst.sin
  have dr : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => lowerRight q p.2) (t,u) :=
    upper_joint_contDiffAt dx h.r_pos
  have dU : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => topRight q p.2) (t,u) :=
    upper_joint_contDiffAt (contDiffAt_const.sub dx) h.U_pos
  have dV : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => topLeft q p.2) (t,u) :=
    contDiffAt_const.sub dU
  have dY : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => topHeight q p.2) (t,u) :=
    upper_joint_contDiffAt dV h.Y_pos
  have dv : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => lowerHeight q p.2) (t,u) :=
    contDiffAt_const.sub dY
  have dw : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => lowerLeft q p.2) (t,u) :=
    upper_joint_contDiffAt dv h.w_pos
  have dk₁ : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => firstComponent q (Real.cos p.1) (Real.sin p.1) p.2) (t,u) :=
    (contDiffAt_const.sub (dc.mul (dr.sub contDiffAt_const))).add (ds.mul dx)
  have dk₂ : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => secondComponent q (Real.cos p.1) (Real.sin p.1) p.2) (t,u) :=
    (contDiffAt_const.add (dc.mul dv)).sub (ds.mul (dw.sub contDiffAt_const))
  have dp : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => slopeRatio q p.2) (t,u) :=
    ((contDiffAt_const.sub dx).mul dV).div (dU.mul dY) (ne_of_gt (mul_pos h.U_pos h.Y_pos))
  have dA : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Real.sin p.1+Real.cos p.1*p.2/lowerRight q p.2) (t,u) :=
    ds.add ((dc.mul dx).div dr (ne_of_gt h.r_pos))
  have dB : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Real.cos p.1+Real.sin p.1*lowerHeight q p.2/lowerLeft q p.2) (t,u) :=
    dc.add ((ds.mul dv).div dw (ne_of_gt h.w_pos))
  have dkt₁ : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => firstTilt q (Real.cos p.1) (Real.sin p.1) p.2) (t,u) :=
    (ds.mul (dr.sub contDiffAt_const)).add (dc.mul dx)
  have dkt₂ : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => secondTilt q (Real.cos p.1) (Real.sin p.1) p.2) (t,u) :=
    (ds.neg.mul dv).sub (dc.mul (dw.sub contDiffAt_const))
  exact ⟨((dk₁.pow 2).add (dk₂.pow 2)).sub contDiffAt_const,
    ((dk₁.mul dA).sub ((dk₂.mul dp).mul dB)).const_mul 2,
    ((dk₁.mul dkt₁).add (dk₂.mul dkt₂)).const_mul 2⟩

theorem jointDefect_hasFDerivAt {q u : ℝ} (h : SmoothDomain q u) (t : ℝ) :
    HasFDerivAt (jointDefect q)
      (pairDerivative (tiltFirst q (Real.cos t) (Real.sin t) u)
        (2*positionHalf q (Real.cos t) (Real.sin t) u)) (t,u) :=
  pair_hasFDerivAt ((h.joint_contDiffAt t).1.differentiableAt (by norm_num))
    (defect_angle_deriv q u t) (position_deriv h.r_pos h.U_pos h.Y_pos h.w_pos)

theorem jointPosition_hasFDerivAt {q u : ℝ} (h : SmoothDomain q u) (t : ℝ) :
    HasFDerivAt (jointPosition q)
      (pairDerivative (mixedSecond q (Real.cos t) (Real.sin t) u)
        (positionSecond q (Real.cos t) (Real.sin t) u)) (t,u) :=
  pair_hasFDerivAt ((h.joint_contDiffAt t).2.1.differentiableAt (by norm_num))
    (mixed_angle_deriv q u t) (position_second_deriv h)

/-- The other mixed partial is differentiated directly, so the Schur
formula does not depend on an uninstantiated symmetry assertion. -/
theorem tiltFirst_position_deriv {q c s u : ℝ} (h : SmoothDomain q u) :
    HasDerivAt (tiltFirst q c s) (mixedSecond q c s u) u := by
  obtain ⟨dr,_,_,_,dv,dw⟩ := h.radical_derivatives
  obtain ⟨dk₁,dk₂⟩ := components_position_deriv (c:=c) (s:=s) h
  have dt₁ : HasDerivAt (firstTilt q c s) (c-s*u/lowerRight q u) u := by
    have hh := ((dr.sub_const 1).const_mul s).add ((hasDerivAt_id u).const_mul c)
    convert hh using 1 <;> dsimp [firstTilt] <;> ring
  have dt₂ : HasDerivAt (secondTilt q c s)
      (s*slopeRatio q u-c*lowerHeight q u*slopeRatio q u/lowerLeft q u) u := by
    have hh := (dv.const_mul (-s)).sub ((dw.sub_const 1).const_mul c)
    convert hh using 1 <;> dsimp [secondTilt] <;> ring
  have hh := ((dk₁.mul dt₁).add (dk₂.mul dt₂)).const_mul 2
  convert hh using 1 <;>
    dsimp [tiltFirst,mixedSecond,mixedNormal,positionA,positionb,positionB] <;> ring

theorem jointTilt_hasFDerivAt {q u : ℝ} (h : SmoothDomain q u) (t : ℝ) :
    HasFDerivAt (jointTilt q)
      (pairDerivative (tiltSecond q (Real.cos t) (Real.sin t) u)
        (mixedSecond q (Real.cos t) (Real.sin t) u)) (t,u) :=
  pair_hasFDerivAt ((h.joint_contDiffAt t).2.2.differentiableAt (by norm_num))
    (defect_angle_second_deriv q u t) (tiltFirst_position_deriv h)

theorem minimizingPosition_smoothDomain {q t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) :
    SmoothDomain q (minimizingPosition q t) :=
  (window_bounds hql hqu (windowMinimizer_mem q (Real.cos t) (Real.sin t))).smoothDomain
    (by linarith)

theorem minimizingPosition_root {q t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (ht : t∈tiltInterval) :
    jointPosition q (t,minimizingPosition q t)=0 := by
  obtain ⟨hc,hs,htan⟩ := tiltInterval_bounds ht
  have hp := (windowMinimizer_geometric hql hqu hc hs.le (trig_unit t) htan.le).2.1
  dsimp [jointPosition,minimizingPosition]
  rw [hp,mul_zero]

theorem minimizingPosition_contDiffAt {q t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (ht : t∈tiltInterval) :
    ContDiffAt ℝ 2 (minimizingPosition q) t := by
  obtain ⟨hc,hs,htan⟩ := tiltInterval_bounds ht
  have hm := windowMinimizer_geometric hql hqu hc hs.le (trig_unit t) htan.le
  have hdom := minimizingPosition_smoothDomain (t:=t) hql hqu
  apply contDiffAt_of_unique_root (hdom.joint_contDiffAt t).2.1
    (jointPosition_hasFDerivAt hdom t)
    (ne_of_gt (hdom.positionSecond_pos hc hs.le (trig_unit t)))
    (W := Ioo (87/100) (11/10)) isOpen_Ioo hm.1 (minimizingPosition_root hql hqu ht)
  filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
  intro v hv hroot
  obtain ⟨hcx,hsx,htx⟩ := tiltInterval_bounds hx
  have hv' : v∈positionWindow := ⟨hv.1.le,hv.2.le⟩
  have hdomv := (window_bounds hql hqu hv').smoothDomain (by linarith)
  have hdv := position_deriv (c:=Real.cos x) (s:=Real.sin x)
    hdomv.r_pos hdomv.U_pos hdomv.Y_pos hdomv.w_pos
  have hz : 2*positionHalf q (Real.cos x) (Real.sin x) v=0 := hroot
  rw [hz] at hdv
  exact (windowMinimizer_eq_of_stationary hql hqu hcx hsx.le (trig_unit x) htx.le
    hdomv.toDomain hdv).symm

theorem minimizingPosition_hasDerivAt {q t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (ht : t∈tiltInterval) :
    HasDerivAt (minimizingPosition q)
      (-mixedSecond q (Real.cos t) (Real.sin t) (minimizingPosition q t)/
        positionSecond q (Real.cos t) (Real.sin t) (minimizingPosition q t)) t := by
  obtain ⟨hc,hs,htan⟩ := tiltInterval_bounds ht
  have hdom := minimizingPosition_smoothDomain (t:=t) hql hqu
  apply implicit_root_derivative
    ((minimizingPosition_contDiffAt hql hqu ht).differentiableAt (by norm_num))
    (jointPosition_hasFDerivAt hdom t)
    (ne_of_gt (hdom.positionSecond_pos hc hs.le (trig_unit t)))
  filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
  exact minimizingPosition_root hql hqu hx

theorem positionEnvelope_hasDerivAt {q t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (ht : t∈tiltInterval) :
    HasDerivAt (positionEnvelope q)
      (tiltFirst q (Real.cos t) (Real.sin t) (minimizingPosition q t)) t := by
  have hdom := minimizingPosition_smoothDomain (t:=t) hql hqu
  have hF := jointDefect_hasFDerivAt hdom t
  have hzero := minimizingPosition_root hql hqu ht
  change 2*positionHalf q (Real.cos t) (Real.sin t) (minimizingPosition q t)=0 at hzero
  rw [hzero] at hF
  have hh := envelope_first_derivative (minimizingPosition_hasDerivAt hql hqu ht) hF
  convert hh using 1
  funext x
  exact positionEnvelope_eq q x

theorem positionEnvelope_second_derivative {q t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (ht : t∈tiltInterval) :
    HasDerivAt (deriv (positionEnvelope q))
      (tiltSecond q (Real.cos t) (Real.sin t) (minimizingPosition q t)-
        mixedSecond q (Real.cos t) (Real.sin t) (minimizingPosition q t)^2/
          positionSecond q (Real.cos t) (Real.sin t) (minimizingPosition q t)) t := by
  have hdom := minimizingPosition_smoothDomain (t:=t) hql hqu
  have hh := envelope_tilt_derivative (minimizingPosition_hasDerivAt hql hqu ht)
    (jointTilt_hasFDerivAt hdom t)
  apply hh.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
  exact (positionEnvelope_hasDerivAt hql hqu hx).deriv

/-- Every critical tilt is a strict local minimum of the actual
position-minimized defect. There is no feasibility or defect-sign input. -/
theorem positionEnvelope_critical_strictMinimum {q t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (ht : t∈tiltInterval)
    (hzero : deriv (positionEnvelope q) t=0) :
    StrictMinimum (positionEnvelope q) t := by
  obtain ⟨hc,hs,htan⟩ := tiltInterval_bounds ht
  have hgrad := (positionEnvelope_hasDerivAt hql hqu ht).deriv
  have htilt : tiltFirst q (Real.cos t) (Real.sin t) (minimizingPosition q t)=0 := by
    linarith
  have hcritical := windowMinimizer_isStripCritical hql hqu hc hs.le (trig_unit t) htan.le htilt
  have hdom := minimizingPosition_smoothDomain (t:=t) hql hqu
  have hdet := hcritical.hessian_pos
  dsimp only [hessianDeterminant] at hdet
  have hschur := schur_positive (hdom.positionSecond_pos hc hs.le (trig_unit t)) hdet
  apply strictMinimum_of_positive_second_derivative
    (a:=0) (b:=Real.arctan (1/5)) (positionEnvelope_continuous q).continuousOn
    (fun x hx => (positionEnvelope_hasDerivAt hql hqu hx).differentiableAt.differentiableWithinAt)
    ht hzero (positionEnvelope_second_derivative hql hqu ht) hschur

theorem positionEnvelope_critical_unique {q t v : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (ht : t∈tiltInterval) (hv : v∈tiltInterval)
    (hdt : deriv (positionEnvelope q) t=0) (hdv : deriv (positionEnvelope q) v=0) : t=v :=
  critical_unique_of_strict_minimum (positionEnvelope_continuous q).continuousOn
    (fun x hx hz => positionEnvelope_critical_strictMinimum hql hqu hx hz) ht hv hdt hdv

/-- The unique interior critical point minimizes over the entire closed
tilt interval, including both endpoints. -/
theorem positionEnvelope_critical_global_minimum {q t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (ht : t∈tiltInterval)
    (hdt : deriv (positionEnvelope q) t=0) :
    ∀ v∈Icc 0 (Real.arctan (1/5)), positionEnvelope q t≤positionEnvelope q v :=
  critical_is_global_minimum (positionEnvelope_continuous q).continuousOn
    (fun x hx hz => positionEnvelope_critical_strictMinimum hql hqu hx hz) ht hdt

end SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry
