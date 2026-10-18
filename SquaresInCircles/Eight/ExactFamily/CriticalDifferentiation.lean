module

public import SquaresInCircles.Eight.ExactFamily.CriticalHessian

/-!
# Derivatives underlying the global critical-Hessian estimate

Uncompiled draft.  The first and second position derivatives and the
mixed position/angle derivative below differentiate the actual nested
circle formulas.  The final theorem combines these identities with the
strict determinant reserve, including critical points of positive defect.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

theorem CriticalStrip.radical_derivatives {q u : ℝ} (h : CriticalStrip q u) :
    HasDerivAt (lowerRight q) (-u/lowerRight q u) u ∧
    HasDerivAt (topRight q) ((2-u)/topRight q u) u ∧
    HasDerivAt (topLeft q) (-((2-u)/topRight q u)) u ∧
    HasDerivAt (topHeight q) (slopeRatio q u) u ∧
    HasDerivAt (lowerHeight q) (-slopeRatio q u) u ∧
    HasDerivAt (lowerLeft q) (lowerHeight q u*slopeRatio q u/lowerLeft q u) u := by
  have hb := h.bounds
  have hr : 0<lowerRight q u := by linarith [hb.r_lower]
  have hU : 0<topRight q u := by linarith [hb.U_lower]
  have hY : 0<topHeight q u := by linarith [hb.Y_lower]
  have hw : 0<lowerLeft q u := by linarith [hb.w_lower]
  have dr : HasDerivAt (lowerRight q) (-u/lowerRight q u) u := by
    simpa [lowerRight] using upper_curve_deriv (hasDerivAt_id u) hr
  have dU : HasDerivAt (topRight q) ((2-u)/topRight q u) u := by
    have hd := upper_curve_deriv ((hasDerivAt_const u (2:ℝ)).sub (hasDerivAt_id u)) hU
    convert hd using 1 <;> dsimp [topRight] <;> ring
  have dV : HasDerivAt (topLeft q) (-((2-u)/topRight q u)) u := by
    simpa [topLeft] using (hasDerivAt_const u (3:ℝ)).sub dU
  have dY : HasDerivAt (topHeight q) (slopeRatio q u) u := by
    have hd := upper_curve_deriv dV hY
    convert hd using 1
    · rfl
    · dsimp [slopeRatio,topHeight]
      field_simp [ne_of_gt hU,ne_of_gt hY]
      ring
  have dv : HasDerivAt (lowerHeight q) (-slopeRatio q u) u := by
    simpa [lowerHeight] using (hasDerivAt_const u (2:ℝ)).sub dY
  have dw : HasDerivAt (lowerLeft q) (lowerHeight q u*slopeRatio q u/lowerLeft q u) u := by
    have hd := upper_curve_deriv dv hw
    convert hd using 1 <;> dsimp [lowerLeft] <;> ring
  exact ⟨dr,dU,dV,dY,dv,dw⟩

theorem circle_ratio_derivative (A U V Y q : ℝ)
    (hA : A≠0) (hU : U≠0) (hV : V≠0) (hY : Y≠0)
    (hcircle₁ : U^2+A^2=q) (hcircle₂ : Y^2+V^2=q) :
    (((-1)*V+A*(-(A/U)))*(U*Y)-(A*V)*((A/U)*Y+U*(A*V/(U*Y))))/(U*Y)^2=
      -(A*V/(U*Y))*(q/(A*U^2)+(A*V/(U*Y))*q/(Y*V^2)) := by
  calc
    _ = -(U^2+A^2)*V/(Y*U^3)-(Y^2+V^2)*A^2/(U^2*Y^3) := by
      field_simp [hA,hU,hV,hY]
      ring
    _ = -q*V/(Y*U^3)-q*A^2/(U^2*Y^3) := by rw [hcircle₁,hcircle₂]
    _ = _ := by
      field_simp [hA,hU,hV,hY]
      ring

theorem slopeRatio_deriv {q u : ℝ} (h : CriticalStrip q u) :
    HasDerivAt (slopeRatio q) (-slopeRatio q u*curvatureRatio q u) u := by
  have hb := h.bounds
  obtain ⟨_,dU,dV,dY,_,_⟩ := h.radical_derivatives
  have hA : 0<2-u := by linarith [h.u_upper]
  have hU : 0<topRight q u := by linarith [hb.U_lower]
  have hV : 0<topLeft q u := by linarith [hb.V_lower]
  have hY : 0<topHeight q u := by linarith [hb.Y_lower]
  have dA := (hasDerivAt_const u (2:ℝ)).sub (hasDerivAt_id u)
  have hp := (dA.mul dV).div (dU.mul dY) (ne_of_gt (mul_pos hU hY))
  have hc₁ := upper_circle hb.domain.second_radicand
  have hc₂ := upper_circle hb.domain.third_radicand
  have he := circle_ratio_derivative (2-u) (topRight q u) (topLeft q u) (topHeight q u) q
    (ne_of_gt hA) (ne_of_gt hU) (ne_of_gt hV) (ne_of_gt hY) hc₁ hc₂
  convert hp using 1
  · rfl
  · simpa [slopeRatio,curvatureRatio] using he.symm

theorem rightRatio_deriv {q u : ℝ} (h : CriticalStrip q u) :
    HasDerivAt (fun v => v/lowerRight q v) (q/lowerRight q u^3) u := by
  have hb := h.bounds
  have dr := h.radical_derivatives.1
  have hr : 0<lowerRight q u := by linarith [hb.r_lower]
  have hd := (hasDerivAt_id u).div dr (ne_of_gt hr)
  have he : (1*lowerRight q u-u*(-u/lowerRight q u))/lowerRight q u^2=
      q/lowerRight q u^3 := by
    calc
      _ = (lowerRight q u^2+u^2)/lowerRight q u^3 := by
        field_simp [ne_of_gt hr]
        ring
      _ = _ := by rw [upper_circle hb.domain.first_radicand]
  simpa only [he] using hd

theorem lowerRatio_deriv {q u : ℝ} (h : CriticalStrip q u) :
    HasDerivAt (fun v => lowerHeight q v/lowerLeft q v)
      (-slopeRatio q u*q/lowerLeft q u^3) u := by
  have hb := h.bounds
  obtain ⟨_,_,_,_,dv,dw⟩ := h.radical_derivatives
  have hw : 0<lowerLeft q u := by linarith [hb.w_lower]
  have hd := dv.div dw (ne_of_gt hw)
  have he : ((-slopeRatio q u)*lowerLeft q u-
      lowerHeight q u*(lowerHeight q u*slopeRatio q u/lowerLeft q u))/lowerLeft q u^2=
      -slopeRatio q u*q/lowerLeft q u^3 := by
    calc
      _ = -slopeRatio q u*(lowerLeft q u^2+lowerHeight q u^2)/lowerLeft q u^3 := by
        field_simp [ne_of_gt hw]
        ring
      _ = _ := by rw [upper_circle hb.domain.fourth_radicand]
  simpa only [he] using hd

theorem positionA_deriv {q c s u : ℝ} (h : CriticalStrip q u) :
    HasDerivAt (positionA q c s) (rightSecond q c u) u := by
  have hd := (hasDerivAt_const u s).add ((rightRatio_deriv h).const_mul c)
  convert hd using 1 <;> dsimp [positionA,rightSecond] <;> ring

theorem positionb_deriv {q c s u : ℝ} (h : CriticalStrip q u) :
    HasDerivAt (positionb q c s) (-leftSecond q c s u) u := by
  have dB : HasDerivAt (positionB q c s) (-s*slopeRatio q u*q/lowerLeft q u^3) u := by
    have hd := (hasDerivAt_const u c).add ((lowerRatio_deriv h).const_mul s)
    convert hd using 1 <;> dsimp [positionB] <;> ring
  have hd := (slopeRatio_deriv h).mul dB
  convert hd using 1 <;> dsimp [positionb,leftSecond] <;> ring

theorem components_position_deriv {q c s u : ℝ} (h : CriticalStrip q u) :
    HasDerivAt (firstComponent q c s) (positionA q c s u) u ∧
    HasDerivAt (secondComponent q c s) (-positionb q c s u) u := by
  obtain ⟨dr,_,_,_,dv,dw⟩ := h.radical_derivatives
  have dk₁ := ((hasDerivAt_const u (2:ℝ)).sub ((dr.sub_const 1).const_mul c)).add
    ((hasDerivAt_id u).const_mul s)
  have dk₂ := ((hasDerivAt_const u (1:ℝ)).add (dv.const_mul c)).sub
    ((dw.sub_const 1).const_mul s)
  constructor
  · convert dk₁ using 1 <;> dsimp [firstComponent,positionA] <;> ring
  · convert dk₂ using 1 <;> dsimp [secondComponent,positionb,positionB] <;> ring

theorem position_second_deriv {q c s u : ℝ} (h : CriticalStrip q u) :
    HasDerivAt (fun v => 2*positionHalf q c s v) (positionSecond q c s u) u := by
  obtain ⟨dk₁,dk₂⟩ := components_position_deriv (c:=c) (s:=s) h
  have hd := ((dk₁.mul (positionA_deriv (c:=c) (s:=s) h)).sub
    (dk₂.mul (positionb_deriv (c:=c) (s:=s) h))).const_mul 2
  convert hd using 1 <;>
    dsimp [positionHalf,positionSecond,positionNorm,positionNormal,positionA,positionb,positionB] <;> ring

theorem positionA_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => positionA q (Real.cos x) (Real.sin x) u)
      (Real.cos t-Real.sin t*u/lowerRight q u) t := by
  have hd := (Real.hasDerivAt_sin t).add ((Real.hasDerivAt_cos t).mul_const (u/lowerRight q u))
  convert hd using 1 <;> dsimp [positionA] <;> ring

theorem positionb_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => positionb q (Real.cos x) (Real.sin x) u)
      (slopeRatio q u*(-Real.sin t+Real.cos t*lowerHeight q u/lowerLeft q u)) t := by
  have hd := ((Real.hasDerivAt_cos t).add
    ((Real.hasDerivAt_sin t).mul_const (lowerHeight q u/lowerLeft q u))).const_mul (slopeRatio q u)
  convert hd using 1 <;> dsimp [positionb,positionB] <;> ring

theorem mixed_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => 2*positionHalf q (Real.cos x) (Real.sin x) u)
      (mixedSecond q (Real.cos t) (Real.sin t) u) t := by
  have hd := (((firstComponent_angle_deriv q u t).mul (positionA_angle_deriv q u t)).sub
    ((secondComponent_angle_deriv q u t).mul (positionb_angle_deriv q u t))).const_mul 2
  convert hd using 1 <;>
    dsimp [positionHalf,mixedSecond,mixedNormal,positionA,positionb,positionB] <;> ring

theorem actual_critical_hessian {q u t : ℝ} (h : StripCritical q (Real.cos t) (Real.sin t) u) :
    HasDerivAt (defect q (Real.cos t) (Real.sin t)) 0 u ∧
    HasDerivAt (fun v => 2*positionHalf q (Real.cos t) (Real.sin t) v)
      (positionSecond q (Real.cos t) (Real.sin t) u) u ∧
    HasDerivAt (fun x => 2*positionHalf q (Real.cos x) (Real.sin x) u)
      (mixedSecond q (Real.cos t) (Real.sin t) u) t ∧
    HasDerivAt (fun x => tiltFirst q (Real.cos x) (Real.sin x) u)
      (tiltSecond q (Real.cos t) (Real.sin t) u) t ∧
    0<positionSecond q (Real.cos t) (Real.sin t) u ∧
    0<hessianDeterminant q (Real.cos t) (Real.sin t) u := by
  have hk := h.components_pos.1
  have hn := h.normalizedPosition_lower
  have hs : 0<positionNormal q (Real.cos t) (Real.sin t) u := by
    dsimp only [normalizedPosition] at hn
    rw [lt_div_iff₀ hk] at hn
    nlinarith
  have huu : 0<positionSecond q (Real.cos t) (Real.sin t) u := by
    dsimp [positionSecond,positionNorm]
    nlinarith [sq_nonneg (positionA q (Real.cos t) (Real.sin t) u),
      sq_nonneg (positionb q (Real.cos t) (Real.sin t) u)]
  exact ⟨h.position_derivative_zero,position_second_deriv h.strip,mixed_angle_deriv q u t,
    defect_angle_second_deriv q u t,huu,h.hessian_pos⟩

theorem coordinate_tiltFirst {d : Coordinates} (hd : d.IsChain) :
    tiltFirst d.q d.c d.s (-d.y)=d.tiltDerivative := by
  obtain ⟨hr,_,_,_,hv,hw⟩ := coordinate_values hd
  dsimp only [tiltFirst,firstComponent,secondComponent,firstTilt,secondTilt]
  rw [hr,hv,hw]
  dsimp [Coordinates.tiltDerivative,Coordinates.h₁,Coordinates.h₂]
  ring

/-- This instantiation uses the broad admissibility predicate.  It does
not call local-box membership or stationary root localization. -/
theorem stationary_isStripCritical {d : Coordinates} (hd : d.IsStationary) :
    StripCritical d.q d.c d.s (-d.y) := by
  have hu := stationary_coordinate_lower hd
  have hc : 0<d.c := halfAngleCos_pos (by rw [abs_lt]; constructor <;> linarith [hd.z_pos,hd.z_lt_one])
  have hs : 0 ≤ d.s := (halfAngleSin_pos hd.z_pos).le
  have ht : d.s/d.c ≤ 1/5 := by
    have hden : 0<1-d.z^2 := by nlinarith [hd.z_pos,hd.z_lt_one,sq_nonneg (1-d.z)]
    have he : d.s/d.c=2*d.z/(1-d.z^2) := by
      dsimp [Coordinates.c,Coordinates.s,halfAngleCos,halfAngleSin]
      field_simp [ne_of_gt (halfAngle_den_pos d.z),ne_of_gt hden]
      ring
    rw [he]
    exact hd.tilt_range.le
  refine ⟨⟨hd.q_lower,hd.q_upper,?_,by linarith [hd.y_lower]⟩,hc,hs,d.unit,ht,?_,?_⟩
  · simpa only [comparisonPosition] using hu.le
  · have hp := coordinate_positionHalf hd.toIsChain
    rw [hd.position_stationary] at hp
    linarith
  · rw [coordinate_tiltFirst hd.toIsChain]
    exact hd.tilt_stationary

end SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry
