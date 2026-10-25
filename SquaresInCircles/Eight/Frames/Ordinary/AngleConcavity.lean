module

public import SquaresInCircles.Eight.Frames.Ordinary.CurvatureBounds

/-!
# Eight squares: concavity on the whole ordinary-angle domain

The radius and both coefficients remain variable. Every point of the
full square `[0,7/10]²` is covered, with explicit negative curvature
reserves. In particular, opposite signed errors in one block are allowed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OrdinaryAngleConcavity
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds

def U (R p q t : ℝ) : ℝ :=
  p*(PositiveAngularEnvelope.phi t-1)-R*(pairNorm p q t-pairNorm p q 0)

def V (R p q t : ℝ) : ℝ :=
  q*(Real.cos t-1)-R*(pairNorm p q (-t)-pairNorm p q 0)

def mixedBlock (R p q P N : ℝ) : ℝ :=
  p*(PositiveAngularEnvelope.phi P-1)+q*(Real.cos N-1)-
    R*(pairNorm p q (P-N)-pairNorm p q 0)

def mixedPDerivative (R p q P N : ℝ) : ℝ :=
  p*(Real.cos P-Real.sin P)-R*normD1 p q (P-N)

def mixedNDerivative (R p q P N : ℝ) : ℝ :=
  -q*Real.sin N+R*normD1 p q (P-N)

@[simp] theorem U_zero (R p q : ℝ) : U R p q 0=0 := by simp [U]
@[simp] theorem V_zero (R p q : ℝ) : V R p q 0=0 := by simp [V]

@[simp] theorem mixedBlock_zero_right (R p q t : ℝ) :
    mixedBlock R p q t 0=U R p q t := by simp [mixedBlock,U]

@[simp] theorem mixedBlock_zero_left (R p q t : ℝ) :
    mixedBlock R p q 0 t=V R p q t := by simp [mixedBlock,V]

theorem phi_cap_lower : (1409/1000 : ℝ)<PositiveAngularEnvelope.phi frameCap := by
  have hs := sin_lower_seven (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hc := cos_lower_six (show (0:ℝ)≤frameCap by norm_num [frameCap])
  norm_num [frameCap] at hs hc
  dsimp [PositiveAngularEnvelope.phi,frameCap]
  linarith

theorem mixed_argument_bound {P N : ℝ}
    (hP : P∈Icc 0 frameCap) (hN : N∈Icc 0 frameCap) : |P-N|≤frameCap := by
  exact abs_le.mpr ⟨by linarith [hP.1,hN.2],by linarith [hP.2,hN.1]⟩

theorem mixedP_hasDerivAt {R p q P N : ℝ} (hp : 0<p) (hq : 0<q)
    (hP : P∈Icc 0 frameCap) (hN : N∈Icc 0 frameCap) :
    HasDerivAt (fun x => mixedBlock R p q x N) (mixedPDerivative R p q P N) P := by
  have hnorm := (pairNorm_hasDerivAt hp hq (mixed_argument_bound hP hN)).comp P
    ((hasDerivAt_id P).sub_const N)
  have hphi := (Real.hasDerivAt_cos P).add (Real.hasDerivAt_sin P)
  have hraw := (((hphi.sub_const 1).const_mul p).add_const
    (q*(Real.cos N-1))).sub ((hnorm.sub_const (pairNorm p q 0)).const_mul R)
  convert hraw using 1
  · rfl
  · dsimp [mixedPDerivative]
    ring

theorem mixedPDerivative_hasDerivAt {R p q P N : ℝ} (hp : 0<p) (hq : 0<q)
    (hP : P∈Icc 0 frameCap) (hN : N∈Icc 0 frameCap) :
    HasDerivAt (fun x => mixedPDerivative R p q x N)
      (curvature R p q (P-N)-p*PositiveAngularEnvelope.phi P) P := by
  have hnorm := (normD1_hasDerivAt hp hq (mixed_argument_bound hP hN)).comp P
    ((hasDerivAt_id P).sub_const N)
  have hraw := (((Real.hasDerivAt_cos P).sub (Real.hasDerivAt_sin P)).const_mul p).sub
    (hnorm.const_mul R)
  convert hraw using 1
  · rfl
  · dsimp [curvature,PositiveAngularEnvelope.phi]
    ring

theorem mixedN_hasDerivAt {R p q P N : ℝ} (hp : 0<p) (hq : 0<q)
    (hP : P∈Icc 0 frameCap) (hN : N∈Icc 0 frameCap) :
    HasDerivAt (mixedBlock R p q P) (mixedNDerivative R p q P N) N := by
  have hnorm := (pairNorm_hasDerivAt hp hq (mixed_argument_bound hP hN)).comp N
    ((hasDerivAt_const N P).sub (hasDerivAt_id N))
  have hraw := ((hasDerivAt_const N (p*(PositiveAngularEnvelope.phi P-1))).add
    (((Real.hasDerivAt_cos N).sub_const 1).const_mul q)).sub
      ((hnorm.sub_const (pairNorm p q 0)).const_mul R)
  convert hraw using 1
  · rfl
  · dsimp [mixedNDerivative]
    ring

theorem mixedNDerivative_hasDerivAt {R p q P N : ℝ} (hp : 0<p) (hq : 0<q)
    (hP : P∈Icc 0 frameCap) (hN : N∈Icc 0 frameCap) :
    HasDerivAt (mixedNDerivative R p q P)
      (curvature R p q (P-N)-q*Real.cos N) N := by
  have hnorm := (normD1_hasDerivAt hp hq (mixed_argument_bound hP hN)).comp N
    ((hasDerivAt_const N P).sub (hasDerivAt_id N))
  have hraw := ((Real.hasDerivAt_sin N).const_mul (-q)).add (hnorm.const_mul R)
  convert hraw using 1
  · rfl
  · dsimp [curvature]
    ring

/-- The positive-coordinate curvature has a uniform strict reserve even
at the largest admissible coefficient ratio and angle. -/
theorem mixedP_second_lt {R p q P N : ℝ} (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hP : P∈Icc 0 frameCap) (hN : N∈Icc 0 frameCap) :
    curvature R p q (P-N)-p*PositiveAngularEnvelope.phi P< -(23/10000)*p := by
  have hq : 0<q := hp.trans_le hpq
  obtain ⟨h₀p,h₁p,h₀q,hsumq⟩ := curvature_constant_bounds hR hQ hp hpq hqp
  have hφ := mul_lt_mul_of_pos_left phi_cap_lower hp
  have h₁h := mul_lt_mul_of_pos_right h₁p
    (show 0<frameCap by norm_num [frameCap])
  have hcomp : curvatureZero R p q+(23/10000)*p<
      -curvatureSlope R p q*P+p*Real.sin P+p*Real.cos P := by
    apply trig_concave_gt hp.le hp.le (by norm_num)
      (by dsimp [frameCap]; linarith [Real.pi_gt_three]) hP
    · norm_num
      linarith
    · dsimp [PositiveAngularEnvelope.phi,frameCap] at hφ h₁h ⊢
      linarith
  have hmono := curvature_monotone hR hp hq
    (abs_le.mp (mixed_argument_bound hP hN))
    (show P∈Icc (-frameCap) frameCap by
      exact ⟨by dsimp [frameCap]; linarith [hP.1],hP.2⟩)
    (show P-N≤P by linarith [hN.1])
  have hupper := curvature_positive_upper hR hp hpq hqp hP
  dsimp [PositiveAngularEnvelope.phi]
  linarith

/-- Both signs of `P-N` are included. The comparison on `0≤N≤P`
is a concave trigonometric function with positive endpoint reserves. -/
theorem mixedN_second_lt {R p q P N : ℝ} (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hP : P∈Icc 0 frameCap) (hN : N∈Icc 0 frameCap) :
    curvature R p q (P-N)-q*Real.cos N< -(11/200)*q := by
  have hq : 0<q := hp.trans_le hpq
  obtain ⟨h₀p,h₁p,h₀q,hsumq⟩ := curvature_constant_bounds hR hQ hp hpq hqp
  have hcosN := mul_lt_mul_of_pos_left (transport_trig hN).1 hq
  by_cases hNP : P≤N
  · have hu := curvature_negative_upper hR hp hq
      (show P-N∈Icc (-frameCap) 0 by
        constructor <;> linarith [hP.1,hN.2])
    linarith
  · have hNP' : N≤P := (lt_of_not_ge hNP).le
    have hslope := curvatureSlope_nonneg hR hp hq
    have hscaled := mul_le_mul_of_nonneg_left hP.2 hslope
    have hcosP := mul_lt_mul_of_pos_left (transport_trig hP).1 hq
    have hcomp : curvatureZero R p q+curvatureSlope R p q*P+(11/200)*q<
        curvatureSlope R p q*N+0*Real.sin N+q*Real.cos N := by
      apply trig_concave_gt (by norm_num) hq.le (by norm_num)
        (by dsimp [frameCap] at hP; linarith [hP.2,Real.pi_gt_three])
        ⟨hN.1,hNP'⟩
      · norm_num
        simp only [frameCap] at hsumq hscaled
        linarith
      · norm_num
        linarith
    have hu := curvature_positive_upper hR hp hpq hqp
      (show P-N∈Icc 0 frameCap by
        constructor <;> linarith [hNP',hP.2,hN.1])
    linarith

theorem mixedBlock_concave_positive {R p q N : ℝ} (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hN : N∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun P => mixedBlock R p q P N) := by
  apply concave_of_deriv2
    (fun P hP => mixedP_hasDerivAt hp (hp.trans_le hpq) hP hN)
    (fun P hP => mixedPDerivative_hasDerivAt hp (hp.trans_le hpq) hP hN)
  intro P hP
  have h := mixedP_second_lt hR hQ hp hpq hqp hP hN
  linarith

theorem mixedBlock_concave_negative {R p q P : ℝ} (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hP : P∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (mixedBlock R p q P) := by
  apply concave_of_deriv2
    (fun N hN => mixedN_hasDerivAt hp (hp.trans_le hpq) hP hN)
    (fun N hN => mixedNDerivative_hasDerivAt hp (hp.trans_le hpq) hP hN)
  intro N hN
  have h := mixedN_second_lt hR hQ hp hpq hqp hP hN
  linarith [hp.trans_le hpq]

theorem U_concave {R p q : ℝ} (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) :
    ConcaveOn ℝ (Icc 0 frameCap) (U R p q) := by
  simpa only [mixedBlock_zero_right] using mixedBlock_concave_positive hR hQ hp hpq hqp
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])

theorem V_concave {R p q : ℝ} (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) :
    ConcaveOn ℝ (Icc 0 frameCap) (V R p q) := by
  have h := mixedBlock_concave_negative hR hQ hp hpq hqp
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  change ConcaveOn ℝ (Icc 0 frameCap) (fun t => mixedBlock R p q 0 t) at h
  simpa only [mixedBlock_zero_left] using h

/-- Concentrating both signs in one block leaves the norm argument fixed;
the final positive-variation parameter is concave on its whole interval. -/
theorem sameBlockLine_concave {R p q z : ℝ}
    (hp : 0≤p) (hq : 0≤q) (hz : z∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-z))
      (fun P => mixedBlock R p q P (z+P)) := by
  let f (P : ℝ) := p*(PositiveAngularEnvelope.phi P-1)+q*(Real.cos (z+P)-1)-
    R*(pairNorm p q (-z)-pairNorm p q 0)
  have he (P : ℝ) : mixedBlock R p q P (z+P)=f P := by
    dsimp [mixedBlock,f]
    rw [show P-(z+P)= -z by ring]
  simp_rw [he]
  apply concave_of_deriv2
    (f' := fun P => p*(Real.cos P-Real.sin P)-q*Real.sin (z+P))
    (f'' := fun P => -p*PositiveAngularEnvelope.phi P-q*Real.cos (z+P))
  · intro P hP
    have hrot := (Real.hasDerivAt_cos (z+P)).comp P ((hasDerivAt_id P).const_add z)
    have hraw := (((((Real.hasDerivAt_cos P).add (Real.hasDerivAt_sin P)).sub_const 1).const_mul p).add
      ((hrot.sub_const 1).const_mul q)).sub_const
        (R*(pairNorm p q (-z)-pairNorm p q 0))
    convert hraw using 1
    · rfl
    · ring
  · intro P hP
    have hrot := (Real.hasDerivAt_sin (z+P)).comp P ((hasDerivAt_id P).const_add z)
    convert (((Real.hasDerivAt_cos P).sub (Real.hasDerivAt_sin P)).const_mul p).sub
      (hrot.const_mul q) using 1
    · rfl
    · dsimp [PositiveAngularEnvelope.phi]
      ring
  · intro P hP
    have hPP : P∈Icc 0 frameCap := ⟨hP.1,by linarith [hP.2,hz.1]⟩
    have hPN : z+P∈Icc 0 frameCap := ⟨by linarith [hP.1,hz.1],by linarith [hP.2]⟩
    have hc := (transport_trig hPP).1
    have hs := (transport_trig hPP).2.2.1
    have hc' := (transport_trig hPN).1
    have hφ : 0≤PositiveAngularEnvelope.phi P := by dsimp [PositiveAngularEnvelope.phi]; linarith
    have hprod := mul_nonneg hp hφ
    have hprod' := mul_nonneg hq (show 0≤Real.cos (z+P) by linarith)
    linarith

end SquaresInCircles.Eight.OrdinaryAngleConcavity
