module

public import SquaresInCircles.Eight.TableFree.SignedOppositeHardPolynomials

/-!
# The complete free signed opposite-angle envelope

Uncompiled source draft.  Rotating around an explicit affine comparison
angle leaves one residual completed square.  The bounds are uniform over
the entire opposite-angle interval, so the opposite tangent may have
either sign.  The larger middle tangent cannot support a wrong weak
intermediate sign once the original outer budget is imposed.

This file proves the local scalar inequality directly from the two
actual circle inequalities and the two actual hard contacts.  It uses
neither a chosen maximizer nor an assumed curvature or endpoint result.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SignedOppositeHardEnvelope
open EndpointRotationPenalty

def referenceU (x : ℝ) : ℝ :=
  (rightRadius x-1)*Real.sin (referenceAngle x)+rightY x*Real.cos (referenceAngle x)

def referenceV (x : ℝ) : ℝ :=
  (rightRadius x-1)*Real.cos (referenceAngle x)-rightY x*Real.sin (referenceAngle x)

def rightFunction (x v : ℝ) : ℝ :=
  (rightRadius x-1)*Real.cos v-rightY x*Real.sin v+charge*v

theorem rotation_identity (P Y u d : ℝ) :
    P*Real.cos (u+d)-Y*Real.sin (u+d)=
      (P*Real.cos u-Y*Real.sin u)*Real.cos d-
        (P*Real.sin u+Y*Real.cos u)*Real.sin d := by
  rw [Real.cos_add,Real.sin_add]
  ring

private theorem signed_cos_upper {d : ℝ} :
    Real.cos d≤1-d^2/2+d^4/24 := by
  by_cases hd : 0≤d
  · exact cos_upper_four hd
  · have hh := cos_upper_four (show 0≤-d by linarith)
    rw [Real.cos_neg] at hh
    nlinarith

/-- A full-interval rotation estimate.  On the large tangent range the
positive displacement is at most one quarter; negative displacements
already have the favorable sine sign. -/
theorem rotation_upper {U V d η : ℝ}
    (hU : U∈Icc 0 (11/10 : ℝ))
    (hV : (2/5 : ℝ)≤V ∨ ((3/10 : ℝ)≤V ∧ d≤1/4))
    (hd : d∈Icc (-frameCap) frameCap)
    (hη : |charge-U|≤η) :
    V*Real.cos d-U*Real.sin d+charge*d≤V+4*η^2 := by
  have hdabs : |d|≤frameCap := abs_le.mpr hd
  have h2 : d^2≤49/100 := by
    have hh := pow_le_pow_left₀ (abs_nonneg d) hdabs 2
    simpa [frameCap,sq_abs] using hh
  have h4 : d^4≤(49/100 : ℝ)*d^2 := by
    nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg d)]
  have hcos := signed_cos_upper (d := d)
  have hcos0 : Real.cos d-1≤0 := sub_nonpos.mpr (Real.cos_le_one d)
  have hparabolic : V*Real.cos d-U*Real.sin d+charge*d≤
      V+(charge-U)*d-d^2/16 := by
    by_cases hd0 : 0≤d
    · have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hd0) hU.1
      have hU3 := mul_le_mul_of_nonneg_right hU.2 (pow_nonneg hd0 3)
      rcases hV with hV | ⟨hV,hdshort⟩
      · have hcV := mul_le_mul_of_nonpos_right hV hcos0
        have hc := mul_le_mul_of_nonneg_left hcos (by norm_num : (0:ℝ)≤2/5)
        have h3 : d^3≤(7/10 : ℝ)*d^2 := by
          have hh := mul_le_mul_of_nonneg_right hd.2 (sq_nonneg d)
          dsimp [frameCap] at hh
          nlinarith
        nlinarith [sq_nonneg d]
      · have hcV := mul_le_mul_of_nonpos_right hV hcos0
        have hc := mul_le_mul_of_nonneg_left hcos (by norm_num : (0:ℝ)≤3/10)
        have h3 : d^3≤(1/4 : ℝ)*d^2 := by
          nlinarith [mul_le_mul_of_nonneg_right hdshort (sq_nonneg d)]
        nlinarith [sq_nonneg d]
    · have hs0 : d≤Real.sin d := by
        have hh := Real.sin_le (show 0≤-d by linarith)
        rw [Real.sin_neg] at hh
        linarith
      have hs := mul_le_mul_of_nonneg_left hs0 hU.1
      have hV0 : (3/10 : ℝ)≤V := by
        rcases hV with h | h
        · linarith
        · exact h.1
      have hcV := mul_le_mul_of_nonpos_right hV0 hcos0
      have hc := mul_le_mul_of_nonneg_left hcos (by norm_num : (0:ℝ)≤3/10)
      nlinarith [sq_nonneg d]
  have hη2 : (charge-U)^2≤η^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (charge-U)) hη 2
  nlinarith [sq_nonneg (d/4-2*(charge-U))]

theorem reference_taylor {x η : ℝ}
    (hR : 1≤rightRadius x) (hY : 0≤rightY x) (hu : 0≤referenceAngle x) :
    lowerU x≤referenceU x ∧ referenceU x≤upperU x ∧
      lowerV x≤referenceV x ∧
      referenceV x+charge*referenceAngle x+4*η^2≤upperValue x η := by
  have hP : 0≤rightRadius x-1 := by linarith
  have hsL := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hu) hP
  have hcL := mul_le_mul_of_nonneg_left
    (Real.one_sub_sq_div_two_le_cos (referenceAngle x)) hY
  have hsU := mul_le_mul_of_nonneg_left (sin_upper_five hu) hP
  have hcU := mul_le_mul_of_nonneg_left (cos_upper_four hu) hY
  have hvcL := mul_le_mul_of_nonneg_left
    (Real.one_sub_sq_div_two_le_cos (referenceAngle x)) hP
  have hvsU := mul_le_mul_of_nonneg_left (Real.sin_le hu) hY
  have hvcU := mul_le_mul_of_nonneg_left (cos_upper_four hu) hP
  have hvsL := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hu) hY
  dsimp [lowerU,upperU,lowerV,referenceU,referenceV,upperValue]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem right_function_upper {x η v : ℝ}
    (hU : referenceU x∈Icc 0 (11/10 : ℝ))
    (hV : (2/5 : ℝ)≤referenceV x ∨
      ((3/10 : ℝ)≤referenceV x ∧ v-referenceAngle x≤1/4))
    (hd : v-referenceAngle x∈Icc (-frameCap) frameCap)
    (hη : |charge-referenceU x|≤η) :
    rightFunction x v≤referenceV x+charge*referenceAngle x+4*η^2 := by
  have hh := rotation_upper hU hV hd hη
  have hid := rotation_identity (rightRadius x-1) (rightY x)
    (referenceAngle x) (v-referenceAngle x)
  rw [show referenceAngle x+(v-referenceAngle x)=v by ring] at hid
  change (rightRadius x-1)*Real.cos v-rightY x*Real.sin v=
    referenceV x*Real.cos (v-referenceAngle x)-
      referenceU x*Real.sin (v-referenceAngle x) at hid
  dsimp [rightFunction]
  nlinarith

/-- The opposite tangent is unrestricted.  Every actual opposite angle
is paid by the same explicit comparison and residual square. -/
theorem opposite_low {d v : ℝ} (hd : d∈Icc 0 lowLength)
    (hv : v∈Icc 0 frameCap) :
    rightFunction (-d) v≤upperValue (-d) (lowTolerance d) := by
  obtain ⟨hR,hY,hu,hη⟩ := right_bounds_low hd
  obtain ⟨hL,hU,hV,hvalue⟩ := reference_taylor
    (η := lowTolerance d) (by linarith [hR.1]) (by linarith [hY.1]) hu.1
  have hres : |charge-referenceU (-d)|≤lowTolerance d := by
    rw [abs_le]
    constructor <;> linarith [low_U_lower hd,low_U_upper hd]
  have htransverse : referenceU (-d)∈Icc 0 (11/10 : ℝ) := by
    have hres' := abs_le.mp hres
    dsimp [charge] at hres'
    constructor <;> linarith [hres'.1,hres'.2,hη.2]
  have hlong : (2/5 : ℝ)≤referenceV (-d) := (low_V_lower hd).trans hV
  have hdisplacement : v-referenceAngle (-d)∈Icc (-frameCap) frameCap := by
    dsimp [frameCap] at *
    constructor <;> linarith [hv.1,hv.2,hu.1,hu.2]
  exact (right_function_upper htransverse (Or.inl hlong) hdisplacement hres).trans hvalue

theorem opposite_high {d v : ℝ} (hd : d∈Icc 0 highLength)
    (hv : v∈Icc 0 frameCap) :
    rightFunction d v≤upperValue d (highTolerance d) := by
  obtain ⟨hR,hY,hu,hη⟩ := right_bounds_high hd
  obtain ⟨hL,hU,hV,hvalue⟩ := reference_taylor
    (η := highTolerance d) (by linarith [hR.1]) (by linarith [hY.1])
    (by linarith [hu.1])
  have hres : |charge-referenceU d|≤highTolerance d := by
    rw [abs_le]
    constructor <;> linarith [high_U_lower hd,high_U_upper hd]
  have htransverse : referenceU d∈Icc 0 (11/10 : ℝ) := by
    have hres' := abs_le.mp hres
    dsimp [charge] at hres'
    constructor <;> linarith [hres'.1,hres'.2,hη.2]
  have hlong : (3/10 : ℝ)≤referenceV d := (high_V_lower hd).trans hV
  have hshort : v-referenceAngle d≤1/4 := by
    dsimp [frameCap] at hv
    linarith [hv.2,hu.1]
  have hdisplacement : v-referenceAngle d∈Icc (-frameCap) frameCap := by
    dsimp [frameCap] at *
    constructor <;> linarith [hv.1,hv.2,hu.1,hu.2]
  exact (right_function_upper htransverse (Or.inr ⟨hlong,hshort⟩)
    hdisplacement hres).trans hvalue

theorem clipped_tail {U d : ℝ} (hU : U∈Icc charge (3/2 : ℝ))
    (hd : d∈Icc 0 frameCap) :
    (1/2)*Real.cos d-U*Real.sin d+charge*d≤1/2 := by
  have hU0 : 0≤U := by dsimp [charge] at hU; linarith [hU.1]
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  have h3 := mul_le_mul_of_nonneg_right hd.2 (sq_nonneg d)
  have h4 := mul_le_mul_of_nonneg_right h2 (sq_nonneg d)
  have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hd.1) hU0
  have hUsmall := mul_le_mul_of_nonneg_right hU.2 (pow_nonneg hd.1 3)
  have hUlarge := mul_le_mul_of_nonneg_right hU.1 hd.1
  have hc := cos_upper_four hd.1
  dsimp [frameCap] at h2 h3 h4
  nlinarith [sq_nonneg d]

/-- The clipped left contribution is bounded without defining its
inverse contact angle.  This includes both sides of that contact. -/
theorem left_clipped {a g d z : ℝ} (hd : d∈Icc 0 lowLength)
    (hA : (a+1/2)^2+(pivot+1/2-d)^2≤qCap)
    (hz : z∈Icc 0 frameCap) (hg : g≤0)
    (hGA : g+1/2≤(a-1/2)*Real.cos z-(pivot+1/2-d)*Real.sin z) :
    g+charge*z≤charge*leftAngle d := by
  have hp : 0<charge := by norm_num [charge]
  by_cases hzlow : z≤leftAngle d
  · nlinarith [mul_le_mul_of_nonneg_left hzlow hp.le]
  · obtain ⟨hR,hu,hY⟩ := left_bounds hd
    have har : a+1/2≤leftRadius d := by
      have hs := left_square_reserve hd
      nlinarith [hR.1]
    have hzcos : 0≤Real.cos z := by linarith [(transport_trig hz).1]
    have hcap := mul_le_mul_of_nonneg_right
      (show a-1/2≤leftRadius d-1 by linarith) hzcos
    have hδ : z-leftAngle d∈Icc 0 frameCap :=
      ⟨by linarith,by linarith [hz.2,hu.1]⟩
    have hδcos : 0≤Real.cos (z-leftAngle d) := by
      linarith [(transport_trig hδ).1]
    have hcontact := mul_le_mul_of_nonneg_right (left_angle_contact hd) hδcos
    have hU := left_angle_transverse hd
    have htail := clipped_tail hU hδ
    have hrot := rotation_identity (leftRadius d-1) (pivot+1/2-d)
      (leftAngle d) (z-leftAngle d)
    rw [show leftAngle d+(z-leftAngle d)=z by ring] at hrot
    nlinarith

theorem left_high {a g d z : ℝ} (hd : d∈Icc 0 highLength)
    (ha : 1/2<a) (hA : (a+1/2)^2+(pivot+1/2+d)^2≤qCap)
    (hz : z∈Icc 0 frameCap)
    (hGA : g+1/2≤(a-1/2)*Real.cos z-(pivot+1/2+d)*Real.sin z) :
    g+charge*z≤ -(43/50)*d := by
  have hR : 0<3/2-(43/50)*d := by
    dsimp [highLength] at hd
    linarith [hd.2]
  have haR : a+1/2≤3/2-(43/50)*d := by
    nlinarith [high_left_square hd.1]
  have hY : 0≤pivot+1/2+d := by dsimp [pivot]; linarith [hd.1]
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hz3 := mul_le_mul_of_nonneg_right hz2 hz.1
  have hsin : (9/10)*z≤Real.sin z := by
    dsimp [frameCap] at hz3
    nlinarith [Real.sin_ge_sub_cube hz.1]
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one z)
    (show 0≤a-1/2 by linarith)
  have hs := mul_le_mul_of_nonneg_left hsin hY
  have hcoefficient : charge≤(9/10)*(pivot+1/2+d) := by
    dsimp [charge,pivot]
    linarith [hd.1]
  have hm := mul_le_mul_of_nonneg_right hcoefficient hz.1
  nlinarith

/-- Complete local signed envelope at the larger middle tangent.
There is no sign premise on t and no envelope premise. -/
theorem actual_middle_wrong_bound {aA aB b g t z v : ℝ}
    (hb : b∈Icc (1/2 : ℝ) (9/10)) (haA : 1/2<aA)
    (hA : (aA+1/2)^2+(b+1/2)^2≤qCap)
    (hB : (aB+1/2)^2+(3/2-b)^2≤qCap)
    (hz : z∈Icc 0 frameCap) (hv : v∈Icc 0 frameCap) (hg : g≤0)
    (hGA : g+1/2≤(aA-1/2)*Real.cos z-(b+1/2)*Real.sin z)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(3/2-b)*Real.sin v) :
    g+t+charge*(z+v)<83/200 := by
  have hcos : 0≤Real.cos v := by linarith [(transport_trig hv).1]
  by_cases hbp : b≤pivot
  · let d := pivot-b
    have hd : d∈Icc 0 lowLength := low_domain ⟨hb.1,hbp⟩
    have hyA : b+1/2=pivot+1/2-d := by dsimp [d]; ring
    have hyB : 3/2-b=rightY (-d) := by dsimp [rightY,d,pivot]; ring
    have haB : aB+1/2≤rightRadius (-d) := by
      have hsq := right_square_low hd
      rw [←hyB] at hsq
      nlinarith [(right_bounds_low hd).1.1]
    have hc := mul_le_mul_of_nonneg_right
      (show aB-1/2≤rightRadius (-d)-1 by linarith) hcos
    have hleft := left_clipped hd (by simpa only [←hyA] using hA) hz hg
      (by simpa only [←hyA] using hGA)
    have hright := opposite_low hd hv
    have hpoly := objectiveLow_lt hd
    rw [hyB] at hBT
    dsimp [rightFunction] at hright
    dsimp [objectiveLow] at hpoly
    nlinarith
  · let d := b-pivot
    have hd : d∈Icc 0 highLength := high_domain ⟨by linarith,hb.2⟩
    have hyA : b+1/2=pivot+1/2+d := by dsimp [d]; ring
    have hyB : 3/2-b=rightY d := by dsimp [rightY,d,pivot]; ring
    have haB : aB+1/2≤rightRadius d := by
      have hsq := right_square_high hd
      rw [←hyB] at hsq
      nlinarith [(right_bounds_high hd).1.1]
    have hc := mul_le_mul_of_nonneg_right
      (show aB-1/2≤rightRadius d-1 by linarith) hcos
    have hleft := left_high hd haA (by simpa only [←hyA] using hA) hz
      (by simpa only [←hyA] using hGA)
    have hright := opposite_high hd hv
    have hpoly := objectiveHigh_lt hd
    rw [hyB] at hBT
    dsimp [rightFunction] at hright
    dsimp [objectiveHigh] at hpoly
    nlinarith

end SquaresInCircles.Eight.TableFree.SignedOppositeHardEnvelope
