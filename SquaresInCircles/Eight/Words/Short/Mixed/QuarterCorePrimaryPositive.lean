module

public import SquaresInCircles.Eight.Stationary.Envelope
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroAlignedL
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroPositiveJ
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroCycle
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterCorePrimaryNegative
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterCoreSecondaryNegative
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterCoreSecondaryPositive
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterSecondary
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterPrimaryReduction
public import SquaresInCircles.Eight.Words.Short.WordZero
public import SquaresInCircles.Eight.Owners.Stationary.PrimitiveForces
public import SquaresInCircles.Eight.Arithmetic.WholeIntervalPolynomial

/-!
# Eight squares: core-source primary contacts with positive outer target

The original primary separator excludes the lower angle half
and forces x > .4 on the upper half. The stated multiplier 1.6 gives
the exact outer axial support and the core-circle support. The resulting
single scalar decreases on the entire remaining interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.CorePrimaryPositive
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives Reference

def multiplier : ℝ := 8/5
def cap (x : ℝ) : ℝ := 1/12+(outerAxial-1/2)*Real.sin x-Real.cos x/2
def N (r : Row) : ℝ := Real.sqrt (multiplier^2+coG r^2)
def F (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2+x+coC r-coG r/2-N r/12-coP r*outerAxial+
    (4/5)*Real.cos x-multiplier*(outerAxial-1/2)*Real.sin x
def Fd (_r : Row) (x : ℝ) : ℝ :=
  1-(4/5)*Real.sin x-multiplier*(outerAxial-1/2)*Real.cos x

theorem sourceSign_negative {r : Row} (hr : sourcePositive r=false) : sourceSign r= -1 := by
  simp [sourceSign,WordProblems.sign,hr]

theorem lower_impossible (r : Row) (hτ : targetPositive r=true)
    {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) : ¬sourcePrimary r a b A B (angle false x) := by
  intro hm
  have hb := CoreAngleEndpoint.state_bounds hs
  have htr := positive_trig hx
  have hA : 0≤A := ht.1.trans ht.2.1
  have hAs := mul_nonneg hA htr.2.2.1
  have hBc := mul_nonneg ht.1 (show 0≤Real.cos x by linarith [htr.1])
  dsimp [sourcePrimary] at hm
  rw [angle_width false hx,angle_cos,angle_sin,targetSign_positive hτ] at hm
  dsimp [direction] at hm
  nlinarith

theorem necessary_cap (r : Row) (hτ : targetPositive r=true)
    {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b A B (angle true x)) : 0≤cap x := by
  have hb := CoreAngleEndpoint.state_bounds hs
  have htB := outer_bounds ht
  have htr := positive_trig hx
  have hAs := mul_le_mul_of_nonneg_right htB.2.1 htr.2.2.1
  have hBc := mul_nonneg ht.1 (show 0≤Real.cos x by linarith [htr.1])
  dsimp [sourcePrimary] at hm
  rw [angle_width true hx,angle_cos,angle_sin,targetSign_positive hτ] at hm
  dsimp [direction,cap] at *
  nlinarith

theorem cap_reference : cap (2/5)<0 := by
  let B := ((Interval.point (1/12)).add
    ((axial.sub (Interval.point (1/2))).mul (sine (by norm_num : (0:ℝ)≤2/5)))).sub
      ((cosine (by norm_num : (0:ℝ)≤2/5)).div (Interval.point 2) (by norm_num [Interval.point]))
  have hhi : B.hi<0 := by dsimp [B]; mixed_fixed
  exact B.mem.2.trans_lt hhi

theorem cap_monotone : MonotoneOn cap (Icc 0 (7/10)) := by
  intro x hx y hy hxy
  have hs := sin_mono hx hy hxy
  have hc := cos_anti hx hy hxy
  have ha : 0≤outerAxial-1/2 := by linarith [outer_endpoint_bounds.1]
  have hp := mul_le_mul_of_nonneg_left hs ha
  dsimp [cap]
  linarith

theorem original_angle_lower (r : Row) (hτ : targetPositive r=true)
    {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b A B (angle true x)) : 2/5<x := by
  have hcap := necessary_cap r hτ hs ht hx hm
  by_contra h
  have hmono := cap_monotone hx (show (2/5:ℝ)∈Icc 0 (7/10) by norm_num) (le_of_not_gt h)
  linarith [cap_reference]

theorem sine_reference : (389/1000:ℝ)<Real.sin (2/5) := by
  have h := (sine (by norm_num : (0:ℝ)≤2/5)).mem.1
  have hb : (389/1000:ℝ)<(sine (by norm_num : (0:ℝ)≤2/5)).lo := by mixed_fixed
  exact hb.trans_le h

theorem support_coefficients (r : Row) (hσ : sourcePositive r=false)
    (hτ : targetPositive r=true) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    -multiplier*Real.sin x-coP r<0 ∧ 0< multiplier*Real.cos x-coQ r := by
  have hx0 : x∈Icc 0 (7/10) := ⟨by linarith [hx.1],hx.2⟩
  have ht := positive_trig hx0
  have hs := sin_mono (show (2/5:ℝ)∈Icc 0 (7/10) by norm_num) hx0 hx.1
  have hp : -(19335/100000:ℝ)≤coP r := by
    revert hσ hτ
    fin_cases r <;> norm_num [sourcePositive,targetPositive,coP]
  have hq := (coefficient_bounds r).2.2.2.1
  dsimp [multiplier]
  constructor <;> linarith [sine_reference]

theorem hasDerivAt_F (r : Row) (x : ℝ) : HasDerivAt (F r) (Fd r x) x := by
  have h := ((((hasDerivAt_id' x).const_add (Real.pi/2+coC r-coG r/2-N r/12-coP r*outerAxial)).add
    ((Real.hasDerivAt_cos x).const_mul (4/5))).sub
      ((Real.hasDerivAt_sin x).const_mul (multiplier*(outerAxial-1/2))))
  have hF : F r=fun y => Real.pi/2+coC r-coG r/2-N r/12-coP r*outerAxial+y+
      4/5*Real.cos y-multiplier*(outerAxial-1/2)*Real.sin y := by
    funext y
    simp only [F]
    ring
  rw [hF]
  convert h using 1
  simp only [Fd]
  ring

theorem derivative_negative (r : Row) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) : Fd r x<0 := by
  have hx0 : x∈Icc 0 (7/10) := ⟨by linarith [hx.1],hx.2⟩
  have ht := positive_trig hx0
  have hs := sin_mono (show (2/5:ℝ)∈Icc 0 (7/10) by norm_num) hx0 hx.1
  have ha : (1829/2000:ℝ)<outerAxial-1/2 := by
    linarith [ShortOuterZero.fine_axial_bounds.1]
  have hmul := mul_lt_mul_of_pos_right ha (show 0<Real.cos x by linarith [ht.1])
  dsimp [Fd,multiplier]
  nlinarith [sine_reference]

theorem antitone (r : Row) : AntitoneOn (F r) (Icc (2/5) (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun x hx => (hasDerivAt_F r x).continuousAt.continuousWithinAt)
    (fun x hx => hasDerivAt_F r x)
    (fun x hx => (derivative_negative r (Ioo_subset_Icc_self hx)).le)

def normBox (r : Row) : Interval (N r) :=
  rootSix (Interval.point (multiplier^2+coG r^2)) 2 (by norm_num)
    (by dsimp [Interval.point]; positivity)
def endpointBox (r : Row) : Interval (F r (7/10)) := by
  convert ((((((((halfPi.add (Interval.point (7/10))).add (Interval.point (coC r))).sub
    (Interval.point (coG r/2))).sub ((normBox r).div (Interval.point 12) (by norm_num [Interval.point]))).sub
      ((Interval.point (coP r)).mul axial)).add
        ((Interval.point (4/5)).mul (cosine (by norm_num : (0:ℝ)≤7/10)))).sub
          (((Interval.point multiplier).mul (axial.sub (Interval.point (1/2)))).mul
            (sine (by norm_num : (0:ℝ)≤7/10))))) using 1 <;> dsimp [F]

private lemma r82_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl

private lemma r82_endpointBox_lo (r : Row) : (endpointBox r).lo =
    ((((((((halfPi.add (Interval.point (7/10))).add (Interval.point (coC r))).sub
    (Interval.point (coG r/2))).sub ((normBox r).div (Interval.point 12) (by norm_num [Interval.point]))).sub
      ((Interval.point (coP r)).mul axial)).add
        ((Interval.point (4/5)).mul (cosine (by norm_num : (0:ℝ)≤7/10)))).sub
          (((Interval.point multiplier).mul (axial.sub (Interval.point (1/2)))).mul
            (sine (by norm_num : (0:ℝ)≤7/10))))).lo := by
  unfold endpointBox
  rw [r82_mpr_lo]
  dsimp [F]

theorem endpoint (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=true) :
    (152/125:ℝ)<F r (7/10) := by
  have hbound : (152/125:ℝ)<(endpointBox r).lo := by
    rw [r82_endpointBox_lo]
    revert hσ hτ
    fin_cases r <;> norm_num [sourcePositive,targetPositive] <;> simp only [normBox,multiplier] <;>
      mixed_fixed
  exact hbound.trans_le (endpointBox r).mem.1

theorem original_lower (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=true)
    {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc (2/5) (7/10)) (hm : sourcePrimary r a b A B (angle true x)) :
    F r x≤coreOuterCost r a b A B (angle true x) := by
  have hx0 : x∈Icc 0 (7/10) := ⟨by linarith [hx.1],hx.2⟩
  have hg := (coefficient_bounds r).1
  have hcore := core_circle_lower (X:= -multiplier) (Y:= -coG r) hs (by linarith)
  have he : Real.sqrt ((-multiplier)^2+(-coG r)^2)=N r := by
    dsimp [N]
    congr 1
    ring
  rw [he] at hcore
  have hcoeff := support_coefficients r hσ hτ hx
  have houter := outer_axial_lower (X:= -multiplier*Real.sin x-coP r)
    (Y:=multiplier*Real.cos x-coQ r) ht hcoeff.1.le hcoeff.2.le
  dsimp [sourcePrimary] at hm
  rw [angle_width true hx0,angle_sin,angle_cos,targetSign_positive hτ] at hm
  have hmult := mul_le_mul_of_nonneg_left hm (show 0≤ multiplier by norm_num [multiplier])
  dsimp [F,coreOuterCost]
  rw [sourceSign_negative hσ,targetSign_positive hτ]
  dsimp [angle,direction,multiplier] at *
  nlinarith

theorem original (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=true)
    (upper : Bool) {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b A B (angle upper x)) :
    (449/500:ℝ)<coreOuterCost r a b A B (angle upper x) := by
  cases upper
  · exact False.elim (lower_impossible r hτ hs ht hx hm)
  · have hxl := original_angle_lower r hτ hs ht hx hm
    have hxr : x∈Icc (2/5) (7/10) := ⟨hxl.le,hx.2⟩
    have hmono := antitone r hxr (show (7/10:ℝ)∈Icc (2/5) (7/10) by norm_num) hx.2
    have hsource := original_lower r hσ hτ hs ht hxr hm
    linarith [endpoint r hσ hτ]

end SquaresInCircles.Eight.ShortWord.MixedQuarter.CorePrimaryPositive
