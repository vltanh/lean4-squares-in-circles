module

public import SquaresInCircles.Eight.TableFree.GlobalGATargetOuterCurvature
public import SquaresInCircles.Eight.TableFree.StationaryIntervalAlgebra

/-!
# The single rational reference for the outer target scalar

Uncompiled transcription of equations (34)--(35) of the target note.
All arithmetic is at the prescribed angle 61/100, with the prescribed
adjacent Taylor polynomials and positive-square radical bounds. The
curvature theorem then controls the complete feasible interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Target.Outer
open FramePair FrameCircleArc Arithmetic HighOrderTaylor StationaryPrimitives

def reference : ℝ := 61/100
def referenceSin : Interval (Real.sin reference) := Interval.of_bounds
  ⟨S11_le_sin (by norm_num [reference]),sin_le_sin9 (by norm_num [reference])⟩
def referenceCos : Interval (Real.cos reference) := Interval.of_bounds
  ⟨cos10_le_cos (by norm_num [reference]),cos_le_C12 (by norm_num [reference])⟩
def Sbox : Interval S := Interval.of_bounds ⟨S_bounds.1.le,S_bounds.2.le⟩
def Pbox : Interval P := Sbox.sub (Interval.point 1)
def referenceK : Interval (K reference) :=
  ((Interval.point 1).add referenceCos).sub (Pbox.mul referenceSin)
def referenceU : Interval (U reference) := referenceSin.add (Pbox.mul referenceCos)
def referenceRadicand : Interval (Q0-K reference^2) :=
  (Interval.point Q0).sub referenceK.square

macro "ga_target_fixed" : tactic => `(tactic|
  norm_num [Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
    referenceSin,referenceCos,Sbox,Pbox,referenceK,referenceU,referenceRadicand,
    reference,S11,C12,sin9,sin7,cos10,cos8,Q0,m])

theorem reference_domain : Domain reference := by
  have hK : K reference<(3/2:ℝ) := by
    have hh : referenceK.hi<(3/2:ℝ) := by ga_target_fixed
    exact referenceK.mem.2.trans_lt hh
  exact ⟨by norm_num [reference,frameCap],by linarith [FrameLowArc.a0_bounds.1]⟩

theorem reference_Y : (6919629/5000000:ℝ)<Y reference ∧
    Y reference<13839261/10000000 := by
  have hh := sqrt_bounds referenceRadicand.mem
    (by norm_num : (0:ℝ)≤6919629/5000000)
    (by norm_num : (0:ℝ)≤13839261/10000000)
    (show (6919629/5000000:ℝ)^2<referenceRadicand.lo by ga_target_fixed)
    (show referenceRadicand.hi<(13839261/10000000:ℝ)^2 by ga_target_fixed)
  exact hh

def referenceY : Interval (Y reference) := Interval.of_bounds
  ⟨reference_Y.1.le,reference_Y.2.le⟩

def referenceSlope : Interval (Jd reference) :=
  ((Interval.point 1).sub ((((Interval.point m).mul referenceK).mul referenceU).div referenceY (by norm_num [referenceY,Interval.of_bounds]))).add
      ((Interval.point (9/100)).mul (referenceCos.sub referenceSin))

theorem reference_value : (117939/100000:ℝ)<J reference := by
  have hsin := referenceSin.mem.1
  have hcos := referenceCos.mem.1
  have hy := reference_Y.2
  have hnum : (117939/100000:ℝ)<reference+m*(2-13839261/10000000)+
      (9/100)*(S11 reference+cos10 reference-1) := by
    norm_num [reference,m,S11,sin9,sin7,cos10,cos8]
  change S11 reference≤Real.sin reference at hsin
  change cos10 reference≤Real.cos reference at hcos
  dsimp [J,m] at *
  linarith

theorem reference_slope : |Jd reference|<(1/1000:ℝ) := by
  have hlo : -(1/1000:ℝ)<referenceSlope.lo := by
    dsimp [referenceSlope,referenceY]
    ga_target_fixed
  have hhi : referenceSlope.hi<(1/1000:ℝ) := by
    dsimp [referenceSlope,referenceY]
    ga_target_fixed
  exact abs_lt.mpr ⟨hlo.trans_le referenceSlope.mem.1,referenceSlope.mem.2.trans_lt hhi⟩

theorem scalar_lower {u : ℝ} (hu : Domain u) : (58969/50000:ℝ)<J u := by
  have hr := reference_domain
  have hl : Domain (min u reference) := by
    rcases le_total u reference with h | h
    · simpa [min_eq_left h] using hu
    · simpa [min_eq_right h] using hr
  have hh : max u reference∈Icc 0 frameCap :=
    ⟨le_max_of_le_left hu.1.1,max_le hu.1.2 hr.1.2⟩
  have hdom (z : ℝ) (hz : z∈Icc (min u reference) (max u reference)) : Domain z :=
    domain_interval hl hh hz
  have ht := CenteredMonomialBounds.second_derivative_tangent_lower
    (κ:=(1/3:ℝ))
    (fun z hz => J_hasDerivAt (hdom z hz))
    (fun z hz => Jd_hasDerivAt (hdom z hz))
    (fun z hz => (curvature_lower (hdom z hz)).le)
    (show reference∈Icc (min u reference) (max u reference) from
      ⟨min_le_right _ _,le_max_right _ _⟩)
    (show u∈Icc (min u reference) (max u reference) from
      ⟨min_le_left _ _,le_max_left _ _⟩)
  have habs := mul_le_mul_of_nonneg_right reference_slope.le (abs_nonneg (u-reference))
  rw [←abs_mul] at habs
  have hlin := (abs_le.mp habs).1
  have hsquare := sq_nonneg (|u-reference|-3/1000)
  have hsqabs := sq_abs (u-reference)
  have hvalue := reference_value
  nlinarith

end SquaresInCircles.Eight.TableFree.GlobalGA.Target.Outer
