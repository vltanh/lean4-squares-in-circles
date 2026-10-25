module

public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3Data
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedPositive
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2SecantCoordinate

/-!
# Eight squares: the exact s-dependent part of the BT3 reference baseline

Both BT3 and the rotated TD0 coefficient are
fixed while s varies. The existing secant-coordinate derivative
identities therefore apply after this explicit baseline cancellation.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.Angular
open Candidate Secondary PositiveAngularEnvelope
open NegativeAPositiveTD.SecantCoordinate

def affected (atG : Bool) (k m : ℝ) : ℝ := if atG then k else m
def ratio (atG : Bool) (k l m : ℝ) : ℝ := affected atG k m/l
def extension (atG : Bool) (k l m s z : ℝ) : ℝ :=
  baseline atG k l m 0 z+FlatTStress.secantCharge R l (affected atG k m) s
abbrev angleSlope := NegativeAPositiveTD.SecantBaseline.angleSlope

theorem baseline_eq_extension (atG : Bool) (k l m z : ℝ) {s : ℝ}
    (hs : s∈Icc 0 frameCap) : baseline atG k l m s z=extension atG k l m s z := by
  have hw := NegativeAPositiveTD.secant_width_identity (l:=l) hs
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  dsimp [NegativeAPositiveTD.secant] at hw
  have hid : l*(1/Real.cos s-1+(13/12)*Real.tan s)=
      l/Real.cos s-l+(13/12)*l*Real.tan s := by ring
  cases atG <;> simp only [extension,baseline,affected,lambdaG,lambdaB,NegativeAPositiveTD.lambdaG,
      NegativeAPositiveTD.lambdaB,↓reduceIte,Bool.false_eq_true,secant,NegativeAPositiveTD.secant,
      Real.cos_zero,div_one,Real.tan_zero,edgeWidth_zero,mul_zero,add_zero,
      fullSupport_pair,FlatTStress.secantCharge] <;>
    rw [hid] <;> linarith only [hw]

theorem extension_hasDerivAt (atG : Bool) {k l m s z : ℝ}
    (hl : 0<l) (hc : 0<Real.cos s) :
    HasDerivAt (fun s => extension atG k l m s z) (angleSlope l (ratio atG k l m) s) s := by
  have hh := (SecantNormCurvature.charge_hasDerivAt (R:=R) (a:=affected atG k m) hl hc).const_add
    (baseline atG k l m 0 z)
  simpa only [extension,ratio,NegativeAPositiveTD.SecantBaseline.angleSlope_eq hc] using hh

theorem pure_at_original (atG : Bool) {k l m s z p q : ℝ}
    (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    NegativeAPositiveTD.SecantCoordinate.pure (baseline atG k l m 0 z)
      l (ratio atG k l m) p q z (Real.tan s)=
      baseline atG k l m s z+OrdinaryAngleConcavity.V R p q (z-s) := by
  rw [baseline_eq_extension atG k l m z hs]
  have hc := charge_arctan hl (affected atG k m) (Real.tan s)
  rw [arctan_tan hs] at hc
  dsimp [NegativeAPositiveTD.SecantCoordinate.pure,extension,ratio]
  rw [hc,arctan_tan hs]

theorem GA_positive_identity {k l m s z : ℝ} (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    baseline true k l m s z+OrdinaryAngleConcavity.U R k (secant l s) (s-z)=
      baseline true k l m 0 z+l*(NegativeAPositiveTD.AffectedPositiveCurves.upper (k/l) z s-1+
        R*OrdinaryCurvatureBounds.shape (k/l)) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  rw [baseline_eq_extension true k l m z hs]
  simp only [extension,affected,↓reduceIte,FlatTStress.secantCharge,OrdinaryAngleConcavity.U]
  rw [NegativeAPositiveTD.AffectedPositive.rotation_norm hl hc k z,
    NegativeAPositiveTD.AffectedPositive.zero_norm hl k]
  dsimp [NegativeAPositiveTD.AffectedPositiveCurves.upper,secant,NegativeAPositiveTD.secant]
  field_simp [hl.ne']
  ring

theorem AB_positive_identity {k l m s z : ℝ} (hl : 0<l)
    (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 s) :
    baseline false k l m s z+OrdinaryAngleConcavity.U R (min (secant l s) m)
      (max (secant l s) m) (s-z)=
      baseline false k l m 0 z+l*(min
        (NegativeAPositiveTD.AffectedPositiveCurves.upper (m/l) z s)
        (NegativeAPositiveTD.AffectedPositiveCurves.lower (m/l) z s)-1+
        R*OrdinaryCurvatureBounds.shape (m/l)) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have ht : s-z∈Icc 0 frameCap := ⟨by linarith [hz.2],by linarith [hs.2,hz.1]⟩
  have hphi := sub_nonneg.mpr (CorrelatedSameBlock.one_le_phi ht)
  have hbranch := NegativeAPositiveTD.AffectedPositive.branch_difference (r:=m/l) (z:=z) hc.ne'
  have hsec : 1/Real.cos s*l=secant l s := by
    simp only [secant,NegativeAPositiveTD.secant]; ring
  rcases le_total (secant l s) m with hh|hh
  · have hr : 1/Real.cos s ≤ m/l := by
      apply (le_div_iff₀ hl).2
      linarith
    have hprod := mul_nonneg (sub_nonneg.mpr hr) hphi
    have hm : NegativeAPositiveTD.AffectedPositiveCurves.lower (m/l) z s≤
        NegativeAPositiveTD.AffectedPositiveCurves.upper (m/l) z s := by linarith
    rw [min_eq_right hm,baseline_eq_extension false k l m z hs]
    simp only [extension,affected,↓reduceIte,Bool.false_eq_true,FlatTStress.secantCharge,
      min_eq_left hh,max_eq_right hh,OrdinaryAngleConcavity.U,pairNorm_symm (secant l s) m]
    rw [NegativeAPositiveTD.AffectedPositive.rotation_norm hl hc m z,
      NegativeAPositiveTD.AffectedPositive.zero_norm hl m,
      NegativeAPositiveTD.AffectedPositiveCurves.lower_identity hc.ne']
    simp only [secant,NegativeAPositiveTD.secant]
    ring
  · have hr : m/l≤1/Real.cos s := by
      apply (div_le_iff₀ hl).2
      linarith
    have hprod := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) hphi
    have hm : NegativeAPositiveTD.AffectedPositiveCurves.upper (m/l) z s≤
        NegativeAPositiveTD.AffectedPositiveCurves.lower (m/l) z s := by linarith
    rw [min_eq_left hm,baseline_eq_extension false k l m z hs]
    simp only [extension,affected,↓reduceIte,Bool.false_eq_true,FlatTStress.secantCharge,
      min_eq_right hh,max_eq_left hh,OrdinaryAngleConcavity.U]
    rw [NegativeAPositiveTD.AffectedPositive.rotation_norm hl hc m z,
      NegativeAPositiveTD.AffectedPositive.zero_norm hl m]
    simp only [NegativeAPositiveTD.AffectedPositiveCurves.upper,secant,NegativeAPositiveTD.secant]
    field_simp [hl.ne']
    ring

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.Angular
