module

public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2CoefficientDomain
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2Endpoints
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2SecantCoordinate

/-!
# Eight squares: the low equal-angle comparison

Increasing the fixed coefficient
decreases the increment of the original zero-angle norm. The GA
equal-angle endpoint therefore also pays for the low AB endpoint.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowEqual
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus
open SecantCoordinate SecantBaseline

theorem norm_increment {k m l p : ℝ} (hk : 0<k) (hkm : k≤ m)
    (hl : 0<l) (hlp : l≤p) :
    pairNorm m p 0-pairNorm m l 0≤pairNorm k p 0-pairNorm k l 0 := by
  have hm : 0< m := hk.trans_le hkm
  have hksq : 0<k^2 := sq_pos_of_pos hk
  have hmsq : 0< m^2 := sq_pos_of_pos hm
  have hd (x : ℝ) : HasDerivAt
      (fun x => radical (k^2) x-radical (m^2) x)
      (x/radical (k^2) x-x/radical (m^2) x) x :=
    (radical_hasDerivAt hksq).sub (radical_hasDerivAt hmsq)
  have hmono : MonotoneOn (fun x => radical (k^2) x-radical (m^2) x) (Icc l p) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
    intro x hx
    have hx0 : 0≤x := (hl.trans hx.1).le
    have hroot : radical (k^2) x≤radical (m^2) x := by
      apply Real.sqrt_le_sqrt
      nlinarith [mul_nonneg (sub_nonneg.mpr hkm) (by linarith : 0≤ m+k)]
    have hquot := div_le_div_of_nonneg_left hx0 (radical_positive hksq) hroot
    linarith
  have hh := hmono ⟨le_rfl,hlp⟩ ⟨hlp,le_rfl⟩ hlp
  dsimp [radical] at hh
  simp only [pairNorm_zero]
  linarith

theorem charge_comparison {k m l s : ℝ} (hk : 0<k) (hkm : k≤ m)
    (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    FlatTStress.secantCharge R l k s≤FlatTStress.secantCharge R l m s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hp : l≤l/Real.cos s := by
    apply (le_div_iff₀ hc).2
    nlinarith [mul_le_mul_of_nonneg_left (Real.cos_le_one s) hl.le]
  have hh := norm_increment hk hkm hl hp
  have hm := mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg qCap)
  dsimp [FlatTStress.secantCharge]
  linarith

theorem baseline_comparison {s z : ℝ} (hz : z∈Icc 0 (1/5:ℝ))
    (hs : s∈Icc 0 frameCap) :
    baseline true (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z≤
      baseline false (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z := by
  have hz' : z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
    norm_num [Certificate.left,Certificate.right,Certificate.split]
    exact hz
  have hp := Explicit.family_positive .low hz'
  have hk := (Explicit.family_basic_domain .low hz').2.2.2.1
  have hm := (Explicit.low_tilted hz).1
  have hh := charge_comparison (m:=Explicit.m .low z) hp.1 (by linarith) hp.2.1 hs
  rw [baseline_eq_extension true _ _ _ _ hs,baseline_eq_extension false _ _ _ _ hs]
  simp only [angularBaseline,affected,↓reduceIte,Bool.false_eq_true,baseline_zero]
  dsimp only [Explicit.m] at hh
  linarith

theorem original (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z z := by
  have hGA := (Certificate.low_endpoints hz).2.2.2.2
  cases atG
  · exact hGA.trans_le (baseline_comparison hz
      ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩)
  · exact hGA

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowEqual
