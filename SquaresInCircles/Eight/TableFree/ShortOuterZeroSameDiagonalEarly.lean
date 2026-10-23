module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroSameDiagonalEarlyGeometry
public import SquaresInCircles.Eight.TableFree.ShortOuterZeroSameAxial

/-!
# The integrated early diagonal cost

Uncompiled transcription of equations (10)--(12). The .91 lower speed,
.942 initial upper speed, and .2 upper acceleration are integrated on
one complete interval. The target-label tangent then yields exactly the
quadratic in the written proof, whose increment is nonnegative in every
coupled row.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Same.Diagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open SecondWord (outer_domain outer_zero_mem)

lemma early_height_bounds {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    (91/100)*(x-e)≤height x ∧ height x≤(471/500)*(x-e)+(1/10)*(x-e)^2 := by
  have hm : MonotoneOn (fun u => height u-(91/100)*u) (Icc e (3/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun u hu => ((SecondWord.SameZero.PJ.Diagonal.height_hasDerivAt
        (early_angle he hu)).sub ((hasDerivAt_id u).const_mul (91/100))).continuousAt.continuousWithinAt)
      (fun u hu => (SecondWord.SameZero.PJ.Diagonal.height_hasDerivAt
        (early_angle he (Ioo_subset_Icc_self hu))).sub ((hasDerivAt_id u).const_mul (91/100)))
      (fun u hu => by linarith [(early_speed_acceleration he (Ioo_subset_Icc_self hu)).1])
  have hmono := hm ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1
  rw [(event_geometry he).2] at hmono
  have ht := curvature_tangent (f := fun u => -height u) (d := fun u => -speed u)
    (dd := fun u => -acceleration u) (κ := -(1/5:ℝ)) hx ⟨le_rfl,hx.1.trans hx.2⟩
    (fun u hu => (SecondWord.SameZero.PJ.Diagonal.height_hasDerivAt (early_angle he hu)).neg)
    (fun u hu => (SecondWord.SameZero.PJ.Diagonal.speed_hasDerivAt (early_angle he hu)).neg)
    (fun u hu => by linarith [(early_speed_acceleration he hu).2])
  rw [(event_geometry he).2] at ht
  have hs := mul_le_mul_of_nonneg_right (initial_speed he).le (sub_nonneg.mpr hx.1)
  exact ⟨by linarith,by nlinarith⟩

def initialTargetSlope (r : Row) : ℝ := t r-P r*ratio 0
def upperTargetSlope (r : Row) : ℝ := t r-(5223/20000)*P r

def linearGain (r : Row) : ℝ := 1-(471/500)*upperTargetSlope r
def quadraticGain (r : Row) : ℝ :=
  (557/2000)*P r*(91/100)^2-(1/10)*upperTargetSlope r

lemma target_slope_bounds (r : Row) (hr : Coupled r) :
    0<initialTargetSlope r ∧ initialTargetSlope r≤upperTargetSlope r := by
  have hp := (coefficient_signs r).2.2
  have hlo := mul_le_mul_of_nonneg_left PositiveCoefficient.rho_bounds.1.le hp
  have hhi := mul_le_mul_of_nonneg_left PositiveCoefficient.rho_bounds.2.le hp
  dsimp [initialTargetSlope,upperTargetSlope]
  rw [Axial.zero_ratio]
  constructor
  · fin_cases r <;> norm_num [Coupled] at hr <;> norm_num [P,t] at hhi ⊢ <;> linarith
  · linarith

lemma gain_coefficients (r : Row) (hr : Coupled r) :
    quadraticGain r≤0 ∧ 0<linearGain r+(193/1000)*quadraticGain r := by
  fin_cases r <;> norm_num [Coupled] at hr <;>
    norm_num [linearGain,quadraticGain,upperTargetSlope,P,t]

lemma gain_nonnegative (r : Row) (hr : Coupled r) {u : ℝ}
    (hu : u∈Icc (0:ℝ) (193/1000)) : 0≤linearGain r*u+quadraticGain r*u^2 := by
  have hc := gain_coefficients r hr
  have hs := mul_nonneg hu.1 (sub_nonneg.mpr hu.2)
  have hq := mul_le_mul_of_nonpos_left
    (show u^2≤(193/1000)*u by nlinarith) hc.1
  have hl := mul_nonneg hc.2.le hu.1
  nlinarith

lemma target_tangent (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    -P r*outerAxial-initialTargetSlope r*B+(557/2000)*P r*B^2≤
      -P r*arc B-t r*B := by
  have ht := curvature_tangent
    (f := fun u => -P r*arc u-t r*u)
    (d := fun u => P r*ratio u-t r)
    (dd := fun u => P r*ShortOuterOne.SameContact.ratioD u)
    (κ := (557/1000)*P r) hB outer_zero_mem
    (fun u hu => by
      convert ((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hu)).const_mul (-P r)).
        sub ((hasDerivAt_id u).const_mul (t r)) using 1 <;> ring)
    (fun u hu => ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hu)).
      const_mul (P r)).sub_const (t r))
    (fun u hu => by
      have hh := mul_le_mul_of_nonneg_left (Axial.ratioD_lower hu).le (coefficient_signs r).2.2
      nlinarith)
  rw [ShortOuterOne.SameContact.arc_zero] at ht
  dsimp [initialTargetSlope]
  nlinarith

/-- All three coupled rows, including the closed initial point. -/
theorem early_lower (r : Row) (hr : Coupled r) {e x : ℝ}
    (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    (11226/12500:ℝ)<cost r x := by
  let u := x-e
  have hu : u∈Icc (0:ℝ) (193/1000) := by
    dsimp [u]
    constructor
    · exact sub_nonneg.mpr hx.1
    · have hl : (107/1000:ℝ)<e := by norm_num [Event.lo] at he; linarith [he.1.1]
      linarith [hx.2]
  have hB := SecondWord.SameZero.PJ.Diagonal.target_mem (early_geometry he hx)
  have hs := early_height_bounds he hx
  have hs0 : 0≤(91/100)*u := by dsimp [u]; positivity
  have hBsquare : ((91/100)*u)^2≤(height x)^2 :=
    pow_le_pow_left₀ hs0 (by simpa [u] using hs.1) 2
  have hm := target_slope_bounds r hr
  have hupper : 0≤(471/500)*u+(1/10)*u^2 := by positivity
  have hneg := mul_le_mul_of_nonneg_left
    (show height x≤(471/500)*u+(1/10)*u^2 by simpa [u] using hs.2) hm.1.le
  have hnegU := mul_le_mul_of_nonneg_right hm.2 hupper
  have hquad := mul_le_mul_of_nonneg_left hBsquare
    (show 0≤(557/2000)*P r by exact mul_nonneg (by norm_num) (coefficient_signs r).2.2)
  have htarget := target_tangent r hB
  have hinitial := Event.initial_cost r hr he
  have hgain := gain_nonnegative r hr hu
  have hidentity : x=e+u := by dsimp [u]; ring
  dsimp [linearGain,quadraticGain] at hgain
  dsimp [cost]
  rw [hidentity]
  nlinarith

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Same.Diagonal
