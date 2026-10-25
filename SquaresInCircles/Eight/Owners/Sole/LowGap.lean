module

public import SquaresInCircles.Eight.Frames.Ordinary.AngleConcavity
public import SquaresInCircles.Eight.Owners.Sole.LowGapPolynomials

/-!
# Eight squares: the low-family charge gap at the original common radius

The polynomial bounds are transferred by two
positive-sided squarings. The original coefficients ell(t), c(t) remain
fixed in the comparison of the two angles. Increasing the radius from
sqrt(qLow) only increases this exact norm difference.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SoleLowGap
open Polynomial SoleECoefficients PositiveAngularEnvelope PairNormCalculus
open OrdinaryAngleConcavity HighOrderTaylor

/-- A purely algebraic two-squaring lemma. Its square-gap and norm-square
bounds are supplied below by the displayed Taylor polynomials. -/
theorem two_squarings {Q R X Y A d v : ℝ}
    (hQ : 0<Q) (hR : 0≤R) (hRQ : Q≤R^2)
    (hX : 0≤X) (hY : 0≤Y) (hA : 0<A)
    (hv : Y^2≤v) (hd : d≤X^2-Y^2)
    (hB : 0<Q*d-A^2)
    (hP : 0<(Q*d-A^2)^2-4*Q*A^2*v) :
    A<R*(X-Y) := by
  let r := Real.sqrt Q
  have hr : 0<r := Real.sqrt_pos.mpr hQ
  have hr2 : r^2=Q := Real.sq_sqrt hQ.le
  have hcross0 : 0≤2*r*A*Y := by positivity
  have hcross2 : (2*r*A*Y)^2=4*Q*A^2*Y^2 := by
    calc
      _=4*r^2*A^2*Y^2 := by ring
      _=_ := by rw [hr2]
  have hm := mul_le_mul_of_nonneg_left hv
    (show 0≤4*Q*A^2 by positivity)
  have hcrosssq : (2*r*A*Y)^2<(Q*d-A^2)^2 := by
    rw [hcross2]
    linarith
  have hcross : 2*r*A*Y<Q*d-A^2 := by
    by_contra hn
    have hh := pow_le_pow_left₀ hB.le (le_of_not_gt hn) 2
    linarith
  have hmd := mul_le_mul_of_nonneg_left hd hQ.le
  have hx2 : (r*X)^2=Q*X^2 := by
    calc _=r^2*X^2 := by ring
         _=_ := by rw [hr2]
  have hy2 : (r*Y+A)^2=Q*Y^2+2*r*A*Y+A^2 := by
    calc _=r^2*Y^2+2*r*A*Y+A^2 := by ring
         _=_ := by rw [hr2]
  have hsecond : (r*Y+A)^2<(r*X)^2 := by rw [hx2,hy2]; linarith
  have hsecond0 : 0≤r*Y+A := by positivity
  have hroot : r*Y+A<r*X := by
    by_contra hn
    have hh := pow_le_pow_left₀ (mul_nonneg hr.le hX) (le_of_not_gt hn) 2
    linarith
  have hgap : 0<X-Y := by
    by_contra hn
    have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hr.le
    linarith only [hh,hroot,hA]
  have hRr : r≤R := by
    have hh := Real.sqrt_le_sqrt hRQ
    rwa [Real.sqrt_sq hR] at hh
  have hmono := mul_le_mul_of_nonneg_right hRr hgap.le
  linarith only [hroot,hmono]

theorem negative_norm_square {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : t∈Set.Icc 0 frameCap) :
    (pairNorm p q (-t))^2=p^2+q^2-2*p*q*Real.sin t := by
  have hn : |-t|≤frameCap := by simpa [abs_of_nonneg ht.1] using ht.2
  have h := pairNorm_sq hp hq hn
  rw [h,Real.sin_neg]
  simp only [pairEnergy,pairProduct]
  ring

theorem norm_square_upper {t : ℝ} (ht : t∈domain .low) :
    (pairNorm (ell .low t) (c .low t) (-frameCap))^2≤
      aeval t SoleLowGapPolynomials.normSquare := by
  have hp := positive ht
  rw [negative_norm_square hp.2.1 hp.2.2.1
    (show frameCap∈Set.Icc 0 frameCap from ⟨by norm_num [frameCap],le_rfl⟩),
    SoleLowGapPolynomials.normSquare_eval]
  have hs := S15_le_sin (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0≤2*ell .low t*c .low t from
      mul_nonneg (mul_nonneg (by norm_num) hp.2.1.le) hp.2.2.1.le)
  linarith

theorem norm_square_gap_lower {t : ℝ} (ht : t∈domain .low) :
    aeval t SoleLowGapPolynomials.squareGap≤
      (pairNorm (ell .low t) (c .low t) (-t))^2-
        (pairNorm (ell .low t) (c .low t) (-frameCap))^2 := by
  have hp := positive ht
  rw [negative_norm_square hp.2.1 hp.2.2.1 (angle ht),
    negative_norm_square hp.2.1 hp.2.2.1
      (show frameCap∈Set.Icc 0 frameCap from ⟨by norm_num [frameCap],le_rfl⟩),
    SoleLowGapPolynomials.squareGap_eval]
  have hs := S15_le_sin (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have htaylor := sin_le_S13 ht.1
  have hm := mul_le_mul_of_nonneg_left
    (show S15 frameCap-S13 t≤Real.sin frameCap-Real.sin t by linarith)
    (show 0≤2*ell .low t*c .low t from
      mul_nonneg (mul_nonneg (by norm_num) hp.2.1.le) hp.2.2.1.le)
  linarith

theorem demand_upper {t : ℝ} (ht : t∈domain .low) :
    43/100+c .low t*(Real.cos t-Real.cos frameCap)≤
      aeval t SoleLowGapPolynomials.demand := by
  rw [SoleLowGapPolynomials.demand_eval]
  have hct := cos_le_C16 ht.1
  have hch := C14_le_cos (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hm := mul_le_mul_of_nonneg_left
    (by linarith : Real.cos t-Real.cos frameCap≤C16 t-C14 frameCap)
    (positive ht).2.2.1.le
  linarith

/-- The common radius is a variable throughout; no original point is
moved to the trial circle. -/
theorem B_gap {R t : ℝ} (hR : 0≤R) (hQ : qLow≤R^2)
    (ht : t∈domain .low) :
    43/100<V R (ell .low t) (c .low t) frameCap-
      V R (ell .low t) (c .low t) t := by
  obtain ⟨hA,hB,hP⟩ := SoleLowGapPolynomials.reserves ht
  rw [SoleLowGapPolynomials.firstSquare_eval] at hB
  rw [SoleLowGapPolynomials.certificate_eval,
    SoleLowGapPolynomials.firstSquare_eval] at hP
  have hQ0 : (0:ℝ)<qLow := by norm_num [qLow]
  have hv := norm_square_upper ht
  have hdg := norm_square_gap_lower ht
  have hd := demand_upper ht
  generalize qLow=Q at *
  have hh := two_squarings
    (Q := Q) (R := R)
    (X := pairNorm (ell .low t) (c .low t) (-t))
    (Y := pairNorm (ell .low t) (c .low t) (-frameCap))
    (A := aeval t SoleLowGapPolynomials.demand)
    (d := aeval t SoleLowGapPolynomials.squareGap)
    (v := aeval t SoleLowGapPolynomials.normSquare)
    hQ0 hR hQ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (by linarith) hv hdg (by linarith) (by linarith)
  dsimp only [V]
  linarith

end SquaresInCircles.Eight.SoleLowGap
