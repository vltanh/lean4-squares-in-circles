module

public import SquaresInCircles.Eight.Frames.Ordinary.AngleConcavity
public import SquaresInCircles.Eight.Frames.Ordinary.NegativeSlope
public import SquaresInCircles.Eight.Frames.Ordinary.PositiveEnvelope
public import SquaresInCircles.Eight.Owners.OccupiedSignedConcentration
public import SquaresInCircles.Eight.Owners.Sole.LowGapPolynomials
public import SquaresInCircles.Eight.Owners.Sole.NormGain

/-!
# Eight squares: ordinary coefficients for the two sole-E stresses

The four indices are H, A, B, D. The Boolean `de`
distinguishes sole-DE from sole-EH. H is a two-angle block only in the
sole-DE case; A retains its actual smaller negative coefficient. B and
D use the full two-angle domain, which also covers a missing incident
ordinary angle by setting that angle to zero.
-/

section
/-!
## Ordinary-angle growth at every radius in the working band

The negative growth estimate is uniform in the radius
and retains a one-angle anchor's actual negative coefficient. Together
with the positive-angle bound, it removes all separated and same-block
allocations in the middle and high sole-E coefficient families.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleAngleGrowth
open PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open OrdinaryAngleConcentration OrdinaryNegativeSlope OrdinaryNegativeEnvelope
open VaryingBFunctions VaryingBComparison SingleAngleConcavity

theorem radius_lower {R : ℝ} (hR : 0≤R) (hQ : qLow≤R^2) : 19787/10000<R := by
  norm_num [qLow] at hQ
  nlinarith

theorem endpoint_normalized_slope {R : ℝ} (hR : 0≤R) (hQ : qLow≤R^2) :
    (2/3 : ℝ)< -Real.sin frameCap+
      R*(2/3)*Real.cos frameCap/root (2/3) (Real.sin frameCap) := by
  have hh : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hN := root_pos (2/3) (sin_mem hh)
  have hN2 := root_sq (2/3) (sin_mem hh)
  have hNhi : root (2/3) (Real.sin frameCap)<1913/2500 := by
    nlinarith [cap_sin_lower]
  have hc := (transport_trig hh).1
  have hs := (transport_trig hh).2.2.2.1
  have hC0 : 0<Real.cos frameCap := by linarith
  have hnum1 := mul_lt_mul_of_pos_right (radius_lower hR hQ) hC0
  have hnum2 := mul_lt_mul_of_pos_left hc (by norm_num : (0:ℝ)<19787/10000)
  have hupper := mul_lt_mul_of_pos_left hNhi
    (show 0<(2/3 : ℝ)+Real.sin frameCap by linarith [(transport_trig hh).2.2.1])
  have hupper2 := mul_lt_mul_of_pos_right hs (by norm_num : (0:ℝ)<1913/2500)
  have hcross : ((2/3 : ℝ)+Real.sin frameCap)*root (2/3) (Real.sin frameCap)<
      R*(2/3)*Real.cos frameCap := by nlinarith
  have hdiv := (lt_div_iff₀ hN).2 hcross
  linarith

theorem Vd_lower {R p q t : ℝ} (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (2/3)*q≤p) (ht : t∈Icc 0 frameCap) :
    (2/3)*q<Vd R p q t := by
  have hq := hp.trans_le hpq
  have hqp : q≤2*p := by linarith
  have hrlo : 2/3≤p/q := (le_div_iff₀ hq).2 hratio
  have hrhi : p/q≤1 := (div_le_one hq).2 hpq
  have hh : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hfrac := normalized_fraction_mono (by norm_num : (0:ℝ)≤2/3) hrlo hrhi (sin_mem hh)
  have hmul := mul_le_mul_of_nonneg_left hfrac
    (mul_nonneg hR (show 0≤Real.cos frameCap by linarith [(transport_trig hh).1]))
  have hnorm : (2/3 : ℝ)< -Real.sin frameCap+
      R*(p/q)*Real.cos frameCap/root (p/q) (Real.sin frameCap) := by
    have hbase := endpoint_normalized_slope hR hQL
    have e1 : R*(p/q)*Real.cos frameCap/root (p/q) (Real.sin frameCap)=
        R*Real.cos frameCap*(p/q/root (p/q) (Real.sin frameCap)) := by ring
    have e2 : R*(2/3)*Real.cos frameCap/root (2/3) (Real.sin frameCap)=
        R*Real.cos frameCap*(2/3/root (2/3) (Real.sin frameCap)) := by ring
    rw [e1]
    rw [e2] at hbase
    linarith
  have hend : (2/3)*q<Vd R p q frameCap := by
    rw [Vd_normalized hq]
    nlinarith only [mul_lt_mul_of_pos_left hnorm hq]
  exact hend.trans_le ((Vd_antitone hR hQU hp hpq hqp) ht hh ht.2)

theorem VnuDeriv_lower {R p q nu t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (2/3)*q≤p) (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) : (2/3)*q<VnuDeriv R p q nu t := by
  have hv := Vd_lower hR hQL hQU hp hpq hratio ht
  have hn := mul_le_mul_of_nonneg_right hnu (transport_trig ht).2.2.1
  dsimp [Vd,mixedNDerivative,VnuDeriv] at *
  simp only [zero_sub] at hv
  linarith

theorem Vnu_growth {R p q nu t u : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (2/3)*q≤p) (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap) (htu : t≤u) :
    (2/3)*q*(u-t)≤Vnu R p q nu u-Vnu R p q nu t := by
  exact derivative_reserve
    (fun x hx => (Vnu_hasDerivAt hp (hp.trans_le hpq) hx).continuousAt.continuousWithinAt)
    (fun x hx => Vnu_hasDerivAt hp (hp.trans_le hpq) (Ioo_subset_Icc_self hx))
    (fun x hx => (VnuDeriv_lower hR hQL hQU hp hpq hratio hnu (Ioo_subset_Icc_self hx)).le)
    ht hu htu

theorem pure_growth {single : Bool} {R p q nu t u : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (2/3)*q≤p) (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap) (htu : t≤u) :
    (2/3)*q*(u-t)≤pure single R p q nu u-pure single R p q nu t := by
  cases single
  · simpa [SingleAngleConcavity.pure] using
      Vnu_growth (nu := q) hR hQL hQU hp hpq hratio (le_refl q) ht hu htu
  · exact Vnu_growth hR hQL hQU hp hpq hratio hnu ht hu htu

/-- Once the coefficient intervals overlap by this explicit growth
reserve, every mixed allocation lies above the smallest pure charge. -/
theorem balanced_envelope {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (m : ι → Bool) (R : ℝ) (p q nu P N : ι → ℝ) {t L qlo qhi : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : ∀ i,0<p i) (hpq : ∀ i,p i≤q i) (hratio : ∀ i,(2/3)*q i≤p i)
    (hnu : ∀ i,p i≤nu i ∧ nu i≤q i) (hqr : ∀ i,qlo≤q i ∧ q i≤qhi)
    (hreserve : (109/200)*qhi≤(2/3)*qlo)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (ht : t∈Icc 0 frameCap) (hbudget : (∑ i,P i)≤frameCap-t)
    (hbalance : (∑ i,N i)=t+∑ i,P i)
    (hsingle : ∀ i,m i=true → P i=0 ∨ N i=0)
    (hpure : ∀ i,L≤pure (m i) R (p i) (q i) (nu i) t) :
    L≤∑ i,F (m i) R (p i) (q i) (nu i) (P i) (N i) := by
  have hqp (i : ι) : q i≤2*p i := by linarith [hratio i,hp i]
  apply SingleAngleConcentration.lower_from_endpoints m R p q nu P N hR hQU hp hpq hqp
    (fun i => (hnu i).1) hP hN ht hbudget hbalance hsingle hpure
  · intro i hi
    have hv : L≤V R (p i) (q i) t := by simpa [SingleAngleConcavity.pure,hi] using hpure i
    exact hv.trans (M_ge_V (hp i).le ((hp i).trans_le (hpq i)).le
      (by linarith [hratio i]) ht)
  · intro i j _
    have hlen : 0≤frameCap-t := by linarith [ht.2]
    have hU := OrdinaryPositiveEnvelope.U_lower hR hQU (hp i) (hpq i) (hqp i)
      (show frameCap-t∈Icc 0 frameCap from ⟨hlen,by linarith [ht.1]⟩)
    have hV := pure_growth (single := m j) hR hQL hQU (hp j) (hpq j) (hratio j)
      (hnu j).2 ht (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht.2
    have hcoef : (109/200)*q i≤(2/3)*q j := by
      linarith [(hqr i).2,(hqr j).1]
    have hm := mul_le_mul_of_nonneg_right hcoef hlen
    linarith [hpure j]

end SquaresInCircles.Eight.SoleAngleGrowth
end
end
end

section
/-!
## The low-family charge gap at the original common radius

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
end
end
end

section
/-!
## The low-family H, D and B charges

H and D are compared along a rectangle of actual
positive force coefficients with the fixed pair (17253/20000,1).
The larger negative coefficient 28/25 allows the sole-DE endpoint too.
All estimates cover whole angle intervals and the original radius band.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleLowChargeBounds
open SoleECoefficients SoleNormGain SoleLowGap PositiveAngularEnvelope
open PairNormCalculus OrdinaryAngleConcavity OrdinaryNegativeSlope
open SingleAngleConcavity OrdinaryCurvatureBounds VaryingBFunctions VaryingBComparison

def base : ℝ := 17253/20000

theorem base_gain_le {R p q s : ℝ} (hR : 0≤R)
    (hp : base≤p) (hpq : p≤q) (hq : q∈Icc 1 (28/25 : ℝ))
    (hs : s∈Icc 0 frameCap) : normGain R base 1 s≤normGain R p q s := by
  have hb : 0<base := by norm_num [base]
  have hq0 : 0<q := by linarith [hq.1]
  have hsin := (transport_trig hs).2.2.2.1
  have hsin0 := (transport_trig hs).2.2.1
  have hr : Real.sin s*q≤base := by
    have hm := mul_le_mul hsin.le hq.2 hq0.le (by norm_num : (0:ℝ)≤6443/10000)
    norm_num [base] at *
    linarith
  have hlarge := normGain_larger_mono hR hb (by norm_num [base]) hq.1 hs hr
  have hsmall := normGain_smaller_mono hR hq0 hs
    (show base∈Icc (q/2) q by
      constructor <;> dsimp [base] at * <;> linarith [hq.1,hq.2])
    (show p∈Icc (q/2) q from ⟨by dsimp [base] at hp; linarith [hq.2],hpq⟩) hp
  exact hlarge.trans hsmall

theorem base_gain_linear {R s : ℝ} (hR : 0≤R) (hQL : qLow≤R^2)
    (hs : s∈Icc 0 frameCap) : (323/250)*Real.sin s≤normGain R base 1 s := by
  have hX0 : 0<pairNorm base 1 0 := by
    rw [pairNorm_zero]; exact Real.sqrt_pos.mpr (by norm_num [base])
  have hY0 : 0≤pairNorm base 1 (-s) := Real.sqrt_nonneg _
  have hX2 : (pairNorm base 1 0)^2=(17253/20000)^2+1 := by
    rw [pairNorm_zero,Real.sq_sqrt (by positivity)]; norm_num [base]
  have hY2 : (pairNorm base 1 (-s))^2=(17253/20000)^2+1-2*(17253/20000)*Real.sin s := by
    rw [negative_norm_square (by norm_num [base]) (by norm_num) hs]; norm_num [base]
  have hsin := (transport_trig hs).2.2.1
  show (323/250)*Real.sin s≤R*(pairNorm base 1 0-pairNorm base 1 (-s))
  generalize pairNorm base 1 0=X at *
  generalize pairNorm base 1 (-s)=Y at *
  have hXY : Y≤X := le_of_pow_le_pow_left₀ two_ne_zero hX0.le (by
    rw [hX2,hY2]; linarith [mul_nonneg (by norm_num : (0:ℝ)≤2*(17253/20000)) hsin])
  have hXhi : X≤132067/100000 := le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) (by
    rw [hX2]; norm_num)
  have hdiff : 0≤X-Y := sub_nonneg.mpr hXY
  have hprod := mul_le_mul_of_nonneg_left
    (show X+Y≤2*(132067/100000 : ℝ) by linarith) hdiff
  have hid : (X-Y)*(X+Y)=2*(17253/20000)*Real.sin s := by linear_combination hX2-hY2
  rw [hid] at hprod
  have hrad := SoleAngleGrowth.radius_lower hR hQL
  have hmR := mul_le_mul_of_nonneg_right hrad.le hdiff
  have hcoef : (323/250 : ℝ)*(132067/100000)≤(19787/10000)*(17253/20000) := by norm_num
  have hmcoef := mul_le_mul_of_nonneg_right hcoef hsin
  have hmprod := mul_le_mul_of_nonneg_left hprod (by norm_num : (0:ℝ)≤19787/10000)
  have hmrad := mul_le_mul_of_nonneg_left hmR (by norm_num : (0:ℝ)≤132067/100000)
  linarith

theorem short_trig {t : ℝ} (ht : t∈Icc 0 (1/5 : ℝ)) :
    (149/150)*t≤Real.sin t ∧ 1-Real.cos t≤t/10 := by
  have ht2 : t^2≤1/25 := by nlinarith [ht.1,ht.2]
  have ht3 := mul_le_mul_of_nonneg_right ht2 ht.1
  have hs := Real.sin_ge_sub_cube ht.1
  have hc := nonneg_of_deriv_nonneg (fun x => Real.cos x-1+x^2/2)
    (by fun_prop) (by norm_num)
    (fun x hx => by
      simp (disch := fun_prop)
      linarith [Real.sin_le hx]) ht.1
  have hquad := mul_le_mul_of_nonneg_left ht.2 ht.1
  constructor <;> nlinarith

theorem wide_short {R p q nu t : ℝ} (hR : 0≤R) (hQL : qLow≤R^2)
    (hp : base≤p) (hpq : p≤q) (hq : q∈Icc 1 (28/25 : ℝ))
    (hnu : nu≤28/25) (ht : t∈domain .low) :
    (117/100)*t≤Vnu R p q nu t := by
  have hg := (base_gain_linear hR hQL (angle ht)).trans
    (base_gain_le hR hp hpq hq (angle ht))
  have hc0 : 0≤1-Real.cos t := by linarith [Real.cos_le_one t]
  have hnu' := mul_le_mul_of_nonneg_right hnu hc0
  obtain ⟨hs,hc⟩ := short_trig ht
  dsimp [normGain,Vnu] at *
  nlinarith [ht.1]

theorem wide_cap {R p q nu : ℝ} (hR : 0≤R) (hQL : qLow≤R^2)
    (hp : base≤p) (hpq : p≤q) (hq : q∈Icc 1 (28/25 : ℝ))
    (hnu : nu≤28/25) : (31/40 : ℝ)<Vnu R p q nu frameCap := by
  have hh : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hg := base_gain_le hR hp hpq hq hh
  have hX2 : (pairNorm base 1 0)^2=(17253/20000)^2+1 := by
    rw [pairNorm_zero,Real.sq_sqrt (by positivity)]; norm_num [base]
  have hY2 : (pairNorm base 1 (-frameCap))^2=
      (17253/20000)^2+1-2*(17253/20000)*Real.sin frameCap := by
    rw [negative_norm_square (by norm_num [base]) (by norm_num) hh]; norm_num [base]
  have hX0 : 0≤pairNorm base 1 0 := Real.sqrt_nonneg _
  have hY0 : 0≤pairNorm base 1 (-frameCap) := Real.sqrt_nonneg _
  have hX : (66033/50000 : ℝ)<pairNorm base 1 0 := lt_of_pow_lt_pow_left₀ 2 hX0 (by
    rw [hX2]; norm_num)
  have hY : pairNorm base 1 (-frameCap)<79543/100000 := by
    have hs := sin_lower_seven (show 0≤frameCap by norm_num [frameCap])
    norm_num [frameCap] at hs
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hY2]; linarith)
  have hdiff : (52523/100000 : ℝ)<pairNorm base 1 0-pairNorm base 1 (-frameCap) := by
    linarith
  have hrad := SoleAngleGrowth.radius_lower hR hQL
  have hmul := mul_lt_mul'' hrad hdiff (by norm_num) (by norm_num)
  have hc := (transport_trig hh).1
  have hnu' := mul_le_mul_of_nonneg_right hnu
    (show 0≤1-Real.cos frameCap by linarith [Real.cos_le_one frameCap])
  dsimp only [normGain,Vnu] at hg hmul ⊢
  linarith

theorem B_zero_slope {R t : ℝ} (hR : R∈Icc 0 2) (ht : t∈domain .low) :
    Vd R (ell .low t) (c .low t) 0≤233/200 := by
  have hp := positive ht
  have hb := low_bounds ht
  have hc : 0<c .low t := hp.2.2.1
  have hr0 : 0≤ell .low t/c .low t := div_nonneg hp.2.1.le hc.le
  have hr1 : ell .low t/c .low t≤669/1000 :=
    (div_le_iff₀ hc).2 (by simpa [mul_comm] using (low_correlations ht).2.1.le)
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hfrac := normalized_fraction_mono hr0 hr1 (by norm_num) hz
  have hN := root_pos (669/1000) hz
  have hN2 := root_sq (669/1000) hz
  have hNlo : (1203/1000 : ℝ)≤root (669/1000) 0 :=
    le_of_pow_le_pow_left₀ two_ne_zero hN.le (by rw [hN2]; norm_num)
  have hnum : c .low t*R*(669/1000)≤(209/200)*2*(669/1000) := by
    have hm := mul_le_mul hb.2.2.2.1.le hR.2 hR.1 (by norm_num : (0:ℝ)≤209/200)
    linarith only [hm]
  have hbound : c .low t*R*(669/1000)/root (669/1000) 0≤233/200 := by
    apply (div_le_iff₀ hN).2
    linarith only [hnum,hNlo]
  have hm := mul_le_mul_of_nonneg_left hfrac (mul_nonneg hc.le hR.1)
  rw [Vd_normalized hc]
  simp only [Real.sin_zero,Real.cos_zero,neg_zero,zero_add,mul_one]
  calc
    c .low t*(R*(ell .low t/c .low t)/root (ell .low t/c .low t) 0)
        ≤c .low t*R*(669/1000)/root (669/1000) 0 := by
          simpa only [mul_div_assoc,mul_assoc] using hm
    _≤233/200 := hbound

theorem B_short {R t : ℝ} (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain .low) :
    V R (ell .low t) (c .low t) t≤(233/200)*t := by
  have hp := positive ht
  have hb := low_bounds ht
  have hpq : ell .low t≤c .low t := hb.2.2.2.2.2.2.1.le.trans hb.2.2.1
  have hqp := hb.2.2.2.2.2.2.2.1
  have hR2 : R≤2 := by norm_num [qCap] at hQ; nlinarith
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hanti := Vd_antitone hR hQ hp.2.1 hpq hqp
  have hd := derivative_reserve
    (f := fun x => -V R (ell .low t) (c .low t) x)
    (df := fun x => -Vd R (ell .low t) (c .low t) x)
    (k := -Vd R (ell .low t) (c .low t) 0)
    (fun x hx => (V_hasDerivAt hp.2.1 hp.2.2.1 hx).neg.continuousAt.continuousWithinAt)
    (fun x hx => (V_hasDerivAt hp.2.1 hp.2.2.1 (Ioo_subset_Icc_self hx)).neg)
    (fun x hx => neg_le_neg (hanti hz (Ioo_subset_Icc_self hx) hx.1.le))
    hz (angle ht) ht.1
  simp only [V_zero,neg_zero,sub_zero] at hd
  have hm := mul_le_mul_of_nonneg_right (B_zero_slope ⟨hR,hR2⟩ ht) ht.1
  linarith

theorem B_cap {R t : ℝ} (hR : R∈Icc 0 2) (ht : t∈domain .low) :
    V R (ell .low t) (c .low t) frameCap<18/25 := by
  have hp := positive ht
  rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
  have hh : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hsmall := normGain_smaller_mono hR.1 hp.2.2.1 hh
    (show ell .low t∈Icc (c .low t/2) (c .low t) from ⟨by linarith,hlk.le.trans hkc⟩)
    (show (349/500 : ℝ)∈Icc (c .low t/2) (c .low t) by constructor <;> linarith)
    hl1.le
  have hlarge := normGain_larger_mono hR.1 (by norm_num : (0:ℝ)<349/500)
    (show (349/500 : ℝ)≤c .low t by linarith) hc1.le hh
    (show Real.sin frameCap*(209/200)≤(349/500 : ℝ) by
      linarith [(transport_trig hh).2.2.2.1])
  have hX2 : (pairNorm (349/500) (209/200) 0)^2=(349/500 : ℝ)^2+(209/200)^2 := by
    simp only [pairNorm_zero]
    exact Real.sq_sqrt (by positivity)
  have hY2 := negative_norm_square (by norm_num : (0:ℝ)<349/500)
    (by norm_num : (0:ℝ)<209/200) hh
  have hX0 : 0≤pairNorm (349/500) (209/200) 0 := Real.sqrt_nonneg _
  have hY0 : 0≤pairNorm (349/500) (209/200) (-frameCap) := Real.sqrt_nonneg _
  have hX : pairNorm (349/500) (209/200) 0≤1257/1000 :=
    le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) (by rw [hX2]; norm_num)
  have hY : (799/1000 : ℝ)≤pairNorm (349/500) (209/200) (-frameCap) :=
    le_of_pow_le_pow_left₀ two_ne_zero hY0 (by
      rw [hY2]; linarith only [(transport_trig hh).2.2.2.1])
  have hdiff : pairNorm (349/500) (209/200) 0-
      pairNorm (349/500) (209/200) (-frameCap)≤229/500 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hdiff hR.1
  have hcos := cos_upper_four (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hclo : (117/500 : ℝ)≤1-Real.cos frameCap := by
    norm_num [frameCap] at hcos
    linarith
  have hpen := mul_le_mul (hk0.trans hkc) hclo
    (by norm_num : (0:ℝ)≤117/500) hp.2.2.1.le
  dsimp only [normGain,V] at hsmall hlarge ⊢
  linarith only [hsmall,hlarge,hmul,hpen,hR.2]

theorem wide_dominates {R p q nu t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : base≤p) (hpq : p≤q) (hq : q∈Icc 1 (28/25 : ℝ))
    (hnu : nu≤28/25) (ht : t∈domain .low) :
    V R (ell .low t) (c .low t) t≤Vnu R p q nu t ∧
    V R (ell .low t) (c .low t) frameCap≤Vnu R p q nu frameCap := by
  have hR2 : R≤2 := by norm_num [qCap] at hQU; nlinarith
  constructor
  · have hwide := wide_short hR hQL hp hpq hq hnu ht
    have hB := B_short hR hQU ht
    nlinarith [ht.1]
  · linarith [wide_cap hR hQL hp hpq hq hnu,B_cap ⟨hR,hR2⟩ ht]

end SquaresInCircles.Eight.SoleLowChargeBounds
end
end
end

section
/-!
## Coefficients of the low family at every split

The two split coordinates range independently over `[0, t]`; the constraint `x + e = t` only
narrows this domain (`split_bounds`, `coarse_upper`). In particular the E coefficient of the
sole-DE stress may reach `28/25` (`wide_pair_H`, `wide_pair_D`). These are scalar inequalities on
the coefficients.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleLowCoefficientBounds
open SoleECoefficients SoleLowChargeBounds SecondaryEStress

theorem tilted_mono {a : ℝ} (ha : a∈Icc (1/4 : ℝ) (7/10)) :
    MonotoneOn (fun s => Real.cos s+a*Real.sin s) (Icc (0:ℝ) (1/5)) := by
  apply monoOn_of_hasDeriv_nonneg
  · fun_prop
  · intro s _
    exact (Real.hasDerivAt_cos s).add ((Real.hasDerivAt_sin s).const_mul a)
  · intro s hs
    have hs' := Ioo_subset_Icc_self hs
    have hc : (49/50 : ℝ)≤Real.cos s := by linarith [(short_trig hs').2,hs'.2]
    have hsin := Real.sin_le hs'.1
    have hm := mul_le_mul ha.1 hc (by norm_num : (0:ℝ)≤49/50)
      (show 0≤a by linarith [ha.1])
    nlinarith [hs'.2]

theorem tilted_lower {a s : ℝ} (ha : a∈Icc (1/4 : ℝ) (7/10))
    (hs : s∈Icc 0 (1/5 : ℝ)) : 1≤Real.cos s+a*Real.sin s := by
  have hm := tilted_mono ha (show (0:ℝ)∈Icc 0 (1/5 : ℝ) by norm_num) hs hs.1
  simpa using hm

theorem tilted_upper {a s : ℝ} (ha : a∈Icc 0 (8/25 : ℝ)) :
    Real.cos s+a*Real.sin s<21/20 := by
  have hid : (Real.cos s+a*Real.sin s)^2+(Real.sin s-a*Real.cos s)^2=
      (1+a^2)*((Real.sin s)^2+(Real.cos s)^2) := by ring
  rw [Real.sin_sq_add_cos_sq] at hid
  have ha2 : a^2≤(8/25 : ℝ)^2 := by nlinarith [ha.1,ha.2]
  nlinarith [sq_nonneg (Real.sin s-a*Real.cos s)]

theorem split_bounds {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    k .low t≤n .low t x ∧ n .low t x<21/20 ∧
    1≤p .low t e ∧ p .low t e<21/20 ∧
    1≤r .low e ∧ r .low e<28/25 := by
  have hx' : x∈Icc 0 (1/5 : ℝ) := ⟨hx.1,hx.2.trans ht.2⟩
  have he' : e∈Icc 0 (1/5 : ℝ) := ⟨he.1,he.2.trans ht.2⟩
  have hp := positive ht
  rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,heta0,heta1⟩
  have hnlo := mul_le_mul_of_nonneg_left
    (tilted_lower (a := 8/25) (by norm_num) hx') hp.1.le
  have hnhi := mul_lt_mul_of_pos_left
    (tilted_upper (a := 8/25) (s := x) (by norm_num)) hp.1
  have hplo := tilted_lower (a := eta .low t)
    ⟨by linarith only [heta0],by linarith only [heta1]⟩ he'
  have hphi := tilted_upper (a := eta .low t) (s := e) ⟨hp.2.2.2.2,heta1.le⟩
  have hrlo := tilted_lower (a := 7/10) (by norm_num) he'
  have hrmono := tilted_mono (a := 7/10) (by norm_num) he'
    (show (1/5 : ℝ)∈Icc 0 (1/5 : ℝ) by norm_num) he'.2
  dsimp only at hrmono
  have hrc := cos_upper_four (x := (1/5 : ℝ)) (by norm_num)
  have hrs := sin_upper_five (x := (1/5 : ℝ)) (by norm_num)
  norm_num at hrc hrs
  dsimp only [n,p,r,g,tiltedWeight]
  simp only [show Band.low≠Band.high by decide,↓reduceIte]
  refine ⟨by linarith only [hnlo],by linarith only [hnhi,hk1],hplo,hphi,hrlo,
    by linarith only [hrmono,hrc,hrs]⟩

theorem coarse_upper {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    k .low t≤1+(7/10)*t ∧ ell .low t≤1+(7/10)*t ∧
    c .low t≤1+(7/10)*t ∧ n .low t x≤1+(7/10)*t ∧
    p .low t e≤1+(7/10)*t ∧ r .low e≤1+(7/10)*t := by
  have hd := angle ht
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans hd.2⟩
  have he' : e∈Icc 0 frameCap := ⟨he.1,he.2.trans hd.2⟩
  have hsx := (transport_trig hx').2.2.1
  have hse := (transport_trig he').2.2.1
  have hcx := Real.cos_le_one x
  have hce := Real.cos_le_one e
  have hsxu := Real.sin_le hx.1
  have hseu := Real.sin_le he.1
  have ht0 := ht.1
  have ht1 : t≤1/5 := ht.2
  rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,heta0,heta1⟩
  have hc : c .low t≤1+(7/10)*t := by
    have ht2 := mul_le_mul_of_nonneg_left ht1 ht0
    dsimp only [c,k]
    linarith only [ht2,ht0,ht1]
  have hnbase : 0≤Real.cos x+(8/25)*Real.sin x := by
    have hco := (transport_trig hx').1
    linarith only [hco,hsx]
  have hn := mul_le_mul_of_nonneg_right (show k .low t≤1 by linarith only [hk1]) hnbase
  have hpeta := mul_le_mul_of_nonneg_right heta1.le hse
  refine ⟨hkc.trans hc,hlk.le.trans (hkc.trans hc),hc,?_,?_,?_⟩
  · dsimp only [n,g,tiltedWeight]
    linarith only [hn,hcx,hsxu,hsx,hx.2,ht0]
  · simp only [p,show Band.low≠Band.high by decide,↓reduceIte]
    linarith only [hpeta,hce,hseu,hse,he.2,ht0]
  · simp only [r,show Band.low≠Band.high by decide,↓reduceIte]
    linarith only [hce,hseu,he.2]

theorem wide_pair_H {de : Bool} {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    base≤ min (if de then r .low e else 1) (n .low t x) ∧
      max (if de then r .low e else 1) (n .low t x)∈Icc 1 (28/25 : ℝ) := by
  have hb := split_bounds ht hx he
  have hk := (low_bounds ht).1
  cases de <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
    constructor
  · exact le_min (by norm_num [base]) (by dsimp [base]; linarith)
  · exact ⟨le_max_left _ _,max_le (by norm_num) (by linarith [hb.2.1])⟩
  · exact le_min (by dsimp [base]; linarith [hb.2.2.2.2.1]) (by dsimp [base]; linarith)
  · exact ⟨hb.2.2.2.2.1.trans (le_max_left _ _),max_le hb.2.2.2.2.2.le (by linarith [hb.2.1])⟩

theorem wide_pair_D {de : Bool} {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    base≤ min (if de then 1 else p .low t e) (c .low t) ∧
      max (if de then 1 else p .low t e) (c .low t)∈Icc 1 (28/25 : ℝ) := by
  have hb := split_bounds ht hx he
  have hk := (low_bounds ht).1
  have hkc := (low_bounds ht).2.2.1
  have hc := (low_bounds ht).2.2.2.1
  cases de <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
    constructor
  · exact le_min (by dsimp [base]; linarith [hb.2.2.1]) (by dsimp [base]; linarith)
  · exact ⟨hb.2.2.1.trans (le_max_left _ _),max_le (by linarith [hb.2.2.2.1]) (by linarith)⟩
  · exact le_min (by norm_num [base]) (by dsimp [base]; linarith)
  · exact ⟨le_max_left _ _,max_le (by norm_num) (by linarith)⟩

end SquaresInCircles.Eight.SoleLowCoefficientBounds
end
end
end

section
/-!
## Growth comparisons of the positive-T ordinary envelope

A single quartic covers every ratio at least `0.72` (`ratio_square`, `high_growth`). The
families of smaller ratio use fixed long secants (`fixed_chords`), transferred by the
monotonicity of the normalized derivative (`normalized_growth`, `low_growth`, `middle_growth`).
The estimates hold at the radius of the cycle on the whole working band.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SolePositiveTGrowth

def lowerRadius : ℚ := 19787/10000

open PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open OrdinaryAngleConcentration OrdinaryNegativeSlope OrdinaryNegativeEnvelope
open VaryingBFunctions VaryingBComparison SingleAngleConcavity

theorem radius_le {R : ℝ} (hR : 0≤R) (hQ : qLow≤R^2) :
    (lowerRadius:ℝ)≤R := by
  have h := SoleAngleGrowth.radius_lower hR hQ
  have he : (lowerRadius:ℝ)=19787/10000 := by norm_num [lowerRadius]
  linarith

theorem ratio_square {r : ℝ} (hr : r∈Icc (18/25:ℝ) 1) :
    (2/25:ℝ)<(lowerRadius:ℝ)^2*r^2*(478/625)^2-
      (r+6443/10000)^2*(1+r^2-2*r*(3221/5000)) := by
  have h1 : 0≤r-18/25 := sub_nonneg.2 hr.1
  have h2 : 0≤1-r := sub_nonneg.2 hr.2
  rw [show (lowerRadius:ℝ)=19787/10000 by norm_num [lowerRadius]]
  linarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h1) h2,
    mul_nonneg (mul_nonneg (mul_nonneg h1 h1) h2) (by linarith : (0:ℝ)≤r)]

theorem normalized_high_slope {R r : ℝ}
    (hR : 0≤R) (hQ : qLow≤R^2) (hr : r∈Icc (18/25:ℝ) 1) :
    r< -Real.sin frameCap+R*r*Real.cos frameCap/root r (Real.sin frameCap) := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hs := transport_trig hh
  have hN := root_pos r (sin_mem hh)
  have hN2 := root_sq r (sin_mem hh)
  have hr0 : 0<r := by linarith [hr.1]
  have hS : Real.sin frameCap≤6443/10000 := hs.2.2.2.1.le
  have hC : (478/625:ℝ)≤Real.cos frameCap := by linarith [hs.1]
  have hD : (root r (Real.sin frameCap))^2≤
      1+r^2-2*r*(3221/5000) := by
    nlinarith [mul_le_mul_of_nonneg_left cap_sin_lower.le hr0.le]
  have hDmul := mul_le_mul_of_nonneg_left hD (sq_nonneg (r+6443/10000))
  have hpoly := ratio_square hr
  have hcross0 : (r+6443/10000)*root r (Real.sin frameCap)<
      (lowerRadius:ℝ)*r*(478/625) := by
    have hp : 0≤(lowerRadius:ℝ)*r*(478/625) := by
      exact mul_nonneg (mul_nonneg (by norm_num [lowerRadius]) hr0.le) (by norm_num)
    have hsq : ((r+6443/10000)*root r (Real.sin frameCap))^2<
        ((lowerRadius:ℝ)*r*(478/625))^2 := by
      have he1 : ((r+6443/10000)*root r (Real.sin frameCap))^2=
          (r+6443/10000)^2*(root r (Real.sin frameCap))^2 := by ring
      have he2 : ((lowerRadius:ℝ)*r*(478/625))^2=(lowerRadius:ℝ)^2*r^2*(478/625)^2 := by ring
      rw [he1,he2]
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 hp hsq
  have hleft : (r+Real.sin frameCap)*root r (Real.sin frameCap)≤
      (r+6443/10000)*root r (Real.sin frameCap) :=
    mul_le_mul_of_nonneg_right (by linarith) hN.le
  have hright := mul_le_mul
    (mul_le_mul_of_nonneg_right (radius_le hR hQ) hr0.le) hC
    (by norm_num : (0:ℝ)≤478/625) (mul_nonneg hR hr0.le)
  have hcross : (r+Real.sin frameCap)*root r (Real.sin frameCap)<
      R*r*Real.cos frameCap := hleft.trans_lt (hcross0.trans_le hright)
  have hdiv := (lt_div_iff₀ hN).2 hcross
  linarith

theorem Vd_gt_smaller {R p q t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (18/25)*q≤p)
    (ht : t∈Icc 0 frameCap) : p<Vd R p q t := by
  have hq := hp.trans_le hpq
  have hr : p/q∈Icc (18/25:ℝ) 1 :=
    ⟨(le_div_iff₀ hq).2 hratio,(div_le_one hq).2 hpq⟩
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hbase := mul_lt_mul_of_pos_left (normalized_high_slope hR hQL hr) hq
  have hcancel : q*(p/q)=p := by field_simp
  rw [hcancel,← Vd_normalized hq] at hbase
  exact hbase.trans_le ((Vd_antitone hR hQU hp hpq (by linarith)) ht hh ht.2)

theorem VnuDeriv_antitone {R p q nu : ℝ}
    (hR : 0≤R) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hnu : p≤nu) :
    AntitoneOn (VnuDeriv R p q nu) (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro x hx
    exact (VnuDeriv_hasDerivAt hp (hp.trans_le hpq) hx).continuousAt.continuousWithinAt
  · intro x hx
    exact VnuDeriv_hasDerivAt hp (hp.trans_le hpq) (Ioo_subset_Icc_self hx)
  · intro x hx
    linarith [Vnu_second_lt hR hQU hp hpq hqp hnu (Ioo_subset_Icc_self hx)]

theorem VnuDeriv_ge_Vd {R p q nu t : ℝ} (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) : Vd R p q t≤VnuDeriv R p q nu t := by
  have h := mul_le_mul_of_nonneg_right hnu (transport_trig ht).2.2.1
  dsimp [Vd,mixedNDerivative,VnuDeriv]
  simp only [zero_sub]
  linarith

theorem high_growth {R p q nu t u : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (18/25)*q≤p) (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap) (htu : t≤u) :
    p*(u-t)≤Vnu R p q nu u-Vnu R p q nu t := by
  apply derivative_reserve
    (fun x hx => (Vnu_hasDerivAt hp (hp.trans_le hpq) hx).continuousAt.continuousWithinAt)
    (fun x hx => Vnu_hasDerivAt hp (hp.trans_le hpq) (Ioo_subset_Icc_self hx))
    (fun x hx => ?_) ht hu htu
  exact (Vd_gt_smaller hR hQL hQU hp hpq hratio (Ioo_subset_Icc_self hx)).le.trans
    (VnuDeriv_ge_Vd hnu (Ioo_subset_Icc_self hx))

/-- Comparing derivatives transfers a normalized chord to `Vnu`, with the one-angle negative
coefficient `nu` itself. -/
theorem normalized_growth {R p q nu r t u : ℝ}
    (hR : (lowerRadius:ℝ)≤R) (hp : 0<p) (hpq : p≤q)
    (hr : 0<r) (hratio : r*q≤p) (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap) (htu : t≤u) :
    q*(V (lowerRadius:ℝ) r 1 u-V (lowerRadius:ℝ) r 1 t)≤
      Vnu R p q nu u-Vnu R p q nu t := by
  have hq := hp.trans_le hpq
  have hratio' : r≤p/q := (le_div_iff₀ hq).2 hratio
  have hpq' : p/q≤1 := (div_le_one hq).2 hpq
  have hd (x : ℝ) (hx : x∈Icc 0 frameCap) :
      q*Vd (lowerRadius:ℝ) r 1 x≤VnuDeriv R p q nu x := by
    have hfrac := normalized_fraction_mono hr.le hratio' hpq' (sin_mem hx)
    have hc : 0≤Real.cos x := by linarith [(transport_trig hx).1]
    have hfrac0 : 0≤r/root r (Real.sin x) := div_nonneg hr.le (root_pos r (sin_mem hx)).le
    have hR0 : 0≤R := (by norm_num [lowerRadius] : (0:ℝ)≤lowerRadius).trans hR
    have hfirst := mul_le_mul_of_nonneg_right hR (mul_nonneg hc hfrac0)
    have hsecond := mul_le_mul_of_nonneg_left hfrac (mul_nonneg hR0 hc)
    have he1 : (lowerRadius:ℝ)*r*Real.cos x/root r (Real.sin x)=
        (lowerRadius:ℝ)*(Real.cos x*(r/root r (Real.sin x))) := by ring
    have he2 : R*(p/q)*Real.cos x/root (p/q) (Real.sin x)=
        R*Real.cos x*((p/q)/root (p/q) (Real.sin x)) := by ring
    have he3 : R*(Real.cos x*(r/root r (Real.sin x)))=
        R*Real.cos x*(r/root r (Real.sin x)) := by ring
    have hnormalized :
        -Real.sin x+(lowerRadius:ℝ)*r*Real.cos x/root r (Real.sin x)≤
        -Real.sin x+R*(p/q)*Real.cos x/root (p/q) (Real.sin x) := by
      rw [he1,he2]
      linarith only [hfirst,hsecond,he3]
    have hscaled := mul_le_mul_of_nonneg_left hnormalized hq.le
    have hscaled' : q*Vd (lowerRadius:ℝ) r 1 x≤Vd R p q x := by
      rw [Vd_normalized hq,Vd_normalized (by norm_num : (0:ℝ)<1)]
      simpa only [div_one,one_mul] using hscaled
    exact hscaled'.trans (VnuDeriv_ge_Vd hnu hx)
  have hg := derivative_reserve
    (f := fun x => Vnu R p q nu x-q*V (lowerRadius:ℝ) r 1 x)
    (df := fun x => VnuDeriv R p q nu x-q*Vd (lowerRadius:ℝ) r 1 x)
    (k := 0)
    (fun x hx => ((Vnu_hasDerivAt hp hq hx).sub
      ((V_hasDerivAt hr (by norm_num) hx).const_mul q)).continuousAt.continuousWithinAt)
    (fun x hx => (Vnu_hasDerivAt hp hq (Ioo_subset_Icc_self hx)).sub
      ((V_hasDerivAt hr (by norm_num) (Ioo_subset_Icc_self hx)).const_mul q))
    (fun x hx => sub_nonneg.mpr (hd x (Ioo_subset_Icc_self hx))) ht hu htu
  simp only [zero_mul] at hg
  linarith

/-- For a concave function, a terminal secant remains a lower bound
when its left endpoint is moved further left. -/
theorem extend_terminal_chord {f : ℝ → ℝ} {a t k : ℝ}
    (hc : ConcaveOn ℝ (Icc 0 frameCap) f)
    (ha : a∈Ico 0 frameCap) (ht : t∈Icc 0 a)
    (hchord : k*(frameCap-a)≤f frameCap-f a) :
    k*(frameCap-t)≤f frameCap-f t := by
  have hgap : 0<frameCap-t := by linarith [ha.2,ht.2]
  obtain ⟨α,hαd⟩ : ∃ α : ℝ,α=(frameCap-a)/(frameCap-t) := ⟨_,rfl⟩
  obtain ⟨β,hβd⟩ : ∃ β : ℝ,β=(a-t)/(frameCap-t) := ⟨_,rfl⟩
  have hα : 0≤α := hαd ▸ div_nonneg (by linarith [ha.2]) hgap.le
  have hβ : 0≤β := hβd ▸ div_nonneg (by linarith [ht.2]) hgap.le
  have hαgap : α*(frameCap-t)=frameCap-a := by rw [hαd,div_mul_cancel₀ _ hgap.ne']
  have hβgap : β*(frameCap-t)=a-t := by rw [hβd,div_mul_cancel₀ _ hgap.ne']
  have hsum : α+β=1 := by
    have h1 : (α+β)*(frameCap-t)=1*(frameCap-t) := by linear_combination hαgap+hβgap
    exact mul_right_cancel₀ hgap.ne' h1
  have hpoint : α*t+β*frameCap=a := by
    have h1 : (α*t+β*frameCap)*(frameCap-t)=a*(frameCap-t) := by
      linear_combination t*hαgap+frameCap*hβgap
    exact mul_right_cancel₀ hgap.ne' h1
  have hh := hc.2
    (show t∈Icc 0 frameCap from ⟨ht.1,ht.2.trans ha.2.le⟩)
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hα hβ hsum
  simp only [smul_eq_mul,hpoint] at hh
  have hh' := mul_le_mul_of_nonneg_right hh hgap.le
  have hclear : (frameCap-a)*f t+(a-t)*f frameCap≤(frameCap-t)*f a := by
    have he : (α*f t+β*f frameCap)*(frameCap-t)=
        (frameCap-a)*f t+(a-t)*f frameCap := by
      calc
        _=(α*(frameCap-t))*f t+(β*(frameCap-t))*f frameCap := by ring
        _=_ := by rw [hαgap,hβgap]
    rw [he] at hh'
    linarith
  have hlast := mul_le_mul_of_nonneg_right hchord hgap.le
  have hfactor : 0≤(frameCap-a)*(f frameCap-f t-k*(frameCap-t)) := by
    nlinarith only [hclear,hlast]
  have hpos : 0<frameCap-a := by linarith [ha.2]
  have hnonneg := (mul_nonneg_iff_of_pos_left hpos).1 hfactor
  linarith

theorem scaled_concave {f : ℝ → ℝ} {b : ℝ}
    (hc : ConcaveOn ℝ (Icc 0 frameCap) f) (hb : 0≤b) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun x => b*f x) := by
  refine ⟨hc.1,?_⟩
  intro x hx y hy a c ha hc' hac
  have h := mul_le_mul_of_nonneg_left (hc.2 hx hy ha hc' hac) hb
  simpa only [smul_eq_mul,mul_add,mul_left_comm] using h

theorem cap_trig :
    (6442176872/10000000000:ℝ)≤Real.sin frameCap ∧
    Real.sin frameCap≤6442176873/10000000000 ∧
    (7648421872/10000000000:ℝ)≤Real.cos frameCap := by
  have hsL := HighOrderTaylor.S15_le_sin (show 0≤frameCap by norm_num [frameCap])
  have hsU := HighOrderTaylor.sin_le_S13 (show 0≤frameCap by norm_num [frameCap])
  have hcL := HighOrderTaylor.C14_le_cos (show 0≤frameCap by norm_num [frameCap])
  norm_num [frameCap,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8]
    at hsL hsU hcL ⊢
  exact ⟨by linarith,by linarith,by linarith⟩

theorem fixed_chords :
    (121/200)*(frameCap-1/5)<(431/500)*
      (V (lowerRadius:ℝ) (117/200) 1 frameCap-V (lowerRadius:ℝ) (117/200) 1 (1/5)) ∧
    (7/10)*(frameCap-7/20)<(923/1000)*
      (V (lowerRadius:ℝ) (13/20) 1 frameCap-V (lowerRadius:ℝ) (13/20) 1 (7/20)) := by
  have hsA := HighOrderTaylor.sin_le_S13 (by norm_num : (0:ℝ)≤1/5)
  have hcA := HighOrderTaylor.cos_le_C16 (by norm_num : (0:ℝ)≤1/5)
  have hsB := HighOrderTaylor.sin_le_S13 (by norm_num : (0:ℝ)≤7/20)
  have hcB := HighOrderTaylor.cos_le_C16 (by norm_num : (0:ℝ)≤7/20)
  have hsA' : Real.sin (1/5:ℝ)≤1986693308/10000000000 := by
    norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7] at hsA
    linarith
  have hcA' : Real.cos (1/5:ℝ)≤9800665779/10000000000 := by
    norm_num [HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
      Arithmetic.cos10,Arithmetic.cos8] at hcA
    linarith
  have hsB' : Real.sin (7/20:ℝ)≤3428978075/10000000000 := by
    norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7] at hsB
    linarith
  have hcB' : Real.cos (7/20:ℝ)≤9393727129/10000000000 := by
    norm_num [HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
      Arithmetic.cos10,Arithmetic.cos8] at hcB
    linarith
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have ha : (1/5:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hb : (7/20:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hnA := root_pos (117/200) (sin_mem ha)
  have hnH := root_pos (117/200) (sin_mem hh)
  have hnA2 := root_sq (117/200) (sin_mem ha)
  have hnH2 := root_sq (117/200) (sin_mem hh)
  have hmB := root_pos (13/20) (sin_mem hb)
  have hmH := root_pos (13/20) (sin_mem hh)
  have hmB2 := root_sq (13/20) (sin_mem hb)
  have hmH2 := root_sq (13/20) (sin_mem hh)
  have hnAL : (1053461856/1000000000:ℝ)≤root (117/200) (Real.sin (1/5)) := by nlinarith
  have hnHU : root (117/200) (Real.sin frameCap)≤767131219/1000000000 := by
    nlinarith [cap_trig.1]
  have hmBL : (988297956/1000000000:ℝ)≤root (13/20) (Real.sin (7/20)) := by nlinarith
  have hmHU : root (13/20) (Real.sin frameCap)≤764864045/1000000000 := by
    nlinarith [cap_trig.1]
  dsimp [V]
  simp only [negativeNorm_normalized (by norm_num : (0:ℝ)<1),div_one,one_mul]
  dsimp [lowerRadius,frameCap] at *
  constructor <;> nlinarith [cap_trig.2.2]

theorem low_growth {R p q nu t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2)
    (hp : 0<p) (hpq : p≤q) (hratio : (117/200)*q≤p)
    (hq : 431/500≤q) (hnu : nu≤q) (ht : t∈Icc 0 (1/5:ℝ)) :
    (121/200)*(frameCap-t)≤Vnu R p q nu frameCap-Vnu R p q nu t := by
  have hconc := scaled_concave (V_concave (R := (lowerRadius:ℝ)) (q := 1)
    (by norm_num [lowerRadius]) (by norm_num [lowerRadius,qCap]) (by norm_num : (0:ℝ)<117/200)
    (by norm_num) (by norm_num)) (by norm_num : (0:ℝ)≤431/500)
  have ht2 : t≤1/5 := ht.2
  have ha : (1/5:ℝ)∈Ico 0 frameCap := ⟨by norm_num,by norm_num [frameCap]⟩
  have hch := extend_terminal_chord hconc ha ht (k := 121/200) (by
    have h := fixed_chords.1.le
    simp only [mul_sub] at h ⊢
    exact h)
  have hlen : 0≤frameCap-t := by simp only [frameCap]; linarith
  have hv0 : 0≤V (lowerRadius:ℝ) (117/200) 1 frameCap-V (lowerRadius:ℝ) (117/200) 1 t := by
    nlinarith [mul_nonneg (by norm_num : (0:ℝ)≤121/200) hlen]
  have hscale := mul_le_mul_of_nonneg_right hq hv0
  have htransfer := normalized_growth (u := frameCap) (radius_le hR hQL) hp hpq (by norm_num)
    hratio hnu ⟨ht.1,by simp only [frameCap]; linarith⟩
    (by norm_num [frameCap]) (by simp only [frameCap]; linarith)
  linarith

theorem middle_growth {R p q nu t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2)
    (hp : 0<p) (hpq : p≤q) (hratio : (13/20)*q≤p)
    (hq : 923/1000≤q) (hnu : nu≤q) (ht : t∈Icc 0 (7/20:ℝ)) :
    (7/10)*(frameCap-t)≤Vnu R p q nu frameCap-Vnu R p q nu t := by
  have hconc := scaled_concave (V_concave (R := (lowerRadius:ℝ)) (q := 1)
    (by norm_num [lowerRadius]) (by norm_num [lowerRadius,qCap]) (by norm_num : (0:ℝ)<13/20)
    (by norm_num) (by norm_num)) (by norm_num : (0:ℝ)≤923/1000)
  have ht2 : t≤7/20 := ht.2
  have ha : (7/20:ℝ)∈Ico 0 frameCap := ⟨by norm_num,by norm_num [frameCap]⟩
  have hch := extend_terminal_chord hconc ha ht (k := 7/10) (by
    have h := fixed_chords.2.le
    simp only [mul_sub] at h ⊢
    exact h)
  have hlen : 0≤frameCap-t := by simp only [frameCap]; linarith
  have hv0 : 0≤V (lowerRadius:ℝ) (13/20) 1 frameCap-V (lowerRadius:ℝ) (13/20) 1 t := by
    nlinarith [mul_nonneg (by norm_num : (0:ℝ)≤7/10) hlen]
  have hscale := mul_le_mul_of_nonneg_right hq hv0
  have htransfer := normalized_growth (u := frameCap) (radius_le hR hQL) hp hpq (by norm_num)
    hratio hnu ⟨ht.1,by simp only [frameCap]; linarith⟩
    (by norm_num [frameCap]) (by simp only [frameCap]; linarith)
  linarith

theorem DE_A_endpoint {R p q : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2)
    (hp : 113/200≤p) (hq : 0<q)
    (hr : p/q∈Icc (533/1000:ℝ) (81/100)) :
    (18/25:ℝ)<VnuDeriv R p q p frameCap := by
  obtain ⟨r,hrd⟩ : ∃ r : ℝ,r=p/q := ⟨_,rfl⟩
  rw [← hrd] at hr
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hN := root_pos r (sin_mem hh)
  have hN2 := root_sq r (sin_mem hh)
  have hr0 : 0≤r := by linarith [hr.1]
  have hproduct := mul_nonneg (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2)
  have hsin := mul_le_mul_of_nonneg_left cap_sin_lower.le hr0
  have hNupper : root r (Real.sin frameCap)≤157/200 := by
    have hsq : (root r (Real.sin frameCap))^2≤(157/200)^2 := by nlinarith
    exact (pow_le_pow_iff_left₀ hN.le (by norm_num) (by norm_num)).1 hsq
  have hc := (transport_trig hh).1.le
  have hs := (transport_trig hh).2.2.2.1.le
  have hLR : (lowerRadius:ℝ)=19787/10000 := by norm_num [lowerRadius]
  have hnum : (19787/10000:ℝ)*(478/625)≤R*Real.cos frameCap := by
    have h1 := radius_le hR hQL
    rw [hLR] at h1
    exact mul_le_mul h1 (by linarith) (by norm_num) hR
  obtain ⟨k,hkd⟩ : ∃ k : ℝ,k=(19787/10000)*(478/625)/(157/200) := ⟨_,rfl⟩
  have hk0 : 0≤k := by rw [hkd]; norm_num
  have hprod := mul_le_mul_of_nonneg_left hNupper hk0
  have hfraction : k≤R*Real.cos frameCap/root r (Real.sin frameCap) := by
    apply (le_div_iff₀ hN).2
    have hk' : k*(157/200)=(19787/10000)*(478/625) := by rw [hkd]; norm_num
    linarith
  have hbracket : k-6443/10000≤
      -Real.sin frameCap+R*Real.cos frameCap/root r (Real.sin frameCap) := by linarith
  have hpositive : 0≤k-6443/10000 := by rw [hkd]; norm_num
  have hmul := mul_le_mul hp hbracket hpositive (by linarith : 0≤p)
  have hreserve : (18/25:ℝ)<(113/200)*(k-6443/10000) := by rw [hkd]; norm_num
  have he : VnuDeriv R p q p frameCap=
      p*(-Real.sin frameCap+R*Real.cos frameCap/root r (Real.sin frameCap)) := by
    simp only [VnuDeriv,normD1,pairProduct]
    rw [Real.cos_neg,negativeNorm_normalized hq,hrd]
    field_simp
  rw [he]
  exact hreserve.trans_le hmul

theorem DE_A_growth {R p q t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 113/200≤p) (hpq : p≤q)
    (hr : p/q∈Icc (533/1000:ℝ) (81/100))
    (ht : t∈Icc 0 frameCap) :
    (18/25)*(frameCap-t)≤Vnu R p q p frameCap-Vnu R p q p t := by
  have hp0 : 0<p := by linarith
  have hq := hp0.trans_le hpq
  have hqp : q≤2*p := by
    have hh := (le_div_iff₀ hq).1 hr.1
    nlinarith
  have hanti := VnuDeriv_antitone hR hQU hp0 hpq hqp (le_refl p)
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  apply derivative_reserve
    (fun x hx => (Vnu_hasDerivAt hp0 hq hx).continuousAt.continuousWithinAt)
    (fun x hx => Vnu_hasDerivAt hp0 hq (Ioo_subset_Icc_self hx))
    (fun x hx => ?_) ht hh ht.2
  exact (DE_A_endpoint hR hQL hp hq hr).le.trans
    (hanti (Ioo_subset_Icc_self hx) hh hx.2.le)

end SquaresInCircles.Eight.SolePositiveTGrowth
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleOrdinaryData
open SoleECoefficients SoleLowCoefficientBounds SoleLowChargeBounds
open SingleAngleConcavity OrdinaryAngleConcavity PositiveAngularEnvelope

def alpha (b : Band) (de : Bool) (t _x e : ℝ) : Fin 4 → ℝ :=
  ![if de then r b e else 1,ell b t,ell b t,if de then 1 else p b t e]
def beta (b : Band) (t x : ℝ) : Fin 4 → ℝ := ![n b t x,k b t,c b t,c b t]
def small (b : Band) (de : Bool) (t x e : ℝ) (i : Fin 4) : ℝ :=
  min (alpha b de t x e i) (beta b t x i)
def large (b : Band) (de : Bool) (t x e : ℝ) (i : Fin 4) : ℝ :=
  max (alpha b de t x e i) (beta b t x i)
def single (de : Bool) : Fin 4 → Bool := ![!de,true,false,false]
def nu (b : Band) (de : Bool) (t x e : ℝ) : Fin 4 → ℝ :=
  ![if de then large b de t x e 0 else n b t x,ell b t,c b t,large b de t x e 3]

theorem alpha_beta_pos {b : Band} {de : Bool} {t x e : ℝ}
    (ht : t∈domain b) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    0<alpha b de t x e i ∧ 0<beta b t x i := by
  obtain ⟨hk,hl,hc,hg,heta⟩ := SoleECoefficients.positive ht
  obtain ⟨hn,hp,hr⟩ := weights_positive ht hx he
  fin_cases i <;> cases de <;> simp [alpha,beta,hk,hl,hc,hn,hp,hr]

theorem small_pos {b : Band} {de : Bool} {t x e : ℝ}
    (ht : t∈domain b) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    0<small b de t x e i := by
  exact lt_min (alpha_beta_pos (de := de) ht hx he i).1 (alpha_beta_pos (de := de) ht hx he i).2

theorem small_le_large (b : Band) (de : Bool) (t x e : ℝ) (i : Fin 4) :
    small b de t x e i≤large b de t x e i := min_le_max

theorem ell_le_k_c {b : Band} {t : ℝ} (ht : t∈domain b) :
    ell b t≤k b t ∧ ell b t≤c b t := by
  cases b
  · have hb := low_bounds ht
    exact ⟨hb.2.2.2.2.2.2.1.le,hb.2.2.2.2.2.2.1.le.trans hb.2.2.1⟩
  · have hb := middle_bounds ht
    exact ⟨hb.2.2.2.2.2.2.1.le,by linarith [hb.2.2.1,hb.2.2.2.2.2.1]⟩
  · have hb := high_bounds ht
    exact ⟨hb.2.2.2.2.2.1.le,by linarith [hb.2.2.1,hb.2.2.2.2.1]⟩

theorem nu_between {b : Band} {de : Bool} {t x e : ℝ}
    (ht : t∈domain b) (i : Fin 4) :
    small b de t x e i≤nu b de t x e i ∧
      nu b de t x e i≤large b de t x e i := by
  have hA := (ell_le_k_c ht).1
  have hB := (ell_le_k_c ht).2
  fin_cases i <;> cases de <;>
    simp [small,large,alpha,beta,nu,hA,hB]

theorem A_data {b : Band} {de : Bool} {t x e : ℝ} (ht : t∈domain b) :
    small b de t x e 1=ell b t ∧ large b de t x e 1=k b t ∧
      nu b de t x e 1=ell b t := by
  have hh := (ell_le_k_c ht).1
  simp [small,large,alpha,beta,nu,min_eq_left hh,max_eq_right hh]

theorem B_data {b : Band} {de : Bool} {t x e : ℝ} (ht : t∈domain b) :
    small b de t x e 2=ell b t ∧ large b de t x e 2=c b t ∧
      nu b de t x e 2=c b t := by
  have hh := (ell_le_k_c ht).2
  simp [small,large,alpha,beta,nu,min_eq_left hh,max_eq_right hh]

theorem low_wide {de : Bool} {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) {i : Fin 4} (hi : i=0 ∨ i=3) :
    base≤ small .low de t x e i ∧ large .low de t x e i∈Icc 1 (28/25 : ℝ) := by
  rcases hi with rfl | rfl
  · simpa [small,large,alpha,beta] using wide_pair_H (de := de) ht hx he
  · simpa [small,large,alpha,beta] using wide_pair_D (de := de) ht hx he

theorem low_half_ratio {de : Bool} {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    large .low de t x e i≤2*small .low de t x e i := by
  have hb := low_bounds ht
  fin_cases i
  · show large .low de t x e 0≤2*small .low de t x e 0
    have hw := low_wide (de := de) ht hx he (Or.inl rfl)
    dsimp [base] at hw
    linarith [hw.1,hw.2.2]
  · show large .low de t x e 1≤2*small .low de t x e 1
    rcases A_data (de := de) (x := x) (e := e) ht with ⟨hs,hl,hn⟩
    rw [hs,hl]
    linarith [hb.2.2.1,hb.2.2.2.2.2.2.2.1]
  · show large .low de t x e 2≤2*small .low de t x e 2
    rcases B_data (de := de) (x := x) (e := e) ht with ⟨hs,hl,hn⟩
    rw [hs,hl]
    exact hb.2.2.2.2.2.2.2.1
  · show large .low de t x e 3≤2*small .low de t x e 3
    have hw := low_wide (de := de) ht hx he (Or.inr rfl)
    dsimp [base] at hw
    linarith [hw.1,hw.2.2]

theorem low_large_upper {de : Bool} {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    large .low de t x e i≤1+(7/10)*t := by
  obtain ⟨hk,hl,hc,hn,hp,hr⟩ := coarse_upper ht hx he
  have h1 : (1:ℝ)≤1+(7/10)*t := by linarith [ht.1]
  fin_cases i <;> cases de <;> simp [large,alpha,beta,hk,hl,hc,hn,hp,hr,h1]

end SquaresInCircles.Eight.SoleOrdinaryData
end
end
end
