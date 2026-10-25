module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3LongCertificates
public import SquaresInCircles.Eight.Owners.GA.Negative.ALongECertificates
public import SquaresInCircles.Eight.Owners.GA.Negative.ALongESourceData
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNorms
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsPolynomial
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LargeBounds
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LargePolynomial

/-!
# Eight squares: radical transfer for all twelve BT3 longer-E endpoints

The nonradical charge and gain bounds
are the previously proved ones. The three possible negative norms
have the fixed H/G/B coefficients, while only D's zero-angle norm
uses the upper bound on the actual positive rotating coefficient.
-/

section
/-!
## Positivity on all four longer-E BT3 domains

TE uses the positive base and its decreasing
positive quotient. TC is a single whole-triangle certificate. RE uses
concavity and its three actual boundary curves; RC uses its positive
base and quotient. Every weak endpoint remains in its native domain.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE.Certificate
open NegativeA.LongE (Region)
open TensorWholeIntervalPolynomial TwoVariablePolynomial

theorem mass_positive (r : Region) (i : Fin 3) (j : Fin 4)
    {x y : ℝ} (hd : Explicit.Domain r x y) : 0<evaluate x y (mass r i j) := by
  have hh := positive_on_domain (mass_certificate r i j).1 (mass_certificate r i j).2 hd
  have hr : (0:ℝ)<(massReserve r:ℝ) := by cases r <;> norm_num [massReserve]
  exact hr.trans hh

theorem TEfar_positive (i : Fin 3) {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) :
    0<aeval x (TEfar i) := by
  have hc := TEfar_certificate i
  have hh := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<8/15) hc.1 hc.2 (x:=x) (by push_cast; exact hx)
  have hr : (0:ℝ)<(TEfarReserve i:ℝ) := by fin_cases i <;> norm_num [TEfarReserve]
  exact hr.trans hh

theorem TEquotient_antitone (i : Fin 3) {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) :
    AntitoneOn (fun y => evaluate x y (TEquotient i)) (Icc 0 (8/15-x)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun y _ => (hasDerivAt_Y (TEquotient i) x y).continuousAt.continuousWithinAt)
    (fun y _ => hasDerivAt_Y (TEquotient i) x y)
  intro y hy
  have hh := upper_on_domain (TEderivative_certificate i).1 (TEderivative_certificate i).2
    (show Explicit.Domain .TE x y from ⟨hx.1,hy.1.le,by linarith [hy.2]⟩)
  have hr : (TEderivativeReserve i:ℝ)<0 := by fin_cases i <;> norm_num [TEderivativeReserve]
  exact (hh.trans hr).le

theorem TE_positive (i : Fin 3) {x y : ℝ} (hd : Explicit.Domain .TE x y) :
    0<evaluate x y (numerator .TE i) := by
  have hx : x∈Icc 0 (8/15:ℝ) := ⟨hd.1,by linarith [hd.2.1,hd.2.2]⟩
  have hy : y∈Icc 0 (8/15-x) := ⟨hd.2.1,by linarith [hd.2.2]⟩
  have hm : evaluate x (8/15-x) (TEquotient i)≤evaluate x y (TEquotient i) :=
    TEquotient_antitone i hx hy
      (show 8/15-x∈Icc 0 (8/15-x) from ⟨by linarith [hx.2],le_rfl⟩) hy.2
  have he : aeval x (TEfar i)=evaluate x (8/15-x) (TEquotient i) := by
    simp [TEfar,evaluate_restrict]
  rw [←he] at hm
  have hq := (TEfar_positive i hx).trans_le hm
  have hbase := PositiveBT3.LargeCertificate.triangle_base_positive i hx
  rw [←TEbase_identity i] at hbase
  have hidentity := divY_identity (numerator .TE i) x y
  rw [←TwoVariablePolynomial.evaluate_baseY] at hidentity
  change evaluate x y (numerator .TE i)=aeval x (TEbase i)+y*evaluate x y (TEquotient i)
    at hidentity
  linarith [mul_nonneg hd.2.1 hq.le]

theorem TC_positive (i : Fin 3) {x y : ℝ} (hd : Explicit.Domain .TC x y) :
    0<evaluate x y (numerator .TC i) := by
  have hh := positive_on_domain (TC_certificate i).1 (TC_certificate i).2 hd
  have hr : (0:ℝ)<(TCreserve i:ℝ) := by fin_cases i <;> norm_num [TCreserve]
  exact hr.trans hh

theorem REboundary_positive (i j : Fin 3) {t : ℝ} (ht : t∈Icc 0 (RElength j:ℝ)) :
    0<aeval t (REboundary i j) := by
  have hlen : (0:ℚ)<RElength j := by fin_cases j <;> norm_num [RElength]
  have hh := WholeIntervalPolynomial.positive_on_interval hlen
    (REboundary_certificate i j).1 (REboundary_certificate i j).2 (x:=t) (by push_cast; exact ht)
  have hr : (0:ℝ)<(REreserve i j:ℝ) := by fin_cases i <;> fin_cases j <;> norm_num [REreserve]
  exact hr.trans hh

theorem REconcave (i : Fin 3) {y : ℝ} (hy : y∈Icc 0 (19/50:ℝ)) :
    ConcaveOn ℝ (Icc 0 (min (1/6) (19/50-y)))
      (fun x => evaluate x y (numerator .RE i)) := by
  apply concave_of_deriv2
    (fun x _ => hasDerivAt_X (numerator .RE i) x y)
    (fun x _ => hasDerivAt_X (numerator .RE i).derivative x y)
  intro x hx
  have hd : Explicit.Domain .RE x y :=
    ⟨⟨hx.1,(le_min_iff.mp hx.2).1⟩,⟨hy.1,by linarith [(le_min_iff.mp hx.2).2]⟩⟩
  have hh := upper_on_domain (REcurvature_certificate i).1 (REcurvature_certificate i).2 hd
  have hr : (REcurvatureReserve i:ℝ)<0 := by fin_cases i <;> norm_num [REcurvatureReserve]
  exact (hh.trans hr).le

theorem RE_positive (i : Fin 3) {x y : ℝ} (hd : Explicit.Domain .RE x y) :
    0<evaluate x y (numerator .RE i) := by
  have hy : y∈Icc 0 (19/50:ℝ) := ⟨hd.2.1,by linarith [hd.1.1,hd.2.2]⟩
  have hx : x∈Icc 0 (min (1/6:ℝ) (19/50-y)) :=
    ⟨hd.1.1,le_min hd.1.2 (by linarith [hd.2.2])⟩
  have hleft : 0<evaluate 0 y (numerator .RE i) := by
    have hy' : y∈Icc 0 (RElength 0:ℝ) := ⟨hy.1,by norm_num [RElength]; linarith [hy.2]⟩
    simpa [REboundary,evaluate_restrict] using REboundary_positive i 0 hy'
  have hright : 0<evaluate (min (1/6:ℝ) (19/50-y)) y (numerator .RE i) := by
    rcases le_total (1/6:ℝ) (19/50-y) with hh|hh
    · rw [min_eq_left hh]
      have hy' : y∈Icc 0 (RElength 1:ℝ) := ⟨hy.1,by norm_num [RElength]; linarith⟩
      simpa [REboundary,evaluate_restrict] using REboundary_positive i 1 hy'
    · rw [min_eq_right hh]
      have ht : 19/50-y∈Icc 0 (RElength 2:ℝ) :=
        ⟨by linarith [hy.2],by norm_num [RElength]; linarith⟩
      simpa [REboundary,evaluate_restrict] using REboundary_positive i 2 ht
  exact concave_gt_of_endpoints (REconcave i hy) hx hleft hright

theorem RC_positive (i : Fin 3) {x y : ℝ} (hd : Explicit.Domain .RC x y) :
    0<evaluate x y (numerator .RC i) := by
  have hbase := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<1/6) (RCbase_certificate i).1 (RCbase_certificate i).2 (x:=x)
    (by push_cast; exact hd.1)
  have hq := positive_on_domain (RCquotient_certificate i).1 (RCquotient_certificate i).2 hd
  have hr0 : (0:ℝ)<((2209/100000:ℚ):ℝ) := by norm_num
  have hr1 : (0:ℝ)<(RCquotientReserve i:ℝ) := by fin_cases i <;> norm_num [RCquotientReserve]
  have hb0 := hr0.trans hbase
  have hq0 := hr1.trans hq
  have hid := divY_identity (numerator .RC i) x y
  rw [←TwoVariablePolynomial.evaluate_baseY] at hid
  change evaluate x y (numerator .RC i)=aeval x (RCbase i)+y*evaluate x y (RCquotient i) at hid
  linarith [mul_nonneg hd.2.1 hq0.le]

/-- All twelve polynomials have strict positive values on their entire
native domains, without an endpoint-reserve premise. -/
theorem numerator_positive (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) : 0<evaluate x y (numerator r i) := by
  cases r
  · exact TE_positive i hd
  · exact TC_positive i hd
  · exact RE_positive i hd
  · exact RC_positive i hd

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE.Certificate
end
end
end

section
/-!
## Strict positivity on the longer-E domains

The triangle TE uses a decreasing quotient and a single completed square; RE uses concavity on the
interval of its variable. The closed domains keep all their boundary points
(`numerator_positive`).
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeA.LongE.Certificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial

theorem mass_positive (r : Region) (i : Fin 3) (j : Fin 4)
    {x y : ℝ} (hd : Explicit.Domain r x y) : 0<evaluate x y (mass r i j) := by
  have hh := positive_on_domain (mass_certificate r i j).1 (mass_certificate r i j).2 hd
  have hr : (0:ℝ)<(massReserve r:ℝ) := by cases r <;> norm_num [massReserve]
  exact hr.trans hh

theorem TEfar_tail {u : ℝ} (hu : |u|≤4/15) (j : Fin 37) :
    -(|(TEcoefficient (j.val+3):ℝ)| *(4/15)^(j.val+1))*u^2≤
      (TEcoefficient (j.val+3):ℝ)*u^(j.val+3) := by
  have hp := pow_le_pow_left₀ (abs_nonneg u) hu (j.val+1)
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (TEcoefficient (j.val+3):ℝ))
  have hh : |(TEcoefficient (j.val+3):ℝ)*u^(j.val+1)|≤
      |(TEcoefficient (j.val+3):ℝ)| * (4/15)^(j.val+1) := by
    simpa [abs_mul,abs_pow] using hm
  have hscaled := mul_le_mul_of_nonneg_right (abs_le.mp hh).1 (sq_nonneg u)
  rw [show u^(j.val+3)=u^(j.val+1)*u^2 by ring]
  nlinarith

theorem TEfar_H_positive {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) :
    (47/1000:ℝ)<aeval x (TEfar 0) := by
  let u : ℝ := x-4/15
  have hu : |u|≤4/15 := by apply abs_le.mpr; dsimp [u]; constructor <;> linarith [hx.1,hx.2]
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => TEfar_tail hu j)
  have he : (∑j : Fin 37,-(|(TEcoefficient (j.val+3):ℝ)| * (4/15)^(j.val+1))*u^2)=
      -(TEtail:ℝ)*u^2 := by simp [TEtail,Finset.sum_mul,Finset.sum_neg_distrib]
  rw [he] at hsum
  have hid := congrArg (fun p : ℚ[X] => aeval u p) TEfar_H_certificate.1
  simp only [map_add,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at hid
  have hlower : (TEcoefficient 0:ℝ)+(TEcoefficient 1:ℝ)*u+
      (TEcurvature:ℝ)*u^2≤aeval u TEcentered := by
    dsimp [TEcurvature]; push_cast; linarith
  have hκ : (0:ℝ)<(TEcurvature:ℝ) := by
    have hh := Rat.cast_lt (K:=ℝ).mpr TEfar_H_certificate.2.1
    push_cast at hh
    linarith
  have hmin := ChebyshevLeadingBounds.quadratic_min
    (a:=(TEcoefficient 0:ℝ)) (b:=(TEcoefficient 1:ℝ)) (x:=u) hκ
  have hreserve : (47/1000:ℝ)<(TEcoefficient 0:ℝ)-(TEcoefficient 1:ℝ)^2/(4*(TEcurvature:ℝ)) := by
    have hh := Rat.cast_lt (K:=ℝ).mpr TEfar_H_certificate.2.2
    push_cast at hh
    exact hh
  have hvalue : aeval u TEcentered=aeval x (TEfar 0) := by simp [TEcentered,aeval_comp,u]
  rw [hvalue] at hlower
  linarith

theorem TEfar_positive (i : Fin 3) {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) :
    0<aeval x (TEfar i) := by
  by_cases hi : i=0
  · subst i; linarith [TEfar_H_positive hx]
  · have hic : i=1∨i=2 := by fin_cases i <;> simp_all
    have hc := TEfar_GB_certificate i hic
    have hh := WholeIntervalPolynomial.positive_on_interval
      (by norm_num : (0:ℚ)<8/15) hc.1 hc.2 (x:=x) (by push_cast; exact hx)
    have hr : (0:ℝ)<(TEfarReserve i:ℝ) := by fin_cases i <;> norm_num [TEfarReserve]
    exact hr.trans hh

theorem TEquotient_antitone (i : Fin 3) {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) :
    AntitoneOn (fun y => evaluate x y (TEquotient i)) (Icc 0 (8/15-x)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun y _ => (hasDerivAt_Y (TEquotient i) x y).continuousAt.continuousWithinAt)
    (fun y _ => hasDerivAt_Y (TEquotient i) x y)
  intro y hy
  have hh := upper_on_domain (TEderivative_certificate i).1 (TEderivative_certificate i).2
    (show Explicit.Domain .TE x y from ⟨hx.1,hy.1.le,by linarith [hy.2]⟩)
  have hr : (TEderivativeReserve i:ℝ)<0 := by fin_cases i <;> norm_num [TEderivativeReserve]
  exact (hh.trans hr).le

theorem TE_positive (i : Fin 3) {x y : ℝ} (hd : Explicit.Domain .TE x y) :
    0<evaluate x y (numerator .TE i) := by
  have hx : x∈Icc 0 (8/15:ℝ) := ⟨hd.1,by linarith [hd.2.1,hd.2.2]⟩
  have hy : y∈Icc 0 (8/15-x) := ⟨hd.2.1,by linarith [hd.2.2]⟩
  have hm : evaluate x (8/15-x) (TEquotient i)≤evaluate x y (TEquotient i) :=
    TEquotient_antitone i hx hy
      (show 8/15-x∈Icc 0 (8/15-x) from ⟨by linarith [hx.2],le_rfl⟩) hy.2
  have he : aeval x (TEfar i)=evaluate x (8/15-x) (TEquotient i) := by
    simp [TEfar,evaluate_restrict]
  rw [←he] at hm
  have hq := (TEfar_positive i hx).trans_le hm
  have hbase := NonnegativeTotals.Certificate.triangle_base_positive .atT i hx
  rw [←TEbase_identity i] at hbase
  have hidentity := divY_identity (numerator .TE i) x y
  rw [←TwoVariablePolynomial.evaluate_baseY] at hidentity
  change evaluate x y (numerator .TE i)=aeval x (TEbase i)+y*evaluate x y (TEquotient i)
    at hidentity
  linarith [mul_nonneg hd.2.1 hq.le]

theorem TC_positive (i : Fin 3) {x y : ℝ} (hd : Explicit.Domain .TC x y) :
    0<evaluate x y (numerator .TC i) := by
  have hh := positive_on_domain (TC_certificate i).1 (TC_certificate i).2 hd
  have hr : (0:ℝ)<(TCreserve i:ℝ) := by fin_cases i <;> norm_num [TCreserve]
  exact hr.trans hh

theorem REboundary_positive (i j : Fin 3) {t : ℝ} (ht : t∈Icc 0 (RElength j:ℝ)) :
    0<aeval t (REboundary i j) := by
  have hlen : (0:ℚ)<RElength j := by fin_cases j <;> norm_num [RElength]
  have hh := WholeIntervalPolynomial.positive_on_interval hlen
    (REboundary_certificate i j).1 (REboundary_certificate i j).2 (x:=t) (by push_cast; exact ht)
  have hr : (0:ℝ)<(REreserve i j:ℝ) := by fin_cases i <;> fin_cases j <;> norm_num [REreserve]
  exact hr.trans hh

theorem REconcave (i : Fin 3) {y : ℝ} (hy : y∈Icc 0 (19/50:ℝ)) :
    ConcaveOn ℝ (Icc 0 (min (1/6) (19/50-y)))
      (fun x => evaluate x y (numerator .RE i)) := by
  apply concave_of_deriv2
    (fun x _ => hasDerivAt_X (numerator .RE i) x y)
    (fun x _ => hasDerivAt_X (numerator .RE i).derivative x y)
  intro x hx
  have hd : Explicit.Domain .RE x y :=
    ⟨⟨hx.1,(le_min_iff.mp hx.2).1⟩,⟨hy.1,by linarith [(le_min_iff.mp hx.2).2]⟩⟩
  have hh := upper_on_domain (REcurvature_certificate i).1 (REcurvature_certificate i).2 hd
  have hr : (REcurvatureReserve i:ℝ)<0 := by fin_cases i <;> norm_num [REcurvatureReserve]
  exact (hh.trans hr).le

theorem RE_positive (i : Fin 3) {x y : ℝ} (hd : Explicit.Domain .RE x y) :
    0<evaluate x y (numerator .RE i) := by
  have hy : y∈Icc 0 (19/50:ℝ) := ⟨hd.2.1,by linarith [hd.1.1,hd.2.2]⟩
  have hx : x∈Icc 0 (min (1/6:ℝ) (19/50-y)) :=
    ⟨hd.1.1,le_min hd.1.2 (by linarith [hd.2.2])⟩
  have hleft : 0<evaluate 0 y (numerator .RE i) := by
    have hy' : y∈Icc 0 (RElength 0:ℝ) := ⟨hy.1,by norm_num [RElength]; linarith [hy.2]⟩
    simpa [REboundary,evaluate_restrict] using REboundary_positive i 0 hy'
  have hright : 0<evaluate (min (1/6:ℝ) (19/50-y)) y (numerator .RE i) := by
    rcases le_total (1/6:ℝ) (19/50-y) with hh|hh
    · rw [min_eq_left hh]
      have hy' : y∈Icc 0 (RElength 1:ℝ) := ⟨hy.1,by norm_num [RElength]; linarith⟩
      simpa [REboundary,evaluate_restrict] using REboundary_positive i 1 hy'
    · rw [min_eq_right hh]
      have ht : 19/50-y∈Icc 0 (RElength 2:ℝ) :=
        ⟨by linarith [hy.2],by norm_num [RElength]; linarith⟩
      simpa [REboundary,evaluate_restrict] using REboundary_positive i 2 ht
  exact concave_gt_of_endpoints (REconcave i hy) hx hleft hright

theorem RC_positive (i : Fin 3) {x y : ℝ} (hd : Explicit.Domain .RC x y) :
    0<evaluate x y (numerator .RC i) := by
  have hbase := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<1/6) (RCbase_certificate i).1 (RCbase_certificate i).2 (x:=x)
    (by push_cast; exact hd.1)
  have hq := positive_on_domain (RCquotient_certificate i).1 (RCquotient_certificate i).2 hd
  have hr0 : (0:ℝ)<(RCbaseReserve i:ℝ) := by fin_cases i <;> norm_num [RCbaseReserve]
  have hr1 : (0:ℝ)<(RCquotientReserve i:ℝ) := by fin_cases i <;> norm_num [RCquotientReserve]
  have hb0 := hr0.trans hbase
  have hq0 := hr1.trans hq
  have hid := divY_identity (numerator .RC i) x y
  rw [←TwoVariablePolynomial.evaluate_baseY] at hid
  change evaluate x y (numerator .RC i)=aeval x (RCbase i)+y*evaluate x y (RCquotient i) at hid
  linarith [mul_nonneg hd.2.1 hq0.le]

/-- All twelve polynomials are strictly positive on their whole native domains, with no reserve
assumed at the endpoints. -/
theorem numerator_positive (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) : 0<evaluate x y (numerator r i) := by
  cases r
  · exact TE_positive i hd
  · exact TC_positive i hd
  · exact RE_positive i hd
  · exact RC_positive i hd

end SquaresInCircles.Eight.GlobalGA.NegativeA.LongE.Certificate
end
end
end

section
/-!
## The twelve longer-E endpoint scalars

The B norm is enlarged
only after its actual coefficient exceeds l sin(delta). The same four
positive masses then transfer each exact numerator to its radical scalar.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeA.LongE
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open TensorWholeIntervalPolynomial TwoVariablePolynomial

def scalar (k l c z e s : ℝ) (i : Fin 3) : ℝ :=
  NonnegativeTotals.Analytic.fullBaseline k l c z+l*gain s+
    TwoPositive.ASupport.charge e+
      NonnegativeTotals.Analytic.negative k l (PositiveTD.tilted c z) (z+e-s) i

namespace Analytic

def endpoint (r : Region) (i : Fin 3) (x y : ℝ) : ℝ :=
  scalar (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
    (Explicit.z r x y) (Explicit.e r x y) (Explicit.s r x y) i
def pAt (r : Region) (x y : ℝ) : Fin 4 → ℝ :=
  ![Explicit.k r x y,Explicit.k r x y,Explicit.l r x y,Explicit.c r x y]
def qAt (r : Region) (x y : ℝ) : Fin 4 → ℝ :=
  ![1,Explicit.l r x y,PositiveTD.tilted (Explicit.c r x y) (Explicit.z r x y),1]
def largeCoefficient (r : Region) (x y : ℝ) : Fin 3 → ℝ :=
  ![1,Explicit.l r x y,max (Explicit.l r x y) (PositiveTD.tilted (Explicit.c r x y) (Explicit.z r x y))]
def normAt (r : Region) (i : Fin 3) (j : Fin 4) (x y : ℝ) : ℝ :=
  pairNorm (pAt r x y j) (qAt r x y j) (if j.val=i.val then -Explicit.delta r x y else 0)
def nonradicalBase (r : Region) (x y : ℝ) : ℝ :=
  2*Explicit.k r x y+3*Explicit.l r x y+3+
    Explicit.c r x y*(1+2*Real.cos (Explicit.z r x y)+
      ((3/2)*PositiveTD.eta+1/2-PositiveTD.sigma)*Real.sin (Explicit.z r x y))+
      TwoPositive.ASupport.charge (Explicit.e r x y)+Explicit.l r x y*gain (Explicit.s r x y)
def nonradical (r : Region) (i : Fin 3) (x y : ℝ) : ℝ :=
  nonradicalBase r x y+largeCoefficient r x y i*(Real.cos (Explicit.delta r x y)-1)

theorem endpoint_identity (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) :
    endpoint r i x y=nonradical r i x y-
      R*(normAt r i 0 x y+normAt r i 1 x y+normAt r i 2 x y+normAt r i 3 x y) := by
  have hz := (Explicit.domains hd).1
  unfold endpoint scalar
  rw [NonnegativeTotals.Analytic.fullBaseline_norms,NonnegativeTotals.Analytic.negative_identity,
    edgeWidth_positive_formula hz]
  fin_cases i <;>
    simp [nonradical,nonradicalBase,largeCoefficient,normAt,pAt,qAt,
      PositiveTD.tilted,Explicit.delta] <;> ring

theorem coefficient_data (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    NonnegativeTotals.Explicit.BaseBounds (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) :=
  NonnegativeTotals.Explicit.base_bounds (Explicit.baseRegion r) (Explicit.base_domain hd)

theorem m_data (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    0<PositiveTD.tilted (Explicit.c r x y) (Explicit.z r x y) ∧
    PositiveTD.tilted (Explicit.c r x y) (Explicit.z r x y)≤evaluate x y (Certificate.M r) ∧
    (2/3)*Explicit.l r x y<PositiveTD.tilted (Explicit.c r x y) (Explicit.z r x y) := by
  have hh := NonnegativeTotals.Analytic.mAt_data (Explicit.baseRegion r) .atT (Explicit.base_domain hd)
  simpa [NonnegativeTotals.Analytic.mAt,NonnegativeTotals.Analytic.zAt,
    NonnegativeTotals.Analytic.polyM,NonnegativeTotals.Certificate.M,
    Certificate.M,Explicit.z,Explicit.c,Explicit.l] using hh

theorem qB_envelope (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    max (Explicit.l r x y) (PositiveTD.tilted (Explicit.c r x y) (Explicit.z r x y))≤
      evaluate x y (Certificate.qB r) := by
  have hh := NonnegativeTotals.Analytic.qB_envelope (Explicit.baseRegion r) .atT (Explicit.base_domain hd)
  cases r <;>
    simpa [Certificate.qB,Certificate.M,Explicit.baseRegion,Explicit.baseY,
      Explicit.z,Explicit.c,Explicit.l,NonnegativeTotals.Certificate.qB,
      NonnegativeTotals.Certificate.M,NonnegativeTotals.Certificate.qStar,
      NonnegativeTotals.Analytic.mAt,NonnegativeTotals.Analytic.zAt] using hh

theorem E_charge (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    evaluate x y (Certificate.jE r)≤TwoPositive.ASupport.charge (Explicit.e r x y) := by
  have he := (Explicit.domains hd).2.1
  cases r with
  | TE =>
    have hh := NonnegativeTotals.Charges.triangle_E_charge
      (show Explicit.e .TE x y∈Icc 0 (8/15:ℝ) from
        ⟨he.1,(by
          dsimp [Explicit.e,Explicit.baseRegion,Explicit.baseY,NonnegativeTotals.Explicit.e]
          linarith [hd.1,hd.2.2])⟩)
    simpa only [Certificate.jE,map_sub,map_mul,map_pow,evaluate_scalar,
      NonnegativeTotals.Charges.evaluate_J,Certificate.evaluate_e,Rat.cast_div,Rat.cast_one,
      Rat.cast_ofNat] using hh
  | TC =>
    have hh := NonnegativeTotals.Charges.triangle_E_charge
      (show Explicit.e .TC x y∈Icc 0 (8/15:ℝ) from
        ⟨he.1,(by
          dsimp [Explicit.e,Explicit.baseRegion,Explicit.baseY,NonnegativeTotals.Explicit.e]
          linarith [hd.1,hd.2.2])⟩)
    simpa only [Certificate.jE,map_sub,map_mul,map_pow,evaluate_scalar,
      NonnegativeTotals.Charges.evaluate_J,Certificate.evaluate_e,Rat.cast_div,Rat.cast_one,
      Rat.cast_ofNat] using hh
  | RE =>
    have hcut : Explicit.e .RE x y≤TwoPositive.ASupport.alpha := by
      dsimp [Explicit.e,Explicit.baseRegion,Explicit.baseY,NonnegativeTotals.Explicit.e]
      linarith [hd.2.2,TwoPositive.ASupport.alpha_bounds.1]
    rw [TwoPositive.ASupport.charge]
    simp only [hcut,↓reduceIte]
    simpa [Certificate.jE,NonnegativeTotals.Charges.evaluate_J] using
      NonnegativeTotals.Charges.J_lower_axial he
  | RC =>
    simpa only [Certificate.jE,map_sub,map_mul,map_pow,evaluate_scalar,
      NonnegativeTotals.Charges.evaluate_J,Certificate.evaluate_e,Rat.cast_div,Rat.cast_one,
      Rat.cast_ofNat] using
        NonnegativeTotals.Charges.rectangle_E_charge he

theorem nonradicalBase_lower (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    evaluate x y (Certificate.ABase r)≤nonradicalBase r x y := by
  have hb := coefficient_data r hd
  have hz := (Explicit.domains hd).1
  have ht := PositiveTD.Certificate.taylor_bounds hz
  have hE := E_charge r hd
  have hg := mul_le_mul_of_nonneg_left (polynomial_gain_lower (Explicit.domains hd).2.2.1) hb.l_positive.le
  have hcoeff : (3/2)*(293/1000:ℝ)+1/2-(NonnegativeTotals.Certificate.sigmabar:ℝ)≤0 := by
    norm_num [NonnegativeTotals.Certificate.sigmabar]
  have hsin := mul_le_mul_of_nonpos_left ht.2.2.1 hcoeff
  have hσ := mul_le_mul_of_nonneg_right NonnegativeTotals.Charges.sigma_upper (transport_trig hz).2.2.1
  have hinner : 1+2*aeval (Explicit.z r x y) PositiveTD.Certificate.C10+
      ((3/2)*(293/1000)+1/2-(NonnegativeTotals.Certificate.sigmabar:ℝ))*
        aeval (Explicit.z r x y) PositiveTD.Certificate.S9≤
      1+2*Real.cos (Explicit.z r x y)+
        ((3/2)*PositiveTD.eta+1/2-PositiveTD.sigma)*Real.sin (Explicit.z r x y) := by
    dsimp [PositiveTD.eta]
    linarith [ht.2.2.2.2.1]
  have hprod := mul_le_mul_of_nonneg_left hinner hb.c_positive.le
  simp only [Certificate.ABase,Certificate.gain,map_add,map_mul,map_sub,map_one,
    evaluate_scalar,evaluate_lift,Certificate.evaluate_k,Certificate.evaluate_l,
    Certificate.evaluate_c,Certificate.evaluate_z,Certificate.evaluate_s]
  push_cast
  dsimp [nonradicalBase]
  linarith

theorem largeCoefficient_bounds (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) : 0≤largeCoefficient r x y i ∧
      largeCoefficient r x y i≤evaluate x y (![1,Certificate.l r,Certificate.qB r] i) := by
  have hb := coefficient_data r hd
  fin_cases i
  · simp [largeCoefficient]
  · simpa [largeCoefficient] using And.intro hb.l_positive.le (le_refl (Explicit.l r x y))
  · exact ⟨hb.l_positive.le.trans (le_max_left _ _),qB_envelope r hd⟩

theorem nonradical_lower (r : Region) (i : Fin 3) {x y : ℝ} (hd : Explicit.Domain r x y) :
    evaluate x y (Certificate.A r i)≤nonradical r i x y := by
  have hδ := (Explicit.domains hd).2.2.2.2
  have ht := PositiveTD.Certificate.taylor_bounds hδ
  have hC : aeval (Explicit.delta r x y) PositiveTD.Certificate.C10-1≤0 := by
    linarith [ht.2.2.2.2.1,Real.cos_le_one (Explicit.delta r x y)]
  have h1 := mul_le_mul_of_nonpos_right (largeCoefficient_bounds r i hd).2 hC
  have h2 := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1)
    (largeCoefficient_bounds r i hd).1
  have hb := nonradicalBase_lower r hd
  simp only [Certificate.A,map_add,map_mul,map_sub,map_one,evaluate_lift,Certificate.evaluate_delta]
  dsimp [nonradical]
  linarith

theorem norm_square_upper (r : Region) (i : Fin 3) (j : Fin 4) {x y : ℝ}
    (hd : Explicit.Domain r x y) : (normAt r i j x y)^2≤evaluate x y (Certificate.P r i j) := by
  have hb := coefficient_data r hd
  have hk : 0<Explicit.k r x y := by linarith [hb.k_lower]
  have hm := m_data r hd
  have hδ := (Explicit.domains hd).2.2.2.2
  have hcharge : Explicit.l r x y*Real.sin (Explicit.delta r x y)≤
      PositiveTD.tilted (Explicit.c r x y) (Explicit.z r x y) := by
    have hh := mul_lt_mul_of_pos_left (transport_trig hδ).2.2.2.1 hb.l_positive
    linarith [hm.2.2,hb.l_positive]
  have h00 := NonnegativeTotals.Analytic.norm_negative_polynomial hk (by norm_num : (0:ℝ)<1) hδ
  have h11 := NonnegativeTotals.Analytic.norm_negative_polynomial hk hb.l_positive hδ
  have h22 := NonnegativeTotals.Analytic.norm_negative_coefficient_upper hb.l_positive hm.1 hm.2.1
    hδ hcharge
  have z0 := NonnegativeTotals.Analytic.norm_zero_square (Explicit.k r x y) 1
  have z1 := NonnegativeTotals.Analytic.norm_zero_square (Explicit.k r x y) (Explicit.l r x y)
  have z2 := NonnegativeTotals.Analytic.norm_zero_coefficient_upper (p:=Explicit.l r x y) hm.1.le hm.2.1
  have z3 := NonnegativeTotals.Analytic.norm_zero_square (Explicit.c r x y) 1
  fin_cases i <;> fin_cases j <;>
    simp [normAt,pAt,qAt,Certificate.P,Certificate.baseNorm,-pairNorm_zero] at h00 h11 h22 z0 z1 z2 z3 ⊢ <;>
    linarith

theorem endpoint_positive (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) : 0<endpoint r i x y := by
  have hm (j : Fin 4) := Certificate.mass_positive r i j hd
  have hn (j : Fin 4) : 0≤normAt r i j x y := Real.sqrt_nonneg _
  have hs (j : Fin 4) := norm_square_upper r i j hd
  have hA := nonradical_lower r i hd
  have hpoly := Certificate.numerator_positive r i hd
  have hP : 0<2*evaluate x y (Certificate.A r i)*
      evaluate x y (Certificate.mass r i 0)*evaluate x y (Certificate.mass r i 1)*
      evaluate x y (Certificate.mass r i 2)*evaluate x y (Certificate.mass r i 3)-
        (PositiveTD.Certificate.Rbar:ℝ)*
          ((evaluate x y (Certificate.P r i 0)+(evaluate x y (Certificate.mass r i 0))^2)*
              evaluate x y (Certificate.mass r i 1)*evaluate x y (Certificate.mass r i 2)*evaluate x y (Certificate.mass r i 3)+
            (evaluate x y (Certificate.P r i 1)+(evaluate x y (Certificate.mass r i 1))^2)*
              evaluate x y (Certificate.mass r i 0)*evaluate x y (Certificate.mass r i 2)*evaluate x y (Certificate.mass r i 3)+
            (evaluate x y (Certificate.P r i 2)+(evaluate x y (Certificate.mass r i 2))^2)*
              evaluate x y (Certificate.mass r i 0)*evaluate x y (Certificate.mass r i 1)*evaluate x y (Certificate.mass r i 3)+
            (evaluate x y (Certificate.P r i 3)+(evaluate x y (Certificate.mass r i 3))^2)*
              evaluate x y (Certificate.mass r i 0)*evaluate x y (Certificate.mass r i 1)*evaluate x y (Certificate.mass r i 2)) := by
    have hRbar : (NonnegativeTotals.Certificate.Rbar:ℝ)=(PositiveTD.Certificate.Rbar:ℝ) := by
      norm_num [NonnegativeTotals.Certificate.Rbar,PositiveTD.Certificate.Rbar]
    simp only [Certificate.numerator,map_sub,map_add,map_mul,map_pow,evaluate_scalar,
      Rat.cast_ofNat] at hpoly
    rw [hRbar] at hpoly
    exact hpoly
  have hh := PositiveTD.Certificate.four_norm_transfer
    (hm 0) (hm 1) (hm 2) (hm 3) (hn 0) (hn 1) (hn 2) (hn 3)
    (hs 0) (hs 1) (hs 2) (hs 3) hA hP
  rwa [endpoint_identity r i hd]

end Analytic
end SquaresInCircles.Eight.GlobalGA.NegativeA.LongE
end
end
end

section
@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open NegativeA.LongE (Region)
open TensorWholeIntervalPolynomial TwoVariablePolynomial

abbrev gain := NegativeA.LongE.gain

def scalar (k l c z e s : ℝ) (i : Fin 3) : ℝ :=
  PositiveBT3.Analytic.fullBaseline k l c z+l*gain s+
    TwoPositive.ASupport.charge e+
      NonnegativeTotals.Analytic.negative k l c (z+e-s) i

namespace Analytic

def endpoint (r : Region) (i : Fin 3) (x y : ℝ) : ℝ :=
  scalar (Explicit.k r x y) (Explicit.l r x y) (Explicit.m r x y)
    (Explicit.z r x y) (Explicit.e r x y) (Explicit.s r x y) i
def pAt (r : Region) (x y : ℝ) : Fin 4 → ℝ :=
  ![Explicit.k r x y,Explicit.k r x y,Explicit.l r x y,1]
def qAt (r : Region) (x y : ℝ) : Fin 4 → ℝ :=
  ![1,Explicit.l r x y,Explicit.m r x y,PositiveBT3.tilted (Explicit.m r x y) (Explicit.z r x y)]
def largeCoefficient (r : Region) (x y : ℝ) : Fin 3 → ℝ :=
  ![1,Explicit.l r x y,max (Explicit.l r x y) (Explicit.m r x y)]
def normAt (r : Region) (i : Fin 3) (j : Fin 4) (x y : ℝ) : ℝ :=
  pairNorm (pAt r x y j) (qAt r x y j) (if j.val=i.val then -Explicit.delta r x y else 0)
def nonradicalBase (r : Region) (x y : ℝ) : ℝ :=
  2*Explicit.k r x y+3*Explicit.l r x y+3+
    Explicit.m r x y*(1+2*Real.cos (Explicit.z r x y)+
      ((3/2)*PositiveTD.eta+1/2-PositiveTD.sigma)*Real.sin (Explicit.z r x y))+
      TwoPositive.ASupport.charge (Explicit.e r x y)+Explicit.l r x y*gain (Explicit.s r x y)
def nonradical (r : Region) (i : Fin 3) (x y : ℝ) : ℝ :=
  nonradicalBase r x y+largeCoefficient r x y i*(Real.cos (Explicit.delta r x y)-1)

theorem endpoint_identity (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) :
    endpoint r i x y=nonradical r i x y-
      R*(normAt r i 0 x y+normAt r i 1 x y+normAt r i 2 x y+normAt r i 3 x y) := by
  have hz := (Explicit.domains hd).1
  unfold endpoint scalar
  rw [PositiveBT3.Analytic.fullBaseline_norms,NonnegativeTotals.Analytic.negative_identity,
    edgeWidth_positive_formula hz]
  fin_cases i <;>
    simp (config := {decide := true}) only [nonradical,nonradicalBase,largeCoefficient,normAt,pAt,
      qAt,Fin.reduceFinMk,Matrix.cons_val,Fin.isValue,↓reduceIte,PositiveBT3.tilted,
      Explicit.delta,NegativeA.LongE.Explicit.delta] <;> ring

theorem coefficient_data (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    NonnegativeTotals.Explicit.BaseBounds (Explicit.k r x y) (Explicit.l r x y) (Explicit.m r x y) :=
  NonnegativeTotals.Explicit.base_bounds (Explicit.baseRegion r) (Explicit.base_domain hd)

theorem rotation_data (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    0<PositiveBT3.tilted (Explicit.m r x y) (Explicit.z r x y) ∧
    PositiveBT3.tilted (Explicit.m r x y) (Explicit.z r x y)≤
      evaluate x y (Certificate.rotation r) := by
  have hh := NegativeA.LongE.Analytic.m_data r hd
  exact ⟨hh.1,hh.2.1⟩

theorem qB_envelope (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    max (Explicit.l r x y) (Explicit.m r x y)≤evaluate x y (Certificate.qB r) := by
  have hh := PositiveBT3.Analytic.largeCoefficient_upper
    (Explicit.baseRegion r) 2 (Explicit.base_domain hd)
  cases r <;>
    simpa [PositiveBT3.Analytic.largeCoefficient,PositiveBT3.LargeCertificate.qB,
      PositiveBT3.LargeCertificate.m,Certificate.qB,Explicit.baseRegion,Explicit.baseY,
      Explicit.m,Explicit.l,NegativeA.LongE.Explicit.baseRegion,NegativeA.LongE.Explicit.baseY,
      NegativeA.LongE.Explicit.c,NegativeA.LongE.Explicit.l,
      NonnegativeTotals.Certificate.qStar] using hh

theorem E_charge (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    evaluate x y (Certificate.jE r)≤TwoPositive.ASupport.charge (Explicit.e r x y) :=
  NegativeA.LongE.Analytic.E_charge r hd

theorem nonradicalBase_lower (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    evaluate x y (Certificate.ABase r)≤nonradicalBase r x y :=
  NegativeA.LongE.Analytic.nonradicalBase_lower r hd

theorem largeCoefficient_bounds (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) : 0≤largeCoefficient r x y i ∧
      largeCoefficient r x y i≤evaluate x y (![1,Certificate.l r,Certificate.qB r] i) := by
  have hb := coefficient_data r hd
  fin_cases i
  · simp [largeCoefficient]
  · simpa [largeCoefficient] using And.intro hb.l_positive.le (le_refl (Explicit.l r x y))
  · exact ⟨hb.l_positive.le.trans (le_max_left _ _),qB_envelope r hd⟩

theorem nonradical_lower (r : Region) (i : Fin 3) {x y : ℝ} (hd : Explicit.Domain r x y) :
    evaluate x y (Certificate.A r i)≤nonradical r i x y := by
  have hδ := (Explicit.domains hd).2.2.2.2
  have ht := PositiveTD.Certificate.taylor_bounds hδ
  have hC : aeval (Explicit.delta r x y) PositiveTD.Certificate.C10-1≤0 := by
    linarith [ht.2.2.2.2.1,Real.cos_le_one (Explicit.delta r x y)]
  have h1 := mul_le_mul_of_nonpos_right (largeCoefficient_bounds r i hd).2 hC
  have h2 := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1)
    (largeCoefficient_bounds r i hd).1
  have hb := nonradicalBase_lower r hd
  simp only [Certificate.A,map_add,map_mul,map_sub,map_one,evaluate_lift,Certificate.evaluate_delta]
  dsimp [nonradical]
  linarith

theorem norm_square_upper (r : Region) (i : Fin 3) (j : Fin 4) {x y : ℝ}
    (hd : Explicit.Domain r x y) : (normAt r i j x y)^2≤evaluate x y (Certificate.P r i j) := by
  have hb := coefficient_data r hd
  have hk : 0<Explicit.k r x y := by linarith [hb.k_lower]
  have hc := rotation_data r hd
  have hδ := (Explicit.domains hd).2.2.2.2
  have n0 := NonnegativeTotals.Analytic.norm_negative_polynomial hk (by norm_num : (0:ℝ)<1) hδ
  have n1 := NonnegativeTotals.Analytic.norm_negative_polynomial hk hb.l_positive hδ
  have n2 := NonnegativeTotals.Analytic.norm_negative_polynomial hb.l_positive hb.c_positive hδ
  have z0 := NonnegativeTotals.Analytic.norm_zero_square (Explicit.k r x y) 1
  have z1 := NonnegativeTotals.Analytic.norm_zero_square (Explicit.k r x y) (Explicit.l r x y)
  have z2 := NonnegativeTotals.Analytic.norm_zero_square (Explicit.l r x y) (Explicit.m r x y)
  have z3 := NonnegativeTotals.Analytic.norm_zero_coefficient_upper (p:=1) hc.1.le hc.2
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [normAt,pAt,qAt,Certificate.P,Certificate.baseNorm,
      Fin.reduceFinMk,Matrix.cons_val,↓reduceIte,map_sub,map_add,map_mul,map_pow,
      map_one,sub_zero,evaluate_scalar,evaluate_lift,Certificate.evaluate_k,
      Certificate.evaluate_l,Certificate.evaluate_m,Certificate.evaluate_delta,Rat.cast_ofNat] <;>
    linarith

theorem endpoint_positive (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) : 0<endpoint r i x y := by
  have hm (j : Fin 4) := Certificate.mass_positive r i j hd
  have hn (j : Fin 4) : 0≤normAt r i j x y := Real.sqrt_nonneg _
  have hs (j : Fin 4) := norm_square_upper r i j hd
  have hA := nonradical_lower r i hd
  have hpoly := Certificate.numerator_positive r i hd
  have hR : (PositiveTD.Certificate.Rbar:ℝ)=(NonnegativeTotals.Certificate.Rbar:ℝ) := by
    norm_num [PositiveTD.Certificate.Rbar,NonnegativeTotals.Certificate.Rbar]
  have hP : 0<2*evaluate x y (Certificate.A r i)*
      evaluate x y (Certificate.mass r i 0)*evaluate x y (Certificate.mass r i 1)*
      evaluate x y (Certificate.mass r i 2)*evaluate x y (Certificate.mass r i 3)-
        (PositiveTD.Certificate.Rbar:ℝ)*
          ((evaluate x y (Certificate.P r i 0)+(evaluate x y (Certificate.mass r i 0))^2)*
              evaluate x y (Certificate.mass r i 1)*evaluate x y (Certificate.mass r i 2)*
              evaluate x y (Certificate.mass r i 3)+
            (evaluate x y (Certificate.P r i 1)+(evaluate x y (Certificate.mass r i 1))^2)*
              evaluate x y (Certificate.mass r i 0)*evaluate x y (Certificate.mass r i 2)*
              evaluate x y (Certificate.mass r i 3)+
            (evaluate x y (Certificate.P r i 2)+(evaluate x y (Certificate.mass r i 2))^2)*
              evaluate x y (Certificate.mass r i 0)*evaluate x y (Certificate.mass r i 1)*
              evaluate x y (Certificate.mass r i 3)+
            (evaluate x y (Certificate.P r i 3)+(evaluate x y (Certificate.mass r i 3))^2)*
              evaluate x y (Certificate.mass r i 0)*evaluate x y (Certificate.mass r i 1)*
              evaluate x y (Certificate.mass r i 2)) := by
    rw [hR]
    simpa only [Certificate.numerator,map_sub,map_add,map_mul,map_pow,evaluate_scalar,
      Rat.cast_ofNat] using hpoly
  have hh := PositiveTD.Certificate.four_norm_transfer
    (hm 0) (hm 1) (hm 2) (hm 3) (hn 0) (hn 1) (hn 2) (hn 3)
    (hs 0) (hs 1) (hs 2) (hs 3) hA hP
  rwa [endpoint_identity r i hd]

end Analytic
end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE
end
end
end
