module

public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3LongCertificates
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LargePolynomial

/-!
# Eight squares: positivity on all four longer-E BT3 domains

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
