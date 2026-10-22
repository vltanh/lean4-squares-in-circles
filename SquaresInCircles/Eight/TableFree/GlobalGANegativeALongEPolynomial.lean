module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeALongECertificates

/-!
# Strict positivity on the complete longer-E domains

Uncompiled transcription of Sections 7.1--7.4. The triangle TE uses a
decreasing quotient and a single completed square; RE uses concavity in
its actual variable interval. All closed boundary points are retained.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE.Certificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial

theorem mass_positive (r : Region) (i : Fin 3) (j : Fin 4)
    {x y : ℝ} (hd : Explicit.Domain r x y) : 0<evaluate x y (mass r i j) := by
  have hh := positive_on_domain (mass_certificate r i j).1 (mass_certificate r i j).2 hd
  have hr : (0:ℝ)<(massReserve r:ℝ) := by cases r <;> norm_num [massReserve]
  exact hr.trans hh

theorem TEfar_tail {u : ℝ} (hu : |u|≤4/15) (j : Fin 37) :
    -(|(TEcoefficient (j.val+3):ℝ)|*(4/15)^(j.val+1))*u^2≤
      (TEcoefficient (j.val+3):ℝ)*u^(j.val+3) := by
  have hp := pow_le_pow_left₀ (abs_nonneg u) hu (j.val+1)
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (TEcoefficient (j.val+3):ℝ))
  have hh : |(TEcoefficient (j.val+3):ℝ)*u^(j.val+1)|≤
      |(TEcoefficient (j.val+3):ℝ)|*(4/15)^(j.val+1) := by
    simpa [abs_mul,abs_pow] using hm
  have hscaled := mul_le_mul_of_nonneg_right (abs_le.mp hh).1 (sq_nonneg u)
  rw [show u^(j.val+3)=u^(j.val+1)*u^2 by rw [←pow_add]; congr 1; omega]
  nlinarith

theorem TEfar_H_positive {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) :
    (47/1000:ℝ)<aeval x (TEfar 0) := by
  let u : ℝ := x-4/15
  have hu : |u|≤4/15 := by apply abs_le.mpr; dsimp [u]; constructor <;> linarith [hx.1,hx.2]
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => TEfar_tail hu j)
  have he : (∑j : Fin 37,-(|(TEcoefficient (j.val+3):ℝ)|*(4/15)^(j.val+1))*u^2)=
      -(TEtail:ℝ)*u^2 := by simp [TEtail,Finset.sum_mul,Finset.sum_neg_distrib]
  rw [he] at hsum
  have hid := congrArg (fun p : ℚ[X] => aeval u p) TEfar_H_certificate.1
  simp only [map_add,map_sum,map_mul,map_pow,aeval_C,aeval_X] at hid
  have hlower : (TEcoefficient 0:ℝ)+(TEcoefficient 1:ℝ)*u+
      (TEcurvature:ℝ)*u^2≤aeval u TEcentered := by
    dsimp [TEcurvature]; push_cast; linarith
  have hκ : (0:ℝ)<(TEcurvature:ℝ) := by
    have hh : (133/100:ℝ)<(TEcurvature:ℝ) := by exact_mod_cast TEfar_H_certificate.2.1
    linarith
  have hmin := ChebyshevLeadingBounds.quadratic_min
    (a:=(TEcoefficient 0:ℝ)) (b:=(TEcoefficient 1:ℝ)) (x:=u) hκ
  have hreserve : (47/1000:ℝ)<(TEcoefficient 0:ℝ)-(TEcoefficient 1:ℝ)^2/(4*(TEcurvature:ℝ)) := by
    exact_mod_cast TEfar_H_certificate.2.2
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
      (by norm_num : (0:ℚ)<8/15) hc.1 hc.2 hx
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
  have hm := TEquotient_antitone i hx hy
    (show 8/15-x∈Icc 0 (8/15-x) from ⟨by linarith [hx.2],le_rfl⟩) hy.2
  have he : aeval x (TEfar i)=evaluate x (8/15-x) (TEquotient i) := by
    simp [TEfar,evaluate_restrict]
  rw [←he] at hm
  have hq := (TEfar_positive i hx).trans_le hm
  have hbase := NonnegativeTotals.Certificate.triangle_base_positive .atT i hx
  rw [←TEbase_identity i] at hbase
  have hidentity := divY_identity (numerator .TE i) x y
  rw [←TwoVariablePolynomial.evaluate_baseY] at hidentity
  change evaluate x y (numerator .TE i)=aeval x (TEbase i)+y*evaluate x y (TEquotient i) at hidentity
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
    (REboundary_certificate i j).1 (REboundary_certificate i j).2 ht
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
    simpa [REboundary,RElength,evaluate_restrict] using REboundary_positive i 0 hy
  have hright : 0<evaluate (min (1/6:ℝ) (19/50-y)) y (numerator .RE i) := by
    rcases le_total (1/6:ℝ) (19/50-y) with hh|hh
    · rw [min_eq_left hh]
      have hy' : y∈Icc 0 (RElength 1:ℝ) := ⟨hy.1,by norm_num [RElength]; linarith⟩
      simpa [REboundary,evaluate_restrict] using REboundary_positive i 1 hy'
    · rw [min_eq_right hh]
      have ht : 19/50-y∈Icc 0 (RElength 2:ℝ) := ⟨by linarith [hy.2],by simpa [RElength] using hh⟩
      simpa [REboundary,evaluate_restrict] using REboundary_positive i 2 ht
  exact concave_gt_of_endpoints (REconcave i hy) hx hleft hright

theorem RC_positive (i : Fin 3) {x y : ℝ} (hd : Explicit.Domain .RC x y) :
    0<evaluate x y (numerator .RC i) := by
  have hbase := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<1/6) (RCbase_certificate i).1 (RCbase_certificate i).2 hd.1
  have hq := positive_on_domain (RCquotient_certificate i).1 (RCquotient_certificate i).2 hd
  have hr0 : (0:ℝ)<(RCbaseReserve i:ℝ) := by fin_cases i <;> norm_num [RCbaseReserve]
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

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE.Certificate
