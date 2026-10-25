module

public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNegativeTDConcentrationGeometry
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNegativeTDScalars

/-!
# Eight squares: every negative-TD2 magnitude and both ordinary sign totals

The A/E primary cost is kept
constant while s varies. The endpoints 0, delta, and h are discharged
by the eight proved scalar families, including the D linear branch.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.NegativeTD.Concentration
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open OrdinaryNegativeSlope

abbrev affine_add_concave := @PositiveANegativeTD.Fixed.affine_add_concave

theorem negative_endpoint (i : Fin 4) {t E : ℝ} (hd : Domain t E) :
    0<base E+primaryCost t E+V R (p E i) (q E i) t := by
  fin_cases i
  · exact negative_positive 0 hd
  · exact negative_positive 1 hd
  · exact negative_positive 2 hd
  · exact negative_positive 0 hd

theorem positive_endpoint (i : Fin 4) {t E : ℝ} (hd : Domain t E) :
    0<base E+primaryCost t E+speed*frameCap+positive E i (frameCap-t) := by
  fin_cases i
  · rw [positive,PositiveTD.Hybrid.positive,ite_eq_right (by decide)]
    exact positive_positive 0 hd
  · rw [positive,PositiveTD.Hybrid.positive,ite_eq_right (by decide)]
    exact positive_positive 1 hd
  · rw [positive,PositiveTD.Hybrid.positive,ite_eq_right (by decide)]
    exact positive_positive 2 hd
  · rw [positive,PositiveTD.Hybrid.positive,ite_eq_left (by decide)]
    have h := D_positive hd
    rw [DScalar] at h
    linarith

theorem lower_negative_positive (j : Fin 4) {t E s : ℝ}
    (hd : Domain t E) (hs : s∈Icc 0 t) :
    0<base E+primaryCost t E+speed*s+V R (p E j) (q E j) (t-s) := by
  have hang := domain_angles hd
  have hc := coefficients hang.2.1 j
  have hV := concave_affine_argument
    (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1 (by linarith [hc.2.2.1]))
    (a:=-1) (b:=t) (l:=0) (u:=t)
    (fun s hs => ⟨by linarith [hs.2],by linarith [hs.1,hd.1.2]⟩)
  have hconc := affine_add_concave hV (base E+primaryCost t E) speed
  have h0 : 0<base E+primaryCost t E+speed*0+V R (p E j) (q E j) ((-1)*0+t) := by
    simpa using negative_endpoint j hd
  have h1 : 0<base E+primaryCost t E+speed*t+V R (p E j) (q E j) ((-1)*t+t) := by
    simpa [equalScalar] using equal_positive hd
  simpa only [neg_mul,one_mul,neg_add_eq_sub] using concave_gt_of_endpoints hconc hs h0 h1

theorem lower_positive_positive (i : Fin 4) {t E s : ℝ}
    (hd : Domain t E) (hs : s∈Icc t frameCap) :
    0<base E+primaryCost t E+speed*s+positive E i (s-t) := by
  have hang := domain_angles hd
  have hc := coefficients hang.2.1 i
  have hU := concave_affine_argument
    (PositiveTD.Hybrid.positive_concave (a:=aD) (p:=p E) (q:=q E) (d:=3) (i:=i)
      (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1 (by linarith [hc.2.2.1]))
    (a:=1) (b:=-t) (l:=t) (u:=frameCap)
    (fun s hs => ⟨by linarith [hs.1],by linarith [hs.2,hang.1.1]⟩)
  have hconc := affine_add_concave hU (base E+primaryCost t E) speed
  have h0 : 0<base E+primaryCost t E+speed*t+
      PositiveTD.Hybrid.positive R aD (p E) (q E) 3 i (1*t+-t) := by
    simpa [equalScalar] using equal_positive hd
  have h1 : 0<base E+primaryCost t E+speed*frameCap+
      PositiveTD.Hybrid.positive R aD (p E) (q E) 3 i (1*frameCap+-t) := by
    simpa only [one_mul,←sub_eq_add_neg,positive] using positive_endpoint i hd
  simpa only [one_mul,←sub_eq_add_neg,positive] using concave_gt_of_endpoints hconc hs h0 h1

theorem upper_positive (i j : Fin 4) {t E s : ℝ}
    (hd : Domain t E) (hs : s∈Icc 0 frameCap) :
    0<base E+primaryCost t E+speed*s+line E i j (frameCap-t) (frameCap-s) := by
  have hang := domain_angles hd
  have hconc := affine_add_concave (upper_line_concave hang.2.1 i j hang.1)
    (base E+primaryCost t E) speed
  have h0 : 0<base E+primaryCost t E+speed*0+line E i j (frameCap-t) (frameCap-0) := by
    have hh := line_excess_lower hang.2.1 i j hang.1
      (show frameCap-t∈Icc 0 (frameCap-t) from ⟨by linarith [hd.1.2],le_rfl⟩)
    rw [show t+(frameCap-t)=frameCap by ring] at hh
    have hp := negative_endpoint j hd
    simp only [mul_zero,add_zero,sub_zero]
    linarith
  have h1 : 0<base E+primaryCost t E+speed*frameCap+line E i j (frameCap-t) (frameCap-frameCap) := by
    simpa only [sub_self,line_zero_right] using positive_endpoint i hd
  have h := concave_gt_of_endpoints hconc hs h0 h1
  exact h

theorem line_scalar_positive (i j : Fin 4) {t E s P : ℝ}
    (hd : Domain t E) (hs : s∈Icc 0 frameCap)
    (hP : P∈Icc (max 0 (s-t)) (frameCap-t)) :
    0<base E+primaryCost t E+speed*s+line E i j P (t-s+P) := by
  have hang := domain_angles hd
  have hconc := affine_add_concave (shifted_line_concave hang.2.1 i j hang.1 hs)
    (base E+primaryCost t E+speed*s) 0
  have hlo : 0<base E+primaryCost t E+speed*s+
      line E i j (max 0 (s-t)) (t-s+max 0 (s-t)) := by
    by_cases hst : s≤t
    · rw [max_eq_left (by linarith : s-t≤0)]
      simp only [add_zero,line_zero_left]
      exact lower_negative_positive j hd ⟨hs.1,hst⟩
    · have hts : t≤ s := (lt_of_not_ge hst).le
      rw [max_eq_right (by linarith : 0≤ s-t),show t-s+(s-t)=0 by ring,line_zero_right]
      exact lower_positive_positive i hd ⟨hts,hs.2⟩
  have hhi : 0<base E+primaryCost t E+speed*s+
      line E i j (frameCap-t) (t-s+(frameCap-t)) := by
    rw [show t-s+(frameCap-t)=frameCap-s by ring]
    exact upper_positive i j hd hs
  simpa only [zero_mul,add_zero] using concave_gt_of_endpoints hconc hP
    (by simpa only [zero_mul,add_zero] using hlo) (by simpa only [zero_mul,add_zero] using hhi)

/-- Both sign totals remain those of the unchanged necessary system.
The same scalar bound holds for all four concentrated block indices. -/
theorem sum_scalar_positive {t E s : ℝ} (P N : Fin 4→ℝ)
    (hd : Domain t E) (hs : s∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPt : (∑i,P i)≤frameCap-t) (hNt : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)=t-s+∑i,P i) :
    0<base E+primaryCost t E+speed*s+∑i,block E i (P i) (N i) := by
  have hang := domain_angles hd
  have hP0 := Finset.sum_nonneg (s:=Finset.univ) (fun i _ => hP i)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ) (fun i _ => hN i)
  obtain ⟨i,j,hij⟩ := PositiveTD.Hybrid.both_signs_concentrate R aD (p E) (q E) P N 3
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (coefficients hang.2.1 i).1) (fun i => (coefficients hang.2.1 i).2.1)
    (fun i => by linarith [(coefficients hang.2.1 i).2.2.1,(coefficients hang.2.1 i).1]) hP hN
    (by linarith [hang.1.1]) (by linarith [hs.1])
  change line E i j (∑i,P i) (∑i,N i)≤∑i,block E i (P i) (N i) at hij
  have hpdom : (∑i,P i)∈Icc (max 0 (s-t)) (frameCap-t) :=
    ⟨max_le hP0 (by linarith),hPt⟩
  have hp := line_scalar_positive i j hd hs hpdom
  rw [hbalance] at hij
  linarith

end SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.NegativeTD.Concentration
