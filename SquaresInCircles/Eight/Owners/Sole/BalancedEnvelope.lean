module

public import SquaresInCircles.Eight.Owners.Sole.BalancedCoefficients

/-!
# Eight squares: middle and high ordinary allocations reduce to actual pure charges

The growth reserve holds also for the middle sole-DE
coefficient cap 59/50. Every ordinary allocation is bounded by the least
of its four pure negative charges at the original total angle. The
endpoint positivity theorem below keeps all four strict alternatives.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleBalancedEnvelope
open SoleECoefficients SoleOrdinaryData SoleBalancedCoefficients SingleAngleConcavity

theorem ordinary_lower {b : Band} {de : Bool} {R t x e L : ℝ}
    (hb : b≠.low) (P N : Fin 4 → ℝ)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain b) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑i,P i)≤frameCap-t) (hbalance : (∑i,N i)=t+∑i,P i)
    (hsingle : ∀ i,single de i=true → P i=0 ∨ N i=0)
    (hpure : ∀ i,L≤pure (single de i) R (small b de t x e i)
      (large b de t x e i) (nu b de t x e i) t) :
    L≤∑i,F (single de i) R (small b de t x e i) (large b de t x e i)
      (nu b de t x e i) (P i) (N i) := by
  cases b
  · exact (hb rfl).elim
  · have hc := middle_conditions (de := de) ht hx he
    exact SoleAngleGrowth.balanced_envelope (single de) R (small .middle de t x e)
      (large .middle de t x e) (nu .middle de t x e) P N
      (qlo := 983/1000) (qhi := 59/50) hR hQL hQU (small_pos ht hx he)
      (small_le_large .middle de t x e) hc.1 (nu_between ht) hc.2 (by norm_num)
      hP hN (angle ht) hbudget hbalance hsingle hpure
  · have hc := high_conditions (de := de) ht hx he
    exact SoleAngleGrowth.balanced_envelope (single de) R (small .high de t x e)
      (large .high de t x e) (nu .high de t x e) P N
      (qlo := 1) (qhi := 113/100) hR hQL hQU (small_pos ht hx he)
      (small_le_large .high de t x e) hc.1 (nu_between ht) hc.2 (by norm_num)
      hP hN (angle ht) hbudget hbalance hsingle hpure

def minimumFour (f : Fin 4 → ℝ) : ℝ := min (f 0) (min (f 1) (min (f 2) (f 3)))

theorem minimumFour_le (f : Fin 4 → ℝ) (i : Fin 4) : minimumFour f≤f i := by
  fin_cases i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

theorem minimumFour_positive {K : ℝ} {f : Fin 4 → ℝ}
    (hf : ∀ i,0<K+f i) : 0<K+minimumFour f := by
  have h0 : -K<f 0 := by linarith [hf 0]
  have h1 : -K<f 1 := by linarith [hf 1]
  have h2 : -K<f 2 := by linarith [hf 2]
  have h3 : -K<f 3 := by linarith [hf 3]
  have hh := lt_min h0 (lt_min h1 (lt_min h2 h3))
  change 0<K+min (f 0) (min (f 1) (min (f 2) (f 3)))
  linarith

end SquaresInCircles.Eight.SoleBalancedEnvelope
