module

public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsTD0Envelope

/-!
# Eight squares: the four actual full-circle blocks at a large total

The moving D pair is kept separately from the
fixed B pair. Both fit the established balanced domain and the common
coefficient scale min(1,l). The D negative alternative is then removed
by the previously proved monotone coefficient comparison.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open OrdinaryNegativeSlope OrdinaryPositiveEnvelope NonnegativeTotals

def pWeights (k l m c : ℝ) : Fin 4 → ℝ := ![k,k,min l m,min 1 c]
def qWeights (_k l m c : ℝ) : Fin 4 → ℝ := ![1,l,max l m,max 1 c]
def endpoint (k l m c t : ℝ) (i j : Fin 4) : ℝ :=
  min (V R (pWeights k l m c j) (qWeights k l m c j) t)
    (if i=j then M R (pWeights k l m c i) (qWeights k l m c i) t
     else U R (pWeights k l m c i) (qWeights k l m c i) (frameCap-t)+
       V R (pWeights k l m c j) (qWeights k l m c j) frameCap)

namespace Balanced

theorem pair_domain (r : Region) {x y u : ℝ} (hd : Explicit.Domain r x y)
    (hu : u∈Icc 0 (Explicit.theta r x y)) (i : Fin 4) :
    0<pWeights (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) (Explicit.tilted r x y u) i ∧
    pWeights (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) (Explicit.tilted r x y u) i≤
      qWeights (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) (Explicit.tilted r x y u) i ∧
    2*qWeights (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) (Explicit.tilted r x y u) i≤
      3*pWeights (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) (Explicit.tilted r x y u) i := by
  have hb := Explicit.base_bounds r hd
  have hz : (0:ℝ)∈Icc 0 (Explicit.theta r x y) := ⟨le_rfl,(Explicit.domains hd).1.1⟩
  have hordinary (j : Fin 4) := Explicit.pair_domain r hd hz j
  fin_cases i
  · simpa [pWeights,qWeights,Explicit.pWeights,Explicit.qWeights,PositiveTD.pWeights,
      PositiveTD.qWeights,Explicit.tilted,Explicit.tilt] using hordinary 0
  · simpa [pWeights,qWeights,Explicit.pWeights,Explicit.qWeights,PositiveTD.pWeights,
      PositiveTD.qWeights,Explicit.tilted,Explicit.tilt] using hordinary 1
  · simpa [pWeights,qWeights,Explicit.pWeights,Explicit.qWeights,PositiveTD.pWeights,
      PositiveTD.qWeights,Explicit.tilted,Explicit.tilt] using hordinary 2
  · change 0< min 1 (Explicit.tilted r x y u) ∧
      min 1 (Explicit.tilted r x y u)≤ max 1 (Explicit.tilted r x y u) ∧
      2*max 1 (Explicit.tilted r x y u)≤3*min 1 (Explicit.tilted r x y u)
    have hlo := Explicit.tilted_lower r hd hu
    have hhi := Explicit.tilted_upper r hd hu
    rcases le_total 1 (Explicit.tilted r x y u) with hc|hc
    · rw [min_eq_left hc,max_eq_right hc]
      exact ⟨by norm_num,hc,by linarith⟩
    · rw [min_eq_right hc,max_eq_left hc]
      exact ⟨by linarith [hb.k_lower],hc,by linarith [hb.k_lower]⟩

theorem scale_bounds (r : Region) {x y u : ℝ} (hd : Explicit.Domain r x y)
    (hu : u∈Icc 0 (Explicit.theta r x y)) (i : Fin 4) :
    min 1 (Explicit.l r x y)≤
      qWeights (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) (Explicit.tilted r x y u) i ∧
    qWeights (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) (Explicit.tilted r x y u) i≤
      (6/5)*min 1 (Explicit.l r x y) := by
  have hz : (0:ℝ)∈Icc 0 (Explicit.theta r x y) := ⟨le_rfl,(Explicit.domains hd).1.1⟩
  have hH := Explicit.pair_scale_bounds r hd hz 0
  fin_cases i
  · simpa [qWeights,Explicit.qWeights,PositiveTD.qWeights] using hH
  · simpa [qWeights,Explicit.qWeights,PositiveTD.qWeights] using Explicit.pair_scale_bounds r hd hz 1
  · simpa [qWeights,Explicit.qWeights,PositiveTD.qWeights,Explicit.tilted,Explicit.tilt] using
      Explicit.pair_scale_bounds r hd hz 2
  · have hrot : Explicit.tilted r x y u≤(6/5)*min 1 (Explicit.l r x y) := by
      rcases le_total 1 (Explicit.l r x y) with hl|hl
      · rw [min_eq_left hl]
        linarith [Explicit.tilted_upper r hd hu]
      · rw [min_eq_right hl]
        nlinarith [(Explicit.tilted_ratio r hd hu).2,(Explicit.base_bounds r hd).l_positive]
    change min 1 (Explicit.l r x y)≤ max 1 (Explicit.tilted r x y u) ∧
      max 1 (Explicit.tilted r x y u)≤(6/5)*min 1 (Explicit.l r x y)
    exact ⟨(min_le_left _ _).trans (le_max_left _ _),max_le hH.2 hrot⟩

theorem pure_lower (r : Region) {x y u : ℝ} (hd : Explicit.Domain r x y)
    (hu : u∈Icc 0 (Explicit.theta r x y)) (j : Fin 4) :
    TwoPositive.balancedEnvelope (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
      (Explicit.delta r x y)≤
    V R (pWeights (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) (Explicit.tilted r x y u) j)
      (qWeights (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) (Explicit.tilted r x y u) j)
      (Explicit.delta r x y) := by
  have hb := Explicit.base_bounds r hd
  fin_cases j
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)
  · exact (min_le_left _ _).trans (TD0.D_redundant
      ⟨hb.k_lower,by linarith [hb.k_upper]⟩ (Explicit.tilted_lower r hd hu).le
      (Explicit.tilted_upper r hd hu).le
      ⟨by linarith [(Explicit.domains hd).2.2.1],(Explicit.domains hd).2.2.2⟩)

theorem endpoint_lower (r : Region) {x y u : ℝ} (hd : Explicit.Domain r x y)
    (hu : u∈Icc 0 (Explicit.theta r x y)) (i j : Fin 4) :
    TwoPositive.balancedEnvelope (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
      (Explicit.delta r x y)≤endpoint (Explicit.k r x y) (Explicit.l r x y)
        (Explicit.c r x y) (Explicit.tilted r x y u) (Explicit.delta r x y) i j := by
  have hc := pair_domain r hd hu
  have ht : Explicit.delta r x y∈Icc 0 frameCap :=
    ⟨by linarith [(Explicit.domains hd).2.2.1],(Explicit.domains hd).2.2.2⟩
  unfold endpoint
  apply le_min (pure_lower r hd hu j)
  by_cases hij : i=j
  · subst j
    simp only [↓reduceIte]
    exact (pure_lower r hd hu i).trans (M_ge_V (hc i).1.le
      ((hc i).1.trans_le (hc i).2.1).le (by linarith [(hc i).2.2,(hc i).1]) ht)
  · simp only [ite_eq_right hij]
    have hlen : 0≤frameCap-Explicit.delta r x y := by linarith [ht.2]
    have hU := U_lower (Real.sqrt_nonneg qCap) radius_sq.le
      (hc i).1 (hc i).2.1 (by linarith [(hc i).2.2,(hc i).1])
      (show frameCap-Explicit.delta r x y∈Icc 0 frameCap from ⟨hlen,by linarith [ht.1]⟩)
    have hV := V_growth (hc j).1 (hc j).2.1 (by linarith [(hc j).2.2]) ht
      (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht.2
    have hmargin : 0≤
        (2/3)*qWeights (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) (Explicit.tilted r x y u) j-
        (109/200)*qWeights (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) (Explicit.tilted r x y u) i := by
      have hi := scale_bounds r hd hu i
      have hj := scale_bounds r hd hu j
      have hp := (hc j).1.trans_le (hc j).2.1
      have hm : 0≤ min 1 (Explicit.l r x y) :=
        le_min zero_le_one (Explicit.base_bounds r hd).l_positive.le
      linarith
    have hpay := mul_nonneg hmargin hlen
    linarith [pure_lower r hd hu j]

end Balanced
end SquaresInCircles.Eight.GlobalGA.PositiveBT3
