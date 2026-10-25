module

public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsBalanced
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsEndpoints
public import SquaresInCircles.Eight.Owners.GA.Positive.ATD0HighScalar

/-!
# Eight squares: the fourth ordinary TD0 block and the same A endpoint certificates

The actual TD0
error has either sign and is not deleted. Its fourth coefficient pair
is (1,c). Both orders of that pair satisfy the original balanced domain,
and its negative alternative is bounded below by the H alternative.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.TD0
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open OrdinaryNegativeSlope OrdinaryPositiveEnvelope

abbrev p := PositiveATD0.pWeights
abbrev q := PositiveATD0.qWeights

theorem coefficient_domain (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) (i : Fin 4) :
    0<p (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) i ∧
    p (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) i≤
      q (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) i ∧
    2*q (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) i≤
      3*p (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) i := by
  have hb := Explicit.base_bounds r hd
  have hz : (0:ℝ)∈Icc 0 (Explicit.theta r x y) := ⟨le_rfl,(Explicit.domains hd).1.1⟩
  fin_cases i
  · simpa [p,q,PositiveATD0.pWeights,PositiveATD0.qWeights,Explicit.pWeights,
      Explicit.qWeights,PositiveTD.pWeights,PositiveTD.qWeights,Explicit.tilted,Explicit.tilt] using
      Explicit.pair_domain r hd hz 1
  · simpa [p,q,PositiveATD0.pWeights,PositiveATD0.qWeights,Explicit.pWeights,
      Explicit.qWeights,PositiveTD.pWeights,PositiveTD.qWeights,Explicit.tilted,Explicit.tilt] using
      Explicit.pair_domain r hd hz 0
  · simpa [p,q,PositiveATD0.pWeights,PositiveATD0.qWeights,Explicit.pWeights,
      Explicit.qWeights,PositiveTD.pWeights,PositiveTD.qWeights,Explicit.tilted,Explicit.tilt] using
      Explicit.pair_domain r hd hz 2
  · change 0< min 1 (Explicit.c r x y) ∧ min 1 (Explicit.c r x y)≤ max 1 (Explicit.c r x y) ∧
      2*max 1 (Explicit.c r x y)≤3*min 1 (Explicit.c r x y)
    rcases le_total 1 (Explicit.c r x y) with hc|hc
    · rw [min_eq_left hc,max_eq_right hc]
      exact ⟨by norm_num,hc,by linarith [Explicit.c_upper r hd]⟩
    · rw [min_eq_right hc,max_eq_left hc]
      exact ⟨hb.c_positive,hc,by linarith [hb.k_lower,hb.k_le_c]⟩

theorem scale_bounds (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) (i : Fin 4) :
    min 1 (Explicit.l r x y)≤q (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) i ∧
    q (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) i≤
      (6/5)*min 1 (Explicit.l r x y) := by
  have hz : (0:ℝ)∈Icc 0 (Explicit.theta r x y) := ⟨le_rfl,(Explicit.domains hd).1.1⟩
  have hb := Explicit.base_bounds r hd
  have hH := Explicit.pair_scale_bounds r hd hz 0
  fin_cases i
  · simpa [q,PositiveATD0.qWeights,Explicit.qWeights,PositiveTD.qWeights,Explicit.tilted,Explicit.tilt] using
      Explicit.pair_scale_bounds r hd hz 1
  · simpa [q,PositiveATD0.qWeights,Explicit.qWeights,PositiveTD.qWeights,Explicit.tilted,Explicit.tilt] using hH
  · simpa [q,PositiveATD0.qWeights,Explicit.qWeights,PositiveTD.qWeights,Explicit.tilted,Explicit.tilt] using
      Explicit.pair_scale_bounds r hd hz 2
  · have hc : Explicit.c r x y≤(6/5)*min 1 (Explicit.l r x y) := by
      rcases le_total 1 (Explicit.l r x y) with hl|hl
      · rw [min_eq_left hl]
        linarith [Explicit.c_upper r hd]
      · rw [min_eq_right hl]
        nlinarith [hb.c_upper_ratio,hb.l_positive]
    change min 1 (Explicit.l r x y)≤ max 1 (Explicit.c r x y) ∧
      max 1 (Explicit.c r x y)≤(6/5)*min 1 (Explicit.l r x y)
    exact ⟨(min_le_left _ _).trans (le_max_left _ _),max_le hH.2 hc⟩

theorem pairwise_ratio (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) (i j : Fin 4) :
    5*q (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) i≤
      6*q (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) j := by
  linarith [(scale_bounds r hd i).2,(scale_bounds r hd j).1]

theorem D_redundant {k c t : ℝ} (hk : k∈Icc (2/3:ℝ) 1)
    (hkc : k≤c) (hc : c≤6/5) (ht : t∈Icc 0 frameCap) :
    V R k 1 t≤V R (min 1 c) (max 1 c) t := by
  by_cases hc1 : c≤1
  · rw [min_eq_right hc1,max_eq_left hc1]
    exact PositiveTD.V_first_coefficient (by norm_num)
      (by linarith [hk.1]) hkc (by linarith) ht
  · have hc1' : 1≤c := (lt_of_not_ge hc1).le
    rw [min_eq_left hc1',max_eq_right hc1']
    have hfirst : V R k 1 t≤V R 1 1 t := PositiveTD.V_first_coefficient
      (by norm_num) (by linarith [hk.1]) hk.2 (by norm_num) ht
    exact hfirst.trans (PositiveATD0.balanced_second_coefficient
      (by norm_num) le_rfl hc1' (by linarith) ht)

theorem pure_lower (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) (j : Fin 4) :
    PositiveATD0.envelope (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) (Explicit.delta r x y)≤
      V R (p (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) j)
        (q (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) j) (Explicit.delta r x y) := by
  have hb := Explicit.base_bounds r hd
  fin_cases j
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_right _ _)
  · exact (min_le_left _ _).trans (D_redundant
      ⟨hb.k_lower,by linarith [hb.k_upper]⟩ hb.k_le_c (Explicit.c_upper r hd).le
      ⟨by linarith [(Explicit.domains hd).2.2.1],(Explicit.domains hd).2.2.2⟩)

theorem endpoint_lower (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) (i j : Fin 4) :
    PositiveATD0.envelope (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) (Explicit.delta r x y)≤
      PositiveATD0.endpoint (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) (Explicit.delta r x y) i j := by
  have hcoef := coefficient_domain r hd
  have ht : Explicit.delta r x y∈Icc 0 frameCap :=
    ⟨by linarith [(Explicit.domains hd).2.2.1],(Explicit.domains hd).2.2.2⟩
  have hlen : 0≤frameCap-Explicit.delta r x y := by linarith [ht.2]
  unfold PositiveATD0.endpoint
  apply le_min (pure_lower r hd j)
  by_cases hij : i=j
  · subst j
    simp only [↓reduceIte]
    exact (pure_lower r hd i).trans (M_ge_V (hcoef i).1.le
      ((hcoef i).1.trans_le (hcoef i).2.1).le (by linarith [(hcoef i).2.2]) ht)
  · simp only [hij,↓reduceIte]
    have hU := U_lower (Real.sqrt_nonneg qCap) radius_sq.le
      (hcoef i).1 (hcoef i).2.1 (by linarith [(hcoef i).2.2,(hcoef i).1])
      (show frameCap-Explicit.delta r x y∈Icc 0 frameCap from ⟨hlen,by linarith [ht.1]⟩)
    have hV := V_growth (hcoef j).1 (hcoef j).2.1 (by linarith [(hcoef j).2.2]) ht
      (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht.2
    have hq0 := (hcoef j).1.trans_le (hcoef j).2.1
    have hmargin : 0≤(2/3)*q (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) j-
        (109/200)*q (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) i := by
      linarith [pairwise_ratio r hd i j]
    have hpay := mul_nonneg hmargin hlen
    linarith [pure_lower r hd j]

theorem A_endpoint_positive (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    0<PositiveATD0.fullBaseline (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)+
      Explicit.l r x y*TwoPositive.ASupport.charge (Explicit.theta r x y)+
      TwoPositive.ASupport.charge (Explicit.e r x y)+
      PositiveATD0.envelope (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) (Explicit.delta r x y) := by
  have h0 := Analytic.endpoint_positive r .atA 0 hd
  have h1 := Analytic.endpoint_positive r .atA 1 hd
  have h2 := Analytic.endpoint_positive r .atA 2 hd
  simp only [Analytic.endpoint,Analytic.largeScalar,Analytic.aAt,sub_self,
    PositiveTD.tilted,Real.cos_zero,Real.sin_zero,mul_zero,add_zero,mul_one,
    Analytic.negative,Matrix.cons_val_zero] at h0 h1 h2
  have he (k l c : ℝ) : Analytic.fullBaseline k l c 0=PositiveATD0.fullBaseline k l c := by
    simp [Analytic.fullBaseline,PositiveATD0.fullBaseline,PositiveTD.tilted]
    ring
  rw [he] at h0 h1 h2
  unfold PositiveATD0.envelope
  rw [add_min,add_min]
  exact lt_min h0 (lt_min h1 h2)

end SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.TD0
