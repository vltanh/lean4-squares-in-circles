module

public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveLowTransfer
public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveHighTransfer
public import SquaresInCircles.Eight.TableFree.GlobalGATD2UpperEnvelope

/-!
# The low and balanced envelopes at a fixed total A/T angle

Uncompiled source following Sections 4--5 of the two-positive split
proof.  The tilted coefficient and the total angle are independent
parameters here.  This is the same concentration envelope with the
total angle replacing the old fixed TD angle.  The balanced proof
uses pairwise coefficient ratios, so no lower bound of one on every
large coefficient is assumed.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope OrdinaryPositiveEnvelope PositiveTD

def endpoint (k l m t : ℝ) (i j : Fin 4) : ℝ :=
  min (V R (pWeights k l m j) (qWeights k l m j) t)
    (if i=j then Hybrid.saturated R (diagonal-1/2) (pWeights k l m) (qWeights k l m) 3 i t
     else Hybrid.positive R (diagonal-1/2) (pWeights k l m) (qWeights k l m) 3 i (frameCap-t)+
       V R (pWeights k l m j) (qWeights k l m j) frameCap)

def splitBase (k l c t a : ℝ) : ℝ := baseline k l c (t-a)+l*ASupport.charge a
def splitScalar (k l c t a : ℝ) (i j : Fin 4) : ℝ :=
  splitBase k l c t a+endpoint k l (tilted c (t-a)) t i j

def lowEnvelope (k l m t : ℝ) : ℝ :=
  min (V R k 1 t)
    (min (V R k 1 t+k*(phi (frameCap-t)-1)+l*(Real.cos frameCap-Real.cos t))
      (min (-(109/200)*m*(frameCap-t)+V R k 1 frameCap)
        (-(109/200)*m*(frameCap-t)+V R k l frameCap)))

def balancedEnvelope (k l m t : ℝ) : ℝ :=
  min (V R k 1 t) (min (V R k l t) (V R (min l m) (max l m) t))

theorem low_envelope_bounds (k l m t : ℝ) :
    lowEnvelope k l m t≤V R k 1 t ∧
    lowEnvelope k l m t≤V R k 1 t+k*(phi (frameCap-t)-1)+l*(Real.cos frameCap-Real.cos t) ∧
    lowEnvelope k l m t≤-(109/200)*m*(frameCap-t)+V R k 1 frameCap ∧
    lowEnvelope k l m t≤-(109/200)*m*(frameCap-t)+V R k l frameCap := by
  unfold lowEnvelope
  exact ⟨min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩

theorem low_coefficient_data {k l m : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : m∈Icc l ((3/2)*l)) (i : Fin 4) :
    0<pWeights k l m i ∧ pWeights k l m i≤qWeights k l m i ∧
      qWeights k l m i≤2*pWeights k l m i ∧ qWeights k l m i≤m := by
  have hk0 : 0<k := by linarith [hk.1]
  have hl0 : 0<l := by linarith [hl.1]
  fin_cases i
  · change 0<k ∧ k≤1 ∧ 1≤2*k ∧ 1≤m
    exact ⟨hk0,by linarith [hk.2],by linarith [hk.1],hl.1.trans hm.1⟩
  · change 0<k ∧ k≤l ∧ l≤2*k ∧ l≤m
    exact ⟨hk0,by linarith [hk.2,hl.1],hl.2,hm.1⟩
  · change 0<min l m ∧ min l m≤max l m ∧ max l m≤2*min l m ∧ max l m≤m
    rw [min_eq_left hm.1,max_eq_right hm.1]
    exact ⟨hl0,hm.1,by linarith [hm.2],le_rfl⟩
  · change 0<k ∧ k≤1 ∧ 1≤2*k ∧ 1≤m
    exact ⟨hk0,by linarith [hk.2],by linarith [hk.1],hl.1.trans hm.1⟩

theorem low_pure_lower {k l m t : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : m∈Icc l ((3/2)*l)) (ht : t∈Icc 0 (1/6:ℝ)) (j : Fin 4) :
    V R k 1 t≤V R (pWeights k l m j) (qWeights k l m j) t := by
  have ht' := PositiveTD.Certificate.low_frame_domain ht
  have hk0 : 0<k := by linarith [hk.1]
  have hl0 : 0<l := by linarith [hl.1]
  fin_cases j
  · exact le_rfl
  · change V R k 1 t≤V R k l t
    exact V_short_second_coefficient hk0 (by norm_num) hl.1 hl.2 ht
  · change V R k 1 t≤V R (min l m) (max l m) t
    rw [min_eq_left hm.1,max_eq_right hm.1]
    have hfirst : V R k 1 t≤V R l 1 t := V_first_coefficient (by norm_num)
      (by linarith [hk.1]) (by linarith [hk.2,hl.1]) (by linarith [hl.2,hk.2]) ht'
    exact hfirst.trans (V_short_second_coefficient hl0 (by norm_num)
      (hl.1.trans hm.1) (by linarith [hm.2]) ht)
  · exact le_rfl

theorem low_positive_lower {k l m t : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : m∈Icc l ((3/2)*l)) (ht : t∈Icc 0 frameCap) (i : Fin 4) :
    -(109/200)*m*(frameCap-t)≤
      Hybrid.positive R (diagonal-1/2) (pWeights k l m) (qWeights k l m) 3 i (frameCap-t) := by
  have hb : frameCap-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  by_cases hi : i=3
  · subst i
    simp only [Hybrid.positive,if_pos rfl]
    have hcoef : diagonal-1/2≤(109/200)*m := by
      linarith [diagonal_bounds.2,hl.1,hm.1]
    nlinarith [mul_le_mul_of_nonneg_right hcoef hb.1]
  · simp only [Hybrid.positive,if_neg hi]
    have hd := low_coefficient_data hk hl hm i
    have hU := U_lower (Real.sqrt_nonneg qCap) radius_sq.le hd.1 hd.2.1 hd.2.2.1 hb
    have hcoef := mul_le_mul_of_nonneg_right hd.2.2.2 hb.1
    nlinarith

theorem low_negative_endpoint_lower {k l m : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : m∈Icc l ((3/2)*l)) (j : Fin 4) :
    min (V R k 1 frameCap) (V R k l frameCap)≤
      V R (pWeights k l m j) (qWeights k l m j) frameCap := by
  fin_cases j
  · exact min_le_left _ _
  · exact min_le_right _ _
  · change min (V R k 1 frameCap) (V R k l frameCap)≤V R (min l m) (max l m) frameCap
    rw [min_eq_left hm.1,max_eq_right hm.1]
    have hB := V_endpoint_lower sqrt_cap_lower (show 0<l by linarith [hl.1])
      hm.1 (show m≤2*l by linarith [hm.2])
    have hH := H_negative_endpoint_upper (show k∈Icc (1/2:ℝ) (17/20) from
      ⟨by linarith [hk.1],hk.2⟩)
    exact (min_le_left _ _).trans (by linarith [hl.1])
  · exact min_le_left _ _

theorem low_saturated_lower {k l m t : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : m∈Icc l ((3/2)*l)) (ht : t∈Icc 0 (1/6:ℝ)) (i : Fin 4) :
    lowEnvelope k l m t≤
      Hybrid.saturated R (diagonal-1/2) (pWeights k l m) (qWeights k l m) 3 i t := by
  have ht' := PositiveTD.Certificate.low_frame_domain ht
  have hb := low_envelope_bounds k l m t
  have hp := low_pure_lower hk hl hm ht i
  fin_cases i
  · change lowEnvelope k l m t≤M R k 1 t
    exact hb.1.trans (M_ge_V (by linarith [hk.1]) (by norm_num) (by linarith [hk.1]) ht')
  · change lowEnvelope k l m t≤M R k l t
    rw [M_correction]
    change V R k 1 t≤V R k l t at hp
    linarith [hb.2.1]
  · change lowEnvelope k l m t≤M R (min l m) (max l m) t
    rw [min_eq_left hm.1,max_eq_right hm.1]
    change V R k 1 t≤V R (min l m) (max l m) t at hp
    rw [min_eq_left hm.1,max_eq_right hm.1] at hp
    exact (hb.1.trans hp).trans (M_ge_V (by linarith [hl.1])
      (by linarith [hl.1,hm.1]) hm.2 ht')
  · change lowEnvelope k l m t≤-(diagonal-1/2)*(frameCap-t)+V R k 1 frameCap
    have hD := low_positive_lower hk hl hm ht' (3:Fin 4)
    change -(109/200)*m*(frameCap-t)≤-(diagonal-1/2)*(frameCap-t) at hD
    linarith [hb.2.2.1]

theorem low_endpoint_lower {k l m t : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : m∈Icc l ((3/2)*l)) (ht : t∈Icc 0 (1/6:ℝ)) (i j : Fin 4) :
    lowEnvelope k l m t≤endpoint k l m t i j := by
  have ht' := PositiveTD.Certificate.low_frame_domain ht
  have hb := low_envelope_bounds k l m t
  unfold endpoint
  apply le_min
  · exact hb.1.trans (low_pure_lower hk hl hm ht j)
  · by_cases hij : i=j
    · subst j
      simp only [if_pos rfl]
      exact low_saturated_lower hk hl hm ht i
    · simp only [if_neg hij]
      have hp := low_positive_lower hk hl hm ht' i
      have hn := low_negative_endpoint_lower hk hl hm j
      have hbase : lowEnvelope k l m t+(109/200)*m*(frameCap-t)≤
          min (V R k 1 frameCap) (V R k l frameCap) := by
        apply le_min <;> linarith [hb.2.2.1,hb.2.2.2]
      linarith

theorem balanced_pure_lower (k l m t : ℝ) (j : Fin 4) :
    balancedEnvelope k l m t≤V R (pWeights k l m j) (qWeights k l m j) t := by
  fin_cases j
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)
  · exact min_le_left _ _

theorem balanced_separated_lower {k l m t : ℝ}
    (hp : ∀i,0<pWeights k l m i) (hpq : ∀i,pWeights k l m i≤qWeights k l m i)
    (hbal : ∀i,2*qWeights k l m i≤3*pWeights k l m i)
    (hratio : ∀i j,5*qWeights k l m i≤6*qWeights k l m j)
    (ht : t∈Icc 0 frameCap) (i j : Fin 4) :
    balancedEnvelope k l m t≤
      Hybrid.positive R (diagonal-1/2) (pWeights k l m) (qWeights k l m) 3 i (frameCap-t)+
        V R (pWeights k l m j) (qWeights k l m j) frameCap := by
  have hb : frameCap-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hq0 : 0<qWeights k l m j := (hp j).trans_le (hpq j)
  have hpositive : -(109/200)*qWeights k l m i*(frameCap-t)≤
      Hybrid.positive R (diagonal-1/2) (pWeights k l m) (qWeights k l m) 3 i (frameCap-t) := by
    by_cases hi : i=3
    · subst i
      change -(109/200)*1*(frameCap-t)≤-(diagonal-1/2)*(frameCap-t)
      have hc := mul_le_mul_of_nonneg_right
        (show diagonal-1/2≤109/200 by linarith [diagonal_bounds.2]) hb.1
      nlinarith
    · simp only [Hybrid.positive,if_neg hi]
      exact U_lower (Real.sqrt_nonneg qCap) radius_sq.le (hp i) (hpq i)
        (by linarith [hbal i]) hb
  have hnegative := V_growth (hp j) (hpq j) (by linarith [hbal j]) ht
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht.2
  have hcoef : (19/1500)*qWeights k l m j≤
      (2/3)*qWeights k l m j-(109/200)*qWeights k l m i := by
    linarith [hratio i j]
  have hprod := mul_le_mul_of_nonneg_right hcoef hb.1
  have hreserve : 0≤(19/1500)*qWeights k l m j*(frameCap-t) := by positivity
  linarith [balanced_pure_lower k l m t j]

/-- The three single-negative alternatives bound every high alternative. -/
theorem balanced_endpoint_lower {k l m t : ℝ}
    (hp : ∀i,0<pWeights k l m i) (hpq : ∀i,pWeights k l m i≤qWeights k l m i)
    (hbal : ∀i,2*qWeights k l m i≤3*pWeights k l m i)
    (hratio : ∀i j,5*qWeights k l m i≤6*qWeights k l m j)
    (ht : t∈Icc 0 frameCap) (i j : Fin 4) :
    balancedEnvelope k l m t≤endpoint k l m t i j := by
  unfold endpoint
  apply le_min (balanced_pure_lower k l m t j)
  by_cases hij : i=j
  · subst j
    simp only [if_pos rfl]
    by_cases hi : i=3
    · subst i
      exact balanced_separated_lower hp hpq hbal hratio ht 3 3
    · simp only [Hybrid.saturated,if_neg hi]
      exact (balanced_pure_lower k l m t i).trans
        (M_ge_V (hp i).le ((hp i).trans_le (hpq i)).le (by linarith [hbal i]) ht)
  · simp only [if_neg hij]
    exact balanced_separated_lower hp hpq hbal hratio ht i j

theorem low_T_endpoint_positive {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) (i j : Fin 4) :
    0<splitScalar (Explicit.lowK t) (Explicit.lowL t) (Explicit.lowC t) t 0 i j := by
  simpa only [splitScalar,splitBase,sub_zero,ASupport.charge_zero,mul_zero,add_zero,
    endpoint,PositiveTD.endpoint] using PositiveTD.Certificate.low_endpoint_positive ht i j

theorem low_A_endpoint_positive {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) (i j : Fin 4) :
    0<splitScalar (Explicit.lowK t) (Explicit.lowL t) (Explicit.lowC t) t t i j := by
  obtain ⟨hklo,hkhi,hllo,hlc,hchi,hlk⟩ := Explicit.low_ranges ht
  have hdom := low_split_domain ht (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,ht.1⟩)
  have hH := Certificate.low_A_H_positive ht
  have hM := Certificate.low_A_M_positive ht
  have hSH := Certificate.low_A_SH_positive ht
  have hSG := Certificate.low_A_SG_positive ht
  have hbase : 0<baseline (Explicit.lowK t) (Explicit.lowL t) (Explicit.lowC t) 0+
      Explicit.lowL t*ASupport.charge t+
        lowEnvelope (Explicit.lowK t) (Explicit.lowL t) (Explicit.lowC t) t := by
    unfold lowEnvelope
    rw [add_min,add_min,add_min]
    exact lt_min hH (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have he := low_endpoint_lower ⟨hklo.le,by linarith⟩ ⟨hllo.le,hlk.le⟩
    ⟨hlc,hdom.2.2.2.2.1⟩ ht i j
  simp only [splitScalar,splitBase,sub_self,tilted,Real.cos_zero,Real.sin_zero,
    mul_zero,add_zero,mul_one]
  linarith

theorem high_endpoint_positive (e : Certificate.Endpoint) {t : ℝ}
    (ht : t∈Icc (1/6:ℝ) frameCap) (i j : Fin 4) :
    0<Certificate.endpointBase e t+
      endpoint (Certificate.kAt t) (Certificate.lAt t) (Certificate.mAt e t) t i j := by
  have hz : Certificate.zAt e t∈Icc 0 t := by
    cases e <;> simp only [Certificate.zAt] <;> constructor <;> linarith [ht.1]
  have hd := high_split_domain ht hz
  have hb := high_balanced ht hz
  have hz' : Certificate.zAt e t∈Icc 0 frameCap := ⟨hz.1,hz.2.trans ht.2⟩
  have hc := PositiveTD.coefficient_domain hd.1 hd.2.1 hd.2.2.1 hz' hd.2.2.2.1
  have he := balanced_endpoint_lower (fun i => (hc i).1) (fun i => (hc i).2.1)
    hb.1 hb.2 (Certificate.high_frame_domain ht) i j
  have hp := Certificate.high_six_scalars_positive e ht
  have hm : 0<Certificate.endpointBase e t+
      balancedEnvelope (Certificate.kAt t) (Certificate.lAt t) (Certificate.mAt e t) t := by
    unfold balancedEnvelope
    rw [add_min,add_min]
    exact lt_min hp.1 (lt_min hp.2.1 hp.2.2)
  exact hm.trans_le (add_le_add_left he _)

end SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive
