module

public import SquaresInCircles.Eight.TableFree.GlobalGATD2Coordinate

/-!
# Four scalar expressions cover every low-angle TD2 alternative

Uncompiled source.  The coefficient comparisons and the ordinary
whole-angle envelopes cover all four blocks and both intrinsic
concentration alternatives.  The D positive part remains its actual
linear clipped-circle bound.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open OrdinaryNegativeEnvelope OrdinaryPositiveEnvelope

def lowEnvelope (k l c z : ℝ) : ℝ :=
  min (V R k 1 z)
    (min (V R k 1 z+k*(phi (frameCap-z)-1)+l*(Real.cos frameCap-Real.cos z))
      (min (-(109/200)*tilted c z*(frameCap-z)+V R k 1 frameCap)
        (-(109/200)*tilted c z*(frameCap-z)+V R k l frameCap)))

theorem low_envelope_bounds (k l c z : ℝ) :
    lowEnvelope k l c z≤V R k 1 z ∧
    lowEnvelope k l c z≤V R k 1 z+k*(phi (frameCap-z)-1)+
      l*(Real.cos frameCap-Real.cos z) ∧
    lowEnvelope k l c z≤-(109/200)*tilted c z*(frameCap-z)+V R k 1 frameCap ∧
    lowEnvelope k l c z≤-(109/200)*tilted c z*(frameCap-z)+V R k l frameCap := by
  unfold lowEnvelope
  exact ⟨min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩

theorem low_coefficient_data {k l c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : tilted c z∈Icc l ((3/2)*l)) (i : Fin 4) :
    0<pWeights k l (tilted c z) i ∧
      pWeights k l (tilted c z) i≤qWeights k l (tilted c z) i ∧
      qWeights k l (tilted c z) i≤2*pWeights k l (tilted c z) i ∧
      qWeights k l (tilted c z) i≤tilted c z := by
  have hk0 : 0<k := by linarith [hk.1]
  have hl0 : 0<l := by linarith [hl.1]
  fin_cases i
  · change 0<k ∧ k≤1 ∧ 1≤2*k ∧ 1≤tilted c z
    exact ⟨hk0,by linarith [hk.2],by linarith [hk.1],hl.1.trans hm.1⟩
  · change 0<k ∧ k≤l ∧ l≤2*k ∧ l≤tilted c z
    exact ⟨hk0,by linarith [hk.2,hl.1],hl.2,hm.1⟩
  · change 0<min l (tilted c z) ∧ min l (tilted c z)≤max l (tilted c z) ∧
      max l (tilted c z)≤2*min l (tilted c z) ∧ max l (tilted c z)≤tilted c z
    rw [min_eq_left hm.1,max_eq_right hm.1]
    exact ⟨hl0,hm.1,by linarith [hm.2],le_rfl⟩
  · change 0<k ∧ k≤1 ∧ 1≤2*k ∧ 1≤tilted c z
    exact ⟨hk0,by linarith [hk.2],by linarith [hk.1],hl.1.trans hm.1⟩

theorem low_pure_lower {k l c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : tilted c z∈Icc l ((3/2)*l)) (hz : z∈Icc 0 (1/6:ℝ)) (j : Fin 4) :
    V R k 1 z≤V R (pWeights k l (tilted c z) j)
      (qWeights k l (tilted c z) j) z := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hk0 : 0<k := by linarith [hk.1]
  have hl0 : 0<l := by linarith [hl.1]
  fin_cases j
  · exact le_rfl
  · change V R k 1 z≤V R k l z
    exact V_short_second_coefficient hk0 (by norm_num) hl.1 hl.2 hz
  · change V R k 1 z≤V R (min l (tilted c z)) (max l (tilted c z)) z
    rw [min_eq_left hm.1,max_eq_right hm.1]
    have hfirst : V R k 1 z≤V R l 1 z := V_first_coefficient (by norm_num)
      (by linarith [hk.1]) (by linarith [hk.2,hl.1])
      (by linarith [hl.2,hk.2]) hz'
    exact hfirst.trans (V_short_second_coefficient hl0 (by norm_num)
      (hl.1.trans hm.1) (by linarith [hm.2]) hz)
  · exact le_rfl

theorem low_positive_lower {k l c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : tilted c z∈Icc l ((3/2)*l)) (hz : z∈Icc 0 frameCap) (i : Fin 4) :
    -(109/200)*tilted c z*(frameCap-z)≤
      Hybrid.positive R (diagonal-1/2) (pWeights k l (tilted c z))
        (qWeights k l (tilted c z)) 3 i (frameCap-z) := by
  have ha : frameCap-z∈Icc 0 frameCap := ⟨by linarith [hz.2],by linarith [hz.1]⟩
  by_cases hi : i=3
  · subst i
    simp only [Hybrid.positive,if_pos rfl]
    have hcoef : diagonal-1/2≤(109/200)*tilted c z := by
      linarith [diagonal_bounds.2,hl.1,hm.1]
    have hh := mul_le_mul_of_nonneg_right hcoef ha.1
    nlinarith
  · simp only [Hybrid.positive,if_neg hi]
    have hd := low_coefficient_data hk hl hm i
    have hU := U_lower (Real.sqrt_nonneg qCap) radius_sq.le hd.1 hd.2.1 hd.2.2.1 ha
    have hcoef := mul_le_mul_of_nonneg_right hd.2.2.2 ha.1
    nlinarith

theorem low_negative_endpoint_lower {k l c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : tilted c z∈Icc l ((3/2)*l)) (j : Fin 4) :
    min (V R k 1 frameCap) (V R k l frameCap)≤
      V R (pWeights k l (tilted c z) j) (qWeights k l (tilted c z) j) frameCap := by
  fin_cases j
  · exact min_le_left _ _
  · exact min_le_right _ _
  · change min (V R k 1 frameCap) (V R k l frameCap)≤
      V R (min l (tilted c z)) (max l (tilted c z)) frameCap
    rw [min_eq_left hm.1,max_eq_right hm.1]
    have hB := V_endpoint_lower sqrt_cap_lower (show 0<l by linarith [hl.1])
      hm.1 (show tilted c z≤2*l by linarith [hm.2])
    have hH := H_negative_endpoint_upper (show k∈Icc (1/2:ℝ) (17/20) from
      ⟨by linarith [hk.1],hk.2⟩)
    exact (min_le_left _ _).trans (by linarith [hl.1])
  · exact min_le_left _ _

theorem M_correction (p q z : ℝ) :
    M R p q z=V R p q z+p*(phi (frameCap-z)-1)+q*(Real.cos frameCap-Real.cos z) := by
  dsimp [M,V]
  ring

theorem low_saturated_lower {k l c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : tilted c z∈Icc l ((3/2)*l)) (hz : z∈Icc 0 (1/6:ℝ)) (i : Fin 4) :
    lowEnvelope k l c z≤Hybrid.saturated R (diagonal-1/2)
      (pWeights k l (tilted c z)) (qWeights k l (tilted c z)) 3 i z := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hb := low_envelope_bounds k l c z
  have hp := low_pure_lower hk hl hm hz i
  fin_cases i
  · change lowEnvelope k l c z≤M R k 1 z
    exact hb.1.trans (M_ge_V (by linarith [hk.1]) (by norm_num)
      (by linarith [hk.1]) hz')
  · change lowEnvelope k l c z≤M R k l z
    rw [M_correction]
    change V R k 1 z≤V R k l z at hp
    linarith [hb.2.1]
  · change lowEnvelope k l c z≤M R (min l (tilted c z)) (max l (tilted c z)) z
    rw [min_eq_left hm.1,max_eq_right hm.1]
    change V R k 1 z≤V R (min l (tilted c z)) (max l (tilted c z)) z at hp
    rw [min_eq_left hm.1,max_eq_right hm.1] at hp
    exact (hb.1.trans hp).trans (M_ge_V (by linarith [hl.1])
      (by linarith [hl.1,hm.1]) hm.2 hz')
  · change lowEnvelope k l c z≤-(diagonal-1/2)*(frameCap-z)+V R k 1 frameCap
    have hD := low_positive_lower hk hl hm hz' (3:Fin 4)
    change -(109/200)*tilted c z*(frameCap-z)≤-(diagonal-1/2)*(frameCap-z) at hD
    linarith [hb.2.2.1]

/-- Every intrinsic alternative lies above the same four explicit
expressions.  No original angle or witness is changed here. -/
theorem low_endpoint_lower {k l c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : tilted c z∈Icc l ((3/2)*l)) (hz : z∈Icc 0 (1/6:ℝ)) (i j : Fin 4) :
    lowEnvelope k l c z≤endpoint k l c z i j := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hb := low_envelope_bounds k l c z
  unfold endpoint
  apply le_min
  · exact hb.1.trans (low_pure_lower hk hl hm hz j)
  · by_cases hij : i=j
    · subst j
      simp only [if_pos rfl]
      exact low_saturated_lower hk hl hm hz i
    · simp only [if_neg hij]
      have hp := low_positive_lower hk hl hm hz' i
      have hn := low_negative_endpoint_lower hk hl hm j
      have hbase : lowEnvelope k l c z+(109/200)*tilted c z*(frameCap-z)≤
          min (V R k 1 frameCap) (V R k l frameCap) := by
        apply le_min <;> linarith [hb.2.2.1,hb.2.2.2]
      linarith

theorem low_scalars_positive {k l c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hl : l∈Icc 1 (2*k))
    (hm : tilted c z∈Icc l ((3/2)*l)) (hz : z∈Icc 0 (1/6:ℝ))
    (hH : 0<baseline k l c z+V R k 1 z)
    (hM : 0<baseline k l c z+V R k 1 z+k*(phi (frameCap-z)-1)+
      l*(Real.cos frameCap-Real.cos z))
    (hSH : 0<baseline k l c z-(109/200)*tilted c z*(frameCap-z)+V R k 1 frameCap)
    (hSG : 0<baseline k l c z-(109/200)*tilted c z*(frameCap-z)+V R k l frameCap)
    (i j : Fin 4) : 0<baseline k l c z+endpoint k l c z i j := by
  have hlow : 0<baseline k l c z+lowEnvelope k l c z := by
    unfold lowEnvelope
    rw [add_min,add_min,add_min]
    exact lt_min hH (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  exact hlow.trans_le (add_le_add_left (low_endpoint_lower hk hl hm hz i j) _)

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD
