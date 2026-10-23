module

public import SquaresInCircles.Eight.TableFree.CriticalPositiveTPureCharges
public import SquaresInCircles.Eight.TableFree.CriticalPositiveTGap
public import SquaresInCircles.Eight.TableFree.SolePositiveTSameBlock

/-!
# The critical positive-T envelope on the original ordinary domain

Uncompiled transcription of sections 4 and 5 of the critical hand
proof. Every pure and far charge dominates the same TD B charge.
The H and TD B mixed alternatives retain their actual two angles.
The original P,N budgets are used before concentration.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.CriticalPositiveTEnvelope
open CriticalPositiveTCoefficients CriticalPositiveTPureCharges
open ExceptionalPositiveTBlocks ExceptionalContactStress
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open SingleAngleConcavity

theorem H_data {t z k l c m eta x e : ℝ} (td : Bool)
    (h : Bounds t z k l c m eta) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    37/40<small (weights td k l c m eta x e) 0 ∧
      large (weights td k l c m eta x e) 0∈Icc 1 (26/25:ℝ) := by
  have hf := h.tilt hx
  have hg := h.tilt he
  have hk : 0≤k := by linarith [h.k_lower]
  have hn0 := mul_le_mul_of_nonneg_left hf.1 hk
  have hn1 := mul_lt_mul h.k_upper hf.2
    (by linarith [hf.1] : 0≤tilt eta x) (by norm_num : (0:ℝ)<199/200)
  change 37/40<min (tilt eta e) (k*tilt eta x) ∧
    max (tilt eta e) (k*tilt eta x)∈Icc 1 (26/25:ℝ)
  refine ⟨lt_min (by linarith) (by linarith),?_,?_⟩
  · exact hg.1.trans (le_max_left _ _)
  · exact max_le hg.2.le (by linarith)

theorem ordinary_data {t z k l c m eta x e : ℝ} (td : Bool)
    (h : Bounds t z k l c m eta) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    (∀ i,0<small (weights td k l c m eta x e) i) ∧
    (∀ i,large (weights td k l c m eta x e) i≤2*small (weights td k l c m eta x e) i) ∧
    (∀ i,large (weights td k l c m eta x e) i≤26/25) := by
  have hH := H_data td h hx he
  have ho := h.order
  have hc : 0<c := by linarith [h.c_lower]
  have hm : 0<m := hc.trans_le h.c_le_m
  have hc1 : c≤1 := h.c_le_m.trans h.m_upper.le
  have hm1 : m≤1 := h.m_upper.le
  have hk1 : k≤1 := by linarith [h.k_upper]
  refine ⟨?_,?_,?_⟩
  · intro i
    fin_cases i
    · linarith [hH.1]
    all_goals cases td <;>
      simp [small,first,second,weights,min_eq_left,min_eq_right,ho.2.1,ho.2.2.1,
        ho.2.2.2.1,hc1,hm1,h.ell_pos,hc,hm]
  · intro i
    fin_cases i
    · linarith [hH.1,hH.2.2]
    all_goals cases td <;>
      simp [small,large,first,second,weights,min_eq_left,min_eq_right,max_eq_left,
        max_eq_right,ho.2.1,ho.2.2.1,ho.2.2.2.1,hc1,hm1] <;>
      linarith [ho.2.2.2.2.1,ho.2.2.2.2.2.1,ho.2.2.2.2.2.2,h.c_lower,h.c_le_m]
  · intro i
    fin_cases i
    · exact hH.2.2
    all_goals cases td <;>
      simp [large,first,second,weights,max_eq_left,max_eq_right,ho.2.1,
        ho.2.2.1,ho.2.2.2.1,hc1,hm1] <;> linarith [hk1,hm1,hc1]

theorem pure_dominates {R t z k l c m eta x e : ℝ} (td : Bool)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (h : Bounds t z k l c m eta) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    V R l m t≤pure (single td i) R (small (weights td k l c m eta x e) i)
      (large (weights td k l c m eta x e) i) (negative (weights td k l c m eta x e) td i) t ∧
    V R l m frameCap≤pure (single td i) R (small (weights td k l c m eta x e) i)
      (large (weights td k l c m eta x e) i) (negative (weights td k l c m eta x e) td i) frameCap := by
  rw [pure_eq,pure_eq]
  have hR2 : R∈Icc 0 2 := ⟨hR,by linarith [radius_upper hR hQU]⟩
  have ho := h.order
  have hc1 : c≤1 := h.c_le_m.trans h.m_upper.le
  have hm1 : m≤1 := h.m_upper.le
  fin_cases i
  · have hh := H_data td h hx he
    apply wide_dominates hR hQL hQU
      (by dsimp [base]; linarith [hh.1]) (small_le_large _ _) hh.2
    · simpa [negative,large,first,second,weights] using hh.2.2
    · exact h
  · simpa [small,large,first,second,negative,weights,min_eq_right ho.2.1,
      max_eq_left ho.2.1] using ⟨A_ge_B hR2 h,A_ge_B_at_cap hR2 h⟩
  · cases td
    · simpa [small,large,first,second,negative,weights,min_eq_left ho.2.2.1,
        max_eq_right ho.2.2.1] using ⟨BT_ge_B hR2 h,BT_ge_B_at_cap hR2 h⟩
    · simp [small,large,first,second,negative,weights,min_eq_left ho.2.2.2.1,
        max_eq_right ho.2.2.2.1,Vnu,V]
  · cases td
    · have hw := wide_dominates hR hQL hQU
        (show base≤m by dsimp [base]; linarith [h.c_lower,h.c_le_m]) hm1
        (show (1:ℝ)∈Icc 1 (26/25:ℝ) by norm_num)
        (show m≤26/25 by linarith [h.m_upper]) h
      simpa [small,large,first,second,negative,weights,min_eq_right hm1,max_eq_left hm1] using hw
    · have hw := wide_dominates hR hQL hQU
        (show base≤c by dsimp [base]; linarith [h.c_lower]) hc1
        (show (1:ℝ)∈Icc 1 (26/25:ℝ) by norm_num)
        (show c≤26/25 by linarith) h
      simpa [small,large,first,second,negative,weights,min_eq_right hc1,max_eq_left hc1] using hw

theorem same_block {R t z k l c m eta x e : ℝ} (td : Bool)
    (h : Bounds t z k l c m eta) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (i : Fin 4) (hi : single td i=false) :
    pure (single td i) R (small (weights td k l c m eta x e) i)
      (large (weights td k l c m eta x e) i) (negative (weights td k l c m eta x e) td i) t≤
      M R (small (weights td k l c m eta x e) i)
        (large (weights td k l c m eta x e) i) t := by
  simp only [pure,hi,if_false]
  have hp := (ordinary_data td h hx he).1 i
  have hq := hp.trans_le (small_le_large _ _)
  have hindices : i=0 ∨ i=2 := by fin_cases i <;> cases td <;> simp_all [single]
  rcases hindices with rfl | rfl
  · have hh := H_data td h hx he
    apply M_ge_V hp.le hq.le _ h.angle
    nlinarith [hh.1,hh.2.2]
  · have htd : td=true := by cases td <;> simp_all [single]
    subst td
    have ho := h.order
    simp only [small,large,first,second,weights,Matrix.cons_val_two,Matrix.cons_val_one,
      Matrix.cons_val_zero,if_true,min_eq_left ho.2.2.2.1,max_eq_right ho.2.2.2.1]
    apply SolePositiveTSameBlock.from_bracket (show 0≤m by linarith [h.c_lower,h.c_le_m])
      h.ell_m_lower.le h.angle
    have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
    have hc := (transport_trig hh).1
    have hs := (transport_trig hh).2.2.2.1
    apply SolePositiveTSameBlock.half_angle_bracket h.angle (by linarith)
    have hlen : (27/50:ℝ)≤frameCap-t := by norm_num [frameCap]; linarith [h.angle_upper]
    have hm := mul_le_mul (show (387/2500:ℝ)≤Real.cos frameCap-61/100 by linarith)
      hlen (by norm_num) (by linarith)
    linarith

theorem original_increment {C : SignedCycle} {ab : Fin 4} (td : Bool)
    {R t z k l c m eta x e : ℝ} (hab : ab=0 ∨ ab=2)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (h : Bounds t z k l c m eta) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hT : 0≤ExceptionalPositiveTStress.primary C td)
    (htotal : delta C.theta G+delta C.theta D+ExceptionalPositiveTStress.primary C td=t) :
    V R l m t≤increment C ab td (weights td k l c m eta x e) R := by
  have hw := ordinary_data td h hx he
  apply original_lower td (weights td k l c m eta x e) hab hR hQU hw.1 hw.2.1
    ha hvar hG hD hT htotal
  · intro i
    exact (pure_dominates td hR hQL hQU h hx he i).1
  · intro i hi
    exact (pure_dominates td hR hQL hQU h hx he i).1.trans (same_block td h hx he i hi)
  · intro i j _
    have hlen : 0≤frameCap-t := by linarith [h.angle.2]
    have hU := OrdinaryPositiveEnvelope.U_lower hR hQU (hw.1 i) (small_le_large _ _) (hw.2.1 i)
      (show frameCap-t∈Icc 0 frameCap from ⟨hlen,by linarith [h.angle.1]⟩)
    have hV := (pure_dominates td hR hQL hQU h hx he j).2
    have hgap := CriticalPositiveTGap.scaled_gap hR hQL hQU
      (show CriticalPositiveTGap.scale≤m by
        dsimp [CriticalPositiveTGap.scale]; linarith [h.c_lower,h.c_le_m])
      h.ell_m_upper.le h.ell_m_lower.le ⟨h.angle.1,h.angle_upper⟩
    have hpay := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hw.2.2 i) (by norm_num : (0:ℝ)≤109/200)) hlen
    have hreserve := mul_nonneg (show (0:ℝ)≤(4201/5000)*(3/4)-(109/200)*(26/25) by norm_num) hlen
    dsimp [CriticalPositiveTGap.scale] at hgap
    linarith

end SquaresInCircles.Eight.TableFree.CriticalPositiveTEnvelope
