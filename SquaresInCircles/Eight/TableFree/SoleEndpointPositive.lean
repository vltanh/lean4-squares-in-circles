module

public import SquaresInCircles.Eight.TableFree.SoleEndpointCharges

/-!
# Strict positivity at both intrinsic sole-E endpoints

Uncompiled source. The concrete scalar estimates are combined with the
original ordinary signed-angle budgets. The low interval uses B alone;
the middle and high intervals use the minimum of the four actual pure
charges. Every scalar is evaluated at the actual common radius.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SoleEndpointPositive
open Candidate SoleECoefficients SoleOrdinaryData SoleOriginalBlocks
open SoleEndpointSupport SoleScalarEndpointAlgebra SoleEndpointCharges
open SingleAngleConcavity SoleBalancedEnvelope
open SoleScalarPolynomials (band atG isDE)

theorem G_pure_positive {b : Band} (de : Bool) {q t : ℝ}
    (ht : t∈domain b) (hq : q≤qTrial) {i : Fin 4} (hi : b=.low → i=2) :
    0<Gbase b (Real.sqrt q) t+
      pure (single de i) (Real.sqrt q) (small b de t t 0 i)
        (large b de t t 0 i) (nu b de t t 0 i) t := by
  have hp := SoleScalarTransfer.actual_radius_positive (Gcase b de i)
    (by simpa only [Gcase_band] using ht) hq
  rw [value_decomposition,base_at_G _ _ _ _ (Gcase_atG b de i),Gcase_band] at hp
  exact lt_of_lt_of_le hp (add_le_add_left (G_charge_le de ht (Real.sqrt q) hi) _)

theorem E_pure_positive {b : Band} (de : Bool) {q t : ℝ}
    (ht : t∈domain b) (hq : q≤qTrial) {i : Fin 4} (hi : b=.low → i=2) :
    0<Ebase b de (Real.sqrt q) (axisCoordinate q) t+
      pure (single de i) (Real.sqrt q) (small b de t 0 t i)
        (large b de t 0 t i) (nu b de t 0 t i) t := by
  have hp := SoleScalarTransfer.actual_radius_positive (Ecase b de i)
    (by simpa only [Ecase_band] using ht) hq
  have hb : Ebase b (isDE (Ecase b de i)) (Real.sqrt q) (axisCoordinate q) t=
      Ebase b de (Real.sqrt q) (axisCoordinate q) t := by
    cases b <;> cases de <;> simp [Ecase,isDE,Ebase]
  rw [value_decomposition,base_at_E _ _ _ _ (Ecase_atG b de i),Ecase_band,hb] at hp
  exact lt_of_lt_of_le hp (add_le_add_left (E_charge_le de ht (Real.sqrt q) hi) _)

theorem B_pure {b : Band} {de : Bool} {t x e : ℝ} (ht : t∈domain b) (R : ℝ) :
    pure (single de 2) R (small b de t x e 2) (large b de t x e 2)
      (nu b de t x e 2) t=OrdinaryAngleConcavity.V R (ell b t) (c b t) t := by
  rcases B_data (de := de) (x := x) (e := e) ht with ⟨hp,hq,hnu⟩
  simp [single,pure,hp,hq,hnu]

theorem G_original_positive {C : SignedCycle} {ab : Fin 4} {b : Band} (de : Bool) {q t : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (hQU : q≤qTrial) (ht : t∈domain b)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤primary C de)
    (htotal : delta C.theta G+primary C de=t) :
    0<Gbase b (Real.sqrt q) t+increment C ab b de (Real.sqrt q) t t 0 := by
  have hq0 : 0≤q := by dsimp [qLow] at hQL; linarith
  have hR := Real.sqrt_nonneg q
  have hR2 := Real.sq_sqrt hq0
  have hcap := hQU.trans uniform_radius_order.2.2.1.le
  have hxt : t∈Icc 0 t := ⟨(angle ht).1,le_rfl⟩
  have he0 : (0:ℝ)∈Icc 0 t := ⟨le_rfl,(angle ht).1⟩
  by_cases hb : b=.low
  · subst b
    have hinc := low_original_increment hab hR (by simpa only [hR2] using hQL)
      (by simpa only [hR2] using hcap) ht hxt he0 ha hvar hG hE htotal
    have hp := G_pure_positive de ht hQU (i := 2) (by intro _; rfl)
    rw [B_pure ht] at hp
    linarith
  · let f : Fin 4 → ℝ := fun i => pure (single de i) (Real.sqrt q)
      (small b de t t 0 i) (large b de t t 0 i) (nu b de t t 0 i) t
    have hinc := balanced_original_increment hb hab hR
      (by simpa only [hR2] using hQL) (by simpa only [hR2] using hcap)
      ht hxt he0 ha hvar hG hE htotal (minimumFour_le f)
    have hp : 0<Gbase b (Real.sqrt q) t+minimumFour f :=
      minimumFour_positive (fun i => G_pure_positive de ht hQU (i := i)
        (fun hh => (hb hh).elim))
    linarith

theorem E_original_positive {C : SignedCycle} {ab : Fin 4} {b : Band} (de : Bool) {q t : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (hQU : q≤qTrial) (ht : t∈domain b)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤primary C de)
    (htotal : delta C.theta G+primary C de=t) :
    0<Ebase b de (Real.sqrt q) (axisCoordinate q) t+
      increment C ab b de (Real.sqrt q) t 0 t := by
  have hq0 : 0≤q := by dsimp [qLow] at hQL; linarith
  have hR := Real.sqrt_nonneg q
  have hR2 := Real.sq_sqrt hq0
  have hcap := hQU.trans uniform_radius_order.2.2.1.le
  have hx0 : (0:ℝ)∈Icc 0 t := ⟨le_rfl,(angle ht).1⟩
  have het : t∈Icc 0 t := ⟨(angle ht).1,le_rfl⟩
  by_cases hb : b=.low
  · subst b
    have hinc := low_original_increment hab hR (by simpa only [hR2] using hQL)
      (by simpa only [hR2] using hcap) ht hx0 het ha hvar hG hE htotal
    have hp := E_pure_positive de ht hQU (i := 2) (by intro _; rfl)
    rw [B_pure ht] at hp
    linarith
  · let f : Fin 4 → ℝ := fun i => pure (single de i) (Real.sqrt q)
      (small b de t 0 t i) (large b de t 0 t i) (nu b de t 0 t i) t
    have hinc := balanced_original_increment hb hab hR
      (by simpa only [hR2] using hQL) (by simpa only [hR2] using hcap)
      ht hx0 het ha hvar hG hE htotal (minimumFour_le f)
    have hp : 0<Ebase b de (Real.sqrt q) (axisCoordinate q) t+minimumFour f :=
      minimumFour_positive (fun i => E_pure_positive de ht hQU (i := i)
        (fun hh => (hb hh).elim))
    linarith

theorem fixed_endpoints {C : SignedCycle} {ab : Fin 4} {b : Band} (de : Bool) {q t : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (hQU : q≤qTrial) (ht : t∈domain b)
    (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤primary C de)
    (htotal : delta C.theta G+primary C de=t) :
    0<SoleSplitModel.value C ab b de (Real.sqrt q) (axisCoordinate q) t 0 ∧
      0<SoleSplitModel.value C ab b de (Real.sqrt q) (axisCoordinate q) t t := by
  have hq0 : 0≤q := by dsimp [qLow] at hQL; linarith
  have hR2 := Real.sq_sqrt hq0
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by
    simpa only [hR2] using hC.contained
  have hx0 : (0:ℝ)∈Icc 0 t := ⟨le_rfl,(angle ht).1⟩
  have hxt : t∈Icc 0 t := ⟨(angle ht).1,le_rfl⟩
  have hEbound := SoleSplitAnchorBounds.value_lower de hab (Real.sqrt_nonneg q) ht hx0 hc hn ha
    (Z := endpointWork b de (Real.sqrt q) (axisCoordinate q) t)
    (by simpa only [sub_zero] using at_E de hQL ht (hC.sorted E) (hC.contained E))
  have hGbound := SoleSplitAnchorBounds.value_lower de hab (Real.sqrt_nonneg q) ht hxt hc hn ha
    (M := axisCoordinate q) (Z := 0)
    (by simp only [sub_self,at_G,le_refl])
  simp only [sub_zero,baseline_at_E de _ _ _ ht] at hEbound
  simp only [sub_self,baseline_at_G de _ _ ht] at hGbound
  exact ⟨(E_original_positive de hab hQL hQU ht ha hvar hG hE htotal).trans_le hEbound,
    (G_original_positive de hab hQL hQU ht ha hvar hG hE htotal).trans_le hGbound⟩

end SquaresInCircles.Eight.TableFree.SoleEndpointPositive
