module

public import SquaresInCircles.Eight.Frames.Ordinary.AngleConcentration

/-!
# Eight squares: concentration with both primary angles removed

Removing the positive primary `d` and negative
primary `s` leaves separate caps `h-d` and `h-s`. The common variation
is reduced to its intrinsic endpoints with both caps unchanged.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.RemovedPrimaryConcentration
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration

theorem negative_concentration {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (R : ℝ) (p q P N : ι → ℝ) {d s : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : ∀ i,0<p i) (hpq : ∀ i,p i≤q i) (hqp : ∀ i,q i≤2*p i)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hd : d∈Icc 0 frameCap) (hs : s∈Icc 0 d)
    (hbudget : (∑ i,P i)≤frameCap-d)
    (hbalance : (∑ i,N i)=d-s+∑ i,P i) :
    ∃ i j, min (V R (p j) (q j) (d-s))
      (if i=j then mixedBlock R (p i) (q i) (frameCap-d) (frameCap-s)
       else U R (p i) (q i) (frameCap-d)+V R (p j) (q j) (frameCap-s))≤
        ∑ k,mixedBlock R (p k) (q k) (P k) (N k) := by
  classical
  have hz : d-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hd.2,hs.1]⟩
  have hPt : (∑ i,P i)≤frameCap := by linarith [hd.1]
  have hNt : (∑ i,N i)≤frameCap := by rw [hbalance]; linarith [hs.1]
  obtain ⟨i,j,hij⟩ := both_signs_concentrate R p q P N hR hQ hp hpq hqp hP hN hPt hNt
  have htotal : (∑ i,P i)∈Icc 0 (frameCap-d) :=
    ⟨Finset.sum_nonneg (fun i _ => hP i),hbudget⟩
  have hspan : 0≤frameCap-d := by linarith [hd.2]
  have hsub : Icc (0:ℝ) (frameCap-d)⊆Icc 0 (frameCap-(d-s)) :=
    Icc_subset_Icc le_rfl (by linarith [hs.1])
  refine ⟨i,j,?_⟩
  by_cases he : i=j
  · subst j
    simp only [] at hij ⊢
    rw [hbalance] at hij
    have hconc := (sameBlockLine_concave (R := R) (hp i).le
      ((hp i).trans_le (hpq i)).le hz).subset hsub (convex_Icc 0 (frameCap-d))
    have hmin := hconc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
    rw [add_zero,mixedBlock_zero_left,show d-s+(frameCap-d)=frameCap-s by ring] at hmin
    exact hmin.trans hij
  · simp only [ite_eq_right he] at hij ⊢
    rw [hbalance] at hij
    have hconc := (separatedLine_concave hR hQ
      (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) hz).subset hsub
        (convex_Icc 0 (frameCap-d))
    have hmin := hconc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
    simp only [U_zero,zero_add,add_zero,
      show d-s+(frameCap-d)=frameCap-s by ring] at hmin
    exact hmin.trans hij

end SquaresInCircles.Eight.RemovedPrimaryConcentration
