module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3Angular

/-!
# Concentrating the two remaining signed totals

Uncompiled Section 5. The budgets are h-z and h-s, with their signed
difference z-s retained. The high family uses four ordinary blocks;
the low family keeps exactly the sorted-D hybrid minorant.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.Concentration
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open Certificate (Family)

def positive (f : Family) (p q : Fin 4→ℝ) (i : Fin 4) (t : ℝ) : ℝ :=
  if f=.low then PositiveTD.Hybrid.positive R (67/100) p q 3 i t else U R (p i) (q i) t
def block (f : Family) (p q : Fin 4→ℝ) (i : Fin 4) (P N : ℝ) : ℝ :=
  if f=.low then PositiveTD.Hybrid.block R (67/100) p q 3 i P N else mixedBlock R (p i) (q i) P N
def pure (f : Family) (p q : Fin 4→ℝ) (i j : Fin 4) (s z : ℝ) : ℝ :=
  if s≤z then V R (p j) (q j) (z-s) else positive f p q i (s-z)
def saturated (f : Family) (p q : Fin 4→ℝ) (i j : Fin 4) (s z : ℝ) : ℝ :=
  if i=j then block f p q i (frameCap-z) (frameCap-s)
  else positive f p q i (frameCap-z)+V R (p j) (q j) (frameCap-s)

@[simp] theorem positive_zero (f : Family) (p q : Fin 4→ℝ) (i : Fin 4) : positive f p q i 0=0 := by
  cases f <;> simp [positive,PositiveTD.Hybrid.positive]
@[simp] theorem block_zero_left (f : Family) (p q : Fin 4→ℝ) (i : Fin 4) (t : ℝ) :
    block f p q i 0 t=V R (p i) (q i) t := by
  cases f <;> simp [block,PositiveTD.Hybrid.block]
@[simp] theorem block_zero_right (f : Family) (p q : Fin 4→ℝ) (i : Fin 4) (t : ℝ) :
    block f p q i t 0=positive f p q i t := by
  cases f <;> simp [block,positive,PositiveTD.Hybrid.block,PositiveTD.Hybrid.positive]

theorem reverse_separated_concave {p q p' q' t : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hp' : 0<p') (hpq' : p'≤q') (hqp' : q'≤2*p')
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t)) (fun N => U R p q (t+N)+V R p' q' N) := by
  have hU := concave_affine_argument (U_concave (Real.sqrt_nonneg _) radius_sq.le hp hpq hqp)
    (a:=1) (b:=t) (l:=0) (u:=frameCap-t)
    (fun N hN => ⟨by linarith [hN.1,ht.1],by linarith [hN.2]⟩)
  have hV := (V_concave (Real.sqrt_nonneg _) radius_sq.le hp' hpq' hqp').subset
    (Icc_subset_Icc le_rfl (by linarith [ht.1])) (convex_Icc 0 (frameCap-t))
  simpa only [one_mul,add_comm t] using hU.add hV

theorem concentrate (f : Family) (p q P N : Fin 4→ℝ) {s z : ℝ}
    (hp : ∀i,0<p i) (hpq : ∀i,p i≤q i) (hqp : ∀i,q i≤2*p i)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hPbudget : (∑i,P i)≤frameCap-z) (hNbudget : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=z-s) :
    ∃i j,min (pure f p q i j s z) (saturated f p q i j s z)≤∑k,block f p q k (P k) (N k) := by
  cases f
  · have hh := NegativeAPositiveTD.Concentration.concentrate R (67/100) p q P N 3
      (Real.sqrt_nonneg _) radius_sq.le hp hpq hqp hP hN hs hz hPbudget hNbudget hbalance
    simpa only [pure,saturated,positive,block,↓reduceIte,
      NegativeAPositiveTD.Concentration.pure,NegativeAPositiveTD.Concentration.saturated] using hh
  · have hPt : (∑i,P i)≤frameCap := by linarith [hz.1]
    have hNt : (∑i,N i)≤frameCap := by linarith [hs.1]
    obtain ⟨i,j,hij⟩ := OrdinaryAngleConcentration.both_signs_concentrate R p q P N
      (Real.sqrt_nonneg _) radius_sq.le hp hpq hqp hP hN hPt hNt
    refine ⟨i,j,?_⟩
    simp only [pure,saturated,positive,block,↓reduceIte]
    by_cases hsz : s≤z
    · have ht : z-s∈Icc 0 frameCap := ⟨by linarith,by linarith [hz.2,hs.1]⟩
      have htotal : (∑i,P i)∈Icc 0 (frameCap-z) :=
        ⟨Finset.sum_nonneg (fun i _ => hP i),hPbudget⟩
      have hspan : 0≤frameCap-z := by linarith [hz.2]
      have heq : (∑i,N i)=(z-s)+(∑i,P i) := by linarith
      have he : (z-s)+(frameCap-z)=frameCap-s := by ring
      simp only [if_pos hsz]
      by_cases heij : i=j
      · subst j
        simp only [if_pos rfl,heq] at hij ⊢
        have hc := (sameBlockLine_concave (R:=R) (hp i).le ((hp i).trans_le (hpq i)).le ht).subset
          (Icc_subset_Icc le_rfl (by linarith [hs.1])) (convex_Icc 0 (frameCap-z))
        have hm := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
        rw [add_zero,mixedBlock_zero_left,he] at hm
        exact hm.trans hij
      · simp only [if_neg heij,heq] at hij ⊢
        have hc := (separatedLine_concave (Real.sqrt_nonneg _) radius_sq.le
          (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) ht).subset
          (Icc_subset_Icc le_rfl (by linarith [hs.1])) (convex_Icc 0 (frameCap-z))
        have hm := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
        simp only [U_zero,zero_add,add_zero,he] at hm
        exact hm.trans hij
    · have ht : s-z∈Icc 0 frameCap := ⟨by linarith,by linarith [hs.2,hz.1]⟩
      have htotal : (∑i,N i)∈Icc 0 (frameCap-s) :=
        ⟨Finset.sum_nonneg (fun i _ => hN i),hNbudget⟩
      have hspan : 0≤frameCap-s := by linarith [hs.2]
      have heq : (∑i,P i)=(s-z)+(∑i,N i) := by linarith
      have he : (s-z)+(frameCap-s)=frameCap-z := by ring
      simp only [if_neg hsz]
      by_cases heij : i=j
      · subst j
        simp only [if_pos rfl,heq] at hij ⊢
        have hc := (NegativeAPositiveTD.Concentration.reverse_ordinary_line_concave
          (R:=R) (hp i).le ((hp i).trans_le (hpq i)).le ht).subset
          (Icc_subset_Icc le_rfl (by linarith [hz.1])) (convex_Icc 0 (frameCap-s))
        have hm := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
        rw [add_zero,mixedBlock_zero_right,he] at hm
        exact hm.trans hij
      · simp only [if_neg heij,heq] at hij ⊢
        have hc := (reverse_separated_concave
          (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) ht).subset
          (Icc_subset_Icc le_rfl (by linarith [hz.1])) (convex_Icc 0 (frameCap-s))
        have hm := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
        simp only [V_zero,add_zero,he] at hm
        exact hm.trans hij

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.Concentration
