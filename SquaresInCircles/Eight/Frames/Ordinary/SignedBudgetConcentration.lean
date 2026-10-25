module

public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2Concentration

/-!
# Eight squares: the ordinary blocks under two signed budgets

The ordinary blocks have positive parts `P k` with `∑ P ≤ frameCap - θ` and negative parts `N k`
with `∑ N ≤ frameCap - s`, and `∑ N - ∑ P = θ - s`. The sum of the block functions
`mixedBlock R (p k) (q k) (P k) (N k)` is then at least, for some blocks `i` and `j`, the smaller of
two values (`concentrate`): `pure`, where the only mass is the surplus `|θ - s|` on one block, and
`saturated`, where both budgets are used up. The two simplex steps of `both_signs_concentrate`
keep the totals, and the concentrated sum is concave between these two ends
(`reverse_separated_concave` and the concavity of the other lines), so it is least at an end. The
sign of the surplus is not assumed.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.OrdinarySignedBudgetConcentration
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration

variable {ι : Type*} [DecidableEq ι]

def pure (R : ℝ) (p q : ι→ℝ) (i j : ι) (s θ : ℝ) : ℝ :=
  if s≤θ then V R (p j) (q j) (θ-s) else U R (p i) (q i) (s-θ)
def saturated (R : ℝ) (p q : ι→ℝ) (i j : ι) (s θ : ℝ) : ℝ :=
  if i=j then mixedBlock R (p i) (q i) (frameCap-θ) (frameCap-s)
  else U R (p i) (q i) (frameCap-θ)+V R (p j) (q j) (frameCap-s)

theorem reverse_separated_concave {R p q p' q' t : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hp' : 0<p') (hpq' : p'≤q') (hqp' : q'≤2*p')
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t)) (fun N => U R p q (t+N)+V R p' q' N) := by
  have hU := concave_affine_argument (U_concave hR hQ hp hpq hqp)
    (a:=1) (b:=t) (l:=0) (u:=frameCap-t)
    (fun N hN => ⟨by linarith [hN.1,ht.1],by linarith [hN.2]⟩)
  have hV := (V_concave hR hQ hp' hpq' hqp').subset
    (Icc_subset_Icc le_rfl (by linarith [ht.1])) (convex_Icc 0 (frameCap-t))
  refine (hU.add hV).congr fun N _ => ?_
  simp only [Pi.add_apply,one_mul,add_comm t]


theorem concentrate [Fintype ι] [Nonempty ι]
    (R : ℝ) (p q P N : ι→ℝ) {s θ : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : ∀i,0<p i) (hpq : ∀i,p i≤q i) (hqp : ∀i,q i≤2*p i)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hs : s∈Icc 0 frameCap) (hθ : θ∈Icc 0 frameCap)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃i j,min (pure R p q i j s θ) (saturated R p q i j s θ)≤
      ∑k,mixedBlock R (p k) (q k) (P k) (N k) := by
  have hPt : (∑i,P i)≤frameCap := by linarith [hθ.1]
  have hNt : (∑i,N i)≤frameCap := by linarith [hs.1]
  obtain ⟨i,j,hij⟩ := both_signs_concentrate R p q P N hR hQ hp hpq hqp hP hN hPt hNt
  refine ⟨i,j,?_⟩
  by_cases horder : s≤θ
  · have ht : θ-s∈Icc 0 frameCap := ⟨by linarith,by linarith [hθ.2,hs.1]⟩
    have htotal : (∑i,P i)∈Icc 0 (frameCap-θ) :=
      ⟨Finset.sum_nonneg (fun i _ => hP i),hPb⟩
    have hspan : 0≤frameCap-θ := by linarith [hθ.2]
    have heq : (∑i,N i)=(θ-s)+(∑i,P i) := by linarith
    have hlast : (θ-s)+(frameCap-θ)=frameCap-s := by ring
    by_cases hsame : i=j
    · subst j
      simp only [pure,horder,↓reduceIte,saturated] at ⊢
      simp only [↓reduceIte,heq] at hij
      have hc := (sameBlockLine_concave (R:=R) (hp i).le ((hp i).trans_le (hpq i)).le ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hs.1])) (convex_Icc 0 (frameCap-θ))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      rw [add_zero,mixedBlock_zero_left,hlast] at hh
      exact hh.trans hij
    · simp only [pure,horder,↓reduceIte,saturated,hsame] at ⊢
      simp only [hsame,↓reduceIte,heq] at hij
      have hc := (separatedLine_concave hR hQ
        (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hs.1])) (convex_Icc 0 (frameCap-θ))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [U_zero,zero_add,add_zero,hlast] at hh
      exact hh.trans hij
  · have ht : s-θ∈Icc 0 frameCap := ⟨by linarith,by linarith [hs.2,hθ.1]⟩
    have htotal : (∑i,N i)∈Icc 0 (frameCap-s) :=
      ⟨Finset.sum_nonneg (fun i _ => hN i),hNb⟩
    have hspan : 0≤frameCap-s := by linarith [hs.2]
    have heq : (∑i,P i)=(s-θ)+(∑i,N i) := by linarith
    have hlast : (s-θ)+(frameCap-s)=frameCap-θ := by ring
    by_cases hsame : i=j
    · subst j
      simp only [pure,horder,↓reduceIte,saturated] at ⊢
      simp only [↓reduceIte,heq] at hij
      have hc := (GlobalGA.NegativeAPositiveTD.Concentration.reverse_ordinary_line_concave
        (R:=R) (hp i).le ((hp i).trans_le (hpq i)).le ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hθ.1])) (convex_Icc 0 (frameCap-s))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      rw [add_zero,mixedBlock_zero_right,hlast] at hh
      exact hh.trans hij
    · simp only [pure,horder,↓reduceIte,saturated,hsame] at ⊢
      simp only [hsame,↓reduceIte,heq] at hij
      have hc := (reverse_separated_concave hR hQ
        (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hθ.1])) (convex_Icc 0 (frameCap-s))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [V_zero,add_zero,hlast] at hh
      exact hh.trans hij

end SquaresInCircles.Eight.OrdinarySignedBudgetConcentration
