module

public import SquaresInCircles.Eight.TableFree.SoleOrdinaryData

/-!
# Every low-family ordinary allocation lies above the B charge

Uncompiled source. The coefficient data come from the actual original
split x,e. All signed ordinary allocations satisfying the exact balanced
variation equations are covered by continuous concentration. The gap at
the frame cap pays the universal positive-angle cost, with strict reserve.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SoleLowEnvelope
open SoleECoefficients SoleOrdinaryData SoleLowChargeBounds
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open SingleAngleConcavity

theorem pure_dominates {de : Bool} {R t x e : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    V R (ell .low t) (c .low t) t≤
      pure (single de i) R (small .low de t x e i) (large .low de t x e i)
        (nu .low de t x e i) t ∧
    V R (ell .low t) (c .low t) frameCap≤
      pure (single de i) R (small .low de t x e i) (large .low de t x e i)
        (nu .low de t x e i) frameCap := by
  have hR2 : R≤2 := by norm_num [qCap] at hQU; nlinarith
  fin_cases i
  · have hw := low_wide (de := de) ht hx he (Or.inl rfl)
    have hh := wide_dominates hR hQL hQU hw.1 (small_le_large .low de t x e 0)
      hw.2 ((nu_between ht 0).2.trans hw.2.2) ht
    cases de <;> simpa [single,SingleAngleConcavity.pure,nu,V,Vnu] using hh
  · rcases A_data (de := de) (x := x) (e := e) ht with ⟨hs,hl,hn⟩
    simp only [Fin.mk_one,Fin.isValue,hs,hl,hn,single,Matrix.cons_val_one,
      SingleAngleConcavity.pure]
    exact ⟨by simpa [V,Vnu] using SoleLowAComparison.A_ge_B ⟨hR,hR2⟩ ht,
      by simpa [V,Vnu] using SoleLowAComparison.A_ge_B_at_cap ⟨hR,hR2⟩ ht⟩
  · rcases B_data (de := de) (x := x) (e := e) ht with ⟨hs,hl,hn⟩
    simp [hs,hl,single,SingleAngleConcavity.pure]
  · have hw := low_wide (de := de) ht hx he (Or.inr rfl)
    have hh := wide_dominates hR hQL hQU hw.1 (small_le_large .low de t x e 3)
      hw.2 ((nu_between ht 3).2.trans hw.2.2) ht
    simpa [single,SingleAngleConcavity.pure,nu,V,Vnu] using hh

theorem same_block_dominates {de : Bool} {R t x e : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (i : Fin 4) (hi : single de i=false) :
    V R (ell .low t) (c .low t) t≤
      M R (small .low de t x e i) (large .low de t x e i) t := by
  by_cases hB : i=2
  · subst i
    rcases B_data (de := de) (x := x) (e := e) ht with ⟨hs,hl,hn⟩
    rw [hs,hl]
    exact SoleLowAComparison.B_same_block ht
  have hwide : i=0 ∨ i=3 := by
    fin_cases i <;> simp_all [single]
  have hw := low_wide (de := de) ht hx he hwide
  have hp := small_pos (de := de) ht hx he i
  have hpq := small_le_large .low de t x e i
  have hratio : (2/3)*large .low de t x e i≤ small .low de t x e i := by
    dsimp [base] at hw
    linarith [hw.1,hw.2.2]
  have hM := M_ge_V (R := R) hp.le (hp.trans_le hpq).le (by linarith) (angle ht)
  have hV := (pure_dominates (de := de) hR hQL hQU ht hx he i).1
  simp only [SingleAngleConcavity.pure,hi,Bool.false_eq_true,↓reduceIte] at hV
  exact hV.trans hM

theorem positive_lower {de : Bool} {R t x e : ℝ}
    (hR : 0≤R) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    -(763/2000 : ℝ)≤
      U R (small .low de t x e i) (large .low de t x e i) (frameCap-t) := by
  have hlen : 0≤frameCap-t := by linarith [(angle ht).2]
  have hU := OrdinaryPositiveEnvelope.U_lower hR hQU (small_pos ht hx he i)
    (small_le_large .low de t x e i) (low_half_ratio ht hx he i)
    (show frameCap-t∈Icc 0 frameCap from ⟨hlen,by linarith [ht.1]⟩)
  have hprod : large .low de t x e i*(frameCap-t)≤7/10 := by
    calc
      _≤(1+(7/10)*t)*(frameCap-t) :=
        mul_le_mul_of_nonneg_right (low_large_upper ht hx he i) hlen
      _≤7/10 := by dsimp [frameCap]; nlinarith [ht.1,sq_nonneg t]
  nlinarith

theorem separated_dominates {de : Bool} {R t x e : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i j : Fin 4) :
    V R (ell .low t) (c .low t) t<
      U R (small .low de t x e i) (large .low de t x e i) (frameCap-t)+
      pure (single de j) R (small .low de t x e j) (large .low de t x e j)
        (nu .low de t x e j) frameCap := by
  have hU := positive_lower (de := de) hR hQU ht hx he i
  have hcap := (pure_dominates (de := de) hR hQL hQU ht hx he j).2
  have hgap := SoleLowGap.B_gap hR hQL ht
  linarith

/-- A closed analytic lower envelope with the original split coefficients.
The remaining arguments are the actual variation and one-angle data,
which are constructed from the original signed blocks in the next layer. -/
theorem ordinary_lower {de : Bool} {R t x e : ℝ} (P N : Fin 4 → ℝ)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑i,P i)≤frameCap-t) (hbalance : (∑i,N i)=t+∑i,P i)
    (hsingle : ∀ i,single de i=true → P i=0 ∨ N i=0) :
    V R (ell .low t) (c .low t) t≤
      ∑i,F (single de i) R (small .low de t x e i) (large .low de t x e i)
        (nu .low de t x e i) (P i) (N i) := by
  apply SingleAngleConcentration.lower_from_endpoints (single de) R
    (small .low de t x e) (large .low de t x e) (nu .low de t x e) P N
    hR hQU (small_pos ht hx he) (small_le_large .low de t x e)
    (low_half_ratio ht hx he) (fun i => (nu_between ht i).1)
    hP hN (angle ht) hbudget hbalance hsingle
  · intro i
    exact (pure_dominates hR hQL hQU ht hx he i).1
  · intro i hi
    exact same_block_dominates hR hQL hQU ht hx he i hi
  · intro i j _
    exact (separated_dominates hR hQL hQU ht hx he i j).le

end SquaresInCircles.Eight.TableFree.SoleLowEnvelope
