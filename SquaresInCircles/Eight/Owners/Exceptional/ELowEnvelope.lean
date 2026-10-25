module

public import SquaresInCircles.Eight.Owners.Exceptional.ContactBlocks
public import SquaresInCircles.Eight.Owners.Exceptional.ELowCharges
public import SquaresInCircles.Eight.Owners.Exceptional.SmallGap

/-!
# Eight squares: complete low-family ordinary envelope for original E contact

All original positive/negative ordinary allocations
are covered by continuous concentration. The H block retains its EH0
angle, D may be relaxed to a two-angle block, and A retains its actual
one-angle coefficient. The fixed-ratio gap pays the whole positive
budget with a strict reserve, leaving the actual B pure charge.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalELowEnvelope
open Candidate ExceptionalECoefficients ExceptionalContactStress ExceptionalContactBlocks
open ExceptionalELowCharges PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryAngleConcentration SingleAngleConcavity

theorem AB_data {t x e : ℝ} (ht : t∈domain .low) :
    small (k .low t) (ell .low t) (c .low t) (eta .low t) x e 1=ell .low t ∧
    large (k .low t) (ell .low t) (c .low t) (eta .low t) x e 1=k .low t ∧
    small (k .low t) (ell .low t) (c .low t) (eta .low t) x e 2=ell .low t ∧
    large (k .low t) (ell .low t) (c .low t) (eta .low t) x e 2=c .low t := by
  have ho := low_order ht
  simp [small,large,ExceptionalContactBlocks.alpha,ExceptionalContactBlocks.beta,min_eq_left ho.2.1,max_eq_right ho.2.1,
    min_eq_left ho.2.2.1,max_eq_right ho.2.2.1]

theorem wide_data {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) {i : Fin 4} (hi : i=0 ∨ i=3) :
    SoleLowChargeBounds.base≤ small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i ∧
    large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i∈Icc 1 (21/20:ℝ) := by
  rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
  obtain ⟨hx0,hx1⟩ := low_tilt ht hx
  obtain ⟨he0',he1'⟩ := low_tilt ht he
  have hkpos := (low_order ht).1
  have hn0 := mul_le_mul_of_nonneg_left hx0 hkpos.le
  have hn1 := mul_lt_mul_of_pos_left hx1 hkpos
  have hn : k .low t*tilt (eta .low t) x≤21/20 := by nlinarith
  rcases hi with rfl | rfl
  · change SoleLowChargeBounds.base≤ min (tilt (eta .low t) e) (k .low t*tilt (eta .low t) x) ∧
      max (tilt (eta .low t) e) (k .low t*tilt (eta .low t) x)∈Icc 1 (21/20:ℝ)
    exact ⟨le_min (by dsimp [SoleLowChargeBounds.base]; linarith)
      (by dsimp [SoleLowChargeBounds.base]; nlinarith),
      he0'.trans (le_max_left _ _),max_le he1'.le hn⟩
  · change SoleLowChargeBounds.base≤ min 1 (c .low t) ∧ max 1 (c .low t)∈Icc 1 (21/20:ℝ)
    exact ⟨le_min (by norm_num [SoleLowChargeBounds.base])
      (by dsimp [SoleLowChargeBounds.base]; linarith),
      le_max_left _ _,max_le (by norm_num) (by linarith)⟩

theorem coefficient_conditions {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    0<small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i ∧
    large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i≤
      2*small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i ∧
    large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i≤21/20 := by
  rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
  have ho := low_order ht
  have hp := small_pos (l := ell .low t) ho.1 (by linarith) (ho.1.trans_le hkc) (tilt_pos ht hx) (tilt_pos ht he) i
  refine ⟨hp,?_⟩
  fin_cases i <;> dsimp only [Fin.reduceFinMk]
  · have hh := wide_data ht hx he (Or.inl rfl)
    dsimp [SoleLowChargeBounds.base] at hh
    constructor <;> linarith [hh.1,hh.2.2]
  · obtain ⟨ha,hA,_,_⟩ := AB_data (x := x) (e := e) ht
    rw [ha,hA]
    constructor <;> linarith
  · obtain ⟨_,_,hb,hB⟩ := AB_data (x := x) (e := e) ht
    rw [hb,hB]
    exact ⟨ho.2.2.2.2,by linarith⟩
  · have hh := wide_data ht hx he (Or.inr rfl)
    dsimp [SoleLowChargeBounds.base] at hh
    constructor <;> linarith [hh.1,hh.2.2]

theorem pure_dominates {R t x e : ℝ} (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    V R (ell .low t) (c .low t) t≤
      pure (single i) R (small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i)
        (large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i)
        (nu (k .low t) (ell .low t) (c .low t) (eta .low t) x e i) t ∧
    V R (ell .low t) (c .low t) frameCap≤
      pure (single i) R (small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i)
        (large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i)
        (nu (k .low t) (ell .low t) (c .low t) (eta .low t) x e i) frameCap := by
  have hR2 : R≤2 := by norm_num [qCap] at hQU; nlinarith
  fin_cases i <;> dsimp only [Fin.reduceFinMk]
  · have hw := wide_data ht hx he (Or.inl rfl)
    have hh := wide_dominates hR hQL hQU hw.1 (small_le_large _ _ _ _ _ _ 0) hw.2 hw.2.2 ht
    exact hh
  · obtain ⟨ha,hA,_,_⟩ := AB_data (x := x) (e := e) ht
    rw [ha,hA]
    exact ⟨A_ge_B ⟨hR,hR2⟩ ht,A_ge_B_at_cap ⟨hR,hR2⟩ ht⟩
  · obtain ⟨_,_,hb,hB⟩ := AB_data (x := x) (e := e) ht
    rw [hb,hB]
    exact ⟨le_rfl,le_rfl⟩
  · have hw := wide_data ht hx he (Or.inr rfl)
    have hh := wide_dominates hR hQL hQU hw.1 (small_le_large _ _ _ _ _ _ 3) hw.2 hw.2.2 ht
    exact hh

theorem same_block_dominates {R t x e : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (i : Fin 4) (hi : single i=false) :
    V R (ell .low t) (c .low t) t≤
      M R (small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i)
        (large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i) t := by
  by_cases hB : i=2
  · subst i
    obtain ⟨_,_,hb,hB⟩ := AB_data (x := x) (e := e) ht
    rw [hb,hB]
    have hc : 0≤c .low t := (low_order ht).1.le.trans (low_bounds ht).2.2.1
    have hratio : PositiveStressCoefficients.ratio t*c .low t≤ell .low t := by
      have hh := (low_correlations ht).1
      dsimp [PositiveStressCoefficients.ratio]
      nlinarith [mul_nonneg ht.1 hc]
    have hh := CorrelatedSameBlock.negative_surplus (R := R) hc hratio (angle ht)
      (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,ht.1⟩)
    have hid : mixedBlock R (ell .low t) (c .low t) (frameCap-t) frameCap=
        M R (ell .low t) (c .low t) t := by
      simpa only [show t+(frameCap-t)=frameCap by ring] using mixedBlock_saturated R (ell .low t) (c .low t) t
    simpa only [sub_zero,hid] using hh
  · have hiw : i=0 ∨ i=3 := by fin_cases i <;> simp_all [single]
    have hw := wide_data ht hx he hiw
    have hp := (coefficient_conditions ht hx he i).1
    have hpq := small_le_large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i
    have hratio : large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i≤
        (3/2)*small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i := by
      dsimp [SoleLowChargeBounds.base] at hw
      linarith [hw.1,hw.2.2]
    have hM := M_ge_V (R := R) hp.le (hp.trans_le hpq).le hratio (angle ht)
    have hV := (pure_dominates hR hQL hQU ht hx he i).1
    simp only [SingleAngleConcavity.pure,hi,Bool.false_eq_true,↓reduceIte] at hV
    exact hV.trans hM

theorem separated_dominates {R t x e : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i j : Fin 4) :
    V R (ell .low t) (c .low t) t<
      U R (small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i)
        (large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i) (frameCap-t)+
      pure (single j) R (small (k .low t) (ell .low t) (c .low t) (eta .low t) x e j)
        (large (k .low t) (ell .low t) (c .low t) (eta .low t) x e j)
        (nu (k .low t) (ell .low t) (c .low t) (eta .low t) x e j) frameCap := by
  have hi := coefficient_conditions ht hx he i
  have hlen : 0≤frameCap-t := by dsimp [frameCap]; linarith [ht.2]
  have hU := OrdinaryPositiveEnvelope.U_lower hR hQU hi.1 (small_le_large _ _ _ _ _ _ i) hi.2.1
    (show frameCap-t∈Icc 0 frameCap from ⟨hlen,by linarith [ht.1]⟩)
  have hUscale := mul_le_mul_of_nonneg_right hi.2.2 hlen
  have hcap := (pure_dominates hR hQL hQU ht hx he j).2
  have ho := low_order ht
  have hc : ExceptionalSmallGap.scale≤c .low t := by
    dsimp [ExceptionalSmallGap.scale]
    exact (low_bounds ht).1.trans (low_bounds ht).2.2.1
  have hgap := ExceptionalSmallGap.scaled_gap hR hQL hQU hc ho.2.2.1 ho.2.2.2.1 ht
  dsimp only [ExceptionalSmallGap.scale] at hgap
  generalize frameCap=F at hU hUscale hcap hgap hlen ⊢
  linarith [hU,hUscale,hcap,hgap,hlen]

theorem ordinary_lower {R t x e : ℝ} (P N : Fin 4 → ℝ)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑i,P i)≤frameCap-t) (hbalance : (∑i,N i)=t+∑i,P i)
    (hsingle : ∀ i,single i=true → P i=0 ∨ N i=0) :
    V R (ell .low t) (c .low t) t≤
      ∑i,F (single i) R (small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i)
        (large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i)
        (nu (k .low t) (ell .low t) (c .low t) (eta .low t) x e i) (P i) (N i) := by
  apply SingleAngleConcentration.lower_from_endpoints single R
    (small (k .low t) (ell .low t) (c .low t) (eta .low t) x e)
    (large (k .low t) (ell .low t) (c .low t) (eta .low t) x e)
    (nu (k .low t) (ell .low t) (c .low t) (eta .low t) x e) P N hR hQU
    (fun i => (coefficient_conditions ht hx he i).1) (small_le_large _ _ _ _ _ _)
    (fun i => (coefficient_conditions ht hx he i).2.1) (fun i => (nu_between _ _ _ _ _ _ i).1)
    hP hN (angle ht) hbudget hbalance hsingle
  · intro i; exact (pure_dominates hR hQL hQU ht hx he i).1
  · intro i hi; exact same_block_dominates hR hQL hQU ht hx he i hi
  · intro i j _; exact (separated_dominates hR hQL hQU ht hx he i j).le

theorem original_increment {C : SignedCycle} {ab : Fin 4} {R t x e : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D=t) :
    V R (ell .low t) (c .low t) t≤ExceptionalContactSupport.increment C ab R
      (k .low t) (ell .low t) (c .low t) (eta .low t) x e := by
  obtain ⟨ht0,hP,hN⟩ := original_budgets hab (k .low t) (ell .low t) (c .low t) (eta .low t) t x e
    hvar hG hD htotal
  have hlow := ordinary_lower
    (fun i => (blocks C ab (k .low t) (ell .low t) (c .low t) (eta .low t) x e i).P)
    (fun i => (blocks C ab (k .low t) (ell .low t) (c .low t) (eta .low t) x e i).N)
    hR hQL hQU ht hx he
    (fun i => (blocks C ab (k .low t) (ell .low t) (c .low t) (eta .low t) x e i).P_nonneg)
    (fun i => (blocks C ab (k .low t) (ell .low t) (c .low t) (eta .low t) x e i).N_nonneg)
    hP hN (single_parts C ab _ _ _ _ _ _)
  exact hlow.trans (sum_minorant hab ht0 (fun i => (coefficient_conditions ht hx he i).1.le) ha hP hN)

end SquaresInCircles.Eight.ExceptionalELowEnvelope
