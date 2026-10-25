module

public import SquaresInCircles.Eight.Owners.Sole.NegativeTGrowth
public import SquaresInCircles.Eight.Owners.OccupiedSignedConcentration

/-!
# Eight squares: the ordinary minorants after a negative T primary

H and A keep their pair charges. A BT3 row changes only the positive B pair, and its negative
charge is bounded by the unchanged B charge. In the EH rows the D block has the clipped support as
positive branch and the smaller of the unchanged D and A charges as negative one. In a sole-DE row
D has no ordinary angle; its zero block uses the functions of A only to keep one finite index
type. These blocks form concave block data (`data`) with their minorants (`positive_lower`,
`negative_lower`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleNegativeTOrdinaryData
open SoleTScalarModel SoleNegativeTCoefficients PositiveAngularEnvelope
open OrdinaryAngleConcavity OrdinaryAngleConcentration SingleAngleConcavity
open ActualOrdinaryBlocks SoleNegativeTGrowth

def shortDomain (td : Bool) : Set ℝ := if td then Icc 0 (3/10) else Icc 0 (9/100)
def dCoefficient (f : Family) (td : Bool) (t s : ℝ) : ℝ :=
  SoleNegativeTSplit.tdWeight f td t s
def Used (f : Family) (i : Fin 4) : Prop := isDE f=false ∨ i≠3

def positive (f : Family) (atG td : Bool) (R t s v : ℝ) (i : Fin 4) : ℝ :=
  if i=3 then
    if isDE f then U R (small f atG t 1) (large f atG t 1) v
    else if p (face f atG) t 0≤dCoefficient f td t s then
      -(2/5)*p (face f atG) t 0*v
    else U R (dCoefficient f td t s) (p (face f atG) t 0) v
  else if i=2 ∧ td=false then U R (ell f t 0) (c f t 0/Real.cos s) v
  else U R (small f atG t i) (large f atG t i) v

def negative (f : Family) (atG : Bool) (R t v : ℝ) (i : Fin 4) : ℝ :=
  if i=3 then
    if isDE f then oldV f atG R t v 1
    else min (oldV f atG R t v 3) (oldV f atG R t v 1)
  else oldV f atG R t v i

def block (f : Family) (atG td : Bool) (R t s P N : ℝ) (i : Fin 4) : ℝ :=
  if single f td i then positive f atG td R t s P i+negative f atG R t N i
  else mixedBlock R (small f atG t i) (large f atG t i) P N

theorem short_small {td : Bool} {s : ℝ} (hs : s∈shortDomain td) : s∈Icc 0 frameCap := by
  cases td <;> norm_num [shortDomain,frameCap] at hs ⊢ <;> exact ⟨hs.1,by linarith [hs.2]⟩

theorem d_coefficient_ge {f : Family} (td : Bool) {t s : ℝ}
    (ht : t∈domain f) (hs : s∈shortDomain td) : c f t 0≤dCoefficient f td t s := by
  have hc := (coefficient_positive ht (zero_mem ht)).2.2.1
  have hsec := SoleNegativeTSplit.secant_nonneg (short_small hs)
  cases td
  · exact le_rfl
  · have hh := mul_nonneg hc.le hsec.2
    have he : c f t 0/Real.cos s=c f t 0*(1/Real.cos s) := by ring
    dsimp [dCoefficient,SoleNegativeTSplit.tdWeight]
    rw [he]
    linarith

theorem mixed_indices {f : Family} {td : Bool} {i : Fin 4} (hi : single f td i=false) :
    (i=0 ∧ isDE f=true) ∨ (i=2 ∧ td=true) := by
  fin_cases i <;> cases hf : isDE f <;> cases ht : td <;>
    simp_all [single]

theorem mixed_nu {f : Family} (atG : Bool) {td : Bool} {t : ℝ}
    (ht : t∈domain f) (i : Fin 4) (hi : single f td i=false) :
    nu f atG t i=large f atG t i := by
  have hpr := pairs f atG t
  rcases mixed_indices hi with ⟨rfl,hf⟩ | ⟨rfl,htd⟩
  · have hh := old_cap atG ht 0
    have hlam : lambda f=5/4 := by simp [lambda,hf]
    have hcap : (SolePositiveTCoefficients.cap f:ℝ)=5/4 := by
      cases f <;> simp_all [isDE,SolePositiveTCoefficients.cap]
    have hlarge : large f atG t 0=max (lambda f) (n (face f atG) t 0) := by
      simp only [large,hpr.1,hpr.2]
      rfl
    have hnu : SoleNegativeTCoefficients.nu f atG t 0=lambda f := by
      simp [SoleNegativeTCoefficients.nu,hf]
    rw [hlarge] at hh ⊢
    rw [hnu]
    rw [hcap,← hlam] at hh
    exact (le_antisymm hh (le_max_left _ _)).symm
  · have he := c_ge_ell atG ht
    have hlarge : large f atG t 2=max (ell f t 0) (c f t 0) := by
      simp only [large,hpr.1,hpr.2]
      rfl
    rw [hlarge,max_eq_right he]
    rfl

theorem positive_mixed {f : Family} (atG : Bool) {td : Bool} (R t s v : ℝ)
    (i : Fin 4) (hi : single f td i=false) :
    positive f atG td R t s v i=U R (small f atG t i) (large f atG t i) v := by
  rcases mixed_indices hi with ⟨rfl,hf⟩ | ⟨rfl,rfl⟩ <;> simp [positive]

theorem negative_mixed {f : Family} (atG : Bool) {td : Bool} (R : ℝ) {t : ℝ}
    (ht : t∈domain f) (v : ℝ) (i : Fin 4) (hi : single f td i=false) :
    negative f atG R t v i=V R (small f atG t i) (large f atG t i) v := by
  have hne : i≠3 := by rcases mixed_indices hi with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide
  rw [negative,ite_eq_right hne,oldV,mixed_nu atG ht i hi,Vnu_larger]

@[simp] theorem positive_zero (f : Family) (atG td : Bool) (R t s : ℝ) (i : Fin 4) :
    positive f atG td R t s 0 i=0 := by
  unfold positive
  split_ifs <;> simp

@[simp] theorem negative_zero (f : Family) (atG : Bool) (R t : ℝ) (i : Fin 4) :
    negative f atG R t 0 i=0 := by
  unfold negative
  split_ifs <;> simp [SoleNegativeTGrowth.zero]

theorem block_left {f : Family} (atG td : Bool) (R : ℝ) {t : ℝ}
    (ht : t∈domain f) (s N : ℝ) (i : Fin 4) :
    block f atG td R t s 0 N i=negative f atG R t N i := by
  cases hi : single f td i
  · simp only [block,hi,Bool.false_eq_true,↓reduceIte]
    rw [mixedBlock_zero_left,negative_mixed atG R ht N i hi]
  · simp [block,hi]

theorem block_right {f : Family} (atG td : Bool) (R t s P : ℝ) (i : Fin 4) :
    block f atG td R t s P 0 i=positive f atG td R t s P i := by
  cases hi : single f td i
  · simp only [block,hi,Bool.false_eq_true,↓reduceIte]
    rw [mixedBlock_zero_right,positive_mixed atG R t s P i hi]
  · simp [block,hi]

theorem affine_concave (a : ℝ) : ConcaveOn ℝ (Icc 0 frameCap) (fun x : ℝ => a*x) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy u v hu hv huv
  simp only [smul_eq_mul]
  ring_nf
  rfl

private lemma r63_concave_add_const {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ (Icc 0 frameCap) g) (C : ℝ) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun x => g x+C) := by
  refine ⟨hg.1,?_⟩
  intro x hx y hy a b ha hb hab
  have h := hg.2 hx hy ha hb hab
  have h2 : a*C+b*C=C := by rw [← add_mul,hab,one_mul]
  simp only [smul_eq_mul] at h ⊢
  linarith

private lemma r63_concave_const_add {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ (Icc 0 frameCap) g) (C : ℝ) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun x => C+g x) := by
  refine ⟨hg.1,?_⟩
  intro x hx y hy a b ha hb hab
  have h := hg.2 hx hy ha hb hab
  have h2 : a*C+b*C=C := by rw [← add_mul,hab,one_mul]
  simp only [smul_eq_mul] at h ⊢
  linarith

theorem minimum_concave {f g : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Icc 0 frameCap) f) (hg : ConcaveOn ℝ (Icc 0 frameCap) g) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun x => min (f x) (g x)) := by
  refine ⟨hf.1,?_⟩
  intro x hx y hy u v hu hv huv
  have hfx := mul_le_mul_of_nonneg_left (min_le_left (f x) (g x)) hu
  have hfy := mul_le_mul_of_nonneg_left (min_le_left (f y) (g y)) hv
  have hgx := mul_le_mul_of_nonneg_left (min_le_right (f x) (g x)) hu
  have hgy := mul_le_mul_of_nonneg_left (min_le_right (f y) (g y)) hv
  have hf' := hf.2 hx hy hu hv huv
  have hg' := hg.2 hx hy hu hv huv
  simp only [smul_eq_mul] at hf' hg' ⊢
  exact le_min (by linarith) (by linarith)

theorem positive_concave {f : Family} (atG td : Bool) {R t s : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain f) (hs : s∈shortDomain td) (i : Fin 4) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun v => positive f atG td R t s v i) := by
  have hbase (j : Fin 4) : ConcaveOn ℝ (Icc 0 frameCap)
      (U R (small f atG t j) (large f atG t j)) :=
    U_concave hR hQ (SoleNegativeTCoefficients.positive atG ht j).2.2 min_le_max
      (SoleNegativeTCoefficients.half_ratio atG ht j)
  by_cases hD : i=3
  · subst i
    by_cases hde : isDE f=true
    · simpa [positive,hde] using hbase 1
    · have hde' := Bool.eq_false_of_not_eq_true hde
      by_cases hdiag : p (face f atG) t 0≤dCoefficient f td t s
      · simpa [positive,hde',hdiag,mul_assoc] using
          affine_concave (-(2/5)*p (face f atG) t 0)
      · have hc := (coefficient_positive ht (zero_mem ht)).2.2.1
        have hcg := d_coefficient_ge td ht hs
        have hp2 := p_half_c atG ht
        have hg : 0<dCoefficient f td t s := hc.trans_le hcg
        simpa [positive,hde',hdiag] using
          U_concave hR hQ hg (lt_of_not_ge hdiag).le (by linarith : p (face f atG) t 0≤2*dCoefficient f td t s)
  · by_cases hB : i=2 ∧ td=false
    · have hsBT : s∈Icc 0 (9/100:ℝ) := by simpa [shortDomain,hB.2] using hs
      have hb := changed_B_domain atG ht hsBT
      simpa [positive,hD,hB] using U_concave hR hQ hb.1 hb.2.1 hb.2.2
    · simpa [positive,hD,hB] using hbase i

theorem negative_concave {f : Family} (atG : Bool) {R t : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain f) (i : Fin 4) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun v => negative f atG R t v i) := by
  by_cases hD : i=3
  · by_cases hde : isDE f=true
    · simpa [negative,hD,hde] using old_concave atG hR hQ ht 1
    · have hde' := Bool.eq_false_of_not_eq_true hde
      simpa [negative,hD,hde'] using minimum_concave
        (old_concave atG hR hQ ht 3) (old_concave atG hR hQ ht 1)
  · simpa [negative,hD] using old_concave atG hR hQ ht i

theorem block_concave_P {f : Family} (atG td : Bool) {R t s N : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain f) (hs : s∈shortDomain td)
    (hN : N∈Icc 0 frameCap) (i : Fin 4) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun P => block f atG td R t s P N i) := by
  cases hi : single f td i
  · simp only [block,hi,Bool.false_eq_true,↓reduceIte]
    exact mixedBlock_concave_positive hR hQ
      (SoleNegativeTCoefficients.positive atG ht i).2.2 min_le_max
      (SoleNegativeTCoefficients.half_ratio atG ht i) hN
  · simp only [block,hi,↓reduceIte]
    exact r63_concave_add_const (positive_concave atG td hR hQ ht hs i)
      (negative f atG R t N i)

theorem block_concave_N {f : Family} (atG td : Bool) {R t s P : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain f) (_hs : s∈shortDomain td)
    (hP : P∈Icc 0 frameCap) (i : Fin 4) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun N => block f atG td R t s P N i) := by
  cases hi : single f td i
  · simp only [block,hi,Bool.false_eq_true,↓reduceIte]
    exact mixedBlock_concave_negative hR hQ
      (SoleNegativeTCoefficients.positive atG ht i).2.2 min_le_max
      (SoleNegativeTCoefficients.half_ratio atG ht i) hP
  · simp only [block,hi,↓reduceIte]
    exact r63_concave_const_add (negative_concave atG hR hQ ht i)
      (positive f atG td R t s P i)

def data {f : Family} (atG td : Bool) {R t s : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain f) (hs : s∈shortDomain td) :
    OccupiedSignedConcentration.Data (Fin 4) where
  U i v := positive f atG td R t s v i
  V i v := negative f atG R t v i
  F i P N := block f atG td R t s P N i
  single := single f td
  U_zero := positive_zero f atG td R t s
  V_zero := negative_zero f atG R t
  F_left := fun i N => block_left atG td R ht s N i
  F_right := fun i P => block_right atG td R t s P i
  U_concave := positive_concave atG td hR hQ ht hs
  V_concave := negative_concave atG hR hQ ht
  F_concave_P := fun i N hN => block_concave_P atG td hR hQ ht hs hN i
  F_concave_N := fun i P hP => block_concave_N atG td hR hQ ht hs hP i

theorem positive_lower {f : Family} (atG td : Bool) {R t s v : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain f) (hs : s∈shortDomain td)
    (hv : v∈Icc 0 frameCap) (i : Fin 4) :
    -gamma f*v≤positive f atG td R t s v i := by
  have hbase (j : Fin 4) : -gamma f*v≤U R (small f atG t j) (large f atG t j) v := by
    have hU : -(109/200)*large f atG t j*v≤U R (small f atG t j) (large f atG t j) v :=
      OrdinaryPositiveEnvelope.U_lower hR hQ
        (SoleNegativeTCoefficients.positive atG ht j).2.2 min_le_max
        (SoleNegativeTCoefficients.half_ratio atG ht j) hv
    have hc := mul_le_mul_of_nonneg_right (old_cost atG ht j) hv.1
    linarith
  by_cases hD : i=3
  · subst i
    by_cases hde : isDE f=true
    · simpa [positive,hde] using hbase 1
    · have hde' := Bool.eq_false_of_not_eq_true hde
      by_cases hdiag : p (face f atG) t 0≤dCoefficient f td t s
      · have hm := mul_le_mul_of_nonneg_right (D_linear_cost atG ht) hv.1
        simp only [positive,↓reduceIte,hde',Bool.false_eq_true,hdiag]
        linarith
      · have hc := (coefficient_positive ht (zero_mem ht)).2.2.1
        have hcg := d_coefficient_ge td ht hs
        have hp2 := p_half_c atG ht
        have hU : -(109/200)*p (face f atG) t 0*v≤
            U R (dCoefficient f td t s) (p (face f atG) t 0) v :=
          OrdinaryPositiveEnvelope.U_lower hR hQ (hc.trans_le hcg)
            (lt_of_not_ge hdiag).le (by linarith : p (face f atG) t 0≤2*dCoefficient f td t s) hv
        have hm := mul_le_mul_of_nonneg_right (D_full_cost atG ht) hv.1
        simp only [positive,↓reduceIte,hde',Bool.false_eq_true,hdiag]
        linarith
  · by_cases hB : i=2 ∧ td=false
    · have hsBT : s∈Icc 0 (9/100:ℝ) := by simpa [shortDomain,hB.2] using hs
      have hb := changed_B_domain atG ht hsBT
      have hU : -(109/200)*(c f t 0/Real.cos s)*v≤
          U R (ell f t 0) (c f t 0/Real.cos s) v :=
        OrdinaryPositiveEnvelope.U_lower hR hQ hb.1 hb.2.1 hb.2.2 hv
      have hm := mul_le_mul_of_nonneg_right (changed_B_cost ht hsBT) hv.1
      obtain ⟨rfl,rfl⟩ := hB
      have hpos : positive f atG false R t s v 2=U R (ell f t 0) (c f t 0/Real.cos s) v := by
        simp [positive]
      rw [hpos]
      linarith
    · simpa [positive,hD,hB] using hbase i

theorem negative_lower {f : Family} (atG : Bool) {R t v L : ℝ}
    (hV : ∀ i,Used f i → L≤oldV f atG R t v i) (i : Fin 4) :
    L≤negative f atG R t v i := by
  by_cases hD : i=3
  · subst i
    by_cases hde : isDE f=true
    · simp only [negative,↓reduceIte,hde]
      exact hV 1 (Or.inr (by decide))
    · have hde' := Bool.eq_false_of_not_eq_true hde
      simp only [negative,↓reduceIte,hde',Bool.false_eq_true]
      exact le_min (hV 3 (Or.inl hde')) (hV 1 (Or.inr (by decide)))
  · simp only [negative,hD,↓reduceIte]
    exact hV i (Or.inr hD)

theorem negative_linear {f : Family} (atG : Bool) {R t v : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain f) (hv : v∈Icc 0 frameCap) (i : Fin 4) :
    gamma f*v≤negative f atG R t v i :=
  negative_lower atG (fun j _ => linear_lower atG hR hQL hQU ht hv j) i

end SquaresInCircles.Eight.SoleNegativeTOrdinaryData
