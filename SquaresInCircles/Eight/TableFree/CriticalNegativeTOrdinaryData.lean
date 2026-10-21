module

public import SquaresInCircles.Eight.TableFree.CriticalNegativeTContinuation
public import SquaresInCircles.Eight.TableFree.SoleNegativeTGrowth
public import SquaresInCircles.Eight.TableFree.OccupiedSignedConcentration

/-!
# The three actual critical ordinary blocks with negative T

Uncompiled source. D has no ordinary angle in either negative-primary
row. H retains both HG and the original EH angle; A has its actual
single AB angle; B is mixed only for TD2. In the aligned BT3 row its
larger force coefficient is the actual secant coefficient, while its
single negative coefficient remains l.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalNegativeTOrdinaryData
open Candidate CriticalECoefficients ExceptionalContactStress
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open SingleAngleConcavity CriticalNegativeTContinuation

def shortDomain (td : Bool) : Set ℝ := if td then Icc 0 (3/10) else Icc 0 (9/100)
def bWeight (td : Bool) (c s : ℝ) : ℝ := if td then c else c/Real.cos s
def tWeight (td : Bool) (c s : ℝ) : ℝ := if td then c/Real.cos s else c
def alpha (k l c eta x e s : ℝ) (td : Bool) : Fin 3 → ℝ := ![tilt eta e,l,l]
def beta (k l c eta x e s : ℝ) (td : Bool) : Fin 3 → ℝ :=
  ![k*tilt eta x,k,bWeight td c s]
def small (k l c eta x e s : ℝ) (td : Bool) (i : Fin 3) : ℝ :=
  min (alpha k l c eta x e s td i) (beta k l c eta x e s td i)
def large (k l c eta x e s : ℝ) (td : Bool) (i : Fin 3) : ℝ :=
  max (alpha k l c eta x e s td i) (beta k l c eta x e s td i)
def single (td : Bool) : Fin 3 → Bool := ![false,true,!td]
def nu (k l c eta x e s : ℝ) (td : Bool) : Fin 3 → ℝ :=
  ![large k l c eta x e s td 0,l,if td then c else l]

theorem short_small {td : Bool} {s : ℝ} (hs : s∈shortDomain td) : s∈Icc 0 frameCap := by
  cases td <;> norm_num [shortDomain,frameCap] at hs ⊢ <;> exact ⟨hs.1,by linarith [hs.2]⟩

theorem b_bounds {t k l c eta s : ℝ} {td : Bool}
    (h : Bounds t k l c eta) (hs : s∈shortDomain td) :
    c≤bWeight td c s ∧ bWeight td c s≤(101/100)*c ∧
      l≤bWeight td c s ∧ bWeight td c s≤2*l ∧ bWeight td c s≤21/20 := by
  have hc : 0<c := by linarith [h.c_lower]
  have ho := h.order
  cases td
  · have hs' : s∈Icc 0 (9/100:ℝ) := by simpa [shortDomain] using hs
    have hb := trig_bracket (l := 0) (u := (9/100:ℝ))
      (by norm_num) (by linarith [Real.pi_gt_three]) hs'
    have hcos : (100/101:ℝ)<Real.cos s := by norm_num at hb; linarith [hb.2.2.1]
    have hcos0 : 0<Real.cos s := by linarith
    have hlo : c≤c/Real.cos s := (le_div_iff₀ hcos0).2
      (by nlinarith [Real.cos_le_one s])
    have hhi : c/Real.cos s≤(101/100)*c := (div_le_iff₀ hcos0).2
      (by nlinarith [mul_pos hc (show 0<Real.cos s-100/101 by linarith)])
    simp only [bWeight,Bool.false_eq_true,if_false]
    refine ⟨hlo,hhi,ho.2.2.1.trans hlo,?_,?_⟩ <;>
      nlinarith [h.ell_c_lower,h.c_upper]
  · simp only [bWeight,if_true]
    exact ⟨le_rfl,by linarith,ho.2.2.1,ho.2.2.2.2.1,by linarith [h.c_upper]⟩

theorem wide_data {t k l c eta x e s : ℝ} (td : Bool) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    SoleLowChargeBounds.base≤small k l c eta x e s td 0 ∧
      large k l c eta x e s td 0∈Icc 1 (21/20:ℝ) := by
  simpa only [small,large,alpha,beta,ExceptionalContactBlocks.small,
    ExceptionalContactBlocks.large,ExceptionalContactBlocks.alpha,
    ExceptionalContactBlocks.beta,Matrix.cons_val_zero] using
      CriticalEEnvelope.wide_data h hx he (Or.inl rfl)

theorem AB_data {t k l c eta x e s : ℝ} {td : Bool}
    (h : Bounds t k l c eta) (hs : s∈shortDomain td) :
    small k l c eta x e s td 1=l ∧ large k l c eta x e s td 1=k ∧
      small k l c eta x e s td 2=l ∧ large k l c eta x e s td 2=bWeight td c s := by
  have hk := h.order.2.1
  have hb := (b_bounds h hs).2.2.1
  simp [small,large,alpha,beta,min_eq_left hk,max_eq_right hk,
    min_eq_left hb,max_eq_right hb]

theorem conditions {t k l c eta x e s : ℝ} {td : Bool} (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td) (i : Fin 3) :
    0<small k l c eta x e s td i ∧
      small k l c eta x e s td i≤nu k l c eta x e s td i ∧
      nu k l c eta x e s td i≤large k l c eta x e s td i ∧
      large k l c eta x e s td i≤2*small k l c eta x e s td i ∧
      large k l c eta x e s td i≤21/20 := by
  have ho := h.order
  obtain ⟨ha,hA,hb,hB⟩ := AB_data (x := x) (e := e) h hs
  fin_cases i
  · have hh := wide_data td h hx he
    have hp : 0<small k l c eta x e s td 0 := by
      dsimp [SoleLowChargeBounds.base] at hh; linarith [hh.1]
    simp only [nu,Matrix.cons_val_zero]
    exact ⟨hp,min_le_max,le_rfl,by dsimp [SoleLowChargeBounds.base] at hh; linarith [hh.1,hh.2.2],hh.2.2⟩
  · simp only [ha,hA,nu,Matrix.cons_val_one,Matrix.cons_val_zero]
    exact ⟨h.ell_pos,le_rfl,ho.2.1,ho.2.2.2.2.2.1,by linarith [h.k_upper]⟩
  · rw [hb,hB]
    have hh := b_bounds h hs
    cases td <;> simp only [nu,Matrix.cons_val_two,Matrix.cons_val_one,Matrix.cons_val_zero,
      Bool.false_eq_true,if_false,if_true,bWeight] at hh ⊢
    · exact ⟨h.ell_pos,le_rfl,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2⟩
    · exact ⟨h.ell_pos,ho.2.2.1,le_rfl,hh.2.2.2.1,hh.2.2.2.2⟩

theorem smaller_lower {t k l c eta x e s : ℝ} {td : Bool} (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td) (i : Fin 3) :
    (2331/4000:ℝ)<small k l c eta x e s td i := by
  obtain ⟨ha,_,hb,_⟩ := AB_data (x := x) (e := e) h hs
  fin_cases i
  · have hh := (wide_data td h hx he).1
    dsimp [SoleLowChargeBounds.base] at hh
    linarith
  · rw [ha]; nlinarith [h.ell_c_lower,h.c_lower]
  · rw [hb]; nlinarith [h.ell_c_lower,h.c_lower]

theorem mixed_indices {td : Bool} {i : Fin 3} (hi : single td i=false) :
    i=0 ∨ (i=2 ∧ td=true) := by
  fin_cases i <;> cases td <;> simp_all [single]

theorem mixed_ratio {t k l c eta x e s : ℝ} {td : Bool} (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td)
    (i : Fin 3) (hi : single td i=false) :
    (63/100)*large k l c eta x e s td i≤small k l c eta x e s td i := by
  rcases mixed_indices hi with rfl | ⟨rfl,rfl⟩
  · have hh := wide_data td h hx he
    dsimp [SoleLowChargeBounds.base] at hh
    linarith [hh.1,hh.2.2]
  · obtain ⟨_,_,hb,hB⟩ := AB_data (x := x) (e := e) h hs
    rw [hb,hB]
    simpa [bWeight] using h.ell_c_lower.le

theorem mixed_nu {t k l c eta x e s : ℝ} {td : Bool}
    (h : Bounds t k l c eta) (hs : s∈shortDomain td)
    (i : Fin 3) (hi : single td i=false) :
    nu k l c eta x e s td i=large k l c eta x e s td i := by
  rcases mixed_indices hi with rfl | ⟨rfl,rfl⟩
  · rfl
  · obtain ⟨_,_,_,hB⟩ := AB_data (x := x) (e := e) h hs
    simpa [nu,bWeight] using hB.symm

def data {R t k l c eta x e s : ℝ} {td : Bool}
    (hR : 0≤R) (hQ : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td) :
    OccupiedSignedConcentration.Data (Fin 3) where
  U := fun i => U R (small k l c eta x e s td i) (large k l c eta x e s td i)
  V := fun i => pure (single td i) R (small k l c eta x e s td i)
    (large k l c eta x e s td i) (nu k l c eta x e s td i)
  F := fun i => F (single td i) R (small k l c eta x e s td i)
    (large k l c eta x e s td i) (nu k l c eta x e s td i)
  single := single td
  U_zero := fun i => U_zero _ _ _
  V_zero := fun i => pure_zero _ _ _ _ _
  F_left := fun i N => F_zero_left _ _ _ _ _ N
  F_right := fun i P => F_zero_right _ _ _ _ _ P
  U_concave := fun i => U_concave hR hQ (conditions h hx he hs i).1
    min_le_max (conditions h hx he hs i).2.2.2.1
  V_concave := fun i => pure_concave hR hQ (conditions h hx he hs i).1
    min_le_max (conditions h hx he hs i).2.2.2.1 (conditions h hx he hs i).2.1
  F_concave_P := fun i N hN => F_concave_P hR hQ (conditions h hx he hs i).1
    min_le_max (conditions h hx he hs i).2.2.2.1 hN
  F_concave_N := fun i P hP => F_concave_N hR hQ (conditions h hx he hs i).1
    min_le_max (conditions h hx he hs i).2.2.2.1 (conditions h hx he hs i).2.1 hP

theorem positive_lower {R t k l c eta x e s v : ℝ} {td : Bool}
    (hR : 0≤R) (hQ : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td)
    (hv : v∈Icc 0 frameCap) (i : Fin 3) :
    -gamma*v≤U R (small k l c eta x e s td i) (large k l c eta x e s td i) v := by
  have hc := conditions h hx he hs i
  have hh := OrdinaryPositiveEnvelope.U_lower hR hQ hc.1 min_le_max hc.2.2.2.1 hv
  have hm := mul_le_mul_of_nonneg_right hc.2.2.2.2 hv.1
  dsimp [gamma]
  nlinarith

theorem negative_linear {R t k l c eta x e s v : ℝ} {td : Bool}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td)
    (hv : v∈Icc 0 frameCap) (i : Fin 3) :
    gamma*v≤pure (single td i) R (small k l c eta x e s td i)
      (large k l c eta x e s td i) (nu k l c eta x e s td i) v := by
  have hc := conditions h hx he hs i
  have hp := smaller_lower h hx he hs i
  have hratio : gamma≤(87/70)*small k l c eta x e s td i := by dsimp [gamma]; linarith
  have hscaled := mul_le_mul_of_nonneg_right hratio hv.1
  cases hm : single td i
  · have hh := SoleNegativeTGrowth.radius_chord hR hQL hQU hc.1 min_le_max hc.2.2.2.1
      (min_le_max : small k l c eta x e s td i≤large k l c eta x e s td i) (le_refl _) hv
    simpa [pure,hm] using hscaled.trans hh
  · have hh := SoleNegativeTGrowth.radius_chord hR hQL hQU hc.1 min_le_max hc.2.2.2.1
      hc.2.1 hc.2.2.1 hv
    simpa [pure,hm] using hscaled.trans hh

end SquaresInCircles.Eight.TableFree.CriticalNegativeTOrdinaryData
