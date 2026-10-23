module

public import SquaresInCircles.Eight.TableFree.SolePositiveTSameBlock
public import SquaresInCircles.Eight.TableFree.SolePositiveTDEChord

/-!
# Actual one-angle coefficients on the two positive-T faces

Uncompiled source. The four pairs remain unordered until this layer.
The one-angle/mixed distinction is the actual owner distinction. The
uniform D enlargement appears only in the final pure scalar comparison.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SolePositiveTOrdinaryData
open SoleTScalarModel SolePositiveTCoefficients PositiveAngularEnvelope
open OrdinaryAngleConcavity SingleAngleConcavity

def small (s : ScalarCase) (t z : ℝ) (i : Fin 4) : ℝ :=
  min (first s t z i) (second s t z i)
def large (s : ScalarCase) (t z : ℝ) (i : Fin 4) : ℝ :=
  max (first s t z i) (second s t z i)
def single (s : ScalarCase) : Fin 4 → Bool :=
  ![!isDE s.family,true,!s.td,isDE s.family || s.td]
def actualNu (s : ScalarCase) (t z : ℝ) : Fin 4 → ℝ :=
  ![if isDE s.family then lambda s.family else n s t z,
    ell s.family t z,if s.td then m s t z else ell s.family t z,
    if isDE s.family then (if s.td then c s.family t z else m s t z)
      else if s.td then p s t z else max (p s t z) (m s t z)]

theorem small_pos (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) : 0<small s t z i := by
  obtain ⟨hn,hm,hp,ha,hb⟩ := weights_positive s ht hz
  exact lt_min (ha i) (hb i)

theorem small_le_large (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    small s t z i≤large s t z i := min_le_max

theorem nu_between (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    small s t z i≤actualNu s t z i ∧ actualNu s t z i≤large s t z i := by
  fin_cases i <;> cases s.family <;> cases s.td <;>
    simp [small,large,actualNu,first,second,lambda,isDE,p,tiltedE,
      min_le_left,min_le_right,le_max_left,le_max_right]

theorem mixed_nu (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) (hi : single s i=false) :
    actualNu s t z i=large s t z i := by
  have hB := m_ge_ell s ht hz
  have hH := pair_upper s ht hz 0
  fin_cases i <;> cases hf : s.family <;> cases htd : s.td <;>
    simp_all [single,actualNu,large,first,second,lambda,isDE,cap,
      max_eq_left,max_eq_right,p,tiltedE]

theorem pure_eq (s : ScalarCase) {R t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) (u : ℝ) :
    pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) u=
      Vnu R (small s t z i) (large s t z i) (actualNu s t z i) u := by
  cases hi : single s i
  · rw [mixed_nu s ht hz i hi]
    rfl
  · rfl

theorem m_ge_c (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) : c s.family t z≤m s t z := by
  have ht' := angle ht
  have hz' := (split_angles s ht hz).1
  have hηlo : 1/4+33/100*z≤eta t := by dsimp [eta]; linarith [hz.2]
  have hηhi : eta t≤481/1000 := by dsimp [eta,frameCap] at *; linarith [ht'.2]
  have hη0 : 0≤eta t := (coefficient_positive ht hz).2.2.2.2.2
  have hc := Real.one_sub_sq_div_two_le_cos z
  have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hz.1) hη0
  have hηz := mul_le_mul_of_nonneg_right hηlo hz.1
  have hηz3 := mul_le_mul_of_nonneg_right hηhi (pow_nonneg hz.1 3)
  have hz2 : z^2≤(7/10)*z := by dsimp [frameCap] at hz'; nlinarith [hz'.1,hz'.2]
  have hz3 : z^3≤(49/100)*z := by
    have hh := mul_le_mul_of_nonneg_right hz2 hz.1
    nlinarith
  have hfactor : 1≤Real.cos z+eta t*Real.sin z := by
    nlinarith [hz.1]
  have hh := mul_le_mul_of_nonneg_left hfactor (coefficient_positive ht hz).2.2.1.le
  simpa only [one_mul,mul_one,m] using hh

theorem DE_A_data (s : ScalarCase) {t z : ℝ} (hf : s.family=.deLow)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) :
    small s t z 1=ell s.family t z ∧ large s t z 1=k s.family t z ∧
    actualNu s t z 1=ell s.family t z ∧
    ell s.family t z/k s.family t z∈Icc (533/1000:ℝ) (81/100) := by
  have hk := (coefficient_positive ht hz).1
  have hdata := de_A s hf ht hz
  have horder : ell s.family t z≤k s.family t z := by nlinarith
  have hr := ratio_lower s ht hz 1
  have hs : small s t z 1=ell s.family t z := by
    simp [small,first,second,min_eq_right horder]
  have hl : large s t z 1=k s.family t z := by
    simp [large,first,second,max_eq_left horder]
  have hr' : (533/1000)*k s.family t z≤ell s.family t z := by
    simpa [ratio,hf,first,second,min_eq_right horder,max_eq_left horder] using hr
  refine ⟨hs,hl,rfl,?_,?_⟩
  · exact (le_div_iff₀ hk).2 hr'
  · exact (div_le_iff₀ hk).2 hdata.2

theorem DE_B_large (s : ScalarCase) {t z : ℝ} (hf : s.family=.deLow)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) : 903/1000≤large s t z 2 := by
  have hc : 903/1000≤c s.family t z := by
    rw [hf]
    dsimp [c,C]
    nlinarith [hz.1,hz.2]
  have hm := m_ge_c s ht hz
  have hh := le_max_right (first s t z 2) (second s t z 2)
  cases s.td <;> simp [large,second] at hh ⊢ <;> linarith

theorem DE_outer_small (s : ScalarCase) {t z : ℝ} (hf : s.family=.deLow)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) (hi : i=0 ∨ i=3) :
    18/25≤small s t z i := by
  have hr := ratio_lower s ht hz i
  have hmax := le_max_left (first s t z i) (second s t z i)
  rcases hi with rfl | rfl <;>
    simp [ratio,hf,first,lambda,isDE,p,tiltedE] at hr hmax <;>
    change 18/25≤min _ _ <;> linarith

theorem norm_eq (s : ScalarCase) (t z u : ℝ) (i : Fin 4) :
    pairNorm (small s t z i) (large s t z i) u=pairNorm (first s t z i) (second s t z i) u := by
  rcases le_total (first s t z i) (second s t z i) with h | h
  · simp [small,large,min_eq_left h,max_eq_right h]
  · simp [small,large,min_eq_right h,max_eq_left h,pairNorm_symm]

def baseline (s : ScalarCase) (R M t z : ℝ) : ℝ :=
  k s.family t z*primaryCoefficient R (g s.family t) (x s t z)+
    c s.family t z*primaryCoefficient R (eta t) z+2*ell s.family t z+eTerm s R M t z-
      R*∑ i,pairNorm (first s t z i) (second s t z i) 0

theorem scalar_identity (s : ScalarCase) (R M t z : ℝ) (i : Fin 4) :
    value {s with negative:=i} R M t z=baseline s R M t z+
      Vnu R (small s t z i) (large s t z i) (nu {s with negative:=i} t z) t := by
  rw [Vnu,norm_eq,norm_eq]
  fin_cases i <;>
    simp [value,baseline,square,nu,first,second,x,e,n,m,p,eTerm,pairNorm,
      Fin.sum_univ_succ,Real.sin_neg] <;> ring

theorem scalar_nu_upper (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) :
    actualNu s t z i≤nu {s with negative:=i} t z := by
  have hD := (nu_between s t z 3).2.trans (D_upper s ht hz)
  fin_cases i <;> cases s.family <;> cases s.td <;>
    simp_all [actualNu,nu,lambda,isDE]

theorem pure_scalar_lower (s : ScalarCase) {R M t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) :
    value {s with negative:=i} R M t z≤baseline s R M t z+
      pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t := by
  rw [scalar_identity,pure_eq s ht hz]
  have hh := mul_le_mul_of_nonpos_right (scalar_nu_upper s ht hz i)
    (show Real.cos t-1≤0 by linarith [Real.cos_le_one t])
  dsimp [Vnu]
  linarith

end SquaresInCircles.Eight.TableFree.SolePositiveTOrdinaryData
