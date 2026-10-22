module

public import SquaresInCircles.Eight.TableFree.ExceptionalPositiveTGrowth
public import SquaresInCircles.Eight.TableFree.ExceptionalPositiveTBlocks

/-!
# Actual contact coefficients and their scalar charges

Uncompiled source. H and the TD B block retain the maximum of their
two actual coefficients during concentration. Only afterward is the
high B coefficient enlarged to m+.03, and the H scalar is selected
between its two already proved full-square inequalities.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalPositiveTOrdinaryData
open ExceptionalPositiveTScalarModel ExceptionalPositiveTCoefficients
open PositiveAngularEnvelope OrdinaryAngleConcavity SingleAngleConcavity

def weights (s : ScalarCase) (t z : ℝ) : ExceptionalPositiveTBlocks.Weights :=
  ⟨n s t z,k s.family t z,ell s.family t z,
    if s.td then m s t z else c s.family t z,
    if s.td then c s.family t z else m s t z,p s t z⟩
def small (s : ScalarCase) (t z : ℝ) (i : Fin 4) : ℝ :=
  ExceptionalPositiveTBlocks.small (weights s t z) i
def large (s : ScalarCase) (t z : ℝ) (i : Fin 4) : ℝ :=
  ExceptionalPositiveTBlocks.large (weights s t z) i
def single (s : ScalarCase) : Fin 4 → Bool := ExceptionalPositiveTBlocks.single s.td
def actualNu (s : ScalarCase) (t z : ℝ) : Fin 4 → ℝ :=
  ExceptionalPositiveTBlocks.negative (weights s t z) s.td

theorem small_eq (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    small s t z i=min (first s t z i) (second s t z i) := rfl
theorem large_eq (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    large s t z i=max (first s t z i) (second s t z i) := rfl
theorem small_pos (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) : 0<small s t z i := by
  obtain ⟨_,_,_,ha,hb⟩ := weights_positive s ht hz
  exact lt_min (ha i) (hb i)
theorem small_le_large (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    small s t z i≤large s t z i := min_le_max
theorem nu_between (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    small s t z i≤actualNu s t z i ∧ actualNu s t z i≤large s t z i :=
  ExceptionalPositiveTBlocks.negative_between (weights s t z) s.td i
theorem mixed_nu (s : ScalarCase) (t z : ℝ) (i : Fin 4) (hi : single s i=false) :
    actualNu s t z i=large s t z i :=
  ExceptionalPositiveTBlocks.mixed_negative (weights s t z) s.td i hi
theorem pure_eq (s : ScalarCase) (R t z u : ℝ) (i : Fin 4) :
    pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) u=
      Vnu R (small s t z i) (large s t z i) (actualNu s t z i) u :=
  ExceptionalPositiveTBlocks.pure_eq (weights s t z) s.td R u i
theorem norm_eq (s : ScalarCase) (t z u : ℝ) (i : Fin 4) :
    pairNorm (small s t z i) (large s t z i) u=pairNorm (first s t z i) (second s t z i) u :=
  ExceptionalPositiveTBlocks.norm_eq (weights s t z) u i

theorem middle_A_data (s : ScalarCase) {t z : ℝ} (hf : s.family=.middle)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) :
    small s t z 1=ell s.family t z ∧ large s t z 1=k s.family t z ∧
    actualNu s t z 1=ell s.family t z ∧
    ell s.family t z/k s.family t z∈Icc (31/50:ℝ) (203/250) := by
  have hk := (coefficient_positive ht hz).1
  have hdata := middle_A s hf ht hz
  have horder : ell s.family t z≤k s.family t z := by nlinarith
  have hr := ratio_lower s ht hz 1
  have hs : small s t z 1=ell s.family t z := by
    simp [small_eq,first,second,min_eq_right horder]
  have hl : large s t z 1=k s.family t z := by
    simp [large_eq,first,second,max_eq_left horder]
  have hr' : (31/50)*k s.family t z≤ell s.family t z := by
    simpa [ratio,hf,first,second,min_eq_right horder,max_eq_left horder] using hr
  refine ⟨hs,hl,rfl,?_,?_⟩
  · exact (le_div_iff₀ hk).2 hr'
  · exact (div_le_iff₀ hk).2 hdata.2

def baseline (s : ScalarCase) (R t z : ℝ) : ℝ :=
  k s.family t z*ExceptionalContactSupport.contactScalar R (eta s.family t) (x s t z)+
    c s.family t z*ExceptionalContactSupport.contactScalar R (eta s.family t) z+
    2*ell s.family t z+ExceptionalContactSupport.contactScalar R (eta s.family t) (e s t z)-
      R*∑i,pairNorm (first s t z i) (second s t z i) 0

def chooseH (s : ScalarCase) (t z : ℝ) : Bool := by
  classical
  exact decide (n s t z≤p s t z)
def charged (s : ScalarCase) (t z : ℝ) (i : Fin 4) : ScalarCase :=
  {s with negative:=i,hCoefficient:=chooseH s t z}

theorem scalar_identity (s : ScalarCase) (R t z : ℝ) (i : Fin 4) (h : Bool) :
    value {s with negative:=i,hCoefficient:=h} R t z=baseline s R t z+
      Vnu R (small s t z i) (large s t z i)
        (nu {s with negative:=i,hCoefficient:=h} t z) t := by
  rw [Vnu,norm_eq,norm_eq]
  fin_cases i <;>
    simp [value,baseline,square,nu,first,second,x,e,n,m,p,pairNorm,
      Fin.sum_univ_succ,Real.sin_neg] <;> ring

theorem scalar_nu_upper (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) :
    actualNu s t z i≤nu (charged s t z i) t z := by
  have hB := scalar_B_upper s ht hz
  fin_cases i
  · by_cases h : n s t z≤p s t z
    · simp [actualNu,ExceptionalPositiveTBlocks.negative,weights,nu,charged,chooseH,h,max_eq_left h]
    · have hp : p s t z≤n s t z := (lt_of_not_ge h).le
      simp [actualNu,ExceptionalPositiveTBlocks.negative,weights,nu,charged,chooseH,h,max_eq_right hp]
  · rfl
  · cases htd : s.td
    · simp [actualNu,ExceptionalPositiveTBlocks.negative,weights,nu,charged,htd]
    · simpa [actualNu,ExceptionalPositiveTBlocks.negative,weights,nu,charged,htd] using hB
  · rfl

theorem pure_scalar_lower (s : ScalarCase) {R t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) :
    value (charged s t z i) R t z≤baseline s R t z+
      pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t := by
  rw [charged,scalar_identity,pure_eq]
  have hh := mul_le_mul_of_nonpos_right (scalar_nu_upper s ht hz i)
    (show Real.cos t-1≤0 by linarith [Real.cos_le_one t])
  dsimp [Vnu]
  linarith

end SquaresInCircles.Eight.TableFree.ExceptionalPositiveTOrdinaryData
