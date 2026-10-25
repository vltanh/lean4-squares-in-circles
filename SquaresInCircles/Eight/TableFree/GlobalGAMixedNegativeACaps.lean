module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeAEntry

/-!
# The four original flat-core A caps

Uncompiled transcription of Section 2 of
`HAND_G3_MIXED_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_ONE.md`.
The upper caps have constant term -1/2. Their parameter P is the
unchanged primary coordinate of G minus 1/2; the lower parameter B
is the unchanged positive tangent magnitude of the outer B point.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.MixedNegativeA
open Candidate Secondary

abbrev cut : ℝ := 19/50
abbrev K : ℝ := 13/12
abbrev k0 : ℝ := 1/12

def cap (d P k r : ℝ) : ℝ := d+(P+k*Real.sin r)/Real.cos r
def capD (P k r : ℝ) : ℝ := (P*Real.sin r+k)/Real.cos r^2

def Uminus (P r : ℝ) : ℝ := cap (-1/2) P (-K) r
def Uplus (P r : ℝ) : ℝ := cap (-1/2) P k0 r
def Lminus (B r : ℝ) : ℝ := cap (1/2) (1/2-B) K r
def Lplus (B r : ℝ) : ℝ := cap (1/2) (1/2-B) (-k0) r

def flat (b : ℝ) : SignedPoint := ⟨7/12,b⟩

theorem angle_domain {r : ℝ} (hr : r∈Icc 0 cut) : r∈Icc 0 frameCap :=
  ⟨hr.1,hr.2.trans (by norm_num [cut,frameCap])⟩

theorem cosine_positive {r : ℝ} (hr : r∈Icc 0 cut) : 0<Real.cos r := by
  linarith [(transport_trig (angle_domain hr)).1]

theorem cap_hasDerivAt (d P k : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    HasDerivAt (cap d P k) (capD P k r) r := by
  have hc := (cosine_positive hr).ne'
  have h1 := ((Real.hasDerivAt_sin r).const_mul k).const_add P
  have hh := (h1.div (Real.hasDerivAt_cos r) hc).const_add d
  convert hh using 1
  · rfl
  · dsimp [capD]
    field_simp [hc]
    linear_combination (-k)*(Real.sin_sq_add_cos_sq r)

theorem Uminus_hasDerivAt (P : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    HasDerivAt (Uminus P) (capD P (-K) r) r := cap_hasDerivAt _ _ _ hr

theorem Uplus_hasDerivAt (P : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    HasDerivAt (Uplus P) (capD P k0 r) r := cap_hasDerivAt _ _ _ hr

theorem Lminus_hasDerivAt (B : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    HasDerivAt (Lminus B) (capD (1/2-B) K r) r := cap_hasDerivAt _ _ _ hr

theorem Lplus_hasDerivAt (B : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    HasDerivAt (Lplus B) (capD (1/2-B) (-k0) r) r := cap_hasDerivAt _ _ _ hr

@[simp] theorem Uminus_zero (P : ℝ) : Uminus P 0=P-1/2 := by norm_num [Uminus,cap]; ring
@[simp] theorem Uplus_zero (P : ℝ) : Uplus P 0=P-1/2 := by norm_num [Uplus,cap]; ring
@[simp] theorem Lminus_zero (B : ℝ) : Lminus B 0=1-B := by norm_num [Lminus,cap]; ring
@[simp] theorem Lplus_zero (B : ℝ) : Lplus B 0=1-B := by norm_num [Lplus,cap]; ring

theorem GA_negative_iff (G : SignedPoint) (b : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    quarterFeasible G (flat b) (-r) 3 ↔ b≤Uminus (G.a-1/2) r := by
  have hc := cosine_positive hr
  rw [quarterFeasible,edgeWidth_negative_formula (angle_domain hr)]
  simp only [quarterProjection,Matrix.cons_val,flat,Real.sin_neg,Real.cos_neg]
  unfold Uminus cap
  rw [← sub_le_iff_le_add',le_div_iff₀ hc]
  simp only [K]
  constructor <;> intro hh <;> linarith only [hh]

theorem GA_positive_iff (G : SignedPoint) (b : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    quarterFeasible G (flat b) r 3 ↔ b≤Uplus (G.a-1/2) r := by
  have hc := cosine_positive hr
  rw [quarterFeasible,edgeWidth_positive_formula (angle_domain hr)]
  simp only [quarterProjection,Matrix.cons_val,flat]
  unfold Uplus cap
  rw [← sub_le_iff_le_add',le_div_iff₀ hc]
  simp only [k0]
  constructor <;> intro hh <;> linarith only [hh]

theorem AB_negative_iff (B : SignedPoint) (b : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    zeroFeasible (flat b) B (-r) 2 ↔ Lminus (-B.y) r≤b := by
  have hc := cosine_positive hr
  rw [zeroFeasible,edgeWidth_negative_formula (angle_domain hr)]
  simp only [zeroProjection,Matrix.cons_val,flat,Real.sin_neg,Real.cos_neg]
  unfold Lminus cap
  rw [← le_sub_iff_add_le',div_le_iff₀ hc]
  simp only [K]
  constructor <;> intro hh <;> linarith only [hh]

theorem AB_positive_iff (B : SignedPoint) (b : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    zeroFeasible (flat b) B r 2 ↔ Lplus (-B.y) r≤b := by
  have hc := cosine_positive hr
  rw [zeroFeasible,edgeWidth_positive_formula (angle_domain hr)]
  simp only [zeroProjection,Matrix.cons_val,flat]
  unfold Lplus cap
  rw [← le_sub_iff_add_le',div_le_iff₀ hc]
  simp only [k0]
  constructor <;> intro hh <;> linarith only [hh]

theorem flat_geometry {b : ℝ} (hb : b∈Ioo 0 (1/2:ℝ)) :
    (flat b).Sorted ∧ (flat b).Core ∧ (flat b).AvoidsCore ∧
      (flat b).circle<313/144 := by
  have habs : |b|=b := abs_of_pos hb.1
  refine ⟨?_,?_,?_,?_⟩
  · simp only [SignedPoint.Sorted,flat,habs]
    exact ⟨by norm_num,by linarith [hb.2]⟩
  · norm_num [SignedPoint.Core,SignedPoint.coreDistance,flat,habs,
      max_eq_right (show b-1/2≤0 by linarith [hb.2])]
  · norm_num [SignedPoint.AvoidsCore,SignedPoint.coreDistance,flat,habs,
      max_eq_right (show b-1/2≤0 by linarith [hb.2])]
  · dsimp [SignedPoint.circle,flat]
    rw [habs]
    nlinarith [hb.1,hb.2]

theorem flat_small_circle {b : ℝ} (hb : b∈Ioo 0 (1/5:ℝ)) :
    (flat b).circle<5989/3600 := by
  dsimp [SignedPoint.circle,flat]
  rw [abs_of_pos hb.1]
  nlinarith [hb.1,hb.2]

end SquaresInCircles.Eight.TableFree.GlobalGA.MixedNegativeA
