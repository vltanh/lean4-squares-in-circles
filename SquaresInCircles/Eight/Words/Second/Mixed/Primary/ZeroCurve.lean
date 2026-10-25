module

public import SquaresInCircles.Eight.Words.Second.Mixed.LHeightGrowth

/-!
# Eight squares: the exact primary zero-source contact curve

The contact height and its speed are one harmonic pair.  The target
transverse coordinate is the positive root of the original circle,
with every derivative proved on that actual radical domain.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.PrimaryZero
open CommonQuarter CorePairGeometry Arithmetic

def m (φ : ℝ) : ℝ := (13/12)*Real.cos φ+Real.sin φ/2
def v (φ : ℝ) : ℝ := (13/12)*Real.sin φ-Real.cos φ/2
def U (φ : ℝ) : ℝ := 1+m φ
def V (φ : ℝ) : ℝ := HeightLabel.root (U φ)
def b (φ : ℝ) : ℝ := V φ-1/2

lemma m_hasDerivAt (φ : ℝ) : HasDerivAt m (-v φ) φ := by
  have h : HasDerivAt (fun y => (13/12)*Real.cos y+Real.sin y/2)
      ((13/12)*(-Real.sin φ)+Real.cos φ/2) φ :=
    ((Real.hasDerivAt_cos φ).const_mul (13/12)).add ((Real.hasDerivAt_sin φ).div_const 2)
  refine h.congr_deriv ?_
  unfold v
  ring

lemma v_hasDerivAt (φ : ℝ) : HasDerivAt v (m φ) φ := by
  have h : HasDerivAt (fun y => (13/12)*Real.sin y-Real.cos y/2)
      ((13/12)*Real.cos φ-(-Real.sin φ)/2) φ :=
    ((Real.hasDerivAt_sin φ).const_mul (13/12)).sub ((Real.hasDerivAt_cos φ).div_const 2)
  refine h.congr_deriv ?_
  unfold m
  ring

lemma U_hasDerivAt (φ : ℝ) : HasDerivAt U (-v φ) φ := (m_hasDerivAt φ).const_add 1

lemma V_hasDerivAt {φ : ℝ} (hφ : 0<Q0-(U φ)^2) :
    HasDerivAt V (U φ*v φ/V φ) φ := by
  refine ((HeightLabel.root_hasDerivAt hφ).comp φ (U_hasDerivAt φ)).congr_deriv ?_
  rw [show V φ=HeightLabel.root (U φ) from rfl]
  ring

lemma mv_circle (φ : ℝ) : (m φ)^2+(v φ)^2=(205/144:ℝ) := by
  dsimp [m,v]
  nlinarith [Real.sin_sq_add_cos_sq φ]

lemma terminal_trig :
    (123181215/125000000:ℝ)≤Real.sin (7/5) ∧ Real.sin (7/5)≤49272487/50000000 ∧
    (8498357/50000000:ℝ)≤Real.cos (7/5) ∧ Real.cos (7/5)≤3399343/20000000 := by
  have hs := HighOrderTaylor.S15_le_sin (x := (7/5:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (7/5:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (7/5:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (7/5:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S11,HighOrderTaylor.S13,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8]
    at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

end SquaresInCircles.Eight.SecondWord.PrimaryZero
