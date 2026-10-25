module

public import SquaresInCircles.Eight.Words.Common.JumpTwo

/-!
# Eight squares: the unchanged canonical core corner in one coordinate

This chart includes the side join and the diagonal.  The derivative
formulas use its positive radical directly, so no angular reparametrizing
or strict-owner convention is required.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedCorner
open CommonQuarter CorePairGeometry Arithmetic

def domain : Set ℝ := Icc (1/2) CoreAngleEndpoint.diagonal
def z (b : ℝ) : ℝ := Real.sqrt (1/144-(b-1/2)^2)
def a (b : ℝ) : ℝ := 1/2+z b
def w (b : ℝ) : ℝ := (b-1/2)/z b

lemma radicand_positive {b : ℝ} (hb : b∈domain) : 0<(1/144:ℝ)-(b-1/2)^2 := by
  have hs := pow_le_pow_left₀ (sub_nonneg.mpr hb.1)
    (show b-1/2≤CoreAngleEndpoint.diagonal-1/2 by linarith [hb.2]) 2
  nlinarith [CoreAngleEndpoint.diagonal_sq]

lemma z_positive {b : ℝ} (hb : b∈domain) : 0<z b := Real.sqrt_pos.mpr (radicand_positive hb)
lemma z_sq {b : ℝ} (hb : b∈domain) : (z b)^2+(b-1/2)^2=(1/144:ℝ) := by
  have hh := Real.sq_sqrt (radicand_positive hb).le
  change (z b)^2=1/144-(b-1/2)^2 at hh
  linarith

lemma chart_bounds {b : ℝ} (hb : b∈domain) :
    CoreAngleEndpoint.diagonal-1/2≤z b ∧ z b≤1/12 ∧ b≤a b := by
  have hp := z_positive hb
  have hs := z_sq hb
  have hdiag := CoreAngleEndpoint.diagonal_bounds
  have hsmall := pow_le_pow_left₀ (sub_nonneg.mpr hb.1)
    (show b-1/2≤CoreAngleEndpoint.diagonal-1/2 by linarith [hb.2]) 2
  refine ⟨?_,?_,?_⟩
  · nlinarith [CoreAngleEndpoint.diagonal_sq]
  · nlinarith [sq_nonneg (b-1/2)]
  · dsimp [a]
    nlinarith [CoreAngleEndpoint.diagonal_sq]

lemma state {b : ℝ} (hb : b∈domain) : CoreState (a b) b := by
  refine Or.inr ⟨hb.1,(chart_bounds hb).2.2,?_⟩
  dsimp [a]
  nlinarith [z_sq hb]

lemma actual {A B : ℝ} (hB : 1/2≤B) (hBA : B≤A)
    (hc : (A-1/2)^2+(B-1/2)^2=(1/12:ℝ)^2) :
    B∈domain ∧ A=a B := by
  have hdom : B∈domain := ⟨hB,(CoreAngleEndpoint.corner_diagonal hB hBA hc).1⟩
  have hp := z_positive hdom
  have hs := z_sq hdom
  refine ⟨hdom,?_⟩
  dsimp [a]
  nlinarith

lemma join : a (1/2)=(7/12:ℝ) := by
  have hb : (1/2:ℝ)∈domain := ⟨le_rfl,by linarith [CoreAngleEndpoint.diagonal_bounds.1]⟩
  have hs := z_sq hb
  have hp := z_positive hb
  dsimp [a]
  nlinarith

lemma diagonal : a CoreAngleEndpoint.diagonal=CoreAngleEndpoint.diagonal := by
  have hb : CoreAngleEndpoint.diagonal∈domain :=
    ⟨by linarith [CoreAngleEndpoint.diagonal_bounds.1],le_rfl⟩
  have hs := z_sq hb
  have hp := z_positive hb
  dsimp [a]
  nlinarith [CoreAngleEndpoint.diagonal_sq,CoreAngleEndpoint.diagonal_bounds.1]

lemma w_bounds {b : ℝ} (hb : b∈domain) : 0≤w b ∧ w b≤1 := by
  have hp := z_positive hb
  have hba := (chart_bounds hb).2.2
  constructor
  · exact div_nonneg (sub_nonneg.mpr hb.1) hp.le
  · apply (div_le_one hp).2
    dsimp [a] at hba
    linarith

lemma circle_ratio {b : ℝ} (hb : b∈domain) : (1+(w b)^2)*(z b)^2=(1/144:ℝ) := by
  have hp := z_positive hb
  dsimp [w]
  field_simp [hp.ne']
  nlinarith [z_sq hb]

lemma z_hasDerivAt {b : ℝ} (hb : b∈domain) : HasDerivAt z (-w b) b := by
  have hp := z_positive hb
  have h1 : HasDerivAt (fun y : ℝ => 1/144-(y-1/2)^2) (-(2*(b-1/2))) b := by
    have h := (((hasDerivAt_id b).sub_const (1/2)).pow 2).const_sub (1/144)
    convert h using 1
    · funext y
      simp
    · simp only [id]
      norm_num
  have h2 := h1.sqrt (radicand_positive hb).ne'
  have hz : (fun y : ℝ => Real.sqrt (1/144-(y-1/2)^2))=z := rfl
  rw [hz] at h2
  convert h2 using 1
  rw [show Real.sqrt (1/144-(b-1/2)^2)=z b from rfl]
  dsimp only [w]
  field_simp

lemma a_hasDerivAt {b : ℝ} (hb : b∈domain) : HasDerivAt a (-w b) b :=
  (z_hasDerivAt hb).const_add (1/2)

lemma w_hasDerivAt {b : ℝ} (hb : b∈domain) :
    HasDerivAt w ((1+(w b)^2)/z b) b := by
  have hp := z_positive hb
  have hd := ((hasDerivAt_id b).sub_const (1/2)).div (z_hasDerivAt hb) hp.ne'
  convert hd using 1
  · rfl
  · dsimp [w]
    field_simp [hp.ne']
    ring

lemma endpoint_mass {b : ℝ} (hb : b∈domain) :
    (a b+1/2)^2+(b-1/2)^2∈Icc (112479/100000:ℝ) (169/144) := by
  have hs := z_sq hb
  have hbounds := chart_bounds hb
  have he : (a b+1/2)^2+(b-1/2)^2=1+2*z b+1/144 := by
    dsimp [a]
    nlinarith
  rw [he]
  constructor <;> linarith [hbounds.1,hbounds.2.1,CoreAngleEndpoint.diagonal_bounds.1]

end SquaresInCircles.Eight.SecondWord.MixedCorner
