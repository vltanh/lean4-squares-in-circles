module
public import SquaresInCircles.Six.Analytic.WestPinCover
public import SquaresInCircles.Six.Normalization.PinData
public import SquaresInCircles.Six.DiagonalReflection

@[expose] public section

/-!
# Symmetries of the fixed pin set, before pin assignment

Only real-coordinate identities are used. These lemmas do not import the
pin-labelled packing or its old certificate-based construction. Consequently
they can be used in a direct proof of covering without a circular dependency.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization Normalization.Certificates

def pinReflection : Fin 5 → Fin 5 := ![1,0,4,3,2]

def pinDirection : Fin 5 → ℝ :=
  ![0,Real.pi/2,11*Real.pi/12,5*Real.pi/4,19*Real.pi/12]

lemma fixedPin_eq_polar (i : Fin 5) : fixedPin i=pinPoint (pinDirection i) := by
  fin_cases i <;> simp [fixedPin,pinDirection,pinPoint]
  all_goals congr 2 <;> ring

lemma pinPoint_periodic (θ : ℝ) : pinPoint (θ+2*Real.pi)=pinPoint θ := by
  simp [pinPoint]

lemma pinPoint_diagonal (θ : ℝ) :
    Six.diagonalPoint (pinPoint θ)=pinPoint (Real.pi/2-θ) := by
  simp [pinPoint,Six.diagonalPoint,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub]

lemma fixedPin_reflect (i : Fin 5) : Six.diagonalPoint (fixedPin i)=fixedPin (pinReflection i) := by
  rw [fixedPin_eq_polar,pinPoint_diagonal,fixedPin_eq_polar]
  fin_cases i
  · simp [pinDirection,pinReflection,pinPoint]
  · simp [pinDirection,pinReflection,pinPoint]
  · have h : Real.pi/2-11*Real.pi/12=19*Real.pi/12-2*Real.pi := by ring
    simp only [pinDirection,pinReflection,h,pinPoint,Real.cos_sub_two_pi,Real.sin_sub_two_pi]
  · have h : Real.pi/2-5*Real.pi/4=5*Real.pi/4-2*Real.pi := by ring
    simp only [pinDirection,pinReflection,h,pinPoint,Real.cos_sub_two_pi,Real.sin_sub_two_pi]
  · have h : Real.pi/2-19*Real.pi/12=11*Real.pi/12-2*Real.pi := by ring
    simp only [pinDirection,pinReflection,h,pinPoint,Real.cos_sub_two_pi,Real.sin_sub_two_pi]

lemma oriented_pin_periodic (t a b : ℝ) (p : Point) :
    openSquare (orientedSquare (t+2*Real.pi) a b) p ↔ openSquare (orientedSquare t a b) p := by
  simp [openSquare,orientedSquare_localX,orientedSquare_localY]

lemma oriented_pin_reflect (t a b : ℝ) (p : Point) :
    openSquare (orientedSquare (Real.pi/2-t) a (-b)) p ↔
      openSquare (orientedSquare t a b) (Six.diagonalPoint p) := by
  have hx : localX (orientedSquare (Real.pi/2-t) a (-b)) p=
      localX (orientedSquare t a b) (Six.diagonalPoint p) := by
    simp only [orientedSquare_localX,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,
      Six.diagonalPoint]
    ring
  have hy : localY (orientedSquare (Real.pi/2-t) a (-b)) p=
      -localY (orientedSquare t a b) (Six.diagonalPoint p) := by
    simp only [orientedSquare_localY,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,
      Six.diagonalPoint]
    ring
  simp only [openSquare,hx,hy,abs_neg]

def axisReflection : CentralAxis → CentralAxis
  | .own => .own
  | .secPlus => .secMinus
  | .secMinus => .secPlus
  | .east => .north
  | .north => .east
  | .west => .south
  | .south => .west

@[simp] lemma axisReflection_twice (k : CentralAxis) : axisReflection (axisReflection k)=k := by
  cases k <;> rfl

lemma margin_reflect (k : CentralAxis) (t a b x y : ℝ) :
    centralMargin (axisReflection k) (Real.pi/2-t) a (-b) y x=centralMargin k t a b x y := by
  cases k <;>
    simp only [axisReflection,centralMargin,centralNormal,centralTransverse,centerX,centerY,
      angularWidth,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub] <;> ring

lemma margin_periodic (k : CentralAxis) (t a b x y : ℝ) :
    centralMargin k (t+2*Real.pi) a b x y=centralMargin k t a b x y := by
  cases k <;> simp [centralMargin,centralNormal,centralTransverse,centerX,centerY,angularWidth]

lemma separator_reflect {t a b x y : ℝ}
    (h : ∃ k, 0 ≤ centralMargin k t a b x y) :
    ∃ k, 0 ≤ centralMargin k (Real.pi/2-t) a (-b) y x := by
  obtain ⟨k,hk⟩ := h
  exact ⟨axisReflection k,by simpa only [margin_reflect] using hk⟩

lemma separator_periodic {t a b x y : ℝ}
    (h : ∃ k, 0 ≤ centralMargin k t a b x y) :
    ∃ k, 0 ≤ centralMargin k (t+2*Real.pi) a b x y := by
  obtain ⟨k,hk⟩ := h
  exact ⟨k,by simpa only [margin_periodic] using hk⟩

end SquaresInCircles.Six.Analytic
