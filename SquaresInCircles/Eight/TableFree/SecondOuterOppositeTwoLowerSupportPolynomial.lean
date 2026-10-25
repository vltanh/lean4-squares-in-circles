module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoLowerSourceSecondary

/-!
# One polynomial for the whole lower-angle support curvature

The squared comparison for the support second derivative is a single
quintic in sin x.  Translation by .645 leaves a positive polynomial
remainder over an explicit cubic lower expression.  The proof uses
only one polynomial identity and the full angle interval.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.LowerSupport

open CommonQuarter CorePairGeometry Arithmetic

def g : ℝ := 83829/100000
def h : ℝ := 1061/1000
def polynomial (t : ℝ) : ℝ :=
  (1-t^2)*(g^2+h^2-2*g*h*t)^3-Q0*g^2*(g-h*t)^2*(h-g*t)^2
def lowerPolynomial (y : ℝ) : ℝ :=
  83/500+(1553/1000)*y+(623/125)*y^2+
    y^3*(2909/500-(691/500)*y-(5629/1000)*y^2)

lemma translated_identity (y : ℝ) :
    polynomial (129/200-y)-lowerPolynomial y=
      (341184490123782502305922594864415451/
        400000000000000000000000000000000000000:ℝ)+
      (40444622553420958760087623349/3125000000000000000000000000000000)*y+
      (3762689327888255944785062136869/5000000000000000000000000000000000)*y^2+
      (237507106019665678702061123/625000000000000000000000000000)*y^3+
      (225920263852122763120047611/250000000000000000000000000000)*y^4+
      (19852391049615193991/125000000000000000000000)*y^5 := by
  norm_num [polynomial,lowerPolynomial,g,h,Q0]
  ring

lemma translated_lower {y : ℝ} (hy : 0≤y) :
    lowerPolynomial y<polynomial (129/200-y) := by
  have he := translated_identity y
  have hp : 0<
      (341184490123782502305922594864415451/
        400000000000000000000000000000000000000:ℝ)+
      (40444622553420958760087623349/3125000000000000000000000000000000)*y+
      (3762689327888255944785062136869/5000000000000000000000000000000000)*y^2+
      (237507106019665678702061123/625000000000000000000000000000)*y^3+
      (225920263852122763120047611/250000000000000000000000000000)*y^4+
      (19852391049615193991/125000000000000000000000)*y^5 := by positivity
  linarith

theorem polynomial_positive {t : ℝ} (ht : t∈Icc 0 (129/200)) :
    (83/500:ℝ)<polynomial t := by
  obtain ⟨y, hyd⟩ : ∃ y : ℝ, y=129/200-t := ⟨_, rfl⟩
  have hy : y∈Icc 0 (129/200) := by rw [hyd]; constructor <;> linarith [ht.1,ht.2]
  have hy2 := pow_le_pow_left₀ hy.1 hy.2 2
  have hbracket : (5/2:ℝ)<2909/500-(691/500)*y-(5629/1000)*y^2 := by
    linarith [hy.2]
  have htail := mul_nonneg (pow_nonneg hy.1 3)
    (show 0≤2909/500-(691/500)*y-(5629/1000)*y^2 by linarith)
  have hh := translated_lower hy.1
  have he : 129/200-y=t := by rw [hyd]; ring
  rw [he] at hh
  dsimp [lowerPolynomial] at hh
  linarith [sq_nonneg y, hy.1]

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.LowerSupport
