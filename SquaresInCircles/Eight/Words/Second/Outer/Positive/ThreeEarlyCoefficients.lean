module

public import SquaresInCircles.Eight.Words.Second.Outer.LReference
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeEarlyData

/-!
# Eight squares: exact coefficients of the single early-angle minorant

At target `27/100`, the physical radical has square `33227/10000`.
The first harmonic is affine in that radical or its reciprocal; the
second harmonic has one rational coefficient and one reciprocal
coefficient.  Thus one integer-square bracket proves every bound here.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.Early

open CommonQuarter CorePairGeometry Arithmetic

def qStar : ℝ := 33227/10000
def firstA : ℝ := 9984177/2500000
def firstC : ℝ := -737592427/125000000

lemma uStar_bounds :
    (182282747400844/100000000000000:ℝ)<uStar ∧
      uStar<182282747400845/100000000000000 := by
  exact shifted_chart_reference (outer_domain star_mem)
    (by norm_num) (by norm_num) (by norm_num [star,W,Q0]) (by norm_num [star,W,Q0])

lemma uStar_positive : 0<uStar := U_positive (outer_domain star_mem)

lemma uStar_sq : uStar^2=qStar := by
  have hh := UW_circle (outer_domain star_mem)
  norm_num [star,W,Q0] at hh
  dsimp [uStar,qStar,star]
  linarith

lemma rStar_times_u : rStar*uStar=wStar := by
  change W star/U star*U star=wStar
  rw [div_mul_cancel₀ _ (show U star≠0 from uStar_positive.ne')]
  norm_num [W,star,wStar]

lemma dStar_times_u : dStar*uStar=firstA*uStar+firstC := by
  have hh := LLabel.first_numerator (outer_domain star_mem)
  dsimp only [dStar,uStar]
  rw [hh]
  simp only [LLabel,star,W,Q0,firstA,firstC]
  ring

lemma a1_affine :
    a1=(-g+g*wStar*firstA/(m*qStar))*uStar+
      (g+g*wStar*firstC/(m*qStar)) := by
  have hq : qStar≠0 := by norm_num [qStar]
  have hp : dStar*rStar=wStar*(firstA*uStar+firstC)/qStar := by
    apply (eq_div_iff hq).2
    calc
      dStar*rStar*qStar=(dStar*uStar)*(rStar*uStar) := by rw [←uStar_sq]; ring
      _=(firstA*uStar+firstC)*wStar := by rw [dStar_times_u,rStar_times_u]
      _=wStar*(firstA*uStar+firstC) := by ring
  dsimp [a1]
  rw [show g*dStar*rStar/m=g*(dStar*rStar)/m by ring,hp]
  field_simp [hq,show m≠0 by norm_num [m]]
  ring

lemma b1_times_u : b1*uStar=(-g*wStar-g*firstA/m)*uStar-g*firstC/m := by
  dsimp [b1]
  linear_combination (-g/m)*dStar_times_u

lemma a2_rational : a2=g^2*(qStar-wStar^2)/(2*m*qStar) := by
  have hq : qStar≠0 := by norm_num [qStar]
  have hr : rStar^2=wStar^2/qStar := by
    apply (eq_div_iff hq).2
    calc
      rStar^2*qStar=(rStar*uStar)^2 := by rw [←uStar_sq]; ring
      _=wStar^2 := by rw [rStar_times_u]
  dsimp [a2]
  rw [hr]
  field_simp [hq,show m≠0 by norm_num [m]]

lemma b2_times_u : b2*uStar= -g^2*wStar/m := by
  dsimp [b2]
  linear_combination (-g^2/m)*rStar_times_u

lemma a1_bounds :
    (-563592126648/1000000000000:ℝ)<a1 ∧ a1< -563592126647/1000000000000 := by
  rw [a1_affine]
  norm_num [g,m,wStar,firstA,firstC,qStar]
  constructor <;> linarith [uStar_bounds.1,uStar_bounds.2]

lemma b1_bounds :
    (-1329332289459/1000000000000:ℝ)<b1 ∧ b1< -1329332289458/1000000000000 := by
  have he := b1_times_u
  norm_num [g,m,wStar,firstA,firstC] at he
  have hl : (-1329332289459/1000000000000:ℝ)*uStar<b1*uStar := by
    nlinarith [uStar_bounds.1,uStar_bounds.2]
  have hh : b1*uStar<(-1329332289458/1000000000000:ℝ)*uStar := by
    nlinarith [uStar_bounds.1,uStar_bounds.2]
  constructor
  · by_contra h
    have hp := mul_le_mul_of_nonneg_right (le_of_not_gt h) uStar_positive.le
    linarith
  · by_contra h
    have hp := mul_le_mul_of_nonneg_right (le_of_not_gt h) uStar_positive.le
    linarith

lemma a2_bounds :
    (305824407767/1000000000000:ℝ)<a2 ∧ a2<305824407768/1000000000000 := by
  rw [a2_rational]
  norm_num [g,m,qStar,wStar]

lemma b2_bounds :
    (-314490550356/1000000000000:ℝ)<b2 ∧ b2< -314490550355/1000000000000 := by
  have he := b2_times_u
  norm_num [g,m,wStar] at he
  have hl : (-314490550356/1000000000000:ℝ)*uStar<b2*uStar := by
    nlinarith [uStar_bounds.1,uStar_bounds.2]
  have hh : b2*uStar<(-314490550355/1000000000000:ℝ)*uStar := by
    nlinarith [uStar_bounds.1,uStar_bounds.2]
  constructor
  · by_contra h
    have hp := mul_le_mul_of_nonneg_right (le_of_not_gt h) uStar_positive.le
    linarith
  · by_contra h
    have hp := mul_le_mul_of_nonneg_right (le_of_not_gt h) uStar_positive.le
    linarith

lemma rStar_bounds :
    (422420668428/1000000000000:ℝ)<rStar ∧ rStar<422420668429/1000000000000 := by
  have he := rStar_times_u
  norm_num [wStar] at he
  have hl : (422420668428/1000000000000:ℝ)*uStar<rStar*uStar := by
    nlinarith [uStar_bounds.1,uStar_bounds.2]
  have hh : rStar*uStar<(422420668429/1000000000000:ℝ)*uStar := by
    nlinarith [uStar_bounds.1,uStar_bounds.2]
  constructor
  · by_contra h
    have hp := mul_le_mul_of_nonneg_right (le_of_not_gt h) uStar_positive.le
    linarith
  · by_contra h
    have hp := mul_le_mul_of_nonneg_right (le_of_not_gt h) uStar_positive.le
    linarith

lemma star_labels :
    (294743185706/1000000000000:ℝ)<L star ∧ L star<294743185707/1000000000000 ∧
    (756535360613/1000000000000:ℝ)<dStar ∧ dStar<756535360614/1000000000000 := by
  have hh := LReference.target star_mem
    (show star∈Icc (27/100) (27/100) by norm_num [star])
    ⟨uStar_bounds.1.le,uStar_bounds.2.le⟩ (by norm_num) (by norm_num)
  norm_num [LReference.valueLo,LReference.valueHi,LReference.firstLo,
    LReference.firstHi,LReference.secondLo,LReference.secondHi,Q0] at hh
  dsimp [dStar]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

end SquaresInCircles.Eight.SecondWord.PositiveThree.Early
