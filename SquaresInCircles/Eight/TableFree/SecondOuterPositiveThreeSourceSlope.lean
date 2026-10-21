module

public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeSourceGeometry
public import SquaresInCircles.Eight.TableFree.SecondOuterLBounds

/-!
# The derivative along each actual fixed-source contact

The coefficient `g` is a fixed source-label derivative.  Two ordinary
chain rules give the exact curvature of the target derivative.  The
quotient estimate discards only two terms of known sign from the
physical circle formula.  These identities apply to both the short
source and the zero-source boundary.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree.SourceCurve

open CommonQuarter CorePairGeometry Arithmetic

def slope (g k φ : ℝ) : ℝ := g*quotient k φ-LLabel.d1 (target k φ)
def slopeFirst (g k φ : ℝ) : ℝ :=
  g*quotientFirst k φ-LLabel.d2 (target k φ)*bp k φ
def slopeSecond (g k φ : ℝ) : ℝ :=
  g*quotientSecond k φ-LLabel.d3 (target k φ)*(bp k φ)^2-
    LLabel.d2 (target k φ)*bpp k φ

lemma slope_hasDerivAt {k φ : ℝ} (g : ℝ) (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal) :
    HasDerivAt (slope g k) (slopeFirst g k φ) φ := by
  convert ((quotient_hasDerivAt h).const_mul g).sub
    ((LLabel.d1_hasDerivAt (outer_domain hb)).comp φ (target_hasDerivAt h))
      using 1 <;> dsimp [slope,slopeFirst] <;> ring

lemma slopeFirst_hasDerivAt {k φ : ℝ} (g : ℝ) (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal) :
    HasDerivAt (slopeFirst g k) (slopeSecond g k φ) φ := by
  have hd := ((quotientFirst_hasDerivAt h).const_mul g).sub
    (((LLabel.d2_hasDerivAt (outer_domain hb)).comp φ
      (target_hasDerivAt h)).mul (bp_hasDerivAt h))
  convert hd using 1 <;> dsimp [slopeFirst,slopeSecond] <;> ring

def quotientUpper (k φ : ℝ) : ℝ :=
  z k φ*Real.sin φ/(y k φ*u k φ)+y k φ*(f k φ)^2/u k φ+
    y k φ*w k φ*fp k φ/(u k φ)^2+
      2*y k φ*(w k φ)^2*(f k φ)^2/(u k φ)^3

lemma quotientSecond_le {k φ : ℝ} (h : Domain k φ) :
    quotientSecond k φ≤quotientUpper k φ := by
  have hy : 0<y k φ := by linarith [(y_data h).1]
  have hu := u_positive h
  have he : quotientUpper k φ-quotientSecond k φ=
      Q0*(Real.cos φ)^2/((y k φ)^3*u k φ)+
        2*yp k φ*up k φ/(u k φ)^2 := by
    dsimp [quotientUpper,quotientSecond,ypp,upp,up]
    field_simp [hy.ne',hu.ne']
    ring
  have hfirst : 0≤Q0*(Real.cos φ)^2/((y k φ)^3*u k φ) := by
    have hq : 0<Q0 := by norm_num [Q0]
    positivity
  have hprod := mul_nonneg_of_nonpos_of_nonpos (yp_nonpositive h) (up_negative h).le
  have hsecond : 0≤2*yp k φ*up k φ/(u k φ)^2 := by
    apply div_nonneg
    · nlinarith
    · positivity
  linarith

lemma quotient_positive {k φ : ℝ} (h : Domain k φ) : 0<quotient k φ :=
  div_pos (by linarith [(y_data h).1]) (u_positive h)

lemma original_slope {k φ : ℝ} (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal) :
    FirstContact.first (target k φ) φ=slope (VLabel.d1 (1/2-k)) k φ :=
  contact_derivative h hb

lemma original_slope_of_lower {g k φ : ℝ} (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal)
    (hg : g≤VLabel.d1 (1/2-k)) :
    slope g k φ≤FirstContact.first (target k φ) φ := by
  rw [original_slope h hb]
  dsimp [slope]
  exact sub_le_sub_right (mul_le_mul_of_nonneg_right hg (quotient_positive h).le) _

lemma opposite_product_upper {x y : ℝ}
    (hx : x∈Icc (-(567/500:ℝ)) (19/10))
    (hy : y∈Icc (-(69/200:ℝ)) (373/500)) : -x*y<(847/1000:ℝ) := by
  by_cases hxs : 0≤x
  · by_cases hys : 0≤y
    · have hh := mul_nonneg hxs hys
      nlinarith
    · have hh := mul_le_mul hx.2
        (show -y≤69/200 by linarith [hy.1])
        (neg_nonneg.mpr (le_of_not_ge hys)) (by norm_num : (0:ℝ)≤19/10)
      nlinarith
  · by_cases hys : 0≤y
    · have hh := mul_le_mul (show -x≤567/500 by linarith [hx.1]) hy.2 hys
        (by norm_num : (0:ℝ)≤567/500)
      nlinarith
    · have hh := mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hxs) (le_of_not_ge hys)
      nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree.SourceCurve
