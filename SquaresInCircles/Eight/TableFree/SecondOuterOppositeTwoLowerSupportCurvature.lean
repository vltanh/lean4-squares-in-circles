module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoLowerSupportPolynomial

/-!
# Strict concavity of the actual lower-angle circle support

The norm is differentiated from its defining radical.  The single
quintic proves the sign of the exact second derivative on the whole
angle interval.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.LowerSupport

open CommonQuarter CorePairGeometry Arithmetic

def R : ℝ := Real.sqrt Q0
def norm (x : ℝ) : ℝ := Real.sqrt (g^2+h^2-2*g*h*Real.sin x)
def value (x : ℝ) : ℝ :=
  Real.pi/2-x-P 0-V 0-R*norm x+h*Real.cos x+(g+h)/2
def first (x : ℝ) : ℝ := -1+R*g*h*Real.cos x/norm x-h*Real.sin x
def second (x : ℝ) : ℝ :=
  -h*Real.cos x-R*g*h*Real.sin x/norm x+
    R*g^2*h^2*(Real.cos x)^2/(norm x)^3

lemma R_data : 0<R ∧ R^2=Q0 ∧ R<4947/2500 := by
  have hp : 0<Q0 := by norm_num [Q0]
  have hpos := Real.sqrt_pos.mpr hp
  have hsq := Real.sq_sqrt hp.le
  exact ⟨hpos,hsq,by norm_num [Q0] at hsq; nlinarith⟩

lemma norm_data {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<norm x ∧ (norm x)^2=g^2+h^2-2*g*h*Real.sin x := by
  have hs := (positive_trig hx).2.2.2.1
  have hrad : 0<g^2+h^2-2*g*h*Real.sin x := by
    norm_num [g,h]
    linarith
  exact ⟨Real.sqrt_pos.mpr hrad,Real.sq_sqrt hrad.le⟩

lemma norm_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt norm (-(g*h*Real.cos x)/norm x) x := by
  have hd := norm_data hx
  have hrad : g^2+h^2-2*g*h*Real.sin x≠0 := by nlinarith [sq_pos_of_pos hd.1]
  convert (((Real.hasDerivAt_sin x).const_mul (2*g*h)).const_sub
    (g^2+h^2)).sqrt hrad using 1 <;> dsimp [norm] <;> ring

lemma value_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt value (first x) x := by
  have hn := norm_hasDerivAt hx
  convert (((((((hasDerivAt_id x).const_sub (Real.pi/2)).sub_const (P 0)).sub_const
    (V 0)).sub (hn.const_mul R)).add ((Real.hasDerivAt_cos x).const_mul h)).add_const
      ((g+h)/2)) using 1 <;> dsimp [value,first] <;> ring

lemma first_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt first (second x) x := by
  have hn := norm_data hx
  have hquot := ((Real.hasDerivAt_cos x).const_mul (R*g*h)).div
    (norm_hasDerivAt hx) hn.1.ne'
  convert ((hquot.const_add (-1)).sub ((Real.hasDerivAt_sin x).const_mul h)) using 1
  · dsimp [first]
    funext t
    ring
  · dsimp [second]
    field_simp [hn.1.ne']
    ring

lemma second_identity {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (second x+h*Real.cos x)*(norm x)^3=
      R*g*h*(g-h*Real.sin x)*(h-g*Real.sin x) := by
  have hn := norm_data hx
  have ht := Real.sin_sq_add_cos_sq x
  calc
    _= -R*g*h*Real.sin x*(norm x)^2+R*g^2*h^2*(Real.cos x)^2 := by
      dsimp [second]
      field_simp [hn.1.ne']
      ring
    _=R*g*h*(g-h*Real.sin x)*(h-g*Real.sin x) := by
      rw [hn.2]
      linear_combination R*g^2*h^2*ht

lemma squared_comparison {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (R*g*(g-h*Real.sin x)*(h-g*Real.sin x))^2<
      (Real.cos x*(norm x)^3)^2 := by
  have hn := norm_data hx
  have hcos : (Real.cos x)^2=1-(Real.sin x)^2 := by
    linarith [Real.sin_sq_add_cos_sq x]
  have hn6 : (norm x)^6=(g^2+h^2-2*g*h*Real.sin x)^3 := by
    calc
      (norm x)^6=((norm x)^2)^3 := by ring
      _=(g^2+h^2-2*g*h*Real.sin x)^3 := by rw [hn.2]
  have he : (Real.cos x*(norm x)^3)^2-
      (R*g*(g-h*Real.sin x)*(h-g*Real.sin x))^2=polynomial (Real.sin x) := by
    calc
      _=(Real.cos x)^2*(norm x)^6-
          R^2*g^2*(g-h*Real.sin x)^2*(h-g*Real.sin x)^2 := by ring
      _=polynomial (Real.sin x) := by rw [hcos,hn6,R_data.2.1]; rfl
  have hp := polynomial_positive
    (show Real.sin x∈Icc 0 (129/200) from
      ⟨(positive_trig hx).2.2.1,(positive_trig hx).2.2.2.1.le⟩)
  linarith

theorem second_negative {x : ℝ} (hx : x∈Icc 0 (7/10)) : second x<0 := by
  have hn := norm_data hx
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  have hs := (positive_trig hx).2.2.2.1
  have hp : 0<g-h*Real.sin x ∧ 0<h-g*Real.sin x := by
    norm_num [g,h]
    constructor <;> linarith
  have hleft : 0<R*g*(g-h*Real.sin x)*(h-g*Real.sin x) := by
    have hg : 0<g := by norm_num [g]
    exact mul_pos (mul_pos (mul_pos R_data.1 hg) hp.1) hp.2
  have hright : 0<Real.cos x*(norm x)^3 := mul_pos hc (pow_pos hn.1 3)
  have hcompare : R*g*(g-h*Real.sin x)*(h-g*Real.sin x)<Real.cos x*(norm x)^3 := by
    nlinarith [squared_comparison hx]
  have hmul := mul_lt_mul_of_pos_left hcompare (show 0<h by norm_num [h])
  have he := second_identity hx
  have hnorm := pow_pos hn.1 3
  nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.LowerSupport
