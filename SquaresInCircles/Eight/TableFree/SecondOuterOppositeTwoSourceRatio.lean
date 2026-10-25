module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoLabels

/-!
# The whole-circle source speed comparison

Convexity supplies one affine upper bound for the source derivative.
Two exact circle supports then pay the full angular displacement on
the original interval.  The argument has no source-coordinate cells.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma P_first_zero : PLabel.d1 0<387/500 := P_first_zero_bounds.2

lemma P_first_affine {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    PLabel.d1 b<387/500+(223/1000)*b := by
  have hh := positive_of_second_nonpos
    (f := fun t => 387/500+(223/1000)*t-PLabel.d1 t)
    (d := fun t => 223/1000-PLabel.d2 t)
    (dd := fun t => -PLabel.d3 t) hb
    (fun t ht => ((((hasDerivAt_id t).const_mul (223/1000)).const_add (387/500)).sub
        (PLabel.d1_hasDerivAt (outer_domain ht))).congr_deriv (by ring))
    (fun t ht => (PLabel.d2_hasDerivAt (outer_domain ht)).const_sub (223/1000))
    (fun t ht => neg_nonpos.mpr (P_third_positive ht).le)
    (by simpa using sub_pos.mpr P_first_zero)
    (by rw [P_first_diagonal]; linarith [fine_outer_endpoint_bounds.2])
  linarith

lemma sine_over_cosine {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    Real.sin x<(8423/10000)*Real.cos x := by
  have hs := sin_mono hx (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num) hx.2
  have hc := cos_anti hx (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num) hx.2
  have hf := ShortOuterOne.FiveSame.cap_fine
  linarith

lemma circle_support_8423 {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    U b+(8423/10000)*W b<647/250 := by
  have hc := UW_circle (outer_domain hb)
  have hs := sq_nonneg ((8423/10000)*U b-W b)
  have he : (U b+(8423/10000)*W b)^2+
      ((8423/10000)*U b-W b)^2=(1+(8423/10000:ℝ)^2)*Q0 := by
    linear_combination (1+(8423/10000:ℝ)^2)*hc
  norm_num [Q0] at he
  nlinarith [hs]

lemma circle_support_51 {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    U b+(51/100)*W b<223/100 := by
  have hc := UW_circle (outer_domain hb)
  have hs := sq_nonneg ((51/100)*U b-W b)
  have he : (U b+(51/100)*W b)^2+
      ((51/100)*U b-W b)^2=(1+(51/100:ℝ)^2)*Q0 := by
    linear_combination (1+(51/100:ℝ)^2)*hc
  norm_num [Q0] at he
  nlinarith [hs]

lemma source_derivative_mass {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    PLabel.d1 b*U b<767/500 := by
  have hu := U_positive (outer_domain hb)
  have hw : 0≤W b := by dsimp [W]; linarith [hb.1]
  have hP : PLabel.d1 b<53/80+(223/1000)*W b := by
    dsimp [W]
    linarith [P_first_affine hb]
  have hcoef : 0<53/80+(223/1000)*W b := by linarith
  have hleft := mul_lt_mul_of_pos_right hP hu
  have hright := mul_lt_mul_of_pos_left (circle_support_51 hb) hcoef
  have hsq := sq_nonneg (W b-31883/45492)
  nlinarith

lemma k_positive {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : 0<k b x := by
  have hh := mul_nonneg (by linarith [(outer_ratio_bounds hb).1] : 0≤ratio b)
    (positive_trig hx).2.2.1
  dsimp [k]
  linarith [(positive_trig hx).1]

lemma ratio_speed_identity {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (x : ℝ) :
    v b x=U b*k b x-Real.cos x := by
  have hu := U_positive (outer_domain hb)
  have he : U b*ratio b=W b := by
    change U b*(W b/U b)=W b
    field_simp [hu.ne']
  dsimp [v,k]
  linear_combination -Real.sin x*he

lemma source_ratio_paid {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : PLabel.d1 b*v b x<k b x := by
  have hu := U_positive (outer_domain hb)
  have hw : 0<W b := by dsimp [W]; linarith [hb.1]
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  have hk := k_positive hb hx
  have hp : 0<PLabel.d1 b := by linarith [(P_first_bounds hb).1]
  have hsin := mul_lt_mul_of_pos_left (sine_over_cosine hx) hw
  have hcircle := mul_lt_mul_of_pos_right (circle_support_8423 hb) hc
  have hU : U b*k b x=U b*Real.cos x+W b*Real.sin x := by
    have he := ratio_speed_identity hb x
    dsimp [v] at he
    linarith
  have hUk : U b*k b x<(647/250)*Real.cos x := by rw [hU]; nlinarith
  have hscaled : v b x<(307/500)*U b*k b x := by
    rw [ratio_speed_identity hb x]
    nlinarith [mul_pos hu hk]
  have hfirst := mul_lt_mul_of_pos_left hscaled hp
  have hsecond := mul_lt_mul_of_pos_right (source_derivative_mass hb) hk
  nlinarith

lemma source_ratio_quotient {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : PLabel.d1 b*(v b x/k b x)<1 := by
  rw [←mul_div_assoc]
  exact (div_lt_one (k_positive hb hx)).2 (source_ratio_paid hb hx)

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo
