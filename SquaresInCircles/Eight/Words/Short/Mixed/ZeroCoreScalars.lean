module

public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroCoreGeometry

/-!
# Eight squares: whole-interval lower bounds for the core-source negative contacts

The six continued circle contacts have strictly negative second
derivative. Their two endpoint values therefore suffice on the full
geometric interval. The competing diagonal branch is monotone, with
the direction determined by its original role coefficient. All bounds
below use rational endpoint and trigonometric estimates.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero.CoreContact

open CommonQuarter CorePairGeometry Arithmetic

def H (r : Row) (x : ℝ) : ℝ := -x+c r+g r*CoreAngleEndpoint.diagonal-
  p r*(U x-1/2)+q r*(V x-1/2)
def Hd (r : Row) (x : ℝ) : ℝ := -1+speed x*(p r*V x+q r*U x)
def Hdd (r : Row) (x : ℝ) : ℝ :=
  speedD x*(p r*V x+q r*U x)+(speed x)^2*(p r*U x-q r*V x)

lemma H_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 cap) :
    HasDerivAt (H r) (Hd r x) x := by
  have hh : HasDerivAt (fun y => -y+c r+g r*CoreAngleEndpoint.diagonal-
      p r*(U y-1/2)+q r*(V y-1/2))
      (-1-p r*(-V x*speed x)+q r*(U x*speed x)) x :=
    ((((hasDerivAt_id x).neg.add_const (c r)).add_const
      (g r*CoreAngleEndpoint.diagonal)).sub
        (((U_hasDerivAt hx).sub_const (1/2)).const_mul (p r))).add
          (((V_hasDerivAt hx).sub_const (1/2)).const_mul (q r))
  exact hh.congr_deriv (by dsimp [Hd]; ring)

lemma Hd_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 cap) :
    HasDerivAt (Hd r) (Hdd r x) x := by
  have hh : HasDerivAt (fun y => -1+speed y*(p r*V y+q r*U y))
      (speedD x*(p r*V x+q r*U x)+speed x*(p r*(U x*speed x)+q r*(-V x*speed x))) x :=
    ((speed_hasDerivAt hx).mul (((V_hasDerivAt hx).const_mul (p r)).add
      ((U_hasDerivAt hx).const_mul (q r)))).const_add (-1)
  exact hh.congr_deriv (by dsimp [Hdd]; ring)

lemma contact_coefficients (r : Row) {x : ℝ} (hx : x∈Icc 0 cap) :
    0<p r*V x+q r*U x ∧ p r*U x-q r*V x<0 := by
  have hc := coordinates hx
  fin_cases r <;> norm_num [p,q] <;>
    constructor <;> nlinarith [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

lemma Hdd_neg (r : Row) {x : ℝ} (hx : x∈Icc 0 cap) : Hdd r x<0 := by
  have hp := contact_coefficients r hx
  have h₁ := mul_neg_of_neg_of_pos (speedD_neg hx) hp.1
  have h₂ := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (speed x)) hp.2.le
  dsimp [Hdd]
  linarith

lemma H_concave (r : Row) : ConcaveOn ℝ (Icc 0 cap) (H r) :=
  concave_of_deriv2 (fun _ hx => H_hasDerivAt r hx)
    (fun _ hx => Hd_hasDerivAt r hx) (fun _ hx => (Hdd_neg r hx).le)

lemma H_endpoints (r : Row) : (449/500:ℝ)<H r 0 ∧ (449/500:ℝ)<H r cap := by
  have h0 := initial_coordinates
  have he := endpoint_coordinates
  have hd := CoreAngleEndpoint.diagonal_bounds
  have hcap : cap=8/25 := rfl
  constructor
  · rw [H,h0.2.2]
    fin_cases r <;> norm_num [c,p,q,g] <;>
      linarith only [h0.1,h0.2.1,hd.1,hd.2]
  · fin_cases r <;> norm_num [H,c,p,q,g] <;>
      linarith only [he.1,he.2.1,he.2.2.1,he.2.2.2,hd.1,hd.2,hcap]

theorem H_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 cap) : (449/500:ℝ)<H r x :=
  concave_gt_of_endpoints (H_concave r) hx (H_endpoints r).1 (H_endpoints r).2

def G (r : Row) (x : ℝ) : ℝ := -x+c r+(q r-p r)*outerDiagonal+
  g r*(1/2+(1/2+outerDiagonal)*Real.sin x+(1/2-outerDiagonal)*Real.cos x)
def Gd (r : Row) (x : ℝ) : ℝ := -1+
  g r*((1/2+outerDiagonal)*Real.cos x+(outerDiagonal-1/2)*Real.sin x)

lemma G_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (G r) (Gd r x) x := by
  have hh : HasDerivAt (fun y => -y+c r+(q r-p r)*outerDiagonal+
      g r*(1/2+(1/2+outerDiagonal)*Real.sin y+(1/2-outerDiagonal)*Real.cos y))
      (-1+g r*((1/2+outerDiagonal)*Real.cos x+(1/2-outerDiagonal)*(-Real.sin x))) x :=
    (((hasDerivAt_id x).neg.add_const (c r)).add_const
      ((q r-p r)*outerDiagonal)).add
        (((((Real.hasDerivAt_sin x).const_mul (1/2+outerDiagonal)).const_add (1/2)).add
          ((Real.hasDerivAt_cos x).const_mul (1/2-outerDiagonal))).const_mul (g r))
  exact hh.congr_deriv (by dsimp [Gd]; ring)

lemma diagonal_projection_upper (x : ℝ) :
    (1/2+outerDiagonal)*Real.cos x+(outerDiagonal-1/2)*Real.sin x<(73/50:ℝ) := by
  let v := (1/2+outerDiagonal)*Real.cos x+(outerDiagonal-1/2)*Real.sin x
  have he : v^2+((1/2+outerDiagonal)*Real.sin x-(outerDiagonal-1/2)*Real.cos x)^2=
      2*outerDiagonal^2+1/2 := by
    dsimp [v]
    linear_combination (2*outerDiagonal^2+1/2)*(Real.sin_sq_add_cos_sq x)
  have hd := outer_endpoint_bounds
  change v<(73/50:ℝ)
  nlinarith [hd.2.2.1,hd.2.2.2,
    sq_nonneg ((1/2+outerDiagonal)*Real.sin x-(outerDiagonal-1/2)*Real.cos x)]

lemma Gd_small_neg (r : Row) (hr : r=0 ∨ r=3) (x : ℝ) : Gd r x<0 := by
  have hh := mul_lt_mul_of_pos_left (diagonal_projection_upper x) (coefficient_bounds r).1
  rcases hr with rfl | rfl <;> norm_num [Gd,g] at hh ⊢ <;> linarith

lemma Gd_large_pos (r : Row) (h0 : r≠0) (h3 : r≠3)
    {x : ℝ} (hx : x∈Icc 0 cap) : 0<Gd r x := by
  have ht := trig_bounds hx
  have hd := fine_diagonal_bounds
  have hc := mul_le_mul_of_nonneg_left ht.2.2.1.le
    (show 0≤1/2+outerDiagonal by linarith [hd.1])
  have hs := mul_nonneg (show 0≤outerDiagonal-1/2 by linarith [hd.1]) ht.1
  have hv : (1:ℝ)<(1/2+outerDiagonal)*Real.cos x+(outerDiagonal-1/2)*Real.sin x := by
    nlinarith [hd.1]
  have hg : (1:ℝ)<g r := by
    fin_cases r
    · exact absurd rfl h0
    · norm_num [g]
    · norm_num [g]
    · exact absurd rfl h3
    · norm_num [g]
    · norm_num [g]
  have hh := mul_lt_mul_of_pos_left hv (coefficient_bounds r).1
  dsimp [Gd]
  linarith

lemma G_initial (r : Row) : (449/500:ℝ)<G r 0 := by
  have hd := fine_diagonal_bounds
  fin_cases r <;> norm_num [G,c,p,q,g] <;> linarith [hd.1,hd.2]

lemma G_small_terminal (r : Row) (hr : r=0 ∨ r=3) : (449/500:ℝ)<G r cap := by
  have ht := cap_trig
  have hd := fine_diagonal_bounds
  have hs := mul_le_mul_of_nonneg_left ht.1.le
    (show 0≤1/2+outerDiagonal by linarith [hd.1])
  have hc := mul_le_mul_of_nonpos_left ht.2.2.2.le
    (show 1/2-outerDiagonal≤0 by linarith [hd.1])
  have hcap : cap=8/25 := rfl
  rcases hr with rfl | rfl <;> norm_num [G,c,p,q,g] <;>
    linarith [hd.1,hd.2]

theorem G_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 cap) : (449/500:ℝ)<G r x := by
  by_cases hr : r=0 ∨ r=3
  · have hm : AntitoneOn (G r) (Icc 0 cap) :=
      antiOn_of_hasDeriv_nonpos (fun z _ => (G_hasDerivAt r z).continuousAt.continuousWithinAt)
        (fun z _ => G_hasDerivAt r z) (fun z _ => (Gd_small_neg r hr z).le)
    exact (G_small_terminal r hr).trans_le (hm hx (by norm_num [cap]) hx.2)
  · have hm : MonotoneOn (G r) (Icc 0 cap) :=
      monoOn_of_hasDeriv_nonneg (fun z _ => (G_hasDerivAt r z).continuousAt.continuousWithinAt)
        (fun z _ => G_hasDerivAt r z)
        (fun z hz => (Gd_large_pos r (fun h => hr (Or.inl h))
          (fun h => hr (Or.inr h)) (Ioo_subset_Icc_self hz)).le)
    exact (G_initial r).trans_le (hm (by norm_num [cap]) hx hx.1)

end SquaresInCircles.Eight.ShortMixedZero.CoreContact
