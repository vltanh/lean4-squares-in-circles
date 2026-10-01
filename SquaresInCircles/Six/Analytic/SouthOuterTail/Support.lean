import SquaresInCircles.Six.Analytic.SouthOuterTail.CardinalEndpoints
import SquaresInCircles.Six.Analytic.SouthOuterTail.OwnEndpoints

/-!
# Supports in the south tail

Far-vertex bounds for the supports of S, W and D in the south tail. The
lengths of the forces are bounded by rational numbers, by the polynomial
majorant for W on the west side of C, and by `61/120 + sin (v + s)/5` for D,
each from its square. The centre of C enters linearly, and is replaced by an
end of its range, chosen by the sign of its coefficient.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.SouthOuterTail
open Normalization

def diagonalU (v s d : ℝ) : ℝ := mu*Real.sin (d+v)+nu*Real.cos (d-s)
def diagonalV (v s d : ℝ) : ℝ := mu*Real.cos (d+v)-nu*Real.sin (d-s)
def coreUpper : ℝ := 5641/50000

lemma width_lower (t : ℝ) : (Real.cos t+Real.sin t)/2 ≤ angularWidth t := by
  dsimp [angularWidth]
  linarith [le_abs_self (Real.cos t),le_abs_self (Real.sin t)]

lemma south_root_bound : Real.sqrt (1+nu^2) ≤ southRootUpper := by
  have hs := Real.sq_sqrt (show 0 ≤ (1:ℝ)+nu^2 by positivity)
  have hn := Real.sqrt_nonneg (1+nu^2)
  norm_num [nu,southRootUpper] at *
  nlinarith

lemma west_own_root_bound :
    Real.sqrt (Own.weightW^2+mu^2) ≤ Own.westRootUpper := by
  have hs := Real.sq_sqrt (show 0 ≤ Own.weightW^2+mu^2 by positivity)
  have hn := Real.sqrt_nonneg (Own.weightW^2+mu^2)
  norm_num [Own.weightW,mu,Own.westRootUpper] at *
  nlinarith

lemma south_support {a b : ℝ} (hc : ContainedChart a |b|) :
    a+nu*b ≤ CandidateWestTail.radiusBound*southRootUpper-(1+nu)/2 := by
  have h := CandidateWestTail.local_vertex_weak hc 1 nu
  have hp := mul_le_mul CandidateWestTail.ceiling_bounds.1 south_root_bound
    (Real.sqrt_nonneg _) (by norm_num [CandidateWestTail.radiusBound])
  norm_num only [one_pow,one_mul] at h
  nlinarith only [h,hp]

lemma west_own_support {a b : ℝ} (hc : ContainedChart a |b|) :
    Own.weightW*a-mu*b ≤
      CandidateWestTail.radiusBound*Own.westRootUpper-(Own.weightW+mu)/2 := by
  have h := CandidateWestTail.local_vertex_support hc Own.weightW (-mu)
  have hp := mul_le_mul CandidateWestTail.ceiling_bounds.1 west_own_root_bound
    (Real.sqrt_nonneg _) (by norm_num [CandidateWestTail.radiusBound])
  norm_num [Own.weightW,mu] at h hp ⊢
  nlinarith only [h,hp]

lemma west_cardinal_support {a b v : ℝ} (hc : ContainedChart a |b|)
    (hv : -(2/5) ≤ Real.sin v ∧ Real.sin v ≤ 2/5) :
    beta*Real.cos v*a+(beta*Real.sin v-mu)*b ≤
      CandidateWestTail.radiusBound*rootPolynomial (Real.sin v)-
        (beta*Real.cos v+mu-beta*Real.sin v)/2 := by
  have h := CandidateWestTail.local_vertex_support hc (beta*Real.cos v) (beta*Real.sin v-mu)
  have hn : (beta*Real.cos v)^2+(beta*Real.sin v-mu)^2=
      13/25-rootRate*Real.sin v := by
    dsimp [beta,mu,rootRate]
    linear_combination (9/25)*(Real.sin_sq_add_cos_sq v)
  rw [hn] at h
  have hp := mul_le_mul CandidateWestTail.ceiling_bounds.1 (root_upper hv)
    (Real.sqrt_nonneg _) (by norm_num [CandidateWestTail.radiusBound])
  have hw : beta*Real.cos v+mu-beta*Real.sin v ≤
      |beta*Real.cos v|+|beta*Real.sin v-mu| := by
    linarith [le_abs_self (beta*Real.cos v),neg_le_abs (beta*Real.sin v-mu)]
  nlinarith only [h,hp,hw]

lemma diagonal_norm (v s d : ℝ) :
    (diagonalU v s d)^2+(diagonalV v s d)^2=
      mu^2+nu^2+2*mu*nu*Real.sin (v+s) := by
  have ht : Real.sin (v+s)=Real.sin (d+v)*Real.cos (d-s)-
      Real.cos (d+v)*Real.sin (d-s) := by
    rw [← Real.sin_sub]
    congr 1
    ring
  dsimp [diagonalU,diagonalV]
  linear_combination mu^2*(Real.sin_sq_add_cos_sq (d+v))+
    nu^2*(Real.sin_sq_add_cos_sq (d-s))-2*mu*nu*ht

lemma diagonal_vertex_support {a b : ℝ} (hc : ContainedChart a |b|) (v s d : ℝ) :
    diagonalU v s d*a+diagonalV v s d*b ≤
      CandidateWestTail.radiusBound*(61/120+Real.sin (v+s)/5)-
        (diagonalU v s d+diagonalV v s d)/2 := by
  have h := CandidateWestTail.local_vertex_weak hc (diagonalU v s d) (diagonalV v s d)
  rw [diagonal_norm] at h
  have hr := Own.diagonal_root_upper (Real.sin (v+s))
    ⟨Real.neg_one_le_sin _,Real.sin_le_one _⟩
  have hp := mul_le_mul CandidateWestTail.ceiling_bounds.1 hr (Real.sqrt_nonneg _)
    (by norm_num [CandidateWestTail.radiusBound])
  nlinarith only [h,hp]

lemma center_face {fx fy cx cy : ℝ}
    (hx : 0 ≤ cx ∧ cx ≤ coreUpper) (hy : cy ≤ coreUpper) (hfy : 0 ≤ fy) :
    ∃ upper : Bool, fx*cx+fy*cy ≤ fx*face upper+fy*coreUpper := by
  have hY := mul_nonneg (sub_nonneg.mpr hy) hfy
  by_cases hfx : 0 ≤ fx
  · refine ⟨true,?_⟩
    have hX := mul_nonneg (sub_nonneg.mpr hx.2) hfx
    dsimp [face,coreUpper] at *
    nlinarith only [hX,hY]
  · refine ⟨false,?_⟩
    have hX := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hfx) hx.1
    dsimp [face] at *
    nlinarith only [hX,hY]

lemma south_cos_lower {s : ℝ} (hs : 11/25 ≤ s ∧ s ≤ 2/3) :
    7/9 ≤ Real.cos s := by
  have hsq := mul_nonneg (sub_nonneg.mpr hs.2)
    (show 0 ≤ 2/3+s by linarith [hs.1])
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := s)]

end SquaresInCircles.Six.Analytic.SouthOuterTail
