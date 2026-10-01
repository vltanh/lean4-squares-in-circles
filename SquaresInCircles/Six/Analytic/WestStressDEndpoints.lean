import SquaresInCircles.Six.Analytic.WestStressDConcavity

/-!
# The west stress along the secondary axis of D at the vertices

`westStressD` is positive at the seven vertices `(-2/3, -2/5)`, `(-2/5, -2/5)`,
`(-2/3, 0)`, `(0, 0)`, `(-2/3, 2/5)`, `(0, 2/5)` and `(2/5, 2/5)` of the parts
of its domain where `sin t` and `sin u` have fixed signs. There its radicals
are at most rational numbers, by squaring, and its sines and cosines are
bounded by Taylor polynomials at the rational angles `2/5`, `2/3`, `4/15` and
`16/15`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private lemma sqrt_upper {x q:ℝ} (hq:0≤q) (hx:x≤q^2) : Real.sqrt x≤q := by
  have h := Real.sqrt_le_sqrt hx
  rwa [Real.sqrt_sq hq] at h

private def D_vertex_expression (t u p q:ℝ) : ℝ :=
  17/20-(113/1000)*(3/10)+(3/10)*Real.cos u+(3/10)*max (-Real.sin u) 0+
    (3483/20000)*Real.cos t+(9/40)*|Real.sin t|-(1017/20000)*max (Real.sin t) 0+
    (1/4)*(Real.cos (u-t)+Real.sin (u-t))-(8443/5000)*(p+q)

private lemma D_lower_from_roots {t u p q:ℝ} (ht:-2/3≤t ∧ t≤2/5)
    (hp:Real.sqrt (53/200+(9/40)*Real.sin (u-t))≤p)
    (hq:Real.sqrt (61/400-(3/20)*Real.sin u)≤q) :
    D_vertex_expression t u p q≤westStressD t u := by
  have hc := westCentralSupport_upper ht
  have hRp := mul_le_mul west_radius_bound.le hp (Real.sqrt_nonneg _)
    (by norm_num : (0:ℝ)≤8443/5000)
  have hRq := mul_le_mul west_radius_bound.le hq (Real.sqrt_nonneg _)
    (by norm_num : (0:ℝ)≤8443/5000)
  dsimp [D_vertex_expression,westStressD]
  nlinarith

/-- Rational upper bounds for the two radicals at the vertices. -/
private lemma D_root_endpoints :
    Real.sqrt (53/200+(9/40)*Real.sin (4/15))≤57/100 ∧
    Real.sqrt (53/200:ℝ)≤103/200 ∧
    Real.sqrt (53/200+(9/40)*Real.sin (2/3))≤637/1000 ∧
    Real.sqrt (53/200+(9/40)*Real.sin (16/15))≤17/25 ∧
    Real.sqrt (53/200+(9/40)*Real.sin (2/5))≤297/500 ∧
    Real.sqrt (61/400-(3/20)*Real.sin (-2/5))≤23/50 ∧
    Real.sqrt (61/400:ℝ)≤391/1000 ∧
    Real.sqrt (61/400-(3/20)*Real.sin (2/5))≤307/1000 := by
  have s415 := Seven.sin_upper_five (x:=(4:ℝ)/15) (by norm_num)
  have s23 := Seven.sin_upper_five (x:=(2:ℝ)/3) (by norm_num)
  have s1615 := Seven.sin_upper_five (x:=(16:ℝ)/15) (by norm_num)
  have s25 := Seven.sin_upper_five (x:=(2:ℝ)/5) (by norm_num)
  have l25 := Seven.sin_lower_seven (x:=(2:ℝ)/5) (by norm_num)
  norm_num at s415 s23 s1615 s25 l25
  refine ⟨?_,west_root_bound,?_,?_,?_,?_,?_,?_⟩
  all_goals apply sqrt_upper (by norm_num)
  all_goals (norm_num <;> linarith)

private lemma D_minorant_endpoints :
    0<D_vertex_expression (-2/3) (-2/5) (57/100) (23/50) ∧
    0<D_vertex_expression (-2/5) (-2/5) (103/200) (23/50) ∧
    0<D_vertex_expression (-2/3) 0 (637/1000) (391/1000) ∧
    0<D_vertex_expression 0 0 (103/200) (391/1000) ∧
    0<D_vertex_expression (-2/3) (2/5) (17/25) (307/1000) ∧
    0<D_vertex_expression 0 (2/5) (297/500) (307/1000) ∧
    0<D_vertex_expression (2/5) (2/5) (103/200) (307/1000) := by
  have c23 := Seven.cos_lower_six (x:=(2:ℝ)/3) (by norm_num)
  have s23 := Seven.sin_lower_seven (x:=(2:ℝ)/3) (by norm_num)
  have c25 := Seven.cos_lower_six (x:=(2:ℝ)/5) (by norm_num)
  have s25 := Seven.sin_lower_seven (x:=(2:ℝ)/5) (by norm_num)
  have c415 := Seven.cos_lower_six (x:=(4:ℝ)/15) (by norm_num)
  have s415 := Seven.sin_lower_seven (x:=(4:ℝ)/15) (by norm_num)
  have c1615 := Seven.cos_lower_six (x:=(16:ℝ)/15) (by norm_num)
  have s1615 := Seven.sin_lower_seven (x:=(16:ℝ)/15) (by norm_num)
  norm_num at c23 s23 c25 s25 c415 s415 c1615 s1615
  have hs23 : 0≤Real.sin ((2:ℝ)/3) := by linarith
  have hs25 : 0≤Real.sin ((2:ℝ)/5) := by linarith
  have hn23 : -Real.sin ((2:ℝ)/3)≤0 := by linarith
  have hn25 : -Real.sin ((2:ℝ)/5)≤0 := by linarith
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals norm_num [D_vertex_expression,Real.cos_neg,Real.sin_neg,
    abs_neg,abs_of_nonneg hs23,abs_of_nonneg hs25,max_eq_right hn23,
    max_eq_right hn25,max_eq_left hs23,max_eq_left hs25]
  all_goals linarith

/-- `westStressD` is positive at the seven vertices. -/
theorem westStressD_vertices :
    0<westStressD (-2/3) (-2/5) ∧
    0<westStressD (-2/5) (-2/5) ∧
    0<westStressD (-2/3) 0 ∧
    0<westStressD 0 0 ∧
    0<westStressD (-2/3) (2/5) ∧
    0<westStressD 0 (2/5) ∧
    0<westStressD (2/5) (2/5) := by
  obtain ⟨w415,w0,w23,w1615,w25,dn,d0,dp⟩ := D_root_endpoints
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := D_minorant_endpoints
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact h0.trans_le (D_lower_from_roots (by norm_num)
      (by convert w415 using 1; norm_num) dn)
  · exact h1.trans_le (D_lower_from_roots (by norm_num)
      (by simpa using w0) dn)
  · exact h2.trans_le (D_lower_from_roots (by norm_num)
      (by convert w23 using 1; norm_num) (by simpa using d0))
  · exact h3.trans_le (D_lower_from_roots (by norm_num)
      (by simpa using w0) (by simpa using d0))
  · exact h4.trans_le (D_lower_from_roots (by norm_num)
      (by convert w1615 using 1; norm_num) dp)
  · exact h5.trans_le (D_lower_from_roots (by norm_num)
      (by simpa using w25) dp)
  · exact h6.trans_le (D_lower_from_roots (by norm_num)
      (by simpa using w0) dp)

end SquaresInCircles.Six.Analytic
