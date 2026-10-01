import SquaresInCircles.Six.Analytic.WestStressDEndpoints

/-!
# The west stress along the secondary axis of D is positive

`westStressD` is positive on the domain `-2/3 ≤ t ≤ u`, `-2/5 ≤ u ≤ 2/5`. On
each of its parts `t ≤ u ≤ 0`, `t ≤ 0 ≤ u` and `0 ≤ t ≤ u` it is concave in
`t`, so it is positive if it is on the edges `t = -2/3`, `t = 0` and `t = u`
that bound the part; it is concave in `u` along the first two edges and along
the diagonal, which reduces these edges to the seven vertices.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

private lemma D_far_negative {u:ℝ} (hu:-2/5≤u ∧ u≤0) :
    0<westDForm false false (-2/3) u := by
  have hf := westDForm_concave_u false false (-2/3) (-2/5) 0 westH_negative_concave
    (by intro x hx; constructor <;> linarith [hx.1,hx.2])
  apply positive_on_concave_interval hf hu
  · rw [westDForm_eq false false (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact westStressD_vertices.1
  · rw [westDForm_eq false false (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact westStressD_vertices.2.2.1

private lemma D_far_positive {u:ℝ} (hu:0≤u ∧ u≤2/5) :
    0<westDForm false true (-2/3) u := by
  have hf := westDForm_concave_u false true (-2/3) 0 (2/5) westH_positive_concave
    (by intro x hx; constructor <;> linarith [hx.1,hx.2])
  apply positive_on_concave_interval hf hu
  · rw [westDForm_eq false true (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact westStressD_vertices.2.2.1
  · rw [westDForm_eq false true (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact westStressD_vertices.2.2.2.2.1

private lemma D_zero_edge (pt:Bool) {u:ℝ} (hu:0≤u ∧ u≤2/5) :
    0<westDForm pt true 0 u := by
  have hf := westDForm_concave_u pt true 0 0 (2/5) westH_positive_concave
    (by intro x hx; constructor <;> linarith [hx.1,hx.2])
  apply positive_on_concave_interval hf hu
  · rw [westDForm_eq pt true (by norm_num) (by norm_num)
      (by cases pt <;> norm_num) (by norm_num)]
    exact westStressD_vertices.2.2.2.1
  · rw [westDForm_eq pt true (by norm_num) (by norm_num)
      (by cases pt <;> norm_num) (by norm_num)]
    exact westStressD_vertices.2.2.2.2.2.1

private lemma D_negative_diagonal {u:ℝ} (hu:-2/5≤u ∧ u≤0) :
    0<westDForm false false u u := by
  have hj : ConcaveOn ℝ (Set.Icc (-2/5) 0) (westJ false) :=
    westJ_negative_concave.subset
      (Set.Icc_subset_Icc (by norm_num) le_rfl) (convex_Icc _ _)
  have hf := westDForm_concave_diagonal false false (-2/5) 0 hj westH_negative_concave
  apply positive_on_concave_interval hf hu
  · rw [westDForm_eq false false (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact westStressD_vertices.2.1
  · rw [westDForm_eq false false (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact westStressD_vertices.2.2.2.1

private lemma D_positive_diagonal {u:ℝ} (hu:0≤u ∧ u≤2/5) :
    0<westDForm true true u u := by
  have hf := westDForm_concave_diagonal true true 0 (2/5)
    westJ_positive_concave westH_positive_concave
  apply positive_on_concave_interval hf hu
  · rw [westDForm_eq true true (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact westStressD_vertices.2.2.2.1
  · rw [westDForm_eq true true (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact westStressD_vertices.2.2.2.2.2.2

/-- `westStressD` is positive on the domain `-2/3 ≤ t ≤ u`, `-2/5 ≤ u ≤ 2/5`. -/
theorem westStressD_positive {t u:ℝ}
    (ht:-2/3≤t) (hu0:-2/5≤u) (hu1:u≤2/5) (htu:t≤u) : 0<westStressD t u := by
  by_cases huSign:u≤0
  · have hj : ConcaveOn ℝ (Set.Icc (-2/3) u) (westJ false) :=
      westJ_negative_concave.subset
        (Set.Icc_subset_Icc le_rfl huSign) (convex_Icc _ _)
    have hf := westDForm_concave_t false false u (-2/3) u hj
      (by intro x hx; constructor <;> linarith [hx.1,hx.2])
    have h := positive_on_concave_interval hf ⟨ht,htu⟩
      (D_far_negative ⟨hu0,huSign⟩) (D_negative_diagonal ⟨hu0,huSign⟩)
    rwa [westDForm_eq false false ⟨ht,by linarith⟩ ⟨hu0,hu1⟩
      (show t≤0 by linarith) huSign] at h
  · have huSign' : 0≤u := le_of_not_ge huSign
    by_cases htSign:t≤0
    · have hf := westDForm_concave_t false true u (-2/3) 0 westJ_negative_concave
        (by intro x hx; constructor <;> linarith [hx.1,hx.2])
      have h := positive_on_concave_interval hf ⟨ht,htSign⟩
        (D_far_positive ⟨huSign',hu1⟩) (D_zero_edge false ⟨huSign',hu1⟩)
      rwa [westDForm_eq false true ⟨ht,by linarith⟩ ⟨hu0,hu1⟩ htSign huSign'] at h
    · have htSign' : 0≤t := le_of_not_ge htSign
      have hj : ConcaveOn ℝ (Set.Icc 0 u) (westJ true) :=
        westJ_positive_concave.subset (Set.Icc_subset_Icc le_rfl hu1) (convex_Icc _ _)
      have hf := westDForm_concave_t true true u 0 u hj
        (by intro x hx; constructor <;> linarith [hx.1,hx.2])
      have h := positive_on_concave_interval hf ⟨htSign',htu⟩
        (D_zero_edge true ⟨huSign',hu1⟩) (D_positive_diagonal ⟨huSign',hu1⟩)
      rwa [westDForm_eq true true ⟨ht,by linarith⟩ ⟨hu0,hu1⟩ htSign' huSign'] at h

end SquaresInCircles.Six.Analytic
