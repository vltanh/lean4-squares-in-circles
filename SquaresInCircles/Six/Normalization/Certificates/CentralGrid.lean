import SquaresInCircles.Six.Normalization.Certificates.ConeSemantics

/-!
# Exact central staircase and forbidden-arc lengths

Closed boxes cover the entire ordered central region, including shared edges.
The choice of the first containing interval proves j<=i when cy<=cx; no point
is lost to floating-point rounding or an unchecked cover inventory.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization.Certificates

@[simp] lemma gridEdge_zero : gridEdge 0 = c0 := by simp [gridEdge]
@[simp] lemma gridEdge_eight : gridEdge 8 = 1/2 := by dsimp [gridEdge]; ring

lemma gridEdge_mono {i j : ℕ} (hij : i ≤ j) : gridEdge i ≤ gridEdge j := by
  have hc : 0 ≤ 1/2-c0 := by linarith [c0_lt_23_200]
  have hn : (i:ℝ) ≤ j := by exact_mod_cast hij
  have hp := mul_nonneg hc (sub_nonneg.mpr hn)
  dsimp [gridEdge]
  nlinarith

lemma grid_cell_exists {z : ℝ} (hz : c0 ≤ z ∧ z ≤ 1/2) :
    ∃ i : Fin 8, gridEdge i.val ≤ z ∧ z ≤ gridEdge (i.val+1) ∧
      (i=0 ∨ gridEdge i.val < z) := by
  by_cases h1 : z ≤ gridEdge 1
  · exact ⟨0,by simpa using hz.1,h1,Or.inl rfl⟩
  by_cases h2 : z ≤ gridEdge 2
  · exact ⟨1,(lt_of_not_ge h1).le,h2,Or.inr (lt_of_not_ge h1)⟩
  by_cases h3 : z ≤ gridEdge 3
  · exact ⟨2,(lt_of_not_ge h2).le,h3,Or.inr (lt_of_not_ge h2)⟩
  by_cases h4 : z ≤ gridEdge 4
  · exact ⟨3,(lt_of_not_ge h3).le,h4,Or.inr (lt_of_not_ge h3)⟩
  by_cases h5 : z ≤ gridEdge 5
  · exact ⟨4,(lt_of_not_ge h4).le,h5,Or.inr (lt_of_not_ge h4)⟩
  by_cases h6 : z ≤ gridEdge 6
  · exact ⟨5,(lt_of_not_ge h5).le,h6,Or.inr (lt_of_not_ge h5)⟩
  by_cases h7 : z ≤ gridEdge 7
  · exact ⟨6,(lt_of_not_ge h6).le,h7,Or.inr (lt_of_not_ge h6)⟩
  exact ⟨7,(lt_of_not_ge h7).le,by simpa using hz.2,Or.inr (lt_of_not_ge h7)⟩

/-- All ordered bad-core centers lie in one of the 36 checked boxes. -/
theorem triangular_grid_cover {cx cy : ℝ}
    (hx : c0 ≤ cx ∧ cx ≤ 1/2) (hy : c0 ≤ cy ∧ cy ≤ cx) :
    ∃ i j : Fin 8, j ≤ i ∧
      (gridEdge i.val ≤ cx ∧ cx ≤ gridEdge (i.val+1)) ∧
      (gridEdge j.val ≤ cy ∧ cy ≤ gridEdge (j.val+1)) := by
  obtain ⟨i,hix0,hix1,hixs⟩ := grid_cell_exists hx
  obtain ⟨j,hjy0,hjy1,hjys⟩ := grid_cell_exists ⟨hy.1,hy.2.trans hx.2⟩
  have hji : j ≤ i := by
    by_contra! hij
    have hn : i.val+1 ≤ j.val := by omega
    have hg := gridEdge_mono hn
    rcases hjys with hj0 | hjstrict
    · subst j
      omega
    · linarith [hy.2]
  exact ⟨i,j,hji,⟨hix0,hix1⟩,⟨hjy0,hjy1⟩⟩

lemma first_arc_long : 2*Real.pi/3 < (61:ℝ)/50-(-99/100) := by
  linarith [Real.pi_lt_d2]

lemma second_arc_long : 2*Real.pi/3 < (39:ℝ)/25-(-27/50) := by
  linarith [Real.pi_lt_d2]

lemma first_arc_near_east : (99:ℝ)/100 < Real.pi/2 ∧ (61:ℝ)/50 < Real.pi/2 := by
  constructor <;> linarith [Real.pi_gt_d2]

lemma second_arc_near_east : (27:ℝ)/50 < Real.pi/2 ∧ (39:ℝ)/25 < Real.pi/2 := by
  constructor <;> linarith [Real.pi_gt_d2]

end SquaresInCircles.Six.Normalization.Certificates
