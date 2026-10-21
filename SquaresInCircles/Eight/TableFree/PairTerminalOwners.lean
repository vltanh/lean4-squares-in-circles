module

public import SquaresInCircles.Eight.TableFree.BoundaryPreprocessing

/-!
# Actual terminal owners, weak aligned ties, and the remaining diagonal

Uncompiled source. A nearest-axis diagonal with a nonpositive primary error
is excluded directly by the core and circle bounds. At an aligned negative
BT endpoint, either original TD owner gives the actual TD0 axis. The only
T terminal outside the secondary-E owner matrix is therefore the genuine
positive nearest-axis diagonal with BT3/TD2; it is kept explicit here.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate

private theorem nonpositive_sin_cos_sum {d : ℝ}
    (hd : |d|≤7/10) (hd0 : d≤0) : 1≤Real.cos d-Real.sin d := by
  have hx : -d∈Icc 0 (7/10 : ℝ) := by
    constructor <;> linarith [(abs_le.mp hd).1]
  have ht := transport_trig hx
  have hc : 0<Real.cos d := by simpa using (show 0<Real.cos (-d) by linarith [ht.1])
  have hs : Real.sin d≤0 := by simpa using neg_nonpos.mpr ht.2.2.1
  have hh := one_le_abs_cos_add_abs_sin d
  rw [abs_of_pos hc,abs_of_nonpos hs] at hh
  linarith

theorem nonpositive_GA_diagonal_false {q d : ℝ} {G A : SignedPoint}
    (hq : q≤qCap) (hGs : G.Sorted) (hGcore : G.AvoidsCore)
    (hAs : A.Sorted) (hAcore : A.AvoidsCore) (hAc : A.Contained q)
    (hd : |d|≤7/10) (hd0 : d≤0) (hdiag : G.y= -G.a)
    (hf : quarterFeasible G A d 1) : False := by
  have hGa := SignedPoint.primary_gt_half hGs hGcore
  have hAa := (SignedPoint.coordinate_bounds hAs hAcore hAc hq).2.1
  have hprod := mul_le_mul_of_nonneg_left (nonpositive_sin_cos_sum hd hd0) hGs.1.le
  have hp : edgeWidth d≤A.a-G.a*(Real.cos d-Real.sin d) := by
    simpa [quarterFeasible,quarterProjection,hdiag,mul_sub,sub_eq_add_neg,
      add_comm,add_left_comm,add_assoc] using hf
  linarith [edgeWidth_ge_one d]

theorem nonpositive_BT_diagonal_false {q d : ℝ} {B T : SignedPoint}
    (hq : q≤qCap) (hTs : T.Sorted) (hTcore : T.AvoidsCore)
    (hBs : B.Sorted) (hBcore : B.AvoidsCore) (hBc : B.Contained q)
    (hd : |d|≤7/10) (hd0 : d≤0) (hdiag : T.y=T.a)
    (hf : quarterFeasible B T d 3) : False := by
  have hTa := SignedPoint.primary_gt_half hTs hTcore
  have hBa := (SignedPoint.coordinate_bounds hBs hBcore hBc hq).2.1
  have hprod := mul_le_mul_of_nonneg_left (nonpositive_sin_cos_sum hd hd0) hTs.1.le
  have hp : edgeWidth d≤B.a-T.a*(Real.cos d-Real.sin d) := by
    simpa [quarterFeasible,quarterProjection,hdiag,mul_sub,sub_eq_add_neg,
      add_comm,add_left_comm,add_assoc] using hf
  linarith [edgeWidth_ge_one d]

namespace TPairOutput

/-- The actual aligned zero-owner tie reselects TD0 without changing any
point, frame, circle, or other separator. -/
theorem aligned_TD0 {q θB θT θD : ℝ} {B D : SignedPoint}
    (O : TPairOutput q B D θB θT θD) (ha : O.theta=θD) :
    zeroFeasible O.point D (θD-O.theta) 0 := by
  have hδ : θD-O.theta=0 := by rw [ha]; ring
  rw [hδ]
  have hf := O.TD
  rw [hδ] at hf
  rcases O.td_allowed with hj | hj
  · simpa [hj] using hf
  · exact (zero_owner_tie _ _).2 (by simpa [hj] using hf)

theorem secondary_E_owner_matrix {q θB θT θD : ℝ} {B D : SignedPoint}
    (O : TPairOutput q B D θB θT θD) (hq : q≤qCap)
    (hBs : B.Sorted) (hBcore : B.AvoidsCore) (hBc : B.Contained q)
    (hd : |O.theta-θB|≤7/10) :
    (∃ td : Fin 4, zeroFeasible O.point D (θD-O.theta) td ∧
      ((O.btOwner=2 ∧ td=0) ∨ (O.btOwner=2 ∧ td=2) ∨
       (O.btOwner=3 ∧ td=0 ∧ (O.theta-θB<0 → θD-O.theta=0)))) ∨
    (O.btOwner=3 ∧ O.tdOwner=2 ∧ O.point.y=O.point.a ∧ 0<O.theta-θB) := by
  by_cases hBT2 : O.btOwner=2
  · left
    refine ⟨O.tdOwner,O.TD,?_⟩
    rcases O.td_allowed with hj | hj
    · exact Or.inl ⟨hBT2,hj⟩
    · exact Or.inr (Or.inl ⟨hBT2,hj⟩)
  have hBT3 : O.btOwner=3 := by
    rcases O.bt_allowed with hj | hj
    · exact False.elim (hBT2 hj)
    · exact hj
  rcases O.terminal with hh | ⟨_,hTD0,hpos⟩ | ⟨_,halign,hneg,hy⟩ | hdiag
  · exact False.elim (hBT2 hh)
  · left
    refine ⟨0,by simpa [hTD0] using O.TD,Or.inr (Or.inr ⟨hBT3,rfl,?_⟩)⟩
    intro hneg
    linarith
  · left
    exact ⟨0,O.aligned_TD0 halign,
      Or.inr (Or.inr ⟨hBT3,rfl,fun _ => by rw [halign]; ring⟩)⟩
  · have hpositive : 0<O.theta-θB := by
      by_contra! hnonpos
      exact nonpositive_BT_diagonal_false hq O.sorted O.avoids hBs hBcore hBc
        hd hnonpos hdiag (by simpa [hBT3] using O.BT)
    rcases O.td_allowed with hTD0 | hTD2
    · left
      refine ⟨0,by simpa [hTD0] using O.TD,Or.inr (Or.inr ⟨hBT3,rfl,?_⟩)⟩
      intro hneg
      linarith
    · exact Or.inr ⟨hBT3,hTD2,hdiag,hpositive⟩

end TPairOutput
end SquaresInCircles.Eight.TableFree
