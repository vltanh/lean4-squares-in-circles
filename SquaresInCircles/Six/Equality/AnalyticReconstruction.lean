import SquaresInCircles.Six.Equality.AnalyticContacts
import SquaresInCircles.Six.Equality.Reflection

/-!
# Reconstruction independent of the legacy balanced-closure theorem

The only remaining geometric premise is the explicit ReductionHypotheses.
SelectedPairWork retains the actual sources; AnalyticContacts and the eight
contact calculation fix the signed coordinates and central center. This file
compares the resulting open/closed point sets with the unchanged candidate.

No fixed-row classifier, CommonDomain or pair certificate is imported here.
The theorem is conditional until the outstanding geometric reduction is supplied.
-/

noncomputable section
namespace SquaresInCircles.Six.Equality.AnalyticReconstruction
open Stress Normalization Analytic.FixedPair
open AnalyticContacts ContactCoordinates

private lemma cos_diagonal : Real.cos (5*Real.pi/4)= -Six.hStar := by
  rw [show 5*Real.pi/4=Real.pi/4+Real.pi by ring,Real.cos_add_pi]
  simp [Six.hStar]

private lemma sin_diagonal : Real.sin (5*Real.pi/4)= -Six.hStar := by
  rw [show 5*Real.pi/4=Real.pi/4+Real.pi by ring,Real.sin_add_pi]
  simp [Six.hStar]

private lemma rho_times_half : rhoStar*Six.hStar=Six.dStar := by
  rw [rhoStar_eq_two_h_d]
  linear_combination (2*Six.dStar)*Six.hStar_sq

private def centers : Fin 5 → Point :=
  ![(Six.sStar+1,Six.sStar),(Six.sStar,Six.sStar+1),(Six.sStar-1,Six.tStar),
    (-Six.dStar,-Six.dStar),(Six.tStar,Six.sStar-1)]

lemma exterior_centers {R : ℝ} (P : NormalizedPacking R)
    (hf : Frame P) (hc : Coordinates P.radial P.transverse) (i : Fin 5) :
    (P.square i).center=centers i := by
  fin_cases i
  · show (P.square 0).center=centers 0
    rw [P.square_def,hf.east,hc.east_radial,hc.east_transverse]
    apply Prod.ext <;> simp [orientedSquare,centers] <;> ring
  · show (P.square 1).center=centers 1
    rw [P.square_def,hf.north,hc.north_radial,hc.north_transverse]
    apply Prod.ext <;> simp [orientedSquare,centers] <;> ring
  · show (P.square 2).center=centers 2
    rw [P.square_def,hf.west,hc.west_radial,hc.west_transverse]
    apply Prod.ext <;> simp [orientedSquare,centers] <;> ring
  · show (P.square 3).center=centers 3
    rw [P.square_def,hf.diagonal,hc.diagonal_radial,hc.diagonal_transverse]
    apply Prod.ext <;>
      simp [orientedSquare,centers,cos_diagonal,sin_diagonal,rho_times_half]
  · show (P.square 4).center=centers 4
    rw [P.square_def,hf.south,hc.south_radial,hc.south_transverse]
    apply Prod.ext <;> simp [orientedSquare,centers,south_cos,south_sin] <;> ring

private lemma cardinal_open (S : UnitSquare)
    (h : (S.cosine=1 ∧ S.sine=0) ∨ (S.cosine=0 ∧ S.sine=1) ∨
      (S.cosine= -1 ∧ S.sine=0) ∨ (S.cosine=0 ∧ S.sine= -1)) (p : Point) :
    openSquare S p ↔ openSquare (axisSquare S.center) p := by
  rcases h with ⟨hc,hs⟩ | ⟨hc,hs⟩ | ⟨hc,hs⟩ | ⟨hc,hs⟩
  all_goals simp [openSquare,localX,localY,axisSquare,hc,hs,abs_sub_comm,and_comm]

private lemma opposite_open (S T : UnitSquare)
    (hc : S.center=T.center) (hcos : S.cosine= -T.cosine) (hsin : S.sine= -T.sine)
    (p : Point) : openSquare S p ↔ openSquare T p := by
  have hx : localX S p= -localX T p := by
    dsimp [localX]
    rw [hc,hcos,hsin]
    ring
  have hy : localY S p= -localY T p := by
    dsimp [localY]
    rw [hc,hcos,hsin]
    ring
  simp only [openSquare,hx,hy,abs_neg]

/-- Candidate order C,N,E,W,S,D versus normalized order C,E,N,W,D,S. -/
def order : Equiv.Perm (Fin 6) where
  toFun := ![0,2,1,3,5,4]
  invFun := ![0,2,1,3,5,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

lemma model_open {R : ℝ} (P : NormalizedPacking R)
    (hf : Frame P) (hc : Coordinates P.radial P.transverse)
    (hcenter : P.center=(Six.sStar,Six.sStar)) (i : Fin 6) (p : Point) :
    openSquare (P.model (order i)) p ↔ openSquare (Six.model i) p := by
  fin_cases i
  · change openSquare (axisSquare P.center) p ↔
      openSquare (axisSquare (Six.sStar,Six.sStar)) p
    rw [hcenter]
  · change openSquare (P.square 1) p ↔ openSquare (axisSquare (Six.sStar,Six.sStar+1)) p
    have hframe : (P.square 1).cosine=0 ∧ (P.square 1).sine=1 := by
      rw [P.square_def,hf.north]
      simp [orientedSquare]
    have ho := cardinal_open (P.square 1) (Or.inr (Or.inl hframe)) p
    rw [exterior_centers P hf hc 1] at ho
    exact ho
  · change openSquare (P.square 0) p ↔ openSquare (axisSquare (Six.sStar+1,Six.sStar)) p
    have hframe : (P.square 0).cosine=1 ∧ (P.square 0).sine=0 := by
      rw [P.square_def,hf.east]
      simp [orientedSquare]
    have ho := cardinal_open (P.square 0) (Or.inl hframe) p
    rw [exterior_centers P hf hc 0] at ho
    exact ho
  · change openSquare (P.square 2) p ↔ openSquare (axisSquare (Six.sStar-1,Six.tStar)) p
    have hframe : (P.square 2).cosine= -1 ∧ (P.square 2).sine=0 := by
      rw [P.square_def,hf.west]
      simp [orientedSquare]
    have ho := cardinal_open (P.square 2) (Or.inr (Or.inr (Or.inl hframe))) p
    rw [exterior_centers P hf hc 2] at ho
    exact ho
  · change openSquare (P.square 4) p ↔ openSquare (axisSquare (Six.tStar,Six.sStar-1)) p
    have hframe : (P.square 4).cosine=0 ∧ (P.square 4).sine= -1 := by
      rw [P.square_def,hf.south]
      simp [orientedSquare,south_cos,south_sin]
    have ho := cardinal_open (P.square 4) (Or.inr (Or.inr (Or.inr hframe))) p
    rw [exterior_centers P hf hc 4] at ho
    exact ho
  · change openSquare (P.square 3) p ↔ openSquare Six.diagonalSquare p
    apply opposite_open (P.square 3) Six.diagonalSquare
    · exact exterior_centers P hf hc 3
    · rw [P.square_def,hf.diagonal]
      simp [orientedSquare,Six.diagonalSquare,cos_diagonal]
    · rw [P.square_def,hf.diagonal]
      simp [orientedSquare,Six.diagonalSquare,sin_diagonal]

/-- Exact point-set reconstruction from the explicit analytic reduction. -/
theorem normalized_congruent_of_reduction {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2 ≤ Six.qStar) (h : ReductionHypotheses P) :
    Congruent P.model (0,0) Six.model := by
  obtain ⟨hf,hc,hcenter,_⟩ := coordinates_of_reduction P hR h
  have ho (i : Fin 6) (p : Point) :
      openSquare (P.model (order i)) p ↔ openSquare (Six.model i) p :=
    model_open P hf hc hcenter i p
  exact Six.congruent_of_origin_sets order ho
    (fun i => same_open_same_closed _ _ (ho i))

/-- Both orientation cases of the already-recorded normalization are discharged
using the candidate's actual diagonal symmetry. -/
theorem original_congruent_of_reduction {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (P : NormalizedPacking R) (hR : R^2 ≤ Six.qStar) (h : ReductionHypotheses P)
    (htrace : CongruentOrDiagonal S o P.model) : Congruent S o Six.model :=
  absorb_normalization_reflection htrace (normalized_congruent_of_reduction P hR h)

end SquaresInCircles.Six.Equality.AnalyticReconstruction
