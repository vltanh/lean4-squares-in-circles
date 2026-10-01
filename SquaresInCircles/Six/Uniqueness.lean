import SquaresInCircles.Six.Stress.StressBound
import SquaresInCircles.Six.Equality.Reflection
import SquaresInCircles.Common.Optimum

/-!
# Six squares: uniqueness

Proposition 10.17 and Theorem 10.1. A packing of six unit squares in the closed
disk of radius `radius` is normalized, possibly after a reflection in a diagonal:
one square contains the disk centre, the pins label the others, and the packing
is read in a frame of the central square. The stress bound turns the exterior
squares as in the model and gives the eight contacts, which fix every centre.
Squares with the same centre whose frames differ by a quarter turn are the same
square, so the normalized packing is the model with its labels permuted, and the
diagonal symmetry of the model absorbs the reflection.

The file ends with `optimum`: the case as an `Optimum`, which also gives the
lower bound.
-/

noncomputable section
namespace SquaresInCircles.Six
open Normalization Equality

/-- Two unit squares with the same centre whose frames differ by a multiple of a
quarter turn have the same interior. -/
lemma open_of_quarter_turn {S T : UnitSquare} (hc : T.center=S.center)
    (hf : (T.cosine=S.cosine ∧ T.sine=S.sine) ∨ (T.cosine=-S.sine ∧ T.sine=S.cosine) ∨
      (T.cosine=-S.cosine ∧ T.sine=-S.sine) ∨ (T.cosine=S.sine ∧ T.sine=-S.cosine))
    (p : Point) : openSquare T p ↔ openSquare S p := by
  rcases hf with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have ex : localX T p=localX S p := by simp only [localX,hc,h1,h2]
    have ey : localY T p=localY S p := by simp only [localY,hc,h1,h2]
    simp only [openSquare,ex,ey]
  · have ex : localX T p=localY S p := by simp only [localX,localY,hc,h1,h2]
    have ey : localY T p=-localX S p := by simp only [localX,localY,hc,h1,h2]; ring
    simp only [openSquare,ex,ey,abs_neg,and_comm]
  · have ex : localX T p=-localX S p := by simp only [localX,hc,h1,h2]; ring
    have ey : localY T p=-localY S p := by simp only [localY,hc,h1,h2]; ring
    simp only [openSquare,ex,ey,abs_neg]
  · have ex : localX T p=-localY S p := by simp only [localX,localY,hc,h1,h2]; ring
    have ey : localY T p=localX S p := by simp only [localX,localY,hc,h1,h2]; ring
    simp only [openSquare,ex,ey,abs_neg,and_comm]

/-- The order C, N, E, W, S, D of `model` against the order C, E, N, W, D, S of a
normalized packing. -/
def order : Equiv.Perm (Fin 6) where
  toFun := ![0,2,1,3,5,4]
  invFun := ![0,2,1,3,5,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private lemma cos_diagonal : Real.cos (5*Real.pi/4)=-hStar := by
  rw [show 5*Real.pi/4=Real.pi/4+Real.pi by ring,Real.cos_add_pi]
  simp [hStar]

private lemma sin_diagonal : Real.sin (5*Real.pi/4)=-hStar := by
  rw [show 5*Real.pi/4=Real.pi/4+Real.pi by ring,Real.sin_add_pi]
  simp [hStar]

/-- The squares at the phases and local coordinates of the model, about the
central square at `(sStar, sStar)`, are those of the model. -/
lemma model_congruent :
    Congruent (pinModel (sStar,sStar) modelPhase modelRadial modelTransverse) (0,0) model := by
  have hd : rhoStar*hStar=dStar := by
    rw [rhoStar_eq_two_h_d]
    linear_combination (2*dStar)*hStar_sq
  have ho (i : Fin 6) (p : Point) :
      openSquare (pinModel (sStar,sStar) modelPhase modelRadial modelTransverse (order i)) p ↔
        openSquare (model i) p := by
    fin_cases i
    · rfl
    · show openSquare (orientedSquare (Real.pi/2) (1+sStar) (-sStar)) p ↔
        openSquare (axisSquare (sStar,sStar+1)) p
      exact open_of_quarter_turn (by apply Prod.ext <;> simp [orientedSquare,axisSquare]; ring)
        (Or.inr (Or.inl (by simp [orientedSquare,axisSquare]))) p
    · show openSquare (orientedSquare 0 (1+sStar) sStar) p ↔
        openSquare (axisSquare (sStar+1,sStar)) p
      exact open_of_quarter_turn (by apply Prod.ext <;> simp [orientedSquare,axisSquare]; ring)
        (Or.inl (by simp [orientedSquare,axisSquare])) p
    · show openSquare (orientedSquare Real.pi (1-sStar) (-tStar)) p ↔
        openSquare (axisSquare (sStar-1,tStar)) p
      exact open_of_quarter_turn (by apply Prod.ext <;> simp [orientedSquare,axisSquare])
        (Or.inr (Or.inr (Or.inl (by simp [orientedSquare,axisSquare])))) p
    · show openSquare (orientedSquare (3*Real.pi/2) (1-sStar) tStar) p ↔
        openSquare (axisSquare (tStar,sStar-1)) p
      exact open_of_quarter_turn
        (by apply Prod.ext <;> simp [orientedSquare,axisSquare,south_cos,south_sin])
        (Or.inr (Or.inr (Or.inr (by simp [orientedSquare,axisSquare,south_cos,south_sin])))) p
    · show openSquare (orientedSquare (5*Real.pi/4) rhoStar 0) p ↔
        openSquare diagonalSquare p
      exact open_of_quarter_turn
        (by apply Prod.ext <;> simp [orientedSquare,diagonalSquare,cos_diagonal,sin_diagonal,hd])
        (Or.inr (Or.inr (Or.inl (by simp [orientedSquare,diagonalSquare,cos_diagonal,
          sin_diagonal])))) p
  exact congruent_of_origin_sets order ho (fun i => same_open_same_closed _ _ (ho i))

/-- Proposition 10.17: every packing of six unit squares in a closed disk of
radius `radius` is congruent to `model`. -/
theorem uniqueness (S : Fin 6 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : Congruent S o model := by
  obtain ⟨P,htrace⟩ := normalize hp radius_sq.le
  obtain ⟨hphase,hcontacts⟩ := Stress.stress_bound P
  obtain ⟨ha,hb,hc⟩ := model_of_contacts hcontacts (Stress.square_box P)
  have hmodel : P.model=pinModel (sStar,sStar) modelPhase modelRadial modelTransverse := by
    change pinModel P.center P.phase P.radial P.transverse=_
    rw [hphase,ha,hb,hc]
  exact congruent_of_reflection htrace (hmodel ▸ model_congruent)

/-- The corner `(sStar + 3/2, sStar + 1/2)` of the square to the right of the
central one lies on the circle of radius `radius`. -/
lemma model_reaches : ∃ (i : Fin 6) (p : Point),
    closedSquare (model i) p ∧ radius ^ 2 ≤ normSq p := by
  refine ⟨2,(sStar+3/2,sStar+1/2),(axisSquare_closed _ _).2 ?_,?_⟩
  · constructor <;> norm_num
  · dsimp [normSq]
    nlinarith [radius_sq,east_radius_identity]

/-- The optimum for six squares: `radius`, attained only by the configurations
congruent to `model`. -/
def optimum : Optimum 6 :=
  .ofUnique model model_packing model_reaches uniqueness

end SquaresInCircles.Six
