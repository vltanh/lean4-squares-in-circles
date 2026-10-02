module

public import SquaresInCircles.Six.Stress.StressBound
public import SquaresInCircles.Six.Equality.Reflection
public import SquaresInCircles.Common.Optimum

/-!
# Six squares: uniqueness

A packing of six unit squares in the closed
disk of radius `radius` is normalized, possibly after a reflection in a diagonal:
one square contains the disk centre, the pins label the others, and the packing
is read in a frame of the central square. The stress bound turns the exterior
squares as in the model and gives the eight contacts, which fix every centre.
Squares with the same centre and the same axes are the same square
(`same_axes_open`), so the normalized packing is the model with its labels
permuted, and the diagonal symmetry of the model absorbs the reflection.

The file ends with `optimum`: the case as an `Optimum`, which also gives the
lower bound.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Six
open Normalization Equality

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
      exact same_axes_open (by apply Prod.ext <;> simp [orientedSquare,axisSquare]; ring)
        (Or.inl (by simp [relativeC,orientedSquare,axisSquare])) p
    · show openSquare (orientedSquare 0 (1+sStar) sStar) p ↔
        openSquare (axisSquare (sStar+1,sStar)) p
      exact same_axes_open (by apply Prod.ext <;> simp [orientedSquare,axisSquare]; ring)
        (Or.inr (by simp [relativeS,orientedSquare,axisSquare])) p
    · show openSquare (orientedSquare Real.pi (1-sStar) (-tStar)) p ↔
        openSquare (axisSquare (sStar-1,tStar)) p
      exact same_axes_open (by apply Prod.ext <;> simp [orientedSquare,axisSquare])
        (Or.inr (by simp [relativeS,orientedSquare,axisSquare])) p
    · show openSquare (orientedSquare (3*Real.pi/2) (1-sStar) tStar) p ↔
        openSquare (axisSquare (tStar,sStar-1)) p
      exact same_axes_open
        (by apply Prod.ext <;> simp [orientedSquare,axisSquare,south_cos,south_sin])
        (Or.inl (by simp [relativeC,orientedSquare,axisSquare,south_cos])) p
    · show openSquare (orientedSquare (5*Real.pi/4) rhoStar 0) p ↔
        openSquare diagonalSquare p
      exact same_axes_open
        (by apply Prod.ext <;> simp [orientedSquare,diagonalSquare,cos_diagonal,sin_diagonal,hd])
        (Or.inr (by simp [relativeS,orientedSquare,diagonalSquare,cos_diagonal,sin_diagonal])) p
  exact congruent_of_origin_sets order ho (fun i => same_open_same_closed _ _ (ho i))

/-- Every packing of six unit squares in a closed disk of radius `radius` is
congruent to `model`. -/
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
