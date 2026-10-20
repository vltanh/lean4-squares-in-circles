module

public import SquaresInCircles.Eight.TableFree.NecessaryCycle

/-!
# The signed necessary cycle is actual square geometry

Uncompiled draft. The coordinate identities apply to arbitrary signed
cycles, including transport descendants which are no longer boundary
records. No sign condition on either transverse coordinate is needed.

The wraparound quarter-word contributes a full turn, which is removed only
inside sine and cosine. Every scalar owner slack is exactly an actual signed
separating-axis slack of the displayed squares.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
namespace SignedCycle
open Candidate

def actualAngle (C : SignedCycle) (i : Vertex) : ℝ :=
  C.theta i+(Candidate.offsets i : ℝ)*Real.pi/2

theorem actualAngle_difference (C : SignedCycle) (i : Vertex) :
    C.actualAngle (next i)-C.actualAngle i =
      Candidate.phi C.theta i-(if i=6 then 2*Real.pi else 0) := by
  fin_cases i <;>
    simp [actualAngle,Candidate.phi,Candidate.word,Candidate.delta,
      Candidate.offsets,next] <;> ring

theorem actualSquare_relative_trig (C : SignedCycle) (i : Vertex) :
    relativeC (C.actualSquare i) (C.actualSquare (next i)) =
        Real.cos (Candidate.phi C.theta i) ∧
      relativeS (C.actualSquare i) (C.actualSquare (next i)) =
        Real.sin (Candidate.phi C.theta i) := by
  have hc : relativeC (C.actualSquare i) (C.actualSquare (next i)) =
      Real.cos (C.actualAngle (next i)-C.actualAngle i) := by
    simp [relativeC,actualSquare,SignedPoint.square,actualAngle,Real.cos_sub] <;> ring
  have hs : relativeS (C.actualSquare i) (C.actualSquare (next i)) =
      Real.sin (C.actualAngle (next i)-C.actualAngle i) := by
    simp [relativeS,actualSquare,SignedPoint.square,actualAngle,Real.sin_sub] <;> ring
  rw [actualAngle_difference] at hc hs
  by_cases hi : i=6
  · simpa [hi,Real.cos_sub,Real.sin_sub] using And.intro hc hs
  · simpa [hi] using And.intro hc hs

/-- Signed transverse coordinates are used as the actual local coordinates;
the auxiliary signs in `forwardMargin` can therefore both be one. -/
theorem actualSquare_margin (C : SignedCycle) (i : Vertex) (j : Fin 4) :
    (forwardAxis j).projection (C.actualSquare i) (C.actualSquare (next i)) -
      SAT.threshold (C.actualSquare i) (C.actualSquare (next i)) = C.slack i j := by
  obtain ⟨hc,hs⟩ := C.actualSquare_relative_trig i
  have hK : (C.actualSquare i).center =
      rotate (C.actualSquare i) ((C.point i).a,-1*(C.point i).y) := by
    simpa [actualSquare] using
      (C.point i).square_center (C.theta i+(Candidate.offsets i : ℝ)*Real.pi/2)
  have hL : (C.actualSquare (next i)).center =
      rotate (C.actualSquare (next i))
        ((C.point (next i)).a,-1*(C.point (next i)).y) := by
    simpa [actualSquare] using
      (C.point (next i)).square_center
        (C.theta (next i)+(Candidate.offsets (next i) : ℝ)*Real.pi/2)
  have h := canonical_margin_identity j (C.actualSquare i)
    (C.actualSquare (next i)) (C.point i).a (C.point i).y
    (C.point (next i)).a (C.point (next i)).y 1 1
    (Candidate.phi C.theta i) hK hL hc hs
  rw [h]
  fin_cases i <;> fin_cases j <;>
    simp [forwardMargin,Candidate.phi,Candidate.word,slack,edge,
      zeroProjection,quarterProjection,edgeWidth,pairWidth,
      Real.sin_add,Real.cos_add] <;> ring

theorem actualSquare_feasible (C : SignedCycle) (i : Vertex) (j : Fin 4) :
    (forwardAxis j).Feasible (C.actualSquare i) (C.actualSquare (next i)) ↔
      C.Feasible i j := by
  change SAT.threshold (C.actualSquare i) (C.actualSquare (next i)) ≤
      (forwardAxis j).projection (C.actualSquare i) (C.actualSquare (next i)) ↔
      0 ≤ C.slack i j
  rw [← actualSquare_margin]
  exact sub_nonneg.symm

theorem actualSquare_contained_iff (C : SignedCycle)
    (hs : ∀ i, (C.point i).Sorted) (q : ℝ) (i : Vertex) :
    SqContained q (C.actualSquare i) ↔ (C.point i).Contained q :=
  SignedPoint.square_contained_iff (hs i) q
    (C.theta i+(Candidate.offsets i : ℝ)*Real.pi/2)

theorem actualSquare_contained {q : ℝ} {C : SignedCycle}
    (hs : ∀ i, (C.point i).Sorted) (hc : ∀ i, (C.point i).Contained q)
    (i : Vertex) : SqContained q (C.actualSquare i) := by
  exact (SignedPoint.square_contained_iff (hs i) q
    (C.theta i+(Candidate.offsets i : ℝ)*Real.pi/2)).2 (hc i)

theorem actualSquare_points_contained {q : ℝ} {C : SignedCycle}
    (hs : ∀ i, (C.point i).Sorted) (hc : ∀ i, (C.point i).Contained q) :
    ∀ i p, closedSquare (C.actualSquare i) p → normSq p ≤ q := by
  have hq0 : 0 ≤ q := (C.point 0).circle_nonneg.trans (hc 0)
  exact fun i => (SqContained.iff_points hq0 _).1
    (actualSquare_contained hs hc i)

theorem actualSquare_frames_of_theta {C D : SignedCycle}
    (ht : C.theta=D.theta) (i : Vertex) :
    SameFrame (C.actualSquare i) (D.actualSquare i) := by
  constructor <;> simp [SameFrame,actualSquare,SignedPoint.square,ht]

end SignedCycle
end SquaresInCircles.Eight.TableFree
