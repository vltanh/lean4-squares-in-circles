module

public import SquaresInCircles.Eight.Generated.Affine.TUpperAffine.Data
public import SquaresInCircles.Eight.Generated.Affine.TUpperAffine.Cover00

/-!
# Eight squares: the affine table `TUpperAffine`

Each of its 6433 rows passes `checkRow`, so it satisfies its claim
(`checkRow_claim`). The walks `coverBlock` over blocks of sources covering all arcs
give the angle coverage (`coverBlocks_sound`). With the state chains and the
arctangent intervals of the arcs they give the charged bound (`charged_bound`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.TUpperAffine
open Arithmetic

set_option maxRecDepth 100000

/-- All rows of the table. -/
noncomputable def rows : List AffineTableRow := data.map (·.toTableRow table ctx.den)

theorem all_row_claims : ∀ r ∈ rows, r.Claim table := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact checkRow_claim ctx_valid (checkRows_sound data_check x hx)

theorem cover_endpoints : cover.EndpointsValid table := endpointsValid_atanEnds table _

theorem cover_blocks :
    AllBlocks (fun a n => ∃ c o, coverBlock coverCtx table false a n c o chunks = true)
    [(0, 47), (47, 55)] :=
  by simp only [AllBlocks]; exact
    ⟨⟨0, 0, cover_0⟩, ⟨14, 159, cover_1⟩, trivial⟩

theorem cover_angles : cover.AngleCovers table rows false :=
  coverBlocks_sound coverCtx_valid.1 coverCtx_valid.2 (by decide +kernel) cover_blocks

theorem word_matches : ∀ i, (table.word i:ℝ)=(Candidate.word i:ℝ) := by
  have hw : table.word = ![0, 1, 0, 1, 0, 1, 1] := rfl
  intro i; rw [hw]; fin_cases i <;> norm_num [Candidate.word]

noncomputable def charged_bound (C : BoundaryCycle (table.radius:ℝ))
    (F : Candidate.Frame C) (β : ℝ)
    (hcharge : ∀ i, (table.charge i:ℝ)=Candidate.charge β i)
    (hcuts : ∀ i, (table.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (table.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈table.allowedAxes i) :
    Candidate.ChargedBound C F β (fun i => (table.target i:ℝ)) :=
  AffineCover.chargedBoundOf cover_endpoints cover_states cover_angles all_row_claims C F β
    word_matches hcharge hcuts hdiff haxes (by simp)

end SquaresInCircles.Eight.Generated.Affine.TUpperAffine
