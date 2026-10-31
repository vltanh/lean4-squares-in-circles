module

public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Data
public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Cover00
public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Cover01

/-!
# Eight squares: the affine table `HLowerAffine`

Each of its 35666 rows passes `checkRow`, so it satisfies its claim
(`checkRow_claim`). The walks `coverBlock` over blocks of sources covering all arcs
give the angle coverage (`coverBlocks_sound`). With the state chains and the
arctangent intervals of the arcs they give the charged bound (`charged_bound`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.HLowerAffine
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
    AllBlocks (fun a n => ∃ c o, coverBlock coverCtx table true a n c o chunks = true)
    [(0, 44), (44, 12), (56, 23), (79, 21), (100, 13), (113, 31), (144, 26), (170, 20), (190, 27),
     (217, 22), (239, 25), (264, 14), (278, 1)] :=
  by simp only [AllBlocks]; exact
    ⟨⟨0, 0, cover_0⟩, ⟨12, 11, cover_1⟩, ⟨29, 2, cover_2⟩, ⟨42, 129, cover_3⟩, ⟨51, 77, cover_4⟩,
    ⟨62, 113, cover_5⟩, ⟨80, 34, cover_6⟩, ⟨98, 95, cover_7⟩, ⟨112, 91, cover_8⟩,
    ⟨127, 171, cover_9⟩, ⟨145, 50, cover_10⟩, ⟨158, 82, cover_11⟩, ⟨177, 11, cover_12⟩, trivial⟩

theorem cover_angles : cover.AngleCovers table rows true :=
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
      ForwardAxis.ofIndex j∈table.allowedAxes i)
    (hC : NoAdjacentCore C) :
    Candidate.ChargedBound C F β (fun i => (table.target i:ℝ)) :=
  AffineCover.chargedBoundOf cover_endpoints cover_states cover_angles all_row_claims C F β
    word_matches hcharge hcuts hdiff haxes (fun _ => hC.corePairBound F)

end SquaresInCircles.Eight.Generated.Affine.HLowerAffine
