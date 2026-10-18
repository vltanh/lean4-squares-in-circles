module

public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Data
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Cover00
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Cover01

/-! # The affine table `TLowerAffine`

Each of its 42178 rows passes `checkRow`, so it satisfies its claim
(`checkRow_claim`). The walks `coverBlock` over blocks of sources covering all arcs
give the angle coverage (`coverBlocks_sound`). With the state chains and the
arctangent intervals of the arcs they give the charged bound. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.TLowerAffine
open Arithmetic

set_option maxRecDepth 100000

/-- All rows of the table. -/
noncomputable def rows : List AffineTableRow := data.map (·.toTableRow table ctx.den)

theorem complete_row_count : rows.length = 42178 := by
  simp only [rows, data, chunks, List.length_map, List.length_flatten, List.map_append,
    List.sum_append, parts000_length, parts001_length, parts002_length, parts003_length,
    parts004_length, Nat.reduceAdd]

theorem all_row_claims : ∀ r ∈ rows, r.Claim table := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact checkRow_claim ctx_valid (checkRows_sound data_check x hx)

theorem cover_endpoints : cover.EndpointsValid table := endpointsValid_atanEnds table _

theorem cover_blocks :
    AllBlocks (fun a n => ∃ c o, coverBlock coverCtx table a n c o chunks = true)
    [(0, 45), (45, 18), (63, 10), (73, 22), (95, 19), (114, 14), (128, 16), (144, 23), (167, 23),
     (190, 24), (214, 21), (235, 23), (258, 21), (279, 11), (290, 10), (300, 3)] :=
  by simp only [AllBlocks]; exact
    ⟨⟨0, 0, cover_0⟩, ⟨12, 58, cover_1⟩, ⟨30, 155, cover_2⟩, ⟨48, 5, cover_3⟩, ⟨60, 122, cover_4⟩,
    ⟨70, 140, cover_5⟩, ⟨81, 186, cover_6⟩, ⟨100, 22, cover_7⟩, ⟨113, 133, cover_8⟩,
    ⟨126, 77, cover_9⟩, ⟨132, 43, cover_10⟩, ⟨145, 161, cover_11⟩, ⟨160, 100, cover_12⟩,
    ⟨172, 195, cover_13⟩, ⟨189, 133, cover_14⟩, ⟨206, 21, cover_15⟩, trivial⟩

theorem cover_angles : cover.AngleCovers table rows :=
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
    word_matches hcharge hcuts hdiff haxes

end SquaresInCircles.Eight.Generated.Affine.TLowerAffine
