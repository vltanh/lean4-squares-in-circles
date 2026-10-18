module

public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Data
public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Cover00
public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Cover01

/-! # The affine table `HLowerAffine`

Each of its 40296 rows passes `checkRow`, so it satisfies its claim
(`checkRow_claim`). The walks `coverBlock` over blocks of sources covering all arcs
give the angle coverage (`coverBlocks_sound`). With the state chains and the
arctangent intervals of the arcs they give the charged bound. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.HLowerAffine
open Arithmetic

set_option maxRecDepth 100000

/-- All rows of the table. -/
noncomputable def rows : List AffineTableRow := data.map (·.toTableRow table ctx.den)

theorem complete_row_count : rows.length = 40296 := by
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
    [(0, 42), (42, 11), (53, 14), (67, 23), (90, 17), (107, 13), (120, 32), (152, 25), (177, 15),
     (192, 19), (211, 23), (234, 22), (256, 14), (270, 9)] :=
  by simp only [AllBlocks]; exact
    ⟨⟨0, 0, cover_0⟩, ⟨11, 68, cover_1⟩, ⟨28, 1, cover_2⟩, ⟨44, 166, cover_3⟩, ⟨57, 52, cover_4⟩,
    ⟨63, 88, cover_5⟩, ⟨79, 62, cover_6⟩, ⟨97, 105, cover_7⟩, ⟨114, 41, cover_8⟩,
    ⟨128, 58, cover_9⟩, ⟨145, 56, cover_10⟩, ⟨159, 192, cover_11⟩, ⟨171, 158, cover_12⟩,
    ⟨189, 53, cover_13⟩, trivial⟩

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

end SquaresInCircles.Eight.Generated.Affine.HLowerAffine
