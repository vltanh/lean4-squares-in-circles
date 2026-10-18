module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Data
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Cover00
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Cover01
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Cover02

/-! # The affine table `Mismatch01To015Affine`

Each of its 92068 rows passes `checkRow`, so it satisfies its claim
(`checkRow_claim`). The walks `coverBlock` over blocks of sources covering all arcs
give the angle coverage (`coverBlocks_sound`). With the state chains and the
arctangent intervals of the arcs they give the charged bound. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
open Arithmetic

set_option maxRecDepth 100000

/-- All rows of the table. -/
noncomputable def rows : List AffineTableRow := data.map (·.toTableRow table ctx.den)

theorem complete_row_count : rows.length = 92068 := by
  simp only [rows, data, chunks, List.length_map, List.length_flatten, List.map_append,
    List.sum_append, parts000_length, parts001_length, parts002_length, parts003_length,
    parts004_length, parts005_length, parts006_length, parts007_length, parts008_length,
    parts009_length, Nat.reduceAdd]

theorem all_row_claims : ∀ r ∈ rows, r.Claim table := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact checkRow_claim ctx_valid (checkRows_sound data_check x hx)

theorem cover_endpoints : cover.EndpointsValid table := endpointsValid_atanEnds table _

theorem cover_blocks :
    AllBlocks (fun a n => ∃ c o, coverBlock coverCtx table a n c o chunks = true)
    [(0, 17), (17, 11), (28, 10), (38, 11), (49, 15), (64, 13), (77, 10), (87, 12), (99, 17),
     (116, 13), (129, 12), (141, 15), (156, 10), (166, 10), (176, 11), (187, 17), (204, 16),
     (220, 14), (234, 12), (246, 13), (259, 13), (272, 12), (284, 14), (298, 12), (310, 10),
     (320, 14), (334, 1)] :=
  by simp only [AllBlocks]; exact
    ⟨⟨0, 0, cover_0⟩, ⟨12, 24, cover_1⟩, ⟨27, 66, cover_2⟩, ⟨46, 172, cover_3⟩, ⟨66, 91, cover_4⟩,
    ⟨87, 165, cover_5⟩, ⟨107, 4, cover_6⟩, ⟨126, 199, cover_7⟩, ⟨145, 2, cover_8⟩,
    ⟨160, 195, cover_9⟩, ⟨177, 115, cover_10⟩, ⟨195, 32, cover_11⟩, ⟨212, 153, cover_12⟩,
    ⟨230, 131, cover_13⟩, ⟨247, 43, cover_14⟩, ⟨264, 28, cover_15⟩, ⟨278, 162, cover_16⟩,
    ⟨295, 106, cover_17⟩, ⟨311, 16, cover_18⟩, ⟨328, 99, cover_19⟩, ⟨346, 176, cover_20⟩,
    ⟨364, 175, cover_21⟩, ⟨384, 196, cover_22⟩, ⟨403, 33, cover_23⟩, ⟨422, 83, cover_24⟩,
    ⟨444, 12, cover_25⟩, ⟨459, 116, cover_26⟩, trivial⟩

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

end SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
