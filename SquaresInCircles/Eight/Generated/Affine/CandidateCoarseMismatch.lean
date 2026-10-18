module

public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Data
public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Cover00
public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Cover01
public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Cover02
public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Cover03

/-! # The affine table `CandidateCoarseMismatch`

Each of its 115463 rows passes `checkRow`, so it satisfies its claim
(`checkRow_claim`). The walks `coverBlock` over blocks of sources covering all arcs
give the angle coverage (`coverBlocks_sound`). With the state chains and the
arctangent intervals of the arcs they give the charged bound. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
open Arithmetic

set_option maxRecDepth 100000

/-- All rows of the table. -/
noncomputable def rows : List AffineTableRow := data.map (·.toTableRow table ctx.den)

theorem complete_row_count : rows.length = 115463 := by
  simp only [rows, data, chunks, List.length_map, List.length_flatten, List.map_append,
    List.sum_append, parts000_length, parts001_length, parts002_length, parts003_length,
    parts004_length, parts005_length, parts006_length, parts007_length, parts008_length,
    parts009_length, parts010_length, parts011_length, Nat.reduceAdd]

theorem all_row_claims : ∀ r ∈ rows, r.Claim table := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact AffineRow.claim_of_target_le (le_add_of_nonneg_right (enhancement_nonneg _))
    (checkRow_claim ctx_valid (checkRows_sound data_check x hx))

theorem cover_endpoints : cover.EndpointsValid table := endpointsValid_atanEnds table _

theorem cover_blocks :
    AllBlocks (fun a n => ∃ c o, coverBlock coverCtx table a n c o chunks = true)
    [(0, 27), (27, 29), (56, 18), (74, 14), (88, 7), (95, 6), (101, 6), (107, 6), (113, 6),
     (119, 15), (134, 11), (145, 10), (155, 11), (166, 12), (178, 8), (186, 8), (194, 7), (201, 6),
     (207, 17), (224, 17), (241, 17), (258, 16), (274, 16), (290, 14), (304, 8), (312, 8),
     (320, 7), (327, 10), (337, 15), (352, 14), (366, 12), (378, 12), (390, 17), (407, 14),
     (421, 7), (428, 6), (434, 6), (440, 6), (446, 6), (452, 6), (458, 4)] :=
  by simp only [AllBlocks]; exact
    ⟨⟨0, 0, cover_0⟩, ⟨14, 32, cover_1⟩, ⟨19, 152, cover_2⟩, ⟨36, 12, cover_3⟩, ⟨54, 38, cover_4⟩,
    ⟨70, 157, cover_5⟩, ⟨87, 143, cover_6⟩, ⟨104, 159, cover_7⟩, ⟨120, 179, cover_8⟩,
    ⟨137, 39, cover_9⟩, ⟨146, 58, cover_10⟩, ⟨162, 89, cover_11⟩, ⟨169, 163, cover_12⟩,
    ⟨173, 185, cover_13⟩, ⟨176, 18, cover_14⟩, ⟨186, 90, cover_15⟩, ⟨199, 166, cover_16⟩,
    ⟨214, 103, cover_17⟩, ⟨229, 46, cover_18⟩, ⟨246, 170, cover_19⟩, ⟨265, 157, cover_20⟩,
    ⟨282, 185, cover_21⟩, ⟨301, 9, cover_22⟩, ⟨318, 124, cover_23⟩, ⟨333, 51, cover_24⟩,
    ⟨343, 153, cover_25⟩, ⟨356, 160, cover_26⟩, ⟨370, 132, cover_27⟩, ⟨387, 32, cover_28⟩,
    ⟨399, 175, cover_29⟩, ⟨415, 95, cover_30⟩, ⟨434, 35, cover_31⟩, ⟨452, 64, cover_32⟩,
    ⟨460, 124, cover_33⟩, ⟨469, 147, cover_34⟩, ⟨485, 196, cover_35⟩, ⟨502, 73, cover_36⟩,
    ⟨518, 74, cover_37⟩, ⟨535, 130, cover_38⟩, ⟨551, 123, cover_39⟩, ⟨567, 64, cover_40⟩, trivial⟩

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

end SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
