module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.Data
public import SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.Cover00
public import SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.Cover01
public import SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.Cover02
public import SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.Cover03

/-! # The affine table `Mismatch026To01Affine`

Each of its 114806 rows passes `checkRow`, so it satisfies its claim
(`checkRow_claim`). The walks `coverBlock` over blocks of sources covering all arcs
give the angle coverage (`coverBlocks_sound`). With the state chains and the
arctangent intervals of the arcs they give the charged bound. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine
open Arithmetic

set_option maxRecDepth 100000

/-- All rows of the table. -/
noncomputable def rows : List AffineTableRow := data.map (·.toTableRow table ctx.den)

theorem complete_row_count : rows.length = 114806 := by
  simp only [rows, data, chunks, List.length_map, List.length_flatten, List.map_append,
    List.sum_append, parts000_length, parts001_length, parts002_length, parts003_length,
    parts004_length, parts005_length, parts006_length, parts007_length, parts008_length,
    parts009_length, parts010_length, parts011_length, Nat.reduceAdd]

theorem all_row_claims : ∀ r ∈ rows, r.Claim table := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact checkRow_claim ctx_valid (checkRows_sound data_check x hx)

theorem cover_endpoints : cover.EndpointsValid table := endpointsValid_atanEnds table _

theorem cover_blocks :
    AllBlocks (fun a n => ∃ c o, coverBlock coverCtx table a n c o chunks = true)
    [(0, 13), (13, 10), (23, 10), (33, 7), (40, 7), (47, 7), (54, 7), (61, 6), (67, 6), (73, 6),
     (79, 6), (85, 14), (99, 13), (112, 12), (124, 12), (136, 11), (147, 8), (155, 8), (163, 8),
     (171, 8), (179, 15), (194, 13), (207, 9), (216, 10), (226, 11), (237, 9), (246, 11),
     (257, 13), (270, 21), (291, 17), (308, 16), (324, 12), (336, 11), (347, 13), (360, 18),
     (378, 15), (393, 8)] :=
  by simp only [AllBlocks]; exact
    ⟨⟨0, 0, cover_0⟩, ⟨18, 136, cover_1⟩, ⟨38, 116, cover_2⟩, ⟨58, 104, cover_3⟩,
    ⟨78, 13, cover_4⟩, ⟨97, 105, cover_5⟩, ⟨116, 148, cover_6⟩, ⟨135, 14, cover_7⟩,
    ⟨153, 174, cover_8⟩, ⟨172, 74, cover_9⟩, ⟨190, 47, cover_10⟩, ⟨209, 84, cover_11⟩,
    ⟨218, 44, cover_12⟩, ⟨231, 186, cover_13⟩, ⟨232, 172, cover_14⟩, ⟨232, 172, cover_15⟩,
    ⟨234, 111, cover_16⟩, ⟨244, 40, cover_17⟩, ⟨255, 111, cover_18⟩, ⟨267, 145, cover_19⟩,
    ⟨281, 197, cover_20⟩, ⟨299, 108, cover_21⟩, ⟨315, 41, cover_22⟩, ⟨333, 153, cover_23⟩,
    ⟨351, 84, cover_24⟩, ⟨368, 102, cover_25⟩, ⟨384, 162, cover_26⟩, ⟨400, 26, cover_27⟩,
    ⟨412, 119, cover_28⟩, ⟨431, 132, cover_29⟩, ⟨451, 50, cover_30⟩, ⟨470, 198, cover_31⟩,
    ⟨490, 69, cover_32⟩, ⟨509, 143, cover_33⟩, ⟨529, 165, cover_34⟩, ⟨549, 59, cover_35⟩,
    ⟨569, 36, cover_36⟩, trivial⟩

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

end SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine
