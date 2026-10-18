module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Data
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Cover00
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Cover01
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Cover02

/-! # The affine table `Mismatch015To001Affine`

Each of its 135810 rows passes `checkRow`, so it satisfies its claim
(`checkRow_claim`). The walks `coverBlock` over blocks of sources covering all arcs
give the angle coverage (`coverBlocks_sound`). With the state chains and the
arctangent intervals of the arcs they give the charged bound. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
open Arithmetic

set_option maxRecDepth 100000

/-- All rows of the table. -/
noncomputable def rows : List AffineTableRow := data.map (·.toTableRow table ctx.den)

theorem complete_row_count : rows.length = 135810 := by
  simp only [rows, data, chunks, List.length_map, List.length_flatten, List.map_append,
    List.sum_append, parts000_length, parts001_length, parts002_length, parts003_length,
    parts004_length, parts005_length, parts006_length, parts007_length, parts008_length,
    parts009_length, parts010_length, parts011_length, parts012_length, parts013_length,
    Nat.reduceAdd]

theorem all_row_claims : ∀ r ∈ rows, r.Claim table := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact checkRow_claim ctx_valid (checkRows_sound data_check x hx)

theorem cover_endpoints : cover.EndpointsValid table := endpointsValid_atanEnds table _

theorem cover_blocks :
    AllBlocks (fun a n => ∃ c o, coverBlock coverCtx table a n c o chunks = true)
    [(0, 13), (13, 11), (24, 11), (35, 11), (46, 10), (56, 10), (66, 10), (76, 10), (86, 9),
     (95, 7), (102, 7), (109, 7), (116, 7), (123, 8), (131, 13), (144, 19), (163, 18), (181, 17),
     (198, 18), (216, 12), (228, 12), (240, 12), (252, 18), (270, 20), (290, 21), (311, 21),
     (332, 19), (351, 16), (367, 16), (383, 16), (399, 13), (412, 8), (420, 8), (428, 8),
     (436, 10), (446, 10)] :=
  by simp only [AllBlocks]; exact
    ⟨⟨0, 0, cover_0⟩, ⟨16, 164, cover_1⟩, ⟨36, 41, cover_2⟩, ⟨55, 114, cover_3⟩,
    ⟨74, 192, cover_4⟩, ⟨95, 111, cover_5⟩, ⟨117, 2, cover_6⟩, ⟨138, 116, cover_7⟩,
    ⟨158, 151, cover_8⟩, ⟨176, 18, cover_9⟩, ⟨196, 67, cover_10⟩, ⟨217, 122, cover_11⟩,
    ⟨238, 170, cover_12⟩, ⟨258, 47, cover_13⟩, ⟨278, 60, cover_14⟩, ⟨294, 65, cover_15⟩,
    ⟨309, 183, cover_16⟩, ⟨327, 170, cover_17⟩, ⟨346, 135, cover_18⟩, ⟨363, 33, cover_19⟩,
    ⟨381, 189, cover_20⟩, ⟨400, 103, cover_21⟩, ⟨418, 199, cover_22⟩, ⟨434, 89, cover_23⟩,
    ⟨453, 191, cover_24⟩, ⟨473, 25, cover_25⟩, ⟨491, 94, cover_26⟩, ⟨510, 58, cover_27⟩,
    ⟨529, 54, cover_28⟩, ⟨548, 136, cover_29⟩, ⟨567, 60, cover_30⟩, ⟨583, 46, cover_31⟩,
    ⟨604, 199, cover_32⟩, ⟨628, 77, cover_33⟩, ⟨650, 21, cover_34⟩, ⟨669, 173, cover_35⟩, trivial⟩

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

end SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
