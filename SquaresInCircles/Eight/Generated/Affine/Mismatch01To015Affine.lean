module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Data
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Cover00
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Cover01
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Cover02

/-! # The affine table `Mismatch01To015Affine`

Each of its 87118 rows passes `checkRow`, so it satisfies its claim
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

theorem complete_row_count : rows.length = 87118 := by
  simp only [rows, data, chunks, List.length_map, List.length_flatten, List.map_append,
    List.sum_append, parts000_length, parts001_length, parts002_length, parts003_length,
    parts004_length, parts005_length, parts006_length, parts007_length, parts008_length,
    Nat.reduceAdd]

theorem all_row_claims : ∀ r ∈ rows, r.Claim table := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact checkRow_claim ctx_valid (checkRows_sound data_check x hx)

theorem cover_endpoints : cover.EndpointsValid table := endpointsValid_atanEnds table _

theorem cover_blocks :
    AllBlocks (fun a n => ∃ c o, coverBlock coverCtx table true a n c o chunks = true)
    [(0, 21), (21, 10), (31, 10), (41, 14), (55, 17), (72, 10), (82, 11), (93, 17), (110, 15),
     (125, 13), (138, 17), (155, 11), (166, 10), (176, 11), (187, 21), (208, 17), (225, 14),
     (239, 14), (253, 14), (267, 12), (279, 12), (291, 17), (308, 10), (318, 13), (331, 4)] :=
  by simp only [AllBlocks]; exact
    ⟨⟨0, 0, cover_0⟩, ⟨10, 140, cover_1⟩, ⟨28, 186, cover_2⟩, ⟨48, 86, cover_3⟩,
    ⟨68, 190, cover_4⟩, ⟨87, 173, cover_5⟩, ⟨108, 32, cover_6⟩, ⟨128, 116, cover_7⟩,
    ⟨145, 22, cover_8⟩, ⟨160, 136, cover_9⟩, ⟨178, 135, cover_10⟩, ⟨197, 88, cover_11⟩,
    ⟨215, 125, cover_12⟩, ⟨232, 37, cover_13⟩, ⟨249, 22, cover_14⟩, ⟨264, 150, cover_15⟩,
    ⟨281, 99, cover_16⟩, ⟨297, 176, cover_17⟩, ⟨316, 141, cover_18⟩, ⟨333, 171, cover_19⟩,
    ⟨353, 159, cover_20⟩, ⟨373, 199, cover_21⟩, ⟨392, 153, cover_22⟩, ⟨415, 106, cover_23⟩,
    ⟨432, 15, cover_24⟩, trivial⟩

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

end SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
