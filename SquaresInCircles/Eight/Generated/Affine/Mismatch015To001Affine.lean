module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Data
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Cover00
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Cover01
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Cover02

/-! # The affine table `Mismatch015To001Affine`

Each of its 130198 rows passes `checkRow`, so it satisfies its claim
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

theorem all_row_claims : ∀ r ∈ rows, r.Claim table := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact checkRow_claim ctx_valid (checkRows_sound data_check x hx)

theorem cover_endpoints : cover.EndpointsValid table := endpointsValid_atanEnds table _

theorem cover_blocks :
    AllBlocks (fun a n => ∃ c o, coverBlock coverCtx table true a n c o chunks = true)
    [(0, 16), (16, 11), (27, 11), (38, 11), (49, 11), (60, 11), (71, 11), (82, 11), (93, 7),
     (100, 7), (107, 7), (114, 7), (121, 8), (129, 12), (141, 21), (162, 18), (180, 17), (197, 21),
     (218, 12), (230, 12), (242, 12), (254, 22), (276, 24), (300, 21), (321, 21), (342, 19),
     (361, 16), (377, 16), (393, 17), (410, 8), (418, 8), (426, 8), (434, 9), (443, 13)] :=
  by simp only [AllBlocks]; exact
    ⟨⟨0, 0, cover_0⟩, ⟨16, 28, cover_1⟩, ⟨35, 101, cover_2⟩, ⟨54, 174, cover_3⟩, ⟨74, 60, cover_4⟩,
    ⟨96, 8, cover_5⟩, ⟨117, 132, cover_6⟩, ⟨138, 105, cover_7⟩, ⟨156, 118, cover_8⟩,
    ⟨176, 128, cover_9⟩, ⟨197, 149, cover_10⟩, ⟨219, 9, cover_11⟩, ⟨239, 7, cover_12⟩,
    ⟨260, 53, cover_13⟩, ⟨276, 103, cover_14⟩, ⟨292, 153, cover_15⟩, ⟨310, 122, cover_16⟩,
    ⟨329, 47, cover_17⟩, ⟨347, 111, cover_18⟩, ⟨366, 49, cover_19⟩, ⟨384, 159, cover_20⟩,
    ⟨402, 161, cover_21⟩, ⟨419, 12, cover_22⟩, ⟨438, 149, cover_23⟩, ⟨456, 121, cover_24⟩,
    ⟨475, 126, cover_25⟩, ⟨495, 18, cover_26⟩, ⟨514, 95, cover_27⟩, ⟨533, 149, cover_28⟩,
    ⟨550, 21, cover_29⟩, ⟨571, 23, cover_30⟩, ⟨594, 67, cover_31⟩, ⟨616, 173, cover_32⟩,
    ⟨638, 144, cover_33⟩, trivial⟩

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

end SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
