module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.Data
public import SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.Cover00
public import SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.Cover01
public import SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.Cover02

/-! # The affine table `Mismatch026To01Affine`

Each of its 107596 rows passes `checkRow`, so it satisfies its claim
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

theorem all_row_claims : ∀ r ∈ rows, r.Claim table := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact checkRow_claim ctx_valid (checkRows_sound data_check x hx)

theorem cover_endpoints : cover.EndpointsValid table := endpointsValid_atanEnds table _

theorem cover_blocks :
    AllBlocks (fun a n => ∃ c o, coverBlock coverCtx table true a n c o chunks = true)
    [(0, 15), (15, 10), (25, 9), (34, 8), (42, 8), (50, 9), (59, 6), (65, 6), (71, 6), (77, 5),
     (82, 7), (89, 19), (108, 13), (121, 12), (133, 12), (145, 8), (153, 8), (161, 8), (169, 7),
     (176, 20), (196, 13), (209, 10), (219, 10), (229, 10), (239, 10), (249, 11), (260, 18),
     (278, 22), (300, 16), (316, 15), (331, 12), (343, 11), (354, 20), (374, 13), (387, 14)] :=
  by simp only [AllBlocks]; exact
    ⟨⟨0, 0, cover_0⟩, ⟨18, 168, cover_1⟩, ⟨38, 116, cover_2⟩, ⟨56, 66, cover_3⟩,
    ⟨75, 160, cover_4⟩, ⟨94, 138, cover_5⟩, ⟨113, 158, cover_6⟩, ⟨132, 35, cover_7⟩,
    ⟨150, 195, cover_8⟩, ⟨168, 90, cover_9⟩, ⟨185, 55, cover_10⟩, ⟨202, 123, cover_11⟩,
    ⟨209, 107, cover_12⟩, ⟨214, 138, cover_13⟩, ⟨214, 138, cover_14⟩, ⟨214, 138, cover_15⟩,
    ⟨223, 68, cover_16⟩, ⟨234, 107, cover_17⟩, ⟨246, 39, cover_18⟩, ⟨258, 79, cover_19⟩,
    ⟨274, 191, cover_20⟩, ⟨292, 145, cover_21⟩, ⟨310, 186, cover_22⟩, ⟨328, 108, cover_23⟩,
    ⟨344, 167, cover_24⟩, ⟨360, 187, cover_25⟩, ⟨376, 11, cover_26⟩, ⟨390, 23, cover_27⟩,
    ⟨409, 144, cover_28⟩, ⟨428, 92, cover_29⟩, ⟨447, 139, cover_30⟩, ⟨467, 104, cover_31⟩,
    ⟨487, 59, cover_32⟩, ⟨506, 12, cover_33⟩, ⟨528, 79, cover_34⟩, trivial⟩

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

end SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine
