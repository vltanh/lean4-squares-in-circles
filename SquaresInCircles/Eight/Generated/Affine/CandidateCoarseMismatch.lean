module

public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Data
public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Cover00
public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Cover01
public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Cover02
public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Cover03
public import SquaresInCircles.Eight.Candidate.GeometricCoreMarker

/-!
# Eight squares: the affine table `CandidateCoarseMismatch`

Each of its 110425 rows passes `checkRow`, so it satisfies its claim
(`checkRow_claim`). The walks `coverBlock` over blocks of sources covering all arcs
give the angle coverage (`coverBlocks_sound`). With the state chains and the
arctangent intervals of the arcs they give the charged bound (`charged_bound`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
open Arithmetic

set_option maxRecDepth 100000

/-- All rows of the table. -/
noncomputable def rows : List AffineTableRow := data.map (·.toTableRow table ctx.den)

theorem all_row_claims : ∀ r ∈ rows, r.Claim table := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact AffineRow.claim_of_target_le (le_add_of_nonneg_right (enhancement_nonneg _))
    (checkRow_claim ctx_valid (checkRows_sound data_check x hx))

theorem cover_endpoints : cover.EndpointsValid table := endpointsValid_atanEnds table _

theorem cover_blocks :
    AllBlocks (fun a n => ∃ c o, coverBlock coverCtx table true a n c o chunks = true)
    [(0, 30), (30, 29), (59, 18), (77, 13), (90, 8), (98, 6), (104, 6), (110, 6), (116, 9),
     (125, 17), (142, 11), (153, 11), (164, 12), (176, 9), (185, 8), (193, 7), (200, 7), (207, 21),
     (228, 18), (246, 18), (264, 15), (279, 17), (296, 12), (308, 8), (316, 7), (323, 7),
     (330, 18), (348, 16), (364, 12), (376, 12), (388, 17), (405, 16), (421, 9), (430, 6),
     (436, 6), (442, 6), (448, 6), (454, 6), (460, 2)] :=
  by simp only [AllBlocks]; exact
    ⟨⟨0, 0, cover_0⟩, ⟨13, 173, cover_1⟩, ⟨19, 194, cover_2⟩, ⟨37, 129, cover_3⟩,
    ⟨56, 70, cover_4⟩, ⟨73, 112, cover_5⟩, ⟨90, 124, cover_6⟩, ⟨107, 78, cover_7⟩,
    ⟨123, 43, cover_8⟩, ⟨138, 158, cover_9⟩, ⟨149, 79, cover_10⟩, ⟨159, 159, cover_11⟩,
    ⟨164, 83, cover_12⟩, ⟨166, 5, cover_13⟩, ⟨175, 199, cover_14⟩, ⟨189, 2, cover_15⟩,
    ⟨203, 50, cover_16⟩, ⟨220, 52, cover_17⟩, ⟨239, 90, cover_18⟩, ⟨259, 2, cover_19⟩,
    ⟨274, 171, cover_20⟩, ⟨294, 119, cover_21⟩, ⟨311, 7, cover_22⟩, ⟨323, 171, cover_23⟩,
    ⟨335, 67, cover_24⟩, ⟨347, 170, cover_25⟩, ⟨363, 44, cover_26⟩, ⟨379, 178, cover_27⟩,
    ⟨392, 173, cover_28⟩, ⟨411, 44, cover_29⟩, ⟨430, 191, cover_30⟩, ⟨440, 111, cover_31⟩,
    ⟨448, 176, cover_32⟩, ⟨465, 55, cover_33⟩, ⟨482, 111, cover_34⟩, ⟨499, 10, cover_35⟩,
    ⟨515, 151, cover_36⟩, ⟨531, 140, cover_37⟩, ⟨547, 40, cover_38⟩, trivial⟩

theorem cover_angles : cover.AngleCovers table rows true :=
  coverBlocks_sound coverCtx_valid.1 coverCtx_valid.2 (by decide +kernel) cover_blocks

theorem markers_valid : Candidate.GeometricCoreMarker.MarkersValid cover table := by
  decide +kernel

theorem budgets_valid : Candidate.GeometricCoreMarker.BudgetsValid table := by decide +kernel

theorem strong_budgets_valid :
    Candidate.GeometricCoreMarker.BudgetsValid {table with target := fun _ => 9/10} := by
  decide +kernel

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
    word_matches hcharge hcuts hdiff haxes (fun _ => Candidate.GeometricCoreMarker.pair_bound cover_endpoints markers_valid
      budgets_valid C F)

/-- No edge of a cycle with the cuts of the table joins two core squares. -/
theorem no_adjacent_core (C : BoundaryCycle (table.radius:ℝ)) (F : Candidate.Frame C) (β : ℝ)
    (hβ : 0 ≤ β) (hcharge : ∀ i, (table.charge i:ℝ)=Candidate.charge β i)
    (hcuts : ∀ i, (table.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (table.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈table.allowedAxes i) : NoAdjacentCore C :=
  Candidate.GeometricCoreMarker.no_adjacent_core cover_endpoints cover_states cover_angles
    all_row_claims markers_valid budgets_valid strong_budgets_valid (by decide +kernel)
    (by decide +kernel) C F β hβ word_matches hcharge hcuts hdiff haxes

end SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
