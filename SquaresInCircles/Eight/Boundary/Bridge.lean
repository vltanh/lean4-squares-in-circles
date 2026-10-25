module

public import SquaresInCircles.Eight.Boundary.Candidate.FramePullback
public import SquaresInCircles.Eight.Frames.Basic
public import SquaresInCircles.Eight.Owners.NecessaryCycle

/-!
# Eight squares: boundary cycles as signed cycles

A boundary cycle `C` read in a candidate frame `F` is a signed cycle `SignedCycle.atFrame F`. Its
physical gaps are the gaps of the centre directions of `C` (`atFrame_physicalGap`), it is ordered
and satisfies `Necessary` at the level of `C` (`atFrame_ordered`, `atFrame_necessary`), and its
squares are the squares of `C`, frames included (`atFrame_actualSquare`). The witness of each
edge is one of the forward axes of the signed cycle (`retainedOwner`, `retainedOwner_axis`,
`retainedOwner_feasible`), and witnesses that are normal owners are witnesses of the signed cycle
(`retainedWitnesses`). The transverse coordinate of a point has the sign of its tangent, and a
square on the outer curve gives an outer point at the level of `C` (`atFrame_outer_of_kind`).

If the frame steps are at most `frameCap` and their frame costs add up to less than
`10394/25425`, the positive and the negative variations of the frame angles are both below
`frameCap` (`variations_lt_of_frameCost`, `atFrame_variations_of_actual_cost`): the cost of a
step is at least its chord on `[0, frameCap]`, and `10394/25425 < 2 frameCost frameCap`.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight
open Candidate

namespace SignedCycle

theorem atFrame_physicalGap {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (i : Vertex) :
    (atFrame F).physicalGap i=angleGap C.beta i := by
  have h := F.physical_angle i
  change Candidate.phi F.theta i+C.alpha i-C.alpha (next i)=angleGap C.beta i
  linarith

theorem atFrame_ordered {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) : (atFrame F).Ordered := {
  gap_pos i := by rw [atFrame_physicalGap]; exact C.gap_pos i
  gap_lt_pi i := by rw [atFrame_physicalGap]; exact C.gap_lt_pi i }

theorem atFrame_necessary {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) : (atFrame F).Necessary q := {
  sorted := atFrame_sorted F
  contained := atFrame_contained F
  core := atFrame_core F
  spread i j := (F.spread i j).le }

theorem atFrame_strictSpread {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) : (atFrame F).StrictSpread := F.spread

private theorem square_eq_of_center_frame {K L : UnitSquare}
    (hc : K.center=L.center) (hf : SameFrame K L) : K=L := by
  cases K with
  | mk p c s hu =>
    cases L with
    | mk p' c' s' hu' =>
      rcases hf with ⟨hcos,hsin⟩
      dsimp only at hc hcos hsin
      cases hc
      cases hcos
      cases hsin
      rfl

/-- The squares of the signed cycle are the squares of `C`, with their directed frames. -/
theorem atFrame_actualSquare {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (i : Vertex) :
    (atFrame F).actualSquare i=C.square i := by
  have hc : (C.square i).cosine=
      Real.cos (F.theta i+(Candidate.offsets i : ℝ)*Real.pi/2) := by
    calc
      _ = Real.cos (C.canonicalAngle i) := C.frame_cos i
      _ = _ := congrArg Real.cos (F.canonical_eq i)
  have hs : (C.square i).sine=
      Real.sin (F.theta i+(Candidate.offsets i : ℝ)*Real.pi/2) := by
    calc
      _ = Real.sin (C.canonicalAngle i) := C.frame_sin i
      _ = _ := congrArg Real.sin (F.canonical_eq i)
  apply square_eq_of_center_frame
  · rw [C.center_eq]
    apply Prod.ext <;>
      simp [actualSquare,atFrame,SignedPoint.square,rotate,hc,hs] <;> ring
  · exact ⟨hc.symm,hs.symm⟩

/-- The index of the witness `C.selected i` among the forward axes. -/
def retainedOwner {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (i : Vertex) : Fin 4 :=
  Classical.choose (F.forward_complete i (C.selected i) (C.feasible i))

theorem retainedOwner_axis {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (i : Vertex) :
    C.selected i=forwardAxis (retainedOwner F i) :=
  Classical.choose_spec (F.forward_complete i (C.selected i) (C.feasible i))

theorem retainedOwner_feasible {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (i : Vertex) :
    (atFrame F).Feasible i (retainedOwner F i) := by
  apply (atFrame_feasible F i _).2
  rw [← retainedOwner_axis]
  exact C.feasible i

/-- The witnesses of `C`, when they are normal owners, as witnesses of the signed cycle. -/
def retainedWitnesses {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (h : Candidate.OwnerRestriction C normalOwners) :
    (atFrame F).Witnesses where
  owner := retainedOwner F
  feasible := retainedOwner_feasible F
  allowed i := h i _ ((atFrame_feasible F i _).1 (retainedOwner_feasible F i))

theorem atFrame_tangent_coordinate {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (i : Vertex) :
    ((atFrame F).point i).y=C.tangent i*C.a i := by
  simp [atFrame,BoundaryCycle.tangent,ne_of_gt (C.a_pos i)]

theorem atFrame_y_nonneg_iff {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (i : Vertex) :
    0≤((atFrame F).point i).y ↔ 0≤C.tangent i := by
  rw [atFrame_tangent_coordinate]
  exact mul_nonneg_iff_of_pos_right (C.a_pos i)

theorem atFrame_y_nonpos_iff {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (i : Vertex) :
    ((atFrame F).point i).y≤0 ↔ C.tangent i≤0 := by
  rw [atFrame_tangent_coordinate]
  exact ⟨fun h => nonpos_of_mul_nonpos_left h (C.a_pos i),
    fun h => mul_nonpos_of_nonpos_of_nonneg h (C.a_pos i).le⟩

theorem atFrame_y_pos_iff {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (i : Vertex) :
    0<((atFrame F).point i).y ↔ 0<C.tangent i := by
  rw [atFrame_tangent_coordinate]
  exact mul_pos_iff_of_pos_right (C.a_pos i)

theorem atFrame_y_neg_iff {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (i : Vertex) :
    ((atFrame F).point i).y<0 ↔ C.tangent i<0 := by
  rw [atFrame_tangent_coordinate]
  refine ⟨fun h => ?_,fun h => mul_neg_of_neg_of_pos h (C.a_pos i)⟩
  by_contra! h'
  linarith [mul_nonneg h' (C.a_pos i).le]

/-- A square of `C` on the outer curve gives an outer point at the level `q` of `C`. -/
theorem atFrame_outer_of_kind {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (i : Vertex) (hi : C.kind i=.outer) :
    ((atFrame F).point i).Outer q := by
  have h := C.boundary i
  rw [hi] at h
  simp only [BoundaryState,SquaresInCircles.phi] at h
  simp only [atFrame,SignedPoint.Outer,SignedPoint.circle,signed_b_abs]
  exact h

end SignedCycle

/-- If the steps of `θ` are at most `frameCap` and their frame costs add up to less than
`10394/25425`, the positive and the negative variations of `θ` are below `frameCap`, by the
chord estimate of the frame cost on `[0, frameCap]`. -/
theorem variations_lt_of_frameCost {θ : Vertex → ℝ}
    (hstep : ∀ i, |delta θ i|≤frameCap)
    (hcost : (∑ i,frameCost |delta θ i|)<10394/25425) :
    positiveVariation θ<frameCap ∧ negativeVariation θ<frameCap := by
  have hcap : (0:ℝ)<frameCap := by norm_num [frameCap]
  have hquarter : frameCap≤Real.pi/4 := by
    dsimp [frameCap]
    linarith [Real.pi_gt_three]
  have hchord (i : Vertex) :
      |delta θ i| * frameCost frameCap≤frameCap*frameCost |delta θ i| := by
    have h := frameCost_chord (abs_nonneg (delta θ i)) (hstep i) hcap hquarter
    have hh := mul_le_mul_of_nonneg_left h hcap.le
    convert hh using 1
    field_simp
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset Vertex))
    (fun i _ => hchord i)
  rw [← Finset.sum_mul,← Finset.mul_sum] at hs
  have hsum : (∑ i,|delta θ i|)=positiveVariation θ+negativeVariation θ := by
    simp only [positiveVariation,negativeVariation,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (positive_add_negative _).symm
  rw [hsum,← variations_equal] at hs
  have hreserve : (10394/25425:ℝ)<2*frameCost frameCap := frameCost_seven_tenths
  have hfc : 0<frameCost frameCap := by linarith
  have hscaled := mul_lt_mul_of_pos_left (hcost.trans hreserve) hcap
  have hp : positiveVariation θ<frameCap := by nlinarith
  exact ⟨hp,by rwa [← variations_equal]⟩

theorem frameCost_eq_actual {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (i : Vertex) :
    frameCost |delta F.theta i|=
      periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i) := by
  have hshort : |delta F.theta i|≤Real.pi/4 := by
    have h := F.delta_small i
    linarith [Real.pi_gt_three]
  rw [F.canonical_eq,F.canonical_eq]
  have hid :
      (F.theta (next i)+(offsets (next i) : ℝ)*Real.pi/2)-
        (F.theta i+(offsets i : ℝ)*Real.pi/2) =
      delta F.theta i+((offsets (next i)-offsets i : ℤ) : ℝ)*(Real.pi/2) := by
    push_cast
    unfold delta
    ring
  rw [hid,periodicFrameCost_int_quarter,periodicFrameCost_of_short hshort]

theorem atFrame_variations_of_actual_cost {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C)
    (hc : (∑ i,periodicFrameCost
      (C.canonicalAngle (next i)-C.canonicalAngle i))<10394/25425) :
    positiveVariation (SignedCycle.atFrame F).theta<frameCap ∧
      negativeVariation (SignedCycle.atFrame F).theta<frameCap := by
  apply variations_lt_of_frameCost (fun i => (F.delta_small i).le)
  simpa only [frameCost_eq_actual F] using hc

namespace SignedCycle

theorem E_nonpos_pullback {q r : ℝ} {C : BoundaryCycle q}
    {D : BoundaryCycle r} (F : Candidate.Frame D) (hR : RadiusExpansion C D)
    (hE : Candidate.EHalf D) :
    ((atFrame (F.pullback hR)).point E).y≤0 := by
  apply (atFrame_y_nonpos_iff _ E).2
  simpa only [Candidate.EHalf,hR.same_tangents] using hE

end SignedCycle
end SquaresInCircles.Eight
