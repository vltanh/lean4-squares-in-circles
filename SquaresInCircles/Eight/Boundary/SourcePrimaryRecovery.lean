module

public import SquaresInCircles.Eight.Boundary.Candidate.Geometry
public import SquaresInCircles.Eight.Boundary.SourceRecovery
public import SquaresInCircles.Eight.Equality.Angles
public import SquaresInCircles.Eight.Frames.Basic
public import SquaresInCircles.Eight.Owners.NecessaryCycle
public import SquaresInCircles.Eight.Owners.Primary.PairClassification
public import SquaresInCircles.Eight.Stationary.System

/-!
# Eight squares: the hard axes of the source

The pair moves of G and T keep track of their source: if the hard axis GA0 becomes feasible only
after the moves, then `θA - θH > 0` or the contact H–G is strict, and the same for BT2 with
`θD - θB` and the contact T–D. So if both hard axes are feasible after the moves, with
`θA ≤ θH`, `θD ≤ θB` and the contacts H–G and T–D tight, they were already feasible on the input
(`original_hard_of_pair_contacts`). Then the moves leave G and T in place (their field
`fixed_if_hard`), and the cycle after both moves is the input itself
(`pairDescendant_eq_original_of_hard`).
-/

section
/-!
## Boundary cycles as signed cycles

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
end
end
end

section
/-!
## Actual primary preprocessing with its original-source obstruction

A source
which already has its hard primary is left literally unchanged.  If a
missing hard primary becomes feasible, the output retains either the
positive original anchor total or a strict actual neighboring zero axis.
The implication tests actual output feasibility, not its selected owner.
No equality conclusion or hard-class endpoint is assumed here.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate

structure GPairSourceOutput (q : ℝ) (H G A : SignedPoint) (θH θG θA : ℝ) where
  output : GPairOutput q H A θH θG θA
  fixed_if_hard : quarterFeasible G A (θA-θG) 0 →
    output.point=G ∧ output.theta=θG
  source_obstruction : (¬quarterFeasible G A (θA-θG) 0) →
    quarterFeasible output.point A (θA-output.theta) 0 →
    0<θA-θH ∨
      edgeWidth (output.theta-θH)<
        zeroProjection H output.point (output.theta-θH) output.hgOwner

namespace GPairSourceOutput

def original_hard {q θH θG θA : ℝ} {H G A : SignedPoint}
    (I : GPairInput q H G A θH θG θA)
    (hhard : quarterFeasible G A (θA-θG) 0) :
    GPairSourceOutput q H G A θH θG θA where
  output := GPairOutput.original_hard I hhard
  fixed_if_hard := fun _ => ⟨rfl,rfl⟩
  source_obstruction := fun h _ => False.elim (h hhard)

/-- An already aligned negative primary remains its literal source.
Moving it again would discard the required source-contact provenance. -/
def original_negative {q θH θG θA : ℝ} {H G A : SignedPoint}
    (I : GPairInput q H G A θH θG θA)
    (hnot : ¬quarterFeasible G A (θA-θG) 0)
    (hn : θA-θG<0) (hy : G.y<0) (ha : θG=θH) :
    GPairSourceOutput q H G A θH θG θA where
  output := {
    point := G
    theta := θG
    hgOwner := I.owner
    gaOwner := 1
    hg_allowed := I.owner_allowed
    ga_allowed := Or.inr rfl
    sorted := I.G_sorted
    contained := I.G_contained
    avoids := I.G_core
    boundary := I.G_boundary
    HG := I.HG
    GA := I.GA
    canceling_normal := I.canceling_normal
    frame_range := Or.inl rfl
    terminal := Or.inr (Or.inr (Or.inl ⟨rfl,ha,hn,hy⟩)) }
  fixed_if_hard := fun h => False.elim (hnot h)
  source_obstruction := fun _ h => False.elim (hnot h)

/-- For an unaligned negative source, an actual hard output keeps the
strict owner supplied by the concrete negative transport.  If the hard
axis remains absent, the endpoint is classified with its aligned tie. -/
theorem of_negative {q θH θG θA : ℝ} {H G A : SignedPoint}
    (hnot : ¬quarterFeasible G A (θA-θG) 0)
    (hne : θG≠θH) (O : NegativeGEndpoint q H A θH θA θG) :
    Nonempty (GPairSourceOutput q H G A θH θG θA) := by
  have hframe : O.theta∈Icc (min θH θA) (max θH θA) := by
    rcases O.endpoint with h | h
    · rw [h]; exact ⟨min_le_right _ _,le_max_right _ _⟩
    · rw [h]; exact ⟨min_le_left _ _,le_max_left _ _⟩
  by_cases hhard : quarterFeasible O.point A (θA-O.theta) 0
  · exact ⟨{
      output := {
        point := O.point
        theta := O.theta
        hgOwner := O.owner
        gaOwner := 0
        hg_allowed := O.owner_allowed
        ga_allowed := Or.inl rfl
        sorted := O.sorted
        contained := O.circle_lt.le
        avoids := O.avoids
        boundary := Or.inr O.core
        HG := O.HG
        GA := hhard
        canceling_normal := fun _ => O.normal
        frame_range := Or.inr hframe
        terminal := Or.inl rfl }
      fixed_if_hard := fun h => False.elim (hnot h)
      source_obstruction := fun _ _ => Or.inr (O.strict_if_unaligned hne) }⟩
  have hH : O.theta=θH := by
    rcases O.endpoint with h | h
    · exact False.elim (hhard (O.hard_at_A h))
    · exact h
  have hzero : zeroFeasible H O.point 0 2 := by
    have hh := O.HG
    rw [hH,sub_self] at hh
    rcases O.owner_allowed with h | h
    · exact (zero_owner_tie _ _).1 (by simpa [h] using hh)
    · simpa [h] using hh
  have hnonzero : θA-O.theta≠0 := by
    intro h
    apply hhard
    rw [h]
    exact (quarter_low_tie _ _).2 (by simpa [h] using O.GA)
  have hterminal :
      (1 : Fin 4)=0 ∨
        ((1 : Fin 4)=1 ∧ (2 : Fin 4)=2 ∧ 0<θA-O.theta) ∨
        ((1 : Fin 4)=1 ∧ O.theta=θH ∧ θA-O.theta<0 ∧ O.point.y<0) ∨
        O.point.y= -O.point.a := by
    rcases lt_or_gt_of_ne hnonzero with hn | hp
    · exact Or.inr (Or.inr (Or.inl ⟨rfl,hH,hn,O.normal⟩))
    · exact Or.inr (Or.inl ⟨rfl,rfl,hp⟩)
  exact ⟨{
    output := {
      point := O.point
      theta := O.theta
      hgOwner := 2
      gaOwner := 1
      hg_allowed := Or.inr rfl
      ga_allowed := Or.inr rfl
      sorted := O.sorted
      contained := O.circle_lt.le
      avoids := O.avoids
      boundary := Or.inr O.core
      HG := by simpa [hH] using hzero
      GA := O.GA
      canceling_normal := fun _ => O.normal
      frame_range := Or.inr hframe
      terminal := hterminal }
    fixed_if_hard := fun h => False.elim (hnot h)
    source_obstruction := fun _ h => False.elim (hhard h) }⟩

end GPairSourceOutput

/-- Every original source row has an actual same-radius output together
with the strict source information needed by the later equality pullback. -/
theorem preprocess_G_pair_with_source {q θH θG θA : ℝ} {H G A : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (I : GPairInput q H G A θH θG θA) :
    Nonempty (GPairSourceOutput q H G A θH θG θA) := by
  by_cases hhard : quarterFeasible G A (θA-θG) 0
  · exact ⟨GPairSourceOutput.original_hard I hhard⟩
  have hnonzero : θA-θG≠0 := by
    intro h
    apply hhard
    rw [h]
    exact (quarter_low_tie _ _).2 (by simpa [h] using I.GA)
  have hHbound : H.y<9/10 := (le_abs_self H.y).trans_lt
    (H.coordinate_bounds I.H_sorted I.H_core I.H_contained hqU).2.2
  have negative_endpoint (hn : θA-θG<0) (hy : G.y≤0) :
      Nonempty (GPairSourceOutput q H G A θH θG θA) := by
    by_cases ha : θG=θH
    · have hzero : zeroFeasible H G 0 0 := by
        have hh := I.HG
        have h0 : θG-θH=0 := sub_eq_zero.mpr ha
        rw [h0] at hh
        rcases I.owner_allowed with hj | hj
        · simpa [hj] using hh
        · exact (zero_owner_tie _ _).2 (by simpa [hj] using hh)
      have hylt := hg0_nonpositive_error_normal hHbound I.G_sorted.1
        (by norm_num : |(0 : ℝ)|≤7/10) (by norm_num : (0 : ℝ)≤0) hzero
      exact ⟨GPairSourceOutput.original_negative I hhard hn hylt ha⟩
    · obtain ⟨O⟩ := negative_GA_pair_endpoint hqU
        I.H_sorted I.G_sorted I.A_sorted I.H_contained I.G_contained I.A_contained
        I.H_core I.G_core I.A_core I.G_boundary I.H_normal hy I.A_normal
        hn I.GA_error (by simpa [abs_sub_comm] using I.HA_error) I.HG_error
        I.owner_allowed I.HG I.GA hhard
      exact GPairSourceOutput.of_negative hhard ha O
  rcases I.owner_allowed with hj | hj
  · have hHG : zeroFeasible H G (θG-θH) 0 := by simpa [hj] using I.HG
    by_cases htotal : 0<θA-θH
    · obtain ⟨O⟩ := positive_GA_HG_pair hqL hqU
        I.H_sorted I.A_sorted I.G_sorted I.H_normal I.H_contained I.A_outer
        I.G_contained I.G_core hHG I.GA I.GA_error I.HG_error
        ⟨htotal,(abs_le.mp I.HA_error).2⟩
      obtain ⟨P⟩ := GPairOutput.of_positive_endpoint O hHbound htotal
      exact ⟨{
        output := P
        fixed_if_hard := fun h => False.elim (hhard h)
        source_obstruction := fun _ _ => Or.inl htotal }⟩
    · have htotal0 : θA≤θH := by linarith
      rcases lt_or_gt_of_ne hnonzero with hn | hp
      · by_cases hy : G.y≤0
        · exact negative_endpoint hn hy
        · have hy0 : 0≤G.y := (lt_of_not_ge hy).le
          have hHGpos : 0<θG-θH := by
            by_contra! hd
            exact (not_le_of_gt
              (hg0_nonpositive_error_normal hHbound I.G_sorted.1 I.HG_error hd hHG)) hy0
          let s := θH-θA
          let v := θG-θH
          have hs : 0≤s := by dsimp [s]; linarith
          have hv : 0≤v := hHGpos.le
          have hsum : v+s=θG-θA := by dsimp [v,s]; ring
          have hsumBound : v+s≤7/10 := by
            have hb := (abs_le.mp I.GA_error).1
            simp only [frameCap] at hb
            rw [hsum]
            linarith
          have hprimary : quarterFeasible G A (-(v+s)) 1 := by
            convert I.GA using 1
            dsimp [v,s]
            ring
          obtain ⟨hs',hc',hcircle,hHG',hGA',hGA1',hstrict⟩ :=
            wrong_sign_nonpositive_total_transport hqU
              I.H_sorted I.G_sorted I.A_sorted I.H_contained I.G_contained I.A_contained
              I.H_core I.G_core I.A_core I.H_normal hy0 I.A_normal hs hv hsumBound
              hHG hprimary
          have he : θA-θH= -s := by dsimp [s]; ring
          have htransverse : zeroFeasible H (SignedPoint.flat (-(A.a-1))) (θA-θH) 0 := by
            rw [he]
            exact hHG'
          refine ⟨{
            output := GPairOutput.flat_hard hs' hc' hcircle htransverse hGA'
            fixed_if_hard := fun h => False.elim (hhard h)
            source_obstruction := ?_ }⟩
          intro _ _
          right
          change edgeWidth (θA-θH)<
            zeroProjection H (SignedPoint.flat (-(A.a-1))) (θA-θH) 0
          rw [he]
          linarith
      · have hHGneg : θG-θH≤0 := by linarith
        have hy := (hg0_nonpositive_error_normal hHbound I.G_sorted.1
          I.HG_error hHGneg hHG).le
        let s := θH-θA
        let x := θA-θG
        have hs : 0≤s := by dsimp [s]; linarith
        have hx : 0<x := hp
        have hsum : s+x=θH-θG := by dsimp [s,x]; ring
        have hsumBound : s+x≤7/10 := by
          have hb := (abs_le.mp I.HG_error).1
          simp only [frameCap] at hb
          rw [hsum]
          linarith
        have htransverse : zeroFeasible H G (-(s+x)) 0 := by
          convert hHG using 1
          dsimp [s,x]
          ring
        obtain ⟨hs',hc',havoid,hcircle,hGA',hGA1',hstrict⟩ :=
          positive_ga1_nonpositive_total_transport hqU
            I.H_sorted I.G_sorted I.A_sorted I.H_contained I.G_contained I.A_contained
            I.H_core I.G_core I.A_core I.H_normal hy I.A_normal hx hs hsumBound
            htransverse I.GA
        have he : θA-θH= -s := by dsimp [s]; ring
        have hHG' : zeroFeasible H (SignedPoint.flat (-(A.a-1))) (θA-θH) 0 := by
          rw [he]
          exact hstrict.le
        refine ⟨{
          output := GPairOutput.flat_hard hs' hc' hcircle hHG' hGA'
          fixed_if_hard := fun h => False.elim (hhard h)
          source_obstruction := ?_ }⟩
        intro _ _
        right
        change edgeWidth (θA-θH)<
          zeroProjection H (SignedPoint.flat (-(A.a-1))) (θA-θH) 0
        rw [he]
        exact hstrict
  · rcases lt_or_gt_of_ne hnonzero with hn | hp
    · exact negative_endpoint hn (I.canceling_normal hj).le
    · exact ⟨{
        output := GPairOutput.original_positive I hj hp
        fixed_if_hard := fun h => False.elim (hhard h)
        source_obstruction := fun _ h => False.elim (hhard h) }⟩

structure TPairSourceOutput (q : ℝ) (B T D : SignedPoint) (θB θT θD : ℝ) where
  output : TPairOutput q B D θB θT θD
  fixed_if_hard : quarterFeasible B T (θT-θB) 2 →
    output.point=T ∧ output.theta=θT
  source_obstruction : (¬quarterFeasible B T (θT-θB) 2) →
    quarterFeasible B output.point (output.theta-θB) 2 →
    0<θD-θB ∨
      edgeWidth (θD-output.theta)<
        zeroProjection output.point D (θD-output.theta) output.tdOwner

/-- Local reflection preserves the actual source and target hard-axis tests.
The original E point and its signed tangent do not occur in this operation. -/
def GPairSourceOutput.reflectToT {q θB θT θD : ℝ} {B T D : SignedPoint}
    (S : GPairSourceOutput q D.reflect T.reflect B.reflect (-θD) (-θT) (-θB)) :
    TPairSourceOutput q B T D θB θT θD where
  output := S.output.reflectToT
  fixed_if_hard := by
    intro h
    have hh : quarterFeasible T.reflect B.reflect (-θB-(-θT)) 0 := by
      have h2 := (quarterFeasible_reflect B T (θT-θB) 2).2 h
      rw [show -θB-(-θT)=θT-θB by ring]
      simpa [reflectedOwner] using h2
    obtain ⟨hp,ht⟩ := S.fixed_if_hard hh
    change S.output.point.reflect=T ∧ -S.output.theta=θT
    constructor
    · rw [hp]; simp
    · linarith
  source_obstruction := by
    intro hnot hout
    have hnot' : ¬quarterFeasible T.reflect B.reflect (-θB-(-θT)) 0 := by
      intro h
      apply hnot
      apply (quarterFeasible_reflect B T (θT-θB) 2).1
      rw [show -θB-(-θT)=θT-θB by ring] at h
      simpa [reflectedOwner] using h
    have hout' : quarterFeasible B S.output.point.reflect (-θB-S.output.theta) 2 := by
      simpa [GPairOutput.reflectToT,sub_eq_add_neg,add_comm] using hout
    have hhard : quarterFeasible S.output.point B.reflect (-θB-S.output.theta) 0 :=
      (quarterFeasible_reflect S.output.point B.reflect (-θB-S.output.theta) 0).1
        (by simpa [reflectedOwner] using hout')
    rcases S.source_obstruction hnot' hhard with htotal | hstrict
    · left
      simpa only [neg_sub_neg] using htotal
    · right
      have hid := zeroProjection_reflect D.reflect S.output.point
        (S.output.theta-(-θD)) S.output.hgOwner
      rw [←hid] at hstrict
      simpa [GPairOutput.reflectToT,sub_eq_add_neg,add_comm] using hstrict

theorem preprocess_T_pair_with_source {q θB θT θD : ℝ} {B T D : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (I : TPairInput q B T D θB θT θD) :
    Nonempty (TPairSourceOutput q B T D θB θT θD) := by
  obtain ⟨S⟩ := preprocess_G_pair_with_source hqL hqU I
  exact ⟨S.reflectToT⟩

end SquaresInCircles.Eight
end
end
end

section
/-!
## The pair moves with their sources

A boundary input at a level `qLow ≤ q ≤ qCap` has pair moves of G and of T that keep track of
their source (`BoundaryInput.g_source_output`, `t_source_output`). The move of G leaves its point
and frame unchanged when G–A is already separated along the axis zero; if that axis becomes
feasible only after the move, then `θA - θH > 0` or the contact H–G of the output is strict. The
move of T behaves in the same way, with B–T, the axis two, `θD - θB` and the contact T–D. On the
cycle after both moves (`pairDescendant`) these alternatives still hold, since the move of T
leaves H–G unchanged and the move of G leaves T–D unchanged (`pairDescendant_g_source_obstruction`,
`pairDescendant_t_source_obstruction`), and a point whose hard axis was feasible keeps its point
and frame (`pairDescendant_fixed_sources`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate

namespace SignedCycle.BoundaryInput

theorem g_source_output {q : ℝ} (I : BoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) :
    Nonempty (GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A)) := by
  by_cases hhard : I.cycle.Feasible G 0
  · exact ⟨{
      output := I.hardG hhard
      fixed_if_hard := fun _ => ⟨rfl,rfl⟩
      source_obstruction := fun h _ => False.elim (h (I.hardG hhard).GA) }⟩
  have hprimary : I.cycle.Feasible G 1 := by
    have howner : I.witnesses.owner G=0 ∨ I.witnesses.owner G=1 := by
      simpa [normalOwners,G] using I.witnesses.allowed G
    rcases howner with he | he
    · exact (hhard (by simpa [he] using I.witnesses.feasible G)).elim
    · simpa [he] using I.witnesses.feasible G
  exact preprocess_G_pair_with_source hqL hqU (I.gPair hprimary)

theorem t_source_output {q : ℝ} (I : BoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) :
    Nonempty (TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D)) := by
  by_cases hhard : I.cycle.Feasible B 2
  · exact ⟨{
      output := I.hardT hhard
      fixed_if_hard := fun _ => ⟨rfl,rfl⟩
      source_obstruction := fun h _ => False.elim (h (I.hardT hhard).BT) }⟩
  have hprimary : I.cycle.Feasible B 3 := by
    have howner : I.witnesses.owner B=2 ∨ I.witnesses.owner B=3 := by
      simpa [normalOwners,B] using I.witnesses.allowed B
    rcases howner with he | he
    · exact (hhard (by simpa [he] using I.witnesses.feasible B)).elim
    · simpa [he] using I.witnesses.feasible B
  exact preprocess_T_pair_with_source hqL hqU (I.tPair hprimary)

/-- If G–A becomes separated along the axis zero only on the cycle after both moves, then
`θA - θH > 0` or the contact H–G is strict on that cycle. -/
theorem pairDescendant_g_source_obstruction {q : ℝ} (I : BoundaryInput q)
    (hq : q≤qCap)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hnot : ¬I.cycle.Feasible G 0)
    (hhard : (I.pairDescendant hq SG.output ST.output).cycle.Feasible G 0) :
    0<I.cycle.theta A-I.cycle.theta H ∨
      0<(I.pairDescendant hq SG.output ST.output).cycle.slack H SG.output.hgOwner := by
  have hnot' : ¬quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta G) 0 := by
    intro h
    apply hnot
    simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible]
      using sub_nonneg.mpr h
  have hhard' : quarterFeasible SG.output.point (I.cycle.point A)
      (I.cycle.theta A-SG.output.theta) 0 := by
    change 0≤(I.pairDescendant hq SG.output ST.output).cycle.slack G 0 at hhard
    rw [pairDescendant_cycle] at hhard
    simpa [slack,edge,replacePoint,word,delta,next,G,A,T,quarterFeasible]
      using sub_nonneg.mp hhard
  rcases SG.source_obstruction hnot' hhard' with htotal | hstrict
  · exact Or.inl htotal
  · right
    rw [pairDescendant_cycle]
    simpa [slack,edge,replacePoint,word,delta,next,H,G,T]
      using sub_pos.mpr hstrict

/-- If B–T becomes separated along the axis two only on the cycle after both moves, then
`θD - θB > 0` or the contact T–D, along the owner of the output, is strict on that cycle. -/
theorem pairDescendant_t_source_obstruction {q : ℝ} (I : BoundaryInput q)
    (hq : q≤qCap)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hnot : ¬I.cycle.Feasible B 2)
    (hhard : (I.pairDescendant hq SG.output ST.output).cycle.Feasible B 2) :
    0<I.cycle.theta D-I.cycle.theta B ∨
      0<(I.pairDescendant hq SG.output ST.output).cycle.slack T ST.output.tdOwner := by
  have hnot' : ¬quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta T-I.cycle.theta B) 2 := by
    intro h
    apply hnot
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible]
      using sub_nonneg.mpr h
  have hhard' : quarterFeasible (I.cycle.point B) ST.output.point
      (ST.output.theta-I.cycle.theta B) 2 := by
    change 0≤(I.pairDescendant hq SG.output ST.output).cycle.slack B 2 at hhard
    rw [pairDescendant_cycle] at hhard
    simpa [slack,edge,replacePoint,word,delta,next,B,T,G,quarterFeasible]
      using sub_nonneg.mp hhard
  rcases ST.source_obstruction hnot' hhard' with htotal | hstrict
  · exact Or.inl htotal
  · right
    rw [pairDescendant_cycle]
    simpa [slack,edge,replacePoint,word,delta,next,T,D,G]
      using sub_pos.mpr hstrict

/-- On the cycle after both moves, G keeps its point and frame when G–A is separated along the
axis zero, and T keeps them when B–T is separated along the axis two. -/
theorem pairDescendant_fixed_sources {q : ℝ} (I : BoundaryInput q)
    (hq : q≤qCap)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D)) :
    (I.cycle.Feasible G 0 →
      (I.pairDescendant hq SG.output ST.output).cycle.point G=I.cycle.point G ∧
      (I.pairDescendant hq SG.output ST.output).cycle.theta G=I.cycle.theta G) ∧
    (I.cycle.Feasible B 2 →
      (I.pairDescendant hq SG.output ST.output).cycle.point T=I.cycle.point T ∧
      (I.pairDescendant hq SG.output ST.output).cycle.theta T=I.cycle.theta T) := by
  constructor
  · intro h
    change 0≤I.cycle.slack G 0 at h
    have h' : quarterFeasible (I.cycle.point G) (I.cycle.point A)
        (I.cycle.theta A-I.cycle.theta G) 0 := by
      simpa [slack,edge,word,delta,next,G,A,quarterFeasible] using sub_nonneg.mp h
    obtain ⟨hp,ht⟩ := SG.fixed_if_hard h'
    rw [pairDescendant_cycle]
    simpa [replacePoint,G,T] using And.intro hp ht
  · intro h
    change 0≤I.cycle.slack B 2 at h
    have h' : quarterFeasible (I.cycle.point B) (I.cycle.point T)
        (I.cycle.theta T-I.cycle.theta B) 2 := by
      simpa [slack,edge,word,delta,next,B,T,quarterFeasible] using sub_nonneg.mp h
    obtain ⟨hp,ht⟩ := ST.fixed_if_hard h'
    rw [pairDescendant_cycle]
    simpa [replacePoint,G,T] using And.intro hp ht

end SignedCycle.BoundaryInput

namespace SignedCycle.NormalizedBoundaryInput

theorem g_source_output {q : ℝ} (I : NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) :
    Nonempty (GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A)) :=
  I.toBoundaryInput.g_source_output hqL hqU

theorem t_source_output {q : ℝ} (I : NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) :
    Nonempty (TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D)) :=
  I.toBoundaryInput.t_source_output hqL hqU

end SignedCycle.NormalizedBoundaryInput
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate Stationary GeometricModel

namespace SignedCycle.BoundaryInput

/-- If, on the cycle after both moves, GA0 and BT2 are feasible, `θA ≤ θH`, `θD ≤ θB`, and the
contacts H–G and T–D are tight, then GA0 and BT2 are feasible on the input. -/
theorem original_hard_of_pair_contacts {q : ℝ} (I : BoundaryInput q)
    (hq : q≤qCap)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hGA : (I.pairDescendant hq SG.output ST.output).cycle.Feasible G 0)
    (hBT : (I.pairDescendant hq SG.output ST.output).cycle.Feasible B 2)
    (hGtotal : (I.pairDescendant hq SG.output ST.output).cycle.theta A≤
      (I.pairDescendant hq SG.output ST.output).cycle.theta H)
    (hTtotal : (I.pairDescendant hq SG.output ST.output).cycle.theta D≤
      (I.pairDescendant hq SG.output ST.output).cycle.theta B)
    (hHG : (I.pairDescendant hq SG.output ST.output).cycle.slack H SG.output.hgOwner=0)
    (hTD : (I.pairDescendant hq SG.output ST.output).cycle.slack T ST.output.tdOwner=0) :
    I.cycle.HardOwners := by
  have ha := I.pairDescendant_anchors hq SG.output ST.output
  have hGsource : I.cycle.theta A≤I.cycle.theta H := by
    have h1 := (ha A (by simp [anchorVertices])).2
    have h2 := (ha H (by simp [anchorVertices])).2
    linarith
  have hTsource : I.cycle.theta D≤I.cycle.theta B := by
    have h1 := (ha D (by simp [anchorVertices])).2
    have h2 := (ha B (by simp [anchorVertices])).2
    linarith
  constructor
  · by_contra hnot
    rcases I.pairDescendant_g_source_obstruction hq SG ST hnot hGA with ht | hs
    · exact (not_lt_of_ge (sub_nonpos.mpr hGsource)) ht
    · rw [hHG] at hs
      exact (lt_irrefl 0) hs
  · by_contra hnot
    rcases I.pairDescendant_t_source_obstruction hq SG ST hnot hBT with ht | hs
    · exact (not_lt_of_ge (sub_nonpos.mpr hTsource)) ht
    · rw [hTD] at hs
      exact (lt_irrefl 0) hs

/-- If the input has hard owners, the moves leave G and T in place, and the anchors do not move,
so the cycle after both moves is the input. -/
theorem pairDescendant_eq_original_of_hard {q : ℝ} (I : BoundaryInput q)
    (hq : q≤qCap)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hhard : I.cycle.HardOwners) :
    (I.pairDescendant hq SG.output ST.output).cycle=I.cycle := by
  have ha := I.pairDescendant_anchors hq SG.output ST.output
  have hfixed := I.pairDescendant_fixed_sources hq SG ST
  have hG := hfixed.1 hhard.1
  have hT := hfixed.2 hhard.2
  have hpoint : (I.pairDescendant hq SG.output ST.output).cycle.point=I.cycle.point := by
    funext i
    by_cases hiG : i=G
    · subst i; exact hG.1
    by_cases hiT : i=T
    · subst i; exact hT.1
    have hi : i∈anchorVertices := by
      fin_cases i <;> simp [anchorVertices,H,G,A,B,T,D,E] at hiG hiT ⊢
    exact (ha i hi).1
  have htheta : (I.pairDescendant hq SG.output ST.output).cycle.theta=I.cycle.theta := by
    funext i
    by_cases hiG : i=G
    · subst i; exact hG.2
    by_cases hiT : i=T
    · subst i; exact hT.2
    have hi : i∈anchorVertices := by
      fin_cases i <;> simp [anchorVertices,H,G,A,B,T,D,E] at hiG hiT ⊢
    exact (ha i hi).2
  have hext : ∀ C D : SignedCycle, C.point=D.point → C.theta=D.theta → C=D := by
    rintro ⟨p,t⟩ ⟨p',t'⟩ h1 h2
    simp only at h1 h2
    subst h1 h2
    rfl
  exact hext _ _ hpoint htheta

end SignedCycle.BoundaryInput

namespace SignedCycle.NormalizedBoundaryInput

end SignedCycle.NormalizedBoundaryInput
end SquaresInCircles.Eight
end
end
end
