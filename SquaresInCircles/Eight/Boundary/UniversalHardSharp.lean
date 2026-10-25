module

public import SquaresInCircles.Eight.Words.Crossed.ClampMotionCycle
public import SquaresInCircles.Eight.Words.Crossed.ClampTerminal

/-!
# Eight squares: sharpness of the hard inputs

A hard input at a level `qLow ≤ q ≤ qStar` is sharp (`HardInput.hard_sharp`): `q = qStar`, A and
B have a common frame with `yA - yB = 1`, G has the frame of H, B, T, D and E have a common frame,
the turn `θH - θD` is the angle of `FiveCorner.selected`, the five anchors lie on the circle of
squared radius `qStar`, and every terminal owner of every edge is tight.

The middle conditions `θA = θB`, `yA - yB = 1` and `θT ≤ θA ≤ θG` come first
(`canonical_hard_sharp`). Under them the outer frames are ordered, `θA ≤ θH` and `θD ≤ θB`
(`canonical_hard_outer_order`), and `ordered_hard_sharp` concludes. A crossed order gives a hard
input with a common-frame entry, which the common clamp at the level `q` excludes through the
strict losses of the middle anchors (`common_frame_entry_impossible`; on the side of T the clamp
is built for the reflected geometry and reflected back,
`reflected_common_frame_entry_impossible`). The side with the larger tangent, `yA ≥ 1/2` or
`-yB ≥ 1/2`, is ordered first; its upper bound then puts the other tangent in `[67/200, 1/2]`,
where the small crossed case applies (`crossed_large_HG_impossible`,
`crossed_small_HG_impossible` and their counterparts for T–D). Every hard input satisfies the
middle conditions (`hard_middle`): its canonical middle (`canonicalize_middle`) is sharp, so its
anchors lie on the circle of `qStar`, and a defect of the middle of the input would give one of
its anchors a strict loss against that circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCycle
open Candidate Stationary GeometricModel

theorem HardInput.common_frame_entry_impossible {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar) (C : CommonFrameEntry I.outerGeometry) : False := by
  have hcap : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨O⟩ := I.outerGeometry.common_clamp_data hqL hcap C
  exact I.crossed_clamp_endpoint_impossible hqL hq C.H_before.le O

/-- A common-frame entry of the reflected outer geometry is impossible: the clamp is built for
the reflected geometry, reflected back to the side of T, and excluded on the hard input itself,
with its own E. -/
theorem HardInput.reflected_common_frame_entry_impossible {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (C : CommonFrameEntry I.outerGeometry.reflected) : False := by
  have hcap : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨O⟩ := I.outerGeometry.reflected.common_clamp_data hqL hcap C
  have O' : CrossedClampData q (I.cycle.point D).reflect (I.cycle.point G).reflect
      0 (I.cycle.theta G-I.cycle.theta D) := by
    change CrossedClampData q (I.cycle.point D).reflect (I.cycle.point G).reflect
      0 ((I.cycle.theta B-I.cycle.theta D)-(I.cycle.theta B-I.cycle.theta G)) at O
    convert O using 1 <;> ring
  have hBD : I.cycle.theta B≤I.cycle.theta D := by
    have hh := C.H_before
    change I.cycle.theta B-I.cycle.theta D<I.cycle.theta B-I.cycle.theta B at hh
    linarith
  exact I.crossed_TD_clamp_endpoint_impossible hqL hq hBD O'.reflectTD

theorem HardInput.crossed_large_HG_impossible {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A) (hlarge : 1/2≤(I.cycle.point A).y) : False := by
  obtain ⟨O,C⟩ := I.crossed_HG_large_entry hqL (hq.trans qStar_limits.2.2.le)
    hAB hnorm hTA hAG hHA hlarge
  exact (I.fromCrossedGAData hAB O).common_frame_entry_impossible hqL hq C

theorem HardInput.crossed_small_HG_impossible {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hsmall : (I.cycle.point A).y∈Icc (67/200:ℝ) (1/2)) : False := by
  obtain ⟨O,C⟩ := I.crossed_HG_small_entry hqL (hq.trans qStar_limits.2.2.le)
    hAB hnorm hTA hAG hHA hsmall
  exact (I.fromCrossedGAData hAB O).common_frame_entry_impossible hqL hq C

theorem HardInput.crossed_large_TD_impossible {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hBD : I.cycle.theta B<I.cycle.theta D) (hlarge : 1/2≤ -(I.cycle.point B).y) : False := by
  obtain ⟨O,C⟩ := I.crossed_TD_large_entry hqL (hq.trans qStar_limits.2.2.le)
    hAB hnorm hTA hAG hBD hlarge
  exact (I.fromCrossedBTData hAB O).reflected_common_frame_entry_impossible hqL hq C

theorem HardInput.crossed_small_TD_impossible {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hBD : I.cycle.theta B<I.cycle.theta D)
    (hsmall : -(I.cycle.point B).y∈Icc (67/200:ℝ) (1/2)) : False := by
  obtain ⟨O,C⟩ := I.crossed_TD_small_entry hqL (hq.trans qStar_limits.2.2.le)
    hAB hnorm hTA hAG hBD hsmall
  exact (I.fromCrossedBTData hAB O).reflected_common_frame_entry_impossible hqL hq C

/-- Under the middle conditions the outer frames are ordered: `θA ≤ θH` and `θD ≤ θB`. The side
with the larger tangent is ordered first, and its upper bound puts the other tangent in
`[67/200, 1/2]`, so no bound on that tangent is assumed. -/
theorem HardInput.canonical_hard_outer_order {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G) :
    I.cycle.theta A≤I.cycle.theta H ∧ I.cycle.theta D≤I.cycle.theta B := by
  have hcap : q≤qCap := hq.trans qStar_limits.2.2.le
  have hTB : I.cycle.theta T≤I.cycle.theta B := by rw [←hAB]; exact hTA
  by_cases hlargeA : 1/2≤(I.cycle.point A).y
  · have hAH : I.cycle.theta A≤I.cycle.theta H := by
      by_contra! hHA
      exact I.crossed_large_HG_impossible hqL hq hAB hnorm hTA hAG hHA hlargeA
    have hG := I.large_middle_G_negative hcap hAB hnorm hTA hAG hlargeA
    have hAy := I.ordered_large_A_upper hqL hcap hAH hAG hG.le hlargeA
    have hsmallB : -(I.cycle.point B).y∈Icc (67/200:ℝ) (1/2) := by
      constructor <;> linarith
    refine ⟨hAH,?_⟩
    by_contra! hBD
    exact I.crossed_small_TD_impossible hqL hq hAB hnorm hTA hAG hBD hsmallB
  · have hlargeB : 1/2≤ -(I.cycle.point B).y := by linarith
    have hDB : I.cycle.theta D≤I.cycle.theta B := by
      by_contra! hBD
      exact I.crossed_large_TD_impossible hqL hq hAB hnorm hTA hAG hBD hlargeB
    have hT := I.large_middle_T_positive hcap hAB hnorm hTA hAG hlargeB
    have hBy := I.ordered_large_B_upper hqL hcap hDB hTB hT.le hlargeB
    have hsmallA : (I.cycle.point A).y∈Icc (67/200:ℝ) (1/2) := by
      constructor <;> linarith
    refine ⟨?_,hDB⟩
    by_contra! hHA
    exact I.crossed_small_HG_impossible hqL hq hAB hnorm hTA hAG hHA hsmallA

theorem HardInput.canonical_hard_sharp {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G) :
    I.cycle.theta A=I.cycle.theta B ∧
      (I.cycle.point A).y-(I.cycle.point B).y=1 ∧
      q=qStar ∧ I.cycle.theta G=I.cycle.theta H ∧
      I.cycle.theta B=I.cycle.theta T ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  obtain ⟨hAH,hDB⟩ := I.canonical_hard_outer_order hqL hq hAB hnorm hTA hAG
  exact I.ordered_hard_sharp hqL hq hAB hnorm hAH hAG hDB (by rw [←hAB]; exact hTA)

/-- Every hard input at a level in `[qLow, qStar]` satisfies the middle conditions `θA = θB`,
`θT ≤ θA ≤ θG` and `yA - yB = 1`: a defect would give one of its anchors a strict loss against
its sharp canonical middle, whose anchors lie on the circle of `qStar`. -/
theorem HardInput.hard_middle {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar) :
    I.cycle.theta A=I.cycle.theta B ∧
      I.cycle.theta A∈Icc (I.cycle.theta T) (I.cycle.theta G) ∧
      (I.cycle.point A).y-(I.cycle.point B).y=1 := by
  have hcap : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨J,hJAB,hJrange,hJnorm,hnon,hstrict,hfixed⟩ := I.canonicalize_middle hcap
  have hG := hfixed G (by decide) (by decide)
  have hT := hfixed T (by decide) (by decide)
  have hJAG : J.cycle.theta A≤J.cycle.theta G := by rw [hG.2]; exact hJrange.2
  have hJTA : J.cycle.theta T≤J.cycle.theta A := by rw [hT.2]; exact hJrange.1
  obtain ⟨_,_,_,_,_,_,_,_,hJon,_⟩ := J.canonical_hard_sharp hqL hq hJAB hJnorm hJTA hJAG
  have hnoloss : ¬StrictAnchorLoss I.cycle J.cycle :=
    no_strict_loss_to_on_circle (fun i _ => (I.necessary.contained i).trans hq) hJon
  have hAB : I.cycle.theta A=I.cycle.theta B := by
    by_contra hne
    exact hnoloss (hstrict (Or.inl hne))
  have hTA : I.cycle.theta T≤I.cycle.theta A := by
    by_contra! hbad
    exact hnoloss (hstrict (Or.inr (Or.inl hbad)))
  have hAG : I.cycle.theta A≤I.cycle.theta G := by
    by_contra! hbad
    exact hnoloss (hstrict (Or.inr (Or.inr (Or.inl hbad))))
  have hsum : (I.cycle.point A).y-(I.cycle.point B).y≤1 := by
    by_contra! hbad
    exact hnoloss (hstrict (Or.inr (Or.inr (Or.inr hbad))))
  exact ⟨hAB,⟨hTA,hAG⟩,le_antisymm hsum (I.aligned_AB_gap hAB)⟩

/-- A hard input at a level in `[qLow, qStar]` is sharp: `q = qStar`, the frames and the turn of
the optimal configuration, the anchors on the circle of `qStar` and every terminal owner tight.
Nothing is assumed about its middle, its tangents, the signs of G and T, the order of its outer
frames or the signs of the errors of H–G and T–D. -/
theorem HardInput.hard_sharp {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar) :
    I.cycle.theta A=I.cycle.theta B ∧
      (I.cycle.point A).y-(I.cycle.point B).y=1 ∧
      q=qStar ∧ I.cycle.theta G=I.cycle.theta H ∧
      I.cycle.theta B=I.cycle.theta T ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  obtain ⟨hAB,hrange,hnorm⟩ := I.hard_middle hqL hq
  exact I.canonical_hard_sharp hqL hq hAB hnorm hrange.1 hrange.2

end SquaresInCircles.Eight.SignedCycle
