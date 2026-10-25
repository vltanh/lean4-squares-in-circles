module

public import SquaresInCircles.Eight.Boundary.SourceRecovery
public import SquaresInCircles.Eight.Owners.Canonical.NegativeSharp
public import SquaresInCircles.Eight.Owners.Negative.Capture
public import SquaresInCircles.Eight.Owners.Ordered.CancelingSplit
public import SquaresInCircles.Eight.Words.Aligned.GAEndpointStress

/-!
# Eight squares: sharpness of the canonical negative hard cycle

A hard input on the canonical negative branch, at a radius `q ≤ d.q` below a stationary
configuration `d`, is that configuration: `q = d.q`, the frames of B, T, D agree, the H–D angle is
`coordinateAngle d`, and the anchors A, B, D, E, H, with B, D, E reflected, are the nominal points
of `d` (`HardInput.nonpositive_canonical_rigidity`). The five contacts of the stress identity come
from the weak axes of the hard input; the identity uses a scalar reflection of B, D, E only, and
the anchor points, their circles and the contact owners are those of the input.

The contacts exclude zero total tilt, and the negative capture bounds the error below `3/200`, so
the theorem needs neither a local angle assumption nor a stationary box.
-/

section
/-!
## The actual delta-zero hard branch reaches the geometric endpoint

The common frame shift below preserves every signed
point and every original SAT slack.  It is used only to express an actual
two-frame endpoint in the convention of the five-corner theorem.

For an aligned hard chain with E in D's frame, the same-radius hard split
has two possible endpoints.  The actual GA--DE endpoint is impossible;
the surviving endpoint is the geometric five-corner chain.  Strict losses
on the original A/B circles exclude an interior source split at equality.
No circle equality is assumed of either free intermediate.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate GeometricModel Stationary
namespace SignedCycle

/-- A common physical rotation, leaving all own-frame coordinates literal. -/
def shiftFrame (C : SignedCycle) (r : ℝ) : SignedCycle where
  point := C.point
  theta i := C.theta i-r

@[simp] theorem shiftFrame_point (C : SignedCycle) (r : ℝ) (i : Vertex) :
    (C.shiftFrame r).point i=C.point i := rfl

theorem shiftFrame_delta (C : SignedCycle) (r : ℝ) (i : Vertex) :
    delta (C.shiftFrame r).theta i=delta C.theta i := by
  dsimp [shiftFrame,delta]
  ring

@[simp] theorem shiftFrame_slack (C : SignedCycle) (r : ℝ)
    (i : Vertex) (j : Fin 4) : (C.shiftFrame r).slack i j=C.slack i j := by
  simp only [slack,shiftFrame_delta,edge,shiftFrame_point]

@[simp] theorem shiftFrame_feasible (C : SignedCycle) (r : ℝ)
    (i : Vertex) (j : Fin 4) :
    (C.shiftFrame r).Feasible i j ↔ C.Feasible i j := by
  simp only [Feasible,shiftFrame_slack]

theorem canonical_shift_theta {C : SignedCycle}
    (hHG : C.theta G=C.theta H) (hAB : C.theta A=C.theta B)
    (hTD : C.theta T=C.theta D) (hAD : C.theta A=C.theta D)
    (hED : C.theta E=C.theta D) :
    (C.shiftFrame (C.theta D)).theta=
      SourceRecovery.endpointTheta (C.theta H-C.theta D) := by
  have hBD : C.theta B=C.theta D := hAB.symm.trans hAD
  simp only [H,G,A,B,T,D,E] at hHG hAB hTD hAD hED hBD
  funext i
  fin_cases i <;>
    simp [shiftFrame,SourceRecovery.endpointTheta,H,D,hHG,hBD,hTD,hAD,hED]

/-- Select the actual hard axes and retain the original weak zero owners.
The only additional mixed axis needed here is the original EH1 witness. -/
def canonicalOwner {C : SignedCycle} (w : C.Witnesses) : Vertex → Fin 4 :=
  ![w.owner H,0,w.owner A,2,w.owner T,w.owner D,1]

theorem canonicalOwner_allowed {C : SignedCycle} (w : C.Witnesses) :
    ∀ i,canonicalOwner w i∈terminalOwners i := by
  intro i
  have hH := w.allowed H
  have hA := w.allowed A
  have hT := w.allowed T
  have hD := w.allowed D
  fin_cases i
  · simpa [canonicalOwner,normalOwners,terminalOwners,H,G,A,B,T,D,E] using hH
  · simp [canonicalOwner,terminalOwners,H,A,T,D]
  · simpa [canonicalOwner,normalOwners,terminalOwners,H,G,A,B,T,D,E] using hA
  · simp [canonicalOwner,terminalOwners,H,A,T,D]
  · simpa [canonicalOwner,normalOwners,terminalOwners,H,G,A,B,T,D,E] using hT
  · simpa [canonicalOwner,normalOwners,terminalOwners,H,G,A,B,T,D,E] using hD
  · simp [canonicalOwner,terminalOwners,H,A,T,D]

theorem HardInput.canonicalOwner_feasible {q : ℝ} (I : HardInput q)
    (hEH : I.cycle.Feasible E 1) :
    ∀ i,I.cycle.Feasible i (canonicalOwner I.witnesses i) := by
  intro i
  fin_cases i
  · exact I.witnesses.feasible H
  · exact I.GA_hard
  · exact I.witnesses.feasible A
  · exact I.BT_hard
  · exact I.witnesses.feasible T
  · exact I.witnesses.feasible D
  · exact hEH

theorem HardInput.canonical_tilt {q : ℝ} (I : HardInput q)
    (horder : I.cycle.theta D≤I.cycle.theta H) :
    0≤I.cycle.theta H-I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D≤Real.pi/4 := by
  have hs := (abs_le.mp (I.necessary.spread H D)).2
  refine ⟨sub_nonneg.mpr horder,?_⟩
  dsimp [frameCap] at hs
  linarith [Real.pi_gt_three]

theorem HardInput.canonical_lower_bound {q : ℝ} (I : HardInput q)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hAD : I.cycle.theta A=I.cycle.theta D)
    (hED : I.cycle.theta E=I.cycle.theta D)
    (horder : I.cycle.theta D≤I.cycle.theta H)
    (hEH : I.cycle.Feasible E 1) : qStar≤q := by
  exact SourceRecovery.endpoint_lower_bound (I.canonical_tilt horder)
    (canonical_shift_theta hHG hAB hTD hAD hED)
    I.necessary.sorted I.necessary.contained (canonicalOwner I.witnesses)
    (canonicalOwner_allowed I.witnesses)
    (fun i => (shiftFrame_feasible _ _ _ _).2 (I.canonicalOwner_feasible hEH i))

/-- The endpoint conclusions concern the source's own five anchor circles
and its own signed slacks, because the common shift changes neither. -/
theorem HardInput.canonical_sharp {q : ℝ} (I : HardInput q)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hAD : I.cycle.theta A=I.cycle.theta D)
    (hED : I.cycle.theta E=I.cycle.theta D)
    (horder : I.cycle.theta D≤I.cycle.theta H)
    (hEH : I.cycle.Feasible E 1) (hq : q≤qStar) :
    q=qStar ∧ I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  have htheta := canonical_shift_theta hHG hAB hTD hAD hED
  have ht := I.canonical_tilt horder
  have hp := canonicalOwner_allowed I.witnesses
  have hf : ∀ i,(I.cycle.shiftFrame (I.cycle.theta D)).Feasible i
      (canonicalOwner I.witnesses i) :=
    fun i => (shiftFrame_feasible _ _ _ _).2 (I.canonicalOwner_feasible hEH i)
  have hslack := SourceRecovery.endpoint_all_slacks_zero ht htheta
    I.necessary.sorted I.necessary.contained (canonicalOwner I.witnesses) hp hf hq
  have hcircle := SourceRecovery.endpoint_all_anchors_on ht htheta
    I.necessary.sorted I.necessary.contained (canonicalOwner I.witnesses) hp hf hq
  refine ⟨le_antisymm hq (I.canonical_lower_bound hHG hAB hTD hAD hED horder hEH),
    hslack.1,hcircle,?_⟩
  intro i j hj
  simpa only [shiftFrame_slack] using hslack.2 i j hj

/-- Split the actual A/B pair while retaining H, D, E and their two mixed
contacts.  The other split endpoint is excluded at the original qCap. -/
theorem HardInput.delta_zero_canonical_split {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A)
    (hED : I.cycle.theta E=I.cycle.theta D)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) :
    ∃ J : HardInput q,
      J.cycle.theta G=J.cycle.theta H ∧
      J.cycle.theta A=J.cycle.theta B ∧
      J.cycle.theta T=J.cycle.theta D ∧
      J.cycle.theta A=J.cycle.theta D ∧
      J.cycle.theta E=J.cycle.theta D ∧
      J.cycle.theta D≤J.cycle.theta H ∧
      J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta A<I.cycle.theta H ∧ I.cycle.theta D<I.cycle.theta A →
        StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧
        J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨J,hend,hJAB,hnon,hstrict,hfixed⟩ :=
    I.split_with_source_loss hq hHG hAB.symm hTD
      (by simpa [hHG] using hleft) (by simpa [hTD] using hright)
  have hH := hfixed H (by decide) (by decide)
  have hG := hfixed G (by decide) (by decide)
  have hT := hfixed T (by decide) (by decide)
  have hD := hfixed D (by decide) (by decide)
  have hE := hfixed E (by decide) (by decide)
  have hJHG : J.cycle.theta G=J.cycle.theta H := by rw [hG.2,hH.2,hHG]
  have hJTD : J.cycle.theta T=J.cycle.theta D := by rw [hT.2,hD.2,hTD]
  have hJED : J.cycle.theta E=J.cycle.theta D := by rw [hE.2,hD.2,hED]
  have hJorder : J.cycle.theta D≤J.cycle.theta H := by
    rw [hD.2,hH.2]
    exact hright.trans hleft
  have hJDE : J.cycle.Feasible D 3 := by
    have e : J.cycle.slack D 3=I.cycle.slack D 3 := by
      simp only [slack,edge,delta,show next D=E from rfl,hD.1,hD.2,hE.1,hE.2]
    rw [Feasible,e]
    exact hDE
  have hJEH : J.cycle.Feasible E 1 := by
    have e : J.cycle.slack E 1=I.cycle.slack E 1 := by
      simp only [slack,edge,delta,show next E=H from rfl,hE.1,hE.2,hH.1,hH.2]
    rw [Feasible,e]
    exact hEH
  have hJAD : J.cycle.theta A=J.cycle.theta D := by
    rcases hend with h | h
    · have hAH := h.trans hJHG
      exact (J.aligned_GA_DE_impossible hq hJHG hJAB hJTD hAH hJED
        (by simpa [hAH] using hJorder) hJDE hJEH).elim
    · exact h.trans hJTD
  refine ⟨J,hJHG,hJAB,hJTD,hJAD,hJED,hJorder,hJDE,hJEH,hnon,?_,hfixed⟩
  intro hi
  apply hstrict
  simpa [hHG,hTD] using hi

/-- Equality is pulled back to the unchanged source frame data.  An
interior source split would strictly reduce an original A/B circle, whereas
the actual endpoint's five circles are all qStar. -/
theorem HardInput.delta_zero_sharp {q : ℝ} (I : HardInput q) (hq : q≤qStar)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A)
    (hED : I.cycle.theta E=I.cycle.theta D)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) :
    I.cycle.theta A=I.cycle.theta D ∧ q=qStar ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  have hQ : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨J,hG,hAB',hT,hAD,hED',ho,hD,hE,hnon,hstrict,hfixed⟩ :=
    I.delta_zero_canonical_split hQ hHG hAB hTD hleft hright hED hDE hEH
  have hsharp := J.canonical_sharp hG hAB' hT hAD hED' ho hE hq
  have hnoloss : ¬StrictAnchorLoss I.cycle J.cycle :=
    no_strict_loss_to_on_circle
      (fun i _ => (I.necessary.contained i).trans hq) hsharp.2.2.1
  have hADsource : I.cycle.theta A=I.cycle.theta D := by
    by_contra hne
    have hDA : I.cycle.theta D<I.cycle.theta A := lt_of_le_of_ne hright (Ne.symm hne)
    have hAH : I.cycle.theta A<I.cycle.theta H := by
      rcases lt_or_eq_of_le hleft with h | h
      · exact h
      · exact (I.aligned_GA_DE_impossible hQ hHG hAB hTD h hED hright hDE hEH).elim
    exact hnoloss (hstrict ⟨hAH,hDA⟩)
  exact ⟨hADsource,I.canonical_sharp hHG hAB hTD hADsource hED
    (hright.trans hleft) hEH hq⟩

end SignedCycle
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace SignedCycle
open Candidate PositiveCancelingOuter
open Stationary.FiveCornerGeometry StationaryTerminal

/-- A hard input on the canonical negative branch at `q ≤ d.q` is the stationary five-anchor
configuration `d`, in its own coordinates and with its own circle equalities. -/
theorem HardInput.nonpositive_canonical_rigidity {q : ℝ}
    (I : HardInput q) {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hqq : q≤d.q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hGHframe : I.cycle.theta G=I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hTD : I.cycle.Feasible T 2) (hBy : 1/2≤ -(I.cycle.point B).y)
    (hDEframe : I.cycle.theta E=I.cycle.theta D)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) :
    q=d.q ∧ I.cycle.theta B=I.cycle.theta T ∧
      I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=coordinateAngle d ∧
      AllAnchorsOn d.q I.cycle ∧
      ![I.cycle.point A,(I.cycle.point B).reflect,(I.cycle.point D).reflect,
          (I.cycle.point E).reflect,I.cycle.point H]=
        nominalPoints d.q (-d.y) (Real.tan (coordinateAngle d)) := by
  have hq : q≤qTrial := hqq.trans (GeometricExistence.stationary_radius_ceiling hd).le
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hHG := I.aligned_HG_zero hGHframe
  have hAG : I.cycle.theta A≤I.cycle.theta G := by rw [hGHframe]; exact hAH
  have hGH : I.cycle.theta G≤I.cycle.theta H := by rw [hGHframe]
  have hb := I.nonpositive_composite_bounds hcap hAB hAG hGH hDT hTB hHG hTD
  let t := I.cycle.theta B-I.cycle.theta T
  let e := I.cycle.theta T-I.cycle.theta D
  let u := I.cycle.theta H-I.cycle.theta A
  let α := I.cycle.theta H-I.cycle.theta D
  have ht : 0≤t := sub_nonneg.mpr hTB
  have he : 0≤e := sub_nonneg.mpr hDT
  have hu0 : 0≤u := sub_nonneg.mpr hAH
  have hsum : t+u+e=α := by dsimp [t,u,e,α]; rw [hAB]; ring
  have hu : t+e≤α := by linarith
  have hsmall := I.nonpositive_canonical_small_error hq hAB hAH hGHframe
    hDT hTB hTD hBy hDEframe hDE hEH
  have hr : t+e≤3/200 := by dsimp [t,e]; linarith
  have hα : α≤27/100 := hb.span_lt.le
  have hHF := I.negative_HG0_composite hcap hAG hGH hHG
  rw [hGHframe] at hHF
  have hHAu : 1+NegativeCaptureStress.W u≤
      (I.cycle.point A).a*Real.cos u-(I.cycle.point A).y*Real.sin u+
        (I.cycle.point H).y := by
    change 0≤NegativeNoncancelingBarrier.F (I.cycle.point H) (I.cycle.point A) u u at hHF
    simp only [NegativeNoncancelingBarrier.F,sub_self,Real.cos_zero,Real.sin_zero,
      mul_one,mul_zero,sub_zero] at hHF
    dsimp [V,NegativeCaptureStress.W,NegativeLargeDEStress.W] at *
    linarith
  have hHA : 1+CanonicalNegativeStress.W (α-t-e)≤
      (I.cycle.point H).y+(I.cycle.point A).a*Real.cos (α-t-e)-
        (I.cycle.point A).y*Real.sin (α-t-e) := by
    rw [show α-t-e=u by linarith]
    change 1+NegativeCaptureStress.W u≤_
    linarith
  have hABsum : 1≤(I.cycle.point A).y+(I.cycle.point B).reflect.y := by
    have hj : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
      simpa [normalOwners,A] using I.witnesses.allowed A
    have hf := I.witnesses.feasible A
    have hd : delta I.cycle.theta A=0 := by
      simp only [delta,show next A=B from rfl,hAB,sub_self]
    simp only [Feasible,slack,edge,hd,edgeWidth_zero,show word A=0 from rfl,
      ite_true,zeroProjection_aligned,show next A=B from rfl] at hf
    rcases hj with hj | hj <;>
      simp [hj,SignedPoint.reflect] at hf ⊢ <;> linarith
  have hDF := I.negative_TD2_composite hcap hDT hTB hTD
  have hBD0 : NegativeOuterEZero.demand (1-V (I.cycle.point B).reflect t) e≤
      (I.cycle.point D).reflect.y := by
    dsimp [NegativeNoncancelingBarrier.F] at hDF
    rw [show (I.cycle.theta B-I.cycle.theta D)-
      (I.cycle.theta B-I.cycle.theta T)=e by dsimp [e]; ring] at hDF
    change 0≤(I.cycle.point D).reflect.y-1/2+
      (V (I.cycle.point B).reflect t-1)*Real.cos e-(13/12)*Real.sin e at hDF
    dsimp [NegativeOuterEZero.demand]
    linarith
  have hBD := NegativeLargeDEStress.composite_secant
    (show t∈Icc 0 (27/100:ℝ) from ⟨ht,by linarith⟩)
    (show e∈Icc 0 (27/100:ℝ) from ⟨he,by linarith⟩) hBD0
  have hDEcontact : 1≤(I.cycle.point D).reflect.a+(I.cycle.point E).reflect.y := by
    have hf := hDE
    have hd : delta I.cycle.theta D=0 := by
      simp only [delta,show next D=E from rfl,hDEframe,sub_self]
    simp only [Feasible,slack,edge,hd,edgeWidth_zero,show word D=1 from rfl,
      show next D=E from rfl,quarterProjection_aligned] at hf
    simp [SignedPoint.reflect] at hf ⊢
    linarith
  have hEHcontact : CanonicalNegativeStress.W α≤
      (I.cycle.point H).a+(I.cycle.point E).reflect.a*Real.sin α-
        (I.cycle.point E).reflect.y*Real.cos α := by
    have hαdom : α∈Icc 0 (7/10:ℝ) := ⟨hb.span_nonneg,by linarith⟩
    have hh : edgeWidth α≤(I.cycle.point H).a+
        (I.cycle.point E).a*Real.sin α+(I.cycle.point E).y*Real.cos α := by
      have hf := hEH
      have hd : delta I.cycle.theta E=α := by
        show I.cycle.theta (next E)-I.cycle.theta E=α
        rw [hDEframe]
        rfl
      simp only [Feasible,slack,edge,hd,show word E=1 from rfl,
        show next E=H from rfl] at hf
      simp [quarterProjection] at hf
      linarith
    rw [edgeWidth_positive_formula hαdom] at hh
    simpa [CanonicalNegativeStress.W,NegativeCaptureStress.W,
      NegativeLargeDEStress.W,SignedPoint.reflect] using hh
  have hαpos : 0<α := by
    by_contra! hzero
    have hz : α=0 := le_antisymm hzero hb.span_nonneg
    have hsumupper := hb.primary_sum
    change (I.cycle.point H).a+(I.cycle.point D).a<
      1248/625-(359/500)*Real.sin α at hsumupper
    rw [hz,Real.sin_zero,mul_zero,sub_zero] at hsumupper
    have hEH0 := hEHcontact
    rw [hz] at hEH0
    norm_num [CanonicalNegativeStress.W,NegativeCaptureStress.W,
      NegativeLargeDEStress.W,SignedPoint.reflect] at hEH0
    dsimp [SignedPoint.reflect] at hDEcontact
    linarith
  have hcircles : ∀i : Fin 5,
      (![I.cycle.point A,(I.cycle.point B).reflect,(I.cycle.point D).reflect,
        (I.cycle.point E).reflect,I.cycle.point H] i).Contained q := by
    intro i
    fin_cases i
    · simpa using I.necessary.contained A
    · simpa using I.necessary.contained B
    · simpa using I.necessary.contained D
    · simpa using I.necessary.contained E
    · simpa using I.necessary.contained H
  obtain ⟨hqq',ht0,he0,hangle,hcircle,hpoints⟩ :=
    CanonicalNegativeSharp.five_anchor_rigidity
      (H:=I.cycle.point H) (A:=I.cycle.point A) (B:=(I.cycle.point B).reflect)
      (D:=(I.cycle.point D).reflect) (E:=(I.cycle.point E).reflect)
      hd hqq hαpos hα ht he hr hu I.anchors_normal.H_nonneg I.anchors_normal.A_nonneg
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.B_nonpos)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.D_nonpos)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.E_nonpos)
      hcircles hHA hABsum hBD hDEcontact hEHcontact
  refine ⟨hqq',?_,?_,hangle,?_,hpoints⟩
  · dsimp [t] at ht0
    linarith
  · dsimp [e] at he0
    linarith
  · intro i hi
    simp only [anchorVertices,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · simpa using hcircle (4 : Fin 5)
    · simpa using hcircle (0 : Fin 5)
    · simpa using hcircle (1 : Fin 5)
    · simpa using hcircle (2 : Fin 5)
    · simpa using hcircle (3 : Fin 5)

end SignedCycle
end SquaresInCircles.Eight
end
end
end
