module

public import SquaresInCircles.Eight.Owners.Canonical.NegativeSharp
public import SquaresInCircles.Eight.Owners.Negative.Capture

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
