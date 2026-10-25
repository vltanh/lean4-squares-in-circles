module

public import SquaresInCircles.Eight.Words.Outside.EArc
public import SquaresInCircles.Eight.Owners.TrueCoreEArc

/-!
# Eight squares: the arcs of E for any contained anchor H

A sorted boundary E with `E.y ≤ 0` lies on one of two arcs (`ArcKind`, `arcSource_of_boundary`):
the core, curved part included, unlike in the short two-negative transport, or the outer circle of
the radius `q` itself. The common interface `ArcSource` gives, for both radial kinds, the point of
E on its arc and the comparison with the corner circle (`ArcSource.initial`, `ArcSource.geometry`,
`ArcSource.radial_identity`); the primary decreases along the arc (`ArcSource.primary_antitone`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace FullE

inductive ArcKind where
  | trueCore
  | outerCircle

def ArcKind.primary (kind : ArcKind) (q b : ℝ) : ℝ :=
  match kind with
  | .trueCore => TrueCoreE.primary b
  | .outerCircle => OutsideE.ArcKind.outerCircle.primary q b

def ArcKind.slope (kind : ArcKind) (q b : ℝ) : ℝ :=
  match kind with
  | .trueCore => TrueCoreE.slope b
  | .outerCircle => OutsideE.ArcKind.outerCircle.slope q b

def ArcKind.point (kind : ArcKind) (q b : ℝ) : SignedPoint :=
  ⟨kind.primary q b,-b⟩

structure ArcSource (q : ℝ) (E : SignedPoint) (kind : ArcKind) : Prop where
  sorted : E.Sorted
  nonpos : E.y≤0
  core : kind=.trueCore → E.Core
  outer : kind=.outerCircle → E.Outer q

theorem arcSource_of_boundary {q : ℝ} {E : SignedPoint}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEr : E.Boundary q) :
    ∃ kind, ArcSource q E kind := by
  rcases hEr with ho | hc
  · exact ⟨.outerCircle,⟨hEs,hEy,(by intro h; cases h),fun _ => ho⟩⟩
  · exact ⟨.trueCore,⟨hEs,hEy,fun _ => hc,(by intro h; cases h)⟩⟩

theorem ArcKind.continuous_primary (kind : ArcKind) (q : ℝ) :
    Continuous (kind.primary q) := by
  cases kind with
  | trueCore => exact TrueCoreE.continuous_primary
  | outerCircle => exact OutsideE.ArcKind.continuous_primary .outerCircle q

theorem ArcSource.initial {q : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) : kind.point q (-E.y)=E := by
  cases kind with
  | trueCore => exact (TrueCoreE.Source.mk I.sorted I.nonpos (I.core rfl)).initial
  | outerCircle =>
    let J : OutsideE.ArcSource q E .outerCircle :=
      ⟨I.sorted,I.nonpos,(by intro h; cases h),fun _ => I.outer rfl⟩
    exact J.initial

theorem ArcSource.geometry {q b : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hq : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    (kind.point q b).Sorted ∧ (kind.point q b).Contained q ∧
      (kind.point q b).AvoidsCore ∧ (kind.point q b).Boundary q ∧
      (kind.point q b).circle≤E.circle ∧
      1/2<kind.primary q b ∧ b≤kind.primary q b := by
  cases kind with
  | trueCore =>
    let J : TrueCoreE.Source E := ⟨I.sorted,I.nonpos,I.core rfl⟩
    have hg := J.geometry hb
    have hbs : b≤TrueCoreE.primary b := by
      simpa [TrueCoreE.point,abs_neg,abs_of_nonneg hb.1] using hg.1.2
    exact ⟨hg.1,J.contained hq hb,hg.2.1.ge,Or.inr hg.2.1,
      J.circle_nonincrease hb,hg.2.2.2.1,hbs⟩
  | outerCircle =>
    let J : OutsideE.ArcSource q E .outerCircle :=
      ⟨I.sorted,I.nonpos,(by intro h; cases h),fun _ => I.outer rfl⟩
    exact J.geometry hq hb

theorem ArcSource.derivative {q b : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hq : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (kind.primary q) (-kind.slope q b) b ∧
      0≤kind.slope q b ∧ kind.slope q b≤1 := by
  cases kind with
  | trueCore => exact (TrueCoreE.Source.mk I.sorted I.nonpos (I.core rfl)).derivative hb
  | outerCircle =>
    let J : OutsideE.ArcSource q E .outerCircle :=
      ⟨I.sorted,I.nonpos,(by intro h; cases h),fun _ => I.outer rfl⟩
    exact J.derivative hq hb

theorem ArcSource.radial_identity {q b : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hq : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    (kind.slope q b=0 ∧ b≤1/2) ∨
      b-kind.slope q b*kind.primary q b=(1-kind.slope q b)/2 ∨
      b-kind.slope q b*kind.primary q b= -(1-kind.slope q b)/2 := by
  cases kind with
  | trueCore =>
    rcases (TrueCoreE.Source.mk I.sorted I.nonpos (I.core rfl)).radial_identity hb with hf | hc
    · exact Or.inl hf
    · exact Or.inr (Or.inl hc)
  | outerCircle =>
    let J : OutsideE.ArcSource q E .outerCircle :=
      ⟨I.sorted,I.nonpos,(by intro h; cases h),fun _ => I.outer rfl⟩
    rcases J.radial_identity hq hb with ⟨hbad,_,_⟩ | hr
    · cases hbad
    · exact Or.inr (Or.inr hr)

theorem ArcSource.primary_antitone {q : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hqL : qLow≤q) :
    AntitoneOn (kind.primary q) (Icc 0 (-E.y)) := by
  apply antiOn_of_hasDeriv_nonpos (kind.continuous_primary q).continuousOn
  · intro b hb
    exact (I.derivative hqL (Ioo_subset_Icc_self hb)).1
  · intro b hb
    exact neg_nonpos.mpr (I.derivative hqL (Ioo_subset_Icc_self hb)).2.1

theorem ArcSource.mixed_projection_mono {q b p : ℝ} {E H : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind) (hqL : qLow≤q)
    (hb : b∈Icc 0 (-E.y)) (hp : p∈Icc 0 (7/10 : ℝ))
    (j : Fin 4) (hj : j=0 ∨ j=1) :
    quarterProjection E H p j≤quarterProjection (kind.point q b) H p j := by
  have hEa : E.a≤kind.primary q b := by
    have hh := I.primary_antitone hqL hb
      (show -E.y∈Icc 0 (-E.y) from ⟨neg_nonneg.mpr I.nonpos,le_rfl⟩) hb.2
    have heq : kind.primary q (-E.y)=E.a := congrArg SignedPoint.a I.initial
    rwa [heq] at hh
  have ht := transport_trig hp
  rcases hj with rfl | rfl
  · simp only [quarterProjection,Matrix.cons_val_zero,ArcKind.point]
    linarith [hb.2]
  · have hprim := mul_nonneg (sub_nonneg.mpr hEa) ht.2.2.1
    have htan := mul_nonneg (show 0≤ -E.y-b by linarith [hb.2])
      (show 0≤Real.cos p by linarith [ht.1])
    simp [quarterProjection,ArcKind.point]
    linarith

end FullE
end SquaresInCircles.Eight
