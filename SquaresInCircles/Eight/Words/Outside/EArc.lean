module

public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: the actual E radial arcs used by the outside transport

Feasible EH1 below a primary smaller than one forces a
true-core E onto its flat arc. The other radial kind is E's own actual outer
q-circle. All arc coordinates, derivatives, sorting and circle values below
are proved from these original radial kinds.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace OutsideE

inductive ArcKind where
  | flatCore
  | outerCircle

def ArcKind.primary (kind : ArcKind) (q b : ℝ) : ℝ :=
  match kind with
  | .flatCore => 7/12
  | .outerCircle => Real.sqrt (q-(b+1/2)^2)-1/2

def ArcKind.point (kind : ArcKind) (q b : ℝ) : SignedPoint :=
  ⟨kind.primary q b,-b⟩

def ArcKind.slope (kind : ArcKind) (q b : ℝ) : ℝ :=
  match kind with
  | .flatCore => 0
  | .outerCircle => (b+1/2)/Real.sqrt (q-(b+1/2)^2)

structure ArcSource (q : ℝ) (E : SignedPoint) (kind : ArcKind) : Prop where
  sorted : E.Sorted
  nonpos : E.y≤0
  flat : kind=.flatCore → E.a=7/12 ∧ -E.y<9/40
  outer : kind=.outerCircle → E.Outer q

theorem core_eh1_flat {H E : SignedPoint} {p : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEc : E.Core)
    (hHa : H.a<1) (hp : p∈Icc 0 (7/10 : ℝ))
    (hf : quarterFeasible E H p 1) : E.a=7/12 ∧ -E.y<9/40 := by
  have hEa := SignedPoint.core_primary_le hEs hEc
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hp
  have hw := edgeWidth_positive_formula hp
  have hfeas : (1+Real.cos p+Real.sin p)/2≤
      H.a+E.a*Real.sin p+E.y*Real.cos p := by
    simpa [quarterFeasible,quarterProjection,hw] using hf
  have hmul := mul_le_mul_of_nonneg_right hEa hs0
  have hb : -E.y<9/40 := by
    by_contra! hbad
    have hlo := mul_lt_mul_of_pos_left hc (show (0:ℝ)<29/40 by norm_num)
    have hcmp := mul_le_mul_of_nonneg_right
      (show (29/40 : ℝ)≤ -E.y+1/2 by linarith) (by linarith : 0≤Real.cos p)
    nlinarith
  have habs : |E.y|≤1/2 := by rw [abs_of_nonpos hEy]; linarith
  exact ⟨(SignedPoint.flat_core_iff hEs habs).1 hEc,hb⟩

theorem arcSource_of_boundary {q p : ℝ} {H E : SignedPoint}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEr : E.Boundary q)
    (hHa : H.a<1) (hp : p∈Icc 0 (7/10 : ℝ))
    (hf : quarterFeasible E H p 1) : ∃ kind, ArcSource q E kind := by
  rcases hEr with ho | hc
  · exact ⟨.outerCircle,⟨hEs,hEy,(by intro h; cases h),fun _ => ho⟩⟩
  · exact ⟨.flatCore,⟨hEs,hEy,fun _ => core_eh1_flat hEs hEy hc hHa hp hf,
      (by intro h; cases h)⟩⟩

theorem ArcKind.continuous_primary (kind : ArcKind) (q : ℝ) :
    Continuous (kind.primary q) := by
  cases kind
  · exact continuous_const
  · show Continuous (fun b : ℝ => Real.sqrt (q-(b+1/2)^2)-1/2)
    fun_prop

theorem ArcSource.initial {q : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) : kind.point q (-E.y)=E := by
  have ha : kind.primary q (-E.y)=E.a := by
    cases kind with
    | flatCore => exact (I.flat rfl).1.symm
    | outerCircle =>
      have ho := I.outer rfl
      have heq : q-(-E.y+1/2)^2=(E.a+1/2)^2 := by
        simp only [SignedPoint.Outer,SignedPoint.circle,abs_of_nonpos I.nonpos] at ho
        linarith
      dsimp [ArcKind.primary]
      rw [heq,Real.sqrt_sq_eq_abs,abs_of_pos (by linarith [I.sorted.1] : 0<E.a+1/2)]
      ring
  unfold ArcKind.point
  rw [ha,neg_neg]

theorem ArcSource.geometry {q b : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hq : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    (kind.point q b).Sorted ∧ (kind.point q b).Contained q ∧
      (kind.point q b).AvoidsCore ∧ (kind.point q b).Boundary q ∧
      (kind.point q b).circle≤E.circle ∧
      1/2<kind.primary q b ∧ b≤kind.primary q b := by
  cases kind with
  | flatCore =>
    obtain ⟨hEa,hEb⟩ := I.flat rfl
    have hbsmall : |-b|≤1/2 := by rw [abs_neg,abs_of_nonneg hb.1]; linarith [hb.2]
    have hs := SignedPoint.flat_sorted hbsmall
    have hc := SignedPoint.flat_contained hq hbsmall
    have hcore := SignedPoint.flat_on_core hbsmall
    have hloss : (SignedPoint.flat (-b)).circle≤E.circle := by
      have hbsq := pow_le_pow_left₀ (show 0≤b+1/2 by linarith [hb.1])
        (show b+1/2≤ -E.y+1/2 by linarith [hb.2]) 2
      simpa [SignedPoint.circle,SignedPoint.flat,hEa,abs_of_nonpos I.nonpos,
        abs_neg,abs_of_nonneg hb.1] using add_le_add_left hbsq ((13/12 : ℝ)^2)
    exact ⟨hs,hc,hcore.ge,Or.inr hcore,hloss,by norm_num [ArcKind.primary],by
      dsimp [ArcKind.primary]; linarith [hb.2]⟩
  | outerCircle =>
    have hediag := SignedPoint.contained_minor_le_diagonal I.sorted (I.outer rfl).le
    have hbdiag : |-b|≤diagonalCoordinate q := by
      rw [abs_neg,abs_of_nonneg hb.1]
      exact hb.2.trans (by simpa [abs_of_nonpos I.nonpos] using hediag)
    have heq : ArcKind.outerCircle.point q b=SignedPoint.outerAt q (-b) := by
      simp [ArcKind.point,ArcKind.primary,SignedPoint.outerAt,
        abs_neg,abs_of_nonneg hb.1]
    obtain ⟨hs,ho,hcore⟩ := SignedPoint.outerAt_spec hq hbdiag
    rw [heq]
    have hprim : 1/2<(SignedPoint.outerAt q (-b)).a :=
      SignedPoint.primary_gt_half hs hcore
    have hsort : b≤(SignedPoint.outerAt q (-b)).a := by
      simpa [SignedPoint.outerAt,abs_neg,abs_of_nonneg hb.1] using hs.2
    exact ⟨hs,ho.le,hcore,Or.inl ho,ho.trans (I.outer rfl).symm |>.le,
      by simpa [SignedPoint.outerAt,ArcKind.primary,abs_neg,abs_of_nonneg hb.1] using hprim,
      by simpa [SignedPoint.outerAt,ArcKind.primary,abs_neg,abs_of_nonneg hb.1] using hsort⟩

theorem ArcSource.derivative {q b : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hq : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (kind.primary q) (-kind.slope q b) b ∧
      0≤kind.slope q b ∧ kind.slope q b≤1 := by
  cases kind with
  | flatCore =>
    refine ⟨?_,by show (0:ℝ) ≤ 0; exact le_rfl,by show (0:ℝ) ≤ 1; norm_num⟩
    show HasDerivAt (fun _ : ℝ => (7/12:ℝ)) (-0) b
    rw [neg_zero]
    exact hasDerivAt_const b _
  | outerCircle =>
    have hgeom := I.geometry hq hb
    have hroot : 0<Real.sqrt (q-(b+1/2)^2) := by
      have hh := hgeom.2.2.2.2.2.1
      dsimp [ArcKind.primary] at hh
      linarith
    have hrad : 0<q-(b+1/2)^2 := Real.sqrt_pos.mp hroot
    have hd := ((hasDerivAt_const b q).fun_sub
      (((hasDerivAt_id' b).add_const (1/2)).fun_pow 2)).sqrt hrad.ne'
    refine ⟨?_,?_,?_⟩
    · convert hd.sub_const (1/2) using 1
      · rfl
      · show -((b+1/2)/Real.sqrt (q-(b+1/2)^2))=_
        field_simp
        push_cast
        ring
    · exact div_nonneg (by linarith [hb.1]) hroot.le
    · apply (div_le_one hroot).2
      have hh := hgeom.2.2.2.2.2.2
      dsimp [ArcKind.primary] at hh
      linarith

theorem ArcSource.radial_identity {q b : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hq : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    (kind=.flatCore ∧ kind.slope q b=0 ∧ b≤1/2) ∨
      b-kind.slope q b*kind.primary q b= -(1-kind.slope q b)/2 := by
  cases kind with
  | flatCore =>
    exact Or.inl ⟨rfl,rfl,by linarith [(I.flat rfl).2,hb.2]⟩
  | outerCircle =>
    right
    have hg := I.geometry hq hb
    have hr : 0<Real.sqrt (q-(b+1/2)^2) := by
      have hh := hg.2.2.2.2.2.1
      dsimp [ArcKind.primary] at hh
      linarith
    dsimp only [ArcKind.slope,ArcKind.primary]
    generalize Real.sqrt (q-(b+1/2)^2)=r at hr ⊢
    field_simp
    ring

def ehSlack (kind : ArcKind) (q : ℝ) (H : SignedPoint) (p b : ℝ) : ℝ :=
  H.a-1/2+(kind.primary q b-1/2)*Real.sin p-(b+1/2)*Real.cos p

def de3Slack (kind : ArcKind) (q α : ℝ) (D : SignedPoint) (p b : ℝ) : ℝ :=
  D.a-1/2-(kind.primary q b+1/2)*Real.sin (p-α)+(b-1/2)*Real.cos (p-α)

def de2Slack (D : SignedPoint) (α p b : ℝ) : ℝ :=
  (D.a-1/2)*Real.cos (p-α)+(D.y-1/2)*Real.sin (p-α)+b-1/2

theorem ehSlack_actual (kind : ArcKind) (q : ℝ) (H : SignedPoint) {p : ℝ} (b : ℝ)
    (hp : p∈Icc 0 (7/10 : ℝ)) :
    ehSlack kind q H p b=quarterProjection (kind.point q b) H p 1-edgeWidth p := by
  rw [edgeWidth_positive_formula hp]
  simp [ehSlack,quarterProjection,ArcKind.point] <;> ring

theorem de3Slack_actual (kind : ArcKind) (q α : ℝ) (D : SignedPoint) {p : ℝ} (b : ℝ)
    (hn : p-α∈Icc 0 (7/10 : ℝ)) :
    de3Slack kind q α D p b=
      quarterProjection D (kind.point q b) (-(p-α)) 3-edgeWidth (-(p-α)) := by
  rw [edgeWidth_negative_formula hn]
  simp only [de3Slack,quarterProjection,ArcKind.point,Matrix.cons_val,Real.sin_neg,
    Real.cos_neg]
  ring

theorem de2Slack_actual (kind : ArcKind) (q α : ℝ) (D : SignedPoint) {p : ℝ} (b : ℝ)
    (hn : p-α∈Icc 0 (7/10 : ℝ)) :
    de2Slack D α p b=
      quarterProjection D (kind.point q b) (-(p-α)) 2-edgeWidth (-(p-α)) := by
  rw [edgeWidth_negative_formula hn]
  simp only [de2Slack,quarterProjection,ArcKind.point,Matrix.cons_val,Real.sin_neg,
    Real.cos_neg]
  ring

end OutsideE
end SquaresInCircles.Eight
