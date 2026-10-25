module

public import SquaresInCircles.Eight.Words.Second.Mixed.Edge.ThreePositiveUpper
public import SquaresInCircles.Eight.Words.Second.Mixed.TransverseSupportWide
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.SourceThreeEarly
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.SourceThreeLateShape
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.SourceThreePrimary
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.SourceThreeSupport
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoCycle

/-!
# Eight squares: original-cycle and reflected positive-source role-three rows

All weak owner choices and both original core pieces pass unchanged
to the completed scalar estimate. Reflection supplies the exact role-five
negative-outer to negative-core counterpart.
-/

section
/-!
## The two endpoints of the late affine dividing curve

Only its left endpoint needs a trigonometric reference. Its aligned
derivative follows from concavity on a fixed physical target interval.
All radical comparisons use exact rational interval algebra.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Late
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio)
open StationaryPrimitives (Interval)
open OppositeThree.ReferenceAlgebra

private lemma r48_mpr_lo {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).lo=S.lo := by subst e; rfl
private lemma r48_mpr_hi {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).hi=S.hi := by subst e; rfl

private lemma r48_shifted_eq {y : ℝ} : U y=Real.sqrt (Q0-(y+1/2)^2) := by
  dsimp [U,ShortOuterOne.SameContact.arc]; ring
private lemma r48_shifted_lo {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).lo=(rootThree (radicand Y) s hs hr).lo :=
  r48_mpr_lo r48_shifted_eq (congrArg _ r48_shifted_eq) _
private lemma r48_shifted_hi {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).hi=(rootThree (radicand Y) s hs hr).hi :=
  r48_mpr_hi r48_shifted_eq (congrArg _ r48_shifted_eq) _

private lemma r48_coordinate_eq {y : ℝ} : ShortOuterOne.SameContact.arc y=U y-1/2 := by
  dsimp [U]; ring
private lemma r48_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).lo=(Y.sub (Interval.point (1/2))).lo :=
  r48_mpr_lo r48_coordinate_eq (congrArg _ r48_coordinate_eq) _
private lemma r48_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).hi=(Y.sub (Interval.point (1/2))).hi :=
  r48_mpr_hi r48_coordinate_eq (congrArg _ r48_coordinate_eq) _

local macro "late_reference" : tactic => `(tactic|
  norm_num [PrimarySupport.sinBox,PrimarySupport.cosBox,r48_shifted_lo,r48_shifted_hi,radicand,rootThree,rootStep,
    r48_coordinate_lo,r48_coordinate_hi,ratioBox,firstBox,LLabel,RoleLabel.eval,Q0,cut,g,e,EdgeThreeAligned.gp,EdgeThreeAligned.ep,
    HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,
    HighOrderTaylor.C12,sin9,sin7,cos10,cos8,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.inv,Interval.div])

lemma left_reference : 0<f (13/10) ∧ 0<D (13/10) := by
  let S := PrimarySupport.sinBox (x := (13/10:ℝ)) (by norm_num)
  let C := PrimarySupport.cosBox (x := (13/10:ℝ)) (by norm_num)
  let X := shifted (Interval.point (cut (13/10))) (7/4) (by norm_num) (by late_reference)
  have hX : 0<X.lo := by dsimp [X]; late_reference
  let R := ratioBox (Interval.point (cut (13/10))) X hX
  let J := firstBox LLabel (Interval.point (cut (13/10))) X hX
  let F₀ := ((Interval.point (1/2)).add (((Interval.point 1).sub X).mul S)).add
    ((Interval.point (cut (13/10)+1/2)).mul C)
  let D₀ : Interval (D (13/10)) := ((Interval.point g).mul ((R.mul S).add C)).sub J
  have hf : 0<F₀.lo := by dsimp [F₀,X,S,C]; late_reference
  have hd : 0<D₀.lo := by dsimp [D₀,J,R,X,S,C]; late_reference
  constructor
  · have hh := hf.trans_le F₀.mem.1
    convert hh using 1
    dsimp [f,source,U]
    ring
  · exact hd.trans_le D₀.mem.1

lemma reference_794 : 0<FB (397/500) (Real.pi/2) := by
  let X := shifted (Interval.point (397/500:ℝ)) (3/2) (by norm_num) (by late_reference)
  have hX : 0<X.lo := by dsimp [X]; late_reference
  let R := ratioBox (Interval.point (397/500:ℝ)) X hX
  let J := firstBox LLabel (Interval.point (397/500:ℝ)) X hX
  let D₀ := ((Interval.point g).mul R).sub J
  have hd : 0<D₀.lo := by dsimp [D₀,J,R,X]; late_reference
  have hh := hd.trans_le D₀.mem.1
  simpa [FB] using hh

lemma terminal_derivative : 0<D (Real.pi/2) := by
  have hlo : (13/20:ℝ)≤cut (Real.pi/2) := by dsimp [cut]; linarith [pi_hand_enclosure.1]
  have hhi := (cut_bounds terminal_angle).2.le
  have hleft : (13/20:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hright : (397/500:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hh := (FB_concave (Real.pi/2)).min_le_of_mem_Icc hleft hright ⟨hlo,hhi⟩
  exact (lt_min Primary.reference_65 reference_794).trans_le hh

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Late
end
end
end

section
/-!
## Every late positive-core transverse owner

Below the affine dividing curve the label envelope pays the required
cost directly. Above it, the concave target derivative leaves only the
dividing point and the diagonal. Both endpoints are proved on the whole
angle interval. The actual source and target are unchanged.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Late
open CommonQuarter CorePairGeometry Arithmetic

lemma source_positive {φ : ℝ} (hφ : φ∈angles) : 0<f φ := by
  have hh := MinimumCalculus.endpoint_minimum hφ
    (fun θ hθ => f_hasDerivAt hθ) (fun θ hθ => f1_hasDerivAt hθ)
    (fun θ hθ => f2_hasDerivAt hθ) (fun θ hθ => (source_third_positive hθ).le)
    terminal_source_slope
  exact (lt_min left_reference.1 terminal_source).trans_le hh

lemma derivative_positive {φ : ℝ} (hφ : φ∈angles) : 0<D φ := by
  have hc : ConcaveOn ℝ angles D :=
    concave_of_deriv2 (fun θ hθ => D_hasDerivAt hθ) (fun θ hθ => D1_hasDerivAt hθ)
      (fun θ hθ => (derivative_second_negative hθ).le)
  exact concave_gt_of_endpoints hc hφ left_reference.2 terminal_derivative

lemma dividing_identity (φ : ℝ) : φ-e-111/1000-(69/100)*cut φ=γ := by
  dsimp [cut,e,γ,EdgeThreeAligned.ep,EdgeThreeAligned.threshold]
  ring

lemma dividing_value {φ : ℝ} (hφ : φ∈angles) : γ<F (cut φ) φ := by
  have hb := cut_bounds hφ
  have hL := MixedLEnvelopes.late_transverse
    (show cut φ∈Icc (0:ℝ) (397/500) from ⟨by linarith [hb.1],hb.2.le⟩)
  have hp := mul_nonneg (by norm_num [g,EdgeThreeAligned.gp] : 0≤g) (source_positive hφ).le
  have he := dividing_identity φ
  dsimp [F,f] at *
  linarith

theorem original {b A B φ : ℝ} (hb : 0≤b) (ht : OuterState A B) (hφ : φ∈angles)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤b+A*Real.sin φ-B*Real.cos φ) : γ<value b B φ := by
  have hB := NegativeTwo.source_mem ht
  by_cases he : B≤cut φ
  · have hL := MixedLEnvelopes.late_transverse
      (show B∈Icc (0:ℝ) (397/500) from ⟨hB.1,he.trans (cut_bounds hφ).2.le⟩)
    have hp := mul_nonneg (by norm_num [g,EdgeThreeAligned.gp] : 0≤g) hb
    have hi := dividing_identity φ
    dsimp [value,EdgeThreeAligned.positiveCost]
    linarith
  · have hdom {y : ℝ} (hy : y∈Icc (cut φ) outerDiagonal) : y∈Icc 0 outerDiagonal :=
      ⟨(cut_domain hφ).1.trans hy.1,hy.2⟩
    have hh := MinimumCalculus.endpoint_minimum_of_third_nonpos
      (f := fun y => F y φ) (d := fun y => FB y φ) (dd := fun y => FBB y φ)
      (ddd := fun y => FBBB y φ)
      (show B∈Icc (cut φ) outerDiagonal from ⟨by linarith,hB.2⟩)
      (fun y hy => F_hasDerivAt (hdom hy)) (fun y hy => FB_hasDerivAt (hdom hy))
      (fun y hy => FBB_hasDerivAt (hdom hy)) (fun y hy => (FBBB_negative (φ := φ) (hdom hy)).le)
      (derivative_positive hφ)
    have hlo := (lt_min (dividing_value hφ) (PositiveSource.diagonal_lower (lower_mem hφ))).trans_le hh
    exact hlo.trans_le (PositiveSource.original_lower ht hsep)

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Late
end
end
end

section
/-!
## All original positive-core to positive-outer role-three owners

The complete lower primary and transverse estimates are joined with
the upper finite aligned comparison. The remaining axes are excluded
at their original signed projections, including every weak tie.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig lower_width)

theorem original {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 1 φ) : γ<value b B φ := by
  have hcore := CoreAngleEndpoint.state_bounds hs
  by_cases hlo : φ≤Real.pi/2
  · have hlow : Lower φ := ⟨by dsimp [lowerAngle]; linarith [(abs_le.mp hφ).1],hlo⟩
    have htr := lower_trig hlow
    have hwidth : (1:ℝ)≤(1+Real.sin φ+Real.cos φ)/2 := by linarith [htr.2.2.2.2]
    fin_cases j
    · have hsep : (1+Real.sin φ+Real.cos φ)/2≤b+A*Real.sin φ-B*Real.cos φ := by
        norm_num [Eight.forwardMargin,lower_width hlow] at hm
        linarith
      by_cases he : φ≤13/10
      · exact Early.original ht ⟨hlow.1,he⟩ hsep
      · exact Late.original hcore.2.2.1 ht ⟨by linarith,hlo⟩ hsep
    · apply Primary.original hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    · have hlarge : 1≤a*Real.sin φ+b*Real.cos φ := by
        norm_num [Eight.forwardMargin,lower_width hlow] at hm
        linarith [ht.1]
      have he : (a*Real.sin φ+b*Real.cos φ)^2+(a*Real.cos φ-b*Real.sin φ)^2=a^2+b^2 := by
        linear_combination (a^2+b^2)*(Real.sin_sq_add_cos_sq φ)
      have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlarge 2
      nlinarith [core_radius_sq hs,sq_nonneg (a*Real.cos φ-b*Real.sin φ)]
    · have hAc := mul_nonneg (show 0≤A by linarith [ht.1,ht.2.1]) htr.2.2.1
      have hBs := mul_nonneg ht.1 (show 0≤Real.sin φ by linarith [htr.1])
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith [hcore.2.1]
  · let x := φ-Real.pi/2
    have hx : x∈Icc (0:ℝ) (7/10) := ⟨by dsimp [x]; linarith,
      by dsimp [x]; exact (abs_le.mp hφ).2⟩
    have hφeq : φ=Real.pi/2+x := by dsimp [x]; ring
    rw [hφeq] at hm ⊢
    exact EdgeThreeAligned.positive_upper_original hs ht hx j hm

theorem literal {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 1 φ) :
    SecondWord.threshold 3<cost 3 kind .outer true true a b A B φ := by
  rw [threshold_value,core_outer_positive_positive hk ht]
  exact original hs ht hφ j hm

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

def Role (i : Vertex) (source target : RadialKind) (σ τ : Bool) : Prop :=
  (i=3 ∧ source≠.outer ∧ target=.outer ∧ σ=true ∧ τ=true) ∨
  (i=5 ∧ source=.outer ∧ target≠.outer ∧ σ=false ∧ τ=false)

theorem original_role {i : Vertex} {source target : RadialKind} {σ τ : Bool}
    (hrole : Role i source target σ τ)
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign τ) φ) :
    SecondWord.threshold i<cost i source target σ τ a b A B φ := by
  rcases hrole with ⟨rfl,hk,rfl,rfl,rfl⟩ | ⟨rfl,rfl,hk,rfl,rfl⟩
  · exact literal hk (by simpa [State,hk] using hs) (by simpa [State] using ht)
      hφ j (by simpa [WordProblems.sign] using hm)
  · have hs' : OuterState a b := by simpa [State] using hs
    have ht' : CoreState A B := by simpa [State,hk] using ht
    have heq := margin_reflection j a b A B (-1) (-1) φ
    have hrev : 0≤Eight.forwardMargin (reflectedOwner j) A B a b 1 1 φ := by
      norm_num at heq
      rw [heq]
      simpa [WordProblems.sign] using hm
    have hh := literal hk ht' hs' hφ (reflectedOwner j) hrev
    have he := cost_reflection (3:Vertex) target .outer true true A B a b φ
    norm_num [reverseEdge] at he
    rw [←he] at hh
    simpa only [threshold_value] using hh

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : Role i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i)))
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    SecondWord.threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hrole with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> norm_num [WordProblems.wrongWord]
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  exact original_role hrole (actual_state C i) (actual_state C (next i)) hφ j
    (original_margin C F hgap i j howner)

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : Role i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i))) :
    SecondWord.threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hrole j howner

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource
end
end
end
