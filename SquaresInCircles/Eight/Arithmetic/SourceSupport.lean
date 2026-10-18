module

public import SquaresInCircles.Eight.Arithmetic.PreparedArc

/-!
# Exact source-state elimination

The source coefficients are constant after reversing axes 2 and 3.  The
support mode is selected solely by rational comparisons whose implications
are proved here.  Each branch yields a lower bound for every state in the
original tangent arc; it does not select a representative state.
-/

@[expose] public section

namespace SquaresInCircles.Eight.Arithmetic

structure SourceSupport where
  arc : PreparedArc
  X : ℚ
  Y : ℚ
  normRoot : QInterval
  deriving DecidableEq, Repr

namespace SourceSupport

def atLo (S : SourceSupport) : ScalarExpr 0 :=
  .add (.mul (.const S.X) S.arc.aLo) (.mul (.const S.Y) S.arc.bLo)
def atHi (S : SourceSupport) : ScalarExpr 0 :=
  .add (.mul (.const S.X) S.arc.aHi) (.mul (.const S.Y) S.arc.bHi)
def slopeLo (S : SourceSupport) : ScalarExpr 0 :=
  .sub (.const S.Y) (.mul (.const S.X) S.arc.ratioLo)
def slopeHi (S : SourceSupport) : ScalarExpr 0 :=
  .sub (.const S.Y) (.mul (.const S.X) S.arc.ratioHi)
def normExpr (S : SourceSupport) : ScalarExpr 0 := .sqrt (.const (S.X^2+S.Y^2)) S.normRoot
def onCircle (S : SourceSupport) : ScalarExpr 0 :=
  .sub (.const (S.arc.data.shift*(S.X+S.Y))) (.mul S.arc.radiusExpr S.normExpr)

def mode (S : SourceSupport) : SupportMode :=
  if S.arc.data.side || decide (0 ≤ S.X) then .endpoints
  else if 0 ≤ (S.slopeLo.range closedBoxes).lo ∧ 0 ≤ (S.slopeHi.range closedBoxes).lo then .lower
  else if (S.slopeLo.range closedBoxes).hi ≤ 0 ∧ (S.slopeHi.range closedBoxes).hi ≤ 0 then .upper
  else .circle

def lower (S : SourceSupport) : ℚ :=
  match S.mode with
  | .endpoints => min (S.atLo.range closedBoxes).lo (S.atHi.range closedBoxes).lo
  | .lower => (S.atLo.range closedBoxes).lo
  | .upper => (S.atHi.range closedBoxes).lo
  | .circle => (S.onCircle.range closedBoxes).lo

def Valid (S : SourceSupport) : Prop :=
  S.arc.NumericValid ∧ S.normExpr.Valid closedBoxes

instance (S : SourceSupport) : Decidable S.Valid := by unfold Valid; infer_instance

theorem atLo_valid {S : SourceSupport} (hS : S.Valid) : S.atLo.Valid closedBoxes :=
  ⟨⟨True.intro,hS.1.2.2.1⟩,⟨True.intro,S.arc.bLo_valid hS.1⟩⟩
theorem atHi_valid {S : SourceSupport} (hS : S.Valid) : S.atHi.Valid closedBoxes :=
  ⟨⟨True.intro,hS.1.2.2.2.1⟩,⟨True.intro,S.arc.bHi_valid hS.1⟩⟩
theorem onCircle_valid {S : SourceSupport} (hS : S.Valid) : S.onCircle.Valid closedBoxes :=
  ⟨True.intro,⟨hS.1.2.2.2.2.1,hS.2⟩⟩

theorem slopeLo_valid {S : SourceSupport} (hS : S.Valid) (hs : S.arc.data.side=false) :
    S.slopeLo.Valid closedBoxes := ⟨True.intro,⟨True.intro,(hS.1.2.2.2.2.2 hs).1⟩⟩
theorem slopeHi_valid {S : SourceSupport} (hS : S.Valid) (hs : S.arc.data.side=false) :
    S.slopeHi.Valid closedBoxes := ⟨True.intro,⟨True.intro,(hS.1.2.2.2.2.2 hs).2⟩⟩

theorem ratioLo_value {S : SourceSupport} {x y : ℝ}
    (hf : S.arc.CircleFacts x y) (hs : S.arc.data.side=false) :
    S.arc.ratioLo.value = circleRatio S.arc.data.shift S.arc.radiusExpr.value S.arc.bLo.value := by
  have he := circle_branch hf.lower_shift hf.lower_circle
  simp only [PreparedArc.ratioLo,hs,if_false]
  change (S.arc.bLo.value-(S.arc.data.shift : ℝ))/(S.arc.aLo.value-(S.arc.data.shift : ℝ)) = _
  rw [he]
  simp [circleX,circleRatio]

theorem ratioHi_value {S : SourceSupport} {x y : ℝ}
    (hf : S.arc.CircleFacts x y) (hs : S.arc.data.side=false) :
    S.arc.ratioHi.value = circleRatio S.arc.data.shift S.arc.radiusExpr.value S.arc.bHi.value := by
  have he := circle_branch hf.upper_shift hf.upper_circle
  simp only [PreparedArc.ratioHi,hs,if_false]
  change (S.arc.bHi.value-(S.arc.data.shift : ℝ))/(S.arc.aHi.value-(S.arc.data.shift : ℝ)) = _
  rw [he]
  simp [circleX,circleRatio]

theorem endpoints_sound {S : SourceSupport} (hS : S.Valid)
    {x y m : ℝ} (hxy : S.arc.data.Contains S.arc.radius x y)
    (hmode : S.arc.data.side=true ∨ 0 ≤ S.X)
    (hl : m ≤ S.atLo.value) (hu : m ≤ S.atHi.value) :
    m ≤ (S.X : ℝ)*x+(S.Y : ℝ)*y := by
  have hd := S.arc.supportDomain hS.1 hxy
  cases hs : S.arc.data.side with
  | true =>
      have hx : x=7/12 := by simpa [PreparedArc.SupportDomain,hs] using hd.2.2
      have hL : S.arc.aLo.value=7/12 := by
        simp [PreparedArc.aLo,PreparedArc.endpointExpr,hs,ScalarExpr.value,ScalarExpr.eval]
      have hU : S.arc.aHi.value=7/12 := by
        simp [PreparedArc.aHi,PreparedArc.endpointExpr,hs,ScalarExpr.value,ScalarExpr.eval]
      apply side_endpoint_lower ⟨hd.1,hd.2.1⟩
      · simpa [atLo,ScalarExpr.value,ScalarExpr.eval,hL,hx] using hl
      · simpa [atHi,ScalarExpr.value,ScalarExpr.eval,hU,hx] using hu
  | false =>
      have hX : (0 : ℝ) ≤ S.X := by
        exact_mod_cast hmode.resolve_left (by simp [hs])
      have hf := S.arc.circleFacts hS.1 hs hxy
      have hdc : x=circleX S.arc.data.shift S.arc.radiusExpr.value y ∧
          (∀ z ∈ Set.Icc S.arc.bLo.value S.arc.bHi.value,
            0 < S.arc.radiusExpr.value^2-(z-(S.arc.data.shift : ℝ))^2) := by
        simpa [PreparedArc.SupportDomain,hs] using hd.2.2
      have hL := circle_branch hf.lower_shift hf.lower_circle
      have hU := circle_branch hf.upper_shift hf.upper_circle
      rw [hdc.1]
      apply circle_endpoints_lower hX hdc.2 ⟨hd.1,hd.2.1⟩
      · simpa [atLo,ScalarExpr.value,ScalarExpr.eval,hL] using hl
      · simpa [atHi,ScalarExpr.value,ScalarExpr.eval,hU] using hu

/-- The exact source lower bound, for every real state on the declared arc. -/
theorem sound {S : SourceSupport} (hS : S.Valid) {x y : ℝ}
    (hxy : S.arc.data.Contains S.arc.radius x y) :
    (S.lower : ℝ) ≤ (S.X : ℝ)*x+(S.Y : ℝ)*y := by
  have hl := S.atLo.closed_sound (atLo_valid hS)
  have hu := S.atHi.closed_sound (atHi_valid hS)
  by_cases hep : S.arc.data.side || decide (0 ≤ S.X)
  · have hm : S.mode=.endpoints := by simp [mode,hep]
    have hp : S.arc.data.side=true ∨ 0 ≤ S.X := by simpa using hep
    have hlq : S.lower ≤ (S.atLo.range closedBoxes).lo := by
      simp [lower,hm]
    have huq : S.lower ≤ (S.atHi.range closedBoxes).lo := by
      simp [lower,hm]
    exact endpoints_sound hS hxy hp
      ((by exact_mod_cast hlq).trans hl.1) ((by exact_mod_cast huq).trans hu.1)
  · have hs : S.arc.data.side=false := by
      cases h : S.arc.data.side <;> simp [h] at hep ⊢
    have hd := S.arc.supportDomain hS.1 hxy
    have hf := S.arc.circleFacts hS.1 hs hxy
    have hdc : x=circleX S.arc.data.shift S.arc.radiusExpr.value y ∧
        (∀ z ∈ Set.Icc S.arc.bLo.value S.arc.bHi.value,
          0 < S.arc.radiusExpr.value^2-(z-(S.arc.data.shift : ℝ))^2) := by
      simpa [PreparedArc.SupportDomain,hs] using hd.2.2
    have hL := circle_branch hf.lower_shift hf.lower_circle
    have hU := circle_branch hf.upper_shift hf.upper_circle
    have hdl := S.slopeLo.closed_sound (slopeLo_valid hS hs)
    have hdu := S.slopeHi.closed_sound (slopeHi_valid hS hs)
    by_cases hdpos : 0 ≤ (S.slopeLo.range closedBoxes).lo ∧ 0 ≤ (S.slopeHi.range closedBoxes).lo
    · have hm : S.mode=.lower := by simp [mode,hep,hdpos]
      have hpL : 0 ≤ (S.Y : ℝ)-(S.X : ℝ)*circleRatio S.arc.data.shift S.arc.radiusExpr.value S.arc.bLo.value := by
        have hh : (0 : ℝ) ≤ (S.slopeLo.range closedBoxes).lo := by exact_mod_cast hdpos.1
        have hp := hh.trans hdl.1
        simpa [slopeLo,ScalarExpr.value,ScalarExpr.sub,ScalarExpr.eval,ratioLo_value hf hs] using hp
      have hpU : 0 ≤ (S.Y : ℝ)-(S.X : ℝ)*circleRatio S.arc.data.shift S.arc.radiusExpr.value S.arc.bHi.value := by
        have hh : (0 : ℝ) ≤ (S.slopeHi.range closedBoxes).lo := by exact_mod_cast hdpos.2
        have hp := hh.trans hdu.1
        simpa [slopeHi,ScalarExpr.value,ScalarExpr.sub,ScalarExpr.eval,ratioHi_value hf hs] using hp
      have hh := circle_lower_endpoint hdc.2 ⟨hd.1,hd.2.1⟩ hpL hpU
      have hstart : (S.lower : ℝ) ≤ (S.X : ℝ)*S.arc.aLo.value+(S.Y : ℝ)*S.arc.bLo.value := by
        simpa [lower,hm,atLo,ScalarExpr.value,ScalarExpr.eval] using hl.1
      simpa [← hL,← hdc.1] using hstart.trans hh
    · by_cases hdneg : (S.slopeLo.range closedBoxes).hi ≤ 0 ∧ (S.slopeHi.range closedBoxes).hi ≤ 0
      · have hm : S.mode=.upper := by simp [mode,hep,hdpos,hdneg]
        have hpL : (S.Y : ℝ)-(S.X : ℝ)*circleRatio S.arc.data.shift S.arc.radiusExpr.value S.arc.bLo.value ≤ 0 := by
          have hh : ((S.slopeLo.range closedBoxes).hi : ℝ) ≤ 0 := by exact_mod_cast hdneg.1
          have hp := hdl.2.trans hh
          simpa [slopeLo,ScalarExpr.value,ScalarExpr.sub,ScalarExpr.eval,ratioLo_value hf hs] using hp
        have hpU : (S.Y : ℝ)-(S.X : ℝ)*circleRatio S.arc.data.shift S.arc.radiusExpr.value S.arc.bHi.value ≤ 0 := by
          have hh : ((S.slopeHi.range closedBoxes).hi : ℝ) ≤ 0 := by exact_mod_cast hdneg.2
          have hp := hdu.2.trans hh
          simpa [slopeHi,ScalarExpr.value,ScalarExpr.sub,ScalarExpr.eval,ratioHi_value hf hs] using hp
        have hh := circle_upper_endpoint hdc.2 ⟨hd.1,hd.2.1⟩ hpL hpU
        have hstart : (S.lower : ℝ) ≤ (S.X : ℝ)*S.arc.aHi.value+(S.Y : ℝ)*S.arc.bHi.value := by
          simpa [lower,hm,atHi,ScalarExpr.value,ScalarExpr.eval] using hu.1
        simpa [← hU,← hdc.1] using hstart.trans hh
      · have hm : S.mode=.circle := by simp [mode,hep,hdpos,hdneg]
        have hc := S.onCircle.closed_sound (onCircle_valid hS)
        have hr : 0 ≤ S.arc.radiusExpr.value := by
          rw [PreparedArc.radiusExpr_value]
          split_ifs <;> positivity
        have hh := full_circle_lower hr hf.point_circle (X := S.X) (Y := S.Y)
        have hc' : (S.lower : ℝ) ≤ (S.arc.data.shift : ℝ)*((S.X : ℝ)+S.Y)-
            S.arc.radiusExpr.value*Real.sqrt ((S.X : ℝ)^2+(S.Y : ℝ)^2) := by
          simpa [lower,hm,onCircle,normExpr,ScalarExpr.value,ScalarExpr.sub,ScalarExpr.eval] using hc.1
        exact hc'.trans hh

end SourceSupport
end SquaresInCircles.Eight.Arithmetic
