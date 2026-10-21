module

public import SquaresInCircles.Eight.TableFree.ZeroPrimaryMarkers
public import SquaresInCircles.Eight.TableFree.ZeroPrimaryPolynomial

/-!
# The boosted original zero-primary cost

The original primary inequality determines the allowed angle, tangent
sign and radial choice. A multiplier cancels the actual source transverse
coordinate on the whole core or outer chart. The target circle support
then is precisely one of the two proved polynomial supports.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.ZeroPrimary

open FramePair CommonQuarter

lemma source_support (s : FramePair.State) (core : Bool)
    (hcore : core=true ↔ s.branch.type=0) {d : ℝ} (hd : d∈Icc (9/20) (7/10)) :
    ((ZeroPrimaryPolynomial.mass core:ℝ)/Real.sin d)*
        (ZeroPrimaryPolynomial.anchor core:ℝ)*Real.cos d≤
      unsigned s+((ZeroPrimaryPolynomial.mass core:ℝ)/Real.sin d)*s.a*Real.cos d-
        ((ZeroPrimaryPolynomial.mass core:ℝ)/Real.sin d)*s.b*Real.sin d := by
  let l : ℝ := (ZeroPrimaryPolynomial.mass core:ℝ)/Real.sin d
  have tr := positive_trig ⟨by linarith [hd.1],hd.2⟩
  have hsine : (2/5:ℝ)<Real.sin d := by
    have hh := (positive_taylor_reserves ⟨by linarith [hd.1],hd.2⟩).1
    linarith [hd.1]
  have hm : 0<(ZeroPrimaryPolynomial.mass core:ℝ) ∧
      (ZeroPrimaryPolynomial.mass core:ℝ)≤107/100 := by
    cases core <;> norm_num [ZeroPrimaryPolynomial.mass]
  have hl : 0<l := div_pos hm.1 (by linarith)
  have hls : l*Real.sin d=(ZeroPrimaryPolynomial.mass core:ℝ) :=
    div_mul_cancel₀ _ (by linarith)
  have hlU : l<3 := by
    have hh := mul_lt_mul_of_pos_left hsine hl
    nlinarith [hm.2]
  have hlc : l*Real.cos d<7 := by
    have hh := mul_le_mul_of_nonneg_left tr.2.1 hl.le
    linarith
  change l*(ZeroPrimaryPolynomial.anchor core:ℝ)*Real.cos d≤
    unsigned s+l*s.a*Real.cos d-l*s.b*Real.sin d
  cases core
  · have ho : s.branch.type≠0 := by
      intro hc
      have hh := hcore.mpr hc
      simp at hh
    have hmark := (outer_marker_bounds s ho).1
    have ha := (outer_bounds (outer_data s ho)).1
    have hac : (899/1000:ℝ)≤s.a := by linarith [fine_outer_endpoint_bounds.2]
    have hmul := mul_le_mul_of_nonneg_right hac
      (mul_nonneg hl.le (by linarith [tr.1] : 0≤Real.cos d))
    norm_num [ZeroPrimaryPolynomial.mass,ZeroPrimaryPolynomial.anchor] at hls ⊢
    nlinarith
  · have hc := hcore.mp rfl
    have hmark := core_marker_lower s hc
    have ha := (FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart s hc)).2.1
    have hprod := mul_nonneg (show 0≤7-l*Real.cos d by linarith)
      (show 0≤7/12-s.a by linarith)
    norm_num [ZeroPrimaryPolynomial.mass,ZeroPrimaryPolynomial.anchor] at hls ⊢
    nlinarith

/-- An actual target-primary zero edge has boosted cost above `.985`.
All G1 marker chart choices remain the ones supplied in the states. -/
theorem target_primary_boost (s t : FramePair.State) {d : ℝ} (hd : |d|≤7/10)
    (hg : (19/25:ℝ)<s.gap t d) (hm : s.Feasible t 1 d) :
    (197/200:ℝ)<d+s.signedLabel-t.signedLabel+(9/50)*frameCost |d| := by
  have hdom := target_primary_domain s t hd hg hm
  have hdi : d∈Icc (9/20) (7/10) := ⟨hdom.1.1.le,hdom.1.2⟩
  have hpositive : 0<d := by linarith [hdom.1.1]
  have tr := positive_trig ⟨hpositive.le,hdi.2⟩
  have hsin : 0<Real.sin d := by
    have hh := (positive_taylor_reserves ⟨hpositive.le,hdi.2⟩).1
    linarith
  have hslabel : s.signedLabel=unsigned s := by
    simp [FramePair.State.signedLabel,unsigned,hdom.2.1,FramePair.sign]
  have htlabel : t.signedLabel≤(2/5)*(t.a-FramePair.a0)+(111/100)*t.b :=
    (signed_upper t).trans (outer_marker_bounds t hdom.2.2.2.2).2
  have hm' : 0≤t.a-s.a*Real.cos d+s.b*Real.sin d-oneWidth d := by
    simpa [FramePair.State.Feasible,forwardMargin,hdom.2.1,FramePair.sign,
      signed_width hd,oneWidth] using hm
  have hcase (core : Bool) (hcore : core=true ↔ s.branch.type=0) :
      (197/200:ℝ)<d+s.signedLabel-t.signedLabel+(9/50)*frameCost |d| := by
    let l : ℝ := (ZeroPrimaryPolynomial.mass core:ℝ)/Real.sin d
    have hl : 0≤l := by
      dsimp [l]
      apply div_nonneg _ hsin.le
      cases core <;> norm_num [ZeroPrimaryPolynomial.mass]
    have hsource := source_support s core hcore hdi
    have htarget := outer_circle_lower (X := -(l+2/5)) (Y := -(111/100:ℝ))
      (outer_data t hdom.2.2.2.2)
    simp only [neg_sq] at htarget
    have hmargin := mul_nonneg hl hm'
    have hscalar := ZeroPrimaryPolynomial.support_gt core hdi
    change (197/200:ℝ)<d+(9/50)*frameCost d+
      l*(oneWidth d+(ZeroPrimaryPolynomial.anchor core:ℝ)*Real.cos d)+
        (2/5)*outerAxial+(l+2/5+111/100)/2-
          radius*Real.sqrt ((l+2/5)^2+(111/100)^2) at hscalar
    change l*(ZeroPrimaryPolynomial.anchor core:ℝ)*Real.cos d≤
      unsigned s+l*s.a*Real.cos d-l*s.b*Real.sin d at hsource
    rw [hslabel,abs_of_pos hpositive]
    change t.signedLabel≤(2/5)*(t.a-outerAxial)+(111/100)*t.b at htlabel
    nlinarith
  by_cases hc : s.branch.type=0
  · exact hcase true (by simp [hc])
  · exact hcase false (by simp [hc])

theorem source_primary_boost (s t : FramePair.State) {d : ℝ} (hd : |d|≤7/10)
    (hg : (19/25:ℝ)<s.gap t d) (hm : s.Feasible t 3 d) :
    (197/200:ℝ)<d+s.signedLabel-t.signedLabel+(9/50)*frameCost |d| := by
  have hrev : t.flip.Feasible s.flip 1 d := by
    simpa [FramePair.State.Feasible,FramePair.State.flip,forwardMargin,FramePair.sign_not,
      sub_eq_add_neg,mul_comm,mul_left_comm,mul_assoc,add_comm,add_left_comm,add_assoc] using hm
  have hh := target_primary_boost t.flip s.flip hd (by simpa using hg) hrev
  simpa using hh

/-- The actual original weak owner gives the local boosted estimate on
the same cycle; no replacement of either square is made. -/
theorem actual_boost (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hk : F.word hgap pi_lt_22_over_7 i=0) (j : Fin 4) (hj : j=1 ∨ j=3)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (197/200:ℝ)<TableFreeWordGeometry.phaseValue F hgap i+
      (stateOf C i).signedLabel-(stateOf C (next i)).signedLabel+
        (9/50)*frameCost |TableFreeWordGeometry.difference F i| := by
  have hphase : FramePair.pairAngle C i=TableFreeWordGeometry.phaseValue F hgap i := by
    linarith [FramePair.pairAngle_gap C i,TableFreeWordGeometry.phase_gap C F hgap i]
  have hz : TableFreeWordGeometry.phaseValue F hgap i=TableFreeWordGeometry.difference F i := by
    simp [TableFreeWordGeometry.phaseValue,hk]
  have hm := stateOf_feasible C i j howner
  have hg : (19/25:ℝ)<(stateOf C i).gap (stateOf C (next i))
      (TableFreeWordGeometry.difference F i) := by
    rw [← hz,← hphase,stateOf_gap]
    exact hgap i
  rw [hphase,hz] at hm
  rw [hz]
  rcases hj with rfl | rfl
  · exact target_primary_boost (stateOf C i) (stateOf C (next i))
      (TableFreeWordGeometry.difference_small F i).le hg hm
  · exact source_primary_boost (stateOf C i) (stateOf C (next i))
      (TableFreeWordGeometry.difference_small F i).le hg hm

end SquaresInCircles.Eight.TableFree.ZeroPrimary
