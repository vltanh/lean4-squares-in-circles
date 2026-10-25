module

public import SquaresInCircles.Eight.Owners.Quarter.SignScalar
public import SquaresInCircles.Eight.Owners.Zero.SignBridge

/-!
# Eight squares: the signs of the quarter owners and the DE restriction

The local boosts are joined to the pair bounds of the six other edges and the return path of the
frame (`ceiling_target_positive`, `ceiling_source_negative`). Fixed-ray expansion keeps every weak
axis and both source signs, so the statements hold at the radius `q` itself, with the physical
normals (`target_positive`, `source_negative`).

On a quarter edge every owner in `{0, 1}` forces a strictly positive target, and every owner in
`{2, 3}` a strictly negative source (`classify`). In particular a nonpositive E forces the owners
of DE and the strict sign of D, with no other owner, anchor or frame order involved
(`frame_target_nonpos`, `frame_DE`).
-/

section
/-!
## A quarter owner with the wrong sign has boosted cost above one

The four combinations of source sign and owner are treated on the two states and their weak
separating-axis inequality (`zero_negative_boost`, `zero_positive_boost`,
`one_negative_negative_boost`, `one_negative_positive_boost`, `one_positive_boost`). The target may
have zero transverse coordinate, and both pieces of the core, every outer chart and both signs of
the frame error are covered. So owners `0` and `1` with a nonpositive target, and owners `2` and
`3` with a nonnegative source, have boosted cost above one (`target_nonpos_boost`,
`source_nonneg_boost`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalQuarterSign

open FramePair ZeroPrimary GlobalZeroSign

theorem frame_abs_formula {d : ℝ} (hd : |d|≤frameCap) :
    frameCost |d|=(Real.cos d+|Real.sin d|-1)/2 := by
  by_cases hp : 0≤d
  · have hs := (transport_trig ⟨hp,(le_abs_self d).trans hd⟩).2.2.1
    simp [frameCost,abs_of_nonneg hp,abs_of_nonneg hs]
  · have hn : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    have hs : Real.sin d≤0 := by
      have hh := (transport_trig hn).2.2.1
      simpa only [Real.sin_neg,neg_nonneg] using hh
    simp [frameCost,abs_of_nonpos (by linarith : d≤0),abs_of_nonpos hs]

theorem frame_abs_nonneg {d : ℝ} (hd : |d|≤frameCap) : 0≤frameCost |d| := by
  have hc : 0<Real.cos d := by
    linarith [(CommonQuarter.signed_cos (by simpa [frameCap] using hd)).1]
  have hh := one_le_abs_cos_add_abs_sin d
  rw [abs_of_pos hc] at hh
  rw [frame_abs_formula hd]
  linarith

theorem zero_negative_boost (s t : State) {d : ℝ} (hd : |d|≤frameCap)
    (hs : s.positive=false) (ht : sign t.positive*t.b≤0)
    (hm : s.Feasible t 0 (Real.pi/2+d)) :
    1<Real.pi/2+d+s.signedLabel-t.signedLabel+(9/50)*frameCost |d| := by
  have hm' := (quarter_zero_margin s t hd ht).1 hm
  simp only [hs,FramePair.sign,Bool.false_eq_true,ite_false,neg_one_mul] at hm'
  have hw : 1≤(1+Real.cos d+|Real.sin d|)/2 := by
    rw [← CommonQuarter.quarter_width (by simpa only [frameCap] using hd)]
    exact CommonQuarter.width_ge_one _
  have hsmall : s.b<1/2 := by
    linarith [rotated_projection_lt t d]
  have hupper := marker_small_upper s hsmall
  have hlower := marker_lower t
  have hcos : 0≤Real.cos d := by
    linarith [(CommonQuarter.signed_cos (by simpa only [frameCap] using hd)).1]
  have hsin := CommonQuarter.signed_sin (by simpa only [frameCap] using hd)
  have hcoef : 0≤(4/5:ℝ)+(111/100)*Real.sin d := by
    linarith [neg_le_abs (Real.sin d)]
  have htail := mul_nonneg hcoef t.b_nonneg
  have hA := mul_le_mul_of_nonneg_right (coordinates t).2.1.le hcos
  have hscalar := secondary_negative_scalar hd
  have hsource : s.signedLabel= -unsigned s := by simp [State.signedLabel,unsigned,hs,FramePair.sign]
  rw [hsource,signed_of_nonpos t ht,frame_abs_formula hd]
  nlinarith only [hm',hupper,hlower,htail,hA,hscalar]

theorem zero_positive_boost (s t : State) {d : ℝ} (hd : |d|≤frameCap)
    (hs : s.positive=true) (ht : sign t.positive*t.b≤0)
    (hm : s.Feasible t 0 (Real.pi/2+d)) :
    1<Real.pi/2+d+s.signedLabel-t.signedLabel+(9/50)*frameCost |d| := by
  have hm' := (quarter_zero_margin s t hd ht).1 hm
  simp only [hs,FramePair.sign,ite_true,one_mul] at hm'
  have hsource : s.signedLabel=unsigned s := by simp [State.signedLabel,unsigned,hs,FramePair.sign]
  have hcos : 0≤Real.cos d := by
    linarith [(CommonQuarter.signed_cos (by simpa only [frameCap] using hd)).1]
  have hsin := CommonQuarter.signed_sin (by simpa only [frameCap] using hd)
  have hcoef : 0≤1+Real.sin d := by linarith [neg_le_abs (Real.sin d)]
  have htail := mul_nonneg hcoef t.b_nonneg
  have hA := mul_le_mul_of_nonneg_right (coordinates t).2.1.le hcos
  have hscalar := secondary_positive_scalar hd
  rw [hsource,signed_of_nonpos t ht,frame_abs_formula hd]
  nlinarith only [hm',marker_lower s,marker_lower t,htail,hA,hscalar]

/-- A negative source at nonpositive error with a primary witness has `s.b < 1/2`, in the
small-marker range, and error below `1/2`; the cut follows from Taylor bounds up to the cap. -/
theorem one_negative_negative_domain (s t : State) {x : ℝ}
    (hx : x∈Icc 0 frameCap)
    (hm : (1+Real.cos x+Real.sin x)/2≤
      t.a-s.a*Real.sin x-s.b*Real.cos x) :
    s.b<1/2 ∧ x<1/2 := by
  have ht := transport_trig hx
  have hcpos : 0<Real.cos x := by linarith [ht.1]
  have hcosU := Real.cos_le_one x
  have hsU : Real.sin x≤13/20 := by linarith [ht.2.2.2.1]
  have hw : 1≤(1+Real.cos x+Real.sin x)/2 := by
    have hh := one_le_abs_cos_add_abs_sin x
    rw [abs_of_pos hcpos,abs_of_nonneg ht.2.2.1] at hh
    linarith
  have hA := (coordinates t).2.1
  have ha := mul_le_mul_of_nonneg_right (primary_lower s).le ht.2.2.1
  have hcLower : 1-Real.sin x^2≤Real.cos x := by
    have hh := mul_nonneg (show 0≤Real.cos x by linarith)
      (sub_nonneg.mpr hcosU)
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hr := mul_nonneg ht.2.2.1
    (show 0≤(447/800:ℝ)-Real.sin x/2 by linarith)
  have hsmall : s.b<1/2 := by
    by_contra! hb
    have hprod := mul_le_mul_of_nonneg_right hb hcpos.le
    nlinarith
  have hcut : x<1/2 := by
    by_contra! hb
    have hxU : x≤(7/10:ℝ) := by simpa only [frameCap] using hx.2
    have hx2 := pow_le_pow_left₀ hx.1 hxU 2
    norm_num at hx2
    have hx3 : x^3≤(49/100)*x := by
      nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx2)]
    have hsin : (551/600)*x≤Real.sin x := by
      nlinarith [Real.sin_ge_sub_cube hx.1]
    have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
    have hprod := mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hxU)
    have hbprod := mul_nonneg s.b_nonneg hcpos.le
    nlinarith
  exact ⟨hsmall,hcut⟩

theorem one_negative_negative_boost (s t : State) {x : ℝ}
    (hx : x∈Icc 0 frameCap) (hs : s.positive=false)
    (ht : sign t.positive*t.b≤0)
    (hm : s.Feasible t 1 (Real.pi/2-x)) :
    1<Real.pi/2-x+s.signedLabel-t.signedLabel+(9/50)*frameCost x := by
  have tr := transport_trig hx
  have hd : |-x|≤frameCap := by simpa only [abs_neg,abs_of_nonneg hx.1] using hx.2
  have hm' := (quarter_one_margin s t hd).1 (by simpa only [sub_eq_add_neg] using hm)
  simp only [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1,
    hs,FramePair.sign,Bool.false_eq_true,ite_false,neg_one_mul] at hm'
  have hmargin : (1+Real.cos x+Real.sin x)/2≤
      t.a-s.a*Real.sin x-s.b*Real.cos x := by nlinarith only [hm']
  obtain ⟨hsmall,hxsmall⟩ := one_negative_negative_domain s t hx hmargin
  have hcpos : 0<Real.cos x := by linarith [tr.1]
  have ha := mul_le_mul_of_nonneg_right (primary_lower s).le tr.2.2.1
  have hbound : s.b*Real.cos x≤283/200-
      (1+Real.cos x+Real.sin x)/2-(447/800)*Real.sin x := by
    nlinarith [ (coordinates t).2.1]
  have hscalar := primary_negative_negative_scaled ⟨hx.1,hxsmall.le⟩
  have hscaled : 0<(Real.pi/2-x-(111/100)*s.b-1)*Real.cos x := by
    nlinarith only [hscalar,hbound]
  have hbase : 1<Real.pi/2-x-(111/100)*s.b := by
    have hh := (mul_pos_iff_of_pos_right hcpos).1 hscaled
    linarith
  have hframe : 0≤frameCost x := by
    simpa only [abs_of_nonneg hx.1] using frame_abs_nonneg
      (show |x|≤frameCap by simpa only [abs_of_nonneg hx.1] using hx.2)
  have hsource : s.signedLabel= -unsigned s := by simp [State.signedLabel,unsigned,hs,FramePair.sign]
  rw [hsource,signed_of_nonpos t ht]
  linarith [marker_small_upper s hsmall,marker_nonneg t]

/-- At a small positive error `d ≤ 1/4`, a primary witness of owner `1` bounds the marker of the
negative source by `(111/100) s.b`, so a core point at or above the junction of side and corner
cannot be that source. -/
theorem one_negative_positive_marker (s t : State) {d : ℝ}
    (hd : d∈Icc 0 (1/4:ℝ))
    (hm : (1+Real.cos d+Real.sin d)/2≤
      t.a+s.a*Real.sin d-s.b*Real.cos d) :
    unsigned s≤(111/100)*s.b := by
  by_cases hcore : s.branch.type=0
  · have ha := (FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart s hcore)).2.1
    have tr := transport_trig (show d∈Icc 0 frameCap by
      constructor <;> norm_num [frameCap] <;> linarith [hd.1,hd.2])
    have hcpos : 0≤Real.cos d := by linarith [tr.1]
    have hsU : Real.sin d≤1/4 := (Real.sin_le hd.1).trans hd.2
    have hcL : (31/32:ℝ)≤Real.cos d := by
      have h2 := pow_le_pow_left₀ hd.1 hd.2 2
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := d)]
    have hsmall : s.b<1/2 := by
      by_contra! hb
      have haP := mul_le_mul_of_nonneg_right ha tr.2.2.1
      have hbP := mul_le_mul_of_nonneg_right hb hcpos
      nlinarith [(coordinates t).2.1]
    exact marker_small_upper s hsmall
  · exact marker_outer_upper s hcore

theorem one_negative_positive_boost (s t : State) {d : ℝ}
    (hd : d∈Icc 0 frameCap) (hs : s.positive=false)
    (ht : sign t.positive*t.b≤0)
    (hm : s.Feasible t 1 (Real.pi/2+d)) :
    1<Real.pi/2+d+s.signedLabel-t.signedLabel+(9/50)*frameCost d := by
  have tr := transport_trig hd
  have hdabs : |d|≤frameCap := by simpa only [abs_of_nonneg hd.1] using hd.2
  have hframe : 0≤frameCost d := by
    simpa only [abs_of_nonneg hd.1] using frame_abs_nonneg hdabs
  have hsource : s.signedLabel= -unsigned s := by simp [State.signedLabel,unsigned,hs,FramePair.sign]
  rw [hsource,signed_of_nonpos t ht]
  by_cases hlarge : 1/4≤d
  · linarith [half_pi_lower,marker_lt_four_fifths s,marker_nonneg t]
  · have hsmall : d∈Icc 0 (1/4:ℝ) := ⟨hd.1,by linarith⟩
    have hm' := (quarter_one_margin s t hdabs).1 hm
    simp only [abs_of_nonneg tr.2.2.1,hs,FramePair.sign,Bool.false_eq_true,
      ite_false,neg_one_mul] at hm'
    have hmargin : (1+Real.cos d+Real.sin d)/2≤
        t.a+s.a*Real.sin d-s.b*Real.cos d := by nlinarith only [hm']
    have hmarker := one_negative_positive_marker s t hsmall hmargin
    have ha := mul_le_mul_of_nonneg_right (coordinates s).2.1.le tr.2.2.1
    have hbound : s.b*Real.cos d≤(283/200)*(1+Real.sin d)-
        (1+Real.cos d+Real.sin d)/2 := by
      nlinarith [(coordinates t).2.1]
    have hscalar := primary_negative_positive_scaled hsmall
    have hscaled : 0<(Real.pi/2+d-(111/100)*s.b-1)*Real.cos d := by
      nlinarith only [hscalar,hbound]
    have hbase : 1<Real.pi/2+d-(111/100)*s.b := by
      have hh := (mul_pos_iff_of_pos_right (show 0<Real.cos d by linarith [tr.1])).1 hscaled
      linarith
    linarith [marker_nonneg t]

theorem one_positive_boost (s t : State) {d : ℝ} (hd : |d|≤frameCap)
    (hs : s.positive=true) (ht : sign t.positive*t.b≤0)
    (hm : s.Feasible t 1 (Real.pi/2+d)) :
    1<Real.pi/2+d+s.signedLabel-t.signedLabel+(9/50)*frameCost |d| := by
  have hsource : s.signedLabel=unsigned s := by simp [State.signedLabel,unsigned,hs,FramePair.sign]
  rw [hsource,signed_of_nonpos t ht]
  by_cases hp : 0≤d
  · linarith [half_pi_lower,marker_nonneg s,marker_nonneg t,frame_abs_nonneg hd]
  · let x := -d
    have hx : x∈Icc 0 frameCap := ⟨by dsimp [x]; linarith,(neg_le_abs d).trans hd⟩
    have he : d= -x := by dsimp [x]; ring
    have tr := transport_trig hx
    have hm' := (quarter_one_margin s t hd).1 hm
    rw [he,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1] at hm'
    simp only [hs,FramePair.sign,ite_true,one_mul] at hm'
    have ha := mul_le_mul_of_nonneg_right (primary_lower s).le tr.2.2.1
    have hbound : (1+Real.cos x+Real.sin x)/2-283/200+
        (447/800)*Real.sin x≤ s.b*Real.cos x := by
      nlinarith [(coordinates t).2.1]
    have hscalar := primary_positive_negative_scaled hx
    have hscaled : 0<(Real.pi/2-x+(4/5)*s.b+(9/50)*frameCost x-1)*Real.cos x := by
      nlinarith only [hscalar,hbound]
    have hbase : 1<Real.pi/2-x+(4/5)*s.b+(9/50)*frameCost x := by
      have hh := (mul_pos_iff_of_pos_right (show 0<Real.cos x by linarith [tr.1])).1 hscaled
      linarith
    rw [he,abs_neg,abs_of_nonneg hx.1]
    linarith [marker_lower s,marker_nonneg t]

/-- Every owner in `{0, 1}` has boosted cost above one when the transverse coordinate of the target
is nonpositive. -/
theorem target_nonpos_boost (s t : State) {d : ℝ} (hd : |d|≤frameCap)
    (ht : sign t.positive*t.b≤0) (j : Fin 4) (hj : j=0 ∨ j=1)
    (hm : s.Feasible t j (Real.pi/2+d)) :
    1<Real.pi/2+d+s.signedLabel-t.signedLabel+(9/50)*frameCost |d| := by
  rcases hj with rfl | rfl
  · cases hs : s.positive
    · exact zero_negative_boost s t hd hs ht hm
    · exact zero_positive_boost s t hd hs ht hm
  · cases hs : s.positive
    · by_cases hp : 0≤d
      · have hh := one_negative_positive_boost s t
          ⟨hp,(le_abs_self d).trans hd⟩ hs ht hm
        simpa only [abs_of_nonneg hp] using hh
      · have hx : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
        have hh := one_negative_negative_boost s t hx hs ht
          (by simpa only [sub_neg_eq_add] using hm)
        simpa only [neg_neg,sub_neg_eq_add,abs_of_nonpos (by linarith : d≤0)] using hh
    · exact one_positive_boost s t hd hs ht hm

/-- Every owner in `{2, 3}` has boosted cost above one when the source is nonnegative: reflection
and reversal keep the quarter error, exchange the owners `0 ↔ 2` and `1 ↔ 3`, and keep the charged
marker value. -/
theorem source_nonneg_boost (s t : State) {d : ℝ} (hd : |d|≤frameCap)
    (hs : 0≤ sign s.positive*s.b) (j : Fin 4) (hj : j=2 ∨ j=3)
    (hm : s.Feasible t j (Real.pi/2+d)) :
    1<Real.pi/2+d+s.signedLabel-t.signedLabel+(9/50)*frameCost |d| := by
  have hbad : sign s.flip.positive*s.flip.b≤0 := by
    simpa only [State.flip,sign_not,neg_mul] using neg_nonpos.mpr hs
  rcases hj with rfl | rfl
  · have hrev := (State.target_secondary_reverse s t (Real.pi/2+d)).1 hm
    have hh := target_nonpos_boost t.flip s.flip hd hbad 0 (Or.inl rfl) hrev
    simp only [State.flip_label] at hh
    linarith
  · have hrev : t.flip.Feasible s.flip 1 (Real.pi/2+d) := by
      simpa [State.Feasible,State.flip,forwardMargin,FramePair.sign_not,
        sub_eq_add_neg,mul_comm,mul_left_comm,mul_assoc,add_comm,add_left_comm,add_assoc] using hm
    have hh := target_nonpos_boost t.flip s.flip hd hbad 1 (Or.inr rfl) hrev
    simp only [State.flip_label] at hh
    linarith

end SquaresInCircles.Eight.GlobalQuarterSign
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight
open Candidate

namespace GlobalQuarterSign

open FramePair QuarterWordGeometry

private theorem one_word (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hi : integerQuarterIncrement F.quarter i=1) :
    F.word hgap pi_lt_22_over_7 i=1 := by
  apply Fin.ext
  have hh := F.word_cast hgap pi_lt_22_over_7 i
  rw [hi] at hh
  omega

theorem ceiling_target_positive (C : BoundaryCycle Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (j : Fin 4) (hj : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    0<C.tangent (next i) := by
  by_contra! hbad
  let hgap : ∀k,19/25<angleGap C.beta k := boundary_gap_lower C le_rfl
  have hz : phaseValue F hgap i=Real.pi/2+difference F i := by
    simp [phaseValue,one_word C F hgap i hi,add_comm]
  have hp : pairAngle C i=Real.pi/2+difference F i := by
    have hh := phase_gap C F hgap i
    rw [hz] at hh
    linarith [pairAngle_gap C i]
  have hm := stateOf_feasible C i j haxis
  rw [hp] at hm
  have hy : sign (stateOf C (next i)).positive*(stateOf C (next i)).b≤0 := by
    have hn : C.sigma (next i)*C.b (next i)≤0 := by
      have hh := (div_le_iff₀ (C.a_pos (next i))).1 hbad
      simpa only [zero_mul] using hh
    simpa only [stateOf,signOf_spec] using hn
  have hb := target_nonpos_boost (stateOf C i) (stateOf C (next i))
    (by simpa only [frameCap] using (difference_small F i).le) hy j hj hm
  apply GlobalZeroSign.closed_boost_impossible C F hgap i
  simpa only [hz] using hb

theorem ceiling_source_negative (C : BoundaryCycle Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (j : Fin 4) (hj : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.tangent i<0 := by
  by_contra! hbad
  let hgap : ∀k,19/25<angleGap C.beta k := boundary_gap_lower C le_rfl
  have hz : phaseValue F hgap i=Real.pi/2+difference F i := by
    simp [phaseValue,one_word C F hgap i hi,add_comm]
  have hp : pairAngle C i=Real.pi/2+difference F i := by
    have hh := phase_gap C F hgap i
    rw [hz] at hh
    linarith [pairAngle_gap C i]
  have hm := stateOf_feasible C i j haxis
  rw [hp] at hm
  have hy : 0≤ sign (stateOf C i).positive*(stateOf C i).b := by
    have hn : 0≤C.sigma i*C.b i := by
      have hh := (le_div_iff₀ (C.a_pos i)).1 hbad
      simpa only [zero_mul] using hh
    simpa only [stateOf,signOf_spec] using hn
  have hb := source_nonneg_boost (stateOf C i) (stateOf C (next i))
    (by simpa only [frameCap] using (difference_small F i).le) hy j hj hm
  apply GlobalZeroSign.closed_boost_impossible C F hgap i
  simpa only [hz] using hb

theorem target_positive {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (j : Fin 4) (hj : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    0<C.tangent (next i) := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  have hinc : integerQuarterIncrement G.quarter i=1 := hi
  have hh := ceiling_target_positive D G i hinc j hj
    (hR.preserves_all_axes i (forwardAxis j) haxis)
  simpa only [hR.same_tangents] using hh

theorem source_negative {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (j : Fin 4) (hj : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.tangent i<0 := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  have hinc : integerQuarterIncrement G.quarter i=1 := hi
  have hh := ceiling_source_negative D G i hinc j hj
    (hR.preserves_all_axes i (forwardAxis j) haxis)
  simpa only [hR.same_tangents] using hh

/-- Every owner of a quarter edge, each member of a weak tie included: owners `0` and `1` make the
target positive, owners `2` and `3` the source negative. -/
theorem classify {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (j : Fin 4)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    ((j=0 ∨ j=1) ∧ 0<C.tangent (next i)) ∨
      ((j=2 ∨ j=3) ∧ C.tangent i<0) := by
  fin_cases j
  · exact Or.inl ⟨Or.inl rfl,target_positive C hq F i hi 0 (Or.inl rfl) haxis⟩
  · exact Or.inl ⟨Or.inr rfl,target_positive C hq F i hi 1 (Or.inr rfl) haxis⟩
  · exact Or.inr ⟨Or.inl rfl,source_negative C hq F i hi 2 (Or.inl rfl) haxis⟩
  · exact Or.inr ⟨Or.inr rfl,source_negative C hq F i hi 3 (Or.inr rfl) haxis⟩

theorem of_offsetLift {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (hm : F.quarter=offsets)
    (i : Vertex) (hi : word i=1) (j : Fin 4)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    ((j=0 ∨ j=1) ∧ 0<C.tangent (next i)) ∨
      ((j=2 ∨ j=3) ∧ C.tangent i<0) := by
  have hinc : integerQuarterIncrement F.quarter i=1 := by
    rw [hm,GlobalZeroSign.offset_increment,hi]
  exact classify C hq F i hinc j haxis

theorem of_frame {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex) (hi : word i=1) (j : Fin 4)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    ((j=0 ∨ j=1) ∧ 0<C.tangent (next i)) ∨
      ((j=2 ∨ j=3) ∧ C.tangent i<0) := by
  obtain ⟨G,hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro k; simpa only [mul_div_assoc] using F.canonical_eq k)
  exact of_offsetLift C hq G hGquarter i hi j haxis

/-- A quarter edge with nonpositive target has every owner in `{2, 3}` and a strictly negative
source, with no sign prescribed at the source. -/
theorem frame_target_nonpos {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex) (hi : word i=1)
    (ht : C.tangent (next i)≤0) :
    C.tangent i<0 ∧ ∀j : Fin 4,
      (forwardAxis j).Feasible (C.square i) (C.square (next i)) → j=2 ∨ j=3 := by
  have heach (j : Fin 4)
      (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
      (j=2 ∨ j=3) ∧ C.tangent i<0 := by
    rcases of_frame F hq i hi j hj with ⟨_,hn⟩ | hh
    · exact (not_lt_of_ge ht hn).elim
    · exact hh
  obtain ⟨j,hj⟩ := F.forward_complete i (C.selected i) (C.feasible i)
  have haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [hj] using C.feasible i
  exact ⟨(heach j haxis).2,fun j hj => (heach j hj).1⟩

theorem frame_DE {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0) :
    C.tangent D<0 ∧ ∀j : Fin 4,
      (forwardAxis j).Feasible (C.square D) (C.square E) → j=2 ∨ j=3 := by
  simpa [D,E,next] using frame_target_nonpos F hq D (by norm_num [word,D])
    (by simpa [D,E,next] using hE)

end GlobalQuarterSign

namespace SignedCycle

end SignedCycle
end SquaresInCircles.Eight
end
end
end
