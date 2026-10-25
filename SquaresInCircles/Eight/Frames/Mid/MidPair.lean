module

public import SquaresInCircles.Eight.Frames.Mid.MidPrimary
public import SquaresInCircles.Eight.Frames.Mid.Parallel

/-!
# Eight squares: the middle/middle pairs

Two states of the closed middle arc, with any signs, separated along any forward axis at a gap of
at least `19/25`, have the cost of the pair above `557/625` (`middle_pair`; `middle_cycle_pair` on
the edges of a boundary cycle at `Q0`). On the secondary axis with two positive ends, the cost is
at least the circle support `F x` for `3/5 ≤ x ≤ 109/100` (`transverse_circle_support`,
`transverse_positive`); with opposite signs, the support of the parallel line bounds it for
`-1/20 ≤ x ≤ 8/25` (`transverse_opposite`); the other cases use the supports of the whole circle
and of the ends of the arc from `FrameMidMidScalars` and `FrameMidMidPrimary`
(`source_secondary`, `source_primary`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidMidPair
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FramePairCalculus FrameCoreMidGeometry FrameMidMidGeometry
open FrameMidMidScalars FrameMidMidPrimary

theorem transverse_circle_support {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (3/5:ℝ) (109/100)) (hm : 0≤ secondary true true b B x) :
    F x≤cost true true b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hs := transverse_source_lower hb
  have hscaled := mul_nonneg (show (0:ℝ)≤lambda by norm_num [lambda]) hm
  have ht := circle_linear_lower
    (A_circle ⟨b1_mem.1.trans hB.1,hB.2.trans b2_mem.2⟩)
    (-p-lambda*Real.sin x) (-q+lambda*Real.cos x)
  have hn : Real.sqrt ((-p-lambda*Real.sin x)^2+(-q+lambda*Real.cos x)^2)=NF x := by
    dsimp [NF,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination lambda^2*(Real.sin_sq_add_cos_sq x)
  rw [hn] at ht
  dsimp [F,cost,secondary,KF,M] at *
  simp only [sign,ite_true,one_mul] at *
  rw [(first_width hxq).1] at hscaled
  rw [(first_width hxq).2]
  nlinarith

theorem transverse_positive {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (3/5:ℝ) (109/100)) (hm : 0≤ secondary true true b B x) :
    (557/625:ℝ)<cost true true b B x :=
  (transverse_lower hx).trans_le (transverse_circle_support hb hB hx hm)

theorem transverse_opposite {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (-(1/20:ℝ)) (8/25)) (hm : 0≤ secondary true false b B x) :
    (557/625:ℝ)<cost true false b B x := by
  have hh := FrameMidParallel.contact_strip hb hB hx
    (by simpa [FrameMidParallel.margin,secondary,sign] using hm)
  simpa [FrameMidParallel.cost,cost,sign] using hh

theorem state_cost (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.middle) (x : ℝ) :
    s.cost t x=cost s.positive t.positive s.b t.b x := by
  rw [State.cost,state_mid_label s hs,state_mid_label t ht]
  rfl

theorem state_secondary (s t : FramePair.State) (ht : t.branch=.middle) (x : ℝ) :
    s.Feasible t 0 x ↔ 0≤ secondary s.positive t.positive s.b t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero,(state_mid_chart t ht).1]
  rfl

theorem state_primary (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.middle) (x : ℝ) :
    s.Feasible t 3 x ↔ 0≤primary t.positive s.b t.b x := by
  simp only [State.Feasible,forwardMargin,
    (state_mid_chart s hs).1,(state_mid_chart t ht).1]
  rfl

theorem source_secondary (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.middle) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (557/625:ℝ)<s.cost t x := by
  have hb := (state_mid_chart s hs).2
  have hB := (state_mid_chart t ht).2
  have hmargin := (state_secondary s t ht x).mp hm
  have hx := angle_floor s t hs ht hgap
  rw [state_cost s t hs ht]
  revert hmargin
  cases hss : s.positive <;> cases htt : t.positive <;> intro hmargin
  · by_cases htail : (109/100:ℝ)≤x
    · exact same_tail false hb hB htail
    · have hlo := same_sign_angle s t hs ht (by rw [hss,htt]) hgap
      exact False.elim (negative_secondary_false false hb hB
        ⟨by linarith,by linarith [FrameLowPair.pi_lower]⟩ hmargin)
  · by_cases htail : (37/20:ℝ)≤x
    · exact negative_positive_tail hb hB htail
    · have hlo := negative_positive_angle s t hs ht hss htt hgap
      exact False.elim (negative_secondary_false true hb hB
        ⟨by linarith,by linarith [FrameLowPair.pi_lower]⟩ hmargin)
  · by_cases htail : (8/25:ℝ)≤x
    · exact positive_negative_tail hb hB htail
    · exact transverse_opposite hb hB ⟨hx.le,(lt_of_not_ge htail).le⟩ hmargin
  · by_cases htail : (109/100:ℝ)≤x
    · exact same_tail true hb hB htail
    · have hlo := same_sign_angle s t hs ht (by rw [hss,htt]) hgap
      exact transverse_positive hb hB ⟨hlo.le,(lt_of_not_ge htail).le⟩ hmargin

theorem source_primary (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.middle) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (557/625:ℝ)<s.cost t x := by
  have hb := (state_mid_chart s hs).2
  have hB := (state_mid_chart t ht).2
  have hmargin := (state_primary s t hs ht x).mp hm
  have hx := angle_floor s t hs ht hgap
  rw [state_cost s t hs ht]
  revert hmargin
  cases htt : t.positive with
  | false =>
      intro hmargin
      exact primary_negative s.positive hb hB hx.le hmargin
  | true =>
      intro hmargin
      exact primary_positive s.positive hb hB hx.le hmargin

/-- The middle/middle pair inequality, on every forward axis. -/
theorem middle_pair (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.middle) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(557/625:ℝ) := by
    norm_num [hs,ht,Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_secondary s t hs ht hgap hm
  · have hh := source_primary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_secondary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_primary s t hs ht hgap hm

theorem middle_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.middle) (hj : branchOf C (next i)=.middle)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact middle_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

end SquaresInCircles.Eight.FrameMidMidPair
