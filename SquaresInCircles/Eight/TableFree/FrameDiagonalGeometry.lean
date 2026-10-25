module

public import SquaresInCircles.Eight.TableFree.FrameDiagonalTransport

/-!
# Actual owner reductions for the two remaining outer frame pairs

The original negative transverse axis is excluded by the actual center
radius.  The other extra axis is excluded on the full first quadrant
and on the only relevant continuation after the quarter turn.  The
nonpositive central-angle exclusion uses the original center gap and
the complete folded arcs.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameDiagonalGeometry
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FramePairCalculus

def physicalRadius (middle : Bool) : ℝ := if middle then 67/50 else 653/500
def originalTransverse (middle : Bool) : ℝ := if middle then 64937/200000 else 5139/10000

theorem original_transverse_lower (m : Bool) (s : FramePair.State)
    (hs : s.branch=kind m) : originalTransverse m<s.b := by
  cases m with
  | false =>
      have hb := (FrameHighArc.state_high_chart s hs).2.1
      exact FrameMidArc.b2_bounds.1.trans_le hb
  | true =>
      have hb := (FrameMidArc.state_mid_chart s hs).2.1
      exact FrameLowArc.b1_bounds.1.trans_le hb

theorem original_projection_lt (n j : Bool) (t : FramePair.State)
    (ht : t.branch=kind n) (x : ℝ) :
    t.a*Real.sin x-sign j*t.b*Real.cos x<physicalRadius n := by
  cases n with
  | false =>
      have hc := FrameHighArc.state_high_chart t ht
      have hr := high_radius_sq hc.2
      rw [hc.1,show physicalRadius false=653/500 from rfl]
      cases j
      · have h := FrameCoreArc.projection_lt (b := t.b) (by norm_num : (0:ℝ)<653/500) hr x
        rw [show sign false=-1 from rfl]
        linarith
      · have hh : (FrameCircleArc.A t.b)^2+(-t.b)^2<(653/500:ℝ)^2 := by
          rw [neg_sq]
          exact hr
        have h := FrameCoreArc.projection_lt (b := -t.b) (by norm_num : (0:ℝ)<653/500) hh x
        rw [show sign true=1 from rfl]
        linarith
  | true =>
      have hc := FrameMidArc.state_mid_chart t ht
      rw [hc.1]
      exact FrameCoreArc.middle_projection_lt j hc.2 x

/-- At least one endpoint is high; the original weak transverse axis
cannot have a negative original source tangent. -/
theorem original_negative_secondary_false (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n)
    (hhigh : m=false ∨ n=false) (hi : s.positive=false) (x : ℝ) :
    ¬s.Feasible t 0 x := by
  intro hm
  have hp := original_projection_lt n t.positive t ht x
  have hb := original_transverse_lower m s hs
  have hw := FrameCoreArc.width_one_le x
  have hnum : physicalRadius n-originalTransverse m<1 := by
    rcases hhigh with rfl | rfl
    · cases n <;> norm_num [physicalRadius,originalTransverse]
    · cases m <;> norm_num [physicalRadius,originalTransverse]
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero,hi] at hm
  rw [show sign false=-1 from rfl] at hm
  linarith

theorem arc_coordinates (m : Bool) {b : ℝ} (hb : b∈arc m) :
    A b+b<(1299/500:ℝ) ∧ (649/1000:ℝ)<A b-b := by
  cases m
  · have hh := high_coordinates hb
    constructor <;> linarith
  · exact mid_coordinates hb

theorem negative_trig {x : ℝ} (hx : x∈Icc (-(81/500:ℝ)) 0) :
    Real.sin x≤0 ∧ (493/500:ℝ)<Real.cos x := by
  have he : -x∈Icc 0 (81/500:ℝ) := ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi he.1
    (by linarith [he.2,Arithmetic.pi_hand_enclosure.1])
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ he.1 he.2 2
  simp only [Real.sin_neg,neg_sq] at hs hsq
  exact ⟨by linarith,by nlinarith⟩

theorem central_nonpositive_false (m n : Bool) {b B x : ℝ}
    (hb : b∈arc m) (hB : B∈arc n) (hx : x∈Icc (-(81/500:ℝ)) 0) :
    central true false (A b) b (A B) B x<0 := by
  have hs := arc_coordinates m hb
  have ht := arc_coordinates n hB
  have htr := negative_trig hx
  have hA := (A_bounds (arc_subset hB)).1
  have hB0 := (arc_subset hB).1
  have hsin := mul_nonpos_of_nonpos_of_nonneg htr.1
    (show 0≤A B+B+1 by linarith [a2_precise.1])
  have hcos := mul_nonneg
    (show 0≤Real.cos x-493/500 by linarith [htr.2])
    (show 0≤A B-B+1-1649/1000 by linarith [ht.2])
  have hw := negative_width
    (show x∈Icc (-(54/125:ℝ)) 0 from ⟨by linarith [hx.1],hx.2⟩)
  dsimp [central,sign]
  rw [hw.1]
  nlinarith

theorem actual_angle_lower (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n)
    (hhigh : m=false ∨ n=false) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) :
    -(81/500:ℝ)<angle s.positive t.positive x := by
  have hh := angle_lower m n s t hs ht hgap
  rcases hhigh with rfl | rfl
  · cases n <;> simp only [cap,Bool.false_eq_true,↓reduceIte] at hh <;> linarith
  · cases m <;> simp only [cap,Bool.false_eq_true,↓reduceIte] at hh <;> linarith

theorem actual_central_positive (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n)
    (hhigh : m=false ∨ n=false) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x)
    (hm : s.Feasible t (centralAxis s.positive) x) :
    0<angle s.positive t.positive x := by
  by_contra! hx
  have hlo := actual_angle_lower m n s t hs ht hhigh hgap
  have hsg := nonpositive_signs m n s t hs ht hgap hx
  have hf := state_central_feasible m n s t hs ht hm
  have hbad := central_nonpositive_false m n
    (state_fold m s hs).1 (state_fold n t ht).1 ⟨hlo.le,hx⟩
  rw [hsg.1,hsg.2] at hf hbad
  simp only [Bool.not_false,Bool.not_true] at hf
  linarith

theorem extra_first_false (m n j : Bool) {b B x : ℝ}
    (hb : b∈arc m) (hB : B∈arc n) (hx : x∈Icc 0 (Real.pi/2)) :
    extra j (A b) b (A B) B x<0 := by
  have hs := arc_coordinates m hb
  have ht := arc_coordinates n hB
  have htr := FrameLowPair.quadrant hx
  have hw := FrameCoreArc.width_one_le x
  have hwf := (first_width hx).1
  have hC : 1≤Real.sin x+Real.cos x := by linarith
  have hA0 : 0≤A B := by linarith [(A_bounds (arc_subset hB)).1,a2_precise.1]
  have hB0 := (arc_subset hB).1
  have hCA := mul_le_mul_of_nonneg_right hC hA0
  have hDlo := mul_le_mul_of_nonneg_right
    (show -(1:ℝ)≤Real.sin x-Real.cos x by linarith) hB0
  have hDhi := mul_le_mul_of_nonneg_right
    (show Real.sin x-Real.cos x≤1 by linarith) hB0
  cases j <;> dsimp [extra,sign] <;> nlinarith

theorem late_sum_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100:ℝ)) :
    (17/20:ℝ)<Real.sin x+Real.cos x := by
  obtain ⟨e,he_def⟩ : ∃ e : ℝ, e=x-Real.pi/2 := ⟨_,rfl⟩
  have he : e∈Icc 0 (7/50:ℝ) := by
    rw [he_def]
    exact ⟨by linarith [hx.1],by linarith [hx.2,Arithmetic.pi_hand_enclosure.1]⟩
  have hs := Real.sin_le he.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := e)
  have hsq := pow_le_pow_left₀ he.1 he.2 2
  have hid : x=Real.pi/2+e := by rw [he_def]; ring
  rw [hid,Real.sin_add,Real.cos_add,Real.sin_pi_div_two,Real.cos_pi_div_two]
  linarith [he.2]

theorem extra_late_false (m n : Bool) {b B x : ℝ}
    (hb : b∈arc m) (hB : B∈arc n) (hx : x∈Icc (Real.pi/2) (171/100:ℝ)) :
    extra true (A b) b (A B) B x<0 := by
  have hs := arc_coordinates m hb
  have hA := (A_bounds (arc_subset hB)).1
  have hB0 := (arc_subset hB).1
  have ht := second_signs
    (show x∈Icc (Real.pi/2) Real.pi from
      ⟨hx.1,by linarith [hx.2,Arithmetic.pi_hand_enclosure.1]⟩)
  have hC := late_sum_lower hx
  have hCA := mul_nonneg (show 0≤Real.sin x+Real.cos x-17/20 by linarith)
    (show 0≤A B-1623/1000 by linarith [a2_precise.1])
  have hDB := mul_nonneg (show 0≤Real.sin x-Real.cos x by linarith) hB0
  have hw := FrameCoreArc.width_one_le x
  dsimp [extra,sign]
  nlinarith

theorem source_first_central (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n)
    (hhigh : m=false ∨ n=false) (j : Fin 4) (hj : j=0 ∨ j=3)
    {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x)
    (hx : angle s.positive t.positive x≤Real.pi/2) (hm : s.Feasible t j x) :
    0<angle s.positive t.positive x ∧ s.Feasible t (centralAxis s.positive) x := by
  cases hi : s.positive with
  | false =>
      have hj3 : j=3 := by
        rcases hj with rfl | hj3
        · exact False.elim ((original_negative_secondary_false m n s t hs ht hhigh hi x) hm)
        · exact hj3
      have hc : s.Feasible t (centralAxis s.positive) x := by
        rw [hi]
        rw [hj3] at hm
        exact hm
      have hp := actual_central_positive m n s t hs ht hhigh hgap hc
      rw [hi] at hp hc
      exact ⟨hp,hc⟩
  | true =>
      have hp : 0<angle s.positive t.positive x := by
        by_contra! hnp
        have hh := (nonpositive_signs m n s t hs ht hgap hnp).1
        rw [hi] at hh
        exact absurd hh (by decide)
      have hj0 : j=0 := by
        rcases hj with hj0 | rfl
        · exact hj0
        · exfalso
          have he := state_extra m n s t hs ht hi x
          have hn := extra_first_false m n (!t.positive)
            (state_fold m s hs).1 (state_fold n t ht).1 ⟨hp.le,hx⟩
          have hm' : 0≤forwardMargin 3 s.a s.b t.a t.b
              (sign s.positive) (sign t.positive) x := hm
          rw [he] at hn
          linarith
      have hc : s.Feasible t (centralAxis s.positive) x := by
        rw [hi]
        rw [hj0] at hm
        exact hm
      rw [hi] at hp hc
      exact ⟨hp,hc⟩

end SquaresInCircles.Eight.TableFree.FrameDiagonalGeometry
