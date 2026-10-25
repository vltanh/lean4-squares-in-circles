module

public import SquaresInCircles.Eight.Frames.Low.HighArc
public import SquaresInCircles.Eight.Frames.Low.MidCuts

/-!
# Eight squares: original low/high signs, weak owners, and coarse angle cuts

These reductions use the original physical center gap and the whole
closed type arcs.  In particular, a negative high source cannot own
the transverse separator at any angle.  The nonpositive-angle cases
are excluded directly by their actual projections.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighGeometry
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus

abbrev secondary := FrameLowMidGeometry.secondary
abbrev primary := FrameLowMidGeometry.primary
def lowHighCost (i k : Bool) (b B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*L b-sign k*H B
def highLowCost (i k : Bool) (b B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*H b-sign k*L B
def lowHighTail (i k : Bool) : ℝ :=
  if i then (if k then 171/100 else 23/50) else (if k then 101/50 else 4/5)
def highLowTail (i k : Bool) : ℝ :=
  if i then (if k then 77/100 else 23/50) else (if k then 101/50 else 171/100)

theorem low_offset_tight (s : FramePair.State) (hs : s.branch=.low) :
    -(49/200:ℝ)<s.offset ∧ s.offset<49/200 := by
  have hh := FrameLowMidGeometry.low_intrinsic s hs
  cases hi : s.positive <;> simp only [State.offset,hi,sign,Bool.false_eq_true,↓reduceIte,one_mul,neg_one_mul]
  all_goals constructor <;> linarith

theorem low_high_angle (s t : FramePair.State) (hs : s.branch=.low)
    {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) : -(34/125:ℝ)<x := by
  have hl := low_offset_tight s hs
  have hh := t.offset_range
  dsimp [State.gap] at hgap
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem high_low_angle (s t : FramePair.State) (ht : t.branch=.low)
    {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) : -(34/125:ℝ)<x := by
  have hl := low_offset_tight t ht
  have hh := s.offset_range
  dsimp [State.gap] at hgap
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem low_high_tail (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : lowHighTail i k≤x) :
    (8833/10000:ℝ)<lowHighCost i k b B x := by
  have hs := L_bounds hb
  have ht := H_bounds hB
  have hch := CorePairGeometry.charge_upper x
  cases i <;> cases k <;> dsimp [lowHighTail,lowHighCost,sign] at *
  all_goals linarith [L1_precise.2,high_label_endpoint,Arithmetic.pi_hand_enclosure.2]

theorem high_low_tail (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1) (hx : highLowTail i k≤x) :
    (8833/10000:ℝ)<highLowCost i k b B x := by
  have hs := H_bounds hb
  have ht := L_bounds hB
  have hch := CorePairGeometry.charge_upper x
  cases i <;> cases k <;> dsimp [highLowTail,highLowCost,sign] at *
  all_goals linarith [L1_precise.2,high_label_endpoint,Arithmetic.pi_hand_enclosure.2]

theorem low_high_weaken_source (i k : Bool) {b B x : ℝ} (hb : b∈Icc 0 b1) :
    lowHighCost false k b B x≤lowHighCost i k b B x := by
  have hh := (L_bounds hb).1
  cases i <;> dsimp [lowHighCost,sign] <;> linarith

theorem high_low_weaken_source (i k : Bool) {b B x : ℝ} (hb : b∈Icc b2 c0) :
    highLowCost false k b B x≤highLowCost i k b B x := by
  have hh : 0≤H b := by linarith [(H_bounds hb).1,high_label_endpoint]
  cases i <;> dsimp [highLowCost,sign] <;> linarith

theorem negative_trig {x : ℝ} (hx : x∈Icc (-(34/125:ℝ)) 0) :
    Real.sin x≤0 ∧ -Real.sin x≤34/125 ∧ (963/1000:ℝ)<Real.cos x := by
  have hz : -x∈Icc 0 (34/125:ℝ) := ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
    (by linarith [hz.2,FrameLowPair.pi_lower])
  have hsu := Real.sin_le hz.1
  have hcu := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hz.1 hz.2 2
  simp only [Real.sin_neg,neg_sq] at hs hsu hsq
  exact ⟨by linarith,by linarith [hz.2],by nlinarith⟩

theorem nonpositive_secondary_owners (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 c0) (hB : B∈Icc 0 c0)
    (hx : x∈Icc (-(34/125:ℝ)) 0) (hm : 0≤ secondary i k b B x) :
    i=true ∧ k=false := by
  have ht := negative_trig hx
  have hA := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤A B by linarith [(A_bounds hB).1,c0_bounds.1]) ht.1
  have hB0 := mul_nonneg hB.1 (by linarith [ht.2.2] : 0≤Real.cos x)
  have hBu := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hB.1
  have hw := FrameCoreArc.width_one_le x
  cases i <;> cases k <;> norm_num [secondary,FrameLowMidGeometry.secondary,sign] at hm ⊢
  all_goals linarith [hb.1,hb.2,hB.2,c0_bounds.2]

theorem nonpositive_primary_false (k : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 c0) (hB : B∈Icc 0 c0)
    (hx : x∈Icc (-(34/125:ℝ)) 0) : primary k b B x<0 := by
  have ht := negative_trig hx
  have hs := A_bounds hb
  have htarget := A_bounds hB
  have hA0 : 0≤A B := by linarith [htarget.1,c0_bounds.1]
  have hAc := mul_le_mul
    (show (899/1000:ℝ)≤A B by linarith [htarget.1,c0_bounds.1]) ht.2.2.le
    (by norm_num : (0:ℝ)≤963/1000) hA0
  have hBsin := mul_le_mul
    (show B≤9/10 by linarith [hB.2,c0_bounds.2]) ht.2.1
    (by linarith [ht.1] : 0≤-Real.sin x) (by norm_num : (0:ℝ)≤9/10)
  have hBneg := mul_nonpos_of_nonneg_of_nonpos hB.1 ht.1
  have hw := FrameCoreArc.width_one_le x
  cases k <;> dsimp [primary,FrameLowMidGeometry.primary,sign]
  all_goals nlinarith [hs.2,a0_precise.2]

theorem high_source_secondary_positive (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hm : 0≤ secondary i k b B x) : i=true := by
  cases i with
  | true => rfl
  | false =>
      have hp := low_projection_lt k hB x
      have hw := FrameCoreArc.width_one_le x
      have hh := high_bounds hb
      dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hm hp
      exfalso
      linarith

theorem high_low_positive_cut {b B x : ℝ}
    (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤ secondary true true b B x) : (2/25:ℝ)<x := by
  by_contra! hsmall
  by_cases hn : x≤0
  · have hh := nonpositive_secondary_owners true true
      ⟨b2_mem.1.trans hb.1,hb.2⟩ ⟨hB.1,hB.2.trans b1_mem.2⟩ ⟨hx,hn⟩ hm
    cases hh.2
  · have hx0 : 0≤x := (lt_of_not_ge hn).le
    have hxq : x∈Icc 0 (Real.pi/2) :=
      ⟨hx0,by linarith [hsmall,FrameLowPair.pi_lower]⟩
    have ht := FrameLowPair.quadrant hxq
    have hs := Real.sin_le hx0
    have hc := Real.one_sub_sq_div_two_le_cos (x := x)
    have hsq := pow_le_pow_left₀ hx0 hsmall 2
    have hAc := mul_le_mul_of_nonneg_right
      (show A B-1/2≤183/200 by linarith [(A_low_bounds hB).2,a0_precise.2]) ht.1
    have hBcos := mul_nonneg hB.1 ht.2.2.1
    dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hm
    rw [(first_width hxq).1] at hm
    nlinarith [hb.2,c0_bounds.2]

theorem high_low_primary_cut (k : Bool) {b B x : ℝ}
    (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤primary k b B x) : (6/5:ℝ)<x := by
  by_contra! hsmall
  by_cases hn : x≤0
  · exact (not_lt_of_ge hm) (nonpositive_primary_false k
      ⟨b2_mem.1.trans hb.1,hb.2⟩ ⟨hB.1,hB.2.trans b1_mem.2⟩ ⟨hx,hn⟩)
  · have hx0 : 0≤x := (lt_of_not_ge hn).le
    have ht := FrameLowPair.quadrant
      (show x∈Icc 0 (Real.pi/2) from ⟨hx0,by linarith [hsmall,FrameLowPair.pi_lower]⟩)
    have hse := sin_lower_seven (show (0:ℝ)≤6/5 by norm_num)
    have hce := cos_lower_six (show (0:ℝ)≤6/5 by norm_num)
    norm_num at hse hce
    have hproj := FrameLowMidCuts.harmonic_endpoint_lower
      (p := (899/500:ℝ)) (q := (7/40:ℝ)) (t := (6/5:ℝ))
      (by norm_num) (by norm_num)
      ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩ ⟨hx0,hsmall⟩
      (by norm_num : (7/10:ℝ)<899/500) (by linarith :
        (7/10:ℝ)<(899/500)*Real.cos (6/5:ℝ)+(7/40)*Real.sin (6/5:ℝ))
    have hAc := mul_le_mul_of_nonneg_right
      (show (899/500:ℝ)≤A B+1/2 by linarith [(A_low_bounds hB).1,a1_precise.1]) ht.2.2.1
    have hBs := mul_le_mul_of_nonneg_right
      (show B≤13/40 by linarith [hB.2,b1_bounds.2]) ht.1
    have hBs0 := mul_nonneg hB.1 ht.1
    have hsource := (high_bounds hb).2.2.2
    dsimp [primary,FrameLowMidGeometry.primary] at hm
    rw [(first_width ⟨hx0,by linarith [hsmall,FrameLowPair.pi_lower]⟩).1] at hm
    cases k <;> dsimp [sign] at hm <;> nlinarith

theorem state_low_high_cost (s t : FramePair.State) (hs : s.branch=.low)
    (ht : t.branch=.high) (x : ℝ) :
    s.cost t x=lowHighCost s.positive t.positive s.b t.b x := by
  rw [State.cost,state_low_label s hs,state_high_label t ht]
  rfl

theorem state_high_low_cost (s t : FramePair.State) (hs : s.branch=.high)
    (ht : t.branch=.low) (x : ℝ) :
    s.cost t x=highLowCost s.positive t.positive s.b t.b x := by
  rw [State.cost,state_high_label s hs,state_low_label t ht]
  rfl

end SquaresInCircles.Eight.FrameLowHighGeometry
