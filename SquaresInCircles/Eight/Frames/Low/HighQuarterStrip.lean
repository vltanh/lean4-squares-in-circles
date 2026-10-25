module

public import SquaresInCircles.Eight.Frames.Low.HighExtendedQuarter
public import SquaresInCircles.Eight.Frames.Low.HighQuarterCalculus

/-!
# Eight squares: the original positive low/high pair throughout the quarter strip

This proof uses only the original weak source-secondary margin.  The
fixed-target scalar contact has a monotone angle cost on the nearby
part of the high arc; the remaining part has a direct strict reserve.
The analytically continued aligned inequality closes both cases.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighQuarterStrip
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus
open FrameLowHighParallelCalculus FrameLowHighParallelBounds
open FrameLowHighQuarterCalculus

theorem quarter_width (x : ℝ) : pairWidth (Real.pi/2+x)=pairWidth x := by
  simp only [pairWidth,Real.sin_add,Real.cos_add,Real.sin_pi_div_two,Real.cos_pi_div_two,
    zero_mul,one_mul,zero_sub,add_zero,abs_neg]
  ring

theorem quarter_charge (x : ℝ) : periodicFrameCost (Real.pi/2+x)=periodicFrameCost x := by
  simpa only [add_comm] using periodicFrameCost_pi_half x

theorem source_contact_le (positive : Bool) {b B x : ℝ}
    (hB : B∈Icc b2 c0) (hx : x∈angleDomain positive)
    (hm : 0≤ secondary true true b B (Real.pi/2+x)) : height positive (A B) x≤b := by
  dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hm
  rw [quarter_width,← width_eq positive hx] at hm
  simp only [Real.sin_add,Real.cos_add,Real.sin_pi_div_two,Real.cos_pi_div_two,
    zero_mul,one_mul,zero_sub] at hm
  rw [height_eq positive hB]
  nlinarith

theorem actual_cost (positive : Bool) {b B x : ℝ} (hB : B∈Icc b2 c0)
    (hx : x∈angleDomain positive) :
    lowHighCost true true b B (Real.pi/2+x)=
      x-(9/50)*(FrameLowHighParallelCalculus.width positive x-1)+L b+G (A B) := by
  dsimp [lowHighCost,sign]
  rw [quarter_charge,quarter_label hB,← width_charge positive hx]
  ring

theorem contact_cost_le (positive : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : x∈angleDomain positive)
    (hm : 0≤ secondary true true b B (Real.pi/2+x)) :
    cost positive B x≤lowHighCost true true b B (Real.pi/2+x) := by
  have hz := height_domain positive hB hx
  have hsource : height positive (A B) x∈Icc (-(1/4:ℝ)) b1 :=
    ⟨hz.1,by linarith [hz.2,b1_bounds.1]⟩
  have hbwide : b∈Icc (-(1/4:ℝ)) b1 := ⟨by linarith [hb.1],hb.2⟩
  have hlabel := source_label_monotone hsource hbwide (source_contact_le positive hB hx hm)
  rw [actual_cost positive hB hx]
  dsimp [cost]
  linarith

@[simp] theorem cost_zero (positive : Bool) (B : ℝ) :
    cost positive B 0=L (1-A B)+G (A B) := by
  cases positive <;> simp [cost,height,FrameLowHighParallelCalculus.width]

theorem aligned_lower (positive : Bool) {B : ℝ} (hB : B∈Icc b2 c0) :
    (8833/10000:ℝ)<cost positive B 0 := by
  have hA := A_high_bounds hB
  have hzero : 1-A B∈FrameLowHighExtendedQuarter.domain := by
    dsimp [FrameLowHighExtendedQuarter.domain,FrameLowHighAligned.b0]
    constructor <;> linarith [hA.1,hA.2,a2_bounds.2]
  have hh := FrameLowHighExtendedQuarter.strict_lower hzero
  have hcancel : 1-(1-A B)=A B := by ring
  rw [hcancel] at hh
  simpa only [cost_zero] using hh

theorem move_to_zero (positive : Bool) {B x : ℝ} (hB : B∈Icc b2 c0)
    (hx : x∈angleDomain positive) (hcap : positive=false → A B≤103/100) :
    cost positive B 0≤cost positive B x := by
  cases positive with
  | false =>
      have ha : AntitoneOn (cost false B) (Icc x 0) := by
        apply antiOn_of_hasDeriv_nonpos
        · intro t ht
          exact (cost_deriv false hB (show t∈angleDomain false from
            ⟨hx.1.trans ht.1,ht.2⟩)).continuousAt.continuousWithinAt
        · intro t ht
          exact cost_deriv false hB ⟨hx.1.trans ht.1.le,ht.2.le⟩
        · intro t ht
          exact (negative_derivative hB (hcap rfl) ⟨hx.1.trans ht.1.le,ht.2.le⟩).le
      exact ha ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2
  | true =>
      have hm : MonotoneOn (cost true B) (Icc 0 x) := by
        apply monoOn_of_hasDeriv_nonneg
        · intro t ht
          exact (cost_deriv true hB (show t∈angleDomain true from
            ⟨ht.1,ht.2.trans hx.2⟩)).continuousAt.continuousWithinAt
        · intro t ht
          exact cost_deriv true hB ⟨ht.1.le,ht.2.le.trans hx.2⟩
        · intro t ht
          exact (positive_derivative hB ⟨ht.1.le,ht.2.le.trans hx.2⟩).le
      exact hm ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1

theorem far_target (positive : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : x∈angleDomain positive)
    (hfar : (103/100:ℝ)≤A B) :
    (8833/10000:ℝ)<lowHighCost true true b B (Real.pi/2+x) := by
  have hG := G_monotone
    (show (103/100:ℝ)∈extendedDomain by constructor <;> norm_num [extendedDomain])
    (target_chart hB) hfar
  have hw := width_bounds positive hx
  have hL := (L_bounds hb).1
  have hxlow : -(1/50:ℝ)≤x := by cases positive <;> dsimp [angleDomain] at hx <;> linarith [hx.1]
  rw [actual_cost positive hB hx]
  linarith [G_reference]

theorem phase (positive : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : x∈angleDomain positive)
    (hm : 0≤ secondary true true b B (Real.pi/2+x)) :
    (8833/10000:ℝ)<lowHighCost true true b B (Real.pi/2+x) := by
  by_cases hcap : A B≤103/100
  · exact (aligned_lower positive hB).trans_le
      ((move_to_zero positive hB hx (fun _ => hcap)).trans
        (contact_cost_le positive hb hB hx hm))
  · exact far_target positive hb hB hx (le_of_not_ge hcap)

theorem weak_separator {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (-(1/50:ℝ)) (1/50))
    (hm : 0≤ secondary true true b B (Real.pi/2+x)) :
    (8833/10000:ℝ)<lowHighCost true true b B (Real.pi/2+x) := by
  by_cases hsign : x≤0
  · exact phase false hb hB ⟨hx.1,hsign⟩ hm
  · exact phase true hb hB ⟨le_of_not_ge hsign,hx.2⟩ hm

theorem actual_angle {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (Real.pi/2-1/50) (Real.pi/2+1/50))
    (hm : 0≤ secondary true true b B x) :
    (8833/10000:ℝ)<lowHighCost true true b B x := by
  have he : x-Real.pi/2∈Icc (-(1/50:ℝ)) (1/50) := by constructor <;> linarith [hx.1,hx.2]
  have hid : Real.pi/2+(x-Real.pi/2)=x := by ring
  have hmargin : 0≤ secondary true true b B (Real.pi/2+(x-Real.pi/2)) := by rwa [hid]
  simpa only [hid] using weak_separator hb hB he hmargin

end SquaresInCircles.Eight.FrameLowHighQuarterStrip
