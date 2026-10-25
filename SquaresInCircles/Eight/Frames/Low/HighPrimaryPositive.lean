module

public import SquaresInCircles.Eight.Frames.Low.HighPrimaryNegative

/-!
# Eight squares: the full low-source primary branch with positive high target

The physical weak margin forces the angle past a quarter turn.  The
target support is concave on its whole high arc, so its two intrinsic
endpoints suffice.  Their scalar functions are concave throughout the
remaining angular interval.  Source signs are restored by the exact
nonnegative original low label.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighPrimaryPositive
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameLowHighGeometry

def endpointA (j : Bool) : ℝ := if j then c0 else a2
def endpointB (j : Bool) : ℝ := if j then c0 else b2
def endpointH (j : Bool) : ℝ := if j then Real.pi/4 else H2
def C (j : Bool) : ℝ := 9/25+(9/10)*endpointB j
def S (j : Bool) : ℝ := 9/25-(9/10)*endpointA j
def K (j : Bool) : ℝ := Real.pi/2-L1-endpointH j+27/50-(9/10)*a1
def F (j : Bool) (z : ℝ) : ℝ := z+K j+C j*Real.cos z+S j*Real.sin z
def Fd (j : Bool) (z : ℝ) : ℝ := 1-C j*Real.sin z+S j*Real.cos z
def Fdd (j : Bool) (z : ℝ) : ℝ := -C j*Real.cos z-S j*Real.sin z

theorem coefficients (j : Bool) :
    (41/50:ℝ)≤C j ∧ C j≤117/100 ∧ -(18/25:ℝ)≤S j ∧ S j≤0 := by
  have hb := b2_bounds
  have ha := a2_bounds
  have hc := diagonal_precise
  cases j <;> dsimp [C,S,endpointA,endpointB] <;> repeat' constructor
  all_goals linarith

theorem F_deriv (j : Bool) (z : ℝ) : HasDerivAt (F j) (Fd j z) z := by
  have h := (((hasDerivAt_id' z).add_const (K j)).fun_add
    ((Real.hasDerivAt_cos z).const_mul (C j))).fun_add ((Real.hasDerivAt_sin z).const_mul (S j))
  refine h.congr_deriv ?_
  simp only [Fd]
  ring

theorem Fd_deriv (j : Bool) (z : ℝ) : HasDerivAt (Fd j) (Fdd j z) z := by
  have h := (((Real.hasDerivAt_sin z).const_mul (C j)).const_sub 1).fun_add
    ((Real.hasDerivAt_cos z).const_mul (S j))
  refine h.congr_deriv ?_
  simp only [Fdd]
  ring

theorem trig_bounds {z : ℝ} (hz : z∈Icc (0:ℝ) (9/20)) :
    0≤Real.sin z ∧ Real.sin z≤9/20 ∧ (89/100:ℝ)≤Real.cos z := by
  have ht := FrameLowPair.quadrant
    (show z∈Icc 0 (Real.pi/2) from ⟨hz.1,by linarith [hz.2,FrameLowPair.pi_lower]⟩)
  have hs := Real.sin_le hz.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := z)
  have hsq := pow_le_pow_left₀ hz.1 hz.2 2
  exact ⟨ht.1,by linarith [hz.2],by nlinarith⟩

theorem Fdd_negative (j : Bool) {z : ℝ} (hz : z∈Icc (0:ℝ) (9/20)) : Fdd j z<0 := by
  have hh := coefficients j
  have ht := trig_bounds hz
  have hC := mul_le_mul hh.1 ht.2.2 (by norm_num : (0:ℝ)≤89/100)
    (by linarith [hh.1] : 0≤C j)
  have hS := mul_le_mul (show -S j≤18/25 by linarith [hh.2.2.1]) ht.2.1 ht.1
    (by norm_num : (0:ℝ)≤18/25)
  dsimp [Fdd]
  nlinarith

theorem F_concave (j : Bool) : ConcaveOn ℝ (Icc (0:ℝ) (9/20)) (F j) :=
  concave_of_deriv2 (fun z _ => F_deriv j z) (fun z _ => Fd_deriv j z)
    (fun _ hz => (Fdd_negative j hz).le)

theorem initial_lower (j : Bool) : (99/100:ℝ)<F j 0 := by
  have hpi := Arithmetic.pi_hand_enclosure
  have hL := L1_precise.2
  have ha := a1_precise.2
  have hb := b2_bounds.1
  have hc := diagonal_precise.1
  have hH := H2_bounds.2
  cases j <;> norm_num [F,K,C,endpointB,endpointH] <;> linarith

theorem final_lower (j : Bool) : (8833/10000:ℝ)<F j (9/20:ℝ) := by
  have hh := coefficients j
  have ht := trig_bounds (show (9/20:ℝ)∈Icc (0:ℝ) (9/20) from ⟨by norm_num,le_rfl⟩)
  have hC := mul_le_mul_of_nonneg_left ht.2.2 (by linarith [hh.1] : 0≤C j)
  have hS := mul_le_mul (show -S j≤18/25 by linarith [hh.2.2.1]) ht.2.1 ht.1
    (by norm_num : (0:ℝ)≤18/25)
  have he := initial_lower j
  norm_num [F] at he ⊢
  nlinarith

theorem lower (j : Bool) {z : ℝ} (hz : z∈Icc (0:ℝ) (9/20)) :
    (8833/10000:ℝ)<F j z :=
  concave_gt_of_endpoints (F_concave j) hz
    (by linarith [initial_lower j]) (final_lower j)

theorem endpoint_support {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (Real.pi/2) (101/50:ℝ)) (hm : 0≤primary true b B x) :
    min (F false (x-Real.pi/2)) (F true (x-Real.pi/2))≤lowHighCost false true b B x := by
  let z := x-Real.pi/2
  have hz : z∈Icc (0:ℝ) (9/20) := by
    dsimp [z]
    constructor <;> linarith [hx.1,hx.2,Arithmetic.pi_hand_enclosure.1]
  have ht := trig_bounds hz
  have hxid : x=Real.pi/2+z := by dsimp [z]; ring
  have hsin : Real.sin x=Real.cos z := by rw [hxid,Real.sin_add]; simp
  have hcos : Real.cos x= -Real.sin z := by rw [hxid,Real.cos_add]; simp
  have hquad : x∈Icc (Real.pi/2) Real.pi :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hs := low_primary_source hb
    (show (9/10:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hscaled := mul_nonneg (show (0:ℝ)≤9/10 by norm_num) hm
  have hp : 0≤FrameHighArc.u+(9/10)*Real.cos x := by
    rw [hcos]
    dsimp [FrameHighArc.u]
    linarith [ht.2.1]
  have htarget := linear_endpoint_lower
    (p := FrameHighArc.u+(9/10)*Real.cos x)
    (q := (9/10)*Real.sin x-FrameHighArc.v) hp b2_mem.1 le_rfl hB
  simp only [linear,A_b2,A_c0] at htarget
  dsimp [primary,FrameLowMidGeometry.primary,sign] at hscaled
  rw [(second_width hquad).1] at hscaled
  rcases le_total
    ((FrameHighArc.u+(9/10)*Real.cos x)*a2+((9/10)*Real.sin x-FrameHighArc.v)*b2)
    ((FrameHighArc.u+(9/10)*Real.cos x)*c0+((9/10)*Real.sin x-FrameHighArc.v)*c0) with he | he
  · rw [min_eq_left he] at htarget
    apply (min_le_left _ _).trans
    dsimp [F,K,C,S,endpointA,endpointB,endpointH,lowHighCost,H,H2,sign]
    rw [(second_width hquad).2]
    rw [hsin,hcos] at htarget hscaled ⊢
    dsimp [z] at *
    nlinarith
  · rw [min_eq_right he] at htarget
    apply (min_le_right _ _).trans
    dsimp [F,K,C,S,endpointA,endpointB,endpointH,lowHighCost,H,FrameHighArc.k,sign]
    rw [(second_width hquad).2]
    rw [hsin,hcos] at htarget hscaled ⊢
    dsimp [z] at *
    nlinarith

theorem weak_separator (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤primary true b B x) : (8833/10000:ℝ)<lowHighCost i true b B x := by
  apply lt_of_lt_of_le _ (low_high_weaken_source i true hb)
  have hcut := FrameLowHighCuts.positive_primary_cut hb hB hx hm
  by_cases htail : (101/50:ℝ)≤x
  · exact low_high_tail false true hb hB (by simpa [lowHighTail] using htail)
  · have hdom : x∈Icc (Real.pi/2) (101/50:ℝ) := ⟨hcut.le,(lt_of_not_ge htail).le⟩
    have hz : x-Real.pi/2∈Icc (0:ℝ) (9/20) := by
      constructor <;> linarith [hdom.1,hdom.2,Arithmetic.pi_hand_enclosure.1]
    exact (lt_min (lower false hz) (lower true hz)).trans_le (endpoint_support hb hB hdom hm)

/-- Both target signs for the supplied original low-source primary owner. -/
theorem low_high_primary (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤primary k b B x) : (8833/10000:ℝ)<lowHighCost i k b B x := by
  cases k
  · exact FrameLowHighPrimaryNegative.weak_separator i hb hB hx hm
  · exact weak_separator i hb hB hx hm

end SquaresInCircles.Eight.FrameLowHighPrimaryPositive
