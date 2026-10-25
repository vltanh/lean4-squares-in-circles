module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Frames.Low.HighSecondaryOpposite
public import SquaresInCircles.Eight.Frames.Low.HighParallelCalculus
public import SquaresInCircles.Eight.Frames.Low.MidSecondaryEndpoints
public import SquaresInCircles.Eight.Frames.Low.MidSecondaryContinuation

/-!
# Eight squares: the low/middle pairs

The pair inequality `γ(s, t) < cost` for a low state against a middle one and for a middle state
against a low one, on each of the four forward axes, at a gap of at least `19/25`
(`low_mid_pair`, `mid_low_pair`), and on the edges of a boundary cycle at `Q0`
(`low_mid_cycle_pair`, `mid_low_cycle_pair`). The two axes of the source give a cost above
`1801/2000` for both signs (`source_secondary_low_mid`, `source_secondary_mid_low`,
`source_primary_low_mid`, `source_primary_mid_low`), and the two axes of the target are axes of
the source of the reversed pair. The given witness is used as it is, and the ends of the arcs
belong to the domains.
-/

section
/-!
## The primary axis of a low source against a negative high target

A low state and a negative high state separated along the primary axis of the low square, at a
frame angle `x ≥ -34/125`, have the cost of the pair above `8833/10000`, for both signs of the
source (`weak_separator`). The weak margin forces `x > 3/5`, and up to `4/5` the cost is at least
`F x`, with the source at the low endpoint `a1`, its label kept, and the target bounded by the
support of the containing circle (`circle_support`). That support increases, since the rotating
norm `N` has derivative at most `lam = 7/10` (`Nd_upper`, `F_monotone`), and `F (3/5)` exceeds
`8833/10000` (`initial_lower`, `lower`); beyond `4/5` the tail `low_high_tail` applies.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighPrimaryNegative
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameLowHighGeometry

def lam : ℝ := 7/10
def N (x : ℝ) : ℝ :=
  CircularNorm.norm (FrameHighArc.u^2+FrameHighArc.v^2+lam^2)
    (-2*lam*FrameHighArc.u) (-2*lam*FrameHighArc.v) x
def Nd (x : ℝ) : ℝ :=
  CircularNorm.d1 (FrameHighArc.u^2+FrameHighArc.v^2+lam^2)
    (-2*lam*FrameHighArc.u) (-2*lam*FrameHighArc.v) x
def K : ℝ := 9/100+FrameHighArc.k-L1-lam*a1+lam/2+
  (FrameHighArc.u-FrameHighArc.v)/2
def F (x : ℝ) : ℝ := x+K+(61/100)*Real.sin x-(9/100)*Real.cos x-R*N x
def Fd (x : ℝ) : ℝ := 1+(61/100)*Real.cos x+(9/100)*Real.sin x-R*Nd x

theorem energy_positive (x : ℝ) :
    0<CircularNorm.energy (FrameHighArc.u^2+FrameHighArc.v^2+lam^2)
      (-2*lam*FrameHighArc.u) (-2*lam*FrameHighArc.v) x := by
  have he : CircularNorm.energy (FrameHighArc.u^2+FrameHighArc.v^2+lam^2)
      (-2*lam*FrameHighArc.u) (-2*lam*FrameHighArc.v) x=
        (FrameHighArc.u-lam*Real.cos x)^2+(FrameHighArc.v-lam*Real.sin x)^2 := by
    dsimp [CircularNorm.energy]
    linear_combination -lam^2*(Real.sin_sq_add_cos_sq x)
  rw [he]
  by_contra! hbad
  have ha : FrameHighArc.u-lam*Real.cos x=0 := by
    apply sq_eq_zero_iff.mp
    nlinarith [sq_nonneg (FrameHighArc.u-lam*Real.cos x),
      sq_nonneg (FrameHighArc.v-lam*Real.sin x)]
  have hb : FrameHighArc.v-lam*Real.sin x=0 := by
    apply sq_eq_zero_iff.mp
    nlinarith [sq_nonneg (FrameHighArc.u-lam*Real.cos x),
      sq_nonneg (FrameHighArc.v-lam*Real.sin x)]
  have hc : Real.cos x=(10/7)*FrameHighArc.u := by dsimp [lam] at ha; linarith
  have hs : Real.sin x=(10/7)*FrameHighArc.v := by dsimp [lam] at hb; linarith
  have hunit := Real.sin_sq_add_cos_sq x
  rw [hc,hs] at hunit
  norm_num [FrameHighArc.u,FrameHighArc.v] at hunit

theorem N_positive (x : ℝ) : 0<N x := CircularNorm.norm_pos (energy_positive x)
theorem N_square (x : ℝ) :
    (N x)^2=FrameHighArc.u^2+FrameHighArc.v^2+lam^2-
      2*lam*(FrameHighArc.u*Real.cos x+FrameHighArc.v*Real.sin x) := by
  have hh := CircularNorm.norm_sq (energy_positive x).le
  convert hh using 1 <;> dsimp [N,CircularNorm.energy]
  ring
theorem N_deriv (x : ℝ) : HasDerivAt N (Nd x) x :=
  CircularNorm.norm_hasDerivAt (energy_positive x)

/-- The derivative of the norm is at most `lam`, the speed of the moving force. -/
theorem Nd_upper (x : ℝ) : Nd x≤lam := by
  have hid : (N x)^2-(FrameHighArc.u*Real.sin x-FrameHighArc.v*Real.cos x)^2=
      (lam-FrameHighArc.u*Real.cos x-FrameHighArc.v*Real.sin x)^2 := by
    rw [N_square]
    linear_combination -(FrameHighArc.u^2+FrameHighArc.v^2)*(Real.sin_sq_add_cos_sq x)
  have hp := N_positive x
  have hforce : FrameHighArc.u*Real.sin x-FrameHighArc.v*Real.cos x≤N x := by
    by_contra! hbad
    have hh := mul_pos (sub_pos.mpr hbad)
      (show 0<FrameHighArc.u*Real.sin x-FrameHighArc.v*Real.cos x+N x by linarith)
    nlinarith [sq_nonneg (lam-FrameHighArc.u*Real.cos x-FrameHighArc.v*Real.sin x)]
  have he : Nd x=lam*(FrameHighArc.u*Real.sin x-FrameHighArc.v*Real.cos x)/N x := by
    dsimp [Nd,CircularNorm.d1,CircularNorm.slope,N]
    ring
  rw [he]
  apply (div_le_iff₀ hp).2
  exact mul_le_mul_of_nonneg_left hforce (by norm_num [lam])

theorem F_deriv (x : ℝ) : HasDerivAt F (Fd x) x := by
  have h := ((((hasDerivAt_id' x).add_const K).fun_add
    ((Real.hasDerivAt_sin x).const_mul (61/100))).fun_sub
      ((Real.hasDerivAt_cos x).const_mul (9/100))).fun_sub ((N_deriv x).const_mul R)
  refine h.congr_deriv ?_
  simp only [Fd]
  ring

theorem F_monotone : MonotoneOn F (Icc (3/5:ℝ) (4/5)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (F_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => F_deriv x
  · intro x hx
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi/2)≤(3/5:ℝ))
      (by linarith [hx.2,FrameLowPair.pi_lower]) hx.1.le
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith [hx.1] : 0≤x) (by linarith [FrameLowPair.pi_lower] : (4/5:ℝ)≤Real.pi)
      hx.2.le
    have hsE := sin_lower_seven (show (0:ℝ)≤3/5 by norm_num)
    have hcE := cos_lower_six (show (0:ℝ)≤4/5 by norm_num)
    norm_num at hsE hcE
    have hprod := mul_le_mul_of_nonneg_left (Nd_upper x) R_pos.le
    have hR : R<(99/50:ℝ) := by linarith [radius_precise.2]
    dsimp [Fd,lam] at *
    nlinarith

theorem initial_norm : N (3/5:ℝ)<1/20 := by
  have hs := sin_lower_seven (show (0:ℝ)≤3/5 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤3/5 by norm_num)
  have he := N_square (3/5)
  have hp := N_positive (3/5)
  norm_num [lam,FrameHighArc.u,FrameHighArc.v] at hs hc he
  nlinarith

theorem initial_lower : (8833/10000:ℝ)<F (3/5:ℝ) := by
  have hR : R<(99/50:ℝ) := by linarith [radius_precise.2]
  have hnorm := mul_le_mul hR.le initial_norm.le (N_positive (3/5)).le
    (by norm_num : (0:ℝ)≤99/50)
  have hs := sin_lower_seven (show (0:ℝ)≤3/5 by norm_num)
  norm_num at hs
  have hc := Real.cos_le_one (3/5:ℝ)
  have hk := high_constant_lower
  have hL := L1_precise.2
  have ha := a1_precise.2
  dsimp [F,K,lam,FrameHighArc.u,FrameHighArc.v]
  linarith

theorem lower {x : ℝ} (hx : x∈Icc (3/5:ℝ) (4/5)) : (8833/10000:ℝ)<F x :=
  initial_lower.trans_le (F_monotone ⟨le_rfl,by norm_num⟩ hx hx.1)

theorem circle_support {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (3/5:ℝ) (4/5)) (hm : 0≤primary false b B x) :
    F x≤lowHighCost false false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hs := low_primary_source hb (show lam∈Icc (0:ℝ) 1 by constructor <;> norm_num [lam])
  have hscaled := mul_nonneg (show (0:ℝ)≤lam by norm_num [lam]) hm
  have ht := circle_linear_lower (A_circle ⟨b2_mem.1.trans hB.1,hB.2⟩)
    (-FrameHighArc.u+lam*Real.cos x) (FrameHighArc.v-lam*Real.sin x)
  have hn : Real.sqrt ((-FrameHighArc.u+lam*Real.cos x)^2+
      (FrameHighArc.v-lam*Real.sin x)^2)=N x := by
    dsimp [N,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination lam^2*(Real.sin_sq_add_cos_sq x)
  rw [hn] at ht
  dsimp [primary,FrameLowMidGeometry.primary,sign] at hscaled
  rw [(first_width hxq).1] at hscaled
  dsimp [F,K,lowHighCost,H,sign]
  rw [(first_width hxq).2]
  dsimp [lam] at hs ht hscaled ⊢
  nlinarith

theorem weak_separator (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤primary false b B x) : (8833/10000:ℝ)<lowHighCost i false b B x := by
  apply lt_of_lt_of_le _ (low_high_weaken_source i false hb)
  have hcut := FrameLowHighCuts.negative_primary_cut hb hB hx hm
  by_cases htail : (4/5:ℝ)≤x
  · exact low_high_tail false false hb hB (by simpa [lowHighTail] using htail)
  · exact (lower ⟨hcut.le,(lt_of_not_ge htail).le⟩).trans_le
      (circle_support hb hB ⟨hcut.le,(lt_of_not_ge htail).le⟩ hm)

end SquaresInCircles.Eight.FrameLowHighPrimaryNegative
end
end
end

section
/-!
## The full low-source primary branch with positive high target

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
end
end
end

section
/-!
## The norm of the middle target on the secondary axis

For a low source and a positive middle target on the secondary axis of the source, the support of
the target on its circle involves the norm `N lam x = √(energy lam x)`, positive with the
derivative `Nd lam x` for `0 ≤ lam ≤ 1` (`N_positive`, `N_deriv`), for both signs of the source.
With a multiplier `lam` and a lower bound `f` of the source term, the cost is at least
`F lam f second x` in the first or the second quadrant (`circle_support`, `F_deriv`). On the first
quadrant `N (189/200) x < 3` (`N_first_upper`), and on `[0, 3]` the quadratic majorant
`n ≤ 13/10 + (5/26) n² - (n² - (13/5)²)²/216` holds, by a nonnegative product
(`quadratic_majorant`); `tangent_majorant` is `n ≤ t/2 + n²/(2t)`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowMidTransverseNorm
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus

def energy (lam x : ℝ) : ℝ :=
  p^2+q^2+lam^2+2*lam*(p*Real.sin x-q*Real.cos x)
def N (lam x : ℝ) : ℝ := Real.sqrt (energy lam x)
def Nd (lam x : ℝ) : ℝ := lam*(p*Real.cos x+q*Real.sin x)/N lam x
def K (lam f : ℝ) : ℝ := 9/100+f-cM+(p+q+lam)/2
def cosCoefficient (lam : ℝ) (second : Bool) : ℝ := if second then lam-9/100 else 9/100
def F (lam f : ℝ) (second : Bool) (x : ℝ) : ℝ :=
  x+K lam f+(lam-9/100)*Real.sin x-cosCoefficient lam second*Real.cos x-R*N lam x
def Fd (lam : ℝ) (second : Bool) (x : ℝ) : ℝ :=
  1+(lam-9/100)*Real.cos x+cosCoefficient lam second*Real.sin x-R*Nd lam x

theorem energy_positive {lam : ℝ} (hlam : lam∈Icc (0:ℝ) 1) (x : ℝ) : 0<energy lam x := by
  have hp : 0<p+lam*Real.sin x := by
    have hh := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin x) hlam.1
    dsimp [p]
    nlinarith [hlam.2]
  have he : energy lam x=(p+lam*Real.sin x)^2+(q-lam*Real.cos x)^2 := by
    dsimp [energy]
    linear_combination -lam^2*(Real.sin_sq_add_cos_sq x)
  rw [he]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hp) (sq_nonneg _)

theorem N_positive {lam : ℝ} (hlam : lam∈Icc (0:ℝ) 1) (x : ℝ) : 0<N lam x :=
  Real.sqrt_pos.mpr (energy_positive hlam x)
theorem N_square {lam : ℝ} (hlam : lam∈Icc (0:ℝ) 1) (x : ℝ) : (N lam x)^2=energy lam x :=
  Real.sq_sqrt (energy_positive hlam x).le
theorem N_deriv {lam : ℝ} (hlam : lam∈Icc (0:ℝ) 1) (x : ℝ) :
    HasDerivAt (N lam) (Nd lam x) x := by
  show HasDerivAt (fun y => Real.sqrt (p^2+q^2+lam^2+2*lam*(p*Real.sin y-q*Real.cos y))) _ x
  convert (((((Real.hasDerivAt_sin x).const_mul p).fun_sub
    ((Real.hasDerivAt_cos x).const_mul q)).const_mul (2*lam)).const_add
      (p^2+q^2+lam^2)).sqrt (energy_positive hlam x).ne' using 1
  simp only [Nd,N,energy]
  ring
theorem F_deriv {lam : ℝ} (hlam : lam∈Icc (0:ℝ) 1) (f : ℝ) (second : Bool) (x : ℝ) :
    HasDerivAt (F lam f second) (Fd lam second x) x := by
  unfold F
  convert ((((hasDerivAt_id' x).add_const (K lam f)).fun_add
    ((Real.hasDerivAt_sin x).const_mul (lam-9/100))).fun_sub
      ((Real.hasDerivAt_cos x).const_mul (cosCoefficient lam second))).fun_sub
        ((N_deriv hlam x).const_mul R) using 1
  simp only [Fd]
  ring

theorem N_first_upper {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) : N (189/200) x<3 := by
  have ht := FrameLowPair.quadrant hx
  have hp := N_positive (show (189/200:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num) x
  have hs := N_square (show (189/200:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num) x
  dsimp [energy,p,q] at hs
  nlinarith [ht.2.1,ht.2.2.1]

theorem quadratic_majorant {n : ℝ} (hn : n∈Icc (0:ℝ) 3) :
    n≤13/10+(5/26)*n^2-(n^2-(13/5)^2)^2/216 := by
  have hs := pow_le_pow_left₀ (show 0≤n+13/5 by linarith [hn.1])
    (show n+13/5≤28/5 by linarith [hn.2]) 2
  have hf : 0≤5/26-(n+13/5)^2/216 := by nlinarith
  have hp := mul_nonneg (sq_nonneg (n-13/5)) hf
  have he : 13/10+(5/26)*n^2-(n^2-(13/5)^2)^2/216-n=
      (n-13/5)^2*(5/26-(n+13/5)^2/216) := by ring
  linarith

theorem tangent_majorant {n t : ℝ} (ht : 0<t) : n≤t/2+n^2/(2*t) := by
  have hs := sq_nonneg (n-t)
  have hh : n≤(t^2+n^2)/(2*t) :=
    (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) ht)).2 (by nlinarith)
  calc
    n≤(t^2+n^2)/(2*t) := hh
    _=t/2+n^2/(2*t) := by field_simp

theorem circle_support (i : Bool) {lam f b B x : ℝ}
    (hlam : lam∈Icc (0:ℝ) 1) (_hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2)
    (hsource : f≤ sign i*(L b-lam*b)) (second : Bool)
    (hx : if second then x∈Icc (Real.pi/2) Real.pi else x∈Icc 0 (Real.pi/2))
    (hm : 0≤FrameLowMidGeometry.secondary i true b B x) :
    F lam f second x≤FrameLowMidGeometry.lowMidCost i true b B x := by
  have hscaled := mul_nonneg hlam.1 hm
  have ht := circle_linear_lower
    (A_circle ⟨b1_mem.1.trans hB.1,hB.2.trans b2_mem.2⟩)
    (-p-lam*Real.sin x) (lam*Real.cos x-q)
  have hn : Real.sqrt ((-p-lam*Real.sin x)^2+(lam*Real.cos x-q)^2)=N lam x := by
    dsimp [N,energy]
    congr 1
    linear_combination lam^2*(Real.sin_sq_add_cos_sq x)
  rw [hn] at ht
  cases second with
  | false =>
      simp only [Bool.false_eq_true,↓reduceIte] at hx
      dsimp [FrameLowMidGeometry.secondary] at hscaled
      rw [(first_width hx).1] at hscaled
      dsimp [F,K,cosCoefficient,FrameLowMidGeometry.lowMidCost,M]
      rw [(first_width hx).2]
      cases i <;> norm_num [sign] at hscaled hsource ⊢ <;> linarith
  | true =>
      simp only [↓reduceIte] at hx
      dsimp [FrameLowMidGeometry.secondary] at hscaled
      rw [(second_width hx).1] at hscaled
      dsimp [F,K,cosCoefficient,FrameLowMidGeometry.lowMidCost,M]
      rw [(second_width hx).2]
      cases i <;> norm_num [sign] at hscaled hsource ⊢ <;> linarith

end SquaresInCircles.Eight.FrameLowMidTransverseNorm
end
end
end

section
/-!
## The full positive low-to-middle transverse support

One quadratic norm majorant produces a second-harmonic polynomial.
Its third derivative is positive on the complete physical interval;
the upper-curvature chord gives a strict lower bound.  The proof retains
the actual radical support and the original weak separator.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowMidTransversePositive
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus
open FrameLowMidTransverseNorm

def r : ℝ := 1978787508/1000000000
def lam : ℝ := 189/200
def m : ℝ := p^2+q^2
def e : ℝ := m+lam^2-(13/5)^2
def E0 : ℝ := K lam (-(1/100000))-
  r*(13/10+(5/26)*(m+lam^2))+(r/216)*(e^2+2*lam^2*m)
def ca : ℝ := lam-9/100-r*lam*p/(13/5)+(r/54)*e*lam*p
def cb : ℝ := -(9/100)+r*lam*q/(13/5)-(r/54)*e*lam*q
def cc : ℝ := -r*lam^2*p*q/54
def cd : ℝ := r*lam^2*(q^2-p^2)/108
def E (x : ℝ) : ℝ :=
  x+E0+ca*Real.sin x+cb*Real.cos x+cc*Real.sin (2*x)+cd*Real.cos (2*x)
def Ed (x : ℝ) : ℝ :=
  1+ca*Real.cos x-cb*Real.sin x+2*cc*Real.cos (2*x)-2*cd*Real.sin (2*x)
def Edd (x : ℝ) : ℝ :=
  -ca*Real.sin x-cb*Real.cos x-4*cc*Real.sin (2*x)-4*cd*Real.cos (2*x)
def Eddd (x : ℝ) : ℝ :=
  -ca*Real.cos x+cb*Real.sin x-8*cc*Real.cos (2*x)+8*cd*Real.sin (2*x)

theorem second_harmonic_identity (x : ℝ) :
    E x=x+K lam (-(1/100000))+(lam-9/100)*Real.sin x-(9/100)*Real.cos x-
      r*(13/10+(5/26)*energy lam x-(energy lam x-(13/5)^2)^2/216) := by
  have hs : Real.sin (2*x)=2*Real.sin x*Real.cos x := by
    rw [two_mul,Real.sin_add]
    ring
  have hc : Real.cos (2*x)=(Real.cos x)^2-(Real.sin x)^2 := by
    rw [two_mul,Real.cos_add]
    ring
  dsimp [E,E0,ca,cb,cc,cd,e,m,energy]
  rw [hs,hc]
  dsimp [r,lam,p,q]
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem norm_support {x : ℝ} (hx : x∈Icc (19/25:ℝ) (7/5)) :
    E x≤F lam (-(1/100000)) false x := by
  have hlam : lam∈Icc (0:ℝ) 1 := by constructor <;> norm_num [lam]
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hn := N_positive hlam x
  have hnU : N lam x≤3 := by simpa [lam] using (N_first_upper hxq).le
  have hmajor := quadratic_majorant ⟨hn.le,hnU⟩
  have hR : R≤r := by simpa [r] using radius_precise.2.le
  have hr : 0≤r := by norm_num [r]
  have hscaled := mul_le_mul hR hmajor hn.le hr
  rw [N_square hlam x] at hscaled
  rw [second_harmonic_identity]
  dsimp [F,cosCoefficient]
  linarith

theorem E_deriv (x : ℝ) : HasDerivAt E (Ed x) x := by
  have hs := ((hasDerivAt_id' x).const_mul 2).sin
  have hc := ((hasDerivAt_id' x).const_mul 2).cos
  unfold E
  convert (((((hasDerivAt_id' x).add_const E0).fun_add
    ((Real.hasDerivAt_sin x).const_mul ca)).fun_add
      ((Real.hasDerivAt_cos x).const_mul cb)).fun_add (hs.const_mul cc)).fun_add
        (hc.const_mul cd) using 1
  simp only [Ed]
  ring

theorem Ed_deriv (x : ℝ) : HasDerivAt Ed (Edd x) x := by
  have hs := ((hasDerivAt_id' x).const_mul 2).sin
  have hc := ((hasDerivAt_id' x).const_mul 2).cos
  unfold Ed
  convert (((((Real.hasDerivAt_cos x).const_mul ca).const_add 1).fun_sub
    ((Real.hasDerivAt_sin x).const_mul cb)).fun_add (hc.const_mul (2*cc))).fun_sub
      (hs.const_mul (2*cd)) using 1
  simp only [Edd]
  ring

theorem Edd_deriv (x : ℝ) : HasDerivAt Edd (Eddd x) x := by
  have hs := ((hasDerivAt_id' x).const_mul 2).sin
  have hc := ((hasDerivAt_id' x).const_mul 2).cos
  unfold Edd
  convert ((((Real.hasDerivAt_sin x).const_mul (-ca)).fun_sub
    ((Real.hasDerivAt_cos x).const_mul cb)).fun_sub (hs.const_mul (4*cc))).fun_sub
      (hc.const_mul (4*cd)) using 1
  simp only [Eddd]
  ring

theorem Eddd_positive {x : ℝ} (hx : x∈Icc (19/25:ℝ) (7/5)) : 0<Eddd x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(19/25:ℝ)) hxq.2 hx.1
  have hs0 := Real.sin_ge_sub_cube (show (0:ℝ)≤19/25 by norm_num)
  norm_num at hs0
  have hsL : (17/25:ℝ)<Real.sin x := by linarith
  have hs2 : 0≤Real.sin (2*x) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [hx.1]) (by linarith [hx.2,FrameLowPair.pi_lower])
  have hc2 := Real.neg_one_le_cos (2*x)
  dsimp [Eddd,ca,cb,cc,cd,r,lam,e,m,p,q]
  linarith

theorem Edd_monotone : MonotoneOn Edd (Icc (19/25:ℝ) (7/5)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (Edd_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => Edd_deriv x
  · exact fun x hx => (Eddd_positive (Ioo_subset_Icc_self hx)).le

theorem Edd_endpoint : Edd (7/5:ℝ)<21/100 := by
  have hs1 := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤7/5 by norm_num)
  have hc1 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤7/5 by norm_num)
  have hs2 := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤14/5 by norm_num)
  have hc2 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤14/5 by norm_num)
  norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs1 hc1 hs2 hc2
  norm_num [Edd,ca,cb,cc,cd,r,lam,e,m,p,q]
  linarith

theorem Edd_upper {x : ℝ} (hx : x∈Icc (19/25:ℝ) (7/5)) : Edd x≤21/100 := by
  exact (Edd_monotone hx ⟨by norm_num,le_rfl⟩ hx.2).trans Edd_endpoint.le

theorem E_endpoints :
    (2301/2500:ℝ)<E (19/25:ℝ) ∧ (1137/1250:ℝ)<E (7/5:ℝ) := by
  constructor
  · have hs1 := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤19/25 by norm_num)
    have hc1 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤19/25 by norm_num)
    have hs2 := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤38/25 by norm_num)
    have hc2 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤38/25 by norm_num)
    norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
      Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs1 hc1 hs2 hc2
    norm_num [E,E0,FrameLowMidTransverseNorm.K,ca,cb,cc,cd,r,lam,e,m,p,q,cM]
    linarith
  · have hs1 := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤7/5 by norm_num)
    have hc1 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤7/5 by norm_num)
    have hs2 := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤14/5 by norm_num)
    have hc2 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤14/5 by norm_num)
    norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
      Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs1 hc1 hs2 hc2
    norm_num [E,E0,FrameLowMidTransverseNorm.K,ca,cb,cc,cd,r,lam,e,m,p,q,cM]
    linarith

def Q (x : ℝ) : ℝ :=
  2301/2500-(3363/40000)*(x-19/25)+(21/200)*(x-19/25)^2
def Qd (x : ℝ) : ℝ := -(3363/40000)+(21/100)*(x-19/25)

theorem Q_deriv (x : ℝ) : HasDerivAt Q (Qd x) x := by
  unfold Q
  convert ((((hasDerivAt_id' x).sub_const (19/25)).const_mul (3363/40000)).const_sub
    (2301/2500)).fun_add
      ((((hasDerivAt_id' x).sub_const (19/25)).fun_pow 2).const_mul (21/200)) using 1
  simp only [Qd]
  ring
theorem Qd_deriv (x : ℝ) : HasDerivAt Qd (21/100:ℝ) x := by
  unfold Qd
  convert (((hasDerivAt_id' x).sub_const (19/25)).const_mul (21/100)).const_add
    (-(3363/40000:ℝ)) using 1
  ring

theorem E_lower {x : ℝ} (hx : x∈Icc (19/25:ℝ) (7/5)) : (1801/2000:ℝ)<E x := by
  have hc : ConcaveOn ℝ (Icc (19/25:ℝ) (7/5)) (fun z => E z-Q z) := by
    apply concave_of_deriv2 (fun z _ => (E_deriv z).sub (Q_deriv z))
      (fun z _ => (Ed_deriv z).sub (Qd_deriv z))
    intro z hz
    linarith [Edd_upper hz]
  have hleft : (0:ℝ)<E (19/25:ℝ)-Q (19/25:ℝ) := by
    norm_num [Q]
    linarith [E_endpoints.1]
  have hright : (0:ℝ)<E (7/5:ℝ)-Q (7/5:ℝ) := by
    norm_num [Q]
    linarith [E_endpoints.2]
  have hh := concave_gt_of_endpoints hc hx hleft hright
  have hmin : (1801/2000:ℝ)<Q x := by
    dsimp [Q]
    nlinarith [sq_nonneg ((x-19/25)-1121/2800)]
  linarith

theorem lower {x : ℝ} (hx : x∈Icc (19/25:ℝ) (7/5)) :
    (1801/2000:ℝ)<F lam (-(1/100000)) false x :=
  (E_lower hx).trans_le (norm_support hx)

theorem weak_separator {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (19/25:ℝ) (7/5))
    (hm : 0≤FrameLowMidGeometry.secondary true true b B x) :
    (1801/2000:ℝ)<FrameLowMidGeometry.lowMidCost true true b B x := by
  have hs : -(1/100000:ℝ)≤ sign true*(L b-lam*b) := by
    simpa [sign,lam] using low_positive_source hb
  have hdom : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  exact (lower hx).trans_le (circle_support true
    (show lam∈Icc (0:ℝ) 1 by constructor <;> norm_num [lam]) hb hB hs false hdom hm)

end SquaresInCircles.Eight.FrameLowMidTransversePositive
end
end
end

section
/-!
## The full negative low-to-middle transverse support

A single tangent majorant has no interior minimum in the first
quadrant.  The original radical support is increasing on the complete
second-quadrant continuation.  The final result keeps the original
negative source and its weak separating-axis equality.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowMidTransverseNegative
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus
open FrameLowMidTransverseNorm

def r : ℝ := 1978787508/1000000000
def lam : ℝ := 49/50
def aa : ℝ := r*lam*p/(14/5)-(lam-9/100)
def bb : ℝ := -(9/100)+r*lam*q/(14/5)
def kk : ℝ := K lam (-(1/25000))-r*(7/5+(5/28)*(p^2+q^2+lam^2))
def E (x : ℝ) : ℝ := x+kk+bb*Real.cos x-aa*Real.sin x
def reflected (z : ℝ) : ℝ := Real.pi/2-z+kk+bb*Real.sin z-aa*Real.cos z
def reflectedD (z : ℝ) : ℝ := -1+bb*Real.cos z+aa*Real.sin z
def reflectedDD (z : ℝ) : ℝ := -bb*Real.sin z+aa*Real.cos z

theorem coefficient_bounds : 0<aa ∧ (1:ℝ)<bb := by
  norm_num [aa,bb,r,lam,p,q]

theorem tangent_support {x : ℝ} (_hx : x∈Icc 1 (Real.pi/2)) :
    E x≤F lam (-(1/25000)) false x := by
  have hlam : lam∈Icc (0:ℝ) 1 := by constructor <;> norm_num [lam]
  have hn := N_positive hlam x
  have hmajor := tangent_majorant (n := N lam x) (show (0:ℝ)<14/5 by norm_num)
  have hR : R≤r := by simpa [r] using radius_precise.2.le
  have hr : 0≤r := by norm_num [r]
  have hh := mul_le_mul hR hmajor hn.le hr
  rw [N_square hlam x] at hh
  dsimp [energy] at hh
  dsimp [E,aa,bb,kk,F,cosCoefficient]
  ring_nf at hh ⊢
  linarith

theorem reflected_identity (x : ℝ) : reflected (Real.pi/2-x)=E x := by
  dsimp [reflected,E]
  rw [Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub]
  ring

theorem reflected_deriv (z : ℝ) : HasDerivAt reflected (reflectedD z) z := by
  unfold reflected
  convert ((((hasDerivAt_id' z).const_sub (Real.pi/2)).add_const kk).fun_add
    ((Real.hasDerivAt_sin z).const_mul bb)).fun_sub
      ((Real.hasDerivAt_cos z).const_mul aa) using 1
  simp only [reflectedD]
  ring

theorem reflectedD_deriv (z : ℝ) : HasDerivAt reflectedD (reflectedDD z) z := by
  unfold reflectedD
  convert (((Real.hasDerivAt_cos z).const_mul bb).const_add (-1)).fun_add
    ((Real.hasDerivAt_sin z).const_mul aa) using 1
  simp only [reflectedDD]
  ring

theorem reflectedDD_deriv (z : ℝ) :
    HasDerivAt reflectedDD (-bb*Real.cos z-aa*Real.sin z) z := by
  unfold reflectedDD
  convert ((Real.hasDerivAt_sin z).const_mul (-bb)).fun_add
    ((Real.hasDerivAt_cos z).const_mul aa) using 1
  ring

theorem reflectedD_concave :
    ConcaveOn ℝ (Icc 0 (Real.pi/2-1)) reflectedD := by
  apply concave_of_deriv2 (fun z _ => reflectedD_deriv z) (fun z _ => reflectedDD_deriv z)
  intro z hz
  have ht := FrameLowPair.quadrant (show z∈Icc 0 (Real.pi/2) from ⟨hz.1,by linarith [hz.2]⟩)
  have h1 := mul_nonneg (by linarith [coefficient_bounds.2] : 0≤bb) ht.2.2.1
  have h2 := mul_nonneg coefficient_bounds.1.le ht.1
  linarith

theorem E_endpoints : (9053/10000:ℝ)<E 1 ∧ (9109/10000:ℝ)<E (Real.pi/2) := by
  constructor
  · have hs := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤1 by norm_num)
    have hc := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤1 by norm_num)
    norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
      Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs hc
    norm_num [E,aa,bb,kk,FrameLowMidTransverseNorm.K,r,lam,p,q,cM]
    linarith
  · have hpi := Arithmetic.pi_hand_enclosure.1
    norm_num [E,aa,bb,kk,FrameLowMidTransverseNorm.K,r,lam,p,q,cM]
    linarith

theorem first_lower {x : ℝ} (hx : x∈Icc 1 (Real.pi/2)) :
    (1801/2000:ℝ)<F lam (-(1/25000)) false x := by
  have hz : Real.pi/2-x∈Icc 0 (Real.pi/2-1) := ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hd0 : 0≤reflectedD 0 := by simp [reflectedD]; linarith [coefficient_bounds.2]
  have hh := endpoint_minimum_of_concave_derivative hz
    (fun z _ => reflected_deriv z) reflectedD_concave hd0
  have h0 : reflected 0=E (Real.pi/2) := by simp [reflected,E]
  have h1 : reflected (Real.pi/2-1)=E 1 := reflected_identity 1
  rw [h0,h1,reflected_identity] at hh
  have hm : (1801/2000:ℝ)< min (E (Real.pi/2)) (E 1) := by
    apply lt_min <;> linarith [E_endpoints.1,E_endpoints.2]
  exact (hm.trans_le hh).trans_le (tangent_support hx)

theorem second_trig {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100)) :
    (99/100:ℝ)<Real.sin x ∧ -(7/50:ℝ)<Real.cos x ∧ Real.cos x≤0 := by
  have hsE := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤171/100 by norm_num)
  have hcE := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤171/100 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hsE hcE
  have hs := sin_endpoint_lower (by positivity : 0≤Real.pi/2)
    (by linarith [FrameLowPair.pi_lower] : (171/100:ℝ)≤Real.pi) hx
    (by norm_num : (99/100:ℝ)<Real.sin (Real.pi/2)) (by linarith)
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx.1,Real.pi_pos] : 0≤x)
    (by linarith [FrameLowPair.pi_lower] : (171/100:ℝ)≤Real.pi) hx.2
  have hsign := second_signs (show x∈Icc (Real.pi/2) Real.pi from
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩)
  exact ⟨hs,by linarith,hsign.2⟩

theorem second_norm_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100)) :
    (29/10:ℝ)<N lam x := by
  have hn := N_positive (show lam∈Icc (0:ℝ) 1 by constructor <;> norm_num [lam]) x
  have hs := N_square (show lam∈Icc (0:ℝ) 1 by constructor <;> norm_num [lam]) x
  have ht := second_trig hx
  dsimp [energy,lam,p,q] at hs hn ⊢
  nlinarith [ht.1,ht.2.2]

theorem second_norm_slope {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100)) :
    Nd lam x<27/50 := by
  have hn := second_norm_lower hx
  have ht := second_trig hx
  dsimp [Nd]
  apply (div_lt_iff₀ (by linarith : 0<N lam x)).2
  have hs := Real.sin_le_one x
  dsimp [lam,p,q] at hn ⊢
  linarith

theorem second_slope_positive {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100)) :
    0<Fd lam true x := by
  have ht := second_trig hx
  have hn := second_norm_slope hx
  have hprod := mul_lt_mul_of_pos_left hn R_pos
  have hR := mul_le_mul_of_nonneg_right
    (show R≤99/50 by linarith [radius_precise.2]) (show (0:ℝ)≤27/50 by norm_num)
  dsimp [Fd,cosCoefficient,lam] at hprod ⊢
  linarith

theorem second_monotone : MonotoneOn (F lam (-(1/25000)) true)
    (Icc (Real.pi/2) (171/100)) := by
  have hlam : lam∈Icc (0:ℝ) 1 := by constructor <;> norm_num [lam]
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (F_deriv hlam (-(1/25000)) true x).continuousAt.continuousWithinAt
  · exact fun x _ => F_deriv hlam (-(1/25000)) true x
  · exact fun x hx => (second_slope_positive (Ioo_subset_Icc_self hx)).le

theorem second_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100)) :
    (1801/2000:ℝ)<F lam (-(1/25000)) true x := by
  have hfirst := first_lower (show Real.pi/2∈Icc (1:ℝ) (Real.pi/2) from
    ⟨by linarith [FrameLowPair.pi_lower],le_rfl⟩)
  have he : F lam (-(1/25000)) false (Real.pi/2)=F lam (-(1/25000)) true (Real.pi/2) := by
    simp [F,cosCoefficient]
  rw [he] at hfirst
  exact hfirst.trans_le (second_monotone ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1)

theorem weak_separator {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (1:ℝ) (171/100))
    (hm : 0≤FrameLowMidGeometry.secondary false true b B x) :
    (1801/2000:ℝ)<FrameLowMidGeometry.lowMidCost false true b B x := by
  have hlam : lam∈Icc (0:ℝ) 1 := by constructor <;> norm_num [lam]
  have hs : -(1/25000:ℝ)≤ sign false*(L b-lam*b) := by
    simpa [sign,lam] using low_negative_source hb
  by_cases hq : x≤Real.pi/2
  · have hdom : x∈Icc 1 (Real.pi/2) := ⟨hx.1,hq⟩
    exact (first_lower hdom).trans_le (circle_support false hlam hb hB hs false
      (show x∈Icc 0 (Real.pi/2) from ⟨by linarith [hx.1],hq⟩) hm)
  · have hdom : x∈Icc (Real.pi/2) (171/100) := ⟨(lt_of_not_ge hq).le,hx.2⟩
    exact (second_lower hdom).trans_le (circle_support false hlam hb hB hs true
      (show x∈Icc (Real.pi/2) Real.pi from ⟨hdom.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩) hm)

end SquaresInCircles.Eight.FrameLowMidTransverseNegative
end
end
end

section
/-!
## The remaining middle-to-low transverse branch

The original negative source and positive target use the multiplier
`3/2`.  The source minimum is the actual lower middle endpoint.  The
target is supported on its containing circle.  The exact circular-norm
curvature proves concavity on both physical quadrants, including their
common endpoint.  No strictness is required of the separating margin.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowMidReverseTransverse
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus
open FrameLowMidGeometry

def lam : ℝ := 3/2
def K : ℝ := 21/25-30461/100000+
  (3/2)*(1298747247/4000000000)+
  FrameLowArc.u*(141457567/100000000)+(FrameLowArc.u+FrameLowArc.v)/2
def N (x : ℝ) : ℝ :=
  CircularNorm.norm (FrameLowArc.u^2+FrameLowArc.v^2+lam^2)
    (-2*lam*FrameLowArc.v) (2*lam*FrameLowArc.u) x
def Nd (x : ℝ) : ℝ :=
  CircularNorm.d1 (FrameLowArc.u^2+FrameLowArc.v^2+lam^2)
    (-2*lam*FrameLowArc.v) (2*lam*FrameLowArc.u) x
def Ndd (x : ℝ) : ℝ :=
  CircularNorm.d2 (FrameLowArc.u^2+FrameLowArc.v^2+lam^2)
    (-2*lam*FrameLowArc.v) (2*lam*FrameLowArc.u) x
def cosCoefficient (second : Bool) : ℝ := if second then 141/100 else 9/100
def F (second : Bool) (x : ℝ) : ℝ :=
  x+K+(141/100)*Real.sin x-cosCoefficient second*Real.cos x-R*N x
def Fd (second : Bool) (x : ℝ) : ℝ :=
  1+(141/100)*Real.cos x+cosCoefficient second*Real.sin x-R*Nd x
def Fdd (second : Bool) (x : ℝ) : ℝ :=
  -(141/100)*Real.sin x+cosCoefficient second*Real.cos x-R*Ndd x
def left (second : Bool) : ℝ := if second then Real.pi/2 else 1
def right (second : Bool) : ℝ := if second then 171/100 else Real.pi/2

theorem energy_positive (x : ℝ) :
    0<CircularNorm.energy (FrameLowArc.u^2+FrameLowArc.v^2+lam^2)
      (-2*lam*FrameLowArc.v) (2*lam*FrameLowArc.u) x := by
  have hh := FrameCoreArc.projection_lt
    (a := -FrameLowArc.u) (b := FrameLowArc.v) (x := x)
    (show (0:ℝ)<117/100 by norm_num)
    (by norm_num [FrameLowArc.u,FrameLowArc.v])
  dsimp [CircularNorm.energy,lam,FrameLowArc.u,FrameLowArc.v] at hh ⊢
  linarith

theorem N_positive (x : ℝ) : 0<N x := CircularNorm.norm_pos (energy_positive x)
theorem N_square (x : ℝ) :
    (N x)^2=FrameLowArc.u^2+FrameLowArc.v^2+lam^2+
      2*lam*(FrameLowArc.u*Real.sin x-FrameLowArc.v*Real.cos x) := by
  have hh := CircularNorm.norm_sq (energy_positive x).le
  convert hh using 1 <;> dsimp [N,CircularNorm.energy]
  ring
theorem N_deriv (x : ℝ) : HasDerivAt N (Nd x) x :=
  CircularNorm.norm_hasDerivAt (energy_positive x)
theorem Nd_deriv (x : ℝ) : HasDerivAt Nd (Ndd x) x :=
  CircularNorm.d1_hasDerivAt (energy_positive x)

theorem Ndd_lower (x : ℝ) : -N x/4≤Ndd x := by
  exact CircularNorm.curvature_lower (energy_positive x)
    (by norm_num [lam,FrameLowArc.u,FrameLowArc.v])

theorem first_trig {x : ℝ} (hx : x∈Icc (1:ℝ) (Real.pi/2)) :
    (21/25:ℝ)<Real.sin x ∧ 0≤Real.cos x ∧ Real.cos x<11/20 := by
  have hs0 := sin_lower_seven (show (0:ℝ)≤1 by norm_num)
  have hc0 := cos_upper_four (show (0:ℝ)≤1 by norm_num)
  norm_num at hs0 hc0
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(1:ℝ)) hx.2 hx.1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤1) (by linarith [hx.2,Real.pi_pos]) hx.1
  have hq := FrameLowPair.quadrant
    (show x∈Icc 0 (Real.pi/2) from ⟨by linarith [hx.1],hx.2⟩)
  exact ⟨by linarith,hq.2.2.1,by linarith⟩

theorem second_trig {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100:ℝ)) :
    (99/100:ℝ)<Real.sin x ∧ -(7/50:ℝ)<Real.cos x ∧ Real.cos x≤0 := by
  have hsE := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤171/100 by norm_num)
  have hcE := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤171/100 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hsE hcE
  have hs := sin_endpoint_lower (by positivity : (0:ℝ)≤Real.pi/2)
    (by linarith [FrameLowPair.pi_lower] : (171/100:ℝ)≤Real.pi) hx
    (by norm_num : (99/100:ℝ)<Real.sin (Real.pi/2))
    (by linarith : (99/100:ℝ)<Real.sin (171/100:ℝ))
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx.1,Real.pi_pos] : 0≤x)
    (by linarith [FrameLowPair.pi_lower] : (171/100:ℝ)≤Real.pi) hx.2
  have hq := second_signs
    (show x∈Icc (Real.pi/2) Real.pi from
      ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩)
  exact ⟨hs,by linarith,hq.2⟩

theorem first_norm_upper {x : ℝ} (hx : x∈Icc (1:ℝ) (Real.pi/2)) :
    N x<1097/500 := by
  have ht := first_trig hx
  have he := N_square x
  have hn := N_positive x
  have hs := Real.sin_le_one x
  dsimp [lam,FrameLowArc.u,FrameLowArc.v] at he
  nlinarith

theorem second_norm_upper {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100:ℝ)) :
    N x<23/10 := by
  have ht := second_trig hx
  have he := N_square x
  have hn := N_positive x
  have hs := Real.sin_le_one x
  dsimp [lam,FrameLowArc.u,FrameLowArc.v] at he
  nlinarith

theorem initial_norm : N 1<17/10 := by
  have hs := sin_upper_five (show (0:ℝ)≤1 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤1 by norm_num)
  have he := N_square 1
  have hn := N_positive 1
  norm_num [lam,FrameLowArc.u,FrameLowArc.v] at hs hc he
  nlinarith

theorem F_deriv (second : Bool) (x : ℝ) : HasDerivAt (F second) (Fd second x) x := by
  refine ((((hasDerivAt_id x).add_const K).add
    ((Real.hasDerivAt_sin x).const_mul (141/100))).sub
      ((Real.hasDerivAt_cos x).const_mul (cosCoefficient second))).sub
        ((N_deriv x).const_mul R) |>.congr_deriv ?_
  rw [Fd]
  ring

theorem Fd_deriv (second : Bool) (x : ℝ) :
    HasDerivAt (Fd second) (Fdd second x) x := by
  refine ((((Real.hasDerivAt_cos x).const_mul (141/100)).const_add 1).add
    ((Real.hasDerivAt_sin x).const_mul (cosCoefficient second))).sub
      ((Nd_deriv x).const_mul R) |>.congr_deriv ?_
  rw [Fdd]
  ring

theorem Fdd_negative (second : Bool) {x : ℝ}
    (hx : x∈Icc (left second) (right second)) : Fdd second x<0 := by
  have hR : R<(99/50:ℝ) := by linarith [radius_precise.2]
  have hcurv := mul_le_mul_of_nonneg_left (Ndd_lower x) R_pos.le
  cases second with
  | false =>
      have hxq : x∈Icc (1:ℝ) (Real.pi/2) := by simpa [left,right] using hx
      have ht := first_trig hxq
      have hn := mul_le_mul hR.le (first_norm_upper hxq).le
        (N_positive x).le (by norm_num : (0:ℝ)≤99/50)
      dsimp [Fdd,cosCoefficient]
      nlinarith
  | true =>
      have hxq : x∈Icc (Real.pi/2) (171/100:ℝ) := by simpa [left,right] using hx
      have ht := second_trig hxq
      have hn := mul_le_mul hR.le (second_norm_upper hxq).le
        (N_positive x).le (by norm_num : (0:ℝ)≤99/50)
      dsimp [Fdd,cosCoefficient]
      nlinarith

theorem F_concave (second : Bool) :
    ConcaveOn ℝ (Icc (left second) (right second)) (F second) :=
  concave_of_deriv2 (fun x _ => F_deriv second x)
    (fun x _ => Fd_deriv second x) (fun _ hx => (Fdd_negative second hx).le)

theorem endpoint_lower (second : Bool) :
    (1801/2000:ℝ)<F second (left second) ∧
      (1801/2000:ℝ)<F second (right second) := by
  have hpi := Arithmetic.pi_hand_enclosure
  have hR : R<(99/50:ℝ) := by linarith [radius_precise.2]
  have hn0 := mul_le_mul hR.le initial_norm.le (N_positive 1).le
    (by norm_num : (0:ℝ)≤99/50)
  have hnm := mul_le_mul hR.le
    (first_norm_upper (show Real.pi/2∈Icc (1:ℝ) (Real.pi/2) from
      ⟨by linarith [hpi.1],le_rfl⟩)).le
    (N_positive (Real.pi/2)).le (by norm_num : (0:ℝ)≤99/50)
  have hn1 := mul_le_mul hR.le
    (second_norm_upper (show (171/100:ℝ)∈Icc (Real.pi/2) (171/100:ℝ) from
      ⟨by linarith [hpi.2],le_rfl⟩)).le
    (N_positive (171/100)).le (by norm_num : (0:ℝ)≤99/50)
  have ht0 := first_trig
    (show (1:ℝ)∈Icc (1:ℝ) (Real.pi/2) from ⟨le_rfl,by linarith [hpi.1]⟩)
  have ht1 := second_trig
    (show (171/100:ℝ)∈Icc (Real.pi/2) (171/100:ℝ) from
      ⟨by linarith [hpi.2],le_rfl⟩)
  have hc1 := FrameLowMidPrimaryScalars.final_cos
  cases second <;> norm_num [F,left,right,K,cosCoefficient,FrameLowArc.u,FrameLowArc.v]
  all_goals constructor <;> linarith

theorem lower (second : Bool) {x : ℝ}
    (hx : x∈Icc (left second) (right second)) : (1801/2000:ℝ)<F second x :=
  concave_gt_of_endpoints (F_concave second) hx
    (endpoint_lower second).1 (endpoint_lower second).2

theorem circle_support {b B x : ℝ} (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1)
    (second : Bool)
    (hx : if second then x∈Icc (Real.pi/2) Real.pi else x∈Icc 0 (Real.pi/2))
    (hm : 0≤ secondary false true b B x) : F second x≤ midLowCost false true b B x := by
  have hs := middle_negative_source hb (show (1:ℝ) ≤ lam by norm_num [lam])
  have hK : K≤9/100+(-M1+lam*b1)+FrameLowArc.u*a0+
      (FrameLowArc.u+FrameLowArc.v+lam)/2 := by
    dsimp [K,lam,FrameLowArc.u,FrameLowArc.v]
    linarith [M_endpoints.2.1,FrameLowMidArc.b1_precise.1,a0_precise.1]
  have hscaled := mul_nonneg (show (0:ℝ) ≤ lam by norm_num [lam]) hm
  have ht := circle_linear_lower (A_circle ⟨hB.1,hB.2.trans b1_mem.2⟩)
    (-FrameLowArc.u-lam*Real.sin x) (lam*Real.cos x-FrameLowArc.v)
  have hn : Real.sqrt ((-FrameLowArc.u-lam*Real.sin x)^2+
      (lam*Real.cos x-FrameLowArc.v)^2)=N x := by
    dsimp [N,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination lam^2*(Real.sin_sq_add_cos_sq x)
  rw [hn] at ht
  cases second with
  | false =>
      rw [ite_eq_right Bool.false_ne_true] at hx
      dsimp [secondary] at hscaled
      rw [(first_width hx).1] at hscaled
      dsimp [F,cosCoefficient,midLowCost,L]
      rw [(first_width hx).2]
      norm_num [sign] at hscaled ⊢
      dsimp [lam] at hs ht hK hscaled
      nlinarith
  | true =>
      rw [ite_eq_left rfl] at hx
      dsimp [secondary] at hscaled
      rw [(second_width hx).1] at hscaled
      dsimp [F,cosCoefficient,midLowCost,L]
      rw [(second_width hx).2]
      norm_num [sign] at hscaled ⊢
      dsimp [lam] at hs ht hK hscaled
      nlinarith

theorem weak_separator {b B x : ℝ} (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (1:ℝ) (171/100)) (hm : 0≤ secondary false true b B x) :
    (1801/2000:ℝ)< midLowCost false true b B x := by
  by_cases hhalf : x≤Real.pi/2
  · exact (lower false (by simpa [left,right] using (show x∈Icc (1:ℝ) (Real.pi/2) from
      ⟨hx.1,hhalf⟩))).trans_le (circle_support hb hB false
        ⟨by linarith [hx.1],hhalf⟩ hm)
  · have hhalf' : Real.pi/2≤x := (lt_of_not_ge hhalf).le
    exact (lower true (by simpa [left,right] using
      (show x∈Icc (Real.pi/2) (171/100:ℝ) from ⟨hhalf',hx.2⟩))).trans_le
      (circle_support hb hB true
        ⟨hhalf',by linarith [hx.2,FrameLowPair.pi_lower]⟩ hm)

end SquaresInCircles.Eight.FrameLowMidReverseTransverse
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowMidPair
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidGeometry

theorem source_secondary_low_mid (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch=.middle) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (1801/2000:ℝ)<s.cost t x := by
  have hb := (state_low_chart s hs).2
  have hB := (state_mid_chart t ht).2
  have hmargin := (FrameLowMidGeometry.state_secondary s t
    (by simp [ht,Branch.type]) x).mp hm
  have hx := low_mid_angle s t hs ht hgap
  rw [state_low_mid_cost s t hs ht]
  generalize s.positive = i at hmargin hx ⊢
  generalize t.positive = k at hmargin hx ⊢
  cases i <;> cases k <;> norm_num [lowMidFloor] at hx
  · by_cases htail : (19/20:ℝ)≤x
    · exact low_mid_tail false false hb hB (by simpa [lowMidTail] using htail)
    · exact FrameLowMidSecondaryEndpoints.low_mid_negative_target false hb hB
        ⟨by simpa [FrameLowMidEndpointScalars.start] using hx,
          by linarith [FrameLowPair.pi_lower]⟩ hmargin
  · by_cases htail : (171/100:ℝ)≤x
    · exact low_mid_tail false true hb hB (by simpa [lowMidTail] using htail)
    · exact FrameLowMidTransverseNegative.weak_separator hb hB
        ⟨hx,(lt_of_not_ge htail).le⟩ hmargin
  · by_cases htail : (16/25:ℝ)≤x
    · exact low_mid_tail true false hb hB (by simpa [lowMidTail] using htail)
    · exact FrameLowMidSecondaryEndpoints.low_mid_negative_target true hb hB
        ⟨by simpa [FrameLowMidEndpointScalars.start] using hx,
          by linarith [FrameLowPair.pi_lower]⟩ hmargin
  · by_cases htail : (7/5:ℝ)≤x
    · exact low_mid_tail true true hb hB (by simpa [lowMidTail] using htail)
    · exact FrameLowMidTransversePositive.weak_separator hb hB
        ⟨hx,(lt_of_not_ge htail).le⟩ hmargin

theorem source_secondary_mid_low (s t : FramePair.State)
    (hs : s.branch=.middle) (ht : t.branch=.low) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (1801/2000:ℝ)<s.cost t x := by
  have hb := (state_mid_chart s hs).2
  have hB := (state_low_chart t ht).2
  have hmargin := (FrameLowMidGeometry.state_secondary s t
    (by simp [ht,Branch.type]) x).mp hm
  have hx := mid_low_angle s t hs ht hgap
  rw [state_mid_low_cost s t hs ht]
  generalize s.positive = i at hmargin hx ⊢
  generalize t.positive = k at hmargin hx ⊢
  cases i <;> cases k <;> norm_num [midLowFloor] at hx
  · by_cases htail : (7/5:ℝ)≤x
    · exact mid_low_tail false false hb hB (by simpa [midLowTail] using htail)
    · exact FrameLowMidSecondaryContinuation.negative_weak_separator hb hB
        ⟨hx,(lt_of_not_ge htail).le⟩ hmargin
  · by_cases htail : (171/100:ℝ)≤x
    · exact mid_low_tail false true hb hB (by simpa [midLowTail] using htail)
    · exact FrameLowMidReverseTransverse.weak_separator hb hB
        ⟨hx,(lt_of_not_ge htail).le⟩ hmargin
  · by_cases htail : (16/25:ℝ)≤x
    · exact mid_low_tail true false hb hB (by simpa [midLowTail] using htail)
    · exact FrameLowMidSecondaryEndpoints.mid_low_positive_negative hb hB
        ⟨hx,(lt_of_not_ge htail).le⟩ hmargin
  · by_cases htail : (19/20:ℝ)≤x
    · exact mid_low_tail true true hb hB (by simpa [midLowTail] using htail)
    · have hcut := FrameLowMidCuts.mid_low_secondary_cut hb hB
        (by linarith : 0≤x) hmargin
      by_cases hcontact : x≤79/100
      · exact FrameLowMidContact.weak_separator hb hB ⟨hcut.le,hcontact⟩ hmargin
      · exact FrameLowMidSecondaryContinuation.positive_weak_separator hb hB
          ⟨(lt_of_not_ge hcontact).le,(lt_of_not_ge htail).le⟩ hmargin

theorem source_primary_low_mid (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch=.middle) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (1801/2000:ℝ)<s.cost t x := by
  have hb := (state_low_chart s hs).2
  have hB := (state_mid_chart t ht).2
  have hmargin := (FrameLowMidGeometry.state_primary s t
    (by simp [hs,Branch.type]) (by simp [ht,Branch.type]) x).mp hm
  have hx := low_mid_angle s t hs ht hgap
  have hlo : 0≤lowMidFloor s.positive t.positive := by
    cases s.positive <;> cases t.positive <;> norm_num [lowMidFloor]
  rw [state_low_mid_cost s t hs ht]
  exact FrameLowMidPrimary.low_mid_primary s.positive t.positive hb hB
    (hlo.trans hx) hmargin

theorem source_primary_mid_low (s t : FramePair.State)
    (hs : s.branch=.middle) (ht : t.branch=.low) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (1801/2000:ℝ)<s.cost t x := by
  have hb := (state_mid_chart s hs).2
  have hB := (state_low_chart t ht).2
  have hmargin := (FrameLowMidGeometry.state_primary s t
    (by simp [hs,Branch.type]) (by simp [ht,Branch.type]) x).mp hm
  have hx := mid_low_angle s t hs ht hgap
  have hlo : 0≤ midLowFloor s.positive t.positive := by
    cases s.positive <;> cases t.positive <;> norm_num [midLowFloor]
  rw [state_mid_low_cost s t hs ht]
  exact FrameLowMidPrimary.mid_low_primary s.positive t.positive hb hB
    (hlo.trans hx) hmargin

/-- The pair inequality for a low source and a middle target, on every forward axis. -/
theorem low_mid_pair (s t : FramePair.State) (hs : s.branch=.low)
    (ht : t.branch=.middle) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(1801/2000:ℝ) := by
    norm_num [hs,ht,Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_secondary_low_mid s t hs ht hgap hm
  · have hh := source_primary_mid_low t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_secondary_mid_low t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_primary_low_mid s t hs ht hgap hm

/-- The pair inequality for a middle source and a low target, on every forward axis. -/
theorem mid_low_pair (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.low) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(1801/2000:ℝ) := by
    norm_num [hs,ht,Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_secondary_mid_low s t hs ht hgap hm
  · have hh := source_primary_low_mid t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_secondary_low_mid t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_primary_mid_low s t hs ht hgap hm

theorem low_mid_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.low) (hj : branchOf C (next i)=.middle)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact low_mid_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

theorem mid_low_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.middle) (hj : branchOf C (next i)=.low)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact mid_low_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

end SquaresInCircles.Eight.FrameLowMidPair
end
end
end
