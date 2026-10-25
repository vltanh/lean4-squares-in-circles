module

public import SquaresInCircles.Eight.Frames.Low.HighCuts

/-!
# Eight squares: the entire negative-low / positive-high transverse branch

The actual weak owner first forces the angle past `1.35`.  The exact
circle norm is nonzero and increasing on the remaining interval.  Its
curvature makes both physical-quadrant supports concave.  The common
quarter-turn endpoint retains the precise radius bound needed for its
strict reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighSecondaryOpposite
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameLowHighGeometry

def lam : ℝ := 51/50
def N (x : ℝ) : ℝ :=
  CircularNorm.norm (FrameHighArc.u^2+FrameHighArc.v^2+lam^2)
    (-2*lam*FrameHighArc.v) (-2*lam*FrameHighArc.u) x
def Nd (x : ℝ) : ℝ :=
  CircularNorm.d1 (FrameHighArc.u^2+FrameHighArc.v^2+lam^2)
    (-2*lam*FrameHighArc.v) (-2*lam*FrameHighArc.u) x
def Ndd (x : ℝ) : ℝ :=
  CircularNorm.d2 (FrameHighArc.u^2+FrameHighArc.v^2+lam^2)
    (-2*lam*FrameHighArc.v) (-2*lam*FrameHighArc.u) x
def K : ℝ := 3/5-FrameHighArc.k-(FrameHighArc.u-FrameHighArc.v)/2
def cosCoefficient (second : Bool) : ℝ := if second then 93/100 else 9/100
def F (second : Bool) (x : ℝ) : ℝ :=
  x+K+(93/100)*Real.sin x-cosCoefficient second*Real.cos x-R*N x
def Fd (second : Bool) (x : ℝ) : ℝ :=
  1+(93/100)*Real.cos x+cosCoefficient second*Real.sin x-R*Nd x
def Fdd (second : Bool) (x : ℝ) : ℝ :=
  -(93/100)*Real.sin x+cosCoefficient second*Real.cos x-R*Ndd x
def left (second : Bool) : ℝ := if second then Real.pi/2 else 27/20
def right (second : Bool) : ℝ := if second then 101/50 else Real.pi/2

theorem energy_positive (x : ℝ) :
    0<CircularNorm.energy (FrameHighArc.u^2+FrameHighArc.v^2+lam^2)
      (-2*lam*FrameHighArc.v) (-2*lam*FrameHighArc.u) x := by
  have hh := FrameCoreArc.projection_lt
    (a := FrameHighArc.u) (b := FrameHighArc.v)
    (by norm_num : (0:ℝ)<7/10)
    (by norm_num [FrameHighArc.u,FrameHighArc.v]) x
  dsimp [CircularNorm.energy,lam,FrameHighArc.u,FrameHighArc.v] at *
  linarith

theorem N_positive (x : ℝ) : 0<N x := CircularNorm.norm_pos (energy_positive x)
theorem N_square (x : ℝ) :
    (N x)^2=FrameHighArc.u^2+FrameHighArc.v^2+lam^2-
      2*lam*(FrameHighArc.u*Real.sin x+FrameHighArc.v*Real.cos x) := by
  have hh := CircularNorm.norm_sq (energy_positive x).le
  convert hh using 1 <;> dsimp [N,CircularNorm.energy] <;> ring
theorem N_deriv (x : ℝ) : HasDerivAt N (Nd x) x :=
  CircularNorm.norm_hasDerivAt (energy_positive x)
theorem Nd_deriv (x : ℝ) : HasDerivAt Nd (Ndd x) x :=
  CircularNorm.d1_hasDerivAt (energy_positive x)

theorem trig_window {x : ℝ} (hx : x∈Icc (27/20:ℝ) (101/50)) :
    (9/10:ℝ)<Real.sin x ∧ Real.cos x<11/50 := by
  have hs0 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤27/20 by norm_num)
  have hs1 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤101/50 by norm_num)
  have hc0 := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤27/20 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs0 hs1 hc0
  have hs := sin_endpoint_lower (by norm_num : (0:ℝ)≤27/20)
    (by linarith [FrameLowPair.pi_lower] : (101/50:ℝ)≤Real.pi) hx
    (by linarith : (9/10:ℝ)<Real.sin (27/20:ℝ))
    (by linarith : (9/10:ℝ)<Real.sin (101/50:ℝ))
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤27/20) (by linarith [hx.2,FrameLowPair.pi_lower]) hx.1
  exact ⟨hs,by linarith⟩

theorem N_monotone : MonotoneOn N (Icc (27/20:ℝ) (101/50)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (N_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => N_deriv x
  · intro x hx
    have ht := trig_window (Ioo_subset_Icc_self hx)
    have hp := N_positive x
    dsimp [Nd,CircularNorm.d1,CircularNorm.slope]
    apply div_nonneg _ (by positivity)
    dsimp [lam,FrameHighArc.u,FrameHighArc.v]
    linarith

theorem endpoint_norms : N (27/20:ℝ)<229/500 ∧
    N (Real.pi/2)<597/1000 ∧ N (101/50:ℝ)<181/200 := by
  have h0 := N_square (27/20)
  have hm := N_square (Real.pi/2)
  have h1 := N_square (101/50)
  have hp0 := N_positive (27/20)
  have hpm := N_positive (Real.pi/2)
  have hp1 := N_positive (101/50)
  have hs0 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤27/20 by norm_num)
  have hc0 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤27/20 by norm_num)
  have hs1 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤101/50 by norm_num)
  have hc1 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤101/50 by norm_num)
  norm_num [lam,FrameHighArc.u,FrameHighArc.v,
    HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at h0 hm h1 hs0 hc0 hs1 hc1
  refine ⟨lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_,lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_,
    lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_⟩
  · rw [h0]; norm_num; linarith
  · rw [hm]; norm_num
  · rw [h1]; norm_num; linarith

theorem N_upper {x : ℝ} (hx : x∈Icc (27/20:ℝ) (101/50)) : N x<181/200 :=
  (N_monotone hx ⟨by norm_num,le_rfl⟩ hx.2).trans_lt endpoint_norms.2.2

theorem Ndd_lower (x : ℝ) : -N x/4≤Ndd x :=
  CircularNorm.curvature_lower (energy_positive x)
    (by norm_num [lam,FrameHighArc.u,FrameHighArc.v])

theorem F_deriv (second : Bool) (x : ℝ) : HasDerivAt (F second) (Fd second x) x := by
  have h := ((((hasDerivAt_id' x).add_const K).fun_add
    ((Real.hasDerivAt_sin x).const_mul (93/100))).fun_sub
      ((Real.hasDerivAt_cos x).const_mul (cosCoefficient second))).fun_sub ((N_deriv x).const_mul R)
  refine h.congr_deriv ?_
  simp only [Fd]
  ring
theorem Fd_deriv (second : Bool) (x : ℝ) : HasDerivAt (Fd second) (Fdd second x) x := by
  have h := ((((Real.hasDerivAt_cos x).const_mul (93/100)).const_add 1).fun_add
    ((Real.hasDerivAt_sin x).const_mul (cosCoefficient second))).fun_sub ((Nd_deriv x).const_mul R)
  refine h.congr_deriv ?_
  simp only [Fdd]
  ring

theorem quadrant_domain (second : Bool) {x : ℝ}
    (hx : x∈Icc (left second) (right second)) : x∈Icc (27/20:ℝ) (101/50) := by
  have hp := Arithmetic.pi_hand_enclosure
  cases second <;> dsimp [left,right] at hx <;> constructor <;> linarith [hx.1,hx.2]

theorem Fdd_negative (second : Bool) {x : ℝ}
    (hx : x∈Icc (left second) (right second)) : Fdd second x<0 := by
  have hdom := quadrant_domain second hx
  have ht := trig_window hdom
  have hcurv := mul_le_mul_of_nonneg_left (Ndd_lower x) R_pos.le
  have hR : R<(99/50:ℝ) := by linarith [radius_precise.2]
  have hn := mul_le_mul hR.le (N_upper hdom).le (N_positive x).le
    (by norm_num : (0:ℝ)≤99/50)
  cases second <;> dsimp [Fdd,cosCoefficient] <;> nlinarith

theorem F_concave (second : Bool) :
    ConcaveOn ℝ (Icc (left second) (right second)) (F second) :=
  concave_of_deriv2 (fun x _ => F_deriv second x) (fun x _ => Fd_deriv second x)
    (fun _ hx => (Fdd_negative second hx).le)

theorem endpoint_lower (second : Bool) :
    (8833/10000:ℝ)<F second (left second) ∧
      (8833/10000:ℝ)<F second (right second) := by
  have hR := radius_precise.2
  have hn0 := mul_le_mul hR.le endpoint_norms.1.le (N_positive (27/20)).le
    (by norm_num)
  have hnm := mul_le_mul hR.le endpoint_norms.2.1.le (N_positive (Real.pi/2)).le
    (by norm_num)
  have hn1 := mul_le_mul hR.le endpoint_norms.2.2.le (N_positive (101/50)).le
    (by norm_num)
  have hs0 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤27/20 by norm_num)
  have hc0 := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤27/20 by norm_num)
  have hs1 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤101/50 by norm_num)
  have hc1 := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤101/50 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs0 hc0 hs1 hc1
  have hk := k_bounds.2.1
  have hp := Arithmetic.pi_hand_enclosure.1
  cases second <;> norm_num [F,K,left,right,cosCoefficient,FrameHighArc.u,FrameHighArc.v]
  all_goals constructor <;> linarith

theorem lower (second : Bool) {x : ℝ} (hx : x∈Icc (left second) (right second)) :
    (8833/10000:ℝ)<F second x :=
  concave_gt_of_endpoints (F_concave second) hx
    (endpoint_lower second).1 (endpoint_lower second).2

theorem circle_support {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (second : Bool)
    (hx : if second then x∈Icc (Real.pi/2) Real.pi else x∈Icc 0 (Real.pi/2))
    (hm : 0≤ secondary false true b B x) : F second x≤lowHighCost false true b B x := by
  have hs : 0≤-L b+lam*b := by dsimp [lam]; linarith [low_unit_source hb,hb.1]
  have hscaled := mul_nonneg (show (0:ℝ)≤lam by norm_num [lam]) hm
  have ht := circle_linear_lower (A_circle ⟨b2_mem.1.trans hB.1,hB.2⟩)
    (FrameHighArc.u-lam*Real.sin x) (lam*Real.cos x-FrameHighArc.v)
  have hn : Real.sqrt ((FrameHighArc.u-lam*Real.sin x)^2+
      (lam*Real.cos x-FrameHighArc.v)^2)=N x := by
    dsimp [N,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination lam^2*(Real.sin_sq_add_cos_sq x)
  rw [hn] at ht
  cases second with
  | false =>
      simp only [Bool.false_eq_true,↓reduceIte] at hx
      dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hscaled
      rw [(first_width hx).1] at hscaled
      dsimp [F,K,cosCoefficient,lowHighCost,H,sign]
      rw [(first_width hx).2]
      dsimp [lam] at hs ht hscaled
      nlinarith
  | true =>
      simp only [↓reduceIte] at hx
      dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hscaled
      rw [(second_width hx).1] at hscaled
      dsimp [F,K,cosCoefficient,lowHighCost,H,sign]
      rw [(second_width hx).2]
      dsimp [lam] at hs ht hscaled
      nlinarith

theorem weak_separator {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : -(34/125:ℝ)≤x) (hm : 0≤ secondary false true b B x) :
    (8833/10000:ℝ)<lowHighCost false true b B x := by
  have hcut : (27/20:ℝ)<x := by
    simpa [FrameLowHighCuts.positiveCut] using
      FrameLowHighCuts.positive_secondary_cut false hb hB hx hm
  by_cases htail : (101/50:ℝ)≤x
  · exact low_high_tail false true hb hB (by simpa [lowHighTail] using htail)
  · by_cases hhalf : x≤Real.pi/2
    · exact (lower false (by simpa [left,right] using
        (show x∈Icc (27/20:ℝ) (Real.pi/2) from ⟨hcut.le,hhalf⟩))).trans_le
        (circle_support hb hB false ⟨by linarith,hhalf⟩ hm)
    · exact (lower true (by simpa [left,right] using
        (show x∈Icc (Real.pi/2) (101/50:ℝ) from
          ⟨(lt_of_not_ge hhalf).le,(lt_of_not_ge htail).le⟩))).trans_le
        (circle_support hb hB true
          ⟨(lt_of_not_ge hhalf).le,by linarith [FrameLowPair.pi_lower]⟩ hm)

end SquaresInCircles.Eight.FrameLowHighSecondaryOpposite
