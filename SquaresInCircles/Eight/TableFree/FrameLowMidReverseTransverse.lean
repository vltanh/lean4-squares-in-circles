module

public import SquaresInCircles.Eight.TableFree.FrameLowMidPrimaryScalars

/-!
# The remaining middle-to-low transverse branch

The original negative source and positive target use the multiplier
`3/2`.  The source minimum is the actual lower middle endpoint.  The
target is supported on its containing circle.  The exact circular-norm
curvature proves concavity on both physical quadrants, including their
common endpoint.  No strictness is required of the separating margin.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowMidReverseTransverse
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
  convert hh using 1 <;> dsimp [N,CircularNorm.energy] <;> ring
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
  convert ((((hasDerivAt_id x).add_const K).add
    ((Real.hasDerivAt_sin x).const_mul (141/100))).sub
      ((Real.hasDerivAt_cos x).const_mul (cosCoefficient second))).sub
        ((N_deriv x).const_mul R) using 1 <;> dsimp [F,Fd] <;> ring

theorem Fd_deriv (second : Bool) (x : ℝ) :
    HasDerivAt (Fd second) (Fdd second x) x := by
  convert ((((Real.hasDerivAt_cos x).const_mul (141/100)).const_add 1).add
    ((Real.hasDerivAt_sin x).const_mul (cosCoefficient second))).sub
      ((Nd_deriv x).const_mul R) using 1 <;> dsimp [Fd,Fdd] <;> ring

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
    (fun x _ => Fd_deriv second x) (fun x hx => (Fdd_negative second hx).le)

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
    (hm : 0≤secondary false true b B x) : F second x≤midLowCost false true b B x := by
  have hs := middle_negative_source hb (show (1:ℝ)≤lam by norm_num [lam])
  have hK : K≤9/100+(-M1+lam*b1)+FrameLowArc.u*a0+
      (FrameLowArc.u+FrameLowArc.v+lam)/2 := by
    dsimp [K,lam,FrameLowArc.u,FrameLowArc.v]
    linarith [M_endpoints.2.1,FrameLowMidArc.b1_precise.1,a0_precise.1]
  have hscaled := mul_nonneg (show (0:ℝ)≤lam by norm_num [lam]) hm
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
      dsimp only [Bool.false_eq_true,ite_false] at hx
      dsimp [secondary] at hscaled
      rw [(first_width hx).1] at hscaled
      dsimp [F,cosCoefficient,midLowCost,L]
      rw [(first_width hx).2]
      norm_num [sign] at hscaled ⊢
      dsimp [lam] at hs ht hK hscaled
      nlinarith
  | true =>
      dsimp only [ite_true] at hx
      dsimp [secondary] at hscaled
      rw [(second_width hx).1] at hscaled
      dsimp [F,cosCoefficient,midLowCost,L]
      rw [(second_width hx).2]
      norm_num [sign] at hscaled ⊢
      dsimp [lam] at hs ht hK hscaled
      nlinarith

theorem weak_separator {b B x : ℝ} (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (1:ℝ) (171/100)) (hm : 0≤secondary false true b B x) :
    (1801/2000:ℝ)<midLowCost false true b B x := by
  by_cases hhalf : x≤Real.pi/2
  · exact (lower false (by simpa [left,right] using (show x∈Icc (1:ℝ) (Real.pi/2) from
      ⟨hx.1,hhalf⟩))).trans_le (circle_support hb hB false
        ⟨by linarith [hx.1],hhalf⟩ hm)
  · have hhalf' : Real.pi/2≤x := (lt_of_not_ge hhalf).le
    exact (lower true (by simpa [left,right] using
      (show x∈Icc (Real.pi/2) (171/100:ℝ) from ⟨hhalf',hx.2⟩))).trans_le
      (circle_support hb hB true
        ⟨hhalf',by linarith [hx.2,FrameLowPair.pi_lower]⟩ hm)

end SquaresInCircles.Eight.TableFree.FrameLowMidReverseTransverse
