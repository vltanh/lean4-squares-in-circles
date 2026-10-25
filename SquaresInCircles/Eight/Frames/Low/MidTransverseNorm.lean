module

public import SquaresInCircles.Eight.Frames.Low.MidGeometry

/-!
# Eight squares: the norm of the middle target on the secondary axis

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
