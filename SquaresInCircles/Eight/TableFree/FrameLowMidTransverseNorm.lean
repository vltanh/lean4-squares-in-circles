module

public import SquaresInCircles.Eight.TableFree.FrameLowMidGeometry
public import SquaresInCircles.Eight.TableFree.HighOrderTaylor

/-!
# The actual middle-target transverse norm

The norm and its derivative are retained for the two physical source
signs.  This module also proves the quadratic radical majorant used on
the first whole angular interval, directly by a nonnegative product.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowMidTransverseNorm
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus

def energy (λ x : ℝ) : ℝ :=
  p^2+q^2+λ^2+2*λ*(p*Real.sin x-q*Real.cos x)
def N (λ x : ℝ) : ℝ := Real.sqrt (energy λ x)
def Nd (λ x : ℝ) : ℝ := λ*(p*Real.cos x+q*Real.sin x)/N λ x
def K (λ f : ℝ) : ℝ := 9/100+f-cM+(p+q+λ)/2
def cosCoefficient (λ : ℝ) (second : Bool) : ℝ := if second then λ-9/100 else 9/100
def F (λ f : ℝ) (second : Bool) (x : ℝ) : ℝ :=
  x+K λ f+(λ-9/100)*Real.sin x-cosCoefficient λ second*Real.cos x-R*N λ x
def Fd (λ : ℝ) (second : Bool) (x : ℝ) : ℝ :=
  1+(λ-9/100)*Real.cos x+cosCoefficient λ second*Real.sin x-R*Nd λ x

theorem energy_positive {λ : ℝ} (hλ : λ∈Icc (0:ℝ) 1) (x : ℝ) : 0<energy λ x := by
  have hp : 0<p+λ*Real.sin x := by
    have hh := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin x) hλ.1
    dsimp [p]
    nlinarith [hλ.2]
  have he : energy λ x=(p+λ*Real.sin x)^2+(q-λ*Real.cos x)^2 := by
    dsimp [energy]
    linear_combination -λ^2*(Real.sin_sq_add_cos_sq x)
  rw [he]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hp) (sq_nonneg _)

theorem N_positive {λ : ℝ} (hλ : λ∈Icc (0:ℝ) 1) (x : ℝ) : 0<N λ x :=
  Real.sqrt_pos.mpr (energy_positive hλ x)
theorem N_square {λ : ℝ} (hλ : λ∈Icc (0:ℝ) 1) (x : ℝ) : (N λ x)^2=energy λ x :=
  Real.sq_sqrt (energy_positive hλ x).le
theorem N_deriv {λ : ℝ} (hλ : λ∈Icc (0:ℝ) 1) (x : ℝ) :
    HasDerivAt (N λ) (Nd λ x) x := by
  convert (((((Real.hasDerivAt_sin x).const_mul p).sub
    ((Real.hasDerivAt_cos x).const_mul q)).const_mul (2*λ)).const_add
      (p^2+q^2+λ^2)).sqrt (energy_positive hλ x).ne' using 1
  · rfl
  · dsimp [Nd,N]; ring
theorem F_deriv {λ : ℝ} (hλ : λ∈Icc (0:ℝ) 1) (f : ℝ) (second : Bool) (x : ℝ) :
    HasDerivAt (F λ f second) (Fd λ second x) x := by
  convert ((((hasDerivAt_id x).add_const (K λ f)).add
    ((Real.hasDerivAt_sin x).const_mul (λ-9/100))).sub
      ((Real.hasDerivAt_cos x).const_mul (cosCoefficient λ second))).sub
        ((N_deriv hλ x).const_mul R) using 1 <;> dsimp [F,Fd] <;> ring

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
    _=t/2+n^2/(2*t) := by field_simp [ht.ne']; ring

theorem circle_support (i : Bool) {λ f b B x : ℝ}
    (hλ : λ∈Icc (0:ℝ) 1) (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2)
    (hsource : f≤sign i*(L b-λ*b)) (second : Bool)
    (hx : if second then x∈Icc (Real.pi/2) Real.pi else x∈Icc 0 (Real.pi/2))
    (hm : 0≤FrameLowMidGeometry.secondary i true b B x) :
    F λ f second x≤FrameLowMidGeometry.lowMidCost i true b B x := by
  have hscaled := mul_nonneg hλ.1 hm
  have ht := circle_linear_lower
    (A_circle ⟨b1_mem.1.trans hB.1,hB.2.trans b2_mem.2⟩)
    (-p-λ*Real.sin x) (λ*Real.cos x-q)
  have hn : Real.sqrt ((-p-λ*Real.sin x)^2+(λ*Real.cos x-q)^2)=N λ x := by
    dsimp [N,energy]
    congr 1
    linear_combination λ^2*(Real.sin_sq_add_cos_sq x)
  rw [hn] at ht
  cases second with
  | false =>
      dsimp only [Bool.false_eq_true,ite_false] at hx
      dsimp [FrameLowMidGeometry.secondary] at hscaled
      rw [(first_width hx).1] at hscaled
      dsimp [F,K,cosCoefficient,FrameLowMidGeometry.lowMidCost,M]
      rw [(first_width hx).2]
      norm_num [sign] at hscaled hsource ⊢
      nlinarith
  | true =>
      dsimp only [ite_true] at hx
      dsimp [FrameLowMidGeometry.secondary] at hscaled
      rw [(second_width hx).1] at hscaled
      dsimp [F,K,cosCoefficient,FrameLowMidGeometry.lowMidCost,M]
      rw [(second_width hx).2]
      norm_num [sign] at hscaled hsource ⊢
      nlinarith

end SquaresInCircles.Eight.TableFree.FrameLowMidTransverseNorm
