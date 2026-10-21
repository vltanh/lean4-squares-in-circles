module

public import SquaresInCircles.Eight.TableFree.FrameHighLowPrimaryPositiveEarly
public import SquaresInCircles.Eight.TableFree.CircularNorm

/-!
# Exact upper-high / low circle support from the original primary margin

For every nonnegative multiplier below the actual upper-marker
slope, the source functional selects its intrinsic diagonal.  The
target is bounded by its complete shifted circle.  This identity is
shared by the constant and affine whole-angle scalar arguments.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowUpperSupport
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameHighLowPrimaryGeometry

def K : ℝ := 480179/500000
def energy (λ x : ℝ) : ℝ := FrameLowArc.u^2+FrameLowArc.v^2+λ^2+
  2*λ*(FrameLowArc.u*Real.sin x-FrameLowArc.v*Real.cos x)
def N (λ x : ℝ) : ℝ := Real.sqrt (energy λ x)
def F (λ x : ℝ) : ℝ :=
  x+9/100+Real.pi/4+FrameLowArc.u*a0+(FrameLowArc.u+FrameLowArc.v)/2+
    (1/2-c0)*λ+(λ-9/100)*Real.sin x-(9/100)*Real.cos x-R*N λ x

theorem energy_squares (λ x : ℝ) : energy λ x=
    (FrameLowArc.u+λ*Real.sin x)^2+(FrameLowArc.v-λ*Real.cos x)^2 := by
  dsimp [energy]
  linear_combination -λ^2*(Real.sin_sq_add_cos_sq x)

theorem N_nonneg (λ x : ℝ) : 0≤N λ x := Real.sqrt_nonneg _

theorem N_square (λ x : ℝ) : (N λ x)^2=energy λ x := by
  apply Real.sq_sqrt
  rw [energy_squares]
  positivity

theorem source_support {λ z : ℝ} (hλ : λ∈Icc 0 K) (hz : z∈sourceDomain) :
    Real.pi/4-λ*c0≤G z-λ*z := by
  have hm : MonotoneOn (fun t => G t-λ*t) sourceDomain := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t ht => ((G_deriv (source_extended ht)).sub
        ((hasDerivAt_id t).const_mul λ)).continuousAt.continuousWithinAt
    · exact fun t ht => (G_deriv (source_extended (Ioo_subset_Icc_self ht))).sub
        ((hasDerivAt_id t).const_mul λ)
    · intro t ht
      have hh := source_Gd_lower (Ioo_subset_Icc_self ht)
      dsimp [K] at hλ
      linarith [hλ.2]
  have hstart : c0∈sourceDomain := ⟨le_rfl,by linarith [c0_bounds.2,a2_bounds.1]⟩
  simpa only [G_c0] using hm hstart hz hz.1

theorem circle_support {λ z B x : ℝ} (hλ : λ∈Icc 0 K)
    (hz : z∈sourceDomain) (hB : B∈Icc 0 b1) (hx : x∈Icc 0 (Real.pi/2))
    (hm : 0≤upperMargin true z B x) : F λ x≤upperCost true z B x := by
  have hsource := source_support hλ hz
  have hscaled := mul_nonneg hλ.1 hm
  have htarget := circle_linear_lower (A_circle ⟨hB.1,hB.2.trans b1_mem.2⟩)
    (-FrameLowArc.u-λ*Real.sin x) (λ*Real.cos x-FrameLowArc.v)
  have hnorm : Real.sqrt ((-FrameLowArc.u-λ*Real.sin x)^2+
      (λ*Real.cos x-FrameLowArc.v)^2)=N λ x := by
    dsimp [N]
    congr 1
    rw [energy_squares]
    ring
  rw [hnorm] at htarget
  dsimp [upperMargin,sign] at hscaled
  rw [(first_width hx).1] at hscaled
  dsimp [F,upperCost,L,sign]
  rw [(first_width hx).2]
  nlinarith

end SquaresInCircles.Eight.TableFree.FrameHighLowUpperSupport
