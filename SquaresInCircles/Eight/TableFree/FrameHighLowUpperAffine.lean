module

public import SquaresInCircles.Eight.TableFree.FrameHighLowUpperPolynomial

/-!
# Directed Taylor transfer for the complete affine support interval

The positive polynomial proved in the preceding module bounds the
actual circle norm from above after squaring.  The sign of the
unsquared Taylor expression is proved explicitly, so the argument
does not introduce a spurious root branch.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowUpperAffine
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameHighLowPrimaryGeometry
open FrameHighLowUpperSupport FrameHighLowUpperPolynomial

theorem energy_taylor {x : ℝ} (hx : x∈domain) : (N (lam x) x)^2≤V x := by
  have ht := Arithmetic.trig_taylor_bounds (show 0≤x by linarith [hx.1])
  have hl := lam_bounds hx
  have htrig : FrameLowArc.u*Real.sin x-FrameLowArc.v*Real.cos x≤
      FrameLowArc.u*Arithmetic.sin9 x-FrameLowArc.v*Arithmetic.cos10 x := by
    dsimp [FrameLowArc.u,FrameLowArc.v]
    linarith [ht.2.1,ht.2.2.1]
  have hm := mul_le_mul_of_nonneg_left htrig (show 0≤2*lam x by linarith [hl.1])
  rw [N_square]
  dsimp [energy,V]
  nlinarith only [hm]

theorem scalar_taylor {x : ℝ} (hx : x∈domain) :
    T x<F (lam x) x+R*N (lam x) x-8833/10000 := by
  have ht := Arithmetic.trig_taylor_bounds (show 0≤x by linarith [hx.1])
  have hl := lam_bounds hx
  have hsin := mul_le_mul_of_nonneg_left ht.1 (sub_nonneg.mpr hl.1.le)
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.2 (by norm_num : (0:ℝ)≤9/100)
  have hdiag := mul_le_mul_of_nonneg_right diagonal_precise.2.le
    (show 0≤lam x by linarith [hl.1])
  have ha := a0_precise.1
  have hpi := Arithmetic.pi_hand_enclosure.1
  dsimp [T,F,FrameLowArc.u,FrameLowArc.v]
  nlinarith

theorem root_comparison {x : ℝ} (hx : x∈domain) : R*N (lam x) x<T x := by
  have hp := polynomial_positive hx
  have hT := T_positive hx
  have hV := mul_le_mul_of_nonneg_left (energy_taylor hx)
    (show 0≤Q0 by norm_num [Q0])
  have hroot : 0≤R*N (lam x) x := mul_nonneg R_pos.le (N_nonneg _ _)
  have hsq : (R*N (lam x) x)^2=Q0*(N (lam x) x)^2 := by rw [mul_pow,R_sq]
  dsimp [P] at hp
  by_contra! hbad
  have hh := pow_le_pow_left₀ hT.le hbad 2
  rw [hsq] at hh
  nlinarith

theorem lower {x : ℝ} (hx : x∈domain) : (8833/10000:ℝ)<F (lam x) x := by
  have hs := scalar_taylor hx
  have hn := root_comparison hx
  linarith

theorem weak_separator {z B x : ℝ} (hz : z∈sourceDomain) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤upperMargin true z B x) :
    (8833/10000:ℝ)<upperCost true z B x := by
  have hl := lam_bounds hx
  exact (lower hx).trans_le (circle_support
    (show lam x∈Icc 0 FrameHighLowUpperSupport.K from ⟨by linarith [hl.1],hl.2⟩) hz hB
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩ hm)

end SquaresInCircles.Eight.TableFree.FrameHighLowUpperAffine
