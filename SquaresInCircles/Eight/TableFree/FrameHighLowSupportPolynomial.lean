module

public import SquaresInCircles.Eight.TableFree.FrameHighLowSecondNormPolynomial

/-!
# One positive quadratic for the complete high/low support interval

Expanding the two displayed quartics and Taylor sums gives a single
absolute-power lower bound.  Every higher power is absorbed into its
quadratic coefficient on `[-.11,.58]`.  Completing the square leaves
the exact reserve `38999/960000000` throughout the entire interval.
Uncompiled source draft of HAND_LOW_HIGH_SCALAR_REPLACEMENTS §3.3.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowSupportPolynomial
open FrameHighLowFirstNormPolynomial FrameHighLowSecondNormPolynomial

def V0 (w : ℝ) : ℝ :=
  (19/100+w)-(9/100)*Arithmetic.cos8 (19/100+w)+
    (lam (19/100+w)-9/100)*(Arithmetic.sin9 (19/100+w)-3/100000000)+
      lam (19/100+w)+(314159/100000)/4+
        (FrameHighArc.u-FrameHighArc.v)*(449607/500000)+
        FrameLowArc.u*(56583/40000)+
        (FrameHighArc.u-FrameHighArc.v+FrameLowArc.u+FrameLowArc.v+9/50)/2-
          (494697/250000)*(U1 w+U2 w)-8833/10000

def lowerPolynomial (u : ℝ) : ℝ :=
  37/500000-(179/100000)*u+(1097/25000)*u^2-(3423/500000)*u^3-
    (1059/25000)*u^4-(1219/250000)*u^5-(2391/1000000)*u^6-
      (119/1250000)*u^7-(1017/1000000000)*u^9-(193/250000000)*u^10

def quadraticCoefficient (u : ℝ) : ℝ :=
  1097/25000-(3423/500000)*u-(1059/25000)*u^2-(1219/250000)*u^3-
    (2391/1000000)*u^4-(119/1250000)*u^5-(1017/1000000000)*u^7-
      (193/250000000)*u^8

theorem positive_remainder {u : ℝ} (hu : 0≤u) : lowerPolynomial u<V0 u := by
  apply sub_pos.mp
  norm_num [lowerPolynomial,V0,U1,U2,lam,FrameHighArc.u,FrameHighArc.v,
    FrameLowArc.u,FrameLowArc.v,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos8]
  ring_nf
  positivity

theorem negative_remainder {u : ℝ} (hu : 0≤u) : lowerPolynomial u<V0 (-u) := by
  apply sub_pos.mp
  norm_num [lowerPolynomial,V0,U1,U2,lam,FrameHighArc.u,FrameHighArc.v,
    FrameLowArc.u,FrameLowArc.v,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos8]
  ring_nf
  positivity

theorem absolute_remainder (w : ℝ) : lowerPolynomial |w|<V0 w := by
  by_cases hw : 0≤w
  · simpa only [abs_of_nonneg hw] using positive_remainder hw
  · have hn : w≤0 := le_of_not_ge hw
    have hh := negative_remainder (neg_nonneg.mpr hn)
    simpa only [neg_neg,abs_of_nonpos hn] using hh

theorem quadratic_coefficient_lower {u : ℝ} (hu : u∈Icc (0:ℝ) (29/50)) :
    (3/125:ℝ)<quadraticCoefficient u := by
  have h2 := pow_le_pow_left₀ hu.1 hu.2 2
  have h3 := pow_le_pow_left₀ hu.1 hu.2 3
  have h4 := pow_le_pow_left₀ hu.1 hu.2 4
  have h5 := pow_le_pow_left₀ hu.1 hu.2 5
  have h7 := pow_le_pow_left₀ hu.1 hu.2 7
  have h8 := pow_le_pow_left₀ hu.1 hu.2 8
  dsimp [quadraticCoefficient]
  linarith [hu.2]

theorem quadratic_lower {u : ℝ} (hu : u∈Icc (0:ℝ) (29/50)) :
    37/500000-(179/100000)*u+(3/125)*u^2≤lowerPolynomial u := by
  have hh := mul_le_mul_of_nonneg_right (quadratic_coefficient_lower hu).le (sq_nonneg u)
  dsimp [lowerPolynomial,quadraticCoefficient] at *
  nlinarith only [hh]

theorem quadratic_reserve (u : ℝ) :
    (38999/960000000:ℝ)≤37/500000-(179/100000)*u+(3/125)*u^2 := by
  nlinarith [sq_nonneg ((6/125:ℝ)*u-179/100000)]

theorem lower {w : ℝ} (hw : w∈domain) : (38999/960000000:ℝ)<V0 w := by
  have hu : |w|∈Icc (0:ℝ) (29/50) :=
    ⟨abs_nonneg w,abs_le.mpr ⟨by linarith [hw.1],hw.2⟩⟩
  exact (quadratic_reserve |w|).trans_lt ((quadratic_lower hu).trans_lt (absolute_remainder w))

end SquaresInCircles.Eight.TableFree.FrameHighLowSupportPolynomial
