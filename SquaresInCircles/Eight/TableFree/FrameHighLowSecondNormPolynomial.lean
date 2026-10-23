module

public import SquaresInCircles.Eight.TableFree.FrameHighLowFirstNormPolynomial
public import SquaresInCircles.Eight.TableFree.HighOrderTaylor

/-!
# The second quartic norm majorant by positive quadratic expressions

One exact Taylor polynomial is bounded on each sign of the centered
coordinate.  The positive half reduces to two completed squares; the
negative half uses one endpoint power bound.  Neither half is split
into subintervals or supplied with coefficient arrays.
Uncompiled source draft of HAND_LOW_HIGH_SCALAR_REPLACEMENTS §3.2.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowSecondNormPolynomial
open FrameHighLowFirstNormPolynomial FrameCircleArc

def U2 (w : ℝ) : ℝ := 302419/500000+(11993/12500)*w-(6409/31250)*w^2-
  (3817/62500)*w^3+(2247/50000)*w^4
def X2 (w : ℝ) : ℝ := FrameLowArc.u^2+FrameLowArc.v^2+(lam (19/100+w))^2+
  2*lam (19/100+w)*(FrameLowArc.u*Arithmetic.sin9 (19/100+w)-
    FrameLowArc.v*Arithmetic.cos8 (19/100+w))
def B (w : ℝ) : ℝ := (U2 w)^2-X2 w-9/100000000
def negativeLower (y : ℝ) : ℝ :=
  3/2500000-(89/20000000)*y-(113/20000000)*y^2+
    y^3*(1067/1000000-(39349/500000)*y^2)-(181/12500)*y^6
def positiveLower (w : ℝ) : ℝ :=
  3/2500000+(111/25000000)*w-(113/20000000)*w^2-(267/250000)*w^3+
    (63/100000)*w^4+(7869/100000)*w^5-(181/12500)*w^6-
      (4493/1000000)*w^7-(323/20000000)*w^9

theorem negative_remainder {y : ℝ} (hy : 0≤y) : negativeLower y<B (-y) := by
  apply sub_pos.mp
  norm_num [negativeLower,B,U2,X2,lam,FrameLowArc.u,FrameLowArc.v,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos8]
  ring_nf
  positivity

theorem positive_remainder {w : ℝ} (hw : 0≤w) : positiveLower w<B w := by
  apply sub_pos.mp
  norm_num [positiveLower,B,U2,X2,lam,FrameLowArc.u,FrameLowArc.v,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos8]
  ring_nf
  positivity

theorem negative_lower_positive {y : ℝ} (hy : y∈Icc (0:ℝ) (11/100)) :
    (61/100000000:ℝ)<negativeLower y := by
  have h2 := pow_le_pow_left₀ hy.1 hy.2 2
  have h6 := pow_le_pow_left₀ hy.1 hy.2 6
  have hb : 0≤1067/1000000-(39349/500000)*y^2 := by linarith
  have hm := mul_nonneg (pow_nonneg hy.1 3) hb
  dsimp [negativeLower]
  nlinarith [hy.2]

theorem positive_tail {w : ℝ} (hw : w∈Icc (0:ℝ) (29/50)) :
    (137/2000:ℝ)<7869/100000-(181/12500)*w-
      (4493/1000000)*w^2-(323/20000000)*w^4 := by
  have h2 := pow_le_pow_left₀ hw.1 hw.2 2
  have h4 := pow_le_pow_left₀ hw.1 hw.2 4
  linarith [hw.2]

theorem first_quadratic (t : ℝ) :
    (59/50000000:ℝ)<3/2500000-(113/20000000)*t+(63/100000)*t^2 := by
  nlinarith [sq_nonneg ((63/50000:ℝ)*t-113/20000000)]

theorem second_quadratic (t : ℝ) :
    (27/100000000:ℝ)<111/25000000-(267/250000)*t+(137/2000)*t^2 := by
  nlinarith [sq_nonneg ((137/1000:ℝ)*t-267/250000)]

theorem positive_lower_positive {w : ℝ} (hw : w∈Icc (0:ℝ) (29/50)) :
    (59/50000000:ℝ)<positiveLower w := by
  have ht := mul_le_mul_of_nonneg_left (positive_tail hw).le (pow_nonneg hw.1 5)
  have hq0 := first_quadratic (w^2)
  have hq1 := mul_nonneg hw.1 (by linarith [second_quadratic (w^2)] :
    0≤111/25000000-(267/250000)*(w^2)+(137/2000)*(w^2)^2)
  dsimp [positiveLower]
  nlinarith only [ht,hq0,hq1]

theorem squared_reserve {w : ℝ} (hw : w∈domain) : 0<B w := by
  by_cases hneg : w≤0
  · have hy : -w∈Icc (0:ℝ) (11/100) := ⟨by linarith,by linarith [hw.1]⟩
    have hh := (negative_lower_positive hy).trans (negative_remainder hy.1)
    simp only [neg_neg] at hh
    linarith
  · have hp : w∈Icc (0:ℝ) (29/50) := ⟨le_of_not_ge hneg,hw.2⟩
    have hh := (positive_lower_positive hp).trans (positive_remainder hp.1)
    linarith

theorem U2_positive {w : ℝ} (hw : w∈domain) : (49/100:ℝ)<U2 w := by
  by_cases hneg : w≤0
  · have hy : -w∈Icc (0:ℝ) (11/100) := ⟨by linarith,by linarith [hw.1]⟩
    have h2 := pow_le_pow_left₀ hy.1 hy.2 2
    have h3 := pow_nonneg hy.1 3
    have h4 := pow_nonneg hy.1 4
    dsimp [U2]
    nlinarith
  · have hp : 0≤w := le_of_not_ge hneg
    have h2 := pow_le_pow_left₀ hp hw.2 2
    have hb : 0≤11993/12500-(6409/31250)*w-(3817/62500)*w^2 := by
      linarith [hw.2]
    have hm := mul_nonneg hp hb
    have h4 := pow_nonneg hp 4
    dsimp [U2]
    nlinarith

end SquaresInCircles.Eight.TableFree.FrameHighLowSecondNormPolynomial
