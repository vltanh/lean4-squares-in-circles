module

public import SquaresInCircles.Eight.Frames.High.LowSupportPolynomial
public import SquaresInCircles.Eight.Frames.Low.HighGeometry

/-!
# Eight squares: the complete original positive-high / positive-low secondary branch

The two quartic polynomial bounds are transferred to the actual
circle-force norms by directed global Taylor estimates.  Subtracting
the original weak margin then gives the full support inequality on
`[.08,.77]`; the original angle cut and elementary tail finish every
angle.  No minimizing-point or polynomial-positivity premise is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowPositiveCircle
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus
open FrameHighLowFirstNormPolynomial (lam U1)
open FrameHighLowSecondNormPolynomial (U2)

def domain : Set ℝ := Icc (2/25:ℝ) (77/100)
def n1 (x : ℝ) : ℝ := Real.sqrt (FrameHighArc.u^2+(lam x-FrameHighArc.v)^2)
def n2 (x : ℝ) : ℝ := Real.sqrt (FrameLowArc.u^2+FrameLowArc.v^2+(lam x)^2+
  2*lam x*(FrameLowArc.u*Real.sin x-FrameLowArc.v*Real.cos x))
def F (x : ℝ) : ℝ := x-(9/100)*Real.cos x+(lam x-9/100)*Real.sin x+lam x+
  FrameHighArc.k+FrameLowArc.u*a0+
    (FrameHighArc.u-FrameHighArc.v+FrameLowArc.u+FrameLowArc.v+9/50)/2-
      R*(n1 x+n2 x)

theorem centered_domain {x : ℝ} (hx : x∈domain) :
    x-19/100∈FrameHighLowFirstNormPolynomial.domain := by
  constructor <;> linarith [hx.1,hx.2]

theorem taylor_bounds {x : ℝ} (hx : x∈domain) :
    Arithmetic.sin9 x-3/100000000≤Real.sin x ∧ Real.sin x≤Arithmetic.sin9 x ∧
      Arithmetic.cos8 x-3/100000000≤Real.cos x ∧ Real.cos x≤Arithmetic.cos8 x := by
  have hx0 : 0≤x := by linarith [hx.1]
  have hs := HighOrderTaylor.S11_le_sin hx0
  have hc := Arithmetic.cos10_le_cos hx0
  have h11 := pow_le_pow_left₀ hx0 hx.2 11
  have h10 := pow_le_pow_left₀ hx0 hx.2 10
  dsimp [HighOrderTaylor.S11] at hs
  dsimp [Arithmetic.cos10] at hc
  exact ⟨by linarith,Arithmetic.sin_le_sin9 hx0,by linarith,Arithmetic.cos_le_cos8 hx0⟩

theorem n1_square (x : ℝ) :
    (n1 x)^2=FrameHighArc.u^2+(lam x-FrameHighArc.v)^2 :=
  Real.sq_sqrt (by positivity)

theorem n2_energy (x : ℝ) :
    FrameLowArc.u^2+FrameLowArc.v^2+(lam x)^2+
      2*lam x*(FrameLowArc.u*Real.sin x-FrameLowArc.v*Real.cos x)=
        (FrameLowArc.u+lam x*Real.sin x)^2+(FrameLowArc.v-lam x*Real.cos x)^2 := by
  linear_combination -(lam x)^2*(Real.sin_sq_add_cos_sq x)

theorem n2_square (x : ℝ) :
    (n2 x)^2=FrameLowArc.u^2+FrameLowArc.v^2+(lam x)^2+
      2*lam x*(FrameLowArc.u*Real.sin x-FrameLowArc.v*Real.cos x) := by
  apply Real.sq_sqrt
  rw [n2_energy]
  positivity

theorem n1_bound {x : ℝ} (hx : x∈domain) : n1 x<U1 (x-19/100) := by
  have hr := FrameHighLowFirstNormPolynomial.squared_reserve (centered_domain hx)
  have hp := FrameHighLowFirstNormPolynomial.U1_positive (centered_domain hx)
  have hs := n1_square x
  have hn : 0≤n1 x := Real.sqrt_nonneg _
  have hid : 19/100+(x-19/100)=x := by ring
  dsimp [FrameHighLowFirstNormPolynomial.A,FrameHighLowFirstNormPolynomial.X1] at hr
  rw [hid] at hr
  nlinarith

theorem n2_taylor {x : ℝ} (hx : x∈domain) :
    (n2 x)^2≤FrameHighLowSecondNormPolynomial.X2 (x-19/100)+9/100000000 := by
  have ht := taylor_bounds hx
  have hl := FrameHighLowFirstNormPolynomial.lam_bounds hx
  have htrig : FrameLowArc.u*Real.sin x-FrameLowArc.v*Real.cos x≤
      FrameLowArc.u*Arithmetic.sin9 x-FrameLowArc.v*Arithmetic.cos8 x+
        FrameLowArc.v*(3/100000000) := by
    dsimp [FrameLowArc.u,FrameLowArc.v]
    linarith
  have hh := mul_le_mul_of_nonneg_left htrig (show 0≤2*lam x by linarith)
  have herr : 2*lam x*FrameLowArc.v*(3/100000000)≤9/100000000 := by
    dsimp [FrameLowArc.v]
    linarith [hl.2]
  have hid : 19/100+(x-19/100)=x := by ring
  rw [n2_square]
  dsimp [FrameHighLowSecondNormPolynomial.X2]
  rw [hid]
  nlinarith only [hh,herr]

theorem n2_bound {x : ℝ} (hx : x∈domain) : n2 x<U2 (x-19/100) := by
  have hr := FrameHighLowSecondNormPolynomial.squared_reserve (centered_domain hx)
  have hp := FrameHighLowSecondNormPolynomial.U2_positive (centered_domain hx)
  have hs := n2_taylor hx
  have hn : 0≤n2 x := Real.sqrt_nonneg _
  dsimp [FrameHighLowSecondNormPolynomial.B] at hr
  nlinarith

theorem polynomial_transfer {x : ℝ} (hx : x∈domain) :
    FrameHighLowSupportPolynomial.V0 (x-19/100)<F x-8833/10000 := by
  have ht := taylor_bounds hx
  have hl := FrameHighLowFirstNormPolynomial.lam_bounds hx
  have hsin := mul_le_mul_of_nonneg_left ht.1 (sub_nonneg.mpr hl.1.le)
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.2 (by norm_num : (0:ℝ)≤9/100)
  have hsum : n1 x+n2 x≤U1 (x-19/100)+U2 (x-19/100) :=
    add_le_add (n1_bound hx).le (n2_bound hx).le
  have hnorm := mul_le_mul
    (show R≤494697/250000 by linarith [radius_precise.2]) hsum
    (by dsimp [n1,n2]; positivity : 0≤n1 x+n2 x)
    (by norm_num : (0:ℝ)≤494697/250000)
  have hid : 19/100+(x-19/100)=x := by ring
  dsimp [FrameHighLowSupportPolynomial.V0]
  rw [hid]
  dsimp [F,k,FrameHighArc.u,FrameHighArc.v,FrameLowArc.u,FrameLowArc.v]
  nlinarith [Arithmetic.pi_hand_enclosure.1,diagonal_precise.1,a0_precise.1]

theorem lower {x : ℝ} (hx : x∈domain) : (8833/10000:ℝ)<F x := by
  have hp := FrameHighLowSupportPolynomial.lower (centered_domain hx)
  have ht := polynomial_transfer hx
  linarith

theorem circle_support {b B x : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤ secondary true true b B x) : F x≤highLowCost true true b B x := by
  have hlam : 0≤lam x := by linarith [(FrameHighLowFirstNormPolynomial.lam_bounds hx).1]
  have hscaled := mul_nonneg hlam hm
  have hs := circle_linear_lower (A_circle ⟨b2_mem.1.trans hb.1,hb.2⟩)
    (-FrameHighArc.u) (FrameHighArc.v-lam x)
  have ht := circle_linear_lower (A_circle ⟨hB.1,hB.2.trans b1_mem.2⟩)
    (-FrameLowArc.u-lam x*Real.sin x) (lam x*Real.cos x-FrameLowArc.v)
  have hn1 : Real.sqrt ((-FrameHighArc.u)^2+(FrameHighArc.v-lam x)^2)=n1 x := by
    dsimp [n1]
    congr 1
    ring
  have hn2 : Real.sqrt ((-FrameLowArc.u-lam x*Real.sin x)^2+
      (lam x*Real.cos x-FrameLowArc.v)^2)=n2 x := by
    dsimp [n2]
    congr 1
    linear_combination (lam x)^2*(Real.sin_sq_add_cos_sq x)
  rw [hn1] at hs
  rw [hn2] at ht
  have hq : x∈Icc 0 (Real.pi/2) := ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hscaled
  rw [(first_width hq).1] at hscaled
  dsimp [F,highLowCost,H,L,sign]
  rw [(first_width hq).2]
  nlinarith

theorem interval_weak_separator {b B x : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤ secondary true true b B x) :
    (8833/10000:ℝ)<highLowCost true true b B x :=
  (lower hx).trans_le (circle_support hb hB hx hm)

theorem weak_separator {b B x : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : -(34/125:ℝ)≤x) (hm : 0≤ secondary true true b B x) :
    (8833/10000:ℝ)<highLowCost true true b B x := by
  have hcut := high_low_positive_cut hb hB hx hm
  by_cases htail : (77/100:ℝ)≤x
  · exact high_low_tail true true hb hB htail
  · exact interval_weak_separator hb hB ⟨hcut.le,le_of_lt (lt_of_not_ge htail)⟩ hm

end SquaresInCircles.Eight.FrameHighLowPositiveCircle
