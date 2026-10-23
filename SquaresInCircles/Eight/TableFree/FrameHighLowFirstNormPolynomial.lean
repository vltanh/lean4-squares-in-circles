module

public import SquaresInCircles.Eight.TableFree.FrameLowHighArc

/-!
# The first quartic norm majorant on the whole high/low interval

The squared difference decreases on `[-.11,.58]`.  Its derivative
sign follows from coefficient grouping and a completed square, and
its final endpoint is positive.  These are identities and inequalities
for one polynomial on one complete interval, not sampled values.
Uncompiled source draft of HAND_LOW_HIGH_SCALAR_REPLACEMENTS §3.1.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowFirstNormPolynomial
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus

def domain : Set ℝ := Icc (-(11/100:ℝ)) (29/50)
def lam (x : ℝ) : ℝ := 495453/500000-(7/25)*x
def U1 (w : ℝ) : ℝ :=
  12336/15625-(48483/250000)*w+(25833/1000000)*w^2+
    (6347/1000000)*w^3+(71/62500)*w^4
def U1d (w : ℝ) : ℝ :=
  -(48483/250000)+2*(25833/1000000)*w+
    3*(6347/1000000)*w^2+4*(71/62500)*w^3
def X1 (w : ℝ) : ℝ := FrameHighArc.u^2+(lam (19/100+w)-FrameHighArc.v)^2
def A (w : ℝ) : ℝ := (U1 w)^2-X1 w
def Ad (w : ℝ) : ℝ := 2*U1 w*U1d w+(14/25)*(lam (19/100+w)-FrameHighArc.v)

theorem lam_bounds {x : ℝ} (hx : x∈Icc (2/25:ℝ) (77/100)) :
    (9/100:ℝ)<lam x ∧ lam x<1 := by dsimp [lam]; constructor <;> linarith [hx.1,hx.2]

theorem U1_deriv (w : ℝ) : HasDerivAt U1 (U1d w) w := by
  convert (((((hasDerivAt_id w).const_mul (-(48483/250000:ℝ))).const_add
    (12336/15625)).add (((hasDerivAt_id w).pow 2).const_mul (25833/1000000))).add
      (((hasDerivAt_id w).pow 3).const_mul (6347/1000000))).add
        (((hasDerivAt_id w).pow 4).const_mul (71/62500)) using 1
  all_goals dsimp [U1,U1d]; ring

theorem A_deriv (w : ℝ) : HasDerivAt A (Ad w) w := by
  have hl : HasDerivAt (fun z => lam (19/100+z)-FrameHighArc.v) (-(7/25:ℝ)) w := by
    convert ((((hasDerivAt_id w).const_add (19/100)).const_mul (-(7/25:ℝ))).const_add
      (495453/500000)).sub_const FrameHighArc.v using 1 <;> dsimp [lam] <;> ring
  convert ((U1_deriv w).pow 2).sub ((hl.pow 2).const_add (FrameHighArc.u^2)) using 1
  all_goals dsimp [A,Ad,X1]; ring

theorem negative_derivative_remainder {y : ℝ} (hy : 0≤y) :
    Ad (-y)<-(97/100000000:ℝ)+(341/50000000)*y^2+
      (169/62500000)*y^3+(101/1000000)*y^6 := by
  apply sub_pos.mp
  norm_num [Ad,U1,U1d,lam,FrameHighArc.v]
  ring_nf
  positivity

theorem positive_derivative_remainder {w : ℝ} (hw : 0≤w) :
    Ad w<-(97/100000000:ℝ)+(269/1000000000)*w+(341/50000000)*w^2+
      w^4*(-563/1000000+(297/500000)*w+(101/1000000)*w^2+(13/1250000)*w^3) := by
  apply sub_pos.mp
  norm_num [Ad,U1,U1d,lam,FrameHighArc.v]
  ring_nf
  positivity

theorem derivative_negative {w : ℝ} (hw : w∈domain) : Ad w<0 := by
  by_cases hneg : w≤0
  · have hy : -w∈Icc (0:ℝ) (11/100) := ⟨by linarith,by linarith [hw.1]⟩
    have hr := negative_derivative_remainder hy.1
    simp only [neg_neg] at hr
    have h2 := pow_le_pow_left₀ hy.1 hy.2 2
    have h3 := pow_le_pow_left₀ hy.1 hy.2 3
    have h6 := pow_le_pow_left₀ hy.1 hy.2 6
    nlinarith
  · have hp : 0≤w := le_of_not_ge hneg
    have hr := positive_derivative_remainder hp
    have h2 := pow_le_pow_left₀ hp hw.2 2
    have h3 := pow_le_pow_left₀ hp hw.2 3
    have hb : -563/1000000+(297/500000)*w+(101/1000000)*w^2+
        (13/1250000)*w^3≤-(9/50000:ℝ) := by linarith [hw.2]
    have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg hp 4)
    have hlin := mul_le_mul_of_nonneg_left hw.2 (by norm_num : (0:ℝ)≤269/1000000000)
    nlinarith [sq_nonneg ((9/25000:ℝ)*w^2-341/50000000)]

theorem A_antitone : AntitoneOn A domain := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun w _ => (A_deriv w).continuousAt.continuousWithinAt
  · exact fun w _ => A_deriv w
  · exact fun w hw => (derivative_negative (Ioo_subset_Icc_self hw)).le

theorem final_reserve : (33/12500000:ℝ)<A (29/50) := by
  norm_num [A,U1,X1,lam,FrameHighArc.u,FrameHighArc.v]

theorem squared_reserve {w : ℝ} (hw : w∈domain) : (33/12500000:ℝ)<A w :=
  final_reserve.trans_le (A_antitone hw ⟨by norm_num,le_rfl⟩ hw.2)

theorem U1_positive {w : ℝ} (hw : w∈domain) : (67/100:ℝ)<U1 w := by
  by_cases hneg : w≤0
  · have hy : -w∈Icc (0:ℝ) (11/100) := ⟨by linarith,by linarith [hw.1]⟩
    have h3 := pow_le_pow_left₀ hy.1 hy.2 3
    have h4 := pow_nonneg hy.1 4
    have h2 := sq_nonneg w
    dsimp [U1]
    nlinarith
  · have hp : 0≤w := le_of_not_ge hneg
    have h2 := sq_nonneg w
    have h3 := pow_nonneg hp 3
    have h4 := pow_nonneg hp 4
    dsimp [U1]
    nlinarith [hw.2]

end SquaresInCircles.Eight.TableFree.FrameHighLowFirstNormPolynomial
