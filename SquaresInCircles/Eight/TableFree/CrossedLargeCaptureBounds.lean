module

public import SquaresInCircles.Eight.TableFree.CrossedAngleReserve

/-!
# An explicit polynomial capture for a crossed large-tangent contact

Uncompiled source draft.  The left circle and the lift of its hard-contact
corner share one quadratic bound.  Combining this with the existing free
opposite-angle bound gives one degree-six polynomial on the complete
middle-tangent interval.  A completed square proves its positive reserve.
There is no optimizing-angle or curvature hypothesis in this comparison.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CrossedLargeCapture
open EndpointRotationPenalty SignedOppositeHardEnvelope

def liftRadius (d : ℝ) : ℝ :=
  9573/5000-(2243/10000)*d-(7/500)*d^2

def captureLower (d : ℝ) : ℝ :=
  1+(2-leftRadius d)*(1-(1/25 : ℝ)^2/2)-(liftRadius d-1)/25+
    charge/25-upperValue (-d) (lowTolerance d)

theorem lift_bounds {d : ℝ} (hd : d∈Icc 0 lowLength) :
    liftRadius d∈Icc (9/5 : ℝ) (383/200) := by
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  have hd1 := hd.1
  have hd2 := hd.2
  dsimp [liftRadius,lowLength] at *
  constructor <;> nlinarith [sq_nonneg d]

theorem lift_square_reserve {d : ℝ} (hd : 0≤d) :
    (pivot+1/2-d)^2+2*leftRadius d-1<(liftRadius d)^2 := by
  have hid : (liftRadius d)^2-((pivot+1/2-d)^2+2*leftRadius d-1)=
      7/156250+(7761/25000000)*d+(270169/100000000)*d^2+
        (15701/2500000)*d^3+(49/250000)*d^4 := by
    dsimp [liftRadius,leftRadius,pivot]
    ring
  have hp : 0<7/156250+(7761/25000000)*d+(270169/100000000)*d^2+
      (15701/2500000)*d^3+(49/250000)*d^4 := by positivity
  linarith

/-- The large-tangent left radius and its G lift use the same q-circle.
The second bound is not obtained by independently maximizing the two
corner coordinates. -/
theorem paired_circle_upper {q R W b : ℝ}
    (hb : b∈Icc (1/2 : ℝ) pivot) (hR : 0≤R) (hW : 0≤W)
    (hcircle : R^2+(b+1/2)^2=q) (hq : q≤qCap)
    (hlift : W^2+(R-1)^2=q) :
    R≤leftRadius (pivot-b) ∧ W≤liftRadius (pivot-b) := by
  have hd := low_domain hb
  have hy : b+1/2=pivot+1/2-(pivot-b) := by ring
  have hleft : R≤leftRadius (pivot-b) := by
    have hr := (left_bounds hd).1.1
    have hs := left_square_reserve hd
    rw [←hy] at hs
    have h1 : R^2<leftRadius (pivot-b)^2 := by
      have h2 := hq.trans_lt hs
      linarith only [h2,hcircle]
    nlinarith only [h1,hR,hr]
  have hright : W≤liftRadius (pivot-b) := by
    have hr := (lift_bounds hd).1
    have hs := lift_square_reserve hd.1
    rw [←hy] at hs
    have h1 : W^2<liftRadius (pivot-b)^2 := by linarith only [hs,hcircle,hlift,hleft]
    nlinarith only [h1,hW,hr]
  exact ⟨hleft,hright⟩

theorem capture_polynomial {d : ℝ} (hd : d∈Icc 0 lowLength) :
    117/200<captureLower d := by
  let x := d-289/2500
  have hx : |x|≤7/40 := by
    apply abs_le.mpr
    dsimp [x,lowLength] at *
    constructor <;> linarith [hd.1,hd.2]
  have hx3 : -(343/64000 : ℝ)≤x^3 := by
    have ht := pow_le_pow_left₀ (abs_nonneg x) hx 3
    rw [←abs_pow] at ht
    have hh : |x^3|≤343/64000 := by norm_num at ht ⊢; exact ht
    exact (abs_le.mp hh).1
  let c0 : ℝ := 1996148877755113198653812291/1640625000000000000000000000000
  let c1 : ℝ := -(12135324569501143440091967/765625000000000000000000000)
  let tail : ℝ := 303751978543492219553/2500000000000000000000-
      (20967579424541241/250000000000000000)*x+
      (3707160531693/400000000000000)*x^2+
      (21628474537/400000000000)*x^3+(67417033/960000000)*x^4
  have htail : 53/500≤tail := by
    have hxu := (abs_le.mp hx).2
    dsimp [tail]
    nlinarith [sq_nonneg x,sq_nonneg (x^2)]
  have hlinear : -(2/125)*|x|≤c1*x := by
    have hl := le_abs_self x
    have hr := abs_nonneg x
    have hp := mul_nonneg (show 0≤2/125+c1 by norm_num [c1]) hr
    have hm := mul_le_mul_of_nonneg_left hl (show 0≤ -c1 by norm_num [c1])
    nlinarith
  have hquad := mul_le_mul_of_nonneg_left htail (sq_nonneg x)
  have hsmall : 0<3/2500-(2/125)*|x|+(53/500)*x^2 := by
    have hid : |x|^2=x^2 := sq_abs x
    nlinarith [sq_nonneg (105*|x|-8)]
  have hc : 3/2500<c0 := by norm_num [c0]
  have hid : captureLower d-117/200=c0+c1*x+x^2*tail := by
    dsimp [captureLower,leftRadius,liftRadius,upperValue,rightRadius,rightY,
      referenceAngle,lowTolerance,charge,c0,c1,tail,x]
    ring
  nlinarith

/-- At GA alignment, every crossing at least .04 violates the unchanged
endpoint budget.  The opposite angle is arbitrary in the original frame
cap and carries its actual hard-contact inequality. -/
theorem aligned_budget_lower {q R W aB b t r v : ℝ}
    (hb : b∈Icc (1/2 : ℝ) pivot) (hR : 3/2≤R) (hW : 0≤W)
    (hcircle : R^2+(b+1/2)^2=q) (hq : q≤qCap)
    (hlift : W^2+(R-1)^2=q)
    (hB : (aB+1/2)^2+(3/2-b)^2≤qCap)
    (hr : r∈Icc (1/25 : ℝ) frameCap) (hv : v∈Icc 0 frameCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(3/2-b)*Real.sin v) :
    117/200<
      (1/2+(2-R)*Real.cos r-(W-1)*Real.sin r)-t+charge*(r-v) := by
  let d := pivot-b
  have hd : d∈Icc 0 lowLength := low_domain hb
  obtain ⟨hRL,hWL⟩ := paired_circle_upper hb (by linarith only [hR]) hW hcircle hq hlift
  have hWcap : W≤383/200 := hWL.trans (lift_bounds hd).2
  have hRcap : R<2 := by
    have hY : 1≤b+1/2 := by linarith only [hb.1]
    have hY2 : 1≤(b+1/2)^2 := by nlinarith only [hY]
    have hq' : q≤9789/2500 := hq
    have hR2 : R^2<4 := by linarith only [hcircle,hq',hY2]
    nlinarith only [hR2,hR]
  have hcurve := CrossedAngleReserve.minimum
    (show 2-R≤1/2 by linarith only [hR]) (show W-1≤183/200 by linarith only [hWcap]) hr
  have hr0 : (1/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := (1/25 : ℝ))
  have hsin := Real.sin_le (show (0:ℝ)≤1/25 by norm_num)
  have hsin0 : 0≤Real.sin (1/25 : ℝ) := (transport_trig hr0).2.2.1
  have hcos0 : 0≤Real.cos (1/25 : ℝ) := by linarith only [(transport_trig hr0).1]
  have hleft : (2-leftRadius d)*(1-(1/25 : ℝ)^2/2)-
      (liftRadius d-1)/25≤
      (2-R)*Real.cos (1/25)-(W-1)*Real.sin (1/25) := by
    have hRcoef : 0≤2-leftRadius d := by
      have h := (left_bounds hd).1.2
      linarith only [h]
    have hWcoef : 0≤liftRadius d-1 := by linarith only [(lift_bounds hd).1]
    have hc := mul_le_mul_of_nonneg_left hcos hRcoef
    have hc' := mul_le_mul_of_nonneg_right
      (show 2-leftRadius d≤2-R by linarith only [hRL]) hcos0
    have hs := mul_le_mul_of_nonneg_left hsin hWcoef
    have hs' := mul_le_mul_of_nonneg_right
      (show W-1≤liftRadius d-1 by linarith only [hWL]) hsin0
    linarith only [hc,hc',hs,hs']
  have hYB : 3/2-b=rightY (-d) := by dsimp [rightY,d,pivot]; ring
  have hRB : aB+1/2≤rightRadius (-d) := by
    have hs := right_square_low hd
    rw [←hYB] at hs
    have h1 : (aB+1/2)^2<rightRadius (-d)^2 := by
      have h2 := hB.trans_lt hs
      linarith only [h2]
    nlinarith only [h1,(right_bounds_low hd).1.1]
  have hvcos : 0≤Real.cos v := by linarith only [(transport_trig hv).1]
  have hcap := mul_le_mul_of_nonneg_right
    (show aB-1/2≤rightRadius (-d)-1 by linarith only [hRB]) hvcos
  have hopposite := opposite_low hd hv
  have hfinal := capture_polynomial hd
  rw [hYB] at hBT
  dsimp [rightFunction] at hopposite
  dsimp [CrossedAngleReserve.curve] at hcurve
  dsimp [captureLower] at hfinal
  linarith only [hcurve,hleft,hBT,hcap,hopposite,hfinal]

end SquaresInCircles.Eight.TableFree.CrossedLargeCapture
