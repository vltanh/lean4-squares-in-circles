module

public import SquaresInCircles.Eight.Frames.Signed.OppositeHardSigns
public import SquaresInCircles.Eight.Owners.Contact.MinimumDerivatives
public import SquaresInCircles.Eight.Owners.Endpoint.Budget
public import SquaresInCircles.Eight.Owners.Positive.CancelingOuter
public import SquaresInCircles.Eight.Owners.Positive.SmallScalar
public import SquaresInCircles.Eight.Owners.Small.PositiveZeroEndpoint
public import SquaresInCircles.Eight.Words.Crossed.ClampBudget
public import SquaresInCircles.Eight.Words.Crossed.SmallScalar

/-!
# Eight squares: the large crossed HG0 capture on the original hard cycle

The middle circle lift only bounds the original HG/GA contact pair (`actual_pair_demand`). The G
support uses that same q-circle (`actual_hard_cap`), and the unchanged original TD witness
supplies the opposite charge. The larger middle tangent forces the original G sign; the opposite
T sign is unrestricted. The capture and its reserve are `HardInput.crossed_HG0_large_reserve`.
-/

section
/-!
## The full crossed HG2/GA0 composite at the original circle

The circle inequality for the original H
bounds its rotated derivative directly, by a positive square comparison.
A feasible-contact continuation then lowers G to the common A/B frame.
The opposite intermediate does not occur in this argument.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedCancelingScalar
open PositiveSmallScalar EndpointRotationPenalty

def S (H : SignedPoint) (h : ℝ) : ℝ :=
  (H.a-1/2)*Real.sin h+(H.y-1/2)*Real.cos h

def U_H (H : SignedPoint) (h : ℝ) : ℝ :=
  (H.a-1/2)*Real.cos h-(H.y-1/2)*Real.sin h

def composite (H : SignedPoint) (P Y r z : ℝ) : ℝ := V P Y z+S H (z+r)
def compositeD (H : SignedPoint) (P Y r z : ℝ) : ℝ := -U P Y z+U_H H (z+r)

structure CapData (q P Y : ℝ) : Prop where
  P_mem : P∈Icc (1/2 : ℝ) (177/250)
  Y_lower : 1≤Y
  circle : (P+1)^2+Y^2≤q
  ceiling : q≤qCap

theorem trig_seven_tenths {h : ℝ} (hh : h∈Icc 0 frameCap) :
    Real.sin h≤6443/10000 ∧ 478/625≤Real.cos h := by
  have he : (7/10:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hs := CorrelatedSameBlock.sin_mono hh he hh.2
  have hc := CorrelatedSameBlock.cos_anti hh he hh.2
  have hs' := sin_upper_five (show (0:ℝ)≤7/10 by norm_num)
  have hc' := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
  constructor <;> norm_num at hs' hc' ⊢ <;> linarith

theorem trig_sixty_six {h : ℝ} (hh : h∈Icc 0 (33/50:ℝ)) :
    Real.sin h≤1533/2500 ∧ 7899/10000≤Real.cos h := by
  have hi : h∈Icc 0 frameCap := ⟨hh.1,by dsimp [frameCap]; linarith [hh.2]⟩
  have he : (33/50:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hs := CorrelatedSameBlock.sin_mono hi he hh.2
  have hc := CorrelatedSameBlock.cos_anti hi he hh.2
  have hs' := sin_upper_five (show (0:ℝ)≤33/50 by norm_num)
  have hc' := cos_lower_six (show (0:ℝ)≤33/50 by norm_num)
  constructor <;> norm_num at hs' hc' ⊢ <;> linarith

/-- The original H circle bounds the second rotated support.  This
single square reserve applies to the complete angle interval. -/
theorem rotated_support_upper {H : SignedPoint} {h : ℝ}
    (hHy : 0≤H.y) (hHq : H.Contained qCap)
    (hh : h∈Icc 0 frameCap) (hS : 73/250≤S H h) : U_H H h<447/500 := by
  have ht := transport_trig hh
  have hb := trig_seven_tenths hh
  let m := Real.cos h+Real.sin h
  let n := Real.cos h-Real.sin h
  have hm : 0≤ m := by dsimp [m]; linarith [ht.1,ht.2.2.1]
  have hn : 0≤n := by dsimp [n]; linarith [ht.2.2.2.2]
  have hmn : m^2+n^2=2 := by
    dsimp [m,n]
    nlinarith [Real.sin_sq_add_cos_sq h]
  have hid : (S H h+m)^2+(U_H H h+n)^2=H.circle := by
    dsimp [S,U_H,m,n,SignedPoint.circle]
    rw [abs_of_nonneg hHy]
    linear_combination (((H.a+1/2)^2+(H.y+1/2)^2)*Real.sin_sq_add_cos_sq h)
  have hlinear : (2595921/5000000:ℝ)≤(73/250)*m+(447/500)*n := by
    dsimp [m,n]
    linarith [hb.1,hb.2]
  by_contra! hbad
  have hs := pow_le_pow_left₀ (show 0≤73/250+m by linarith)
    (show 73/250+m≤S H h+m by linarith) 2
  have hu := pow_le_pow_left₀ (show 0≤447/500+n by linarith)
    (show 447/500+n≤U_H H h+n by linarith) 2
  have hq : H.circle≤9789/2500 := hHq
  nlinarith

theorem V_upper {q P Y z : ℝ} (C : CapData q P Y)
    (hz : z∈Icc 0 frameCap) : V P Y z≤P := by
  have ht := transport_trig hz
  have hc := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤P by linarith [C.P_mem.1])
  have hs := mul_nonneg (show 0≤Y by linarith [C.Y_lower]) ht.2.2.1
  dsimp [V]
  linarith

theorem V_antitone {q P Y : ℝ} (C : CapData q P Y) :
    AntitoneOn (V P Y) (Icc 0 frameCap) := by
  intro x hx z hz hxz
  have hc := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.cos_anti hx hz hxz)
    (show 0≤P by linarith [C.P_mem.1])
  have hs := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.sin_mono hx hz hxz)
    (show 0≤Y by linarith [C.Y_lower])
  dsimp [V]
  linarith

theorem U_lower {q P Y z : ℝ} (C : CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hV : 1/2≤V P Y z) : 1≤U P Y z := by
  have ht := transport_trig hz
  have hp := mul_nonneg (show 0≤P by linarith [C.P_mem.1]) ht.2.2.1
  have hy := mul_nonneg (show 0≤Y by linarith [C.Y_lower])
    (show 0≤Real.cos z by linarith [ht.1])
  have hu : 0≤U P Y z := by dsimp [U]; linarith
  have hv := V_upper C hz
  have hv2 := pow_le_pow_left₀ (show 0≤V P Y z by linarith) hv 2
  nlinarith [rotation_identity P Y z,C.Y_lower]

theorem S_hasDerivAt (H : SignedPoint) (h : ℝ) :
    HasDerivAt (S H) (U_H H h) h := by
  have h1 : HasDerivAt (fun x => (H.a-1/2)*Real.sin x+(H.y-1/2)*Real.cos x)
      ((H.a-1/2)*Real.cos h+(H.y-1/2)*(-Real.sin h)) h :=
    ((Real.hasDerivAt_sin h).const_mul (H.a-1/2)).fun_add
      ((Real.hasDerivAt_cos h).const_mul (H.y-1/2))
  have e : U_H H h=(H.a-1/2)*Real.cos h+(H.y-1/2)*(-Real.sin h) := by simp only [U_H]; ring
  rw [e]
  exact h1

theorem composite_hasDerivAt (H : SignedPoint) (P Y r z : ℝ) :
    HasDerivAt (composite H P Y r) (compositeD H P Y r z) z := by
  have hd : HasDerivAt (fun x => S H (x+r)) (U_H H (z+r)) z :=
    HasDerivAt.comp_add_const z r (S_hasDerivAt H (z+r))
  exact (V_hasDerivAt P Y z).fun_add hd

/-- The source HG2 and GA0 inequalities eliminate the original signed G
coordinate exactly.  G is not raised to any comparison circle. -/
theorem original_pair {H G A : SignedPoint} {r z : ℝ}
    (hr : 0≤r) (hz : 0≤z) (hspan : z+r≤frameCap)
    (hHG : zeroFeasible H G (z+r) 2)
    (hGA : quarterFeasible G A (-z) 0) :
    1≤composite H (A.a-1/2) (A.y+1/2) r z := by
  have hh : z+r∈Icc 0 frameCap := ⟨by linarith,hspan⟩
  have hi : z∈Icc 0 frameCap := ⟨hz,by linarith⟩
  rw [zeroFeasible,edgeWidth_positive_formula hh] at hHG
  rw [quarterFeasible,edgeWidth_negative_formula hi] at hGA
  simp [zeroProjection,quarterProjection,Real.sin_neg,Real.cos_neg] at hHG hGA
  dsimp [composite,V,S]
  linarith

/-- The entire feasible composite improves toward zero.  Feasibility
on the motion is derived by continuation, rather than assumed. -/
theorem alignment_reserve {q P Y r z : ℝ} {H : SignedPoint}
    (C : CapData q P Y) (hHy : 0≤H.y) (hHq : H.Contained q)
    (hr : 0≤r) (hz : 0≤z) (hspan : z+r≤frameCap)
    (hV : 1/2≤V P Y z) (hpair : 1≤composite H P Y r z) :
    ∀x∈Icc 0 z, 1≤composite H P Y r x ∧
      (53/500)*(z-x)≤composite H P Y r x-composite H P Y r z := by
  apply feasible_left_reserve hz (by norm_num : (0:ℝ)<53/500)
  · exact fun x _ => (composite_hasDerivAt H P Y r x).continuousAt.continuousWithinAt
  · intro x hx
    exact composite_hasDerivAt H P Y r x
  · intro x hx hfeasible
    have hxi : x∈Icc 0 frameCap := ⟨hx.1,by linarith [hx.2]⟩
    have hzi : z∈Icc 0 frameCap := ⟨hz,by linarith⟩
    have hhi : x+r∈Icc 0 frameCap := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have hxV : 1/2≤V P Y x := hV.trans (V_antitone C hxi hzi hx.2)
    have hxU := U_lower C hxi hxV
    have hxupper := (V_upper C hxi).trans C.P_mem.2
    have hxS : 73/250≤S H (x+r) := by dsimp [composite] at hfeasible; linarith
    have hhU := rotated_support_upper hHy (hHq.trans C.ceiling) hhi hxS
    dsimp [compositeD]
    linarith
  · exact hpair

end SquaresInCircles.Eight.CrossedCancelingScalar
end
end
end

section
/-!
## A polynomial capture for a crossed large-tangent contact

The left circle and the lift of its hard-contact corner share one quadratic bound
(`paired_circle_upper`). With the free opposite-angle bound this gives one degree-six polynomial
`captureLower` on the middle-tangent interval; a completed square proves its positive reserve
(`capture_polynomial`). At GA alignment every crossing of at least `.04` then violates the
endpoint budget (`aligned_budget_lower`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedLargeCapture
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

/-- The large-tangent left radius and its G lift use the same q-circle, so the two corner
coordinates are bounded jointly. -/
theorem paired_circle_upper {q R W b : ℝ}
    (hb : b∈Icc (1/2 : ℝ) pivot) (_hR : 0≤R) (_hW : 0≤W)
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
    nlinarith only [h1,hr]
  have hright : W≤liftRadius (pivot-b) := by
    have hr := (lift_bounds hd).1
    have hs := lift_square_reserve hd.1
    rw [←hy] at hs
    have h1 : W^2<liftRadius (pivot-b)^2 := by linarith only [hs,hcircle,hlift,hleft]
    nlinarith only [h1,hr]
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

/-- At GA alignment, every crossing of at least `.04` violates the unchanged endpoint budget.
The opposite angle is arbitrary in the frame cap and carries its hard-contact inequality. -/
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

end SquaresInCircles.Eight.CrossedLargeCapture
end
end
end

section
/-!
## Capture and GA-alignment reserve for the large crossed cap

Concavity reduces the G interval to GA alignment and the intrinsic zero-transverse contact.
Both endpoints are excluded when the crossing is at least `.04`, by the polynomial budget and
the signed opposite envelope (`crossing_short`). The retained original opposite hard contact and
the unchanged mixed-endpoint budget are the only global inputs.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedLargeCapture
open PositiveSmallScalar CrossedLargeScalar EndpointRotationPenalty EndpointBudgetScalars

theorem zero_budget_lower {q P Y aB t r Z v : ℝ}
    (I : CrossedLargeScalar.CapData q P Y)
    (hr : r∈Icc 0 frameCap) (hZ : Z∈Icc 0 (1/5 : ℝ))
    (heq : V P Y Z=1/2) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v) :
    117/200<demand q P Y r Z-t+charge*(r-v) := by
  have hZi : Z∈Icc 0 frameCap := ⟨hZ.1,by dsimp [frameCap]; linarith [hZ.2]⟩
  have hp := SignedOppositeHardEnvelope.actual_middle_wrong_bound
    (aA := P+1/2) (aB := aB) (b := Y-1/2) (g := 0) (t := t) (z := Z) (v := v)
    ⟨I.tangent_range.1,I.tangent_range.2.trans (by norm_num [SignedOppositeHardEnvelope.pivot])⟩
    (by linarith [I.P_mem.1])
    (by convert I.circle.le.trans I.ceiling using 1; ring)
    (by convert hB using 1; ring) hZi hv (by norm_num)
    (by dsimp [V] at heq; nlinarith)
    (by convert hBT using 1; ring)
  have B := CrossedLargeScalar.point_bounds I hZi heq.ge
  have hhi : r+Z∈Icc 0 (9/10 : ℝ) := by
    dsimp [frameCap] at hr
    constructor <;> linarith [hr.1,hr.2,hZ.1,hZ.2]
  have hf := CrossedAngleReserve.nonnegative (A := (1/2:ℝ))
    (k := W q P Y Z-1) le_rfl (by linarith [B.W_mem.2]) hhi
  have hfloor : 1≤demand q P Y r Z+charge*(r+Z) := by
    dsimp [CrossedAngleReserve.curve] at hf
    dsimp [demand]
    rw [heq]
    linarith
  linarith

theorem crossing_short {q P Y aB t bH r z v : ℝ}
    (I : CrossedLargeScalar.CapData q P Y)
    (hr : r∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hGA : 1/2≤V P Y z) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v)
    (hHG : demand q P Y r z≤bH)
    (hbudget : bH-t+charge*(r-v)<1-S0) : r<1/25 := by
  by_contra! hwide
  obtain ⟨Z,hzZ,hZshort,hZE,hZall⟩ := CrossedLargeScalar.contact_endpoint I hz hGA
  have hZi : Z∈Icc 0 (1/5 : ℝ) := ⟨by linarith [hz.1],hZshort.le⟩
  have hW0 : W q P Y 0=Real.sqrt (q-P^2) := by simp [W,V]
  have hrad : 0≤q-P^2 := by nlinarith [I.circle,I.P_mem.1,I.Y_mem.1]
  have hWsq : (W q P Y 0)^2+P^2=q := by
    rw [hW0,Real.sq_sqrt hrad]
    ring
  have hleft := aligned_budget_lower
    (q := q) (R := P+1) (W := W q P Y 0) (b := Y-1/2)
    (aB := aB) (t := t) (r := r) (v := v)
    I.tangent_range (by linarith [I.P_mem.1]) (Real.sqrt_nonneg _)
    (by convert I.circle using 1; ring) I.ceiling
    (by convert hWsq using 1; ring)
    (by convert hB using 1; ring) ⟨hwide,hr.2⟩ hv
    (by convert hBT using 1; ring)
  have hleft' : 117/200<demand q P Y r 0-t+charge*(r-v) := by
    rw [show (2:ℝ)-(P+1)=1-P by ring] at hleft
    simpa [demand,V] using hleft
  have hright := zero_budget_lower I hr hZi hZE hv hB hBT
  have hmin := endpoint_minimum I hr hZi hZall ⟨hz.1,hzZ⟩
  have hboth : 117/200+t-charge*(r-v)<
      min (demand q P Y r 0) (demand q P Y r Z) :=
    lt_min (by linarith) (by linarith)
  have hconstant := SmallPositiveZeroEndpoint.endpoint_constant_lower
  linarith

/-- The original budget that captures the crossing also gives the strict displacement reserve
from which the A loss is constructed. -/
theorem captured_alignment_gain {q P Y aB t bH r z v : ℝ}
    (I : CrossedLargeScalar.CapData q P Y)
    (hr : r∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hGA : 1/2≤V P Y z) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v)
    (hHG : demand q P Y r z≤bH)
    (hbudget : bH-t+charge*(r-v)<1-S0) :
    r<1/25 ∧ demand q P Y r 0+z/150≤bH := by
  have hc := crossing_short I hr hz hGA hv hB hBT hHG hbudget
  obtain ⟨Z,hzZ,hZshort,hZE,hZall⟩ := CrossedLargeScalar.contact_endpoint I hz hGA
  have hgain := alignment_gain I ⟨hr.1,hc.le⟩
    ⟨by linarith [hz.1],hZshort.le⟩ hZE hZall ⟨hz.1,hzZ⟩
  exact ⟨hc,by linarith⟩

end SquaresInCircles.Eight.CrossedLargeCapture
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate PositiveSmallScalar EndpointRotationPenalty EndpointBudgetScalars

namespace CrossedLargeGeometry

def capP (q : ℝ) (A : SignedPoint) : ℝ := Real.sqrt (q-(A.y+1/2)^2)-1
def capY (A : SignedPoint) : ℝ := A.y+1/2

theorem actual_hard_cap {q z : ℝ} {G A : SignedPoint}
    (hq : q≤qCap) (hAs : A.Sorted) (hAc : A.AvoidsCore)
    (hAq : A.Contained q) (hAy : 1/2≤A.y) (hGy : G.y≤0)
    (hz : z∈Icc 0 frameCap) (hGA : quarterFeasible G A (-z) 0) :
    CrossedLargeScalar.CapData q (capP q A) (capY A) ∧
      -G.y+1/2≤V (capP q A) (capY A) z := by
  have haa := SignedPoint.primary_gt_half hAs hAc
  have hsource : -G.y+1/2≤(A.a-1/2)*Real.cos z-(A.y+1/2)*Real.sin z :=
    SignedOppositeHardEnvelope.negative_hard_contact hz hGA
  have ht := transport_trig hz
  have hPcos := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤A.a-1/2 by linarith)
  have hYsin := mul_nonneg (show 0≤A.y+1/2 by linarith) ht.2.2.1
  have ha1 : 1≤A.a := by linarith
  have hcircle : (A.a+1/2)^2+(A.y+1/2)^2≤q := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg (show 0≤A.y by linarith)] using hAq
  have hr : 0≤q-(A.y+1/2)^2 := by linarith [sq_nonneg (A.a+1/2)]
  have hs := Real.sq_sqrt hr
  have hs0 := Real.sqrt_nonneg (q-(A.y+1/2)^2)
  have hprimary : A.a-1/2≤capP q A := by
    have h := le_of_pow_le_pow_left₀ two_ne_zero hs0
      (show (A.a+1/2)^2≤(Real.sqrt (q-(A.y+1/2)^2))^2 by rw [hs]; linarith)
    dsimp [capP]; linarith
  have hPl : 1/2≤capP q A := by linarith
  have hq' : q≤9789/2500 := hq
  have hy1 := pow_le_pow_left₀ (by norm_num) (show (1:ℝ)≤A.y+1/2 by linarith) 2
  have hPu : capP q A≤177/250 := by
    have h := le_of_pow_le_pow_left₀ two_ne_zero (by norm_num : (0:ℝ)≤427/250)
      (show (Real.sqrt (q-(A.y+1/2)^2))^2≤(427/250)^2 by rw [hs]; linarith)
    dsimp [capP]; linarith
  have hYu : capY A≤13/10 := by
    have ha2 := pow_le_pow_left₀ (by norm_num) (show (3/2:ℝ)≤A.a+1/2 by linarith) 2
    have h := le_of_pow_le_pow_left₀ two_ne_zero (by norm_num : (0:ℝ)≤13/10)
      (show (A.y+1/2)^2≤(13/10)^2 by linarith)
    dsimp [capY]; linarith
  have hcapcircle : (capP q A+1)^2+(capY A)^2=q := by
    dsimp [capP,capY]
    rw [sub_add_cancel,hs]
    ring
  have hcap := mul_le_mul_of_nonneg_right hprimary (show 0≤Real.cos z by linarith [ht.1])
  refine ⟨⟨⟨hPl,hPu⟩,⟨by dsimp [capY]; linarith,hYu⟩,hcapcircle,hq⟩,?_⟩
  dsimp [V,capY]
  linarith

theorem actual_pair_demand {q r z : ℝ} {H G A : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hGs : G.Sorted) (hGq : G.Contained q) (hGy : G.y≤0)
    (S : CrossedLargeScalar.CapData q (capP q A) (capY A))
    (hz : z∈Icc 0 frameCap) (hh : r+z∈Icc 0 frameCap)
    (hGA : -G.y+1/2≤V (capP q A) (capY A) z)
    (hHG : zeroFeasible H G (r+z) 0) :
    CrossedLargeScalar.demand q (capP q A) (capY A) r z≤H.y := by
  let Vz := V (capP q A) (capY A) z
  let R := SignedPoint.outerAt q (Vz-1/2)
  have hv : 1/2≤Vz := by dsimp [Vz]; linarith
  have hvU : Vz≤177/250 := (CrossedLargeScalar.V_upper S hz).trans S.P_mem.2
  have hy : 0≤Vz-1/2 := by linarith
  have hdiag : |Vz-1/2|≤diagonalCoordinate q := by
    rw [abs_of_nonneg hy]
    linarith [(uniform_circle_reserves hqL hq).1]
  obtain ⟨hRs,hRq,hRc⟩ := SignedPoint.outerAt_spec hqL hdiag
  have hsupport := PositiveCancelingOuter.sorted_support_mono
    (H := G.reflect) (J := R) (by simpa using hGs) hRs
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
    (show 0≤R.y from hy)
    (show G.reflect.circle≤R.circle by simpa [R] using hGq.trans_eq hRq.symm)
    (show G.reflect.y≤R.y by dsimp [SignedPoint.reflect,R,SignedPoint.outerAt]; linarith) hh
  have hRa : R.a=W q (capP q A) (capY A) z-1/2 := by
    change Real.sqrt (q-(|Vz-1/2|+1/2)^2)-1/2=_
    rw [abs_of_nonneg hy,sub_add_cancel]
    rfl
  change G.a*Real.sin (r+z)+(-G.y)*Real.cos (r+z)≤
    R.a*Real.sin (r+z)+(Vz-1/2)*Real.cos (r+z) at hsupport
  rw [hRa] at hsupport
  have hf := hHG
  rw [zeroFeasible,edgeWidth_positive_formula hh] at hf
  simp only [zeroProjection,Matrix.cons_val_zero] at hf
  dsimp [CrossedLargeScalar.demand]
  dsimp [Vz] at hsupport
  linarith

end CrossedLargeGeometry

namespace SignedCycle
open CrossedLargeGeometry

/-- The crossed large side is captured from the original points and the retained original axes.
The lifted cap is only a comparison, and its strict alignment reserve is at the q of the
source. -/
theorem HardOuterGeometry.crossed_HG0_large_reserve {q : ℝ}
    (I : HardOuterGeometry q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H≤I.cycle.theta A)
    (hlarge : 1/2≤(I.cycle.point A).y) (hHG : I.cycle.Feasible H 0) :
    I.cycle.theta A-I.cycle.theta H<1/25 ∧
      CrossedLargeScalar.demand q (capP q (I.cycle.point A)) (capY (I.cycle.point A))
        (I.cycle.theta A-I.cycle.theta H) 0+
        (I.cycle.theta G-I.cycle.theta A)/150≤(I.cycle.point H).y := by
  let r := I.cycle.theta A-I.cycle.theta H
  let z := I.cycle.theta G-I.cycle.theta A
  let v := I.cycle.theta A-I.cycle.theta T
  have hr : r∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hHA,(le_abs_self r).trans (I.necessary.spread A H)⟩
  have hz : z∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hAG,(le_abs_self z).trans (I.necessary.spread G A)⟩
  have hv : v∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hTA,(le_abs_self v).trans (I.necessary.spread A T)⟩
  have hh : r+z∈Icc 0 frameCap := by
    constructor
    · linarith [hr.1,hz.1]
    · have hspan := (le_abs_self (I.cycle.theta G-I.cycle.theta H)).trans
        (I.necessary.spread G H)
      dsimp [r,z]
      linarith
  have hGy := I.large_middle_G_negative hq hAB hnorm hTA hAG hlarge
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-z) 0 := by
    simpa [z,Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,neg_sub]
      using I.GA_hard
  obtain ⟨S,hcap⟩ := actual_hard_cap hq (I.necessary.sorted A) (I.necessary.core A)
    (I.necessary.contained A) hlarge hGy.le hz hGA
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) (r+z) 0 := by
    convert hHG using 1
    simp [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg,r,z]
  have hpair := actual_pair_demand hqL hq (I.necessary.sorted G) (I.necessary.contained G)
    hGy.le S hz hh hcap hHG'
  have hBT : quarterFeasible (I.cycle.point B) (I.cycle.point T) (-v) 2 := by
    rw [show -v=I.cycle.theta T-I.cycle.theta B by dsimp [v]; rw [←hAB]; ring]
    simpa [Feasible,slack,edge,word,delta,next,B,Candidate.T,quarterFeasible,sub_nonneg]
      using I.BT_hard
  have hBTref : quarterFeasible (I.cycle.point T).reflect (I.cycle.point B).reflect (-v) 0 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect _ _ (-v) 2).2 hBT
  have hBTscalar := SignedOppositeHardEnvelope.negative_hard_contact hv hBTref
  simp only [SignedPoint.reflect,neg_neg] at hBTscalar
  have hyB : -(I.cycle.point B).y+1/2=2-capY (I.cycle.point A) := by
    dsimp [capY]
    linarith
  rw [hyB] at hBTscalar
  have hBcircle : ((I.cycle.point B).a+1/2)^2+(2-capY (I.cycle.point A))^2≤qCap := by
    have hb := (I.necessary.contained B).trans hq
    dsimp [SignedPoint.Contained,SignedPoint.circle] at hb
    rw [abs_of_nonpos I.anchors_normal.B_nonpos,hyB] at hb
    exact hb
  have hTD := (signed_outer_charges hq I.necessary I.anchors_normal I.witnesses I.zero_signs).2
  have hep := I.endpoint_bound hq
  have hbudget : (I.cycle.point H).y-(I.cycle.point T).y+EndpointRotationPenalty.charge*(r-v)<1-S0 := by
    dsimp [r,v,epsilon] at *
    linarith
  exact CrossedLargeCapture.captured_alignment_gain S hr hz
    (by linarith) hv hBcircle hBTscalar hpair hbudget

theorem HardInput.crossed_HG0_large_reserve {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H≤I.cycle.theta A)
    (hlarge : 1/2≤(I.cycle.point A).y) (hHG : I.cycle.Feasible H 0) :
    I.cycle.theta A-I.cycle.theta H<1/25 ∧
      CrossedLargeScalar.demand q (capP q (I.cycle.point A)) (capY (I.cycle.point A))
        (I.cycle.theta A-I.cycle.theta H) 0+
        (I.cycle.theta G-I.cycle.theta A)/150≤(I.cycle.point H).y :=
  I.outerGeometry.crossed_HG0_large_reserve hqL hq hAB hnorm hTA hAG hHA hlarge hHG

end SignedCycle
end SquaresInCircles.Eight
end
end
end
