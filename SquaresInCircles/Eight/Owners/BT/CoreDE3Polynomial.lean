module

public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Frames.High.Arc
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.DirectedPowerBounds
public import SquaresInCircles.Eight.Owners.Outer.AnchorDomain
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: whole-interval bounds for the core-E DE3 scalars

The small-DE prefix polynomial and the saturated aligned prefix polynomial have positive Bernstein
coefficients on their intervals, `[0, 7/10]` and `[1/5, 7/10]` (`PrefixPolynomial.positive`,
`BasePolynomial.positive`).
-/

section
/-!
## Marker planes of the BT exclusion

The common marker `ZeroPrimary.unsigned` lies above a plane on each chart: above
`tailMargin + tailWeight * s.b` for the BT tail (`tail_marker`) and above `(43/50) s.b` for the
return path (`marker_linear_lower`). The bounds hold on the whole charts, on both pieces of the
core, and with either marker at a junction of charts; the three tail coefficients are data of the
charts.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open FramePair FrameCircleArc FrameLowArc FrameMidArc GlobalZeroSign
open GlobalOuterAnchor

def kappa : ℝ := 49/50
def returnThreshold : ℝ := 103/40
def pathThreshold : ℝ := 16761/4520
def tailWeight : Fin 4→ℝ := ![9449/10000,9449/10000,797/1000,16/25]
def tailMargin : Fin 4→ℝ := ![0,0,229/5000,67/500]

theorem thresholds_sum : pathThreshold+returnThreshold=710/113 := by
  norm_num [pathThreshold,returnThreshold]

theorem low_tail_marker {b : ℝ} (hb : b∈Icc 0 b1) :
    (9449/10000:ℝ)*b≤L b := by
  have hend : 0≤L1-(9449/10000)*b1 := by
    dsimp [L1,FrameLowArc.u,FrameLowArc.v,b1]
    linarith [a1_precise.1,a0_bounds.2]
  have hh := label_loss_lower (lambda := (9449/10000:ℝ))
    (epsilon := 0) hb le_rfl (by simpa using hend)
  linarith

theorem middle_tail_marker {b : ℝ} (hb : b∈Icc b1 b2) :
    (229/5000:ℝ)+(797/1000)*b≤M b := by
  have hh := linear_endpoint_lower (p := p) (q := q-797/1000)
    (by norm_num [p]) b1_mem.1 b2_mem.2 hb
  have hleft : 229/5000-cM≤linear p (q-797/1000) b1 := by
    rw [linear,A_b1]
    dsimp [p,q,cM,b1]
    linarith [a1_precise.1]
  have hright : 229/5000-cM≤linear p (q-797/1000) b2 := by
    rw [linear,A_b2]
    dsimp [p,q,cM,b2]
    linarith [a2_bounds.1]
  have hm := (le_min hleft hright).trans hh
  dsimp [linear,FrameMidArc.M] at hm ⊢
  linarith

theorem high_tail_marker {b : ℝ} (hb : b∈Icc b2 c0) :
    (67/500:ℝ)+(16/25)*b≤FrameHighArc.H b := by
  have hmono : MonotoneOn (fun z => FrameHighArc.H z-(16/25)*z) (Icc b2 c0) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro z hz
      exact ((FrameHighArc.H_deriv hz).sub
        ((hasDerivAt_id z).const_mul (16/25:ℝ))).continuousAt.continuousWithinAt
    · intro z hz
      exact (FrameHighArc.H_deriv (Ioo_subset_Icc_self hz)).sub
        ((hasDerivAt_id z).const_mul (16/25:ℝ))
    · intro z hz
      have hs := (FrameHighArc.slope_high_bounds (Ioo_subset_Icc_self hz)).1
      dsimp [FrameHighArc.Hd,FrameHighArc.u,FrameHighArc.v]
      linarith
  have hleft : (67/500:ℝ)<FrameHighArc.H b2-(16/25)*b2 := by
    rw [FrameHighArc.H_b2]
    dsimp [FrameHighArc.H2,FrameHighArc.k,FrameHighArc.u,FrameHighArc.v,b2]
    linarith [a2_bounds.2,FrameHighArc.diagonal_bounds.1,Arithmetic.pi_hand_enclosure.1]
  have hm := hmono ⟨le_rfl,b2_mem.2⟩ hb hb.1
  dsimp only at hm
  linarith

/-- The marker of a state lies above the tail plane of its chart:
`tailMargin + tailWeight * s.b ≤ unsigned s`. -/
theorem tail_marker (s : State) :
    tailMargin s.branch.type+tailWeight s.branch.type*s.b≤ZeroPrimary.unsigned s := by
  cases hs : s.branch with
  | coreSide | coreCorner =>
      have hc : s.branch.type=0 := by simp [hs,Branch.type]
      have ha := (core_bounds s hc).1
      have hb := s.b_nonneg
      simp only [ZeroPrimary.unsigned,hs,Branch.type,tailWeight,tailMargin,
        Matrix.cons_val_zero,FramePair.label]
      nlinarith
  | low =>
      have hc := state_low_chart s hs
      have hh := low_tail_marker hc.2
      simpa [ZeroPrimary.unsigned,hs,Branch.type,tailWeight,tailMargin,
        FramePair.label,L,FrameLowArc.u,FrameLowArc.v,← hc.1] using hh
  | middle =>
      have hc := state_mid_chart s hs
      have hh := middle_tail_marker hc.2
      simpa [ZeroPrimary.unsigned,hs,Branch.type,tailWeight,tailMargin,
        FramePair.label,FrameMidArc.M,p,q,cM,← hc.1] using hh
  | high =>
      have hc := FrameHighArc.state_high_chart s hs
      have hh := high_tail_marker hc.2
      dsimp [ZeroPrimary.unsigned]
      rw [hs]
      simp only [Branch.type,tailWeight,tailMargin,Matrix.cons_val]
      dsimp [FramePair.label]
      rw [hc.1]
      dsimp [FrameHighArc.H,FrameHighArc.k,FrameHighArc.u,FrameHighArc.v] at hh
      linarith

theorem high_linear_marker (s : State) (hs : s.branch=.high) :
    (43/50:ℝ)*s.b≤ZeroPrimary.unsigned s := by
  have hp := state_support s FrameHighArc.u (43/50-FrameHighArc.v)
  have hn : Real.sqrt (FrameHighArc.u^2+(43/50-FrameHighArc.v)^2)<7379/10000 := by
    have hh := Real.sq_sqrt (show 0≤FrameHighArc.u^2+(43/50-FrameHighArc.v)^2 by positivity)
    have hz := Real.sqrt_nonneg (FrameHighArc.u^2+(43/50-FrameHighArc.v)^2)
    dsimp [FrameHighArc.u,FrameHighArc.v] at *
    nlinarith
  have hR : 0<CommonQuarter.radius := by linarith [CommonQuarter.radius_bounds.1]
  have hprod := (mul_lt_mul_of_pos_left hn hR).trans
    (mul_lt_mul_of_pos_right (show CommonQuarter.radius<1979/1000 by
      linarith [CommonQuarter.radius_bounds.2]) (by norm_num : (0:ℝ)<7379/10000))
  dsimp [ZeroPrimary.unsigned]
  rw [hs]
  dsimp [FramePair.label,FrameHighArc.u,FrameHighArc.v] at hp hn hprod ⊢
  linarith [FrameHighArc.diagonal_bounds.1,Arithmetic.pi_hand_enclosure.1]

theorem marker_linear_lower (s : State) : (43/50:ℝ)*s.b≤ZeroPrimary.unsigned s := by
  have ht := tail_marker s
  have hb := s.b_nonneg
  cases hs : s.branch with
  | coreSide | coreCorner | low =>
      simp [hs,Branch.type,tailWeight,tailMargin] at ht
      linarith
  | middle =>
      have hu := (state_mid_chart s hs).2.2
      have hb2 := b2_bounds.2
      simp [hs,Branch.type,tailWeight,tailMargin] at ht
      linarith
  | high => exact high_linear_marker s hs

end SquaresInCircles.Eight.GlobalBT
end
end
end

section
/-!
## One circle-norm concavity theorem for every BT tail multiplier

The original shared-circle force has norm
sqrt(a²+c²−2ac sin z).  Its exact curvature is bounded using its two
unit force components.  The result holds for every positive a,c,
including the larger core-E multiplier, on the full error interval.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open FramePair FrameCircleArc

def tailNorm (a c z : ℝ) : ℝ := Real.sqrt (a^2+c^2-2*a*c*Real.sin z)
def tailNormD (a c z : ℝ) : ℝ := -a*c*Real.cos z/tailNorm a c z
def tailNormDD (a c z : ℝ) : ℝ :=
  a*c*Real.sin z/tailNorm a c z-a^2*c^2*(Real.cos z)^2/(tailNorm a c z)^3
def normForceU (a c z : ℝ) : ℝ := (a-c*Real.sin z)/tailNorm a c z
def normForceV (a c z : ℝ) : ℝ := c*Real.cos z/tailNorm a c z
def normForceW (a c z : ℝ) : ℝ := c*Real.sin z/tailNorm a c z
def normCos (a c z : ℝ) : ℝ := a*Real.cos z-R*tailNorm a c z
def normCosD (a c z : ℝ) : ℝ := -a*Real.sin z-R*tailNormD a c z
def normCosDD (a c z : ℝ) : ℝ := -a*Real.cos z-R*tailNormDD a c z

theorem tail_energy_positive {a c z : ℝ} (_ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : 0<a^2+c^2-2*a*c*Real.sin z := by
  have ht := transport_trig hz
  have hv : 0<c*Real.cos z := mul_pos hc (by linarith [ht.1])
  have hid : a^2+c^2-2*a*c*Real.sin z=
      (a-c*Real.sin z)^2+(c*Real.cos z)^2 := by
    linear_combination -c^2*(Real.sin_sq_add_cos_sq z)
  rw [hid]
  nlinarith [sq_nonneg (a-c*Real.sin z),sq_pos_of_pos hv]

theorem tailNorm_pos {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : 0<tailNorm a c z :=
  Real.sqrt_pos.mpr (tail_energy_positive ha hc hz)

theorem tailNorm_sq {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : (tailNorm a c z)^2=a^2+c^2-2*a*c*Real.sin z :=
  Real.sq_sqrt (tail_energy_positive ha hc hz).le

theorem tailNorm_literal {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) :
    (tailNorm a c z)^2=(a-c*Real.sin z)^2+(c*Real.cos z)^2 := by
  rw [tailNorm_sq ha hc hz]
  linear_combination -c^2*(Real.sin_sq_add_cos_sq z)

theorem tailNorm_deriv {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : HasDerivAt (tailNorm a c) (tailNormD a c z) z := by
  have hd := ((hasDerivAt_const z (a^2+c^2)).sub
    ((Real.hasDerivAt_sin z).const_mul (2*a*c))).sqrt
      (tail_energy_positive ha hc hz).ne'
  convert hd using 1
  · funext y
    rfl
  · simp only [tailNormD,tailNorm,Pi.sub_apply]
    ring

theorem tailNormD_deriv {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : HasDerivAt (tailNormD a c) (tailNormDD a c z) z := by
  have hn := (tailNorm_pos ha hc hz).ne'
  have hd := ((Real.hasDerivAt_cos z).const_mul (-a*c)).div
    (tailNorm_deriv ha hc hz) hn
  convert hd using 1
  · rfl
  · dsimp [tailNormD,tailNormDD]
    field_simp [hn]

theorem norm_force_unit {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : (normForceU a c z)^2+(normForceV a c z)^2=1 := by
  have hn := (tailNorm_pos ha hc hz).ne'
  have hh := tailNorm_literal ha hc hz
  dsimp [normForceU,normForceV]
  field_simp [hn]
  nlinarith only [hh]

theorem norm_curvature_force {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) :
    tailNormDD a c z=a*((normForceU a c z)^2*normForceW a c z-
      normForceU a c z*(normForceV a c z)^2) := by
  have hn := (tailNorm_pos ha hc hz).ne'
  have hh := tailNorm_literal ha hc hz
  dsimp [tailNormDD,normForceU,normForceV,normForceW]
  field_simp [hn]
  linear_combination Real.sin z*hh

/-- A rational upper bound on u v² over the complete unit circle. -/
theorem unit_cubic_upper {u v : ℝ} (hu : u^2+v^2=1) :
    u*v^2≤(193/500:ℝ) := by
  by_cases hs : u≤0
  · have hh := mul_nonpos_of_nonpos_of_nonneg hs (sq_nonneg v)
    linarith
  · have hs' : 0≤u := by linarith
    have hlast : 0≤4/3-u^2 := by nlinarith [sq_nonneg v]
    have hprod := mul_nonneg (sq_nonneg (u^2-1/3)) hlast
    have hid : 4/27-(u*v^2)^2=(u^2-1/3)^2*(4/3-u^2) := by
      rw [show v^2=1-u^2 by linarith]
      ring
    have hsq : (u*v^2)^2≤4/27 := by nlinarith only [hprod,hid]
    have hn := mul_nonneg hs' (sq_nonneg v)
    nlinarith only [hsq,hn]

theorem tailNorm_curvature_lower {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : -(193/500)*a≤tailNormDD a c z := by
  have hu := unit_cubic_upper (norm_force_unit ha hc hz)
  have hw : 0≤normForceW a c z := by
    dsimp [normForceW]
    exact div_nonneg (mul_nonneg hc.le (transport_trig hz).2.2.1)
      (tailNorm_pos ha hc hz).le
  have hnonneg := mul_nonneg (sq_nonneg (normForceU a c z)) hw
  have hm := mul_le_mul_of_nonneg_left hu ha.le
  rw [norm_curvature_force ha hc hz]
  nlinarith only [hm,mul_nonneg ha.le hnonneg]

theorem normCos_deriv {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : HasDerivAt (normCos a c) (normCosD a c z) z := by
  have hd := ((Real.hasDerivAt_cos z).const_mul a).sub
    ((tailNorm_deriv ha hc hz).const_mul R)
  convert hd using 1
  · rfl
  · simp only [normCosD]
    ring

theorem normCosD_deriv {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : HasDerivAt (normCosD a c) (normCosDD a c z) z := by
  have hd := ((Real.hasDerivAt_sin z).const_mul (-a)).sub
    ((tailNormD_deriv ha hc hz).const_mul R)
  convert hd using 1
  · rfl
  · simp only [normCosDD]

theorem normCos_curvature {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : normCosDD a c z<0 := by
  have hn := mul_le_mul_of_nonneg_left (tailNorm_curvature_lower ha hc hz) R_pos.le
  have hR : R<1979/1000 := by
    have hh := FrameHighArc.radius_bound
    dsimp [FrameHighArc.radiusUpper] at hh
    linarith
  have hRprod := mul_lt_mul_of_pos_right hR ha
  have hcos := mul_lt_mul_of_pos_left (transport_trig hz).1 ha
  dsimp [normCosDD]
  nlinarith only [hn,hRprod,hcos,ha]

theorem normCos_concave {a c : ℝ} (ha : 0<a) (hc : 0<c) :
    ConcaveOn ℝ (Icc 0 frameCap) (normCos a c) :=
  concave_of_deriv2 (fun _ hz => normCos_deriv ha hc hz)
    (fun _ hz => normCosD_deriv ha hc hz)
    (fun _ hz => (normCos_curvature ha hc hz).le)

@[simp] theorem tailNorm_comm (a c z : ℝ) : tailNorm a c z=tailNorm c a z := by
  dsimp [tailNorm]
  congr 1
  ring

end SquaresInCircles.Eight.GlobalBT
end
end
end

section
/-!
## Scalar data of the core-E negative-DE3 tail

The endpoint coefficient `endpointWeight t` is chosen by the DE error `t`: `kappa` for `t ≤ 1/5`
and `m / cos t` beyond. The prefix coefficient `weight p = 3/5 + (2/5) p` depends only on the
total `p` of the prefix errors and stays fixed during the concentration comparison.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.CoreDE3

open FrameCircleArc

def m : ℝ := 269343/250000
def slope : ℝ := 2/5
def weight (p : ℝ) : ℝ := 3/5+slope*p
def endpointWeight (t : ℝ) : ℝ := if t≤1/5 then kappa else m/Real.cos t

def first (p t e : ℝ) : ℝ :=
  Real.pi-p-t+(3/2)*kappa+2*weight p+e+kappa*Real.cos p+
    (e/2)*Real.cos t+e*(13/12)*Real.sin t-
      R*(tailNorm kappa (weight p) p+tailNorm e (weight p) 0)

def last (p t e : ℝ) : ℝ :=
  Real.pi-p-t+(5/2)*kappa+weight p+e+weight p*Real.cos p+
    (e/2)*Real.cos t+e*(13/12)*Real.sin t-
      R*(tailNorm kappa (weight p) 0+tailNorm e (weight p) p)

def base (t e : ℝ) : ℝ :=
  Real.pi-t+(5/2)*kappa+6/5+e*(1+(1/2)*Real.cos t+(13/12)*Real.sin t)-
    R*(tailNorm kappa (3/5) 0+tailNorm e (3/5) 0)

def «prefix» (p : ℝ) : ℝ :=
  Real.pi-p+3*kappa+2*weight p+kappa*Real.cos p-
    R*(tailNorm kappa (weight p) p+tailNorm kappa (weight p) 0)

theorem weight_bounds {p : ℝ} (hp : p∈Icc 0 frameCap) :
    (3/5:ℝ)≤weight p ∧ weight p≤22/25 ∧ weight p≤kappa := by
  dsimp [weight,slope,kappa,frameCap] at *
  constructor
  · linarith [hp.1]
  · constructor <;> linarith [hp.2]

theorem weight_pos {p : ℝ} (hp : p∈Icc 0 frameCap) : 0<weight p := by
  linarith [(weight_bounds hp).1]

theorem first_zero (t e : ℝ) : first 0 t e=base t e := by
  simp [first,base,weight]
  ring

theorem last_zero (t e : ℝ) : last 0 t e=base t e := by
  simp [last,base,weight]
  ring

end SquaresInCircles.Eight.GlobalBT.CoreDE3
end
end
end

section
/-!
## The six complete DE2 tail polynomials

Three intrinsic E charts each give two one-variable endpoint scalars.
Every polynomial is positive on the full interval [0,.7], where its
Bernstein coefficients of degree ten are positive (`positive`).  All constants are rational consequences
of the displayed force norms.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.TailPolynomial

open Polynomial PowerTailBounds DirectedPowerBounds

def e : Fin 3→ℚ := ![9449/10000,797/1000,16/25]
def m : Fin 3→ℚ := ![0,229/5000,67/500]
def initial : Fin 3→ℚ := ![567/1000,13/25,23/50]
def slope : Fin 3→ℚ := ![89/200,73/200,1/4]
def join : Fin 3→ℚ := ![33/445,16/73,14/25]
def weight (i : Fin 3) : ℚ[X] := C (initial i)+C (slope i)*X
def S7 : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5-C (1/5040)*X^7
def C6 : ℚ[X] := 1-C (1/2)*X^2+C (1/24)*X^4-C (1/720)*X^6
def p1 (i : Fin 3) (last : Bool) : ℚ[X] :=
  if last then
    ![C (1132205/1000000)+C (225750/1000000)*X+C (52828/1000000)*X^2,
      C (1109414/1000000)+C (172770/1000000)*X+C (39524/1000000)*X^2,
      C (1082589/1000000)+C (106793/1000000)*X+C (21222/1000000)*X^2] i
  else
    ![C (1132205/1000000)-C (274033/1000000)*X-C (308441/1000000)*X^2,
      C (1109414/1000000)-C (291174/1000000)*X-C (290425/1000000)*X^2,
      C (1082589/1000000)-C (312978/1000000)*X-C (232552/1000000)*X^2] i
def p2 (i : Fin 3) (last : Bool) : ℚ[X] :=
  if last then
    ![C (1101964/1000000)-C (264348/1000000)*X-C (296959/1000000)*X^2,
      C (951635/1000000)-C (242875/1000000)*X-C (241022/1000000)*X^2,
      C (788162/1000000)-C (232523/1000000)*X-C (178814/1000000)*X^2] i
  else
    ![C (1101964/1000000)+C (232011/1000000)*X+C (52697/1000000)*X^2,
      C (951635/1000000)+C (201690/1000000)*X+C (39207/1000000)*X^2,
      C (788162/1000000)+C (146966/1000000)*X+C (21489/1000000)*X^2] i
def x1 (i : Fin 3) (last : Bool) : ℚ[X] :=
  C ((49/50)^2)+weight i^2-(if last then 0 else C (2*(49/50))*weight i*S7)
def x2 (i : Fin 3) (last : Bool) : ℚ[X] :=
  C (e i^2)+weight i^2-(if last then C (2*e i)*weight i*S7 else 0)
def cosinePart (i : Fin 3) (last : Bool) : ℚ[X] :=
  if last then C (49/50)+C (e i)*C6 else C (49/50)*C6+C (e i)
def distance (i : Fin 3) (last : Bool) : ℚ[X] :=
  C (314159/100000+(3/2)*(49/50)+(1/2)*e i+m i-16761/4520)-X+
    C 2*weight i+cosinePart i last
def certificate (i : Fin 3) (last : Bool) : ℚ[X] :=
  C 2*p1 i last*p2 i last*distance i last-C (1979/1000)*
    (p2 i last*(x1 i last+p1 i last^2)+p1 i last*(x2 i last+p2 i last^2))

@[simp] theorem weight_eval (i : Fin 3) (z : ℝ) :
    aeval z (weight i)=(initial i:ℝ)+(slope i:ℝ)*z := by simp [weight]
@[simp] theorem S7_eval (z : ℝ) : aeval z S7=Arithmetic.sin7 z := by
  simp [S7,Arithmetic.sin7]
  ring
@[simp] theorem C6_eval (z : ℝ) : aeval z C6=1-z^2/2+z^4/24-z^6/720 := by
  simp [C6]
  ring

theorem rational_aeval (p : ℚ[X]) (r : ℚ) : aeval (r:ℝ) p=((p.eval r:ℚ):ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n a => simp

theorem centered_domain {z : ℝ} (hz : z∈Icc 0 frameCap) :
    |z-(7/20:ℝ)|≤7/20 := by
  rw [abs_le]
  dsimp [frameCap] at hz
  constructor <;> linarith [hz.1,hz.2]

theorem strict_quadratic {a b c x : ℝ} (ha : 0<a) (hd : b^2<4*a*c) :
    0<a*x^2+b*x+c := by
  have hh := sq_nonneg (2*a*x+b)
  have hmul : 0<4*a*(a*x^2+b*x+c) := by nlinarith only [hh,hd]
  exact (mul_pos_iff_of_pos_left (by positivity : 0<4*a)).1 hmul

/-- Each of the six polynomials has positive Bernstein coefficients of degree `10` on
`[0, 7/10]`: it is a positive combination of the products `z^i (7/10 - z)^(10-i)`, which
`linarith` finds. -/
local macro "tail_positive" : tactic => `(tactic| (
  intro z hz
  have h1 : 0≤7/10-z := sub_nonneg.2 hz.2
  have hb (i j : ℕ) : 0≤z^i*(7/10-z)^j := mul_nonneg (pow_nonneg hz.1 i) (pow_nonneg h1 j)
  simp only [certificate,p1,p2,x1,x2,cosinePart,distance,weight,e,m,initial,slope,S7,C6,
    Bool.false_eq_true,↓reduceIte,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,map_add,map_sub,
    map_mul,map_pow,map_one,map_zero,sub_zero,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 10 0,hb 9 1,hb 8 2,hb 7 3,hb 6 4,hb 5 5,hb 4 6,hb 3 7,hb 2 8,hb 1 9,hb 0 10]))

private theorem positive_0_true : ∀ {z : ℝ},z∈Icc 0 frameCap → 0<aeval z (certificate 0 true) := by
  tail_positive
private theorem positive_0_false : ∀ {z : ℝ},z∈Icc 0 frameCap → 0<aeval z (certificate 0 false) := by
  tail_positive
private theorem positive_1_true : ∀ {z : ℝ},z∈Icc 0 frameCap → 0<aeval z (certificate 1 true) := by
  tail_positive
private theorem positive_1_false : ∀ {z : ℝ},z∈Icc 0 frameCap → 0<aeval z (certificate 1 false) := by
  tail_positive
private theorem positive_2_true : ∀ {z : ℝ},z∈Icc 0 frameCap → 0<aeval z (certificate 2 true) := by
  tail_positive
private theorem positive_2_false : ∀ {z : ℝ},z∈Icc 0 frameCap → 0<aeval z (certificate 2 false) := by
  tail_positive

theorem positive (i : Fin 3) (last : Bool) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0<aeval z (certificate i last) := by
  fin_cases i <;> cases last
  exacts [positive_0_false hz,positive_0_true hz,positive_1_false hz,positive_1_true hz,
    positive_2_false hz,positive_2_true hz]

theorem envelopes_positive (i : Fin 3) (last : Bool) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    1/2<aeval z (p1 i last) ∧ 1/2<aeval z (p2 i last) := by
  obtain ⟨h0,h1⟩ := hz
  have h1' : z≤7/10 := h1
  have h2 : z^2≤(7/10)*z := by
    have hh := mul_le_mul_of_nonneg_left h1' h0
    nlinarith
  fin_cases i <;> cases last <;>
    simp only [p1,p2,Bool.false_eq_true,↓reduceIte,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
      Matrix.tail_cons,map_add,map_sub,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast,
      Rat.cast_div,Rat.cast_ofNat] <;>
    exact ⟨by linarith [sq_nonneg z],by linarith [sq_nonneg z]⟩

theorem weights_bounds (i : Fin 3) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0<aeval z (weight i) ∧ aeval z (weight i)≤kappa ∧ aeval z (weight i)≤(e i:ℝ) := by
  rw [weight_eval]
  dsimp [frameCap] at hz
  obtain ⟨h0,h1⟩ := hz
  fin_cases i <;> norm_num [initial,slope,e,kappa] <;>
    exact ⟨by linarith,by linarith,by linarith⟩

theorem chart_positive (i : Fin 3) : 0<(e i:ℝ) := by fin_cases i <;> norm_num [e]

theorem join_domain (i : Fin 3) : (join i:ℝ)∈Icc 0 frameCap := by
  fin_cases i <;> norm_num [join,frameCap]

theorem join_weight (i : Fin 3) : aeval (join i:ℝ) (weight i)=3/5 := by
  rw [weight_eval]
  fin_cases i <;> norm_num [initial,slope,join]

theorem constant_above_before_join (i : Fin 3) {z : ℝ} (hz : z≤(join i:ℝ)) :
    aeval z (weight i)≤3/5 := by
  rw [weight_eval]
  fin_cases i <;> norm_num [initial,slope,join] at hz ⊢ <;> linarith

theorem affine_above_after_join (i : Fin 3) {z : ℝ} (hz : (join i:ℝ)≤z) :
    3/5≤aeval z (weight i) := by
  rw [weight_eval]
  fin_cases i <;> norm_num [initial,slope,join] at hz ⊢ <;> linarith

end SquaresInCircles.Eight.GlobalBT.TailPolynomial
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.CoreDE3

open Polynomial PowerTailBounds FrameCircleArc

namespace PrefixPolynomial

def c : ℚ[X] := C (3/5)+C (2/5)*X
def P1 : ℚ[X] := C (1149087/1000000)-C (308159/1000000)*X-C (293179/1000000)*X^2
def P2 : ℚ[X] := C (1149087/1000000)+C (210926/1000000)*X+C (41598/1000000)*X^2
def X1 : ℚ[X] := C ((49/50)^2)+c^2-C (2*(49/50))*c*TailPolynomial.S7
def X2 : ℚ[X] := C ((49/50)^2)+c^2
def L : ℚ[X] := C (314159/100000+3*(49/50)-16761/4520)-X+C 2*c+
  C (49/50)*TailPolynomial.C6
def H : ℚ[X] := C 2*P1*P2*L-C (1979/1000)*(P2*(X1+P1^2)+P1*(X2+P2^2))


@[simp] theorem c_eval (p : ℝ) : aeval p c=weight p := by simp [c,weight,slope]

/-- `H` has positive Bernstein coefficients of degree `10` on `[0, 7/10]`: it is a positive
combination of the products `p^i (7/10 - p)^(10-i)`, which `linarith` finds. -/
theorem positive {p : ℝ} (hp : p∈Icc 0 frameCap) : 0<aeval p H := by
  have h1 : 0≤7/10-p := sub_nonneg.2 hp.2
  have hb (i j : ℕ) : 0≤p^i*(7/10-p)^j := mul_nonneg (pow_nonneg hp.1 i) (pow_nonneg h1 j)
  simp only [H,P1,P2,L,X1,X2,c,TailPolynomial.S7,TailPolynomial.C6,map_add,map_sub,map_mul,
    map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 10 0,hb 9 1,hb 8 2,hb 7 3,hb 6 4,hb 5 5,hb 4 6,hb 3 7,hb 2 8,hb 1 9,hb 0 10]

theorem envelopes_positive {p : ℝ} (hp : p∈Icc 0 frameCap) :
    (3/4:ℝ)<aeval p P1 ∧ 1<aeval p P2 := by
  have h2 := pow_le_pow_left₀ hp.1 hp.2 2
  dsimp [frameCap] at hp h2
  norm_num [P1,P2]
  constructor <;> nlinarith [hp.1,hp.2,sq_nonneg p]

end PrefixPolynomial

namespace BasePolynomial

def P : ℚ[X] := C (3083/2500)-C (73/500)*X^2+C (4/125)*X^4
def coefficient : ℚ[X] :=
  C (314159/100000+(5/2)*(49/50)+6/5-11369/5000-16761/4520+(269343/250000)/2)-X
def U : ℚ[X] := 1-C (1/2)*X^2+C (1/24)*X^4
def L : ℚ[X] := coefficient*TailPolynomial.C6+
  C (269343/250000)*(1+C (13/12)*TailPolynomial.S7)
def energy : ℚ[X] := C ((269343/250000)^2)+C (9/25)*U^2
def H : ℚ[X] := C 2*P*L-C (1979/1000)*(energy+P^2)

/-- `H` has positive Bernstein coefficients of degree `11` on `[1/5, 7/10]`. -/
theorem positive {t : ℝ} (ht : t∈Icc (1/5:ℝ) frameCap) : 0<aeval t H := by
  have h0 : 0≤t-1/5 := sub_nonneg.2 ht.1
  have h1 : 0≤7/10-t := sub_nonneg.2 ht.2
  have hb (i j : ℕ) : 0≤(t-1/5)^i*(7/10-t)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  simp only [H,P,L,coefficient,energy,U,TailPolynomial.S7,TailPolynomial.C6,map_add,map_sub,
    map_mul,map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 11 0,hb 10 1,hb 9 2,hb 8 3,hb 7 4,hb 6 5,hb 5 6,hb 4 7,hb 3 8,hb 2 9,hb 1 10,
    hb 0 11]

theorem envelope_positive {t : ℝ} (ht : t∈Icc 0 frameCap) : 1<aeval t P := by
  have h2 := pow_le_pow_left₀ ht.1 ht.2 2
  dsimp [frameCap] at ht h2
  norm_num [P]
  nlinarith [pow_nonneg (sq_nonneg t) 2]

theorem coefficient_positive {t : ℝ} (ht : t∈Icc 0 frameCap) :
    0<aeval t coefficient := by
  norm_num [coefficient]
  dsimp [frameCap] at ht
  linarith [ht.2]

end BasePolynomial

end SquaresInCircles.Eight.GlobalBT.CoreDE3
end
end
end
