module

public import SquaresInCircles.Eight.Owners.All.HighQuarter
public import SquaresInCircles.Eight.Owners.All.HighZeroNegative
public import SquaresInCircles.Eight.Owners.All.HighBridgePolynomials
public import SquaresInCircles.Eight.Owners.All.HighZeroPositive
public import SquaresInCircles.Eight.Owners.Quarter.OuterBridge
public import SquaresInCircles.Eight.Owners.Zero.SourceOuter

/-!
# Eight squares: the actual cyclic quarter and zero components

One potential is assigned to each original physical vertex.  Original
owner classification, radial anchors, and the global variation theorem
supply all component hypotheses.  The six charged edges below are
ready for the remaining original outer DE bridge.
-/

section
/-!
## Explicit norm envelopes for the original nonpositive zero source

The two actual circle forces have polynomial upper envelopes over the
whole frame interval.  Squaring is justified by explicit positive lower
bounds for both envelope factors.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh

open Polynomial FramePair FrameCircleArc ZeroPolynomial

def zeroMu (z : ℝ) : ℝ := 1-z/5
def zeroN1 (z : ℝ) : ℝ := Real.sqrt (1+(zeroMu z)^2-2*zeroMu z*Real.cos z)
def zeroN2 (z : ℝ) : ℝ := Real.sqrt (1+(zeroMu z)^2)

theorem zeroMu_bounds {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (43/50:ℝ)≤zeroMu z ∧ zeroMu z≤1 := by
  dsimp [zeroMu,frameCap] at *
  constructor <;> linarith [hz.1,hz.2]

theorem zeroN1_radicand {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0≤1+(zeroMu z)^2-2*zeroMu z*Real.cos z := by
  have hm : 0≤zeroMu z := by linarith [(zeroMu_bounds hz).1]
  have hp := mul_nonneg hm (sub_nonneg.mpr (Real.cos_le_one z))
  nlinarith [sq_nonneg (1-zeroMu z)]

theorem zeroN1_sq {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (zeroN1 z)^2=1+(zeroMu z)^2-2*zeroMu z*Real.cos z :=
  Real.sq_sqrt (zeroN1_radicand hz)

theorem zeroN2_sq (z : ℝ) : (zeroN2 z)^2=1+(zeroMu z)^2 :=
  Real.sq_sqrt (by positivity)

theorem zero_p1_positive {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (9/10:ℝ)<aeval z p1 := by
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  norm_num [frameCap] at h2
  rw [p1_eval]
  dsimp [frameCap] at hz
  nlinarith [pow_nonneg hz.1 3,pow_nonneg hz.1 4,hz.2]

theorem zero_p2_bounds {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (93/100:ℝ)≤aeval z p2 ∧ aeval z p2≤1 := by
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  have h3 := pow_le_pow_left₀ hz.1 hz.2 3
  norm_num [frameCap] at h2 h3
  have hcoefficient : -(1/10:ℝ)+z/200+z^2/2000+z^3/20000≤0 := by
    dsimp [frameCap] at hz
    nlinarith [hz.2]
  have hprod := mul_nonpos_of_nonneg_of_nonpos hz.1 hcoefficient
  rw [p2_eval]
  dsimp [frameCap] at hz
  constructor
  · nlinarith [sq_nonneg z,pow_nonneg hz.1 3,pow_nonneg hz.1 4,hz.2]
  · nlinarith only [hprod]

theorem zero_p2_square {z : ℝ} (hz : z∈Icc 0 frameCap) :
    1-z/5+z^2/50≤(aeval z p2)^2 := by
  have hbracket : 0≤(1/40000:ℝ)-z/200000+
      3*z^2/4000000+z^3/20000000+z^4/400000000 := by
    dsimp [frameCap] at hz
    nlinarith [sq_nonneg z,pow_nonneg hz.1 3,pow_nonneg hz.1 4,hz.2]
  have hp := mul_nonneg (pow_nonneg hz.1 4) hbracket
  have hi : (1-z/10+z^2/200+z^3/2000+z^4/20000)^2-(1-z/5+z^2/50)=
      z^4*((1/40000:ℝ)-z/200000+3*z^2/4000000+z^3/20000000+z^4/400000000) := by
    ring
  rw [p2_eval]
  nlinarith only [hp,hi]

theorem zeroN1_polynomial_square {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (zeroN1 z)^2≤z^2*aeval z X1 := by
  have hmu : 0≤2*zeroMu z := by linarith [(zeroMu_bounds hz).1]
  have hc := mul_le_mul_of_nonneg_left (cos_lower_six hz.1) hmu
  rw [zeroN1_sq hz,X1_eval]
  dsimp [zeroMu] at *
  nlinarith only [hc]

theorem zeroN1_envelope {z : ℝ} (hz : z∈Icc 0 frameCap) :
    zeroN1 z≤(Real.sqrt 26/5)*z*aeval z p1 := by
  have hp : 0≤aeval z p1 := by linarith [zero_p1_positive hz]
  have he : 0≤(Real.sqrt 26/5)*z*aeval z p1 :=
    mul_nonneg (mul_nonneg (by positivity) hz.1) hp
  have hr := remainder_nonnegative hz
  have hrem : aeval z X1≤(26/25)*(aeval z p1)^2 := by
    simp only [remainder,map_sub,map_mul,map_pow,aeval_C,eq_ratCast] at hr
    push_cast at hr
    linarith
  have hm := mul_le_mul_of_nonneg_left hrem (sq_nonneg z)
  have hs := zeroN1_polynomial_square hz
  have h26 : (Real.sqrt 26)^2=(26:ℝ) := Real.sq_sqrt (by norm_num)
  have hi : ((Real.sqrt 26/5)*z*aeval z p1)^2=(26/25)*z^2*(aeval z p1)^2 := by
    calc
      _=(Real.sqrt 26)^2/25*z^2*(aeval z p1)^2 := by ring
      _=_ := by rw [h26]
  have hn : 0≤zeroN1 z := Real.sqrt_nonneg _
  nlinarith only [hm,hs,hi,he,hn]

theorem zeroN2_envelope {z : ℝ} (hz : z∈Icc 0 frameCap) :
    zeroN2 z≤Real.sqrt 2*aeval z p2 := by
  have hp : 0≤aeval z p2 := by linarith [(zero_p2_bounds hz).1]
  have he : 0≤Real.sqrt 2*aeval z p2 := by positivity
  have hs := zero_p2_square hz
  have hn := zeroN2_sq z
  have h2 : (Real.sqrt 2)^2=(2:ℝ) := Real.sq_sqrt (by norm_num)
  have hi : (Real.sqrt 2*aeval z p2)^2=2*(aeval z p2)^2 := by
    rw [mul_pow,h2]
  have hn0 : 0≤zeroN2 z := Real.sqrt_nonneg _
  dsimp [zeroMu] at hn
  nlinarith

theorem radius_sqrt_twenty_six : R*Real.sqrt 26/5<(1009/500:ℝ) := by
  have h26 : (Real.sqrt 26)^2=(26:ℝ) := Real.sq_sqrt (by norm_num)
  have he : (R*Real.sqrt 26/5)^2=(26/25)*Q0 := by
    calc
      _=R^2*(Real.sqrt 26)^2/25 := by ring
      _=_ := by rw [R_sq,h26]; ring
  have hp : 0≤R*Real.sqrt 26/5 :=
    div_nonneg (mul_nonneg R_pos.le (Real.sqrt_nonneg _)) (by norm_num)
  norm_num [Q0] at he
  nlinarith

theorem radius_sqrt_two : R*Real.sqrt 2=2*c0+1 := by
  have h2 : (Real.sqrt 2)^2=(2:ℝ) := Real.sq_sqrt (by norm_num)
  have he : (R*Real.sqrt 2)^2=2*Q0 := by rw [mul_pow,R_sq,h2]; ring
  have hp : 0≤R*Real.sqrt 2 := mul_nonneg R_pos.le (Real.sqrt_nonneg _)
  nlinarith [c0_circle,c0_bounds.1]

theorem radius_norm1_envelope {z : ℝ} (hz : z∈Icc 0 frameCap) :
    R*zeroN1 z≤(1009/500)*z*aeval z p1 := by
  have hfirst := mul_le_mul_of_nonneg_left (zeroN1_envelope hz) R_pos.le
  have hp : 0≤z*aeval z p1 := mul_nonneg hz.1 (by linarith [zero_p1_positive hz])
  have hsecond := mul_le_mul_of_nonneg_right radius_sqrt_twenty_six.le hp
  nlinarith only [hfirst,hsecond]

theorem radius_norm2_difference {z : ℝ} (hz : z∈Icc 0 frameCap) :
    R*(zeroN2 z-Real.sqrt 2)≤(139921/50000)*(aeval z p2-1) := by
  have hfirst := mul_le_mul_of_nonneg_left (zeroN2_envelope hz) R_pos.le
  have hR : (139921/50000:ℝ)≤R*Real.sqrt 2 := by
    rw [radius_sqrt_two]
    linarith [diagonal_bounds.1]
  have hsecond := mul_le_mul_of_nonpos_right hR (sub_nonpos.mpr (zero_p2_bounds hz).2)
  nlinarith only [hfirst,hsecond]

end SquaresInCircles.Eight.GlobalAllHigh
end
end
end

section
/-!
## Zero edges from a nonpositive source

For a source with nonpositive transverse coordinate, the fixed positive multiplier `zeroMu` is
applied to the projection of owner `2`, and the corner disks of both states bound the forces
(`zero_source_force`, `zero_target_force`). The source may be on the core or outer: containment
suffices for its force bound. The polynomials `H` and `L` then bound the charge on the high and on
the lower target charts (`nonpositive_zero_high_transfer`, `nonpositive_zero_lower_transfer`),
which gives `nonpositive_zero_charge`.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh

open Polynomial FramePair FrameCircleArc GlobalZeroSign GlobalOuterAnchor ZeroPolynomial

def zeroHighRaw (z : ℝ) : ℝ := z+kappa*(zeroMu z*(1+Real.sin z)-1-
  R*zeroN1 z-R*(zeroN2 z-Real.sqrt 2))
def zeroLowRaw (z : ℝ) : ℝ := zeroGap+z+kappa*(zeroMu z*Real.sin z+z/250-R*zeroN1 z)

theorem zero_source_force (s : State) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (zeroMu z*Real.sin z)*s.a+(1-zeroMu z*Real.cos z)*s.b≤
      R*zeroN1 z-(zeroMu z*Real.sin z+1-zeroMu z*Real.cos z)/2 := by
  have hn : 0≤zeroN1 z := Real.sqrt_nonneg _
  have hnorm : (zeroMu z*Real.sin z)^2+(1-zeroMu z*Real.cos z)^2=(zeroN1 z)^2 := by
    have hu := congrArg (fun r : ℝ => (zeroMu z)^2*r) (Real.sin_sq_add_cos_sq z)
    nlinarith [zeroN1_sq hz]
  have hsq : Q0*((zeroMu z*Real.sin z)^2+(1-zeroMu z*Real.cos z)^2)≤
      (R*zeroN1 z)^2 := by
    rw [hnorm,mul_pow,R_sq]
  convert circle_product_support s (mul_nonneg R_pos.le hn) hsq using 1
  ring

theorem zero_target_force (t : State) (z : ℝ) :
    t.a+zeroMu z*t.b≤R*zeroN2 z-(1+zeroMu z)/2 := by
  have hn : 0≤zeroN2 z := Real.sqrt_nonneg _
  have hsq : Q0*((1:ℝ)^2+(zeroMu z)^2)≤(R*zeroN2 z)^2 := by
    rw [mul_pow,R_sq,zeroN2_sq]
    norm_num
  simpa only [one_mul] using circle_product_support t (mul_nonneg R_pos.le hn) hsq

theorem high_polynomial_transfer {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z H≤zeroHighRaw z := by
  have hmu : 0≤zeroMu z := by linarith [(zeroMu_bounds hz).1]
  have hs : Arithmetic.sin7 z≤Real.sin z := by
    simpa only [Arithmetic.sin7] using sin_lower_seven hz.1
  have hsin := mul_le_mul_of_nonneg_left hs hmu
  have hnorm1 := radius_norm1_envelope hz
  have hnorm2 := radius_norm2_difference hz
  rw [H_eval]
  dsimp [zeroHighRaw,zeroMu,kappa] at *
  nlinarith only [hsin,hnorm1,hnorm2]

theorem low_polynomial_transfer {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z L≤zeroLowRaw z := by
  have hmu : 0≤zeroMu z := by linarith [(zeroMu_bounds hz).1]
  have hs : Arithmetic.sin7 z≤Real.sin z := by
    simpa only [Arithmetic.sin7] using sin_lower_seven hz.1
  have hsin := mul_le_mul_of_nonneg_left hs hmu
  have hnorm := radius_norm1_envelope hz
  rw [L_eval]
  dsimp [zeroLowRaw,zeroMu,kappa] at *
  nlinarith only [hsin,hnorm]

theorem lower_target_constant_gap : zeroGap<2*kappa*c0-
    ((6/5)*zeroU+(13/25)*(kappa-zeroV)+rho*highConstant) := by
  have hpi := Arithmetic.two_pi_lt_710_over_113
  have hc := diagonal_bounds.1
  dsimp [zeroGap,zeroU,zeroV,highConstant,kappa,rho] at *
  linarith

theorem nonpositive_zero_high_transfer (s t : State) (ht : t.branch=.high)
    (hs : transverse s≤0) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width z≤ s.a*Real.sin z+transverse s*Real.cos z+t.b) :
    aeval z H≤zeroCharge s t z-gammaZero := by
  have hsy : transverse s= -s.b := transverse_nonpos_eq s hs
  have hmu : 0≤zeroMu z := by linarith [(zeroMu_bounds hz).1]
  have hproj := mul_le_mul_of_nonneg_left hm hmu
  have hsource := zero_source_force s hz
  have htarget := zero_target_force t z
  have hR := radius_sqrt_two
  have hsin := (transport_trig hz).2.2.1
  have hraw : zeroHighRaw z≤zeroCharge s t z-gammaZero := by
    simp only [GlobalOuterAnchor.width,abs_of_nonneg hsin,hsy] at hproj
    rw [zeroCharge,potential_high t ht,hsy]
    dsimp [zeroHighRaw,gammaZero,kappa]
    nlinarith only [hproj,hsource,htarget,hR]
  exact (high_polynomial_transfer hz).trans hraw

theorem nonpositive_zero_lower_transfer (s t : State)
    (ht : t.branch=.low ∨ t.branch=.middle) (hs : transverse s≤0)
    {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width z≤ s.a*Real.sin z+transverse s*Real.cos z+t.b) :
    aeval z L≤zeroCharge s t z-gammaZero := by
  have hsy : transverse s= -s.b := transverse_nonpos_eq s hs
  have hmu := zeroMu_bounds hz
  have hproj := mul_le_mul_of_nonneg_left hm (show 0≤zeroMu z by linarith [hmu.1])
  have hsource := zero_source_force s hz
  have hpotential := potential_upper t
  have htarget := lower_chart_linear_upper t ht
    (by norm_num [zeroU] : 0≤zeroU)
    (show zeroU*(102/169)≤kappa*zeroMu z-zeroV by
      dsimp [zeroU,zeroV,kappa]
      linarith [hmu.1])
  have hgap := lower_target_constant_gap
  have hsin := (transport_trig hz).2.2.1
  have hraw : zeroLowRaw z≤zeroCharge s t z-gammaZero := by
    simp only [GlobalOuterAnchor.width,abs_of_nonneg hsin,hsy] at hproj
    rw [zeroCharge,hsy]
    dsimp [zeroLowRaw,gammaZero,zeroMu,kappa] at hproj hsource htarget hgap ⊢
    nlinarith only [hproj,hsource,htarget,hpotential,hgap]
  exact (low_polynomial_transfer hz).trans hraw

/-- The zero charge of owner `2` from a nonpositive source: no loss on the lower target charts, a
loss below `7/1000` on the high chart, and none there for angles up to `7/20`. -/
theorem nonpositive_zero_charge (s t : State) (ht : t.branch.type≠0)
    (hs : transverse s≤0) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width z≤ s.a*Real.sin z+transverse s*Real.cos z+t.b) :
    gammaZero-7/1000<zeroCharge s t z ∧
      ((z≤7/20 ∨ t.branch≠.high) → gammaZero≤zeroCharge s t z) := by
  cases hbr : t.branch with
  | coreSide | coreCorner => simp [hbr,Branch.type] at ht
  | low =>
      have htfer := nonpositive_zero_lower_transfer s t (Or.inl hbr) hs hz hm
      have hpos := L_positive hz
      exact ⟨by linarith,fun _ => by linarith⟩
  | middle =>
      have htfer := nonpositive_zero_lower_transfer s t (Or.inr hbr) hs hz hm
      have hpos := L_positive hz
      exact ⟨by linarith,fun _ => by linarith⟩
  | high =>
      have htfer := nonpositive_zero_high_transfer s t hbr hs hz hm
      have hlower := H_lower hz
      refine ⟨by linarith,?_⟩
      intro hshort
      have hzshort : z≤7/20 := hshort.resolve_right (fun hn => hn rfl)
      have hnonneg := H_short_nonnegative ⟨hz.1,hzshort⟩
      linarith

end SquaresInCircles.Eight.GlobalAllHigh
end
end
end

section
/-!
## The zero edges and their shared variation budget

A weak witness of owner `0` or `2` on a zero edge into an outer target with nonpositive transverse
coordinate makes the zero charge exceed `gammaZero - 7/1000`, and reach `gammaZero` unless the
error exceeds `7/20` on a high target from a source with negative transverse coordinate
(`zero_charge`). This covers every error, source sign, core piece and outer chart of the target.
At most one of three zero edges can use that loss range, since their positive variations add up
to less than `7/10` (`three_zero_charge_bound`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.GlobalAllHigh

open FramePair GlobalOuterAnchor

/-- The zero charge of a weak witness of owner `0` or `2`. The only sign premise, that owner `0`
has a source with positive transverse coordinate, is the implication given by the sign
classification of the zero owners. -/
theorem zero_charge (s t : State) (htOuter : t.branch.type≠0)
    (ht : transverse t≤0) {j : Fin 4} {d : ℝ}
    (hj : j=0 ∨ j=2) (hd : |d|≤frameCap)
    (hm : s.Feasible t j d) (hsource : j=0 → 0<transverse s) :
    gammaZero-7/1000<zeroCharge s t d ∧
      ((d≤7/20 ∨ 0≤transverse s ∨ t.branch≠.high) → gammaZero≤zeroCharge s t d) := by
  have hproj : GlobalOuterAnchor.width d≤transverse s+t.a*Real.sin d+t.b*Real.cos d ∨
      GlobalOuterAnchor.width d≤ s.a*Real.sin d+transverse s*Real.cos d+t.b := by
    rcases hj with rfl | rfl
    · left
      have hh := (left_margin s t false hd ht).1 (by
        simpa only [leftOwner,Bool.false_eq_true,ite_false] using hm)
      exact hh
    · right
      have hh := (left_margin s t true hd ht).1 (by
        simpa only [leftOwner,ite_true] using hm)
      exact hh
  by_cases hy : 0≤transverse s
  · have hc := zero_nonnegative_source s t htOuter hy hd hproj
    exact ⟨by linarith,fun _ => hc⟩
  · have hs : transverse s≤0 := (lt_of_not_ge hy).le
    have hj2 : j=2 := by
      rcases hj with hj | hj
      · exact (hy (hsource hj).le).elim
      · exact hj
    have hdpos : 0<d := by
      by_contra! hdn
      exact hy (zero_nonpositive_error_source s t hd hdn hproj).le
    have hm2 : GlobalOuterAnchor.width d≤ s.a*Real.sin d+transverse s*Real.cos d+t.b := by
      have hh := (left_margin s t true hd ht).1 (by
        simpa only [leftOwner,ite_true,hj2] using hm)
      exact hh
    have hc := nonpositive_zero_charge s t htOuter hs
      ⟨hdpos.le,(le_abs_self d).trans hd⟩ hm2
    refine ⟨hc.1,?_⟩
    rintro (hshort | hpositive | hlower)
    · exact hc.2 (Or.inl hshort)
    · exact (hy hpositive).elim
    · exact hc.2 (Or.inr hlower)

theorem three_zero_charge_bound {d₀ d₁ d₂ C₀ C₁ C₂ : ℝ}
    (hvariation : max d₀ 0+max d₁ 0+max d₂ 0<frameCap)
    (h₀ : gammaZero-7/1000<C₀ ∧ (d₀≤7/20 → gammaZero≤C₀))
    (h₁ : gammaZero-7/1000<C₁ ∧ (d₁≤7/20 → gammaZero≤C₁))
    (h₂ : gammaZero-7/1000<C₂ ∧ (d₂≤7/20 → gammaZero≤C₂)) :
    3*gammaZero-7/1000<C₀+C₁+C₂ := by
  by_cases hd₀ : d₀≤7/20
  · by_cases hd₁ : d₁≤7/20
    · linarith [h₀.2 hd₀,h₁.2 hd₁,h₂.1]
    · have hbad₁ : (7/20:ℝ)<d₁ := lt_of_not_ge hd₁
      have hd₂ : d₂≤7/20 := by
        by_contra! hn
        dsimp [frameCap] at hvariation
        linarith [le_max_right d₀ 0,le_max_left d₁ 0,le_max_left d₂ 0]
      linarith [h₀.2 hd₀,h₁.1,h₂.2 hd₂]
  · have hbad₀ : (7/20:ℝ)<d₀ := lt_of_not_ge hd₀
    have hd₁ : d₁≤7/20 := by
      by_contra! hn
      dsimp [frameCap] at hvariation
      linarith [le_max_left d₀ 0,le_max_left d₁ 0,le_max_right d₂ 0]
    have hd₂ : d₂≤7/20 := by
      by_contra! hn
      dsimp [frameCap] at hvariation
      linarith [le_max_left d₀ 0,le_max_right d₁ 0,le_max_left d₂ 0]
    linarith [h₀.1,h₁.2 hd₁,h₂.2 hd₂]

end SquaresInCircles.Eight.GlobalAllHigh
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.GlobalAllHigh

open Candidate FramePair GlobalOuterAnchor

def cyclePotential (C : BoundaryCycle Q0) (i : Vertex) : ℝ :=
  if word i=0 then kappa*transverse (stateOf C i) else potential (stateOf C i)
def cycleCharge (C : BoundaryCycle Q0) (theta : Vertex→ℝ) (i : Vertex) : ℝ :=
  Candidate.phi theta i+(cyclePotential C i-cyclePotential C (next i))

theorem cycleCharge_sum (C : BoundaryCycle Q0) (theta : Vertex→ℝ) :
    (∑i,cycleCharge C theta i)=2*Real.pi := by
  simp only [cycleCharge,Finset.sum_add_distrib,sum_phi,sum_marker_difference,add_zero]

theorem cycleCharge_zero (C : BoundaryCycle Q0) (theta : Vertex→ℝ)
    (i : Vertex) (hi : word i=0) (hn : word (next i)=1) :
    cycleCharge C theta i=zeroCharge (stateOf C i) (stateOf C (next i)) (delta theta i) := by
  simp [cycleCharge,cyclePotential,Candidate.phi,hi,hn,zeroCharge]
  ring

theorem cycleCharge_quarter (C : BoundaryCycle Q0) (theta : Vertex→ℝ)
    (i : Vertex) (hi : word i=1) (hn : word (next i)=0) :
    cycleCharge C theta i=Real.pi/2+
      quarterCharge (stateOf C i) (transverse (stateOf C (next i))) (delta theta i) := by
  simp [cycleCharge,cyclePotential,Candidate.phi,hi,hn,quarterCharge]
  ring

theorem cycleCharge_DE (C : BoundaryCycle Q0) (theta : Vertex→ℝ) :
    cycleCharge C theta D=Real.pi/2+delta theta D+potential (stateOf C D)-potential (stateOf C E) := by
  simp [cycleCharge,cyclePotential,Candidate.phi,word,D,E,next]
  ring

theorem state_outer_of_kind (C : BoundaryCycle Q0) (i : Vertex) (hi : C.kind i=.outer) :
    (stateOf C i).branch.type≠0 := by
  intro hc
  exact ((branchOf_core_iff C i).1 hc) hi

theorem state_transverse_eq (C : BoundaryCycle Q0) (i : Vertex) :
    transverse (stateOf C i)=C.a i*C.tangent i := by
  simp only [transverse,stateOf,signOf_spec,BoundaryCycle.tangent]
  field_simp [(C.a_pos i).ne']

theorem state_positive_of_tangent (C : BoundaryCycle Q0) (i : Vertex)
    (hi : 0<C.tangent i) : 0<transverse (stateOf C i) := by
  rw [state_transverse_eq]
  exact mul_pos (C.a_pos i) hi

theorem state_negative_of_tangent (C : BoundaryCycle Q0) (i : Vertex)
    (hi : C.tangent i<0) : transverse (stateOf C i)<0 := by
  rw [state_transverse_eq]
  exact mul_neg_of_pos_of_neg (C.a_pos i) hi

theorem frame_state_feasible {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (i : Vertex) (j : Fin 4)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (stateOf C i).Feasible (stateOf C (next i)) j (Candidate.phi F.theta i) := by
  have hh := stateOf_feasible C i j haxis
  have hphase : pairAngle C i=Candidate.phi F.theta i :=
    (pairAngle_gap C i).trans (F.physical_angle i).symm
  rwa [hphase] at hh

/-- A high quarter followed by a zero supplies every domain condition
of the complete quarter theorem directly on the physical states. -/
theorem frame_quarter_charge {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (i : Vertex) (hi : word i=1) (hn : word (next i)=0)
    (j : Fin 4) (hj : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    Real.pi/2+kappa≤cycleCharge C F.theta i := by
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hs := GlobalQuarterOuter.frame_high_anchor F hq i hi j hj haxis
  have ht : (stateOf C (next i)).branch.type≠0 ∨
      0<transverse (stateOf C (next i)) := by
    by_cases hp : 0<C.tangent (next i)
    · exact Or.inr (state_positive_of_tangent C (next i) hp)
    · exact Or.inl (state_outer_of_kind C (next i)
        (GlobalZeroSourceOuter.frame_nonpositive_source_outer F hq (next i) hn
          (le_of_not_gt hp)))
  have hm := frame_state_feasible F i j haxis
  have hm' : (stateOf C i).Feasible (stateOf C (next i)) j
      (Real.pi/2+delta F.theta i) := by
    simpa [Candidate.phi,hi] using hm
  have hc := high_quarter_charge (stateOf C i) (stateOf C (next i))
    (state_outer_of_kind C i hs.1) (state_negative_of_tangent C i hs.2).le ht hj
    (by simpa only [frameCap] using (F.delta_small i).le) hm'
  rw [cycleCharge_quarter C F.theta i hi hn]
  linarith [hc.1]

/-- The following high quarter makes the zero target a negative outer
anchor.  Its original zero witness is then classified independently. -/
theorem frame_zero_charge {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (i : Vertex) (hi : word i=0) (hn : word (next i)=1)
    (j p : Fin 4) (hp : p=2 ∨ p=3)
    (hzero : (forwardAxis j).Feasible (C.square i) (C.square (next i)))
    (hquarter : (forwardAxis p).Feasible (C.square (next i)) (C.square (next (next i)))) :
    gammaZero-7/1000<cycleCharge C F.theta i ∧
      (delta F.theta i≤7/20 → gammaZero≤cycleCharge C F.theta i) := by
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have ht := GlobalQuarterOuter.frame_high_anchor F hq (next i) hn p hp hquarter
  have hj := GlobalZeroSign.of_frame F hq i hi j hzero
  have hjOwner : j=0 ∨ j=2 := hj.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hsource : j=0 → 0<transverse (stateOf C i) := by
    intro hj0
    rcases hj with ⟨_,hy⟩ | ⟨hj2,_⟩
    · exact state_positive_of_tangent C i hy
    · norm_num [hj0] at hj2
  have hm := frame_state_feasible F i j hzero
  have hm' : (stateOf C i).Feasible (stateOf C (next i)) j (delta F.theta i) := by
    simpa [Candidate.phi,hi] using hm
  have hc := zero_charge (stateOf C i) (stateOf C (next i))
    (state_outer_of_kind C (next i) ht.1) (state_negative_of_tangent C (next i) ht.2).le
    hjOwner (by simpa only [frameCap] using (F.delta_small i).le) hm' hsource
  rw [cycleCharge_zero C F.theta i hi hn]
  exact ⟨hc.1,fun hshort => hc.2 (Or.inl hshort)⟩

theorem frame_three_quarters {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (owner : Vertex→Fin 4)
    (hf : ∀i,(forwardAxis (owner i)).Feasible (C.square i) (C.square (next i)))
    (hhigh : ∀i,word i=1 → owner i=2 ∨ owner i=3) :
    3*(Real.pi/2+kappa)≤
      cycleCharge C F.theta E+cycleCharge C F.theta G+cycleCharge C F.theta B := by
  have hE := frame_quarter_charge F E (by norm_num [word,E])
    (by norm_num [word,E,next]) (owner E) (hhigh E (by norm_num [word,E])) (hf E)
  have hG := frame_quarter_charge F G (by norm_num [word,G])
    (by norm_num [word,G,next]) (owner G) (hhigh G (by norm_num [word,G])) (hf G)
  have hB := frame_quarter_charge F B (by norm_num [word,B])
    (by norm_num [word,B,next]) (owner B) (hhigh B (by norm_num [word,B])) (hf B)
  linarith

theorem frame_three_zeros {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (owner : Vertex→Fin 4)
    (hf : ∀i,(forwardAxis (owner i)).Feasible (C.square i) (C.square (next i)))
    (hhigh : ∀i,word i=1 → owner i=2 ∨ owner i=3) :
    3*gammaZero-7/1000<
      cycleCharge C F.theta H+cycleCharge C F.theta A+cycleCharge C F.theta T := by
  have hz (i : Vertex) (hi : word i=0) (hn : word (next i)=1) :=
    frame_zero_charge F i hi hn (owner i) (owner (next i)) (hhigh (next i) hn) (hf i) (hf (next i))
  have hH := hz H (by norm_num [word,H]) (by norm_num [word,H,next])
  have hA := hz A (by norm_num [word,A]) (by norm_num [word,A,next])
  have hT := hz T (by norm_num [word,T]) (by norm_num [word,T,next])
  have hv := (FramePhysicalTransport.candidate_variations F
    (by norm_num [Q0] : Q0∈Icc (5/2:ℝ) Q0)).1
  change positiveVariation F.theta<frameCap at hv
  have hpartial : max (delta F.theta H) 0+max (delta F.theta A) 0+
      max (delta F.theta T) 0<frameCap := by
    have hG := positivePart_nonneg (delta F.theta G)
    have hB := positivePart_nonneg (delta F.theta B)
    have hD := positivePart_nonneg (delta F.theta D)
    have hE := positivePart_nonneg (delta F.theta E)
    simp [positiveVariation,positivePart,Fin.sum_univ_succ] at hv
    dsimp [positivePart,G,B,D,E] at hG hB hD hE
    dsimp [H,A,T]
    linarith
  exact three_zero_charge_bound hpartial hH hA hT

end SquaresInCircles.Eight.GlobalAllHigh
end
end
end
