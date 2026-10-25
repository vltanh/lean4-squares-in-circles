module

public import SquaresInCircles.Eight.Owners.All.HighNegativeOuter
public import SquaresInCircles.Eight.Owners.All.HighPositiveTransfer

/-!
# Eight squares: zero edges from a nonnegative source at nonnegative error

From a source with nonnegative transverse coordinate, both owners of a zero edge into an outer
target give the zero charge `gammaZero` on the whole angle interval (`positive_zero_nonnegative`).
For a high target the primary multiplier is `κ cos z`, and one quadratic completion bounds the
radical on the whole interval (`positive_zero_primary_quadratic`, `positive_zero_high_primary`).
The lower target charts use their uniform potential gap (`positive_zero_lower_target`).
-/

section
/-!
## The target-potential gap of a zero edge

On the lower outer charts the target potential leaves a uniform gap greater than
`zeroGap = 3/50` (`lower_chart_target_gap`); on the high chart the gap is the diagonal one, and on
every outer chart `potential t + kappa * t.b ≤ 2 * kappa * c0` (`target_gap`). These estimates use
the marker of each state and allow both adjacent charts at a cut.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh

open FramePair ZeroPrimary FrameCircleArc FrameLowArc FrameMidArc GlobalOuterAnchor

def zeroU : ℝ := 126119/312500
def zeroV : ℝ := 2580127/5000000
def zeroGap : ℝ := 3/50
def highConstant : ℝ := Real.pi/4+(89293/500000)*c0
def zeroCharge (s t : State) (d : ℝ) : ℝ := d+kappa*transverse s-potential t

theorem potential_upper (t : State) :
    potential t≤zeroU*t.a-zeroV*t.b+rho*highConstant := by
  have hm := GlobalOuterAnchor.marker_lower t
  dsimp [potential,J,highExtension,zeroU,zeroV,highConstant,kappa,rho,
    GlobalOuterAnchor.k] at *
  linarith

theorem lower_chart_transverse (t : State) (ht : t.branch=.low ∨ t.branch=.middle) :
    t.b≤13/25 := by
  rcases ht with ht | ht
  · have hb := (state_low_chart t ht).2.2
    linarith [b1_bounds.2]
  · have hb := (state_mid_chart t ht).2.2
    linarith [b2_bounds.2]

theorem zero_short_endpoint :
    (119/100:ℝ)<A (13/25) ∧ A (13/25)<6/5 := by
  have hb : (13/25:ℝ)∈Icc 0 c0 := ⟨by norm_num,by linarith [c0_bounds.1]⟩
  have hc := A_circle hb
  have hp := A_shift_pos hb
  norm_num [Q0] at hc
  constructor <;> nlinarith

theorem zero_short_slope {b : ℝ} (hb : b∈Icc 0 (13/25:ℝ)) :
    (b+1/2)/(A b+1/2)≤102/169 := by
  have hcap : (13/25:ℝ)≤c0 := by linarith [c0_bounds.1]
  have hdom : b∈Icc 0 c0 := ⟨hb.1,hb.2.trans hcap⟩
  have hm := A_antitone hdom ⟨by norm_num,hcap⟩ hb.2
  apply (div_le_iff₀ (A_shift_pos hdom)).2
  linarith [zero_short_endpoint.1,hb.2]

theorem zero_short_linear_monotone {p q : ℝ}
    (hp : 0≤p) (hq : p*(102/169)≤q) :
    MonotoneOn (linear p q) (Icc 0 (13/25:ℝ)) := by
  have hcap : (13/25:ℝ)≤c0 := by linarith [c0_bounds.1]
  apply monoOn_of_hasDeriv_nonneg
  · intro b hb
    exact (linear_hasDerivAt ⟨hb.1,hb.2.trans hcap⟩ p q).continuousAt.continuousWithinAt
  · intro b hb
    exact linear_hasDerivAt ⟨hb.1.le,hb.2.le.trans hcap⟩ p q
  · intro b hb
    have hh := mul_le_mul_of_nonneg_left (zero_short_slope (Ioo_subset_Icc_self hb)) hp
    dsimp [Ad]
    rw [neg_div]
    linarith

theorem lower_chart_linear_upper (t : State) (ht : t.branch=.low ∨ t.branch=.middle)
    {p q : ℝ} (hp : 0≤p) (hq : p*(102/169)≤q) :
    p*t.a+q*t.b≤(6/5)*p+(13/25)*q := by
  have htOuter : t.branch.type≠0 := by
    rcases ht with ht | ht <;> simp [ht,Branch.type]
  have hchart := state_outer_chart t htOuter
  have hm := zero_short_linear_monotone hp hq
    (show t.b∈Icc 0 (13/25:ℝ) from ⟨t.b_nonneg,lower_chart_transverse t ht⟩)
    (by norm_num : (13/25:ℝ)∈Icc 0 (13/25:ℝ)) (lower_chart_transverse t ht)
  have hA := mul_le_mul_of_nonneg_left zero_short_endpoint.2.le hp
  dsimp [linear] at hm
  rw [← hchart.1] at hm
  linarith

/-- On the lower outer charts the target potential leaves a gap greater than `zeroGap = 3/50`, a
reserve slightly below the value at the endpoint that keeps the polynomials of the zero charge
small. -/
theorem lower_chart_target_gap (t : State) (ht : t.branch=.low ∨ t.branch=.middle) :
    zeroGap<2*kappa*c0-potential t-kappa*t.b := by
  have hp := potential_upper t
  have hs := lower_chart_linear_upper t ht
    (by norm_num [zeroU] : 0≤zeroU)
    (by norm_num [zeroU,zeroV,kappa] : zeroU*(102/169)≤kappa-zeroV)
  have hpi := Arithmetic.two_pi_lt_710_over_113
  have hc := diagonal_bounds.1
  dsimp [zeroGap,zeroU,zeroV,highConstant,kappa,rho] at *
  nlinarith only [hp,hs,hpi,hc]

theorem target_gap (t : State) (ht : t.branch.type≠0) :
    potential t+kappa*t.b≤2*kappa*c0 := by
  cases hbr : t.branch with
  | coreSide | coreCorner => simp [hbr,Branch.type] at ht
  | low =>
      have hh := lower_chart_target_gap t (Or.inl hbr)
      dsimp [zeroGap] at hh
      linarith
  | middle =>
      have hh := lower_chart_target_gap t (Or.inr hbr)
      dsimp [zeroGap] at hh
      linarith
  | high =>
      have hh := sorted_diagonal_support t (f:=1) (g:=1) (by norm_num) le_rfl
      rw [potential_high t hbr]
      dsimp [kappa]
      nlinarith only [hh]

end SquaresInCircles.Eight.GlobalAllHigh
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh

open FramePair FrameCircleArc GlobalZeroSign GlobalOuterAnchor

theorem circle_product_support (s : State) {f g K : ℝ}
    (hK : 0≤K) (hsq : Q0*(f^2+g^2)≤K^2) :
    f*s.a+g*s.b≤K-(f+g)/2 := by
  have hc := state_circle s
  have hmul := mul_le_mul_of_nonneg_left hc (show 0≤f^2+g^2 by positivity)
  have hid : (f*(s.a+1/2)+g*(s.b+1/2))^2+
      (f*(s.b+1/2)-g*(s.a+1/2))^2=
      (f^2+g^2)*((s.a+1/2)^2+(s.b+1/2)^2) := by ring
  have hdot : f*(s.a+1/2)+g*(s.b+1/2)≤K := by
    nlinarith [sq_nonneg (f*(s.b+1/2)-g*(s.a+1/2))]
  linarith

def zeroRoughScalar (z : ℝ) : ℝ :=
  z-kappa*(coreU*Real.sin z+(1-Real.cos z)/2)

theorem zero_rough_scalar {z : ℝ} (hz : z∈Icc 0 frameCap) :
    -(3/50)*z≤zeroRoughScalar z := by
  have hs := sin_upper_five hz.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := z)
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  norm_num [frameCap] at h2
  have h3 := pow_nonneg hz.1 3
  have h5 : z^5≤(49/100)*z^3 := by
    have hh := mul_le_mul_of_nonneg_left h2 h3
    nlinarith only [hh]
  have hpoly : (11/200)*z-(13/50)*z^2+(3/20)*z^3≤zeroRoughScalar z := by
    dsimp [zeroRoughScalar,kappa,coreU]
    nlinarith only [hs,hc,h5,hz.1,sq_nonneg z,h3]
  have hpositive := positive_quadratic (z:=z)
    (show (0:ℝ)<3/20 by norm_num)
    (show (-(13/50:ℝ))^2<4*(3/20)*(23/200) by norm_num)
  have hh := mul_nonneg hz.1 hpositive.le
  nlinarith only [hpoly,hh]

theorem positive_zero_lower_target (s t : State)
    (ht : t.branch=.low ∨ t.branch=.middle) (hy : 0≤transverse s)
    {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width z≤transverse s+t.a*Real.sin z+t.b*Real.cos z ∨
      GlobalOuterAnchor.width z≤ s.a*Real.sin z+transverse s*Real.cos z+t.b) :
    gammaZero<zeroCharge s t z := by
  have tr := transport_trig hz
  have htarget := lower_chart_target_gap t ht
  have hrough := zero_rough_scalar hz
  have hbound : zeroGap+zeroRoughScalar z≤zeroCharge s t z-gammaZero := by
    rcases hm with hm | hm
    · have hA := mul_nonneg
        (show 0≤(283/200:ℝ)-t.a by linarith [(ZeroPrimary.coordinates t).2.1]) tr.2.2.1
      have hB := mul_nonneg t.b_nonneg (sub_nonneg.mpr tr.2.1)
      simp only [GlobalOuterAnchor.width,abs_of_nonneg tr.2.2.1] at hm
      dsimp [zeroCharge,zeroRoughScalar,gammaZero,kappa,coreU] at ⊢
      dsimp [kappa] at htarget
      nlinarith only [hm,htarget,hA,hB]
    · have ha := mul_nonneg
        (show 0≤(283/200:ℝ)-s.a by linarith [(ZeroPrimary.coordinates s).2.1]) tr.2.2.1
      have hyc := mul_nonneg hy (sub_nonneg.mpr tr.2.1)
      simp only [GlobalOuterAnchor.width,abs_of_nonneg tr.2.2.1] at hm
      dsimp [zeroCharge,zeroRoughScalar,gammaZero,kappa,coreU] at ⊢
      dsimp [kappa] at htarget
      nlinarith only [hm,htarget,ha,hyc]
  dsimp [zeroGap,frameCap] at *
  linarith [hz.2]

theorem positive_zero_secondary_support (t : State) {z : ℝ}
    (hz : z∈Icc 0 frameCap) :
    (1+Real.sin z)*t.a+Real.cos z*t.b≤
      (2*c0+1)*(1+Real.sin z/2)-(1+Real.sin z+Real.cos z)/2 := by
  have tr := transport_trig hz
  have hdiag : (2*c0+1)^2=2*Q0 := by nlinarith [c0_circle]
  have hK : 0≤(2*c0+1)*(1+Real.sin z/2) := by
    exact mul_nonneg (by linarith [c0_bounds.1]) (by linarith [tr.2.2.1])
  apply circle_product_support t hK
  have hscaled := congrArg (fun r : ℝ => r*(1+Real.sin z/2)^2) hdiag
  have hunit := congrArg (fun r : ℝ => Q0*r) (Real.sin_sq_add_cos_sq z)
  have hreserve := mul_nonneg (show 0≤Q0 by norm_num [Q0]) (sq_nonneg (Real.sin z))
  nlinarith only [hscaled,hunit,hreserve]

theorem positive_zero_secondary_scalar {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (91/400)*z≤z+kappa*(Real.cos z-1-(c0-1/2)*Real.sin z) := by
  have tr := transport_trig hz
  have hsin := Real.sin_le hz.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x := z)
  have hdiag := mul_nonneg
    (show 0≤(2/5:ℝ)-(c0-1/2) by linarith [diagonal_bounds.2]) tr.2.2.1
  have h2 := mul_nonneg hz.1 (sub_nonneg.mpr hz.2)
  dsimp [kappa,frameCap] at *
  nlinarith only [hsin,hcos,hdiag,h2]

theorem positive_zero_high_secondary (s t : State) (ht : t.branch=.high)
    {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width z≤transverse s+t.a*Real.sin z+t.b*Real.cos z) :
    gammaZero≤zeroCharge s t z := by
  have hsupport := positive_zero_secondary_support t hz
  have hscalar := positive_zero_secondary_scalar hz
  have hsin := (transport_trig hz).2.2.1
  simp only [GlobalOuterAnchor.width,abs_of_nonneg hsin] at hm
  rw [zeroCharge,potential_high t ht]
  dsimp [gammaZero,kappa] at *
  nlinarith only [hm,hsupport,hscalar,hz.1]

def zeroPositivePrimaryScalar (z : ℝ) : ℝ := z+kappa*
  (Real.cos z-1-coreU*Real.sin z*Real.cos z+(c0-1/2)/2*(Real.sin z)^2)
def zeroPositivePrimaryPolynomial (z : ℝ) : ℝ :=
  (1-kappa*coreU)*z+kappa*(etaLower-1)/2*z^2+(2*kappa*coreU/3)*z^3+
    kappa*(1/24-etaLower/6)*z^4-(2*kappa*coreU/15)*z^5-kappa/720*z^6

theorem positive_zero_primary_polynomial_transfer {z : ℝ} (hz : z∈Icc 0 frameCap) :
    zeroPositivePrimaryPolynomial z≤zeroPositivePrimaryScalar z := by
  have hcos := cos_lower_six hz.1
  have hsin := sin_upper_five (show 0≤2*z by linarith [hz.1])
  rw [Real.sin_two_mul] at hsin
  have hcos2 := cos_upper_four (show 0≤2*z by linarith [hz.1])
  rw [Real.cos_two_mul] at hcos2
  have hsquare : z^2-z^4/3≤(Real.sin z)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq z]
  have heta := mul_nonneg
    (show 0≤c0-1/2-etaLower by dsimp [etaLower]; linarith [diagonal_bounds.1])
    (sq_nonneg (Real.sin z))
  dsimp [zeroPositivePrimaryPolynomial,zeroPositivePrimaryScalar,kappa,coreU,etaLower] at *
  nlinarith only [hcos,hsin,hsquare,heta]

theorem positive_zero_primary_quadratic {z : ℝ} (hz : z∈Icc 0 frameCap) :
    z*((23/400)-(31/100)*z+(27/50)*z^2)≤zeroPositivePrimaryPolynomial z := by
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  have h3U := pow_le_pow_left₀ hz.1 hz.2 3
  norm_num [frameCap] at h2 h3U
  have h3 := pow_nonneg hz.1 3
  have h4 : z^4≤(7/10)*z^3 := by
    have hh := mul_le_mul_of_nonneg_left hz.2 h3
    dsimp [frameCap] at hh
    nlinarith only [hh]
  have h5 : z^5≤(49/100)*z^3 := by
    have hh := mul_le_mul_of_nonneg_left h2 h3
    nlinarith only [hh]
  have h6 : z^6≤(343/1000)*z^3 := by
    have hh := mul_le_mul_of_nonneg_left h3U h3
    nlinarith only [hh]
  dsimp [zeroPositivePrimaryPolynomial,kappa,coreU,etaLower]
  nlinarith only [h4,h5,h6,hz.1,sq_nonneg z,h3]

theorem positive_zero_primary_scalar {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0≤zeroPositivePrimaryScalar z := by
  have hpositive := positive_quadratic (z:=z)
    (show (0:ℝ)<27/50 by norm_num)
    (show (-(31/100:ℝ))^2<4*(27/50)*(23/400) by norm_num)
  have hprod := mul_nonneg hz.1 hpositive.le
  have hpoly := positive_zero_primary_quadratic hz
  have htransfer := positive_zero_primary_polynomial_transfer hz
  nlinarith only [hprod,hpoly,htransfer]

theorem positive_zero_primary_support (t : State) {z : ℝ}
    (_hz : z∈Icc 0 frameCap) :
    t.a+Real.cos z*t.b≤
      (2*c0+1)*(1-(Real.sin z)^2/4)-(1+Real.cos z)/2 := by
  have hu := Real.sin_sq_add_cos_sq z
  have hdiag : (2*c0+1)^2=2*Q0 := by nlinarith [c0_circle]
  have hK : 0≤(2*c0+1)*(1-(Real.sin z)^2/4) := by
    exact mul_nonneg (by linarith [c0_bounds.1])
      (by nlinarith [sq_nonneg (Real.cos z)])
  have hscaled := congrArg (fun r : ℝ => r*(1-(Real.sin z)^2/4)^2) hdiag
  have hunit := congrArg (fun r : ℝ => Q0*r) hu
  have hreserve := mul_nonneg (show 0≤Q0 by norm_num [Q0]) (sq_nonneg ((Real.sin z)^2))
  have hnorm : Q0*((1:ℝ)^2+(Real.cos z)^2)≤
      ((2*c0+1)*(1-(Real.sin z)^2/4))^2 := by
    nlinarith only [hscaled,hunit,hreserve]
  simpa only [one_mul] using circle_product_support t (f:=1) (g:=Real.cos z) hK hnorm

/-- A primary witness into a high target from a source with nonnegative transverse coordinate
gives the zero charge `gammaZero`. The multiplier is `κ cos z`, and the source coefficient
`κ sin² z` is nonnegative. -/
theorem positive_zero_high_primary (s t : State) (ht : t.branch=.high)
    (hy : 0≤transverse s) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width z≤ s.a*Real.sin z+transverse s*Real.cos z+t.b) :
    gammaZero≤zeroCharge s t z := by
  have tr := transport_trig hz
  have hc : 0≤Real.cos z := by linarith [tr.1]
  have hproj := mul_le_mul_of_nonneg_left hm hc
  have hcap := mul_nonneg
    (show 0≤(283/200:ℝ)-s.a by linarith [(ZeroPrimary.coordinates s).2.1])
    (mul_nonneg tr.2.2.1 hc)
  have hyc := mul_nonneg hy (show 0≤1-(Real.cos z)^2 by
    nlinarith [Real.sin_sq_add_cos_sq z,sq_nonneg (Real.sin z)])
  have hsupport := positive_zero_primary_support t hz
  have hscalar := positive_zero_primary_scalar hz
  have hunit := Real.sin_sq_add_cos_sq z
  have hscaled := congrArg (fun r : ℝ => kappa*r/2) hunit
  simp only [GlobalOuterAnchor.width,abs_of_nonneg tr.2.2.1] at hproj
  rw [zeroCharge,potential_high t ht]
  dsimp [gammaZero,zeroPositivePrimaryScalar,kappa,coreU] at *
  nlinarith only [hproj,hcap,hyc,hsupport,hscalar,hscaled]

theorem positive_zero_nonnegative (s t : State) (ht : t.branch.type≠0)
    (hy : 0≤transverse s) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width z≤transverse s+t.a*Real.sin z+t.b*Real.cos z ∨
      GlobalOuterAnchor.width z≤ s.a*Real.sin z+transverse s*Real.cos z+t.b) :
    gammaZero≤zeroCharge s t z := by
  cases hbr : t.branch with
  | coreSide | coreCorner => simp [hbr,Branch.type] at ht
  | low => exact (positive_zero_lower_target s t (Or.inl hbr) hy hz hm).le
  | middle => exact (positive_zero_lower_target s t (Or.inr hbr) hy hz hm).le
  | high =>
      rcases hm with hm | hm
      · exact positive_zero_high_secondary s t hbr hz hm
      · exact positive_zero_high_primary s t hbr hy hz hm

end SquaresInCircles.Eight.GlobalAllHigh
end
end
end
