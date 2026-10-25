module

public import SquaresInCircles.Eight.Owners.All.HighNegativeOuter

/-!
# Eight squares: the target-potential gap of a zero edge

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
