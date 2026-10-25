module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighCycleComponents

/-!
# The original outer bridge and its fixed dual data

Both the old marker charge and the common augmented charge retain the
one original marker at each endpoint.  All endpoint enclosures below
come from the exact circle and cut equations.  Uncompiled draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge

open FramePair ZeroPrimary GlobalOuterAnchor FrameCircleArc FrameLowArc FrameMidArc

def cap : ℝ := 710/113-6*(8833/10000)
def tau : Fin 4 → ℝ := ![0,0,93/10000,53/2000]
def bonus (i j : Fin 4) : ℝ :=
  max |tau i-tau j| (if i=2 ∧ j=2 then 93/5000 else 0)
def oldCharge (s t : State) (d : ℝ) : ℝ :=
  Real.pi/2+d-unsigned s+unsigned t
def augmentedOld (s t : State) (d : ℝ) : ℝ :=
  oldCharge s t d+(9/50)*frameCost |d|
def charge (s t : State) (d : ℝ) : ℝ :=
  Real.pi/2+d+potential s-potential t
def arcMarker (j : Branch) (b : ℝ) : ℝ := label j (A b) b
def arcPotential (j : Branch) (b : ℝ) : ℝ :=
  kappa*A b+rho*(FrameHighArc.H b-arcMarker j b)
def arcK (j : Branch) (mu b : ℝ) : ℝ := arcPotential j b-mu*arcMarker j b
def K (s : State) (mu : ℝ) : ℝ := potential s-mu*unsigned s

theorem bonus_nonnegative (i j : Fin 4) : 0≤bonus i j :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem a0_precise : (3536439/2500000:ℝ)<a0 ∧ a0<14145757/10000000 := by
  have hs := Real.sq_sqrt (show 0≤Q0-1/4 by norm_num [Q0])
  have hn := Real.sqrt_nonneg (Q0-1/4)
  dsimp [a0,Q0] at *
  constructor <;> nlinarith

theorem c0_precise : (449607/500000:ℝ)<c0 ∧ c0<8992141/10000000 := by
  have hc := c0_circle
  have hp := c0_bounds.1
  norm_num [Q0] at hc
  constructor <;> nlinarith

theorem b1_precise : (811717/2500000:ℝ)<b1 ∧ b1<3246869/10000000 := by
  dsimp [b1]
  constructor <;> linarith [a1_precise.1,a1_precise.2]

theorem b2_precise : (1284917/2500000:ℝ)<b2 ∧ b2<5139669/10000000 := by
  dsimp [b2]
  constructor <;> linarith [a2_bounds.1,a2_bounds.2]

@[simp] theorem arcMarker_low (b : ℝ) : arcMarker .low b=FrameLowArc.L b := by
  simp [arcMarker,label,FrameLowArc.L,FrameLowArc.u,FrameLowArc.v]

@[simp] theorem arcMarker_middle (b : ℝ) : arcMarker .middle b=FrameMidArc.M b := by
  simp [arcMarker,label,FrameMidArc.M,FrameMidArc.p,FrameMidArc.q,FrameMidArc.cM]

@[simp] theorem arcMarker_high (b : ℝ) : arcMarker .high b=FrameHighArc.H b := by
  dsimp [arcMarker,label,FrameHighArc.H,FrameHighArc.k,FrameHighArc.u,FrameHighArc.v]
  ring

@[simp] theorem arcPotential_high (b : ℝ) : arcPotential .high b=kappa*A b := by
  simp [arcPotential]

theorem unsigned_arc (s : State) (hs : s.branch.type≠0) :
    unsigned s=arcMarker s.branch s.b := by
  unfold unsigned arcMarker
  rw [← (state_outer_chart s hs).1]

theorem potential_arc (s : State) (hs : s.branch.type≠0) :
    potential s=arcPotential s.branch s.b := by
  rw [potential,J,unsigned_arc s hs,(state_outer_chart s hs).1]
  dsimp [arcPotential,highExtension,FrameHighArc.H,FrameHighArc.k,
    FrameHighArc.u,FrameHighArc.v]
  ring

theorem K_arc (s : State) (hs : s.branch.type≠0) (mu : ℝ) :
    K s mu=arcK s.branch mu s.b := by
  simp only [K,arcK,potential_arc s hs,unsigned_arc s hs]

theorem marker_outer_bounds (s : State) (hs : s.branch.type≠0) :
    0≤unsigned s ∧ unsigned s≤Real.pi/4 := by
  rw [unsigned_arc s hs]
  cases hj : s.branch with
  | coreSide | coreCorner => simp [hj,Branch.type] at hs
  | low =>
      rw [arcMarker_low]
      have hh := FrameLowArc.L_bounds (state_low_chart s hj).2
      exact ⟨hh.1,by linarith [FrameLowArc.L1_bounds.2,Arithmetic.pi_hand_enclosure.1]⟩
  | middle =>
      rw [arcMarker_middle]
      have hh := FrameMidArc.M_bounds (state_mid_chart s hj).2
      exact ⟨by linarith [FrameMidArc.M_endpoints.1],
        by linarith [FrameMidArc.M_endpoints.2.2.2,Arithmetic.pi_hand_enclosure.1]⟩
  | high =>
      rw [arcMarker_high]
      have hh := FrameHighArc.H_bounds (FrameHighArc.state_high_chart s hj).2
      exact ⟨by linarith [FrameHighArc.H2_bounds.1],hh.2⟩

theorem marker_nonhigh_upper (s : State) (hs : s.branch.type≠0)
    (hh : s.branch≠.high) : unsigned s<57/125 := by
  rw [unsigned_arc s hs]
  cases hj : s.branch with
  | coreSide | coreCorner => simp [hj,Branch.type] at hs
  | low =>
      rw [arcMarker_low]
      linarith [(FrameLowArc.L_bounds (state_low_chart s hj).2).2.2,
        FrameLowArc.L1_bounds.2]
  | middle =>
      rw [arcMarker_middle]
      linarith [(FrameMidArc.M_bounds (state_mid_chart s hj).2).2,
        FrameMidArc.M_endpoints.2.2.2]
  | high => exact (hh hj).elim

theorem marker_nonlow_lower (s : State) (hs : s.branch.type≠0)
    (hl : s.branch≠.low) : (38/125:ℝ)<unsigned s := by
  rw [unsigned_arc s hs]
  cases hj : s.branch with
  | coreSide | coreCorner => simp [hj,Branch.type] at hs
  | low => exact (hl hj).elim
  | middle =>
      rw [arcMarker_middle]
      linarith [(FrameMidArc.M_bounds (state_mid_chart s hj).2).1,
        FrameMidArc.M_endpoints.1]
  | high =>
      rw [arcMarker_high]
      linarith [(FrameHighArc.H_bounds (FrameHighArc.state_high_chart s hj).2).1,
        FrameHighArc.H2_bounds.1]

/-- The fixed nonnegative multipliers only add actual original
projection and cap inequalities. -/
theorem negative_dual (s t : State) {z mu lambda : ℝ}
    (hz : z∈Icc 0 frameCap) (hmu : 0≤ mu) (hlambda : 0≤lambda)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a*Real.cos z-s.b*Real.sin z+t.b)
    (hc : augmentedOld s t (-z)<cap-bonus s.branch.type t.branch.type) :
    (1+mu)*(Real.pi/2-z)-mu*(cap-bonus s.branch.type t.branch.type)+
      lambda*GlobalOuterAnchor.width (-z)+mu*(9/50)*frameCost z+
      (K s mu-lambda*s.a*Real.cos z+lambda*s.b*Real.sin z)+
      (-K t mu-lambda*t.b)≤charge s t (-z) := by
  have hp := mul_le_mul_of_nonneg_left hm hlambda
  have hcap := mul_le_mul_of_nonneg_left hc.le hmu
  rw [augmentedOld,oldCharge,abs_neg,abs_of_nonneg hz.1] at hcap
  dsimp [K,charge]
  nlinarith only [hp,hcap]

end SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge
