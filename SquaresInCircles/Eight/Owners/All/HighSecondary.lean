module

public import SquaresInCircles.Eight.Owners.Outer.AnchorBridge

/-!
# Eight squares: the quarter charge of a high secondary

A weak projection of owner `2` from an outer source makes the quarter charge at least `kappa`,
strictly at nonzero error (`secondary_charge`), for every sign and radial kind of the target; the
source keeps its marker correction. Negative errors use either the quadratic reserve on the whole
arc (`secondaryNegative_small`) or the concave derivative on the whole angle interval
(`secondaryNegative_large`).
-/

section
/-!
## The common outer potential of the all-high branch

The potential of a state is `potential s = kappa * s.a + rho * J s`, where the correction
`J s = highExtension s.a s.b - unsigned s` is the extension of the high-chart formula minus the
marker of the state. On the outer charts `J` is nonnegative and vanishes exactly on the high chart
(`J_nonnegative`, `J_eq_zero_iff`); its strict bounds on the two lower charts hold on the whole
arcs (`lowJ_below_original`, `midJ_below_original`), and at a junction of charts with either
marker. The same potential is used at every occurrence of a vertex.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh

open FramePair ZeroPrimary GlobalZeroSign GlobalOuterAnchor
open FrameCircleArc FrameLowArc FrameMidArc

def kappa : ℝ := 103/100
def rho : ℝ := 11/10
def highExtension (a b : ℝ) : ℝ :=
  Real.pi/4-(8898/15625)*(a-c0)+(195443/500000)*(b-c0)
def J (s : State) : ℝ := highExtension s.a s.b-unsigned s
def potential (s : State) : ℝ := kappa*s.a+rho*J s
def gammaZero : ℝ := kappa*(1-2*c0)

def lowA : ℝ := 973347/1000000
def lowB : ℝ := 698179/1000000
def midA : ℝ := 2059065/1000000
def midB : ℝ := 1189333/1000000
def lowK : ℝ := (314159/100000)/4+(178586/1000000)*(89921/100000)+
  (403875/1000000)*(141457/100000)+(lowA+lowB)/2
def midK : ℝ := (314159/100000)/4+(178586/1000000)*(89921/100000)+
  2143075/1000000+(midA+midB)/2
def lowJ (b : ℝ) : ℝ := lowK-lowA*(A b+1/2)-lowB*(b+1/2)
def midJ (b : ℝ) : ℝ := midK-midA*(A b+1/2)-midB*(b+1/2)

def quadraticR : ℝ := 1151/2400
def quadraticS : ℝ := 7/60
def quadraticD (s : State) : ℝ :=
  quadraticR*(s.a-1/2)-quadraticS*(s.b+1/2)
def primaryThreshold : ℝ := 1/kappa-1/2

@[simp] theorem J_flip (s : State) : J s.flip=J s := rfl
@[simp] theorem potential_flip (s : State) : potential s.flip=potential s := rfl

theorem diagonal_bounds : (89921/100000:ℝ)<c0 ∧ c0<44961/50000 := by
  exact ⟨by linarith [FrameHighArc.diagonal_bounds.1],
    by linarith [FrameHighArc.diagonal_bounds.2]⟩

theorem lowJ_derivative {b : ℝ} (hb : b∈Icc 0 c0) :
    HasDerivAt lowJ (-lowA*Ad b-lowB) b := by
  have h := ((hasDerivAt_const b lowK).sub
    (((A_hasDerivAt hb).add_const (1/2)).const_mul lowA)).sub
    (((hasDerivAt_id b).add_const (1/2)).const_mul lowB)
  convert h using 1
  · funext x
    simp only [lowJ,Pi.sub_apply,id]
  · ring

theorem midJ_derivative {b : ℝ} (hb : b∈Icc 0 c0) :
    HasDerivAt midJ (-midA*Ad b-midB) b := by
  have h := ((hasDerivAt_const b midK).sub
    (((A_hasDerivAt hb).add_const (1/2)).const_mul midA)).sub
    (((hasDerivAt_id b).add_const (1/2)).const_mul midB)
  convert h using 1
  · funext x
    simp only [midJ,Pi.sub_apply,id]
  · ring

theorem lowJ_b1 : (13/500:ℝ)<lowJ b1 := by
  rw [lowJ,A_b1]
  have ha : a1<(12988/10000:ℝ) := by linarith [a1_precise.2]
  have hb : b1<(3247/10000:ℝ) := by dsimp [b1]; linarith [a1_precise.2]
  dsimp [lowK,lowA,lowB]
  linarith

theorem lowJ_zero : (351/2500:ℝ)<lowJ 0 := by
  rw [lowJ,A_zero]
  dsimp [lowK,lowA,lowB]
  linarith [a0_bounds.2]

theorem lowJ_antitone : AntitoneOn lowJ (Icc 0 b1) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro b hb
    exact (lowJ_derivative ⟨hb.1,hb.2.trans b1_mem.2⟩).continuousAt.continuousWithinAt
  · intro b hb
    exact lowJ_derivative ⟨hb.1.le,hb.2.le.trans b1_mem.2⟩
  · intro b hb
    have hh := (slope_bounds (Ioo_subset_Icc_self hb)).2
    have he : Ad b= -FrameLowArc.slope b := by
      simp only [Ad,FrameLowArc.slope,neg_div]
    rw [he]
    dsimp [lowA,lowB]
    linarith

theorem lowJ_lower {b : ℝ} (hb : b∈Icc 0 b1) : (13/500:ℝ)<lowJ b :=
  lowJ_b1.trans_le (lowJ_antitone hb ⟨b1_mem.1,le_rfl⟩ hb.2)

theorem midJ_positive {b : ℝ} (hb : b∈Icc 0 c0) : 0< midJ b := by
  have hc := A_circle hb
  have hx := A_shift_pos hb
  have ht : 0≤b+1/2 := by linarith [hb.1]
  have hC : 0< midK := by norm_num [midK,midA,midB]
  have hreserve : Q0*(midA^2+midB^2)< midK^2 := by
    norm_num [midK,midA,midB,Q0]
  have hid : (midA*(A b+1/2)+midB*(b+1/2))^2+
      (midA*(b+1/2)-midB*(A b+1/2))^2=Q0*(midA^2+midB^2) := by
    rw [← hc]
    ring
  have hsign : 0≤ midA*(A b+1/2)+midB*(b+1/2) := by
    dsimp [midA,midB]
    positivity
  dsimp [midJ]
  nlinarith [sq_nonneg (midA*(b+1/2)-midB*(A b+1/2))]

theorem short_root_bounds :
    (449/250:ℝ)<A (33/100)+1/2 ∧ A (33/100)+1/2<1797/1000 := by
  have hb : (33/100:ℝ)∈Icc 0 c0 := ⟨by norm_num,by linarith [c0_bounds.1]⟩
  have hc := A_circle hb
  have hx := A_shift_pos hb
  norm_num [Q0] at hc
  constructor <;> nlinarith

theorem midJ_antitone_short : AntitoneOn midJ (Icc 0 (33/100:ℝ)) := by
  have hcap : (33/100:ℝ)≤c0 := by linarith [c0_bounds.1]
  apply antiOn_of_hasDeriv_nonpos
  · intro b hb
    exact (midJ_derivative ⟨hb.1,hb.2.trans hcap⟩).continuousAt.continuousWithinAt
  · intro b hb
    exact midJ_derivative ⟨hb.1.le,hb.2.le.trans hcap⟩
  · intro b hb
    have hdom : b∈Icc 0 c0 := ⟨hb.1.le,hb.2.le.trans hcap⟩
    have hlo := A_antitone hdom ⟨by norm_num,hcap⟩ hb.2.le
    have hx : 0<A b+1/2 := A_shift_pos hdom
    have hratio : midA*((b+1/2)/(A b+1/2)) < midB := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hx).2
      dsimp [midA,midB]
      linarith [short_root_bounds.1,hb.2]
    have he : Ad b= -((b+1/2)/(A b+1/2)) := by
      simp only [Ad,neg_div]
    rw [he]
    linarith

theorem midJ_short {b : ℝ} (hb : b∈Icc 0 (33/100:ℝ)) :
    (1/40:ℝ)< midJ b := by
  have hm := midJ_antitone_short hb ⟨by norm_num,le_rfl⟩ hb.2
  have he : (1/40:ℝ)< midJ (33/100) := by
    dsimp [midJ,midK,midA,midB]
    linarith [short_root_bounds.2]
  exact he.trans_le hm

theorem lowJ_below_original (s : State) (hs : s.branch=.low) : lowJ s.b<J s := by
  have ha := (state_low_chart s hs).1
  dsimp [J,highExtension,unsigned]
  rw [hs]
  dsimp [FramePair.label,lowJ,lowK,lowA,lowB]
  rw [ha]
  linarith [diagonal_bounds.1,a0_bounds.1,Arithmetic.pi_hand_enclosure.1]

theorem midJ_below_original (s : State) (hs : s.branch=.middle) : midJ s.b<J s := by
  have ha := (state_mid_chart s hs).1
  dsimp [J,highExtension,unsigned]
  rw [hs]
  dsimp [FramePair.label,midJ,midK,midA,midB]
  rw [ha]
  linarith [diagonal_bounds.1,Arithmetic.pi_hand_enclosure.1]

theorem J_high (s : State) (hs : s.branch=.high) : J s=0 := by
  simp [J,highExtension,unsigned,hs,FramePair.label]

theorem J_nonnegative (s : State) (hs : s.branch.type≠0) : 0≤J s := by
  cases hbr : s.branch with
  | coreSide | coreCorner => simp [hbr,Branch.type] at hs
  | low =>
      have hh := (lowJ_lower (state_low_chart s hbr).2).trans (lowJ_below_original s hbr)
      linarith
  | middle =>
      have hc := state_outer_chart s hs
      exact ((midJ_positive hc.2).trans (midJ_below_original s hbr)).le
  | high => rw [J_high s hbr]

theorem J_small_transverse (s : State) (hs : s.branch.type≠0) (hb : s.b≤33/100) :
    (1/40:ℝ)<J s := by
  cases hbr : s.branch with
  | coreSide | coreCorner => simp [hbr,Branch.type] at hs
  | low =>
      have hh := (lowJ_lower (state_low_chart s hbr).2).trans (lowJ_below_original s hbr)
      linarith
  | middle =>
      exact (midJ_short ⟨s.b_nonneg,hb⟩).trans (midJ_below_original s hbr)
  | high =>
      have hh := (FrameHighArc.state_high_chart s hbr).2.1
      linarith [b2_bounds.1]

theorem J_eq_zero_iff (s : State) (hs : s.branch.type≠0) : J s=0 ↔ s.branch=.high := by
  constructor
  · intro hJ
    cases hbr : s.branch with
    | coreSide | coreCorner => simp [hbr,Branch.type] at hs
    | low =>
        have hh := (lowJ_lower (state_low_chart s hbr).2).trans (lowJ_below_original s hbr)
        linarith
    | middle =>
        have hc := state_outer_chart s hs
        have hh := (midJ_positive hc.2).trans (midJ_below_original s hbr)
        linarith
    | high => rfl
  · exact J_high s

theorem potential_high (s : State) (hs : s.branch=.high) : potential s=kappa*s.a := by
  rw [potential,J_high s hs]
  ring

end SquaresInCircles.Eight.GlobalAllHigh
end
end
end

section
/-!
## The outer bridge and its dual data

The marker charge `unsignedCharge s t d = π/2 + d - unsigned s + unsigned t`, its augmentation
`augmentedUnsigned` by `(9/50) frameCost |d|`, and the charge `charge` of the common potential all
use the marker of each endpoint state. The enclosures of the endpoints `a0`, `c0`, `b1`, `b2` and
of the arc markers come from the circle and cut equations; `negative_dual` adds a weak projection
and the cycle cap with nonnegative multipliers.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh.Bridge

open FramePair ZeroPrimary GlobalOuterAnchor FrameCircleArc FrameLowArc FrameMidArc

def cap : ℝ := 710/113-6*(8833/10000)
def tau : Fin 4 → ℝ := ![0,0,93/10000,53/2000]
def bonus (i j : Fin 4) : ℝ :=
  max |tau i-tau j| (if i=2 ∧ j=2 then 93/5000 else 0)
def unsignedCharge (s t : State) (d : ℝ) : ℝ :=
  Real.pi/2+d-unsigned s+unsigned t
def augmentedUnsigned (s t : State) (d : ℝ) : ℝ :=
  unsignedCharge s t d+(9/50)*frameCost |d|
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

/-- The charge at error `-z` is at least the combination of the weak projection `hm`, with
multiplier `lambda`, and the cycle cap `hc`, with multiplier `mu`. -/
theorem negative_dual (s t : State) {z mu lambda : ℝ}
    (hz : z∈Icc 0 frameCap) (hmu : 0≤ mu) (hlambda : 0≤lambda)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a*Real.cos z-s.b*Real.sin z+t.b)
    (hc : augmentedUnsigned s t (-z)<cap-bonus s.branch.type t.branch.type) :
    (1+mu)*(Real.pi/2-z)-mu*(cap-bonus s.branch.type t.branch.type)+
      lambda*GlobalOuterAnchor.width (-z)+mu*(9/50)*frameCost z+
      (K s mu-lambda*s.a*Real.cos z+lambda*s.b*Real.sin z)+
      (-K t mu-lambda*t.b)≤charge s t (-z) := by
  have hp := mul_le_mul_of_nonneg_left hm hlambda
  have hcap := mul_le_mul_of_nonneg_left hc.le hmu
  rw [augmentedUnsigned,unsignedCharge,abs_neg,abs_of_nonneg hz.1] at hcap
  dsimp [K,charge]
  nlinarith only [hp,hcap]

end SquaresInCircles.Eight.GlobalAllHigh.Bridge
end
end
end

section
/-!
## The whole-arc quadratic reserve in the all-high correction

The low-arc reserve is concave.  Its curvature sign is proved directly
after multiplying by the positive cube of the actual circle radical;
one positive cubic bounds the resulting expression on the entire arc.
The middle reserve is concave up to its intrinsic primary threshold.
Both proofs retain the original marker and actual circle.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh

open FramePair FrameCircleArc FrameLowArc FrameMidArc

def arcD (b : ℝ) : ℝ := quadraticR*(A b-1/2)-quadraticS*(b+1/2)
def lowAlpha : ℝ := 4*kappa*rho*quadraticR*(lowK+lowA)
def lowDelta : ℝ := 4*kappa*rho*(lowA*quadraticS-lowB*quadraticR)
def lowGamma : ℝ := 4*kappa*rho*(lowA*quadraticR+lowB*quadraticS)-kappa^2
def lowNu : ℝ := 4*kappa*rho*(-lowK*quadraticS+lowB*quadraticR)+2*kappa
def lowOmega : ℝ := 4*kappa*rho*(-lowK*quadraticR-lowA*quadraticR*Q0)-1

def lowReserve (b : ℝ) : ℝ :=
  lowAlpha*(A b+1/2)+lowDelta*(A b+1/2)*(b+1/2)+
    lowGamma*(b+1/2)^2+lowNu*(b+1/2)+lowOmega
def lowReserveD (b : ℝ) : ℝ :=
  lowAlpha*Ad b+lowDelta*(Ad b*(b+1/2)+(A b+1/2))+2*lowGamma*(b+1/2)+lowNu
def lowReserveDD (b : ℝ) : ℝ :=
  lowAlpha*FrameCircleArc.Add b+lowDelta*(FrameCircleArc.Add b*(b+1/2)+2*Ad b)+2*lowGamma

theorem lowReserve_identity {b : ℝ} (hb : b∈Icc 0 c0) :
    lowReserve b=4*kappa*rho*lowJ b*arcD b-(1-kappa*(b+1/2))^2 := by
  have hc := A_circle hb
  dsimp [lowReserve,lowAlpha,lowDelta,lowGamma,lowNu,lowOmega,lowJ,arcD]
  linear_combination 4*kappa*rho*lowA*quadraticR*hc

theorem lowReserve_derivative {b : ℝ} (hb : b∈Icc 0 c0) :
    HasDerivAt lowReserve (lowReserveD b) b := by
  have hx := (A_hasDerivAt hb).add_const (1/2)
  have ht := (hasDerivAt_id b).add_const (1/2)
  have h := ((((hx.const_mul lowAlpha).add ((hx.mul ht).const_mul lowDelta)).add
    ((ht.pow 2).const_mul lowGamma)).add (ht.const_mul lowNu)).add_const lowOmega
  convert h using 1
  · funext x
    simp only [lowReserve,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,id]
    ring
  · simp only [lowReserveD,id]
    ring

theorem lowReserve_second_derivative {b : ℝ} (hb : b∈Icc 0 c0) :
    HasDerivAt lowReserveD (lowReserveDD b) b := by
  have hd := Ad_hasDerivAt hb
  have hx := (A_hasDerivAt hb).add_const (1/2)
  have ht := (hasDerivAt_id b).add_const (1/2)
  have h := (((hd.const_mul lowAlpha).add
    (((hd.mul ht).add hx).const_mul lowDelta)).add
    (ht.const_mul (2*lowGamma))).add_const lowNu
  convert h using 1
  · funext x
    simp only [lowReserveD,Pi.add_apply,Pi.mul_apply,id]
  · simp only [lowReserveDD,id]
    ring

theorem low_coefficients :
    (36/5:ℝ)<lowAlpha ∧ -(101/100:ℝ)<lowDelta ∧ lowDelta<0 ∧
      2*lowGamma<(29/10:ℝ) := by
  norm_num [lowAlpha,lowDelta,lowGamma,kappa,rho,quadraticR,quadraticS,
    lowK,lowA,lowB]

/-- Keeping the circle relation in the denominator yields this one
positive cubic; no partition of the original low arc is necessary. -/
theorem low_curvature_polynomial {t : ℝ} (ht : 1/2≤t) :
    0<(36/5)*Q0-(101/100)*t*(3*Q0-2*t^2)-
      (29/10)*(383/200)*(Q0-t^2) := by
  have hw : 0≤t-1/2 := by linarith
  have h3 := pow_nonneg hw 3
  have hs := sq_nonneg (t-1/2-24/85)
  dsimp [Q0]
  nlinarith only [h3,hs,sq_nonneg (t-1/2),hw]

theorem lowReserve_second_negative {b : ℝ} (hb : b∈Icc 0 b1) :
    lowReserveDD b<0 := by
  have hdom : b∈Icc 0 c0 := ⟨hb.1,hb.2.trans b1_mem.2⟩
  obtain ⟨x,hxdef⟩ : ∃ x,x=A b+1/2 := ⟨_,rfl⟩
  obtain ⟨t,htdef⟩ : ∃ t,t=b+1/2 := ⟨_,rfl⟩
  have hx : 0<x := hxdef ▸ A_shift_pos hdom
  have hx3 : 0<x^3 := pow_pos hx 3
  have hcircle : x^2+t^2=Q0 := by rw [hxdef,htdef]; exact A_circle hdom
  have hxu : x<383/200 := by
    have hh := (A_bounds hdom).2
    rw [hxdef]
    linarith [a0_bounds.2]
  have ht : 1/2≤t := by rw [htdef]; linarith [hb.1]
  have htu : t<8247/10000 := by
    rw [htdef]
    have hb1 : b1<3247/10000 := by dsimp [b1]; linarith [a1_precise.2]
    linarith [hb.2]
  have ht2 := pow_le_pow_left₀ (by linarith : 0≤t) htu.le 2
  have hfactor : 0<t*(3*Q0-2*t^2) := by
    apply mul_pos (by linarith)
    norm_num [Q0] at ht2 ⊢
    linarith
  have hbase := low_curvature_polynomial ht
  have hnum₁ := mul_lt_mul_of_pos_right low_coefficients.1 (by norm_num [Q0] : 0<Q0)
  have hnum₂ := mul_lt_mul_of_pos_right low_coefficients.2.1 hfactor
  have hgamma := mul_lt_mul_of_pos_right low_coefficients.2.2.2 hx3
  have hcube := mul_le_mul_of_nonneg_right hxu.le (sq_nonneg x)
  have hreserve : 2*lowGamma*x^3<
      lowAlpha*Q0+lowDelta*t*(3*Q0-2*t^2) := by
    nlinarith only [hbase,hnum₁,hnum₂,hgamma,hcube,hcircle]
  have hid₀ : lowReserveDD b*x^3=
      2*lowGamma*x^3-lowAlpha*Q0-lowDelta*t*(Q0+2*x^2) := by
    rw [lowReserveDD,Ad,FrameCircleArc.Add,← hxdef,← htdef]
    field_simp
    ring
  have hid₁ : Q0+2*x^2=3*Q0-2*t^2 := by linarith [hcircle]
  rw [hid₁] at hid₀
  have hnegative : lowReserveDD b*x^3<0 := by linarith
  exact neg_of_mul_neg_left hnegative hx3.le

theorem lowReserve_concave : ConcaveOn ℝ (Icc 0 b1) lowReserve := by
  apply concave_of_deriv2
    (fun b hb => lowReserve_derivative ⟨hb.1,hb.2.trans b1_mem.2⟩)
    (fun b hb => lowReserve_second_derivative ⟨hb.1,hb.2.trans b1_mem.2⟩)
  exact fun b hb => (lowReserve_second_negative hb).le

theorem low_arcD_positive {b : ℝ} (hb : b∈Icc 0 b1) : 0<arcD b := by
  have ha := (A_low_bounds hb).1
  have hbu : b1<3247/10000 := by dsimp [b1]; linarith [a1_precise.2]
  dsimp [arcD,quadraticR,quadraticS]
  linarith [a1_precise.1,hb.2]

theorem lowReserve_zero : 0<lowReserve 0 := by
  rw [lowReserve_identity ⟨le_rfl,by linarith [c0_bounds.1]⟩]
  have hj := lowJ_zero
  have hD : quadraticR*(91457/100000)-quadraticS/2<arcD 0 := by
    simp only [arcD,A_zero,zero_add]
    dsimp [quadraticR,quadraticS]
    linarith [a0_bounds.1]
  have hp := mul_nonneg (sub_nonneg.mpr hj.le) (sub_nonneg.mpr hD.le)
  dsimp [kappa,rho,quadraticR,quadraticS] at *
  nlinarith only [hj,hD,hp]

theorem lowReserve_b1 : 0<lowReserve b1 := by
  rw [lowReserve_identity b1_mem]
  have hj := lowJ_b1
  have hbu : b1<3247/10000 := by dsimp [b1]; linarith [a1_precise.2]
  have hbl : (3246/10000:ℝ)<b1 := by dsimp [b1]; linarith [a1_precise.1]
  have hD : quadraticR*(7984/10000)-quadraticS*(8247/10000)<arcD b1 := by
    rw [arcD,A_b1]
    dsimp [quadraticR,quadraticS]
    linarith [a1_precise.1]
  have hp := mul_nonneg (sub_nonneg.mpr hj.le) (sub_nonneg.mpr hD.le)
  have hsq : (1-kappa*(b1+1/2))^2≤(1-kappa*(8246/10000))^2 := by
    have hnonneg : 0≤1-kappa*(b1+1/2) := by dsimp [kappa]; linarith
    have hle : 1-kappa*(b1+1/2)≤1-kappa*(8246/10000) := by dsimp [kappa]; linarith
    exact pow_le_pow_left₀ hnonneg hle 2
  dsimp [kappa,rho,quadraticR,quadraticS] at *
  nlinarith only [hj,hD,hp,hsq]

theorem lowReserve_positive {b : ℝ} (hb : b∈Icc 0 b1) : 0<lowReserve b :=
  concave_gt_of_endpoints lowReserve_concave hb lowReserve_zero lowReserve_b1

def midQuadratic (b : ℝ) : ℝ := midJ b-(1-kappa*(b+1/2))^2
def midQuadraticD (b : ℝ) : ℝ := -midA*Ad b-midB+2*kappa*(1-kappa*(b+1/2))
def midQuadraticDD (b : ℝ) : ℝ := -midA*FrameCircleArc.Add b-2*kappa^2

theorem threshold_domain : b1<primaryThreshold ∧ primaryThreshold<b2 := by
  dsimp [primaryThreshold,kappa]
  constructor <;> linarith [b1_bounds.2,b2_bounds.1]

theorem threshold_root_lower {b : ℝ} (hb : b∈Icc 0 primaryThreshold) :
    (43/25:ℝ)<A b+1/2 := by
  have hdom : b∈Icc 0 c0 := ⟨hb.1,hb.2.trans (threshold_domain.2.le.trans b2_mem.2)⟩
  have hc := A_circle hdom
  have hx := A_shift_pos hdom
  have ht : b+1/2≤100/103 := by dsimp [primaryThreshold,kappa] at hb; linarith [hb.2]
  have hs := pow_le_pow_left₀ (by linarith [hb.1] : 0≤b+1/2) ht 2
  norm_num [Q0] at hc hs
  nlinarith

theorem midQuadratic_derivative {b : ℝ} (hb : b∈Icc 0 c0) :
    HasDerivAt midQuadratic (midQuadraticD b) b := by
  have h := (midJ_derivative hb).sub
    (((((hasDerivAt_id b).add_const (1/2)).const_mul kappa).const_sub 1).pow 2)
  convert h using 1
  · funext x
    simp only [midQuadratic,Pi.sub_apply,Pi.pow_apply,id]
  · simp only [midQuadraticD,id]
    push_cast
    ring

theorem midQuadratic_second_derivative {b : ℝ} (hb : b∈Icc 0 c0) :
    HasDerivAt midQuadraticD (midQuadraticDD b) b := by
  have h := (((Ad_hasDerivAt hb).const_mul (-midA)).sub_const midB).add
    (((((hasDerivAt_id b).add_const (1/2)).const_mul kappa).const_sub 1).const_mul
      (2*kappa))
  convert h using 1
  · funext x
    simp only [midQuadraticD,Pi.add_apply,id]
  · simp only [midQuadraticDD]
    ring

theorem midQuadratic_concave : ConcaveOn ℝ (Icc b1 primaryThreshold) midQuadratic := by
  have hdom (b : ℝ) (hb : b∈Icc b1 primaryThreshold) : b∈Icc 0 c0 :=
    ⟨b1_mem.1.trans hb.1,hb.2.trans (threshold_domain.2.le.trans b2_mem.2)⟩
  apply concave_of_deriv2 (fun b hb => midQuadratic_derivative (hdom b hb))
    (fun b hb => midQuadratic_second_derivative (hdom b hb))
  intro b hb
  have hx := A_shift_pos (hdom b hb)
  have hl := threshold_root_lower ⟨b1_mem.1.trans hb.1,hb.2⟩
  have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤43/25) hl.le 3
  have hcoef : midA*Q0≤2*kappa^2*(A b+1/2)^3 := by
    dsimp [midA,Q0,kappa] at *
    norm_num at hcube
    linarith
  have hid : midQuadraticDD b=midA*Q0/(A b+1/2)^3-2*kappa^2 := by
    rw [midQuadraticDD,FrameCircleArc.Add]
    ring
  rw [hid]
  have hq := (div_le_iff₀ (pow_pos hx 3)).2 hcoef
  linarith

theorem midQuadratic_b1 : 0< midQuadratic b1 := by
  have hj : (7/250:ℝ)< midJ b1 := by
    rw [midJ,A_b1]
    have hb : b1<(3247/10000:ℝ) := by dsimp [b1]; linarith [a1_precise.2]
    dsimp [midK,midA,midB]
    linarith [a1_precise.2]
  have hbL : (3246/10000:ℝ)<b1 := by dsimp [b1]; linarith [a1_precise.1]
  have hbU : b1<3247/10000 := by dsimp [b1]; linarith [a1_precise.2]
  have hsq : (1-kappa*(b1+1/2))^2≤(1-kappa*(8246/10000))^2 := by
    apply pow_le_pow_left₀
    · dsimp [kappa]; linarith
    · dsimp [kappa]; linarith
  dsimp [midQuadratic,kappa] at *
  nlinarith only [hj,hsq]

theorem midQuadratic_threshold : 0< midQuadratic primaryThreshold := by
  have hb : primaryThreshold∈Icc 0 c0 :=
    ⟨b1_mem.1.trans threshold_domain.1.le,threshold_domain.2.le.trans b2_mem.2⟩
  have hh := midJ_positive hb
  have hz : 1-kappa*(primaryThreshold+1/2)=0 := by norm_num [primaryThreshold,kappa]
  rw [midQuadratic,hz]
  simpa using hh

theorem midQuadratic_positive {b : ℝ} (hb : b∈Icc b1 primaryThreshold) :
    0< midQuadratic b :=
  concave_gt_of_endpoints midQuadratic_concave hb midQuadratic_b1 midQuadratic_threshold

/-- The complete marker reserve for the negative original secondary
quarter; all admissible lower-chart states are included. -/
theorem correction_quadratic (s : State) (hs : s.branch.type≠0)
    (hb : s.b<primaryThreshold) :
    0<quadraticD s ∧
      (1-kappa*(s.b+1/2))^2<4*kappa*rho*J s*quadraticD s := by
  cases hbr : s.branch with
  | coreSide | coreCorner => simp [hbr,Branch.type] at hs
  | low =>
      have hc := state_low_chart s hbr
      have hD : quadraticD s=arcD s.b := by rw [quadraticD,hc.1]; rfl
      have hp := low_arcD_positive hc.2
      have hR := lowReserve_positive hc.2
      rw [lowReserve_identity ⟨hc.2.1,hc.2.2.trans b1_mem.2⟩] at hR
      have hJ := lowJ_below_original s hbr
      have hprod := mul_lt_mul_of_pos_right hJ hp
      rw [hD]
      refine ⟨hp,?_⟩
      dsimp [kappa,rho] at *
      nlinarith only [hR,hprod]
  | middle =>
      have hc := state_mid_chart s hbr
      have hl := threshold_root_lower ⟨s.b_nonneg,hb.le⟩
      have hD : (23/100:ℝ)<quadraticD s := by
        rw [quadraticD,hc.1]
        dsimp [quadraticR,quadraticS,primaryThreshold,kappa] at *
        linarith
      have hQ := midQuadratic_positive ⟨hc.2.1,hb.le⟩
      have hJ := midJ_below_original s hbr
      have hJstrong : (1-kappa*(s.b+1/2))^2<J s := by
        dsimp [midQuadratic] at hQ
        linarith
      have hJpos : 0<J s := (sq_nonneg _).trans_lt hJstrong
      have hp := mul_lt_mul_of_pos_left hD hJpos
      refine ⟨by linarith,?_⟩
      dsimp [kappa,rho] at *
      nlinarith only [hp,hJstrong,hJpos]
  | high =>
      have hc := (FrameHighArc.state_high_chart s hbr).2.1
      linarith [threshold_domain.2]

end SquaresInCircles.Eight.GlobalAllHigh
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh

open FramePair FrameCircleArc FrameLowArc FrameMidArc GlobalOuterAnchor

def quarterCharge (s : State) (Y d : ℝ) : ℝ := d+potential s-kappa*Y
def secondaryNegative (s : State) (z : ℝ) : ℝ :=
  -z+kappa*((s.b+1/2)*Real.sin z+(s.a-1/2)*(1-Real.cos z))+rho*J s
def secondaryNegativeD (s : State) (z : ℝ) : ℝ :=
  -1+kappa*((s.b+1/2)*Real.cos z+(s.a-1/2)*Real.sin z)
def secondaryNegativeDD (s : State) (z : ℝ) : ℝ :=
  kappa*(-(s.b+1/2)*Real.sin z+(s.a-1/2)*Real.cos z)
def secondaryNegativeDDD (s : State) (z : ℝ) : ℝ :=
  -kappa*((s.b+1/2)*Real.cos z+(s.a-1/2)*Real.sin z)

theorem secondaryNegative_derivative (s : State) (z : ℝ) :
    HasDerivAt (secondaryNegative s) (secondaryNegativeD s z) z := by
  have h := ((hasDerivAt_id z).neg.add
    ((((Real.hasDerivAt_sin z).const_mul (s.b+1/2)).add
      (((Real.hasDerivAt_cos z).const_sub 1).const_mul (s.a-1/2))).const_mul kappa)).add_const
    (rho*J s)
  convert h using 1
  · funext x
    simp only [secondaryNegative,Pi.add_apply,Pi.neg_apply,id]
  · simp only [secondaryNegativeD]
    ring

theorem secondaryNegative_second_derivative (s : State) (z : ℝ) :
    HasDerivAt (secondaryNegativeD s) (secondaryNegativeDD s z) z := by
  have h := ((((Real.hasDerivAt_cos z).const_mul (s.b+1/2)).add
    ((Real.hasDerivAt_sin z).const_mul (s.a-1/2))).const_mul kappa).const_add (-1)
  convert h using 1
  · funext x
    simp only [secondaryNegativeD,Pi.add_apply]
  · simp only [secondaryNegativeDD]
    ring

theorem secondaryNegative_third_derivative (s : State) (z : ℝ) :
    HasDerivAt (secondaryNegativeDD s) (secondaryNegativeDDD s z) z := by
  have h := (((Real.hasDerivAt_sin z).const_mul (-(s.b+1/2))).add
    ((Real.hasDerivAt_cos z).const_mul (s.a-1/2))).const_mul kappa
  convert h using 1
  · funext x
    simp only [secondaryNegativeDD,Pi.add_apply]
  · simp only [secondaryNegativeDDD]
    ring

theorem secondaryNegativeD_concave (s : State) (hs : s.branch.type≠0) :
    ConcaveOn ℝ (Icc 0 frameCap) (secondaryNegativeD s) := by
  apply concave_of_deriv2 (fun z _ => secondaryNegative_second_derivative s z)
    (fun z _ => secondaryNegative_third_derivative s z)
  intro z hz
  have ha := (A_bounds (state_outer_chart s hs).2).1
  rw [← (state_outer_chart s hs).1] at ha
  have tr := transport_trig hz
  have hp := mul_nonneg (show 0≤ s.b+1/2 by linarith [s.b_nonneg])
    (show 0≤Real.cos z by linarith [tr.1])
  have hq := mul_nonneg (show 0≤ s.a-1/2 by linarith [c0_bounds.1]) tr.2.2.1
  dsimp [secondaryNegativeDDD,kappa]
  linarith

theorem secondaryNegativeD_right (s : State) (hs : s.branch.type≠0)
    (hb : primaryThreshold≤ s.b) : (1/50:ℝ)<secondaryNegativeD s frameCap := by
  have ha := (A_bounds (state_outer_chart s hs).2).1
  rw [← (state_outer_chart s hs).1] at ha
  have ht : 1≤kappa*(s.b+1/2) := by
    dsimp [primaryThreshold,kappa] at hb ⊢
    linarith
  have hc := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
  have hsine := sin_lower_seven (show (0:ℝ)≤7/10 by norm_num)
  norm_num at hc hsine
  have hc0 : 0≤Real.cos frameCap := by dsimp [frameCap]; linarith
  have hsin0 : 0≤Real.sin frameCap := by dsimp [frameCap]; linarith
  have hp := mul_le_mul_of_nonneg_right ht hc0
  have hq := mul_le_mul_of_nonneg_right
    (show (399/1000:ℝ)≤ s.a-1/2 by linarith [diagonal_bounds.1]) hsin0
  dsimp [secondaryNegativeD,kappa,frameCap] at *
  nlinarith only [hp,hq,hc,hsine]

theorem secondaryNegativeD_nonnegative (s : State) (hs : s.branch.type≠0)
    (hb : primaryThreshold≤ s.b) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0≤ secondaryNegativeD s z := by
  have h0 : 0≤ secondaryNegativeD s 0 := by
    norm_num [secondaryNegativeD] at ⊢
    dsimp [primaryThreshold,kappa] at hb ⊢
    linarith
  have h1 : 0≤ secondaryNegativeD s frameCap := by
    linarith [secondaryNegativeD_right s hs hb]
  exact (le_min h0 h1).trans
    ((secondaryNegativeD_concave s hs).min_le_of_mem_Icc
      ⟨le_rfl,hz.1.trans hz.2⟩ ⟨hz.1.trans hz.2,le_rfl⟩ hz)

theorem secondaryNegativeD_high (s : State) (hs : s.branch=.high)
    {z : ℝ} (hz : z∈Icc 0 frameCap) : (1/50:ℝ)≤ secondaryNegativeD s z := by
  have hsOuter : s.branch.type≠0 := by simp [hs,Branch.type]
  have hb := (FrameHighArc.state_high_chart s hs).2.1
  have hthreshold : primaryThreshold≤ s.b := by linarith [threshold_domain.2]
  have h0 : (1/50:ℝ)≤ secondaryNegativeD s 0 := by
    norm_num [secondaryNegativeD,kappa] at ⊢
    linarith [b2_bounds.1]
  have h1 := (secondaryNegativeD_right s hsOuter hthreshold).le
  exact (le_min h0 h1).trans
    ((secondaryNegativeD_concave s hsOuter).min_le_of_mem_Icc
      ⟨le_rfl,hz.1.trans hz.2⟩ ⟨hz.1.trans hz.2,le_rfl⟩ hz)

theorem secondaryNegative_large (s : State) (hs : s.branch.type≠0)
    (hb : primaryThreshold≤ s.b) {z : ℝ} (hz : z∈Ioc 0 frameCap) :
    0<secondaryNegative s z := by
  have hmono : MonotoneOn (secondaryNegative s) (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t _ => (secondaryNegative_derivative s t).continuousAt.continuousWithinAt
    · exact fun t _ => secondaryNegative_derivative s t
    · exact fun t ht => secondaryNegativeD_nonnegative s hs hb (Ioo_subset_Icc_self ht)
  have hbase := hmono (by norm_num [frameCap]) (Ioc_subset_Icc_self hz) hz.1.le
  have hzero : secondaryNegative s 0=rho*J s := by simp [secondaryNegative]
  rw [hzero] at hbase
  by_cases hJ : 0<J s
  · exact (mul_pos (by norm_num [rho] : 0<rho) hJ).trans_le hbase
  · have hJzero : J s=0 := le_antisymm (le_of_not_gt hJ) (J_nonnegative s hs)
    have hhigh := (J_eq_zero_iff s hs).1 hJzero
    have hd (t : ℝ) : HasDerivAt (fun t : ℝ => secondaryNegative s t-t/50)
        (secondaryNegativeD s t-1/50) t :=
      (secondaryNegative_derivative s t).sub ((hasDerivAt_id t).div_const 50)
    have hm : MonotoneOn (fun t : ℝ => secondaryNegative s t-t/50) (Icc 0 frameCap) := by
      apply monoOn_of_hasDeriv_nonneg
      · exact fun t _ => (hd t).continuousAt.continuousWithinAt
      · exact fun t _ => hd t
      · intro t ht
        linarith [secondaryNegativeD_high s hhigh (Ioo_subset_Icc_self ht)]
    have hh := hm (by norm_num [frameCap]) (Ioc_subset_Icc_self hz) hz.1.le
    simp only at hh
    rw [hzero,hJzero] at hh
    norm_num at hh
    linarith [hz.1]

theorem secondaryNegative_quadratic_lower (s : State) (hs : s.branch.type≠0)
    {z : ℝ} (hz : z∈Icc 0 frameCap) :
    rho*J s+(kappa*(s.b+1/2)-1)*z+kappa*quadraticD s*z^2≤ secondaryNegative s z := by
  have hA := (A_bounds (state_outer_chart s hs).2).1
  rw [← (state_outer_chart s hs).1] at hA
  have ha : 0≤ s.a-1/2 := by linarith [c0_bounds.1]
  have hb : 0≤ s.b+1/2 := by linarith [s.b_nonneg]
  have hsin := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hz.1) hb
  have hcos := mul_le_mul_of_nonneg_left (cos_upper_four hz.1) ha
  have h3 : z^3≤(7/10)*z^2 := by
    have hh := mul_le_mul_of_nonneg_right hz.2 (sq_nonneg z)
    dsimp [frameCap] at hh
    nlinarith only [hh]
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  have h4 : z^4≤(49/100)*z^2 := by
    have hh := mul_le_mul_of_nonneg_right h2 (sq_nonneg z)
    dsimp [frameCap] at hh
    nlinarith only [hh]
  have h3b := mul_le_mul_of_nonneg_left h3 hb
  have h4a := mul_le_mul_of_nonneg_left h4 ha
  dsimp [secondaryNegative,quadraticD,quadraticR,quadraticS,kappa]
  nlinarith only [hsin,hcos,h3b,h4a]

theorem positive_quadratic {A B C z : ℝ} (hA : 0<A) (hdisc : B^2<4*A*C) :
    0<A*z^2+B*z+C := by
  have hid : 4*A*(A*z^2+B*z+C)=(2*A*z+B)^2+(4*A*C-B^2) := by ring
  have hp : 0<4*A*(A*z^2+B*z+C) := by linarith [sq_nonneg (2*A*z+B)]
  exact (mul_pos_iff_of_pos_left (by linarith : 0<4*A)).1 hp

theorem secondaryNegative_small (s : State) (hs : s.branch.type≠0)
    (hb : s.b<primaryThreshold) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0<secondaryNegative s z := by
  have hreserve := correction_quadratic s hs hb
  have hA : 0<kappa*quadraticD s := mul_pos (by norm_num [kappa]) hreserve.1
  have hdisc : (kappa*(s.b+1/2)-1)^2<4*(kappa*quadraticD s)*(rho*J s) := by
    nlinarith only [hreserve.2]
  have hp := positive_quadratic (z:=z) hA hdisc
  have hl := secondaryNegative_quadratic_lower s hs hz
  linarith

/-- The weak projection of owner `2` gives `kappa ≤ quarterCharge s Y d`, strictly when
`d ≠ 0`. -/
theorem secondary_charge (s : State) (hs : s.branch.type≠0) {Y d : ℝ}
    (hd : |d|≤frameCap)
    (hm : GlobalOuterAnchor.width d≤ s.a*Real.cos d+s.b*Real.sin d-Y) :
    kappa≤quarterCharge s Y d ∧ (d≠0 → kappa<quarterCharge s Y d) := by
  have hJ := J_nonnegative s hs
  have houter := state_outer_chart s hs
  have hab := A_bounds houter.2
  rw [← houter.1] at hab
  by_cases hd0 : 0≤d
  · have hd' : d∈Icc 0 frameCap := ⟨hd0,(le_abs_self d).trans hd⟩
    have tr := transport_trig hd'
    have hsin := Real.sin_le hd0
    have hfirst := mul_nonneg (show 0≤ s.a-1/2 by linarith [c0_bounds.1])
      (sub_nonneg.mpr (Real.cos_le_one d))
    have hsecond := mul_nonneg (show 0≤(9/10:ℝ)-s.b by linarith [houter.2.2,c0_bounds.2])
      tr.2.2.1
    dsimp [GlobalOuterAnchor.width] at hm
    rw [abs_of_nonneg tr.2.2.1] at hm
    have hgain : (147/250)*d≤quarterCharge s Y d-kappa := by
      dsimp [quarterCharge,potential,kappa,rho]
      nlinarith only [hm,hJ,hfirst,hsecond,hsin]
    refine ⟨by linarith,?_⟩
    intro hdne
    have hdpos : 0<d := lt_of_le_of_ne hd0 (Ne.symm hdne)
    linarith
  · have hz : -d∈Ioc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    have hscalar : 0<secondaryNegative s (-d) := by
      rcases lt_or_ge s.b primaryThreshold with hb | hb
      · exact secondaryNegative_small s hs hb (Ioc_subset_Icc_self hz)
      · exact secondaryNegative_large s hs hb hz
    have hsine := (transport_trig (Ioc_subset_Icc_self hz)).2.2.1
    have hsinneg : Real.sin d= -Real.sin (-d) := by simp
    have hcosneg : Real.cos d=Real.cos (-d) := by simp
    dsimp [GlobalOuterAnchor.width] at hm
    rw [hsinneg,hcosneg,abs_neg,abs_of_nonneg hsine] at hm
    have hgain : secondaryNegative s (-d)≤quarterCharge s Y d-kappa := by
      dsimp [secondaryNegative,quarterCharge,potential,kappa,rho]
      nlinarith only [hm]
    exact ⟨by linarith,fun _ => by linarith⟩

end SquaresInCircles.Eight.GlobalAllHigh
end
end
end
