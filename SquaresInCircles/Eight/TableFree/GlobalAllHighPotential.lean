module

public import SquaresInCircles.Eight.TableFree.GlobalQuarterOuterBridge

/-!
# The common outer potential for the all-high owner branch

The correction is the extended high-chart formula minus the unchanged
original marker.  Its strict bounds on both lower charts concern the
whole original arcs; at a chart junction either original marker is
retained.  The same potential is used at every occurrence of a vertex.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh

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
  convert ((hasDerivAt_const b lowK).sub
    (((A_hasDerivAt hb).add_const (1/2)).const_mul lowA)).sub
    (((hasDerivAt_id b).add_const (1/2)).const_mul lowB) using 1 <;>
    dsimp [lowJ] <;> ring

theorem midJ_derivative {b : ℝ} (hb : b∈Icc 0 c0) :
    HasDerivAt midJ (-midA*Ad b-midB) b := by
  convert ((hasDerivAt_const b midK).sub
    (((A_hasDerivAt hb).add_const (1/2)).const_mul midA)).sub
    (((hasDerivAt_id b).add_const (1/2)).const_mul midB) using 1 <;>
    dsimp [midJ] <;> ring

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
    dsimp [Ad,slope,lowA,lowB] at *
    linarith

theorem lowJ_lower {b : ℝ} (hb : b∈Icc 0 b1) : (13/500:ℝ)<lowJ b :=
  lowJ_b1.trans_le (lowJ_antitone hb ⟨b1_mem.1,le_rfl⟩ hb.2)

theorem midJ_positive {b : ℝ} (hb : b∈Icc 0 c0) : 0<midJ b := by
  have hc := A_circle hb
  have hx := A_shift_pos hb
  have ht : 0≤b+1/2 := by linarith [hb.1]
  have hC : 0<midK := by norm_num [midK,midA,midB]
  have hreserve : Q0*(midA^2+midB^2)<midK^2 := by
    norm_num [midK,midA,midB,Q0]
  have hid : (midA*(A b+1/2)+midB*(b+1/2))^2+
      (midA*(b+1/2)-midB*(A b+1/2))^2=Q0*(midA^2+midB^2) := by
    rw [← hc]
    ring
  have hsign : 0≤midA*(A b+1/2)+midB*(b+1/2) := by
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
    have hratio : midA*((b+1/2)/(A b+1/2))<midB := by
      rw [mul_div_assoc]
      apply (div_lt_iff₀ hx).2
      dsimp [midA,midB]
      linarith [short_root_bounds.1,hb.2]
    dsimp [Ad] at *
    linarith

theorem midJ_short {b : ℝ} (hb : b∈Icc 0 (33/100:ℝ)) :
    (1/40:ℝ)<midJ b := by
  have hm := midJ_antitone_short hb ⟨by norm_num,le_rfl⟩ hb.2
  have he : (1/40:ℝ)<midJ (33/100) := by
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

end SquaresInCircles.Eight.TableFree.GlobalAllHigh
