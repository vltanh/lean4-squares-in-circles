module

public import SquaresInCircles.Eight.TableFree.SecondMixedTSmallEnvelope
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreePrimaryBounds
public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveCoreTwoUpper
public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveCoreTwoLower

/-!
# Original-coordinate data for negative outer to positive core at edge three

The two contact relaxations are functions of the original outer point.
The high transverse-coordinate derivative estimate follows from the
already established primary-coordinate label bound. Uncompiled draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open PositiveThree (Lower lowerAngle)

def g : ℝ := 94831/100000
def c : ℝ := 497/10000
def γ : ℝ := 17953/20000
def value (b B φ : ℝ) : ℝ := φ-c-T b-g*B
def aligned (b : ℝ) : ℝ := Real.pi/2-c-T b-g*(arc b-1)
abbrev secondaryCut := MixedTwo.PositiveCore.secondaryCut
abbrev primaryCut := MixedTwo.PositiveCore.primaryCut
def secondaryContact (b φ : ℝ) : ℝ := φ-c-T b-g*secondaryCut (arc b) b φ
def primaryContact (b φ : ℝ) : ℝ := φ-c-T b-g*primaryCut (arc b) φ

lemma high_ratio {b : ℝ} (hb : b∈Icc (7/10:ℝ) outerDiagonal) :
    TLabel.d1 b<(17/20)*ratio b := by
  have hdom : b∈Icc 0 outerDiagonal := ⟨by linarith [hb.1],hb.2⟩
  have hs := ShortOuterOne.SameContact.arc_state hdom
  have ha := NegativeTwo.primary_mem hs
  have hu : arc b≤11/10 := by
    have hc := hs.2.2
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤6/5)
      (show 6/5≤b+1/2 by linarith [hb.1]) 2
    norm_num [Q0] at hc
    nlinarith [hs.1,hs.2.1]
  have hr : 0<ratio b := by
    dsimp [ratio]
    exact div_pos (by linarith [hb.1]) (by linarith [hs.1,hs.2.1])
  have hh := mul_lt_mul_of_pos_right (OppositeThree.primary_first_eleven ⟨ha.1,hu⟩) hr
  rw [NegativeThree.primary_first_exchange hs] at hh
  exact hh

lemma aligned_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt aligned (g*ratio b-TLabel.d1 b) b := by
  have hT : HasDerivAt T (TLabel.d1 b) b := TLabel.outer_hasDerivAt (outer_domain hb)
  have h := (hT.const_sub (Real.pi/2-c)).sub
    (((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).sub_const 1).const_mul g)
  exact h.congr_deriv (by ring)

lemma aligned_monotone : MonotoneOn aligned (Icc (7/10:ℝ) outerDiagonal) := by
  have hdom {b : ℝ} (hb : b∈Icc (7/10:ℝ) outerDiagonal) : b∈Icc 0 outerDiagonal :=
    ⟨by linarith [hb.1],hb.2⟩
  apply monoOn_of_hasDeriv_nonneg
    (fun b hb => (aligned_hasDerivAt (hdom hb)).continuousAt.continuousWithinAt)
    (fun b hb => aligned_hasDerivAt (hdom (Ioo_subset_Icc_self hb)))
  intro b hb
  have hh := high_ratio (Ioo_subset_Icc_self hb)
  have hr : 0≤ratio b := by
    dsimp [ratio]
    have hs := ShortOuterOne.SameContact.arc_state (hdom (Ioo_subset_Icc_self hb))
    exact div_nonneg (by linarith [hb.1]) (by linarith [hs.1,hs.2.1])
  norm_num [g] at *
  nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveCore
