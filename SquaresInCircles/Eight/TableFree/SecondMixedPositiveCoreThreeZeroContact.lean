module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveCoreThreeZeroSlope

/-!
# Original-point closure of the early primary owner

Feasibility supplies the physical lower angle and places the original
source below the zero-contact transverse coordinate. The relaxed cost
comparison therefore applies on its proved domain, including the weak
owner boundary. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig)

lemma zeroHeight_antitone : AntitoneOn PrimaryZero.U (Icc lowerAngle (Real.pi/2)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun φ _ => (PrimaryZero.U_hasDerivAt φ).continuousAt.continuousWithinAt)
    (fun φ _ => PrimaryZero.U_hasDerivAt φ)
  intro φ hφ
  have hh := lower_trig (Ioo_subset_Icc_self hφ)
  dsimp [PrimaryZero.v]
  linarith [hh.1,hh.2.2.2.1]

lemma preinitial_height : (961/500:ℝ)<PrimaryZero.U (28/25) := by
  have hs := HighOrderTaylor.S15_le_sin (x := (28/25:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (28/25:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hc
  dsimp [PrimaryZero.U,PrimaryZero.m]
  linarith

lemma early_primary {a b B φ : ℝ} (hs : OuterState a b) (hB : 0≤B)
    (hφ : Lower φ) (hφu : φ≤7/5)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-(7/12)*Real.cos φ-B*Real.sin φ) :
    γ<value b B φ := by
  have ht := lower_trig hφ
  have hsin : 0<Real.sin φ := by linarith [ht.1]
  have hBsin := mul_nonneg hB hsin.le
  have hheight : PrimaryZero.U φ-1/2≤a := by
    dsimp [PrimaryZero.U,PrimaryZero.m]
    linarith
  have ha : a<(283/200:ℝ) := (NegativeTwo.primary_mem hs).2.trans_lt outer_endpoint_bounds.2.1
  have h28 : Lower (28/25:ℝ) :=
    ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],by linarith [pi_hand_enclosure.1]⟩
  have h57 : Lower (57/50:ℝ) :=
    ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],by linarith [pi_hand_enclosure.1]⟩
  have hlo : (28/25:ℝ)<φ := by
    by_contra hn
    have hm := zeroHeight_antitone hφ h28 (le_of_not_gt hn)
    linarith [preinitial_height]
  by_cases he : φ≤57/50
  · have hm := zeroHeight_antitone hφ h57 he
    have hi : (19/10:ℝ)<PrimaryZero.U (57/50) := by
      dsimp [PrimaryZero.U,PrimaryZero.m]
      linarith [Zero.initial_trig.1,Zero.initial_trig.2.2.1]
    have haL : (7/5:ℝ)<a := by linarith
    have hb : b<(27/500:ℝ) := by
      have hc := hs.2.2
      norm_num [Q0] at hc
      have h1 : (19/10:ℝ)^2≤(a+1/2)^2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
      by_contra hn
      have h2 : (277/500:ℝ)^2≤(b+1/2)^2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
      norm_num at h1 h2
      linarith
    have hBhi : B<(1/50:ℝ) := by
      have hweight := mul_le_mul_of_nonneg_left ht.1.le hB
      have hcut : B*Real.sin φ≤a-(PrimaryZero.U φ-1/2) := by
        dsimp [PrimaryZero.U,PrimaryZero.m]
        linarith
      linarith
    have hT := T_increment_upper (by constructor <;> linarith [fine_outer_endpoint_bounds.2] :
      (0:ℝ)∈Icc 0 outerDiagonal) (NegativeTwo.source_mem hs) hs.1
    have hz : T 0=(167/10000:ℝ) := by norm_num [T,RoleLabel.outer,RoleLabel.eval,TLabel]
    rw [hz] at hT
    dsimp [value,c,g,γ]
    linarith
  · have hz : φ∈Zero.angles := ⟨by linarith,hφu⟩
    have hzstate := Zero.physical hz
    have hab : Zero.a φ≤a := hheight
    have hb : b≤Zero.b φ := by
      have hc := hs.2.2
      have hc0 := hzstate.2.2
      have hsq := pow_le_pow_left₀
        (show 0≤Zero.a φ+1/2 by linarith [hzstate.1,hzstate.2.1])
        (show Zero.a φ+1/2≤a+1/2 by linarith) 2
      by_contra hn
      have hlt := pow_lt_pow_left₀ (show Zero.b φ+1/2<b+1/2 by linarith)
        (by linarith [hzstate.1] : 0≤Zero.b φ+1/2) two_ne_zero
      linarith
    have hcutEq : primaryCut a φ*Real.sin φ=
        a-1/2-(13/12)*Real.cos φ-Real.sin φ/2 := by
      dsimp [primaryCut,MixedTwo.PositiveCore.primaryCut]
      field_simp [hsin.ne']
    have hcut : B≤primaryCut a φ := by
      apply (mul_le_mul_iff_left₀ hsin).mp
      linarith
    have hp := mul_le_mul_of_nonneg_left hcut (show 0≤g by norm_num [g])
    have hm := Zero.contact_antitone hz
      (show b∈Icc (0:ℝ) (Zero.b φ) from ⟨hs.1,hb⟩)
      (show Zero.b φ∈Icc (0:ℝ) (Zero.b φ) from ⟨hzstate.1,le_rfl⟩) hb
    dsimp only at hm
    rw [Zero.boundary_identity hz] at hm
    have hv := Zero.cost_lower hz
    dsimp [primaryContact] at hm
    rw [(ShortOuterOne.SameContact.actual_arc hs).1] at hm
    dsimp [value]
    linarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveCore
