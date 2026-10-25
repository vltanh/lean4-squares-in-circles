module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveSourceThreePrimaryData
public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveSourceThreeCorner

/-!
# The complete lower primary owner for the positive core source

The side uses the proved circle support through B=.65. Beyond it, a
concave first derivative leaves the fixed endpoint, the explicit physical
zero-source endpoint, or the diagonal. The corner has its independent
original-height comparison. Every exit is retained. Uncompiled draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource.Primary
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open PositiveThree (Lower lowerAngle lower_trig)

lemma small_relaxation {B φ : ℝ} (hB : B∈Icc (0:ℝ) (13/20)) (hφ : Lower φ)
    (he : φ≤73/50) : γ<H B φ := by
  have hBf := Asymmetric.rational_outer_mem
    (show B∈Icc (0:ℝ) (899/1000) from ⟨hB.1,by linarith [hB.2]⟩)
  have ht := ShortOuterOne.SameContact.arc_state hBf
  have hs : 0<Real.sin φ := by linarith [(lower_trig hφ).1]
  let x := Real.pi/2-φ
  have hx : x∈Icc (11/100:ℝ) (7/10) :=
    ⟨by dsimp [x]; linarith [pi_hand_enclosure.1],by
      show Real.pi/2-φ≤7/10
      linarith [show Real.pi/2-7/10≤φ from hφ.1]⟩
  have hφeq : φ=Real.pi/2-x := by dsimp [x]; ring
  have hL := MixedLEnvelopes.primary hB
  have hLp := mul_le_mul_of_nonneg_right hL.le hs.le
  have hcircle := outer_circle_lower (X := -g) (Y := -PrimarySupport.p*Real.sin φ) ht
  have hnorm : Real.sqrt ((-g)^2+(-PrimarySupport.p*Real.sin φ)^2)=
      MixedPrimarySupport.N g PrimarySupport.p x := by
    rw [hφeq]
    norm_num [Real.sin_sub,MixedPrimarySupport.N]
    congr 1
    ring
  rw [hnorm] at hcircle
  have hraw : (H B φ-γ)*Real.sin φ=
      (φ-e-L B-γ)*Real.sin φ+g*(LPrimaryZero.U φ-1/2-arc B) := by
    dsimp [H,source]
    field_simp [hs.ne']
    ring
  have hpaid : PrimarySupport.f x≤(H B φ-γ)*Real.sin φ := by
    rw [hraw]
    dsimp [LPrimaryZero.U,PrimaryZero.U,PrimaryZero.m]
    rw [hφeq] at hcircle hLp ⊢
    norm_num [Real.sin_sub,Real.cos_sub,PrimarySupport.f,MixedPrimarySupport.minus,
      PrimarySupport.K,PrimarySupport.k,PrimarySupport.p] at hcircle hLp ⊢
    nlinarith
  have hpos := PrimarySupport.positive hx
  nlinarith

lemma small_direct {b B φ : ℝ} (hb : 0≤b) (hB : B∈Icc (0:ℝ) (13/20))
    (hφ : (73/50:ℝ)≤φ) : γ<value b B φ := by
  have hL := MixedLEnvelopes.primary hB
  have hp := mul_nonneg (by norm_num [g,EdgeThreeAligned.gp] : 0≤g) hb
  dsimp [value,EdgeThreeAligned.positiveCost,γ,EdgeThreeAligned.threshold,e,EdgeThreeAligned.ep] at *
  linarith [hB.2]

lemma endpoint_lower {l B φ : ℝ} (hl : l∈Icc 0 outerDiagonal)
    (hB : B∈Icc l outerDiagonal) (hφ : Lower φ)
    (hslope : 0<HB l φ) (hvalue : γ<H l φ) : γ<H B φ := by
  have hdom {y : ℝ} (hy : y∈Icc l outerDiagonal) : y∈Icc 0 outerDiagonal :=
    ⟨hl.1.trans hy.1,hy.2⟩
  have hh := MinimumCalculus.endpoint_minimum_of_third_nonpos
    (f := fun y => H y φ) (d := fun y => HB y φ)
    (dd := fun y => HBB y φ) (ddd := fun y => HBBB y φ) hB
    (fun y hy => H_hasDerivAt (hdom hy)) (fun y hy => HB_hasDerivAt (hdom hy))
    (fun y hy => HBB_hasDerivAt (hdom hy))
    (fun y hy => (HBBB_negative (hdom hy) hφ).le) hslope
  exact (lt_min hvalue (diagonal_lower hφ)).trans_le hh

lemma zero_source {φ : ℝ} (hφ : φ∈LPrimaryZero.angles) : source (LPrimaryZero.b φ) φ=0 := by
  have ha := (ShortOuterOne.SameContact.actual_arc (LPrimaryZero.physical hφ)).1
  simp [source,ha]

lemma zero_value {φ : ℝ} (hφ : φ∈LPrimaryZero.angles) : γ<H (LPrimaryZero.b φ) φ := by
  have hh := LPrimaryZero.actual_positive (LPrimaryZero.physical hφ) hφ (by ring)
  rw [H,zero_source hφ]
  dsimp [γ,EdgeThreeAligned.threshold,e,EdgeThreeAligned.ep]
  linarith

theorem side_original {b A B φ : ℝ} (hb : 0≤b) (ht : OuterState A B) (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤-(7/12)*Real.cos φ+b*Real.sin φ+A) :
    γ<value b B φ := by
  have hB := NegativeTwo.source_mem ht
  have hcmp := original_lower ht hφ hsep
  have h65 : (13/20:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have h65unit : (13/20:ℝ)∈Icc (13/20:ℝ) EdgeThreeAligned.B1 :=
    ⟨le_rfl,by linarith [EdgeThreeAligned.B1_bounds.1]⟩
  by_cases hsmall : B≤13/20
  · by_cases he : φ≤73/50
    · exact (small_relaxation ⟨hB.1,hsmall⟩ hφ he).trans_le hcmp
    · exact small_direct hb ⟨hB.1,hsmall⟩ (by linarith)
  · have hlarge : (13/20:ℝ)≤B := by linarith
    by_cases he : φ≤73/50
    · exact (endpoint_lower h65 ⟨hlarge,hB.2⟩ hφ (zero_derivative h65unit hφ)
        (small_relaxation (by norm_num) hφ he)).trans_le hcmp
    · have hangle : φ∈LPrimaryZero.angles := ⟨by linarith,hφ.2⟩
      have hzstate := LPrimaryZero.physical hangle
      have hz := NegativeTwo.source_mem hzstate
      have hzunit : LPrimaryZero.b φ≤EdgeThreeAligned.B1 :=
        (EdgeThreeAligned.unit_target_cut hzstate).1 (by linarith [(LPrimaryZero.U_bounds hangle).1])
      have haz := (ShortOuterOne.SameContact.actual_arc hzstate).1
      by_cases hzsmall : LPrimaryZero.b φ≤13/20
      · have ha := ShortOuterOne.SameContact.arc_antitone (outer_domain hz) (outer_domain h65) hzsmall
        rw [haz] at ha
        have hs0 : 0 ≤ source (13/20) φ := div_nonneg (by linarith) (by linarith [(lower_trig hφ).1])
        have hd := small_direct hs0 (show (13/20:ℝ)∈Icc (0:ℝ) (13/20) by norm_num) (by linarith : (73/50:ℝ)≤φ)
        have hleft : γ<H (13/20) φ := by simpa [H,value,EdgeThreeAligned.positiveCost] using hd
        exact (endpoint_lower h65 ⟨hlarge,hB.2⟩ hφ (zero_derivative h65unit hφ) hleft).trans_le hcmp
      · by_cases hbefore : B≤LPrimaryZero.b φ
        · have hL := L_monotone hB hz hbefore
          have hh := LPrimaryZero.actual_positive hzstate hangle (by ring)
          have hp := mul_nonneg (by norm_num [g,EdgeThreeAligned.gp] : 0≤g) hb
          dsimp [value,EdgeThreeAligned.positiveCost,e,EdgeThreeAligned.ep,γ,EdgeThreeAligned.threshold]
          linarith
        · exact (endpoint_lower hz ⟨by linarith,hB.2⟩ hφ
            (zero_derivative ⟨by linarith,hzunit⟩ hφ) (zero_value hangle)).trans_le hcmp

theorem original {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B) (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤-a*Real.cos φ+b*Real.sin φ+A) :
    γ<value b B φ := by
  rcases hs with ⟨rfl,hb,hbu⟩ | ⟨hb,hba,hcircle⟩
  · exact side_original hb ht hφ hsep
  · exact Corner.original (Or.inr ⟨hb,hba,hcircle⟩) hb ht hφ hsep

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource.Primary
