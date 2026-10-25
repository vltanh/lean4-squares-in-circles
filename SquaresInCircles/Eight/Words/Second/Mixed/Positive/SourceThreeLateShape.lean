module

public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.SourceThreeLateData

/-!
# Eight squares: whole-angle derivative signs on the affine dividing curve

The source has increasing second derivative and a negative terminal
slope. The target derivative is concave on the same complete interval.
The estimates use the unchanged circle and uniform rational bounds.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Late
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio ratioD ratioDD)

lemma ratio_identities {φ : ℝ} (hφ : φ∈angles) :
    ratio (cut φ)*U (cut φ)=W (cut φ) ∧
    ratioDD (cut φ)*U (cut φ)=3*ratio (cut φ)*ratioD (cut φ) := by
  have hu := U_positive (outer_domain (cut_domain hφ))
  simp only [ratio,ratioD,ratioDD,U,W] at hu ⊢
  generalize ShortOuterOne.SameContact.arc (cut φ)+1/2=u at hu ⊢
  have hne := hu.ne'
  constructor
  · field_simp
  · field_simp

lemma source_third_positive {φ : ℝ} (hφ : φ∈angles) : 0<f3 φ := by
  have hu := shifted_bounds hφ
  have ht := trig hφ
  have hr := (outer_ratio_bounds (cut_domain hφ)).1
  have hU : 0<U (cut φ) := by linarith [hu.1]
  have hR : 0<ratio (cut φ) := by linarith
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1497/1000) hu.1.le 2
  have hkernel : 0<3*v^3*ratioD (cut φ)-3*v*U (cut φ)+(U (cut φ))^2 := by
    dsimp [v]
    nlinarith [hu.2.1,hu.2.2]
  have hpaid := mul_pos hR hkernel
  have hi := ratio_identities hφ
  have he : (v^3*ratioDD (cut φ)-3*v*ratio (cut φ)+W (cut φ))*U (cut φ)=
      ratio (cut φ)*(3*v^3*ratioD (cut φ)-3*v*U (cut φ)+(U (cut φ))^2) := by
    linear_combination v^3*hi.2-U (cut φ)*hi.1
  have hfirst : 0<v^3*ratioDD (cut φ)-3*v*ratio (cut φ)+W (cut φ) := by nlinarith
  have hsecond : 0<3*v^2*ratioD (cut φ)-1+U (cut φ)-3*v := by
    dsimp [v]
    linarith [hu.1,hu.2.2]
  exact add_pos_of_pos_of_nonneg (mul_pos hfirst ht.1) (mul_nonneg hsecond.le ht.2.2.1)

lemma derivative_second_negative {φ : ℝ} (hφ : φ∈angles) : D2 φ<0 := by
  have hb := cut_domain hφ
  have ht := trig hφ
  have hr := ratioDD_upper hb
  have hr0 := ratioDD_positive hb
  have hd := (outer_ratio_bounds hb).2.2.1
  have hratio := (outer_ratio_bounds hb).1
  have hp := mul_nonneg (show 0≤g*v^2*ratioDD (cut φ) by
      have hg : 0≤g := by norm_num [g,EdgeThreeAligned.gp]
      positivity) (show 0≤1-Real.sin φ by linarith [ht.2.1])
  have hq := mul_le_mul_of_nonneg_left ht.2.2.2
    (show 0≤2*g*v*ratioD (cut φ) by dsimp [g,v,EdgeThreeAligned.gp]; linarith)
  have hB := mul_nonneg hb.1 hr0.le
  have hlast := mul_nonneg (show 0≤ratio (cut φ) by linarith) ht.1.le
  dsimp [D2,RoleLabel.d3,LLabel,g,EdgeThreeAligned.gp,v] at hp hq ⊢
  nlinarith [ht.2.2.1]

lemma terminal_angle : Real.pi/2∈angles := ⟨by linarith [pi_hand_enclosure.1],le_rfl⟩

lemma terminal_source : 0<f (Real.pi/2) := by
  have hu := shifted_bounds terminal_angle
  have hc := UW_circle (outer_domain (cut_domain terminal_angle))
  have hb : (793/1000:ℝ)<cut (Real.pi/2) := by dsimp [cut]; linarith [pi_hand_enclosure.1]
  have hw : (1293/1000:ℝ)<W (cut (Real.pi/2)) := by dsimp [W]; linarith
  have hws := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1293/1000) hw.le 2
  have hU : U (cut (Real.pi/2))<(3/2:ℝ) := by norm_num [Q0] at hc; nlinarith
  norm_num [f,source]
  dsimp [U] at hU
  linarith

lemma terminal_source_slope : f1 (Real.pi/2)<0 := by
  have hu := shifted_bounds terminal_angle
  have hr := (outer_ratio_bounds (cut_domain terminal_angle)).1
  have hi := (ratio_identities terminal_angle).1
  have hp := mul_neg_of_pos_of_neg (show 0<ratio (cut (Real.pi/2)) by linarith)
    (show v-U (cut (Real.pi/2))<0 by dsimp [v]; linarith [hu.1])
  norm_num [f1]
  nlinarith

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Late
