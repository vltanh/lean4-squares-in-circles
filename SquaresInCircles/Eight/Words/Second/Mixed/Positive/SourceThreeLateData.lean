module

public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.SourceThreeContact
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeLowerFourth

/-!
# Eight squares: one affine dividing curve for every late transverse angle

The line is determined by the proved affine L envelope and the exact
required cost. It remains inside the original target circle domain.
The source coordinate and the target derivative are differentiated
along this whole curve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Late
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open PositiveThree (Lower lowerAngle lower_trig)

def angles : Set ℝ := Icc (13/10) (Real.pi/2)
def v : ℝ := 100/69
def cut (φ : ℝ) : ℝ := (φ-51157/50000)/(69/100)
def f (φ : ℝ) : ℝ := source (cut φ) φ
def f1 (φ : ℝ) : ℝ :=
  (v*ratio (cut φ)-W (cut φ))*Real.sin φ+(1-U (cut φ)+v)*Real.cos φ
def f2 (φ : ℝ) : ℝ :=
  (v^2*ratioD (cut φ)-1+U (cut φ)-2*v)*Real.sin φ+
    (2*v*ratio (cut φ)-W (cut φ))*Real.cos φ
def f3 (φ : ℝ) : ℝ :=
  (v^3*ratioDD (cut φ)-3*v*ratio (cut φ)+W (cut φ))*Real.sin φ+
    (3*v^2*ratioD (cut φ)-1+U (cut φ)-3*v)*Real.cos φ
def D (φ : ℝ) : ℝ := FB (cut φ) φ
def D1 (φ : ℝ) : ℝ := g*(v*ratioD (cut φ)*Real.sin φ+ratio (cut φ)*Real.cos φ-Real.sin φ)-
  v*LLabel.d2 (cut φ)
def D2 (φ : ℝ) : ℝ :=
  g*((v^2*ratioDD (cut φ)-ratio (cut φ))*Real.sin φ+
    2*v*ratioD (cut φ)*Real.cos φ-Real.cos φ)-v^2*LLabel.d3 (cut φ)

lemma lower_mem {φ : ℝ} (hφ : φ∈angles) : Lower φ :=
  ⟨by dsimp [lowerAngle]; linarith [hφ.1,pi_hand_enclosure.2],hφ.2⟩

lemma cut_bounds {φ : ℝ} (hφ : φ∈angles) :
    (2/5:ℝ)<cut φ ∧ cut φ<(397/500:ℝ) := by
  dsimp [cut]
  constructor <;> linarith [hφ.1,hφ.2,pi_hand_enclosure.2]

lemma cut_domain {φ : ℝ} (hφ : φ∈angles) : cut φ∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem ⟨by linarith [(cut_bounds hφ).1],by linarith [(cut_bounds hφ).2]⟩

lemma trig {φ : ℝ} (hφ : φ∈angles) :
    0<Real.sin φ ∧ Real.sin φ≤1 ∧ 0≤Real.cos φ ∧ Real.cos φ≤67/250 := by
  have ht := lower_trig (lower_mem hφ)
  have hi : Lower (13/10:ℝ) := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],
    by linarith [pi_hand_enclosure.1]⟩
  have hm := PositiveThree.lower_cos_antitone hi (lower_mem hφ) hφ.1
  have hc := HighOrderTaylor.cos_le_C12 (x := (13/10:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.C12,cos10,cos8] at hc
  exact ⟨by linarith [ht.1],ht.2.1,ht.2.2.1,by linarith⟩

lemma shifted_bounds {φ : ℝ} (hφ : φ∈angles) :
    (1497/1000:ℝ)<U (cut φ) ∧ U (cut φ)<(1763/1000:ℝ) ∧
    (357/500:ℝ)<ratioD (cut φ) := by
  have hc := UW_circle (outer_domain (cut_domain hφ))
  have hp := U_positive (outer_domain (cut_domain hφ))
  have hb := cut_bounds hφ
  have hw : (9/10:ℝ)<W (cut φ) ∧ W (cut φ)<647/500 := by dsimp [W]; constructor <;> linarith
  have hwL := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤9/10) hw.1.le 2
  have hwU := pow_le_pow_left₀ (by linarith [hw.1] : 0≤W (cut φ)) hw.2.le 2
  have hlo : (1497/1000:ℝ)<U (cut φ) := by norm_num [Q0] at hc; nlinarith
  have hhi : U (cut φ)<(1763/1000:ℝ) := by norm_num [Q0] at hc; nlinarith
  have h3 := pow_le_pow_left₀ hp.le hhi.le 3
  have hrd : (357/500:ℝ)<ratioD (cut φ) := by
    change (357/500:ℝ)<Q0/(U (cut φ))^3
    apply (lt_div_iff₀ (pow_pos hp 3)).2
    norm_num [Q0]
    nlinarith
  exact ⟨hlo,hhi,hrd⟩

lemma cut_hasDerivAt (φ : ℝ) : HasDerivAt cut v φ := by
  have hd := ((hasDerivAt_id' (x := φ)).sub_const (51157/50000)).div_const (69/100)
  refine hd.congr_deriv ?_
  norm_num [v]

lemma U_hasDerivAt {φ : ℝ} (hφ : φ∈angles) :
    HasDerivAt (fun θ => U (cut θ)) (-v*ratio (cut φ)) φ := by
  have hd := ((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain (cut_domain hφ))).comp φ
    (cut_hasDerivAt φ)).add_const (1/2)
  exact hd.congr_deriv (by ring)

lemma W_hasDerivAt (φ : ℝ) : HasDerivAt (fun θ => W (cut θ)) v φ :=
  (cut_hasDerivAt φ).add_const (1/2)

lemma ratio_hasDerivAt {φ : ℝ} (hφ : φ∈angles) :
    HasDerivAt (fun θ => ratio (cut θ)) (v*ratioD (cut φ)) φ := by
  exact ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain (cut_domain hφ))).comp φ
    (cut_hasDerivAt φ)).congr_deriv (by ring)

lemma ratioD_hasDerivAt {φ : ℝ} (hφ : φ∈angles) :
    HasDerivAt (fun θ => ratioD (cut θ)) (v*ratioDD (cut φ)) φ := by
  exact ((ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain (cut_domain hφ))).comp φ
    (cut_hasDerivAt φ)).congr_deriv (by ring)

lemma f_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt f (f1 φ) φ := by
  have hd := ((((U_hasDerivAt hφ).const_sub 1).fun_mul (Real.hasDerivAt_sin φ)).fun_add
    ((W_hasDerivAt φ).fun_mul (Real.hasDerivAt_cos φ))).add_const (1/2)
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · simp only [f1]
    ring
  · simp only [f,source,U,W]
    ring

lemma f1_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt f1 (f2 φ) φ := by
  have hd := ((((ratio_hasDerivAt hφ).const_mul v).fun_sub (W_hasDerivAt φ)).fun_mul
    (Real.hasDerivAt_sin φ)).fun_add
      (((U_hasDerivAt hφ).const_sub (1+v)).fun_mul (Real.hasDerivAt_cos φ))
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · simp only [f2]
    ring
  · simp only [f1]
    ring

lemma f2_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt f2 (f3 φ) φ := by
  have hd := (((((ratioD_hasDerivAt hφ).const_mul (v^2)).fun_add (U_hasDerivAt hφ)).sub_const
    (1+2*v)).fun_mul (Real.hasDerivAt_sin φ)).fun_add
      ((((ratio_hasDerivAt hφ).const_mul (2*v)).fun_sub (W_hasDerivAt φ)).fun_mul
        (Real.hasDerivAt_cos φ))
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · simp only [f3]
    ring
  · simp only [f2]
    ring

lemma D_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt D (D1 φ) φ := by
  have hd := ((((ratio_hasDerivAt hφ).fun_mul (Real.hasDerivAt_sin φ)).fun_add
    (Real.hasDerivAt_cos φ)).const_mul g).fun_sub
      ((LLabel.d1_hasDerivAt (outer_domain (cut_domain hφ))).comp φ (cut_hasDerivAt φ))
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · simp only [D1]
    ring
  · simp only [D,FB,Function.comp]

lemma D1_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt D1 (D2 φ) φ := by
  have hd := (((((((ratioD_hasDerivAt hφ).const_mul v).fun_mul (Real.hasDerivAt_sin φ)).fun_add
    ((ratio_hasDerivAt hφ).fun_mul (Real.hasDerivAt_cos φ))).fun_sub
      (Real.hasDerivAt_sin φ)).const_mul g).fun_sub
      (((LLabel.d2_hasDerivAt (outer_domain (cut_domain hφ))).comp φ
        (cut_hasDerivAt φ)).const_mul v))
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · simp only [D2]
    ring
  · simp only [D1,Function.comp]

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Late
