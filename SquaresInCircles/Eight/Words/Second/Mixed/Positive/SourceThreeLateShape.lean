module

public import SquaresInCircles.Eight.Words.Second.Mixed.Edge.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeUpperEasy

/-!
# Eight squares: whole-angle derivative signs on the affine dividing curve

The source has increasing second derivative and a negative terminal
slope. The target derivative is concave on the same complete interval.
The estimates use the unchanged circle and uniform rational bounds.
-/

section
/-!
## The original positive-core transverse comparison

The relaxed source coordinate is used only as a lower bound on the
original source. Its first derivative is concave on the complete
physical target arc. Both the circle and every label remain at Q0.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open PositiveThree (Lower lowerAngle lower_trig)

abbrev g := EdgeThreeAligned.gp
abbrev e := EdgeThreeAligned.ep
abbrev γ := EdgeThreeAligned.threshold
abbrev value := EdgeThreeAligned.positiveCost

def source (B φ : ℝ) : ℝ := (1+Real.sin φ+Real.cos φ)/2-arc B*Real.sin φ+B*Real.cos φ
def F (B φ : ℝ) : ℝ := φ-e+g*source B φ-L B
def FB (B φ : ℝ) : ℝ := g*(ratio B*Real.sin φ+Real.cos φ)-LLabel.d1 B
def FBB (B φ : ℝ) : ℝ := g*ratioD B*Real.sin φ-LLabel.d2 B
def FBBB (B φ : ℝ) : ℝ := g*ratioDD B*Real.sin φ-LLabel.d3 B

lemma source_hasDerivAt {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (fun z => source z φ) (ratio B*Real.sin φ+Real.cos φ) B := by
  have h := (((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).const_mul
    (Real.sin φ)).const_sub ((1+Real.sin φ+Real.cos φ)/2)).add
      ((hasDerivAt_id' B).const_mul (Real.cos φ))
  convert h using 1
  · funext z
    simp only [source,Pi.add_apply]
    ring
  · ring

lemma F_hasDerivAt {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (fun z => F z φ) (FB B φ) B := by
  exact ((((source_hasDerivAt (φ := φ) hB).const_mul g).const_add (φ-e)).sub
    (LLabel.outer_hasDerivAt (outer_domain hB))).congr_deriv (by simp only [FB])

lemma FB_hasDerivAt {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (fun z => FB z φ) (FBB B φ) B := by
  exact ((((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).mul_const
    (Real.sin φ)).add_const (Real.cos φ)).const_mul g).sub
      (LLabel.d1_hasDerivAt (outer_domain hB)) |>.congr_deriv (by simp only [FBB]; ring)

lemma FBB_hasDerivAt {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (fun z => FBB z φ) (FBBB B φ) B := by
  exact (((ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hB)).const_mul g).mul_const
    (Real.sin φ)).sub (LLabel.d2_hasDerivAt (outer_domain hB)) |>.congr_deriv
      (by simp only [FBBB])

lemma FBBB_negative {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) : FBBB B φ<0 := by
  have hr := ratioDD_upper hB
  have hr0 := ratioDD_positive hB
  have hd := ShortOuterOne.SameContact.ratioD_pos (outer_domain hB)
  have hs := mul_le_mul_of_nonneg_left (Real.sin_le_one φ)
    (mul_nonneg (by norm_num [g,EdgeThreeAligned.gp] : 0≤g) hr0.le)
  have hp := mul_nonneg hB.1 hr0.le
  dsimp [g,EdgeThreeAligned.gp] at hs
  dsimp [FBBB,RoleLabel.d3,LLabel,g,EdgeThreeAligned.gp]
  nlinarith

lemma FB_concave (φ : ℝ) : ConcaveOn ℝ (Icc 0 outerDiagonal) (fun B => FB B φ) :=
  concave_of_deriv2 (fun _ hB => FB_hasDerivAt hB)
    (fun _ hB => FBB_hasDerivAt hB) (fun _ hB => (FBBB_negative (φ := φ) hB).le)

lemma FBB_antitone (φ : ℝ) : AntitoneOn (fun B => FBB B φ) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hB => (FBB_hasDerivAt (φ := φ) hB).continuousAt.continuousWithinAt)
    (fun _ hB => FBB_hasDerivAt (φ := φ) (Ioo_subset_Icc_self hB))
    (fun _ hB => (FBBB_negative (φ := φ) (Ioo_subset_Icc_self hB)).le)

lemma FB_angle_hasDerivAt (B φ : ℝ) : HasDerivAt (FB B)
    (g*(ratio B*Real.cos φ-Real.sin φ)) φ := by
  have hd := (((Real.hasDerivAt_sin φ).const_mul (ratio B)).add
    (Real.hasDerivAt_cos φ)).const_mul g
  exact (hd.sub_const (LLabel.d1 B)).congr_deriv (by ring)

lemma FB_angle_antitone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : AntitoneOn (FB B) (Icc lowerAngle (Real.pi/2)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun φ _ => (FB_angle_hasDerivAt B φ).continuousAt.continuousWithinAt)
    (fun φ _ => FB_angle_hasDerivAt B φ)
  intro φ hφ
  have ht := lower_trig (Ioo_subset_Icc_self hφ)
  have hr := (outer_ratio_bounds hB).2.1
  have hp := mul_le_mul_of_nonneg_right hr ht.2.2.1
  have hn : ratio B*Real.cos φ-Real.sin φ<0 := by linarith [ht.1,ht.2.2.2.1]
  exact (mul_neg_of_pos_of_neg (by norm_num [g,EdgeThreeAligned.gp]) hn).le

lemma original_lower {b A B φ : ℝ} (ht : OuterState A B)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤b+A*Real.sin φ-B*Real.cos φ) :
    F B φ≤value b B φ := by
  have hA := (ShortOuterOne.SameContact.actual_arc ht).1
  have hp := mul_le_mul_of_nonneg_left hsep (by norm_num [g,EdgeThreeAligned.gp] : 0≤g)
  dsimp [F,source,value,EdgeThreeAligned.positiveCost]
  rw [hA]
  nlinarith

lemma diagonal_lower {φ : ℝ} (hφ : Lower φ) : γ<F outerDiagonal φ := by
  let f : ℝ→ℝ := fun θ => F outerDiagonal θ
  let fd : ℝ→ℝ := fun θ => 1+g*(1/2-outerDiagonal)*Real.cos θ-
    g*(1/2+outerDiagonal)*Real.sin θ
  have hf (θ : ℝ) : HasDerivAt f (fd θ) θ := by
    have h := (((((Real.hasDerivAt_sin θ).const_mul (1/2-outerDiagonal)).add
      ((Real.hasDerivAt_cos θ).const_mul (1/2+outerDiagonal))).const_mul g).add
        (hasDerivAt_id' θ)).add_const (g/2-e-L outerDiagonal)
    convert h using 1
    · funext x
      simp only [f,F,source,ShortOuterOne.SameContact.arc_diagonal,Pi.add_apply]
      ring
    · simp only [fd]
      ring
  have hfd : ∀θ∈Icc lowerAngle (Real.pi/2),fd θ<0 := by
    intro θ hθ
    have ht := lower_trig hθ
    have hd0 := fine_outer_endpoint_bounds.2
    have hs := mul_le_mul_of_nonneg_left ht.1.le
      (show 0≤g*(1/2+outerDiagonal) by dsimp [g,EdgeThreeAligned.gp]; linarith)
    have hc := mul_nonpos_of_nonpos_of_nonneg
      (show g*(1/2-outerDiagonal)≤0 by dsimp [g,EdgeThreeAligned.gp]; linarith) ht.2.2.1
    dsimp [fd,g,EdgeThreeAligned.gp] at hs hc ⊢
    nlinarith
  have hm : AntitoneOn f (Icc lowerAngle (Real.pi/2)) :=
    antiOn_of_hasDeriv_nonpos (fun θ _ => (hf θ).continuousAt.continuousWithinAt)
      (fun θ _ => hf θ) (fun θ hθ => (hfd θ (Ioo_subset_Icc_self hθ)).le)
  have he := hm hφ ⟨by dsimp [lowerAngle]; linarith,le_rfl⟩ hφ.2
  have hz := EdgeThreeAligned.positive_diagonal
  have hM := LHeight_actual EdgeThreeAligned.diagonal_state
  dsimp [EdgeThreeAligned.positiveHeight] at hz
  rw [hM] at hz
  have hf2 : f (Real.pi/2)=Real.pi/2-e+g*(1-outerDiagonal)-L outerDiagonal := by
    simp only [f,F,source,ShortOuterOne.SameContact.arc_diagonal,Real.sin_pi_div_two,
      Real.cos_pi_div_two]
    ring
  have hfφ : f φ=F outerDiagonal φ := rfl
  rw [hf2,hfφ] at he
  simp only [γ,EdgeThreeAligned.threshold,e,g] at he ⊢
  linarith

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource
end
end
end

section
/-!
## One affine dividing curve for every late transverse angle

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
end
end
end

section
/-!
## Whole-target derivative shape for the positive source side

The exact side relaxation has a concave first derivative on the full
target circle. Its diagonal endpoint decreases to the proved aligned
pair. The derivative is positive at every late zero-source endpoint.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Primary
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open PositiveThree (Lower lowerAngle lower_trig)

def source (B φ : ℝ) : ℝ := (LPrimaryZero.U φ-1/2-arc B)/Real.sin φ
def H (B φ : ℝ) : ℝ := φ-e+g*source B φ-L B
def HB (B φ : ℝ) : ℝ := g*ratio B/Real.sin φ-LLabel.d1 B
def HBB (B φ : ℝ) : ℝ := g*ratioD B/Real.sin φ-LLabel.d2 B
def HBBB (B φ : ℝ) : ℝ := g*ratioDD B/Real.sin φ-LLabel.d3 B

lemma H_hasDerivAt {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (fun z => H z φ) (HB B φ) B := by
  have hd := (((((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).const_sub
    (LPrimaryZero.U φ-1/2)).div_const (Real.sin φ)).const_mul g).const_add (φ-e)).fun_sub
      (LLabel.outer_hasDerivAt (outer_domain hB))
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  · simp only [HB]
    ring
  · simp only [H,source,L]

lemma HB_hasDerivAt {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (fun z => HB z φ) (HBB B φ) B := by
  have hd := (((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).const_mul g).div_const
    (Real.sin φ)).fun_sub (LLabel.d1_hasDerivAt (outer_domain hB))
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  · simp only [HBB]
  · simp only [HB]

lemma HBB_hasDerivAt {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (fun z => HBB z φ) (HBBB B φ) B := by
  have hd := (((ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hB)).const_mul g).div_const
    (Real.sin φ)).fun_sub (LLabel.d2_hasDerivAt (outer_domain hB))
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  · simp only [HBBB]
  · simp only [HBB]

lemma HBBB_negative {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) (hφ : Lower φ) : HBBB B φ<0 := by
  have ht := lower_trig hφ
  have hs : 0<Real.sin φ := by linarith [ht.1]
  have hg : g/Real.sin φ<(7/5:ℝ) := by
    apply (div_lt_iff₀ hs).2
    dsimp [g,EdgeThreeAligned.gp]
    linarith [ht.1]
  have hr := ratioDD_upper hB
  have hr0 := ratioDD_positive hB
  have hd := ShortOuterOne.SameContact.ratioD_pos (outer_domain hB)
  have hp := mul_le_mul_of_nonneg_right hg.le hr0.le
  have hBprod := mul_nonneg hB.1 hr0.le
  have he : g*ratioDD B/Real.sin φ=(g/Real.sin φ)*ratioDD B := by ring
  dsimp [HBBB]
  rw [he]
  norm_num [RoleLabel.d3,LLabel]
  nlinarith

lemma diagonal_hasDerivAt {φ : ℝ} (hφ : Lower φ) : HasDerivAt (H outerDiagonal)
    (1+g*((outerDiagonal-1/2)*Real.cos φ-13/12)/(Real.sin φ)^2) φ := by
  have hs : Real.sin φ≠0 := ne_of_gt (by linarith [(lower_trig hφ).1])
  have hd := (((PrimaryZero.U_hasDerivAt φ).sub_const (1/2+outerDiagonal)).fun_div
    (Real.hasDerivAt_sin φ) hs).const_mul g
  have hd0 := (((hasDerivAt_id' (x := φ)).sub_const e).fun_add hd).sub_const (L outerDiagonal)
  refine (hd0.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · simp only [PrimaryZero.U,PrimaryZero.m,PrimaryZero.v]
    field_simp
    linear_combination -26*g*(Real.sin_sq_add_cos_sq φ)
  · simp only [H,source,LPrimaryZero.U,ShortOuterOne.SameContact.arc_diagonal]
    ring

lemma diagonal_lower {φ : ℝ} (hφ : Lower φ) : γ<H outerDiagonal φ := by
  have hneg {θ : ℝ} (hθ : Lower θ) :
      1+g*((outerDiagonal-1/2)*Real.cos θ-13/12)/(Real.sin θ)^2<0 := by
    have ht := lower_trig hθ
    have hs : 0<(Real.sin θ)^2 := sq_pos_of_pos (by linarith [ht.1])
    apply (mul_lt_mul_iff_left₀ hs).mp
    have he : (1+g*((outerDiagonal-1/2)*Real.cos θ-13/12)/(Real.sin θ)^2)*
        (Real.sin θ)^2=(Real.sin θ)^2+g*(outerDiagonal-1/2)*Real.cos θ-13*g/12 := by
      field_simp [ne_of_gt (by linarith [ht.1] : 0<Real.sin θ)]
      ring
    rw [he,zero_mul]
    have hd : 0≤g*(outerDiagonal-1/2) := by
      dsimp [g,EdgeThreeAligned.gp]
      linarith [fine_outer_endpoint_bounds.2]
    have hdu : g*(outerDiagonal-1/2)≤(2/5)*g := by
      dsimp [g,EdgeThreeAligned.gp]
      linarith [outer_endpoint_bounds.2.2.2]
    have hd2 := pow_le_pow_left₀ hd hdu 2
    have hsq := sq_nonneg (Real.cos θ-g*(outerDiagonal-1/2)/2)
    dsimp [g,EdgeThreeAligned.gp] at hd2 hsq ⊢
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hm : AntitoneOn (H outerDiagonal) (Icc lowerAngle (Real.pi/2)) :=
    antiOn_of_hasDeriv_nonpos
      (fun θ hθ => (diagonal_hasDerivAt hθ).continuousAt.continuousWithinAt)
      (fun θ hθ => diagonal_hasDerivAt (Ioo_subset_Icc_self hθ))
      (fun θ hθ => (hneg (Ioo_subset_Icc_self hθ)).le)
  have hh := hm hφ ⟨by dsimp [lowerAngle]; linarith,le_rfl⟩ hφ.2
  have hz := EdgeThreeAligned.positive_diagonal
  have hM := LHeight_actual EdgeThreeAligned.diagonal_state
  dsimp [EdgeThreeAligned.positiveHeight] at hz
  rw [hM] at hz
  have hπ : H outerDiagonal (Real.pi/2)=Real.pi/2-e+g*(1-outerDiagonal)-L outerDiagonal := by
    simp only [H,source,LPrimaryZero.U,PrimaryZero.U,PrimaryZero.m,
      ShortOuterOne.SameContact.arc_diagonal,Real.sin_pi_div_two,Real.cos_pi_div_two]
    ring
  dsimp [γ,EdgeThreeAligned.threshold]
  dsimp [e,g] at hπ
  linarith

lemma reference_65 : 0<FB (13/20) (Real.pi/2) := by
  have hb := Asymmetric.rational_outer_mem (show (13/20:ℝ)∈Icc 0 (899/1000) by norm_num)
  have hr := shifted_chart_reference (outer_domain hb)
    (l := (1610310529059/1000000000000:ℝ)) (u := (1610310529060/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hd := LLabel.first_chart_reference (outer_domain hb)
    (l := (1610310529059/1000000000000:ℝ)) (u := (1610310529060/1000000000000:ℝ))
    (dlo := (0:ℝ)) (dhi := (137/200:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  have hU := U_positive (outer_domain hb)
  have he : ratio (13/20)*U (13/20)=(23/20:ℝ) := by
    simp only [ratio,U] at hU ⊢
    generalize arc (13/20)+1/2=u at hU ⊢
    field_simp [hU.ne']
    norm_num
  have hr0 := (outer_ratio_bounds hb).1
  have hpaid := mul_le_mul_of_nonneg_left hr.2.le (by linarith : 0≤ratio (13/20))
  norm_num [FB,g,EdgeThreeAligned.gp]
  nlinarith

lemma reference_unit : 0<FB EdgeThreeAligned.B1 (Real.pi/2) := by
  have hb := EdgeThreeAligned.B1_bounds
  have hA := (ShortOuterOne.SameContact.actual_arc EdgeThreeAligned.unit_state).1
  have hsq := pow_le_pow_left₀ (by linarith [hb.1] : 0≤EdgeThreeAligned.B1) hb.2.le 2
  norm_num [FB,RoleLabel.d1,LLabel,ratio,g,EdgeThreeAligned.gp,hA]
  nlinarith

lemma zero_derivative {B φ : ℝ} (hB : B∈Icc (13/20:ℝ) EdgeThreeAligned.B1) (hφ : Lower φ) :
    0<HB B φ := by
  have hBf : B∈Icc 0 outerDiagonal :=
    ⟨by linarith [hB.1],hB.2.trans EdgeThreeAligned.B1_domain.2⟩
  have hs := lower_trig hφ
  have hsin : 0<Real.sin φ := by linarith [hs.1]
  have hdom {y : ℝ} (hy : y∈Icc (13/20:ℝ) EdgeThreeAligned.B1) : y∈Icc 0 outerDiagonal :=
    ⟨by linarith [hy.1],hy.2.trans EdgeThreeAligned.B1_domain.2⟩
  have hc : ConcaveOn ℝ (Icc (13/20:ℝ) EdgeThreeAligned.B1) (fun y => FB y (Real.pi/2)) :=
    concave_of_deriv2 (fun y hy => FB_hasDerivAt (hdom hy))
      (fun y hy => FBB_hasDerivAt (hdom hy))
      (fun y hy => (FBBB_negative (φ := Real.pi/2) (hdom hy)).le)
  have hpos := concave_gt_of_endpoints hc hB reference_65 reference_unit
  have hr := (outer_ratio_bounds hBf).1
  have hp := mul_nonneg (show 0≤g*ratio B by dsimp [g,EdgeThreeAligned.gp]; linarith)
    (show 0≤1-Real.sin φ by linarith [hs.2.1])
  have hquot : g*ratio B≤g*ratio B/Real.sin φ := by
    apply (le_div_iff₀ hsin).2
    nlinarith
  norm_num [FB] at hpos
  dsimp [HB]
  linarith

lemma original_lower {b A B φ : ℝ} (ht : OuterState A B) (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤-(7/12)*Real.cos φ+b*Real.sin φ+A) :
    H B φ≤value b B φ := by
  have hs : 0<Real.sin φ := by linarith [(lower_trig hφ).1]
  have ha := (ShortOuterOne.SameContact.actual_arc ht).1
  have hsource : source B φ≤b := by
    apply (div_le_iff₀ hs).2
    dsimp [LPrimaryZero.U,PrimaryZero.U,PrimaryZero.m]
    rw [ha]
    linarith
  have hp := mul_le_mul_of_nonneg_left hsource (by norm_num [g,EdgeThreeAligned.gp] : 0≤g)
  dsimp [H,value,EdgeThreeAligned.positiveCost]
  linarith

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Primary
end
end
end

section
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
end
end
end
