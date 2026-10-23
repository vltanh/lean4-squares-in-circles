module

public import SquaresInCircles.Eight.TableFree.SecondMixedEdgeThreePositiveUpper
public import SquaresInCircles.Eight.TableFree.SecondOuterConcaveSlope

/-!
# The original positive-core transverse comparison

The relaxed source coordinate is used only as a lower bound on the
original source. Its first derivative is concave on the complete
physical target arc. Both the circle and every label remain at Q0.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource
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
  convert (((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).const_mul (Real.sin φ)).const_sub
    ((1+Real.sin φ+Real.cos φ)/2)).add
      ((hasDerivAt_id B).const_mul (Real.cos φ)) using 1 <;> dsimp [source] <;> ring

lemma F_hasDerivAt {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (fun z => F z φ) (FB B φ) B := by
  convert (((source_hasDerivAt (φ := φ) hB).const_mul g).const_add (φ-e)).sub
    (LLabel.outer_hasDerivAt (outer_domain hB)) using 1 <;> dsimp [F,FB,L] <;> ring

lemma FB_hasDerivAt {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (fun z => FB z φ) (FBB B φ) B := by
  convert ((((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).const_mul (Real.sin φ)).add_const
    (Real.cos φ)).const_mul g).sub (LLabel.d1_hasDerivAt (outer_domain hB)) using 1 <;>
    dsimp [FB,FBB] <;> ring

lemma FBB_hasDerivAt {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (fun z => FBB z φ) (FBBB B φ) B := by
  convert (((ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hB)).const_mul g).mul_const
    (Real.sin φ)).sub (LLabel.d2_hasDerivAt (outer_domain hB)) using 1 <;>
    dsimp [FBB,FBBB] <;> ring

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
  concave_of_deriv2 (fun B hB => FB_hasDerivAt hB)
    (fun B hB => FBB_hasDerivAt hB) (fun B hB => (FBBB_negative (φ := φ) hB).le)

lemma FBB_antitone (φ : ℝ) : AntitoneOn (fun B => FBB B φ) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun B hB => (FBB_hasDerivAt (φ := φ) hB).continuousAt.continuousWithinAt)
    (fun B hB => FBB_hasDerivAt (φ := φ) (Ioo_subset_Icc_self hB))
    (fun B hB => (FBBB_negative (φ := φ) (Ioo_subset_Icc_self hB)).le)

lemma FB_angle_hasDerivAt (B φ : ℝ) : HasDerivAt (FB B)
    (g*(ratio B*Real.cos φ-Real.sin φ)) φ := by
  have hd := (((Real.hasDerivAt_sin φ).const_mul (ratio B)).add
    (Real.hasDerivAt_cos φ)).const_mul g
  convert hd.sub_const (LLabel.d1 B) using 1 <;> dsimp [FB] <;> ring

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
  have hA := (actual_arc ht).1
  have hp := mul_le_mul_of_nonneg_left hsep (by norm_num [g,EdgeThreeAligned.gp] : 0≤g)
  dsimp [F,source,value,EdgeThreeAligned.positiveCost]
  rw [hA]
  nlinarith

lemma diagonal_lower {φ : ℝ} (hφ : Lower φ) : γ<F outerDiagonal φ := by
  let f : ℝ→ℝ := fun θ => F outerDiagonal θ
  let fd : ℝ→ℝ := fun θ => 1+g*(1/2-outerDiagonal)*Real.cos θ-
    g*(1/2+outerDiagonal)*Real.sin θ
  have hf (θ : ℝ) : HasDerivAt f (fd θ) θ := by
    convert (((((Real.hasDerivAt_sin θ).const_mul (1/2-outerDiagonal)).add
      ((Real.hasDerivAt_cos θ).const_mul (1/2+outerDiagonal))).const_mul g).add
        (hasDerivAt_id θ)).add_const (g/2-e-L outerDiagonal) using 1 <;>
      dsimp [f,fd,F,source] <;> simp only [ShortOuterOne.SameContact.arc_diagonal] <;> ring
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
  norm_num [f,F,source,ShortOuterOne.SameContact.arc_diagonal] at he
  dsimp [γ,EdgeThreeAligned.threshold]
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource
