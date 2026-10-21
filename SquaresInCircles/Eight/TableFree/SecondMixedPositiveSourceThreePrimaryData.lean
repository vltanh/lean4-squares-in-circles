module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveSourceThreeSupport
public import SquaresInCircles.Eight.TableFree.SecondMixedLEnvelopes

/-!
# Whole-target derivative shape for the positive source side

The exact side relaxation has a concave first derivative on the full
target circle. Its diagonal endpoint decreases to the proved aligned
pair. The derivative is positive at every late zero-source endpoint.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource.Primary
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
  convert (((((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).const_sub
    (LPrimaryZero.U φ-1/2)).div_const (Real.sin φ)).const_mul g).const_add (φ-e)).sub
      (LLabel.outer_hasDerivAt (outer_domain hB)) using 1 <;> dsimp [H,source,HB,L] <;> ring

lemma HB_hasDerivAt {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (fun z => HB z φ) (HBB B φ) B := by
  convert (((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).const_mul g).div_const
    (Real.sin φ)).sub (LLabel.d1_hasDerivAt (outer_domain hB)) using 1 <;> dsimp [HB,HBB] <;> ring

lemma HBB_hasDerivAt {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (fun z => HBB z φ) (HBBB B φ) B := by
  convert (((ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hB)).const_mul g).div_const
    (Real.sin φ)).sub (LLabel.d2_hasDerivAt (outer_domain hB)) using 1 <;> dsimp [HBB,HBBB] <;> ring

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
  have hd := (((PrimaryZero.U_hasDerivAt φ).sub_const (1/2+outerDiagonal)).div
    (Real.hasDerivAt_sin φ) hs).const_mul g
  have hd0 := ((hasDerivAt_id φ).sub_const e).add hd
  convert hd0.sub_const (L outerDiagonal) using 1
  · ext y
    dsimp [H,source,LPrimaryZero.U]
    rw [ShortOuterOne.SameContact.arc_diagonal]
    ring
  · dsimp [PrimaryZero.U,PrimaryZero.m,PrimaryZero.v]
    field_simp [hs]
    linear_combination -g*(Real.sin_sq_add_cos_sq φ)

lemma diagonal_lower {φ : ℝ} (hφ : Lower φ) : γ<H outerDiagonal φ := by
  have hneg {θ : ℝ} (hθ : Lower θ) :
      1+g*((outerDiagonal-1/2)*Real.cos θ-13/12)/(Real.sin θ)^2<0 := by
    have ht := lower_trig hθ
    have hs : 0<(Real.sin θ)^2 := sq_pos_of_pos (by linarith [ht.1])
    apply (mul_lt_mul_right hs).mp
    have he : (1+g*((outerDiagonal-1/2)*Real.cos θ-13/12)/(Real.sin θ)^2)*
        (Real.sin θ)^2=(Real.sin θ)^2+g*(outerDiagonal-1/2)*Real.cos θ-13*g/12 := by
      field_simp [ne_of_gt (by linarith [ht.1] : 0<Real.sin θ)]
      ring
    rw [he]
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
  norm_num [H,source,LPrimaryZero.U,PrimaryZero.U,PrimaryZero.m,
    ShortOuterOne.SameContact.arc_diagonal] at hh
  dsimp [γ,EdgeThreeAligned.threshold]
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
    dsimp [ratio,U]
    field_simp [hU.ne']
    ring
  have hr0 := (outer_ratio_bounds hb).1
  have hpaid := mul_le_mul_of_nonneg_left hr.2.le (by linarith : 0≤ratio (13/20))
  norm_num [FB,g,EdgeThreeAligned.gp]
  nlinarith

lemma reference_unit : 0<FB EdgeThreeAligned.B1 (Real.pi/2) := by
  have hb := EdgeThreeAligned.B1_bounds
  have hA := (actual_arc EdgeThreeAligned.unit_state).1
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
  have ha := (actual_arc ht).1
  have hsource : source B φ≤b := by
    apply (div_le_iff₀ hs).2
    dsimp [LPrimaryZero.U,PrimaryZero.U,PrimaryZero.m]
    rw [ha]
    linarith
  have hp := mul_le_mul_of_nonneg_left hsource (by norm_num [g,EdgeThreeAligned.gp] : 0≤g)
  dsimp [H,value,EdgeThreeAligned.positiveCost]
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource.Primary
