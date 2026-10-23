module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeTargetTwoCornerGeometry

/-!
# Exact derivatives of the polynomial corner lower cost

The source polynomial is applied only after the original-height
comparison. Every derivative below is of that explicit relaxed scalar,
on the complete canonical core corner. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeTarget.Corner
open CommonQuarter CorePairGeometry Arithmetic

def f (B φ : ℝ) : ℝ := φ+PHeightTaylor.poly (u B φ)+MixedThree.negativeCore (MixedCorner.a B) B
def fB (B φ : ℝ) : ℝ := -PHeightTaylor.d1 (u B φ)*L B φ+h*MixedCorner.w B+g-2*z*B
def fBB (B φ : ℝ) : ℝ := PHeightTaylor.d2 (u B φ)*(L B φ)^2-
  (PHeightTaylor.d1 (u B φ)*Real.cos φ-h)*D B-2*z
def fAngle (B φ : ℝ) : ℝ := 1-PHeightTaylor.d1 (u B φ)*speed B φ
def fAngleD (B φ : ℝ) : ℝ := PHeightTaylor.d2 (u B φ)*(speed B φ)^2-
  PHeightTaylor.d1 (u B φ)*(u B φ-1)
def fBBAngle (B φ : ℝ) : ℝ := -PHeightTaylor.c3*speed B φ*(L B φ)^2+
  2*PHeightTaylor.d2 (u B φ)*L B φ*N B φ+
  D B*(PHeightTaylor.d2 (u B φ)*speed B φ*Real.cos φ+PHeightTaylor.d1 (u B φ)*Real.sin φ)

lemma u_core_hasDerivAt {B φ : ℝ} (hB : B∈MixedCorner.domain) :
    HasDerivAt (fun B => u B φ) (-L B φ) B := by
  convert ((((MixedCorner.a_hasDerivAt hB).add_const (1/2)).mul_const (Real.cos φ)).const_add 1).sub
    (((hasDerivAt_id B).sub_const (1/2)).mul_const (Real.sin φ)) using 1 <;> dsimp [u,L] <;> ring

lemma L_core_hasDerivAt {B φ : ℝ} (hB : B∈MixedCorner.domain) :
    HasDerivAt (fun B => L B φ) (D B*Real.cos φ) B := by
  convert ((MixedCorner.w_hasDerivAt hB).mul_const (Real.cos φ)).const_add (Real.sin φ) using 1 <;>
    dsimp [L,D] <;> ring

lemma u_angle_hasDerivAt (B φ : ℝ) : HasDerivAt (u B) (-speed B φ) φ := by
  convert ((((Real.hasDerivAt_cos φ).const_mul (MixedCorner.a B+1/2)).const_add 1).sub
    ((Real.hasDerivAt_sin φ).const_mul (B-1/2))) using 1 <;> dsimp [u,speed] <;> ring

lemma speed_hasDerivAt (B φ : ℝ) : HasDerivAt (speed B) (u B φ-1) φ := by
  convert ((Real.hasDerivAt_sin φ).const_mul (MixedCorner.a B+1/2)).add
    ((Real.hasDerivAt_cos φ).const_mul (B-1/2)) using 1 <;> dsimp [u,speed] <;> ring

lemma L_angle_hasDerivAt (B φ : ℝ) : HasDerivAt (L B) (N B φ) φ := by
  convert (Real.hasDerivAt_sin φ).add ((Real.hasDerivAt_cos φ).const_mul (MixedCorner.w B)) using 1 <;>
    dsimp [L,N] <;> ring

lemma f_core_hasDerivAt {B φ : ℝ} (hB : B∈MixedCorner.domain) :
    HasDerivAt (fun B => f B φ) (fB B φ) B := by
  have hbase := (((MixedCorner.a_hasDerivAt hB).const_mul (-h)).const_add (11021/50000)).add
    ((hasDerivAt_id B).const_mul g)
  have hc := hbase.sub (((hasDerivAt_id B).pow 2).const_mul z)
  convert (((PHeightTaylor.poly_hasDerivAt (u B φ)).comp B (u_core_hasDerivAt hB)).const_add φ).add hc
    using 1 <;> dsimp [f,fB,MixedThree.negativeCore,h,g,z] <;> ring

lemma fB_hasDerivAt {B φ : ℝ} (hB : B∈MixedCorner.domain) :
    HasDerivAt (fun B => fB B φ) (fBB B φ) B := by
  have hd := ((((PHeightTaylor.d1_hasDerivAt (u B φ)).comp B
    (u_core_hasDerivAt hB)).mul (L_core_hasDerivAt hB)).neg).add
      ((MixedCorner.w_hasDerivAt hB).const_mul h)
  convert (hd.add_const g).sub ((hasDerivAt_id B).const_mul (2*z)) using 1 <;>
    dsimp [fB,fBB,D] <;> ring

lemma f_angle_hasDerivAt (B φ : ℝ) : HasDerivAt (f B) (fAngle B φ) φ := by
  convert ((hasDerivAt_id φ).add
    ((PHeightTaylor.poly_hasDerivAt (u B φ)).comp φ (u_angle_hasDerivAt B φ))).add_const
      (MixedThree.negativeCore (MixedCorner.a B) B) using 1 <;> dsimp [f,fAngle] <;> ring

lemma fAngle_hasDerivAt (B φ : ℝ) : HasDerivAt (fAngle B) (fAngleD B φ) φ := by
  convert ((((PHeightTaylor.d1_hasDerivAt (u B φ)).comp φ (u_angle_hasDerivAt B φ)).mul
    (speed_hasDerivAt B φ)).const_sub 1) using 1 <;> dsimp [fAngle,fAngleD] <;> ring

lemma fBB_angle_hasDerivAt (B φ : ℝ) : HasDerivAt (fBB B) (fBBAngle B φ) φ := by
  have hd := ((PHeightTaylor.d2_hasDerivAt (u B φ)).comp φ (u_angle_hasDerivAt B φ)).mul
    ((L_angle_hasDerivAt B φ).pow 2)
  have he := ((((PHeightTaylor.d1_hasDerivAt (u B φ)).comp φ (u_angle_hasDerivAt B φ)).mul
    (Real.hasDerivAt_cos φ)).sub_const h).mul_const (D B)
  convert (hd.sub he).sub_const (2*z) using 1 <;> dsimp [fBB,fBBAngle] <;> ring

lemma angle_curvature {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈angles) :
    (1/20:ℝ)<fAngleD B φ := by
  have hu := u_bounds hB hφ
  have hc := PHeightTaylor.curvature_lower
    (show u B φ∈Icc (133/100:ℝ) (17/10) from ⟨by linarith [hu.1],hu.2.le⟩)
  have hd := PHeightTaylor.d2_positive
    (show u B φ∈PHeightBounds.heights from ⟨by linarith [hu.1],by linarith [hu.2]⟩)
  have hm := (MixedCorner.endpoint_mass hB).1
  have hp := mul_nonneg hd.le (sub_nonneg.mpr hm)
  have he := congrArg (fun t : ℝ => PHeightTaylor.d2 (u B φ)*t) (harmonic_circle B φ)
  dsimp [fAngleD,PHeightTaylor.curvature,PHeightTaylor.mass] at *
  nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeTarget.Corner
