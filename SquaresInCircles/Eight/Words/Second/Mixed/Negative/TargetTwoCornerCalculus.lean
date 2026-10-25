module

public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.TargetTwoCornerGeometry
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.TargetTwoData
public import SquaresInCircles.Eight.Words.Second.Mixed.PHeightTaylorBounds

/-!
# Eight squares: exact derivatives of the polynomial corner lower cost

The source polynomial is applied only after the original-height
comparison. Every derivative below is of that explicit relaxed scalar,
on the complete canonical core corner.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Corner
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
  exact ((((MixedCorner.a_hasDerivAt hB).add_const (1/2)).mul_const (Real.cos φ)).const_add 1).sub
    (((hasDerivAt_id' B).sub_const (1/2)).mul_const (Real.sin φ))
    |>.congr_deriv (by dsimp only [L]; ring)

lemma L_core_hasDerivAt {B φ : ℝ} (hB : B∈MixedCorner.domain) :
    HasDerivAt (fun B => L B φ) (D B*Real.cos φ) B := by
  convert ((MixedCorner.w_hasDerivAt hB).mul_const (Real.cos φ)).const_add (Real.sin φ) using 1 <;>
    dsimp [L,D]

lemma u_angle_hasDerivAt (B φ : ℝ) : HasDerivAt (u B) (-speed B φ) φ := by
  exact ((((Real.hasDerivAt_cos φ).const_mul (MixedCorner.a B+1/2)).const_add 1).sub
    ((Real.hasDerivAt_sin φ).const_mul (B-1/2))) |>.congr_deriv (by dsimp only [speed]; ring)

lemma speed_hasDerivAt (B φ : ℝ) : HasDerivAt (speed B) (u B φ-1) φ := by
  exact ((Real.hasDerivAt_sin φ).const_mul (MixedCorner.a B+1/2)).add
    ((Real.hasDerivAt_cos φ).const_mul (B-1/2)) |>.congr_deriv (by dsimp only [u]; ring)

lemma L_angle_hasDerivAt (B φ : ℝ) : HasDerivAt (L B) (N B φ) φ := by
  exact (Real.hasDerivAt_sin φ).add ((Real.hasDerivAt_cos φ).const_mul (MixedCorner.w B))
    |>.congr_deriv (by dsimp only [N]; ring)

lemma f_core_hasDerivAt {B φ : ℝ} (hB : B∈MixedCorner.domain) :
    HasDerivAt (fun B => f B φ) (fB B φ) B := by
  have hc : HasDerivAt (fun x => MixedThree.negativeCore (MixedCorner.a x) x) _ B :=
    ((((MixedCorner.a_hasDerivAt hB).const_mul (8623/25000)).const_sub (11021/50000)).add
      ((hasDerivAt_id' B).const_mul (98439/100000))).sub
        (((hasDerivAt_id' B).pow 2).const_mul (2667/50000))
  have hf := (((PHeightTaylor.poly_hasDerivAt (u B φ)).comp B
    (u_core_hasDerivAt (φ := φ) hB)).const_add φ).add hc
  convert hf using 1
  · funext x
    simp only [f,Pi.add_apply,Function.comp_apply]
  · simp only [fB,h,g,z,Nat.cast_ofNat]
    ring

lemma fB_hasDerivAt {B φ : ℝ} (hB : B∈MixedCorner.domain) :
    HasDerivAt (fun B => fB B φ) (fBB B φ) B := by
  exact (((((PHeightTaylor.d1_hasDerivAt (u B φ)).comp B
    (u_core_hasDerivAt (φ := φ) hB)).neg.mul (L_core_hasDerivAt (φ := φ) hB)).add
      ((MixedCorner.w_hasDerivAt hB).const_mul h)).add_const g).sub
        ((hasDerivAt_id' B).const_mul (2*z)) |>.congr_deriv (by
      simp only [fBB,D,Function.comp_apply,Pi.neg_apply]
      ring)

lemma f_angle_hasDerivAt (B φ : ℝ) : HasDerivAt (f B) (fAngle B φ) φ := by
  exact ((hasDerivAt_id' φ).add
    ((PHeightTaylor.poly_hasDerivAt (u B φ)).comp φ (u_angle_hasDerivAt B φ))).add_const
      (MixedThree.negativeCore (MixedCorner.a B) B) |>.congr_deriv (by
      simp only [fAngle]
      ring)

lemma fAngle_hasDerivAt (B φ : ℝ) : HasDerivAt (fAngle B) (fAngleD B φ) φ := by
  exact (((PHeightTaylor.d1_hasDerivAt (u B φ)).comp φ (u_angle_hasDerivAt B φ)).mul
    (speed_hasDerivAt B φ)).const_sub 1 |>.congr_deriv (by
      simp only [fAngleD,Function.comp_apply]
      ring)

lemma fBB_angle_hasDerivAt (B φ : ℝ) : HasDerivAt (fBB B) (fBBAngle B φ) φ := by
  have hd := ((PHeightTaylor.d2_hasDerivAt (u B φ)).comp φ (u_angle_hasDerivAt B φ)).mul
    ((L_angle_hasDerivAt B φ).pow 2)
  have he := ((((PHeightTaylor.d1_hasDerivAt (u B φ)).comp φ (u_angle_hasDerivAt B φ)).mul
    (Real.hasDerivAt_cos φ)).sub_const h).mul_const (D B)
  exact (hd.sub he).sub_const (2*z) |>.congr_deriv (by
      simp only [fBBAngle,Function.comp_apply,Pi.pow_apply,Nat.cast_ofNat]
      ring)

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

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Corner
