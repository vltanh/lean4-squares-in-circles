module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2AffectedPositive
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2SecantBounds
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2AffectedJoin

/-!
# The two exact affected negative curves in the secant coordinate

Uncompiled transcription of (62)--(64). The larger-secant branch is
affine minus the original rotated norm. The other branch retains its
square root and cosine quotient, including both exact derivatives.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.AffectedNegativeCurves
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open SecantCoordinate

def cosine (z x : ℝ) : ℝ := (Real.cos z+x*Real.sin z)/radical 1 x
def upper (r z x : ℝ) : ℝ :=
  Real.cos z+(13/12+Real.sin z)*x-R*AffectedNorm.norm r z x
def lower (r z x : ℝ) : ℝ :=
  radical 1 x+(13/12)*x+r*(cosine z x-1)-R*AffectedNorm.norm r z x
def upperFirst (r z x : ℝ) : ℝ := 13/12+Real.sin z-R*AffectedNorm.first r z x
def lowerFirst (r z x : ℝ) : ℝ :=
  x/radical 1 x+13/12+r*(Real.sin z-x*Real.cos z)/(radical 1 x)^3-R*AffectedNorm.first r z x
def lowerSecond (r z x : ℝ) : ℝ :=
  1/(radical 1 x)^3+r*(-Real.cos z*(1-2*x^2)-3*x*Real.sin z)/(radical 1 x)^5-
    R*AffectedNorm.second r z x

theorem cosine_arctan (z x : ℝ) : cosine z x=Real.cos (z-Real.arctan x) := by
  rw [Real.cos_sub,Real.cos_arctan,Real.sin_arctan]
  dsimp [cosine,radical]
  ring

theorem cosine_le_one (z x : ℝ) : cosine z x≤1 := by
  rw [cosine_arctan]
  exact Real.cos_le_one _

theorem cosine_hasDerivAt (z x : ℝ) :
    HasDerivAt (cosine z) ((Real.sin z-x*Real.cos z)/(radical 1 x)^3) x := by
  have hW := radical_positive (A:=1) (x:=x) (by norm_num)
  have hW2 := radical_square (A:=1) (x:=x) (by norm_num)
  have hd := (((hasDerivAt_id' x).mul_const (Real.sin z)).const_add (Real.cos z)).div
    (radical_hasDerivAt (A:=1) (by norm_num)) hW.ne'
  convert hd using 1
  · rfl
  · field_simp [hW.ne']
    nlinarith [congrArg (fun a : ℝ => a*Real.sin z) hW2]

theorem cosineFirst_hasDerivAt (z x : ℝ) :
    HasDerivAt (fun x => (Real.sin z-x*Real.cos z)/(radical 1 x)^3)
      ((-Real.cos z*(1-2*x^2)-3*x*Real.sin z)/(radical 1 x)^5) x := by
  have hW := radical_positive (A:=1) (x:=x) (by norm_num)
  have hW2 := radical_square (A:=1) (x:=x) (by norm_num)
  have hd := (((hasDerivAt_id' x).mul_const (Real.cos z)).const_sub (Real.sin z)).fun_div
    ((radical_hasDerivAt (A:=1) (by norm_num)).fun_pow 3) (pow_ne_zero 3 hW.ne')
  convert hd using 1
  simp only [Nat.cast_ofNat,show (3:ℕ)-1=2 from rfl]
  field_simp [hW.ne']
  nlinarith [congrArg (fun a : ℝ => a*Real.cos z) hW2]

theorem upper_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (upper r z) (upperFirst r z x) x := by
  convert (((hasDerivAt_id x).const_mul (13/12+Real.sin z)).const_add
    (Real.cos z)).sub ((AffectedNorm.norm_hasDerivAt hv).const_mul R) using 1
  · rfl
  · dsimp [upperFirst]
    ring

theorem upperFirst_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (upperFirst r z) (-R*AffectedNorm.second r z x) x := by
  convert ((AffectedNorm.first_hasDerivAt hv).const_mul R).const_sub
    (13/12+Real.sin z) using 1
  · rfl
  · ring

theorem lower_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (lower r z) (lowerFirst r z x) x := by
  have hd := (((radical_hasDerivAt (A:=1) (x:=x) (by norm_num)).add
    ((hasDerivAt_id x).const_mul (13/12:ℝ))).add
      (((cosine_hasDerivAt z x).sub_const 1).const_mul r)).sub
        ((AffectedNorm.norm_hasDerivAt hv).const_mul R)
  convert hd using 1
  · rfl
  · dsimp [lowerFirst]
    ring

theorem lowerFirst_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (lowerFirst r z) (lowerSecond r z x) x := by
  have hd := (((radicalFirst_hasDerivAt (A:=1) (x:=x) (by norm_num)).add_const
    (13/12:ℝ)).add ((cosineFirst_hasDerivAt z x).const_mul r)).sub
      ((AffectedNorm.first_hasDerivAt hv).const_mul R)
  convert hd using 1
  · funext y
    simp only [lowerFirst,Pi.add_apply,Pi.sub_apply]
    ring
  · dsimp [lowerSecond]
    ring

theorem upper_concave {r z a b : ℝ} (hv : 0<1-r*Real.sin z) :
    ConcaveOn ℝ (Icc a b) (upper r z) := by
  apply concave_of_deriv2 (fun x _ => upper_hasDerivAt hv)
    (fun x _ => upperFirst_hasDerivAt hv)
  intro x hx
  have hn : 0≤AffectedNorm.second r z x := by
    exact div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) 3)
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.sqrt_nonneg qCap)) hn

theorem branch_difference (r z x : ℝ) :
    upper r z x-lower r z x=(radical 1 x-r)*(cosine z x-1) := by
  have hW := radical_positive (A:=1) (x:=x) (by norm_num)
  dsimp [upper,lower,cosine]
  field_simp [hW.ne']
  ring

theorem downward_derivative {r z x : ℝ} (hx : 0≤x) (he : radical 1 x=r) :
    upperFirst r z x≤lowerFirst r z x := by
  have hW := radical_positive (A:=1) (x:=x) (by norm_num)
  have hW2 := radical_square (A:=1) (x:=x) (by norm_num)
  have hid : upperFirst r z x-lowerFirst r z x=
      (x/radical 1 x)*(cosine z x-1) := by
    rw [←he]
    dsimp [upperFirst,lowerFirst,cosine]
    field_simp [hW.ne']
    nlinarith [congrArg (fun a : ℝ => a*Real.sin z) hW2]
  have hp := mul_nonpos_of_nonneg_of_nonpos (div_nonneg hx hW.le)
    (sub_nonpos.mpr (cosine_le_one z x))
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.AffectedNegativeCurves
