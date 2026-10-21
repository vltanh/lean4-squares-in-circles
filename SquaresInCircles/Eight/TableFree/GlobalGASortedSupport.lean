module

public import SquaresInCircles.Eight.TableFree.GlobalGARadicals
public import SquaresInCircles.Eight.TableFree.SignedStress

/-!
# The actual sorted-circle support for the high-GA stress

Uncompiled source.  These bounds use the source point's circle
inequality at its actual radius.  The axial and diagonal alternatives
are proved from supporting lines of that circle, so no maximizing
point or replacement radial label is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
open PositiveAngularEnvelope

def fullSupport (f g : ℝ) : ℝ := R*Real.sqrt (f^2+g^2)-(f+g)/2

def diagonalSupport (f g : ℝ) : ℝ := (f+g)*diagonal

/-- The circle clipped only by the sorting half-plane.  In the D
domain the axial endpoint is inactive; the upper bound itself does
not require that separate geometric fact. -/
def clippedSupport (f g : ℝ) : ℝ :=
  if f≤g then diagonalSupport f g else fullSupport f g

theorem axial_circle : (axial+1/2)^2+(1/2:ℝ)^2=qCap := by
  have h := Real.sq_sqrt (show 0≤qCap-1/4 by norm_num [qCap])
  dsimp [axial]
  nlinarith

theorem diagonal_circle : 2*(diagonal+1/2)^2=qCap := by
  have h := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
  dsimp [diagonal,diagonalCoordinate]
  nlinarith

theorem actual_coordinate_bounds {q : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : 0≤P.y) (hc : P.Contained q) (hq : q≤qCap) :
    P.a≤axial ∧ P.y≤diagonal ∧ P.a+P.y≤2*diagonal := by
  have hcircle : (P.a+1/2)^2+(P.y+1/2)^2≤qCap := by
    simpa [SignedPoint.circle,abs_of_nonneg hy] using hc.trans hq
  have hsort : P.y≤P.a := by simpa [abs_of_nonneg hy] using hs.2
  have ha0 : 0<axial+1/2 := by linarith [axial_bounds.1]
  have hd0 : 0<diagonal+1/2 := by linarith [diagonal_bounds.1]
  have ha : P.a≤axial := by
    nlinarith [axial_circle,sq_nonneg P.y,hs.1]
  have hy' : P.y≤diagonal := by
    have hm := mul_nonneg (sub_nonneg.mpr hsort)
      (show 0≤P.a+P.y+1 by linarith [hs.1])
    nlinarith [diagonal_circle]
  have hsum : P.a+P.y≤2*diagonal := by
    nlinarith [diagonal_circle,sq_nonneg (P.a-P.y),hs.1]
  exact ⟨ha,hy',hsum⟩

theorem actual_full_support {q f g : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained q) (hq : q≤qCap) :
    f*P.a+g*P.y≤fullSupport f g := by
  have hc' : P.Contained (R^2) := by rw [radius_sq]; exact hc.trans hq
  have h := SignedStress.work_le_signed_support (Real.sqrt_nonneg qCap) hc'
    (sign:=1) (Or.inl rfl) (by simp [abs_of_nonneg hy]) (f,g)
  simpa [SignedStress.work,fullSupport] using h

theorem actual_axial_support {q f g : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained q) (hq : q≤qCap)
    (hf : 0≤f) (haxis : (axial+1/2)*g≤f/2) :
    f*P.a+g*P.y≤f*axial := by
  have hcircle : (P.a+1/2)^2+(P.y+1/2)^2≤qCap := by
    simpa [SignedPoint.circle,abs_of_nonneg hy] using hc.trans hq
  have htangent : (axial+1/2)*(P.a-axial)+P.y/2≤0 := by
    nlinarith [axial_circle,sq_nonneg (P.a-axial),sq_nonneg P.y]
  have hfprod := mul_nonpos_of_nonneg_of_nonpos hf htangent
  have hgprod := mul_nonpos_of_nonpos_of_nonneg
    (show (axial+1/2)*g-f/2≤0 by linarith) hy
  have hpositive : 0<axial+1/2 := by linarith [axial_bounds.1]
  nlinarith

theorem actual_diagonal_support {q f g : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : 0≤P.y) (hc : P.Contained q) (hq : q≤qCap)
    (hfg : f≤g) (hsum : 0≤f+g) :
    f*P.a+g*P.y≤diagonalSupport f g := by
  have hb := actual_coordinate_bounds hs hy hc hq
  have hsort : P.y≤P.a := by simpa [abs_of_nonneg hy] using hs.2
  have hfirst := mul_le_mul_of_nonneg_left hb.2.2 hsum
  have hsecond := mul_nonneg (sub_nonneg.mpr hfg) (sub_nonneg.mpr hsort)
  dsimp [diagonalSupport]
  nlinarith

theorem actual_clipped_support {q f g : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : 0≤P.y) (hc : P.Contained q) (hq : q≤qCap)
    (hsum : 0≤f+g) : f*P.a+g*P.y≤clippedSupport f g := by
  unfold clippedSupport
  split_ifs with hfg
  · exact actual_diagonal_support hs hy hc hq hfg hsum
  · exact actual_full_support hy hc hq

theorem full_at_diagonal {f g : ℝ} (he : f=g) (hsum : 0≤f+g) :
    fullSupport f g=diagonalSupport f g := by
  have hN := Real.sqrt_nonneg (f^2+g^2)
  have hN2 := Real.sq_sqrt (show 0≤f^2+g^2 by positivity)
  have hR := Real.sqrt_nonneg qCap
  have hd : 0≤diagonal+1/2 := by linarith [diagonal_bounds.1]
  have hp : 0≤R*Real.sqrt (f^2+g^2) := mul_nonneg hR hN
  have hq : 0≤(f+g)*(diagonal+1/2) := mul_nonneg hsum hd
  have hsq : (R*Real.sqrt (f^2+g^2))^2=((f+g)*(diagonal+1/2))^2 := by
    rw [mul_pow,mul_pow,radius_sq,hN2]
    rw [he]
    nlinarith [congrArg (fun x : ℝ => g^2*x) diagonal_circle]
  have hprod : R*Real.sqrt (f^2+g^2)=(f+g)*(diagonal+1/2) := by
    nlinarith
  dsimp [fullSupport,diagonalSupport]
  linarith

theorem fullSupport_pair (p q : ℝ) :
    fullSupport q p=R*pairNorm p q 0-(p+q)/2 := by
  simp [fullSupport,pairNorm_zero,add_comm]

end SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
