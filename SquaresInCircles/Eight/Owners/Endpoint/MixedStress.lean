module

public import SquaresInCircles.Eight.Owners.Endpoint.ECharge

/-!
# Eight squares: the four original mixed-owner stresses on H, D, E

The actual H and D circles are each supported
once.  A rotated owner retains its exact signed norm increment.  A
primary owner retains its actual E remainder.  These identities allow
all four weak DE/EH owner pairs without moving or relabeling E.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EndpointMixedStress
open PositiveAngularEnvelope EndpointRotationPenalty EndpointBudgetScalars EndpointECharge

def objective (H D : SignedPoint) (u v : ℝ) : ℝ := H.y-D.y-charge*(u+v)

theorem corner_support {X Y : ℝ} (hc : X^2+Y^2≤qCap) (l r : ℝ) :
    l*Real.cos r*X+(1+l*Real.sin r)*Y≤R*pairNorm l 1 r := by
  have hc' : normSq (X,Y)≤R^2 := by simpa [normSq,R_sq] using hc
  have h := dot_le_radius (v := rotatedPair l 1 0 r) R_nonneg hc'
  have hn : vectorLength (rotatedPair l 1 0 r)=pairNorm l 1 r := by
    simpa [vectorLength,normSq] using rotatedPair_norm l 1 0 r
  rw [hn] at h
  simpa [dot,rotatedPair,add_comm] using h

theorem positive_corner {H : SignedPoint} (hy : 0≤H.y) (hc : H.circle≤qCap)
    (l r : ℝ) :
    l*Real.cos r*(H.a+1/2)+(1+l*Real.sin r)*(H.y+1/2)≤R*pairNorm l 1 r := by
  apply corner_support
  simpa [SignedPoint.circle,abs_of_nonneg hy] using hc

theorem negative_corner {D : SignedPoint} (hy : D.y≤0) (hc : D.circle≤qCap)
    (l r : ℝ) :
    l*Real.cos r*(D.a+1/2)+(1+l*Real.sin r)*(-D.y+1/2)≤R*pairNorm l 1 r := by
  apply corner_support
  simpa [SignedPoint.circle,abs_of_nonpos hy] using hc

theorem two_rotated {H D E : SignedPoint} {l u v : ℝ}
    (hyH : 0≤H.y) (hyD : D.y≤0) (hcH : H.circle≤qCap) (hcD : D.circle≤qCap)
    (hl : 0≤l) (hu : |u|≤frameCap) (hv : |v|≤frameCap)
    (hDE : quarterFeasible D E u 2) (hEH : quarterFeasible E H v 0) :
    objective H D u v≤baseline l+defect l u+defect l v := by
  have hH := positive_corner hyH hcH l v
  have hD := negative_corner hyD hcD l u
  have hDE' : edgeWidth u≤D.a*Real.cos u-D.y*Real.sin u-E.y := by
    simpa [quarterFeasible,quarterProjection] using hDE
  have hEH' : edgeWidth v≤E.y+H.a*Real.cos v+H.y*Real.sin v := by
    simpa [quarterFeasible,quarterProjection] using hEH
  have hDEw := mul_le_mul_of_nonneg_left hDE' hl
  have hEHw := mul_le_mul_of_nonneg_left hEH' hl
  have hwu := congrArg (fun z : ℝ => l*z) (width_add_half_phi hu)
  have hwv := congrArg (fun z : ℝ => l*z) (width_add_half_phi hv)
  dsimp [objective,baseline,defect,PositiveAngularEnvelope.phi] at *
  nlinarith

theorem rotated_D_primary_H {H D E : SignedPoint} {l u v : ℝ}
    (hyH : 0≤H.y) (hyD : D.y≤0) (hcH : H.circle≤qCap) (hcD : D.circle≤qCap)
    (hl : 0≤l) (hu : |u|≤frameCap) (hv : |v|≤frameCap)
    (hDE : quarterFeasible D E u 2) (hEH : quarterFeasible E H v 1) :
    objective H D u v≤baseline l+defect l u+l*JH E v-charge*v := by
  have hH := positive_corner hyH hcH l 0
  have hD := negative_corner hyD hcD l u
  simp only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero,one_mul] at hH
  have hDE' : edgeWidth u≤D.a*Real.cos u-D.y*Real.sin u-E.y := by
    simpa [quarterFeasible,quarterProjection] using hDE
  have hEH' : edgeWidth v≤H.a+E.a*Real.sin v+E.y*Real.cos v := by
    simpa [quarterFeasible,quarterProjection] using hEH
  have hDEw := mul_le_mul_of_nonneg_left hDE' hl
  have hEHw := mul_le_mul_of_nonneg_left hEH' hl
  have hwu := congrArg (fun z : ℝ => l*z) (width_add_half_phi hu)
  have hwv := congrArg (fun z : ℝ => l*z) (width_add_half_phi hv)
  dsimp [objective,baseline,defect,JH,PositiveAngularEnvelope.phi,psi] at *
  nlinarith

theorem primary_D_rotated_H {H D E : SignedPoint} {l u v : ℝ}
    (hyH : 0≤H.y) (hyD : D.y≤0) (hcH : H.circle≤qCap) (hcD : D.circle≤qCap)
    (hl : 0≤l) (hu : |u|≤frameCap) (hv : |v|≤frameCap)
    (hDE : quarterFeasible D E u 3) (hEH : quarterFeasible E H v 0) :
    objective H D u v≤baseline l+defect l v+l*JD E u-charge*u := by
  have hH := positive_corner hyH hcH l v
  have hD := negative_corner hyD hcD l 0
  simp only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero,one_mul] at hD
  have hDE' : edgeWidth u≤D.a+E.a*Real.sin u-E.y*Real.cos u := by
    simpa [quarterFeasible,quarterProjection] using hDE
  have hEH' : edgeWidth v≤E.y+H.a*Real.cos v+H.y*Real.sin v := by
    simpa [quarterFeasible,quarterProjection] using hEH
  have hDEw := mul_le_mul_of_nonneg_left hDE' hl
  have hEHw := mul_le_mul_of_nonneg_left hEH' hl
  have hwu := congrArg (fun z : ℝ => l*z) (width_add_half_phi hu)
  have hwv := congrArg (fun z : ℝ => l*z) (width_add_half_phi hv)
  dsimp [objective,baseline,defect,JD,PositiveAngularEnvelope.phi,psi] at *
  nlinarith

theorem primary_sum {H D : SignedPoint} {l j u v : ℝ}
    (hyH : 0≤H.y) (hyD : D.y≤0) (hcH : H.circle≤qCap) (hcD : D.circle≤qCap)
    (hl : 0≤l) (hprimary : 2-j≤H.a+D.a) :
    objective H D u v≤baseline l+l*j-charge*(u+v) := by
  have hH := positive_corner hyH hcH l 0
  have hD := negative_corner hyD hcD l 0
  simp only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero,one_mul] at hH hD
  have hm := mul_le_mul_of_nonneg_left hprimary hl
  dsimp [objective,baseline]
  nlinarith

end SquaresInCircles.Eight.EndpointMixedStress
