module

public import SquaresInCircles.Eight.Owners.Endpoint.MixedStress
public import SquaresInCircles.Eight.Owners.Stronger.EndpointScalars

/-!
# Eight squares: the unchanged mixed stress at coefficient 41/40

These are algebraic reexpressions of the original
circle-support identities. Only the charged objective changes. Every
original E coordinate and weak mixed witness stays in the formula.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.StrongerEndpointStress
open EndpointBudgetScalars EndpointECharge StrongerEndpointScalars

def objective (H D : SignedPoint) (u v : ℝ) : ℝ := H.y-D.y-charge*(u+v)

theorem two_rotated {H D E : SignedPoint} {l u v : ℝ}
    (hyH : 0≤H.y) (hyD : D.y≤0) (hcH : H.circle≤qCap) (hcD : D.circle≤qCap)
    (hl : 0≤l) (hu : |u|≤frameCap) (hv : |v|≤frameCap)
    (hDE : quarterFeasible D E u 2) (hEH : quarterFeasible E H v 0) :
    objective H D u v≤baseline l+defect l u+defect l v := by
  have hh := EndpointMixedStress.two_rotated hyH hyD hcH hcD hl hu hv hDE hEH
  dsimp [objective,EndpointMixedStress.objective,defect,charge,EndpointRotationPenalty.charge] at *
  linarith

theorem rotated_D_primary_H {H D E : SignedPoint} {l u v : ℝ}
    (hyH : 0≤H.y) (hyD : D.y≤0) (hcH : H.circle≤qCap) (hcD : D.circle≤qCap)
    (hl : 0≤l) (hu : |u|≤frameCap) (hv : |v|≤frameCap)
    (hDE : quarterFeasible D E u 2) (hEH : quarterFeasible E H v 1) :
    objective H D u v≤baseline l+defect l u+l*JH E v-charge*v := by
  have hh := EndpointMixedStress.rotated_D_primary_H hyH hyD hcH hcD hl hu hv hDE hEH
  dsimp [objective,EndpointMixedStress.objective,defect,charge,EndpointRotationPenalty.charge] at *
  linarith

theorem primary_D_rotated_H {H D E : SignedPoint} {l u v : ℝ}
    (hyH : 0≤H.y) (hyD : D.y≤0) (hcH : H.circle≤qCap) (hcD : D.circle≤qCap)
    (hl : 0≤l) (hu : |u|≤frameCap) (hv : |v|≤frameCap)
    (hDE : quarterFeasible D E u 3) (hEH : quarterFeasible E H v 0) :
    objective H D u v≤baseline l+defect l v+l*JD E u-charge*u := by
  have hh := EndpointMixedStress.primary_D_rotated_H hyH hyD hcH hcD hl hu hv hDE hEH
  dsimp [objective,EndpointMixedStress.objective,defect,charge,EndpointRotationPenalty.charge] at *
  linarith

theorem primary_sum {H D : SignedPoint} {l j u v : ℝ}
    (hyH : 0≤H.y) (hyD : D.y≤0) (hcH : H.circle≤qCap) (hcD : D.circle≤qCap)
    (hl : 0≤l) (hprimary : 2-j≤H.a+D.a) :
    objective H D u v≤baseline l+l*j-charge*(u+v) := by
  have hh := EndpointMixedStress.primary_sum (u := u) (v := v) hyH hyD hcH hcD hl hprimary
  dsimp [objective,EndpointMixedStress.objective,charge,EndpointRotationPenalty.charge] at *
  linarith

end SquaresInCircles.Eight.StrongerEndpointStress
