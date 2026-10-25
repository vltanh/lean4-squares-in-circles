module

public import SquaresInCircles.Eight.TableFree.CanonicalNominalTails
public import SquaresInCircles.Eight.TableFree.StationaryCanonicalRigidity
public import SquaresInCircles.Eight.TableFree.GeometricStationaryExistence

/-!
# The complete canonical five-anchor sharp theorem

Uncompiled reconstruction.  The original inequalities first localize
the tilt.  The geometric existence theorem supplies the stationary
radius bounds.  Thus neither a local stationary enclosure nor an
assumed terminal tilt interval remains in these exports.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CanonicalNegativeSharp
open ExactFamily.FiveCornerGeometry CanonicalNegativeStress StationaryTerminal

theorem five_anchor_quantitative {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {H A B D E : SignedPoint} {q α t e : ℝ}
    (hq : q≤qTrial) (hαpos : 0<α) (hαmax : α≤27/100)
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) (hu : t+e≤α)
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y) (hyD : 0≤D.y) (hyE : 0≤E.y)
    (hc : ∀i : Fin 5,(![A,B,D,E,H] i).Contained q)
    (hHA : 1+W (α-t-e)≤H.y+A.a*Real.cos (α-t-e)-A.y*Real.sin (α-t-e))
    (hAB : 1≤A.y+B.y)
    (hBD : W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e≤
      D.y/Real.cos e+B.a*Real.cos t-B.y*Real.sin t)
    (hDE : 1≤D.a+E.y)
    (hEH : W α≤H.a+E.a*Real.sin α-E.y*Real.cos α) :
    d.q+(t+e)/5000+
      centerLoss (minimizingWeights d.q α) α t (α-t-e) e ![A,B,D,E,H]+
      circleLoss q (minimizingWeights d.q α) ![A,B,D,E,H]≤q := by
  have htilt := CanonicalNominal.five_anchor_tilt_range hq ⟨hαpos.le,hαmax⟩ hαpos
    ht he hr hyH hyA hyB hyD hyE hc hHA hAB hBD hDE hEH
  exact stationary_quantitative_bound (q:=q) hd (GeometricExistence.stationary_radius_strip hd)
    ⟨htilt.1.le,htilt.2.le⟩ ht he hr hu hyH hyA hyB hyD hyE hHA hAB hBD hDE hEH

theorem five_anchor_rigidity {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {H A B D E : SignedPoint} {q α t e : ℝ}
    (hqq : q≤d.q) (hαpos : 0<α) (hαmax : α≤27/100)
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) (hu : t+e≤α)
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y) (hyD : 0≤D.y) (hyE : 0≤E.y)
    (hc : ∀i : Fin 5,(![A,B,D,E,H] i).Contained q)
    (hHA : 1+W (α-t-e)≤H.y+A.a*Real.cos (α-t-e)-A.y*Real.sin (α-t-e))
    (hAB : 1≤A.y+B.y)
    (hBD : W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e≤
      D.y/Real.cos e+B.a*Real.cos t-B.y*Real.sin t)
    (hDE : 1≤D.a+E.y)
    (hEH : W α≤H.a+E.a*Real.sin α-E.y*Real.cos α) :
    q=d.q ∧ t=0 ∧ e=0 ∧ α=coordinateAngle d ∧
      (∀i : Fin 5,(![A,B,D,E,H] i).circle=d.q) ∧
      ![A,B,D,E,H]=nominalPoints d.q (-d.y) (Real.tan (coordinateAngle d)) := by
  have hq : q≤qTrial := hqq.trans (GeometricExistence.stationary_radius_ceiling hd).le
  have htilt := CanonicalNominal.five_anchor_tilt_range hq ⟨hαpos.le,hαmax⟩ hαpos
    ht he hr hyH hyA hyB hyD hyE hc hHA hAB hBD hDE hEH
  exact stationary_rigidity hd (GeometricExistence.stationary_radius_strip hd)
    hqq ⟨htilt.1.le,htilt.2.le⟩ ht he hr hu hyH hyA hyB hyD hyE hc hHA hAB hBD hDE hEH

end SquaresInCircles.Eight.TableFree.CanonicalNegativeSharp
