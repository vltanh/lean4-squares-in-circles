module

public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveAxial
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveLowerSecondaryCurvature
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveLowerSecondarySlope

/-!
# Eight squares: both full lower secondary owners on opposite edge five

The whole axial polynomial, the whole-angle slope comparison, and
the actual contact curvature combine by the stated completed square.
The result starts with the original two states and the weak owner.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerSecondary
open CommonQuarter CorePairGeometry Arithmetic

theorem contact_lower (r : Bool) {v u : ℝ} (hd : Domain v u) (hx : half u≤halfCap) :
    threshold<cost r v u := by
  have hvalue := Axial.lower r (small_angle hd.1) hx
  have hslope := first_axial_lower r hd.1
  have htangent := tangent r hd
  have hfirst := mul_le_mul_of_nonneg_right hslope.le
    (show 0≤v-1/2 by linarith [hd.2.1.1])
  have hsquare := sq_nonneg (v-1/2-2/95)
  dsimp [threshold]
  nlinarith only [hvalue,htangent,hfirst,hsquare]

theorem original (r : Bool) {a b A B u : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hu : u∈Icc 0 (7/10))
    (hm : width u≤-b+A*Real.cos u-B*Real.sin u) :
    threshold<Real.pi/2-u+c+p r*a-q r*b-P r*A-t r*B := by
  have hd := contact_domain hs ht hu hm
  have hhalf := forced_half_cap hu (feasible hs ht hu hm)
  exact (contact_lower r hd hhalf.le).trans_le (original_to_contact r hs ht hu hm)

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerSecondary
