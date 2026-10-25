module

public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveLowerPrimaryCurvature

/-!
# Eight squares: the increasing lower-primary axial reference

At
alignment the two literal tuples have the stated value and slope
reserves. Monotonicity of the original signed product J transports both
reserves through every feasible angle, without changing its endpoint.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerPrimary
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open ShortWord.MixedQuarter.Reference

theorem X_half : X (1/2)=X0 := root_half
theorem K_initial : K (1/2) 0=3/2 := by norm_num [K,z]
theorem V_initial : V (1/2) 0=T0 := by rw [V,K_initial,root_three_halves]
theorem T_initial : T (1/2) 0=X0 := by
  simp only [T, X_half, Real.cos_zero, Real.sin_zero]
  ring
theorem J_initial_formula (r : Bool) : J r 0=(p r+q r*(3/2)/T0)*X0 := by
  rw [J,coefficient,K_initial,V_initial,T_initial]
theorem value_initial_formula (r : Bool) :
    value r (1/2) 0=Real.pi/2+cShift r+p r*(3/2)-q r*T0-P r*X0-t r/2 := by
  rw [value,K_initial,V_initial,X_half]
  ring
theorem slope_initial_formula (r : Bool) :
    targetFirst r (1/2) 0=p r+q r*(3/2)/T0+P r/(2*X0)-t r := by
  rw [reference_slope,J_initial_formula]
  field_simp [show X0≠0 by linarith [X0_bounds.1]]

private theorem r85_cast_lo {a b : ℝ} (e : a=b) (h : Interval a=Interval b) (I : Interval b) :
    (h.mpr I).lo=I.lo := by
  subst e
  rfl

def X0Box : Interval X0 := Interval.of_bounds ⟨X0_bounds.1.le,X0_bounds.2.le⟩
def T0Box : Interval T0 := Interval.of_bounds ⟨T0_bounds.1.le,T0_bounds.2.le⟩
def JBox (r : Bool) : Interval (J r 0) := by
  rw [J_initial_formula]
  exact ((Interval.point (p r)).add
    ((Interval.point (q r*(3/2))).div T0Box (by norm_num [T0Box,Interval.of_bounds]))).mul X0Box
def valueBox (r : Bool) : Interval (value r (1/2) 0) := by
  rw [value_initial_formula]
  exact (((((halfPi.add (Interval.point (cShift r))).add (Interval.point (p r*(3/2)))).sub
    ((Interval.point (q r)).mul T0Box)).sub ((Interval.point (P r)).mul X0Box)).sub (Interval.point (t r/2)))
def slopeBox (r : Bool) : Interval (targetFirst r (1/2) 0) := by
  rw [slope_initial_formula]
  exact (((Interval.point (p r)).add
    ((Interval.point (q r*(3/2))).div T0Box (by norm_num [T0Box,Interval.of_bounds]))).add
      ((Interval.point (P r)).div ((Interval.point 2).mul X0Box)
        (by norm_num [X0Box,Interval.of_bounds,Interval.mul,Interval.point]))).sub (Interval.point (t r))

theorem initial_J (r : Bool) : (143/100:ℝ)<J r 0 := by
  have hh : (143/100:ℝ)<(JBox r).lo := by
    unfold JBox
    rw [r85_cast_lo (J_initial_formula r)]
    cases r <;> dsimp [X0Box,T0Box,p,q,pQ,qQ] <;> mixed_fixed
  exact hh.trans_le (JBox r).mem.1
theorem initial_value (r : Bool) : (4493/5000:ℝ)<value r (1/2) 0 := by
  have hh : (4493/5000:ℝ)<(valueBox r).lo := by
    unfold valueBox
    rw [r85_cast_lo (value_initial_formula r)]
    cases r <;> dsimp [X0Box,T0Box,cShift,c,p,q,P,t,pQ,qQ,PQ,tQ] <;> mixed_fixed
  exact hh.trans_le (valueBox r).mem.1
theorem initial_slope (r : Bool) : -(3/125:ℝ)<targetFirst r (1/2) 0 := by
  have hh : -(3/125:ℝ)<(slopeBox r).lo := by
    unfold slopeBox
    rw [r85_cast_lo (slope_initial_formula r)]
    cases r <;> dsimp [X0Box,T0Box,p,q,P,t,pQ,qQ,PQ,tQ] <;> mixed_fixed
  exact hh.trans_le (slopeBox r).mem.1

theorem reference_J (r : Bool) {u : ℝ} (hd : Domain (1/2) u) : (143/100:ℝ)<J r u :=
  (initial_J r).trans_le (J_monotone r hd ⟨le_rfl,hd.1.1⟩ ⟨hd.1.1,le_rfl⟩ hd.1.1)
theorem reference_value (r : Bool) {u : ℝ} (hd : Domain (1/2) u) :
    (4493/5000:ℝ)<value r (1/2) u := by
  have hm : MonotoneOn (value r (1/2)) (Icc 0 u) :=
    monoOn_of_hasDeriv_nonneg
      (fun v hv => (value_angle_hasDerivAt r (angle_interval hd hv)).continuousAt.continuousWithinAt)
      (fun v hv => value_angle_hasDerivAt r (angle_interval hd (Ioo_subset_Icc_self hv)))
      (fun v hv => by
        have hh := reference_J r (angle_interval hd (Ioo_subset_Icc_self hv))
        dsimp [J] at hh
        linarith)
  exact (initial_value r).trans_le (hm ⟨le_rfl,hd.1.1⟩ ⟨hd.1.1,le_rfl⟩ hd.1.1)
theorem reference_slope_lower (r : Bool) {u : ℝ} (hd : Domain (1/2) u) :
    -(3/125:ℝ)<targetFirst r (1/2) u := by
  have hm := J_monotone r hd ⟨le_rfl,hd.1.1⟩ ⟨hd.1.1,le_rfl⟩ hd.1.1
  have hh := div_le_div_of_nonneg_right hm (show 0≤X0 by linarith [X0_bounds.1])
  have h0 := initial_slope r
  rw [reference_slope] at h0 ⊢
  linarith

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerPrimary
