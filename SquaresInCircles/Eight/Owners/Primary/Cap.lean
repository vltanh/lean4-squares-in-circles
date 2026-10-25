module

public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.Endpoint.Principles
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: the intrinsic flat-core primary cap

The cap is exactly the GA1 contact equation for aG=7/12 and negative
GA error. Its sole terminal parameter is an actual zero-tangent contact,
constructed by the intermediate value theorem. No discrete cover is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace PrimaryCap

def K : ℝ := 13/12

def value (P x : ℝ) : ℝ := (P-K*Real.sin x)/Real.cos x

def derivative (P x : ℝ) : ℝ :=
  (P*Real.sin x-K)/(Real.cos x)^2

def contactHeight (x : ℝ) : ℝ := Real.cos x/2+K*Real.sin x

def contactDerivative (x : ℝ) : ℝ := -Real.sin x/2+K*Real.cos x

@[simp] theorem value_zero (P : ℝ) : value P 0=P := by
  simp [value]

@[simp] theorem contactHeight_zero : contactHeight 0=1/2 := by
  norm_num [contactHeight]

theorem value_contact_identity (P x : ℝ) (hc : Real.cos x ≠ 0) :
    value P x * Real.cos x+K*Real.sin x=P := by
  simp [value,hc]

theorem value_hasDerivAt (P x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt (value P) (derivative P x) x := by
  have hd := ((hasDerivAt_const x P).fun_sub ((Real.hasDerivAt_sin x).const_mul K)).fun_div
    (Real.hasDerivAt_cos x) hc
  refine hd.congr_deriv ?_
  unfold derivative
  congr 1
  linear_combination (-K)*Real.sin_sq_add_cos_sq x

theorem derivative_rewrite (P x : ℝ) (hc : Real.cos x ≠ 0) :
    derivative P x=value P x*Real.tan x-K := by
  unfold derivative value
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  linear_combination K*Real.sin_sq_add_cos_sq x

theorem contactHeight_hasDerivAt (x : ℝ) :
    HasDerivAt contactHeight (contactDerivative x) x := by
  exact ((Real.hasDerivAt_cos x).div_const 2).fun_add ((Real.hasDerivAt_sin x).const_mul K)

theorem contact_derivative_positive {x : ℝ} (hx : x ∈ Icc 0 (7/10 : ℝ)) :
    39/80 < contactDerivative x := by
  obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse hx
  unfold contactDerivative K
  linarith

theorem contactHeight_strictMono : StrictMonoOn contactHeight (Icc 0 (7/10 : ℝ)) := by
  apply strict_increase_of_reserve (df := contactDerivative) (k := 39/80)
  · exact fun x _ => (contactHeight_hasDerivAt x).continuousAt.continuousWithinAt
  · intro x _
    exact contactHeight_hasDerivAt x
  · norm_num
  · intro x hx
    exact (contact_derivative_positive (Ioo_subset_Icc_self hx)).le

theorem contactHeight_ge_half {x : ℝ} (hx : x ∈ Icc 0 (7/10 : ℝ)) :
    1/2 ≤ contactHeight x := by
  have h := contactHeight_strictMono.monotoneOn
    (show (0:ℝ)∈Icc 0 (7/10) by constructor <;> norm_num) hx hx.1
  simpa using h

theorem contactHeight_endpoint : 183/200 < contactHeight (9/20) := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := (9/20 : ℝ))
  have hs := Real.sin_ge_sub_cube (show (0:ℝ) ≤ 9/20 by norm_num)
  have hr := primary_cap_endpoint_reserve
  unfold contactHeight K
  linarith

theorem cap_eq_half_iff {P x : ℝ} (hx : x ∈ Icc 0 (7/10 : ℝ)) :
    value P x=1/2 ↔ contactHeight x=P := by
  have hc := transport_cos_pos (by rw [abs_of_nonneg hx.1]; exact hx.2)
  have hi := value_contact_identity P x hc.ne'
  unfold contactHeight
  constructor <;> intro h <;> nlinarith

theorem derivative_negative_reserve {P x : ℝ}
    (hP : 0 ≤ P ∧ P ≤ 183/200) (hx : x ∈ Icc 0 (7/10 : ℝ)) :
    derivative P x < -(1/4) := by
  obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse hx
  have hcpos : 0 < Real.cos x := by linarith
  have hmul := mul_le_mul hP.2 hs.le hs0 (by norm_num : (0:ℝ)≤183/200)
  have hsq : (Real.cos x)^2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq x]
  unfold derivative K
  rw [div_lt_iff₀ (sq_pos_of_pos hcpos)]
  nlinarith

theorem value_strictAnti {P : ℝ} (hP : 0 ≤ P ∧ P ≤ 183/200) :
    StrictAntiOn (value P) (Icc 0 (7/10 : ℝ)) := by
  have hm : StrictMonoOn (fun x => -value P x) (Icc 0 (7/10 : ℝ)) := by
    apply strict_increase_of_reserve
      (df := fun x => -derivative P x) (k := 1/4)
    · apply ContinuousOn.neg
      intro x hx
      exact (value_hasDerivAt P x
        (transport_cos_pos (by rw [abs_of_nonneg hx.1]; exact hx.2)).ne').continuousAt.continuousWithinAt
    · intro x hx
      exact (value_hasDerivAt P x
        (transport_cos_pos (by rw [abs_of_nonneg hx.1.le]; exact hx.2.le)).ne').neg
    · norm_num
    · intro x hx
      have hd := derivative_negative_reserve hP (Ioo_subset_Icc_self hx)
      linarith
  intro x hx y hy hxy
  have h := hm hx hy hxy
  linarith

theorem value_le_position {P x : ℝ}
    (hP : 0 ≤ P ∧ P ≤ 183/200) (hx : x ∈ Icc 0 (7/10 : ℝ)) :
    value P x ≤ P := by
  have h := (value_strictAnti hP).antitoneOn
    (show (0:ℝ)∈Icc 0 (7/10) by constructor <;> norm_num) hx hx.1
  simpa using h

/-- The endpoint is determined by the contact equation, not by a mesh. -/
theorem exists_unique_zero_tangent {P : ℝ}
    (hPlo : 1/2 < P) (hPhi : P < 183/200) :
    ∃! z, z ∈ Ioo 0 (9/20 : ℝ) ∧ value P z=1/2 := by
  have hc : ContinuousOn contactHeight (Icc 0 (9/20 : ℝ)) :=
    fun x _ => (contactHeight_hasDerivAt x).continuousAt.continuousWithinAt
  have himage : P ∈ contactHeight '' Icc 0 (9/20 : ℝ) := by
    apply intermediate_value_Icc (by norm_num) hc
    constructor
    · simpa using hPlo.le
    · exact hPhi.le.trans contactHeight_endpoint.le
  obtain ⟨z,hz,hval⟩ := himage
  have hz0 : 0 < z := by
    by_contra! h
    have he : z=0 := le_antisymm h hz.1
    simp [he] at hval
    linarith
  have hzu : z < 9/20 := by
    by_contra! h
    have he : z=9/20 := le_antisymm hz.2 h
    rw [he] at hval
    linarith [contactHeight_endpoint]
  have hzwide : z ∈ Icc 0 (7/10 : ℝ) := ⟨hz.1,by linarith [hz.2]⟩
  refine ⟨z,⟨⟨hz0,hzu⟩,(cap_eq_half_iff hzwide).2 hval⟩,?_⟩
  intro w hw
  have hwwide : w ∈ Icc 0 (7/10 : ℝ) := ⟨hw.1.1.le,by linarith [hw.1.2]⟩
  have hwval := (cap_eq_half_iff hwwide).1 hw.2
  exact contactHeight_strictMono.injOn hwwide hzwide (hwval.trans hval.symm)

/-- On the full allowed angle interval, feasibility ends at that unique contact. -/
theorem cap_feasible_iff_before {P z x : ℝ}
    (hP : 1/2 < P ∧ P < 183/200)
    (hz : z ∈ Ioo 0 (9/20 : ℝ)) (hzval : value P z=1/2)
    (hx : x ∈ Icc 0 (7/10 : ℝ)) :
    1/2 ≤ value P x ↔ x ≤ z := by
  have hzwide : z ∈ Icc 0 (7/10 : ℝ) := ⟨hz.1.le,by linarith [hz.2]⟩
  have ha := value_strictAnti (P := P) ⟨by linarith [hP.1],hP.2.le⟩
  constructor
  · intro h
    by_contra! hgt
    have hh := ha hzwide hx hgt
    linarith
  · intro h
    have hh := ha.antitoneOn hx hzwide h
    linarith

/-- The shifted flat-core point on the exact primary contact. -/
def point (P x : ℝ) : SignedPoint := ⟨7/12,-(value P x-1/2)⟩

theorem point_geometric {P x q : ℝ}
    (hP : 1/2 < P ∧ P < 183/200)
    (hx : x ∈ Icc 0 (7/10 : ℝ)) (hcap : 1/2 ≤ value P x)
    (hq : 5/2 < q) :
    (point P x).Sorted ∧ (point P x).Core ∧
      (point P x).AvoidsCore ∧ (point P x).circle < q := by
  have hupper := value_le_position ⟨by linarith [hP.1],hP.2.le⟩ hx
  have hb : |-(value P x-1/2)| ≤ 1/2 := by
    rw [abs_neg,abs_of_nonneg (by linarith : 0≤value P x-1/2)]
    linarith [hP.2]
  have hpoint : point P x=SignedPoint.flat (-(value P x-1/2)) := rfl
  have hs := SignedPoint.flat_sorted hb
  have hc := SignedPoint.flat_on_core hb
  rw [hpoint]
  refine ⟨hs,hc,hc.ge,?_⟩
  have hid : (SignedPoint.flat (-(value P x-1/2))).circle=K^2+value P x^2 := by
    show (7/12+1/2)^2+(|(-(value P x-1/2))|+1/2)^2=K^2+value P x^2
    rw [abs_neg,abs_of_nonneg (by linarith : 0≤value P x-1/2)]
    unfold K
    ring
  rw [hid]
  have hsq := pow_le_pow_left₀ (by linarith : 0≤value P x) (hupper.trans hP.2.le) 2
  have hr := flat_core_corner_reserve
  unfold K
  linarith

theorem actual_primary_contact {P x : ℝ} {A : SignedPoint}
    (hA : A.a=P+1/2) (hx : x ∈ Icc 0 (7/10 : ℝ)) :
    quarterProjection (point P x) A (-x) 1=edgeWidth (-x) := by
  have hc := transport_cos_pos (by rw [abs_of_nonneg hx.1]; exact hx.2)
  have hid := value_contact_identity P x hc.ne'
  rw [edgeWidth_negative_formula hx]
  simp [quarterProjection,point,hA,Real.sin_neg,Real.cos_neg]
  unfold K at hid
  nlinarith

end PrimaryCap
end SquaresInCircles.Eight