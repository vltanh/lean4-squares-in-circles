module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterOuterNegativeEndpointReferences

/-!
# The whole-height source curvature ratio

Uncompiled transcription of equation (13). A single concave denominator
has positive endpoint reserves, so M'' < 2.8 M' on the entire continued
height range. The actual source-circle derivative is retained.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative.Ratio
open CommonQuarter Arithmetic StationaryPrimitives Reference

def D (u : ℝ) : ℝ := (Q0-u^2)*(u-(263/1000)*v u)
def D1 (u : ℝ) : ℝ := Q0-3*u^2+(789/1000)*u*v u
def D2 (u : ℝ) : ℝ := -6*u+(789/1000)*(Q0-2*u^2)/v u

theorem height_radicand {u : ℝ} (hu : HeightRange u) : 0<Q0-u^2 := by
  have h := source_radicand (height_source_domain hu)
  simp only [sub_add_cancel] at h
  linarith
theorem D_hasDerivAt {u : ℝ} (hu : HeightRange u) : HasDerivAt D (D1 u) u := by
  have hv := height_v_bounds hu
  have he := Real.sq_sqrt (height_radicand hu).le
  change (v u)^2=Q0-u^2 at he
  have hvp : 0<v u := by linarith [hv.1]
  have h1 : HasDerivAt (fun x : ℝ => Q0-x^2) (-(↑2*u^(2-1))) u :=
    (hasDerivAt_pow 2 u).const_sub Q0
  have h2 : HasDerivAt (fun x : ℝ => x-(263/1000)*v x) (1-(263/1000)*(-u/v u)) u :=
    (hasDerivAt_id' u).sub ((v_hasDerivAt (height_radicand hu)).const_mul (263/1000))
  refine (h1.mul h2).congr_deriv ?_
  rw [D1,show Q0=(v u)^2+u^2 by linarith]
  field_simp
  ring
theorem D1_hasDerivAt {u : ℝ} (hu : HeightRange u) : HasDerivAt D1 (D2 u) u := by
  have hv := height_v_bounds hu
  have he := Real.sq_sqrt (height_radicand hu).le
  change (v u)^2=Q0-u^2 at he
  have hvp : 0<v u := by linarith [hv.1]
  have h := (((hasDerivAt_pow 2 u).const_mul 3).const_sub Q0).fun_add
    (((hasDerivAt_id' u).const_mul (789/1000)).fun_mul (v_hasDerivAt (height_radicand hu)))
  refine h.congr_deriv ?_
  rw [D2,show Q0=(v u)^2+u^2 by linarith]
  field_simp
  ring
theorem D2_negative {u : ℝ} (hu : HeightRange u) : D2 u<0 := by
  have hv := height_v_bounds hu
  have hvp : 0<v u := by linarith [hv.1]
  have hu2 := mul_nonneg (show 0≤u-33/25 by linarith [hu.1])
    (show 0≤u+33/25 by linarith [hu.1])
  have huv := mul_le_mul (show (33/25:ℝ)≤u from hu.1) hv.1.le
    (by norm_num : (0:ℝ)≤101/100) (by linarith [hu.1] : 0≤u)
  have hid : D2 u*v u= -6*u*v u+(789/1000)*(Q0-2*u^2) := by
    rw [D2,add_mul,div_mul_cancel₀ _ hvp.ne']
  have hn : D2 u*v u<0 := by
    rw [hid]
    norm_num [Q0]
    nlinarith
  by_contra h
  have hp := mul_nonneg (le_of_not_gt h) hvp.le
  linarith
theorem concave : ConcaveOn ℝ (Icc (33/25) (17/10)) D :=
  concave_of_deriv2 (fun u hu => D_hasDerivAt hu) (fun u hu => D1_hasDerivAt hu)
    (fun u hu => (D2_negative hu).le)

def endpointV (right : Bool) : Interval (v (if right then 17/10 else 33/25)) := by
  let U := Interval.point (if right then (17/10:ℝ) else 33/25)
  exact rootSix ((Interval.point Q0).sub U.square) (3/2) (by norm_num)
    (by cases right <;> dsimp [U] <;> mixed_fixed)
def endpointD (right : Bool) : Interval (D (if right then 17/10 else 33/25)) := by
  let U := Interval.point (if right then (17/10:ℝ) else 33/25)
  exact ((Interval.point Q0).sub U.square).mul
    (U.sub ((Interval.point (263/1000)).mul (endpointV right)))
theorem endpoint_reserve (right : Bool) : Q0/(14/5)<D (if right then 17/10 else 33/25) := by
  have hh : Q0/(14/5)<(endpointD right).lo := by
    cases right <;> dsimp [endpointD,endpointV] <;> mixed_fixed
  exact hh.trans_le (endpointD right).mem.1
theorem denominator_lower {u : ℝ} (hu : HeightRange u) : Q0/(14/5)<D u := by
  apply concave_gt_of_endpoints concave hu
  · simpa using endpoint_reserve false
  · simpa using endpoint_reserve true

theorem source_ratio (r : Row) (hr : Remaining r) {a : ℝ} (ha : HeightRange (a+1/2)) :
    M2 r a<(14/5)*M1 r a := by
  have hd : SourceDomain a := by simpa using height_source_domain ha
  have hc := coefficients r hr
  have hv := source_v_positive hd
  have hv3 := pow_pos hv 3
  have he := source_v_square hd
  have hD := denominator_lower ha
  have hq : 0<ocQ r := by linarith [hc.1]
  have hp := mul_lt_mul_of_pos_right hc.2.2.2.1 hv3
  have hD' : Q0<D (a+1/2)*(14/5) := (div_lt_iff₀ (by norm_num)).mp hD
  have hM1 : M1 r a*(v (a+1/2))^3=
      ocP r*(v (a+1/2))^3+ocQ r*(a+1/2)*(Q0-(a+1/2)^2) := by
    simp only [M1]
    rw [←he]
    generalize v (a+1/2) = w at hv ⊢
    field_simp
  have hM2 : M2 r a*(v (a+1/2))^3=ocQ r*Q0 := by
    dsimp [M2]
    exact div_mul_cancel₀ _ hv3.ne'
  have hDform : D (a+1/2)=(a+1/2)*(Q0-(a+1/2)^2)-(263/1000)*(v (a+1/2))^3 := by
    dsimp [D]
    rw [←he]
    ring
  rw [hDform] at hD'
  have hDen := mul_lt_mul_of_pos_left hD' hq
  have hprod : M2 r a*(v (a+1/2))^3<((14/5)*M1 r a)*(v (a+1/2))^3 := by
    rw [hM2,mul_assoc,hM1]
    linarith
  exact (mul_lt_mul_iff_of_pos_right hv3).mp hprod

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative.Ratio
