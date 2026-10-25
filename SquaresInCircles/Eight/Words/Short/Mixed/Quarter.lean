module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoCycle
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterCorePrimaryPositive
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterNegativeSide
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterNegativeEndpointReferences
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterPositive
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterPrimaryReduction
public import SquaresInCircles.Eight.Words.Short.WordZero

/-!
# Eight squares: complete original-cycle mixed quarter-one component of 0010111

The selected physical separator supplies one of the
four original forward owners. Its literal state coordinates and actual
signed markers enter the now-complete mixed-quarter owner theorem.
-/

section
/-!
## Every original core-to-outer normalized quarter contact

The secondary and primary owners (`core_secondary`, `core_primary`) cover every row. The signs
of a primary source are reduced by pointwise dominance on the unchanged source state; the cyclic
label itself stays the same.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter
open CommonQuarter CorePairGeometry

theorem core_secondary (r : Row) (upper : Bool) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourceSecondary r a b A B (angle upper x)) :
    (449/500:ℝ)<coreOuterCost r a b A B (angle upper x) := by
  cases hτ : targetPositive r
  · exact CoreSecondaryNegative.original r hτ upper hs ht hx hm
  · exact CoreSecondaryPositive.original r hτ upper hs ht hx hm

theorem core_primary (r : Row) (upper : Bool) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle upper x)) :
    (449/500:ℝ)<coreOuterCost r a b A B (angle upper x) := by
  have hσ := (primaryRow_signs r).1
  have hm' := (primary_constraint r a b A B (angle upper x)).2 hm
  have hred := core_cost_reduction (r:=r) (A:=A) (B:=B) (φ:=angle upper x) hs
  cases hτ : targetPositive (primaryRow r)
  · exact (CorePrimaryNegative.original (primaryRow r) hσ hτ upper hs ht hx hm').trans_le hred
  · exact (CorePrimaryPositive.original (primaryRow r) hσ hτ upper hs ht hx hm').trans_le hred

end SquaresInCircles.Eight.ShortWord.MixedQuarter
end
end
end

section
/-!
## The whole-height source curvature ratio

A single concave denominator `D` (`concave`) has positive endpoint reserves
(`endpoint_reserve`), so `M'' < 2.8 M'` on the whole continued height range (`source_ratio`).
The derivative of the source circle is kept exactly.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.Ratio
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
  concave_of_deriv2 (fun _ hu => D_hasDerivAt hu) (fun _ hu => D1_hasDerivAt hu)
    (fun _ hu => (D2_negative hu).le)

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

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.Ratio
end
end
end

section
/-!
## Every original lower-half negative-core corner contact

The source-label ratio and the
same corner slope in both derivative terms give strict concavity across
the whole corner. The original primary separator supplies the contact
height. The late portion uses the stated direct diagonal label bound.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.Corner
open CommonQuarter CorePairGeometry Arithmetic

def cost (r : Row) (φ B : ℝ) : ℝ := φ+ocC r+M r (contactPrimary B φ)+ocG r*B
def first (r : Row) (φ B : ℝ) : ℝ := -M1 r (contactPrimary B φ)*contactTangent B φ+ocG r
def second (r : Row) (φ B : ℝ) : ℝ :=
  M2 r (contactPrimary B φ)*(contactTangent B φ)^2-
    M1 r (contactPrimary B φ)*(Real.cos φ/SecondWord.MixedCorner.z B)*(1+(SecondWord.MixedCorner.w B)^2)

theorem cost_hasDerivAt (r : Row) {φ B : ℝ} (hφ : φ∈earlyAngles) (hB : B∈SecondWord.MixedCorner.domain) :
    HasDerivAt (cost r φ) (first r φ B) B := by
  have h := (((M_hasDerivAt r (contact_domain hB hφ)).comp B
    (contactPrimary_hasDerivAt_B hB)).const_add (φ+ocC r)).fun_add
      ((hasDerivAt_id' B).const_mul (ocG r))
  exact h.congr_deriv (by simp only [first]; ring)
theorem first_hasDerivAt (r : Row) {φ B : ℝ} (hφ : φ∈earlyAngles) (hB : B∈SecondWord.MixedCorner.domain) :
    HasDerivAt (first r φ) (second r φ B) B := by
  have h := ((((M1_hasDerivAt r (contact_domain hB hφ)).comp B
    (contactPrimary_hasDerivAt_B hB)).fun_neg).fun_mul (contactTangent_hasDerivAt_B (φ:=φ) hB)).add_const
      (ocG r)
  exact h.congr_deriv (by simp only [second,contactTangent,Function.comp]; ring)

theorem second_negative (r : Row) (hr : Remaining r) {φ B : ℝ}
    (hφ : φ∈earlyAngles) (hB : B∈SecondWord.MixedCorner.domain) : second r φ B<0 := by
  have hM := M1_positive r hr (contact_domain hB hφ)
  have hratio := Ratio.source_ratio r hr (contact_height_range hB hφ)
  have hcos := early_cosine hφ
  have hz := SecondWord.MixedCorner.z_positive hB
  have hzU := (SecondWord.MixedCorner.chart_bounds hB).2.1
  have hnorm : (contactTangent B φ)^2≤1+(SecondWord.MixedCorner.w B)^2 := by
    have he : (contactTangent B φ)^2+(Real.cos φ-SecondWord.MixedCorner.w B*Real.sin φ)^2=
        1+(SecondWord.MixedCorner.w B)^2 := by
      dsimp [contactTangent]
      linear_combination (1+(SecondWord.MixedCorner.w B)^2)*(Real.sin_sq_add_cos_sq φ)
    nlinarith [sq_nonneg (Real.cos φ-SecondWord.MixedCorner.w B*Real.sin φ)]
  have hpay : (14/5:ℝ)<Real.cos φ/SecondWord.MixedCorner.z B :=
    (lt_div_iff₀ hz).2 (by linarith)
  have hfirst := mul_le_mul_of_nonneg_right hratio.le (sq_nonneg (contactTangent B φ))
  have hnext := mul_le_mul_of_nonneg_left hnorm (show 0≤(14/5)*M1 r (contactPrimary B φ) by positivity)
  have hstrict := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hpay hM)
    (show 0<1+(SecondWord.MixedCorner.w B)^2 by positivity)
  dsimp [second]
  nlinarith

theorem lower (r : Row) (hr : Remaining r) {φ B : ℝ}
    (hφ : φ∈earlyAngles) (hB : B∈SecondWord.MixedCorner.domain) : (89809/100000:ℝ)<cost r φ B := by
  have hc : ConcaveOn ℝ SecondWord.MixedCorner.domain (cost r φ) :=
    concave_of_deriv2 (fun B hB => cost_hasDerivAt r hφ hB)
      (fun B hB => first_hasDerivAt r hφ hB)
      (fun B hB => (second_negative r hr hφ hB).le)
  have hj := Endpoint.lower r hr false hφ
  have hd := Endpoint.lower r hr true hφ
  have hjoin : Endpoint.H r false φ=cost r φ (1/2) := by
    rw [Endpoint.H,Endpoint.height_contact]
    simp [cost,Endpoint.bC]
  have hdiag : Endpoint.H r true φ=cost r φ CoreAngleEndpoint.diagonal := by
    rw [Endpoint.H,Endpoint.height_contact]
    simp [cost,Endpoint.bC]
  exact concave_gt_of_endpoints hc hB (hjoin ▸ hj) (hdiag ▸ hd)

theorem original_early (r : Row) (hr : Remaining r) {a b A B φ : ℝ}
    (hs : OuterState a b) (hB : 1/2≤B) (hBA : B≤A)
    (hc : (A-1/2)^2+(B-1/2)^2=(1/12:ℝ)^2) (hφ : φ∈earlyAngles)
    (hm : sourcePrimary r a b A B φ) : (89809/100000:ℝ)<outerCoreCost r a b A B φ := by
  obtain ⟨hdom,hA⟩ := SecondWord.MixedCorner.actual hB hBA hc
  have hheight := actual_height r hr hdom hA hφ hm
  have hM := M_monotone r hr (contact_domain hdom hφ) (actual_source_domain hs) hheight
  have hcost := lower r hr hφ hdom
  have hsid := source_identity r hs
  rw [primary_cost r hr]
  dsimp [cost] at hcost
  linarith

theorem late_reference (r : Row) (hr : Remaining r) :
    (183/200:ℝ)<6/5+ocC r+(ocP r-ocQ r)*outerDiagonal+ocG r/2 := by
  have hd := ShortMixedZero.fine_diagonal_bounds
  rcases (remaining_iff r).1 hr with rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [ocC,ocP,ocQ,ocG] <;> linarith [hd.1,hd.2]

theorem original_late (r : Row) (hr : Remaining r) {a b A B φ : ℝ}
    (hs : OuterState a b) (hB : 1/2≤B) (hφ : (6/5:ℝ)≤φ) :
    (183/200:ℝ)<outerCoreCost r a b A B φ := by
  have hd : SourceDomain outerDiagonal :=
    ⟨by linarith [ShortMixedZero.fine_diagonal_bounds.1],
      by linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2]⟩
  have hM := M_monotone r hr hd (actual_source_domain hs) (outer_bounds hs).1
  rw [source_diagonal,source_identity r hs] at hM
  have hg := mul_le_mul_of_nonneg_left hB (coefficients r hr).2.1.le
  rw [primary_cost r hr]
  linarith [late_reference r hr]

theorem original_lower (r : Row) (hr : Remaining r) {a b A B x : ℝ}
    (hs : OuterState a b) (hB : 1/2≤B) (hBA : B≤A)
    (hc : (A-1/2)^2+(B-1/2)^2=(1/12:ℝ)^2) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle false x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle false x) := by
  by_cases hφ : angle false x≤6/5
  · have he : angle false x∈earlyAngles := by
      refine ⟨?_,hφ⟩
      dsimp [angle,direction,lowerAngle]
      linarith [hx.2]
    have hh := original_early r hr hs hB hBA hc he hm
    linarith
  · have hh := original_late (A:=A) r hr hs hB (le_of_not_ge hφ)
    linarith

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.Corner
end
end
end

section
/-!
## The two small-slope side families and their intrinsic diagonal event

The only transition is where the active side join reaches the original
source diagonal. The source label decreases along the original active
contact until that diagonal or the target side join is reached.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.SmallSide
open CommonQuarter CorePairGeometry Arithmetic Reference

def Rows (r : Row) : Prop := r=0∨r=11
def c0 : ℝ := 13/12
def eventSine : ℝ := (outerDiagonal-1/2)/c0
def IsEvent (e : ℝ) : Prop := e∈Icc 0 (2/5) ∧ Real.sin e=eventSine
def height (x B : ℝ) : ℝ := 1/2+c0*Real.sin x+(1/2-B)*Real.cos x
def cost (r : Row) (x B : ℝ) : ℝ := angle false x+ocC r+M r (height x B)+ocG r*B
def first (r : Row) (x B : ℝ) : ℝ := -M1 r (height x B)*Real.cos x+ocG r
def diagonalB (x : ℝ) : ℝ :=
  1/2-(outerDiagonal-1/2)/Real.cos x+c0*(Real.sin x/Real.cos x)
def diagonalCost (r : Row) (x : ℝ) : ℝ :=
  angle false x+ocC r+(ocP r-ocQ r)*outerDiagonal+ocG r*diagonalB x
def diagonalFirst (r : Row) (x : ℝ) : ℝ :=
  -1+ocG r*(c0-(outerDiagonal-1/2)*Real.sin x)/(Real.cos x)^2

theorem rows_remaining (r : Row) (hr : Rows r) : Remaining r := by
  rcases hr with rfl|rfl <;> norm_num [Remaining,sourcePositive,targetPositive]
theorem coefficient_reserves (r : Row) (hr : Rows r) :
    0<ocP r+ocQ r ∧ ocG r≤251/400 ∧
      ocG r<(191/250)*(ocP r+ocQ r) := by
  rcases hr with rfl|rfl <;> norm_num [ocP,ocQ,ocG]

theorem eventSine_bounds : 0<eventSine ∧ eventSine<37/100 := by
  have hd := ShortMixedZero.fine_diagonal_bounds
  dsimp [eventSine,c0]
  constructor <;> linarith [hd.1,hd.2]
theorem event_exists : ∃e,IsEvent e := by
  have hright : eventSine<Real.sin (2/5) :=
    eventSine_bounds.2.trans (by linarith [CorePrimaryPositive.sine_reference])
  obtain ⟨e,he,hzero⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤2/5)
    Real.continuous_sin.continuousOn
    (show eventSine∈Icc (Real.sin 0) (Real.sin (2/5)) by
      simpa using ⟨eventSine_bounds.1.le,hright.le⟩)
  exact ⟨e,he,hzero⟩
theorem event_domain {e : ℝ} (he : IsEvent e) : e∈Icc 0 (7/10) :=
  ⟨he.1.1,he.1.2.trans (by norm_num)⟩
theorem event_identity {e : ℝ} (he : IsEvent e) : c0*Real.sin e=outerDiagonal-1/2 := by
  rw [he.2]
  simp only [eventSine,c0]
  ring

theorem event_early {e : ℝ} (he : IsEvent e) : angle false e∈earlyAngles := by
  have hcos : Real.cos (6/5)<eventSine := by
    have hc := (cosine (by norm_num : (0:ℝ)≤6/5)).mem.2
    have hup : (cosine (by norm_num : (0:ℝ)≤6/5)).hi<(363/1000:ℝ) := by mixed_fixed
    have hd := ShortMixedZero.fine_diagonal_bounds.1
    dsimp [eventSine,c0]
    linarith
  have hp : Real.pi/2-6/5∈Icc 0 (7/10) := by
    constructor <;> linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]
  have hs : Real.sin (Real.pi/2-6/5)=Real.cos (6/5) := Real.sin_pi_div_two_sub (6/5)
  have hp_lt : Real.pi/2-6/5<e := by
    by_contra hn
    have hh := sin_mono (event_domain he) hp (le_of_not_gt hn)
    rw [he.2,hs] at hh
    linarith
  simp only [earlyAngles,angle,direction,lowerAngle,Bool.false_eq_true,↓reduceIte]
  constructor <;> linarith [he.1.2]

theorem height_antitone {x : ℝ} (hx : x∈Icc 0 (7/10)) : Antitone (height x) := by
  intro B D hBD
  have hc : 0≤Real.cos x := by linarith [(positive_trig hx).1]
  have hp := mul_le_mul_of_nonneg_right hBD hc
  dsimp [height]
  linarith
theorem height_zero {x : ℝ} (hx : x∈Icc 0 (7/10)) : 1≤height x 0 := by
  have ht := positive_trig hx
  have hc : 0≤Real.cos x := by linarith [ht.1]
  have hs : 0≤Real.sin x := ht.2.2.1
  have hsc := mul_nonneg hs hc
  have hu : 1≤Real.sin x+Real.cos x := by nlinarith [Real.sin_sq_add_cos_sq x]
  dsimp [height,c0]
  nlinarith
theorem diagonal_contact {x : ℝ} (hx : x∈Icc 0 (7/10)) : height x (diagonalB x)=outerDiagonal := by
  have hc : Real.cos x≠0 := ne_of_gt (by linarith [(positive_trig hx).1])
  dsimp [height,diagonalB]
  field_simp [hc]
  ring
theorem join_after_event {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    outerDiagonal≤height x (1/2) := by
  have hx0 : x∈Icc 0 (7/10) := ⟨(event_domain he).1.trans hx.1,hx.2⟩
  have hs := sin_mono (event_domain he) hx0 hx.1
  have hh := event_identity he
  dsimp [height,c0] at *
  nlinarith
theorem diagonal_at_event {e : ℝ} (he : IsEvent e) : diagonalB e=1/2 := by
  have hc : Real.cos e≠0 := ne_of_gt (by linarith [(positive_trig (event_domain he)).1])
  have hh := event_identity he
  dsimp [diagonalB]
  field_simp [hc]
  nlinarith

theorem source_slope (r : Row) (hr : Rows r) {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    ocP r+ocQ r≤M1 r a := by
  have hd : SourceDomain a := ⟨by linarith [ha.1,outer_endpoint_bounds.2.2.1],ha.2⟩
  have hv := source_v_positive hd
  have he := source_v_square hd
  have hu : 0≤a+1/2 := by linarith [ha.1,outer_endpoint_bounds.2.2.1]
  have hsq := mul_nonneg (sub_nonneg.mpr ha.1)
    (show 0≤a+outerDiagonal+1 by linarith [ha.1,outer_endpoint_bounds.2.2.1])
  have hratio : v (a+1/2)≤a+1/2 := by nlinarith [diagonal_circle]
  have hq : 0≤ocQ r := by linarith [(coefficients r (rows_remaining r hr)).1]
  have hp := mul_le_mul_of_nonneg_left hratio hq
  have hdiv : ocQ r≤ocQ r*(a+1/2)/v (a+1/2) := (le_div_iff₀ hv).2 hp
  dsimp [M1]
  linarith
theorem first_negative (r : Row) (hr : Rows r) {x B : ℝ}
    (hx : x∈Icc 0 (7/10)) (hh : height x B∈Icc outerDiagonal outerAxial) : first r x B<0 := by
  have hc := (positive_trig hx).1
  have hs := source_slope r hr hh
  have hp := mul_le_mul_of_nonneg_right hs (show 0≤Real.cos x by linarith)
  have hq := mul_lt_mul_of_pos_left hc (coefficient_reserves r hr).1
  dsimp [first]
  linarith [(coefficient_reserves r hr).1,(coefficient_reserves r hr).2.2]
theorem cost_hasDerivAt (r : Row) {x B : ℝ} (hh : SourceDomain (height x B)) :
    HasDerivAt (cost r x) (first r x B) B := by
  have hh' : HasDerivAt (height x) (-Real.cos x) B :=
    ((((hasDerivAt_id' B).const_sub (1/2)).mul_const (Real.cos x)).const_add
      (1/2+c0*Real.sin x)).congr_deriv (by ring)
  have h := (((M_hasDerivAt r hh).comp B hh').const_add (angle false x+ocC r)).fun_add
    ((hasDerivAt_id' B).const_mul (ocG r))
  exact h.congr_deriv (by simp only [first]; ring)

theorem active_descent (r : Row) (hr : Rows r) {x B D : ℝ}
    (hx : x∈Icc 0 (7/10)) (hBD : B≤D) (hl : outerDiagonal≤height x D)
    (hu : height x B≤outerAxial) : cost r x D≤cost r x B := by
  have hheight (Z : ℝ) (hZ : Z∈Icc B D) : height x Z∈Icc outerDiagonal outerAxial :=
    ⟨hl.trans (height_antitone hx hZ.2),(height_antitone hx hZ.1).trans hu⟩
  have hdomain (Z : ℝ) (hZ : Z∈Icc B D) : SourceDomain (height x Z) :=
    ⟨by linarith [(hheight Z hZ).1,outer_endpoint_bounds.2.2.1],(hheight Z hZ).2⟩
  have hm : AntitoneOn (cost r x) (Icc B D) :=
    antiOn_of_hasDeriv_nonpos
      (fun Z hZ => (cost_hasDerivAt r (hdomain Z hZ)).continuousAt.continuousWithinAt)
      (fun Z hZ => cost_hasDerivAt r (hdomain Z (Ioo_subset_Icc_self hZ)))
      (fun Z hZ => (first_negative r hr hx (hheight Z (Ioo_subset_Icc_self hZ))).le)
  exact hm ⟨le_rfl,hBD⟩ ⟨hBD,le_rfl⟩ hBD

theorem original_height (r : Row) (hr : Rows r) {a b B x : ℝ}
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b (7/12) B (angle false x)) : height x B≤a := by
  rw [primary_separator r (rows_remaining r hr)] at hm
  rw [angle_width false hx,angle_sin,angle_cos] at hm
  simp only [direction,Bool.false_eq_true,↓reduceIte] at hm
  dsimp [height,c0]
  linarith

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.SmallSide
end
end
end

section
/-!
## Completion of both small-slope negative-core side families

Before the intrinsic
event, the original source diagonal decreases to the target side join.
After it, the active contact descends directly to that join. The shared
endpoint theorem closes both alternatives, including weak contacts.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.SmallSide
open CommonQuarter CorePairGeometry Arithmetic

theorem diagonalB_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt diagonalB ((c0-(outerDiagonal-1/2)*Real.sin x)/(Real.cos x)^2) x := by
  have hc : Real.cos x≠0 := ne_of_gt (by linarith [(positive_trig hx).1])
  have h := (((hasDerivAt_const x (outerDiagonal-1/2)).div (Real.hasDerivAt_cos x) hc).const_sub
    (1/2)).fun_add ((CorePrimaryNegative.tangent_hasDerivAt hx).const_mul c0)
  exact h.congr_deriv (by ring)
theorem diagonalCost_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (diagonalCost r) (diagonalFirst r x) x := by
  have h := (((((hasDerivAt_id' x).const_mul (direction false)).const_add (Real.pi/2)).add_const
    (ocC r)).add_const ((ocP r-ocQ r)*outerDiagonal)).fun_add
      ((diagonalB_hasDerivAt hx).const_mul (ocG r))
  exact h.congr_deriv (by simp only [diagonalFirst,direction,Bool.false_eq_true,↓reduceIte]; ring)

theorem diagonalFirst_negative (r : Row) (hr : Rows r) {e x : ℝ}
    (he : IsEvent e) (hx : x∈Icc 0 e) : diagonalFirst r x<0 := by
  have hx0 : x∈Icc 0 (7/10) := ⟨hx.1,hx.2.trans (event_domain he).2⟩
  have ht := positive_trig hx0
  have hc : 0<Real.cos x := by linarith [ht.1]
  have hs := sin_mono hx0 (event_domain he) hx.2
  rw [he.2] at hs
  have hsbound : Real.sin x≤37/100 := hs.trans eventSine_bounds.2.le
  have hs2 := pow_le_pow_left₀ ht.2.2.1 hsbound 2
  have hg := (coefficients r (rows_remaining r hr)).2.1
  have hgU := (coefficient_reserves r hr).2.1
  have hterm := mul_nonneg (mul_nonneg hg.le
    (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1])) ht.2.2.1
  have hid : diagonalFirst r x*(Real.cos x)^2=
      (Real.sin x)^2-ocG r*(outerDiagonal-1/2)*Real.sin x+ocG r*c0-1 := by
    dsimp [diagonalFirst]
    field_simp [hc.ne']
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hn : diagonalFirst r x*(Real.cos x)^2<0 := by
    dsimp [c0] at hid
    nlinarith
  by_contra h
  have hp := mul_nonneg (le_of_not_gt h) (sq_nonneg (Real.cos x))
  linarith
theorem diagonal_descent (r : Row) (hr : Rows r) {e : ℝ} (he : IsEvent e) :
    AntitoneOn (diagonalCost r) (Icc 0 e) := by
  have hsub : Icc 0 e⊆Icc 0 (7/10) := fun x hx => ⟨hx.1,hx.2.trans (event_domain he).2⟩
  exact antiOn_of_hasDeriv_nonpos
    (fun x hx => (diagonalCost_hasDerivAt r (hsub hx)).continuousAt.continuousWithinAt)
    (fun x hx => diagonalCost_hasDerivAt r (hsub (Ioo_subset_Icc_self hx)))
    (fun x hx => (diagonalFirst_negative r hr he (Ioo_subset_Icc_self hx)).le)

theorem join_cost (r : Row) (x : ℝ) :
    cost r x (1/2)=Endpoint.H r false (angle false x) := by
  dsimp [cost,Endpoint.H,Endpoint.height,Endpoint.AA,Endpoint.BB,Endpoint.bC]
  rw [angle_cos]
  dsimp [direction,height,c0]
  ring
theorem diagonal_event_cost (r : Row) {e : ℝ} (he : IsEvent e) :
    diagonalCost r e=Endpoint.H r false (angle false e) := by
  have hheight : height e (1/2)=outerDiagonal := by
    dsimp [height]
    nlinarith [event_identity he]
  rw [←join_cost,diagonalCost,cost,diagonal_at_event he,hheight,source_diagonal]

theorem diagonal_lower (r : Row) (hr : Rows r) {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    (89809/100000:ℝ)<diagonalCost r x := by
  have hm := diagonal_descent r hr he hx ⟨he.1.1,le_rfl⟩ hx.2
  have hjoin := Endpoint.lower r (rows_remaining r hr) false (event_early he)
  rw [←diagonal_event_cost r he] at hjoin
  linarith

theorem original_to_contact (r : Row) (hr : Rows r) {a b B x : ℝ}
    (hs : OuterState a b) (hh : SourceDomain (height x B))
    (hheight : height x B≤a) : cost r x B≤outerCoreCost r a b (7/12) B (angle false x) := by
  have hm := M_monotone r (rows_remaining r hr) hh (actual_source_domain hs) hheight
  have hsid := source_identity r hs
  rw [primary_cost r (rows_remaining r hr)]
  dsimp [cost]
  linarith
theorem contact_diagonal_cost (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    cost r x (diagonalB x)=diagonalCost r x := by
  rw [cost,diagonal_contact hx,source_diagonal]
  rfl

theorem original_before (r : Row) (hr : Rows r) {e a b B x : ℝ}
    (he : IsEvent e) (hs : OuterState a b) (hx : x∈Icc 0 e)
    (hm : sourcePrimary r a b (7/12) B (angle false x)) :
    (89809/100000:ℝ)<outerCoreCost r a b (7/12) B (angle false x) := by
  have hx0 : x∈Icc 0 (7/10) := ⟨hx.1,hx.2.trans (event_domain he).2⟩
  have hheight := original_height r hr hx0 hm
  have hdiag := diagonal_lower r hr he hx
  have houter := outer_bounds hs
  by_cases hBD : B≤diagonalB x
  · have hheightlo : outerDiagonal≤height x B := by
      rw [←diagonal_contact hx0]
      exact height_antitone hx0 hBD
    have hh : SourceDomain (height x B) :=
      ⟨by linarith [hheightlo,outer_endpoint_bounds.2.2.1],hheight.trans houter.2.1⟩
    have hdescent := active_descent r hr hx0 hBD (by rw [diagonal_contact hx0]) hh.2
    rw [contact_diagonal_cost r hx0] at hdescent
    exact hdiag.trans_le (hdescent.trans (original_to_contact r hr hs hh hheight))
  · have hd : SourceDomain outerDiagonal :=
      ⟨by linarith [outer_endpoint_bounds.2.2.1],
        by linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2]⟩
    have hM := M_monotone r (rows_remaining r hr) hd (actual_source_domain hs) houter.1
    rw [source_diagonal,source_identity r hs] at hM
    have hg := mul_le_mul_of_nonneg_left (le_of_not_ge hBD)
      (coefficients r (rows_remaining r hr)).2.1.le
    rw [primary_cost r (rows_remaining r hr)]
    dsimp [diagonalCost] at hdiag
    linarith

theorem original_after (r : Row) (hr : Rows r) {e a b B x : ℝ}
    (he : IsEvent e) (hs : OuterState a b) (hB : B≤1/2) (hx : x∈Icc e (7/10))
    (hm : sourcePrimary r a b (7/12) B (angle false x)) :
    (89809/100000:ℝ)<outerCoreCost r a b (7/12) B (angle false x) := by
  have hx0 : x∈Icc 0 (7/10) := ⟨(event_domain he).1.trans hx.1,hx.2⟩
  have hheight := original_height r hr hx0 hm
  have hjoin := join_after_event he hx
  have hfirst := hjoin.trans (height_antitone hx0 hB)
  have hh : SourceDomain (height x B) :=
    ⟨by linarith [hfirst,outer_endpoint_bounds.2.2.1],hheight.trans (outer_bounds hs).2.1⟩
  have hdescent := active_descent r hr hx0 hB hjoin hh.2
  have hφ : angle false x∈earlyAngles := by
    have hφe := event_early he
    constructor
    · dsimp [angle,direction,lowerAngle]
      linarith [hx.2]
    · dsimp [angle,direction] at *
      linarith [hφe.2,hx.1]
  have hbound := Endpoint.lower r (rows_remaining r hr) false hφ
  rw [←join_cost] at hbound
  exact hbound.trans_le (hdescent.trans (original_to_contact r hr hs hh hheight))

theorem original (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (hA : A=7/12) (hB : B∈Icc 0 (1/2)) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle false x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle false x) := by
  subst A
  obtain ⟨e,he⟩ := event_exists
  rcases le_total x e with hxe|hex
  · have hh := original_before r hr he hs ⟨hx.1,hxe⟩ hm
    linarith
  · have hh := original_after r hr he hs hB.2 ⟨hex,hx.2⟩ hm
    linarith

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.SmallSide
end
end
end

section
/-!
## All six original negative-core primary families

The lower half uses the two prescribed straight-side
arguments and the complete corner argument; the upper half uses its one
increasing whole-circle support. Both closed core pieces and all ties
are included.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative
open CommonQuarter CorePairGeometry

theorem original (r : Row) (hr : Remaining r) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle upper x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle upper x) := by
  cases upper
  · rcases ht with ⟨hA,hB0,hB1⟩|⟨hB,hBA,hcircle⟩
    · by_cases hsmall : SmallSide.Rows r
      · exact SmallSide.original r hsmall hs hA ⟨hB0,hB1⟩ hx hm
      · have hrow : SideChord.Rows r := by
          rcases (remaining_iff r).1 hr with h|h|h|h|h|h <;>
            simp_all [SmallSide.Rows,SideChord.Rows]
        exact SideChord.original_side r hr hrow hs hA hx hm
    · exact Corner.original_lower r hr hs hB hBA hcircle hx hm
  · exact Upper.original r hr hs ht hx hm

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative
end
end
end

section
/-!
## Every normalized outer-to-core quarter contact

The original primary sign dominance is applied only
to the pair inequality, on the same actual source coordinates. The
literal cyclic role labels remain the conclusion.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter
open CommonQuarter CorePairGeometry

theorem outer_primary (r : Row) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle upper x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle upper x) := by
  have hσ := (primaryRow_signs r).1
  have hm' := (primary_constraint r a b A B (angle upper x)).2 hm
  have hred := outer_cost_reduction (r:=r) (A:=A) (B:=B) (φ:=angle upper x) hs
  cases hτ : targetPositive (primaryRow r)
  · exact (OuterNegative.original (primaryRow r) ⟨hσ,hτ⟩ upper hs ht hx hm').trans_le hred
  · exact (OuterPositive.original (primaryRow r) hσ hτ upper hs ht hx hm').trans_le hred

theorem outer_secondary (r : Row) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourceSecondary r a b A B (angle upper x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle upper x) :=
  OuterSecondary.original r upper hs ht hx hm

end SquaresInCircles.Eight.ShortWord.MixedQuarter
end
end
end

section
/-!
## All ninety-six original mixed quarter owners

Only edge indices, signs, radial orders and the four original owners are split
(`original_core_source`, `original_outer_source`, `original`). The target owners are the exact
reflection and reversal of the two source owners (`reverse_margin`). The original angle and the
signed role cost are kept, including both closed core pieces.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry WordProblems

def directRow (i : Vertex) (σ τ : Bool) : Row :=
  if i=2 then (if τ then 2 else 0)
  else if i=4 then (if σ then (if τ then 10 else 8) else (if τ then 6 else 4))
  else if i=5 then (if σ then (if τ then 18 else 16) else (if τ then 14 else 12))
  else if σ then 22 else 20
def reverseRow (i : Vertex) (σ τ : Bool) : Row := directRow i σ τ+1

theorem direct_data (i : Vertex) (σ τ : Bool) (hq : wrongWord .short i=1)
    (ha : allowed .short i σ τ) :
    reversed (directRow i σ τ)=false ∧ edge (directRow i σ τ)=i ∧
      sourcePositive (directRow i σ τ)=σ ∧ targetPositive (directRow i σ τ)=τ := by
  fin_cases i <;> cases σ <;> cases τ <;>
    simp [wrongWord,allowed,next,directRow,reversed,edge,sourcePositive,targetPositive] at hq ha ⊢
theorem reverse_data (i : Vertex) (σ τ : Bool) (hq : wrongWord .short i=1)
    (ha : allowed .short i σ τ) :
    reversed (reverseRow i σ τ)=true ∧ edge (reverseRow i σ τ)=i ∧
      sourcePositive (reverseRow i σ τ)=(!τ) ∧ targetPositive (reverseRow i σ τ)=(!σ) := by
  fin_cases i <;> cases σ <;> cases τ <;>
    simp [wrongWord,allowed,next,reverseRow,directRow,reversed,edge,sourcePositive,targetPositive] at hq ha ⊢

theorem angle_cover {φ : ℝ} (hφ : |φ-Real.pi/2|≤7/10) :
    ∃upper x,x∈Icc 0 (7/10) ∧ φ=angle upper x := by
  have hb := abs_le.mp hφ
  by_cases h : φ≤Real.pi/2
  · refine ⟨false,Real.pi/2-φ,⟨by linarith,by linarith [hb.1]⟩,?_⟩
    dsimp [angle,direction]; ring
  · refine ⟨true,φ-Real.pi/2,⟨by linarith,by linarith [hb.2]⟩,?_⟩
    dsimp [angle,direction]; ring

theorem core_source_owner (r : Row) {a b A B φ : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (j : Fin 4) (hj : j=0∨j=3)
    (hm : 0≤Eight.forwardMargin j a b A B (sourceSign r) (targetSign r) φ) :
    (449/500:ℝ)<coreOuterCost r a b A B φ := by
  obtain ⟨upper,x,hx,rfl⟩ := angle_cover hφ
  rcases hj with rfl|rfl
  · apply core_secondary r upper hs ht hx
    dsimp [sourceSecondary]
    simpa [Eight.forwardMargin,sub_nonneg] using hm
  · apply core_primary r upper hs ht hx
    dsimp [sourcePrimary]
    simpa [Eight.forwardMargin,sub_nonneg] using hm
theorem outer_source_owner (r : Row) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (j : Fin 4) (hj : j=0∨j=3)
    (hm : 0≤Eight.forwardMargin j a b A B (sourceSign r) (targetSign r) φ) :
    (449/500:ℝ)<outerCoreCost r a b A B φ := by
  obtain ⟨upper,x,hx,rfl⟩ := angle_cover hφ
  rcases hj with rfl|rfl
  · apply outer_secondary r upper hs ht hx
    dsimp [sourceSecondary]
    simpa [Eight.forwardMargin,sub_nonneg] using hm
  · apply outer_primary r upper hs ht hx
    dsimp [sourcePrimary]
    simpa [Eight.forwardMargin,sub_nonneg] using hm

theorem sign_not (σ : Bool) : (sign (!σ):ℝ)= -(sign σ:ℝ) := by cases σ <;> norm_num [sign]
theorem reverse_margin (j : Fin 4) (a b A B φ : ℝ) (σ τ : Bool) :
    Eight.forwardMargin (SecondWord.reflectedOwner j) A B a b (sign (!τ)) (sign (!σ)) φ=
      Eight.forwardMargin j a b A B (sign σ) (sign τ) φ := by
  rw [sign_not,sign_not]
  exact SecondWord.margin_reflection j a b A B (sign σ) (sign τ) φ

theorem original_core_source (i : Vertex) (σ τ : Bool) (core : RadialKind) (hcore : core≠.outer)
    (hq : wrongWord .short i=1) (ha : allowed .short i σ τ)
    {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (sign σ) (sign τ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i core σ a b-
      wrongValue .short (next i) .outer τ A B := by
  by_cases hj : j=0∨j=3
  · let r := directRow i σ τ
    have hd := direct_data i σ τ hq ha
    have hm' : 0≤Eight.forwardMargin j a b A B (sourceSign r) (targetSign r) φ := by
      simpa [r,sourceSign,targetSign,hd.2.2.1,hd.2.2.2] using hm
    have hh := core_source_owner r hs ht hφ j hj hm'
    rw [coreOuter_literal r core hcore] at hh
    simpa [r,literalCoreOuter,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2] using hh
  · let r := reverseRow i σ τ
    have hd := reverse_data i σ τ hq ha
    have hj' : SecondWord.reflectedOwner j=0∨SecondWord.reflectedOwner j=3 := by
      fin_cases j <;> simp [SecondWord.reflectedOwner] at hj ⊢
    have hm' : 0≤Eight.forwardMargin (SecondWord.reflectedOwner j) A B a b
        (sourceSign r) (targetSign r) φ := by
      have hh : 0≤Eight.forwardMargin (SecondWord.reflectedOwner j) A B a b (sign (!τ)) (sign (!σ)) φ := by
        rw [reverse_margin]; exact hm
      simpa [r,sourceSign,targetSign,hd.2.2.1,hd.2.2.2] using hh
    have hh := outer_source_owner r ht hs hφ (SecondWord.reflectedOwner j) hj' hm'
    rw [outerCore_literal r core hcore] at hh
    simpa [r,literalOuterCore,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2] using hh

theorem original_outer_source (i : Vertex) (σ τ : Bool) (core : RadialKind) (hcore : core≠.outer)
    (hq : wrongWord .short i=1) (ha : allowed .short i σ τ)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (sign σ) (sign τ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i .outer σ a b-
      wrongValue .short (next i) core τ A B := by
  by_cases hj : j=0∨j=3
  · let r := directRow i σ τ
    have hd := direct_data i σ τ hq ha
    have hm' : 0≤Eight.forwardMargin j a b A B (sourceSign r) (targetSign r) φ := by
      simpa [r,sourceSign,targetSign,hd.2.2.1,hd.2.2.2] using hm
    have hh := outer_source_owner r hs ht hφ j hj hm'
    rw [outerCore_literal r core hcore] at hh
    simpa [r,literalOuterCore,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2] using hh
  · let r := reverseRow i σ τ
    have hd := reverse_data i σ τ hq ha
    have hj' : SecondWord.reflectedOwner j=0∨SecondWord.reflectedOwner j=3 := by
      fin_cases j <;> simp [SecondWord.reflectedOwner] at hj ⊢
    have hm' : 0≤Eight.forwardMargin (SecondWord.reflectedOwner j) A B a b
        (sourceSign r) (targetSign r) φ := by
      have hh : 0≤Eight.forwardMargin (SecondWord.reflectedOwner j) A B a b (sign (!τ)) (sign (!σ)) φ := by
        rw [reverse_margin]; exact hm
      simpa [r,sourceSign,targetSign,hd.2.2.1,hd.2.2.2] using hh
    have hh := core_source_owner r ht hs hφ (SecondWord.reflectedOwner j) hj' hm'
    rw [coreOuter_literal r core hcore] at hh
    simpa [r,literalCoreOuter,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2] using hh

def Mixed (source target : RadialKind) : Prop :=
  (source=.outer∧target≠.outer)∨(source≠.outer∧target=.outer)

theorem original {i : Vertex} {source target : RadialKind} {σ τ : Bool}
    (hq : wrongWord .short i=1) (ha : allowed .short i σ τ) (hmixed : Mixed source target)
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (sign σ) (sign τ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i source σ a b-
      wrongValue .short (next i) target τ A B := by
  rcases hmixed with ⟨rfl,hcore⟩|⟨hcore,rfl⟩
  · exact original_outer_source i σ τ target hcore hq ha
      (by simpa [State] using hs) (by simpa [State,hcore] using ht) hφ j hm
  · exact original_core_source i σ τ source hcore hq ha
      (by simpa [State,hcore] using hs) (by simpa [State] using ht) hφ j hm

end SquaresInCircles.Eight.ShortWord.MixedQuarter
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry WordProblems

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord .short)
    (i : Vertex) (hq : wrongWord .short i=1) (hmixed : Mixed (C.kind i) (C.kind (next i)))
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-wrongMarker C .short (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by rw [hw]; exact hq
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    simpa [phaseValue,hk] using (difference_small F i).le
  exact original hq (actual_allowed C F hgap .short hw i) hmixed
    (actual_state C i) (actual_state C (next i)) hφ j (original_margin C F hgap i j howner)

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord .short)
    (i : Vertex) (hq : wrongWord .short i=1) (hmixed : Mixed (C.kind i) (C.kind (next i))) :
    (wrongGamma .short i:ℝ)<phaseValue F hgap i+wrongMarker C .short i-wrongMarker C .short (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact (Zero.threshold_le i).trans_lt (actual_owner C F hgap hw i hq hmixed j howner)

end SquaresInCircles.Eight.ShortWord.MixedQuarter
end
end
end
