module

public import SquaresInCircles.Eight.Arithmetic.WholeIntervalPolynomial
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Owners.Stationary.TerminalWeights
public import SquaresInCircles.Eight.Stationary.System
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroLReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroAsymmetric
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroCycle
public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroCoreNegative
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterReferences
public import SquaresInCircles.Eight.Words.Short.WordZero

/-!
# Eight squares: the unique positive-core interior circle contact

The stationarity equation is solved in the original shifted source coordinates (`criticalU`,
`critical_coordinate`). Its positive root lies between the axial contact and the source-axis
endpoint whenever the axial target derivative is nonpositive. The root differentiates to a
nonnegative derivative (`criticalU_hasDerivAt`, `criticalD_nonneg`).
-/

section
/-!
## Fixed references for the positive-core primary contact

Only fixed geometric endpoints and the three displayed interior
references are enclosed. The following calculus proves the full domains.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive.Reference
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open MixedQuarter.Reference
open SecondWord.OppositeThree.ReferenceAlgebra (rootThree)

def uBox {x : ℝ} (hx : 0≤x) : Interval (U x) :=
  let W := ((Interval.point 1).add ((Interval.point c0).mul (sine hx))).add
    ((cosine hx).mul (Interval.point (1/2)))
  ⟨W.lo,W.hi,by
    have e : U x=1+c0*Real.sin x+Real.cos x*(1/2) := by simp only [U]; ring
    rw [e]; exact W.mem⟩
def hBox {x : ℝ} (hx : 0≤x) : Interval (h x) :=
  let W := ((Interval.point c0).mul (cosine hx)).sub ((sine hx).mul (Interval.point (1/2)))
  ⟨W.lo,W.hi,by
    have e : h x=c0*Real.cos x-Real.sin x*(1/2) := by simp only [h]; ring
    rw [e]; exact W.mem⟩
def radicand {u : ℝ} (Y : Interval u) : Interval (Q0-u^2) := (Interval.point Q0).sub Y.square
def vBox {u : ℝ} (Y : Interval u) (hr : 0≤(radicand Y).lo) : Interval (V u) :=
  rootThree (radicand Y) (13/10) (by norm_num) hr
def mBox (r : Row) {u : ℝ} (Y : Interval u) (W : Interval (V u)) : Interval (M r u) :=
  ((Interval.point (ocP r)).mul (Y.sub (Interval.point (1/2)))).sub
    ((Interval.point (ocQ r)).mul (W.sub (Interval.point (1/2))))
def mdBox (r : Row) {u : ℝ} (Y : Interval u) (W : Interval (V u)) (hW : 0<W.lo) :
    Interval (Md r u) :=
  (Interval.point (ocP r)).add (((Interval.point (ocQ r)).mul Y).div W hW)
def curvatureBox (r : Row) {u : ℝ} (Y : Interval u) (W : Interval (V u)) (hW : 0<W.lo) :
    Interval (curvature r u) :=
  ((((Interval.point (ocQ r*Q0)).div W.cube (Interval.cube_lo_pos hW)).mul
    ((Interval.point J).sub ((Y.sub (Interval.point 1)).square))).sub
      ((mdBox r Y W hW).mul (Y.sub (Interval.point 1))))
def kBox (r : Row) {x : ℝ} (hx : 0≤x) (W : Interval (V (U x))) : Interval (K r x) :=
  (((halfPi.sub (Interval.point x)).add (Interval.point (ocC r))).add (mBox r (uBox hx) W))
def kdBox (r : Row) {x : ℝ} (hx : 0≤x) (W : Interval (V (U x))) (hW : 0<W.lo) : Interval (Kd r x) :=
  (Interval.point (-1)).add ((mdBox r (uBox hx) W hW).mul (hBox hx))
def eventBox (r : Row) {x : ℝ} (hx : 0≤x) (W : Interval (V (U x))) (hW : 0<W.lo) : Interval (H r x) :=
  ((mdBox r (uBox hx) W hW).mul (cosine hx)).sub (Interval.point (ocG r))

macro "positive_core_reference" : tactic => `(tactic|
  (dsimp [uBox,hBox,radicand,vBox,mBox,mdBox,curvatureBox,kBox,kdBox,eventBox,
    c0,J,cap,U,h,K,Kd,H,M,Md,Mdd,curvature,reference]; mixed_fixed))

private theorem r84_nonrising (r : Row) (hr : Rows r) (h : ¬Rising r) :
    r=3 ∨ r=14 ∨ r=15 := by
  rcases rows r hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [Rising] at h ⊢

private theorem r84_exterior (r : Row) (hr : Rows r) (h : ¬Interior r) :
    r=2 ∨ r=6 ∨ r=20 ∨ r=21 := by
  rcases rows r hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [Interior] at h ⊢

theorem cap_height : outerAxial+1/2<U cap ∧ U cap<383/200 := by
  have h0 : (0:ℝ)≤cap := by norm_num [cap]
  have hL : MixedQuarter.Reference.axial.hi+1/2<(uBox h0).lo := by positive_core_reference
  have hU : (uBox h0).hi<(383/200:ℝ) := by positive_core_reference
  exact ⟨by linarith [MixedQuarter.Reference.axial.mem.2,(uBox h0).mem.1],
    (uBox h0).mem.2.trans_lt hU⟩

theorem cap_trig : (903/1000:ℝ)<Real.cos cap ∧ Real.sin cap<107/250 := by
  have h0 : (0:ℝ)≤cap := by norm_num [cap]
  have hC : (903/1000:ℝ)<(MixedQuarter.Reference.cosine h0).lo := by positive_core_reference
  have hS : (MixedQuarter.Reference.sine h0).hi<(107/250:ℝ) := by positive_core_reference
  exact ⟨hC.trans_le (MixedQuarter.Reference.cosine h0).mem.1,
    (MixedQuarter.Reference.sine h0).mem.2.trans_lt hS⟩

theorem initial_curvature (r : Row) (hr : Rows r) : (109/100:ℝ)<curvature r (3/2) := by
  let Y := Interval.point (3/2:ℝ)
  have hrad : 0≤(radicand Y).lo := by dsimp [Y]; positive_core_reference
  let W := vBox Y hrad
  have hW : 0<W.lo := by dsimp [W,Y]; positive_core_reference
  have hh : (109/100:ℝ)<(curvatureBox r Y W hW).lo := by
    fin_cases r <;> norm_num [Rows,sourcePositive,targetPositive] at hr <;>
      dsimp [W,Y] <;> positive_core_reference
  exact hh.trans_le (curvatureBox r Y W hW).mem.1

theorem initial_values (r : Row) (hr : Rows r) (hRise : Rising r) :
    (8981/10000:ℝ)<K r 0 ∧ 0<Kd r 0 := by
  have h0 : (0:ℝ)≤0 := le_rfl
  have hrad : 0≤(radicand (uBox h0)).lo := by positive_core_reference
  let W := vBox (uBox h0) hrad
  have hW : 0<W.lo := by dsimp [W]; positive_core_reference
  have hV : (8981/10000:ℝ)<(kBox r h0 W).lo := by
    rcases hRise with rfl|rfl|rfl|rfl|rfl <;> dsimp [W] <;> positive_core_reference
  have hD : 0<(kdBox r h0 W hW).lo := by
    rcases hRise with rfl|rfl|rfl|rfl|rfl <;> dsimp [W] <;> positive_core_reference
  exact ⟨hV.trans_le (kBox r h0 W).mem.1,hD.trans_le (kdBox r h0 W hW).mem.1⟩

theorem reference_bound (r : Row) (hr : Rows r) (hRise : ¬Rising r) :
    (449/500:ℝ)<K r (reference r)-(Kd r (reference r))^2/(109/50) := by
  have hrow := r84_nonrising r hr hRise
  have hnonneg : 0≤reference r := by
    dsimp [reference]; split_ifs <;> norm_num
  have hrad : 0≤(radicand (uBox hnonneg)).lo := by
    rcases hrow with rfl|rfl|rfl <;> positive_core_reference
  let W := vBox (uBox hnonneg) hrad
  have hW : 0<W.lo := by
    rcases hrow with rfl|rfl|rfl <;> dsimp [W] <;> positive_core_reference
  let L := (kBox r hnonneg W).sub
    (((kdBox r hnonneg W hW).square).mul (Interval.point (50/109)))
  have hh : (449/500:ℝ)<L.lo := by
    rcases hrow with rfl|rfl|rfl <;> dsimp [L,W] <;> positive_core_reference
  have he := hh.trans_le L.mem.1
  have e : (Kd r (reference r))^2/(109/50)=(Kd r (reference r))^2*(50/109) := by ring
  rw [e]
  exact he

theorem initial_event (r : Row) (hr : Rows r) :
    (Interior r → H r 0<0) ∧ (¬Interior r → 0<H r 0) := by
  have h0 : (0:ℝ)≤0 := le_rfl
  have hrad : 0≤(radicand (uBox h0)).lo := by positive_core_reference
  let W := vBox (uBox h0) hrad
  have hW : 0<W.lo := by dsimp [W]; positive_core_reference
  constructor
  · intro hi
    have hh : (eventBox r h0 W hW).hi<0 := by
      rcases hi with rfl|rfl|rfl|rfl <;> dsimp [W] <;> positive_core_reference
    exact (eventBox r h0 W hW).mem.2.trans_lt hh
  · intro hi
    have hh : 0<(eventBox r h0 W hW).lo := by
      rcases r84_exterior r hr hi with rfl|rfl|rfl|rfl <;> dsimp [W] <;> positive_core_reference
    exact hh.trans_le (eventBox r h0 W hW).mem.1

theorem event_at_eleven (r : Row) (hr : Rows r) (hi : Interior r) : (1/250:ℝ)<H r (11/100) := by
  have h0 : (0:ℝ)≤11/100 := by norm_num
  have hrad : 0≤(radicand (uBox h0)).lo := by positive_core_reference
  let W := vBox (uBox h0) hrad
  have hW : 0<W.lo := by dsimp [W]; positive_core_reference
  have hh : (1/250:ℝ)<(eventBox r h0 W hW).lo := by
    rcases hi with rfl|rfl|rfl|rfl <;> dsimp [W] <;> positive_core_reference
  exact hh.trans_le (eventBox r h0 W hW).mem.1

def alignedInterior (r : Row) : ℝ := Real.pi/2+ocC r+ocG r+
  (ocG r-ocP r+ocQ r)/2-CommonQuarter.radius*Real.sqrt ((ocG r-ocP r)^2+ocQ r^2)

theorem aligned_interior (r : Row) (hr : Rows r) (hi : Interior r) :
    (89809/100000:ℝ)<alignedInterior r := by
  let Z := Interval.point ((ocG r-ocP r)^2+ocQ r^2)
  have hZ : 0≤Z.lo := by dsimp [Z,Interval.point]; positivity
  let N := rootThree Z (if r=3 then 21/10 else 3/2)
    (by split_ifs <;> norm_num) hZ
  let F := (((halfPi.add (Interval.point (ocC r))).add (Interval.point (ocG r))).add
    (Interval.point ((ocG r-ocP r+ocQ r)/2))).sub (circleRadius.mul N)
  have hh : (89809/100000:ℝ)<F.lo := by
    rcases hi with rfl|rfl|rfl|rfl <;> (try dsimp only [F,N,Z]) <;> positive_core_reference
  exact hh.trans_le F.mem.1

theorem aligned_multiplier (r : Row) (hr : Rows r) : max (ocG r) (Md r (3/2))<57/50 := by
  let Y := Interval.point (3/2:ℝ)
  have hrad : 0≤(radicand Y).lo := by dsimp [Y]; positive_core_reference
  let W := vBox Y hrad
  have hW : 0<W.lo := by dsimp [W,Y]; positive_core_reference
  have hh : (mdBox r Y W hW).hi<(57/50:ℝ) := by
    fin_cases r <;> norm_num [Rows,sourcePositive,targetPositive] at hr <;>
      dsimp [W,Y] <;> positive_core_reference
  exact max_lt (by linarith [(coefficients r hr).2.2.2.2])
    ((mdBox r Y W hW).mem.2.trans_lt hh)

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive.Reference
end
end
end

section
/-!
## Whole axial curvature and the unique interior/axial event

The derivative of the
axial curvature is controlled by the single completed-square polynomial
E(U) on the entire source coordinate interval. The resulting 1.09
curvature reserve proves every axial value. The target derivative H
is strictly increasing on the whole physical axial interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
open CommonQuarter CorePairGeometry Arithmetic

theorem angle_small {x : ℝ} (hx : x∈angleDomain) : x∈Icc 0 (7/10) :=
  ⟨hx.1,hx.2.trans (by norm_num [cap])⟩

theorem axial_coordinate {x : ℝ} (hx : x∈angleDomain) : U x∈coordinateDomain := by
  have h0 := U_strictMono.monotoneOn (by norm_num : (0:ℝ)∈Icc 0 (7/10)) (angle_small hx) hx.1
  have hc := U_strictMono.monotoneOn (angle_small hx)
    (by norm_num [cap] : cap∈Icc 0 (7/10)) hx.2
  have hU0 : U 0=3/2 := by norm_num [U]
  rw [hU0] at h0
  exact ⟨h0,hc.trans Reference.cap_height.2.le⟩

theorem axial_trig {x : ℝ} (hx : x∈angleDomain) :
    (903/1000:ℝ)<Real.cos x ∧ Real.sin x<107/250 ∧ (191/250:ℝ)<h x := by
  have hc := cos_anti (angle_small hx) (by norm_num [cap] : cap∈Icc 0 (7/10)) hx.2
  have hs := sin_mono (angle_small hx) (by norm_num [cap] : cap∈Icc 0 (7/10)) hx.2
  have hC := Reference.cap_trig.1.trans_le hc
  have hS := hs.trans_lt Reference.cap_trig.2
  refine ⟨hC,hS,?_⟩
  dsimp [h,c0]
  linarith

theorem E_lower (u : ℝ) : (867/1000:ℝ)<E u := by
  have hs := sq_nonneg (u-(Q0+1-J)/2)
  norm_num [Q0,J,E] at hs ⊢
  nlinarith

theorem curvature_hasDerivAt (r : Row) {u : ℝ} (hu : u∈coordinateDomain) :
    HasDerivAt (curvature r) (curvatureD r u) u := by
  have hf := (Mdd_hasDerivAt r hu).fun_mul
    ((((hasDerivAt_id' u).sub_const 1).pow 2).const_sub J)
  have hg := (Md_hasDerivAt r hu).fun_mul ((hasDerivAt_id' u).sub_const 1)
  exact (hf.fun_sub hg).congr_deriv (by simp only [curvatureD]; norm_num; ring)

theorem curvatureD_identity (r : Row) {u : ℝ} (hu : u∈coordinateDomain) :
    curvatureD r u*(V u)^5=
      ocQ r*(3*Q0*E u-u*(V u)^4)-ocP r*(V u)^5 := by
  have hn := (V_positive hu).ne'
  have hs := V_square hu
  simp only [curvatureD,Mddd,Mdd,Md,E]
  generalize V u = w at hn hs ⊢
  rw [← hs]
  field_simp
  ring

theorem curvatureD_positive (r : Row) (hr : Rows r) {u : ℝ} (hu : u∈coordinateDomain) :
    0<curvatureD r u := by
  have hb := coefficients r hr
  have hq : 0<ocQ r := by linarith [hb.2.2.1]
  have hv := V_bounds hu
  have hv0 := V_positive hu
  have hv4 : (V u)^4≤(833/500:ℝ)^2 := by nlinarith [sq_nonneg ((V u)^2-833/500)]
  have hv5 := pow_le_pow_left₀ hv0.le hv.2.1.le 5
  have hu0 : 0≤u := by linarith [hu.1]
  have huV := mul_le_mul hu.2 hv4 (by positivity : 0≤(V u)^4) (by norm_num : (0:ℝ)≤383/200)
  have hpV := mul_le_mul_of_nonneg_right hb.2.1.le (pow_nonneg hv0.le 5)
  have hEV := mul_lt_mul_of_pos_left (E_lower u) (by norm_num [Q0] : (0:ℝ)<3*Q0)
  have hbracket : (39/10:ℝ)<3*Q0*E u-u*(V u)^4-(253/1000)*(V u)^5 := by
    norm_num [Q0] at hEV hv5 huV ⊢
    linarith
  have hm := mul_pos hq (show 0<3*Q0*E u-u*(V u)^4-(253/1000)*(V u)^5 by linarith)
  have hid := curvatureD_identity r hu
  have hpositive : 0<curvatureD r u*(V u)^5 := by linarith
  exact pos_of_mul_pos_left hpositive (pow_nonneg hv0.le 5)

theorem curvature_monotone (r : Row) (hr : Rows r) : MonotoneOn (curvature r) coordinateDomain :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hu => (curvature_hasDerivAt r hu).continuousAt.continuousWithinAt)
    (fun _ hu => curvature_hasDerivAt r (Ioo_subset_Icc_self hu))
    (fun _ hu => (curvatureD_positive r hr (Ioo_subset_Icc_self hu)).le)

theorem K_hasDerivAt (r : Row) {x : ℝ} (hx : x∈angleDomain) : HasDerivAt (K r) (Kd r x) x := by
  have hh := (((hasDerivAt_id' x).const_sub (Real.pi/2)).add_const (ocC r)).fun_add
    ((M_hasDerivAt r (axial_coordinate hx)).comp x (U_hasDerivAt x))
  exact hh.congr_deriv (by simp only [Kd])

theorem Kd_hasDerivAt (r : Row) {x : ℝ} (hx : x∈angleDomain) : HasDerivAt (Kd r) (Kdd r x) x := by
  have hh := (((Md_hasDerivAt r (axial_coordinate hx)).comp x (U_hasDerivAt x)).fun_mul
    (h_hasDerivAt x)).const_add (-1)
  refine hh.congr_deriv ?_
  simp only [Kdd,curvature,Function.comp]
  rw [← h_square]
  ring

theorem Kdd_lower (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) : (109/100:ℝ)<Kdd r x :=
  (Reference.initial_curvature r hr).trans_le (curvature_monotone r hr
    (by norm_num [coordinateDomain]) (axial_coordinate hx) (axial_coordinate hx).1)

theorem axial_lower (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) : (449/500:ℝ)<K r x := by
  by_cases hRise : Rising r
  · have hD : MonotoneOn (Kd r) angleDomain := monoOn_of_hasDeriv_nonneg
      (fun y hy => (Kd_hasDerivAt r hy).continuousAt.continuousWithinAt)
      (fun y hy => Kd_hasDerivAt r (Ioo_subset_Icc_self hy))
      (fun y hy => by linarith [Kdd_lower r hr (Ioo_subset_Icc_self hy)])
    have hK : MonotoneOn (K r) angleDomain := monoOn_of_hasDeriv_nonneg
      (fun y hy => (K_hasDerivAt r hy).continuousAt.continuousWithinAt)
      (fun y hy => K_hasDerivAt r (Ioo_subset_Icc_self hy))
      (fun y hy => (Reference.initial_values r hr hRise).2.le.trans
        (hD (by norm_num [angleDomain,cap]) (Ioo_subset_Icc_self hy) hy.1.le))
    have hh := hK (by norm_num [angleDomain,cap]) hx hx.1
    linarith [(Reference.initial_values r hr hRise).1]
  · have href : reference r∈angleDomain := by
      dsimp [reference,angleDomain,cap]; split_ifs <;> norm_num
    have hh := CenteredMonomialBounds.second_derivative_tangent_lower
      (κ:=(109/100:ℝ)) (fun y hy => K_hasDerivAt r hy)
      (fun y hy => Kd_hasDerivAt r hy) (fun y hy => (Kdd_lower r hr hy).le) href hx
    have hs := sq_nonneg ((109/100)*(x-reference r)+Kd r (reference r))
    have hb := Reference.reference_bound r hr hRise
    nlinarith

theorem H_hasDerivAt (r : Row) {x : ℝ} (hx : x∈angleDomain) : HasDerivAt (H r) (Hd r x) x := by
  have hh := (((Md_hasDerivAt r (axial_coordinate hx)).comp x (U_hasDerivAt x)).fun_mul
    (Real.hasDerivAt_cos x)).sub_const (ocG r)
  exact hh.congr_deriv (by simp only [Hd,Function.comp]; ring)

theorem Hd_positive (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) : 0<Hd r x := by
  have hb := coefficients r hr
  have hq : 0<ocQ r := by linarith [hb.2.2.1]
  have hu := axial_coordinate hx
  have hv := V_bounds hu
  have hv0 := V_positive hu
  have tr := axial_trig hx
  have hs0 := (positive_trig (angle_small hx)).2.2.1
  have hv3 := pow_le_pow_left₀ hv0.le hv.2.1.le 3
  have hUV := mul_le_mul hu.2 hv.2.2.le (sq_nonneg _) (by norm_num : (0:ℝ)≤383/200)
  have hpV := mul_le_mul_of_nonneg_right hb.2.1.le (pow_nonneg hv0.le 3)
  have hqv3 := mul_le_mul_of_nonneg_left hv3 hq.le
  have hqUV := mul_le_mul_of_nonneg_left hUV hq.le
  have hsum : ocP r*(V (U x))^3+ocQ r*U x*(V (U x))^2≤
      ocQ r*((253/1000)*(1291/1000)^3+(383/200)*(833/500)) := by linarith
  have hprod := mul_le_mul hsum tr.2.1.le hs0
    (by positivity : 0≤ocQ r*((253/1000)*(1291/1000)^3+(383/200)*(833/500)))
  have hhk := mul_lt_mul'' tr.2.2 tr.1
    (by norm_num : (0:ℝ)≤191/250) (by norm_num : (0:ℝ)≤903/1000)
  have hnum := mul_lt_mul_of_pos_left hhk (mul_pos hq (by norm_num [Q0] : (0:ℝ)<Q0))
  have hid : Hd r x*(V (U x))^3=ocQ r*Q0*h x*Real.cos x-
      (ocP r*(V (U x))^3+ocQ r*U x*(V (U x))^2)*Real.sin x := by
    simp only [Hd,Mdd,Md]
    generalize V (U x) = w at hv0 ⊢
    field_simp
  have hpositive : 0<Hd r x*(V (U x))^3 := by
    norm_num [Q0] at hnum hid
    linarith
  exact pos_of_mul_pos_left hpositive (pow_nonneg hv0.le 3)

theorem H_strictMono (r : Row) (hr : Rows r) : StrictMonoOn (H r) angleDomain := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 cap)
  · exact fun x hx => (H_hasDerivAt r hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(H_hasDerivAt r (Ioo_subset_Icc_self hx)).deriv]
    exact Hd_positive r hr (Ioo_subset_Icc_self hx)

def IsTransition (r : Row) (e : ℝ) : Prop := e∈Ioo 0 (11/100:ℝ) ∧ H r e=0

theorem transition_exists_unique (r : Row) (hr : Rows r) (hi : Interior r) : ∃!e,IsTransition r e := by
  have hsmall : ∀x∈Icc 0 (11/100:ℝ),x∈angleDomain := by
    intro x hx; exact ⟨hx.1,hx.2.trans (by norm_num [cap])⟩
  have hc : ContinuousOn (H r) (Icc 0 (11/100:ℝ)) :=
    fun x hx => (H_hasDerivAt r (hsmall x hx)).continuousAt.continuousWithinAt
  obtain ⟨e,he,hzero⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤11/100) hc
    (show (0:ℝ)∈Icc (H r 0) (H r (11/100)) from
      ⟨(Reference.initial_event r hr).1 hi |>.le,by linarith [Reference.event_at_eleven r hr hi]⟩)
  have he0 : 0<e := lt_of_le_of_ne he.1 (by
    intro hh; subst e; exact (ne_of_lt ((Reference.initial_event r hr).1 hi)) hzero)
  have he1 : e<11/100 := lt_of_le_of_ne he.2 (by
    intro hh; rw [hh] at hzero; linarith [Reference.event_at_eleven r hr hi])
  refine ⟨e,⟨⟨he0,he1⟩,hzero⟩,?_⟩
  intro f hf
  apply (H_strictMono r hr).injOn (hsmall f ⟨hf.1.1.le,hf.1.2.le⟩) (hsmall e he)
  rw [hf.2,hzero]

theorem always_axial (r : Row) (hr : Rows r) (hi : ¬Interior r) {x : ℝ} (hx : x∈angleDomain) : 0<H r x :=
  ((Reference.initial_event r hr).2 hi).trans_le
    ((H_strictMono r hr).monotoneOn (by norm_num [angleDomain,cap]) hx hx.1)

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
end
end
end

section
/-!
## The actual lower-half side contact and its axial alternative

The core corner and the side
join are infeasible. The original separator gives the increasing-source
contact on A=7/12, whose angle lies before the unique axial event.
The upper target endpoint is the source-axis endpoint and has positive
target derivative. Nonnegative H makes the original minimum axial.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
open CommonQuarter CorePairGeometry Arithmetic

theorem lower_separator (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b A B (angle false x)) :
    1/2+(A+1/2)*Real.sin x+(B+1/2)*Real.cos x≤a := by
  rw [sourcePrimary,angle_width false hx,angle_cos,angle_sin,targetSign_positive hr.2] at hm
  dsimp [direction] at hm
  linarith

theorem target_side (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle false x)) : A=7/12 ∧ 0≤B ∧ B<1/2 := by
  have hsep := lower_separator r hr hx hm
  have tr := positive_trig hx
  have hsum : 1≤Real.sin x+Real.cos x := by
    have hh := one_le_abs_cos_add_abs_sin x
    rw [abs_of_pos (by linarith [tr.1]),abs_of_nonneg tr.2.2.1] at hh
    linarith
  have hnot : B<1/2 := by
    by_contra! hb
    have hA : 1/2≤A := by linarith [(CoreAngleEndpoint.state_bounds ht).1]
    have hp := mul_le_mul_of_nonneg_right (show 1≤A+1/2 by linarith) tr.2.2.1
    have hq := mul_le_mul_of_nonneg_right (show 1≤B+1/2 by linarith) (by linarith [tr.1] : 0≤Real.cos x)
    have ha := (outer_bounds hs).2.1.trans_lt outer_endpoint_bounds.2.1
    linarith
  have hside := core_small_side ht hnot
  exact ⟨hside.1,(CoreAngleEndpoint.state_bounds ht).2.2.1,hnot⟩

theorem lower_contact_bounds (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle false x)) :
    x∈angleDomain ∧ U x+B*Real.cos x≤a+1/2 ∧
      U x+B*Real.cos x∈coordinateDomain ∧ a+1/2∈coordinateDomain := by
  have hside := target_side r hr hs ht hx hm
  have hsep := lower_separator r hr hx hm
  rw [hside.1] at hsep
  have he : U x+B*Real.cos x≤a+1/2 := by dsimp [U,c0]; linarith
  have hBcos := mul_nonneg hside.2.1 (by linarith [(positive_trig hx).1] : 0≤Real.cos x)
  have h0 := U_strictMono.monotoneOn (by norm_num : (0:ℝ)∈Icc 0 (7/10)) hx hx.1
  have hU0' : U 0=3/2 := by norm_num [U]
  have hU0 : (3/2:ℝ)≤U x := by rw [← hU0']; exact h0
  have hxcap : x<cap := by
    by_contra! hbad
    have hc := U_strictMono.monotoneOn (by norm_num [cap] : cap∈Icc 0 (7/10)) hx hbad
    linarith [Reference.cap_height.1,(outer_bounds hs).2.1]
  have haU : a+1/2≤383/200 := by linarith [(outer_bounds hs).2.1,outer_endpoint_bounds.2.1]
  exact ⟨⟨hx.1,hxcap.le⟩,he,⟨by linarith,he.trans haU⟩,⟨by linarith,haU⟩⟩

def contactCost (r : Row) (B x : ℝ) : ℝ := Real.pi/2-x+ocC r+M r (U x+B*Real.cos x)-ocG r*B

theorem original_ge_contact (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle false x)) :
    contactCost r B x≤outerCoreCost r a b A B (angle false x) := by
  have hd := lower_contact_bounds r hr hs ht hx hm
  have hmono := M_monotone r hr hd.2.2.1 hd.2.2.2 hd.2.1
  have hMa : M r (a+1/2)=ocP r*a-ocQ r*b := by rw [M,actual_source hs]; ring
  have hss : sourceSign r= -1 := by simp [sourceSign,WordProblems.sign,hr.1]
  have hts : targetSign r=1 := targetSign_positive hr.2
  have hang : angle false x=Real.pi/2-x := by
    simp only [angle,direction,Bool.false_eq_true,↓reduceIte]
    ring
  rw [outerCoreCost,hss,hts,hang]
  dsimp [contactCost]
  linarith

theorem upper_source_root : V (outerAxial+1/2)=1/2 := by
  have he : Q0-(outerAxial+1/2)^2=(1/2:ℝ)^2 := by linarith [axial_circle]
  rw [V,he,Real.sqrt_sq (by norm_num : (0:ℝ)≤1/2)]

theorem upper_target_derivative (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) :
    0<Md r (outerAxial+1/2)*Real.cos x-ocG r := by
  have hb := coefficients r hr
  have tr := axial_trig hx
  have hq : 0≤ocQ r := by linarith [hb.2.2.1]
  have ha : (957/500:ℝ)<outerAxial+1/2 := by linarith [ShortOuterZero.fine_axial_bounds.1]
  have hprod := mul_le_mul hb.2.2.1 (show (957/500:ℝ)≤outerAxial+1/2 by linarith)
    (by norm_num) hq
  have hM : (121/50:ℝ)<Md r (outerAxial+1/2) := by
    rw [Md,upper_source_root]
    have he : ocQ r*(outerAxial+1/2)/(1/2)=2*(ocQ r*(outerAxial+1/2)) := by ring
    rw [he]
    linarith [hb.1]
  have hh := mul_lt_mul'' hM tr.1 (by norm_num : (0:ℝ)≤121/50) (by norm_num : (0:ℝ)≤903/1000)
  linarith [hb.2.2.2.2]

theorem contact_ge_axial (r : Row) (hr : Rows r) {B x : ℝ}
    (hx : x∈angleDomain) (hB : 0≤B) (hu : U x+B*Real.cos x∈coordinateDomain)
    (hH : 0≤H r x) : K r x≤contactCost r B x := by
  have hC : 0≤Real.cos x := by linarith [(axial_trig hx).1]
  have hUle : U x≤U x+B*Real.cos x := by nlinarith
  have hdom : ∀u∈Icc (U x) (U x+B*Real.cos x),u∈coordinateDomain := by
    intro u hu'
    exact ⟨(axial_coordinate hx).1.trans hu'.1,hu'.2.trans hu.2⟩
  have hh := derivative_reserve
    (f:=M r) (df:=Md r) (k:=Md r (U x))
    (fun u hu' => (M_hasDerivAt r (hdom u hu')).continuousAt.continuousWithinAt)
    (fun u hu' => M_hasDerivAt r (hdom u (Ioo_subset_Icc_self hu')))
    (fun u hu' => Md_monotone r hr (axial_coordinate hx)
      (hdom u (Ioo_subset_Icc_self hu')) hu'.1.le)
    (show U x∈Icc (U x) (U x+B*Real.cos x) from ⟨le_rfl,hUle⟩)
    (show U x+B*Real.cos x∈Icc (U x) (U x+B*Real.cos x) from ⟨hUle,le_rfl⟩) hUle
  have hpay := mul_nonneg hB hH
  dsimp [H,K,contactCost] at *
  nlinarith

theorem original_axial (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle false x)) (hH : 0≤H r x) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle false x) := by
  have hd := lower_contact_bounds r hr hs ht hx hm
  have hB := (CoreAngleEndpoint.state_bounds ht).2.2.1
  exact (axial_lower r hr hd.1).trans_le
    ((contact_ge_axial r hr hd.1 hB hd.2.2.1 hH).trans (original_ge_contact r hr hs ht hx hm))

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
open CommonQuarter CorePairGeometry Arithmetic

def lam (r : Row) (x : ℝ) : ℝ := ocG r/Real.cos x
def lamD (r : Row) (x : ℝ) : ℝ := ocG r*Real.sin x/(Real.cos x)^2
def L (r : Row) (x : ℝ) : ℝ := lam r x-ocP r
def N (r : Row) (x : ℝ) : ℝ := Real.sqrt ((L r x)^2+(ocQ r)^2)
def criticalU (r : Row) (x : ℝ) : ℝ := CommonQuarter.radius*(L r x/N r x)
def criticalD (r : Row) (x : ℝ) : ℝ := CommonQuarter.radius*(ocQ r)^2*lamD r x/(N r x)^3
def X (r : Row) (x : ℝ) : ℝ := (criticalU r x-1-c0*Real.sin x)/Real.cos x
def Xd (r : Row) (x : ℝ) : ℝ :=
  criticalD r x/Real.cos x-c0+X r x*(Real.sin x/Real.cos x)

theorem p_lt_g (r : Row) (hr : Rows r) : ocP r<ocG r := by
  rcases rows r hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [ocP,ocG]

theorem lam_positive (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) : 0<lam r x :=
  div_pos (coefficients r hr).2.2.2.1 (by linarith [(axial_trig hx).1])

theorem g_le_lam (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) : ocG r≤lam r x := by
  have hc : 0<Real.cos x := by linarith [(axial_trig hx).1]
  apply (le_div_iff₀ hc).2
  exact mul_le_of_le_one_right (coefficients r hr).2.2.2.1.le (Real.cos_le_one x)

theorem L_positive (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) : 0<L r x := by
  dsimp [L]
  linarith [p_lt_g r hr,g_le_lam r hr hx]

theorem N_positive (r : Row) (hr : Rows r) (x : ℝ) : 0<N r x := by
  have hq : 0<ocQ r := by linarith [(coefficients r hr).2.2.1]
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg (L r x)]

theorem N_square (r : Row) (x : ℝ) : (N r x)^2=(L r x)^2+(ocQ r)^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem lam_cos (r : Row) {x : ℝ} (hx : x∈angleDomain) : lam r x*Real.cos x=ocG r :=
  div_mul_cancel₀ _ (by linarith [(axial_trig hx).1] : Real.cos x≠0)

theorem lam_hasDerivAt (r : Row) {x : ℝ} (hx : x∈angleDomain) :
    HasDerivAt (lam r) (lamD r x) x := by
  have hc : Real.cos x≠0 := by linarith [(axial_trig hx).1]
  have hh : HasDerivAt (lam r) ((0*Real.cos x-ocG r*(-Real.sin x))/(Real.cos x)^2) x :=
    (hasDerivAt_const x (ocG r)).div (Real.hasDerivAt_cos x) hc
  exact hh.congr_deriv (by simp only [lamD]; ring)

theorem N_hasDerivAt (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) :
    HasDerivAt (N r) (L r x*lamD r x/N r x) x := by
  have hh := ((((lam_hasDerivAt r hx).sub_const (ocP r)).pow 2).add_const
    ((ocQ r)^2)).sqrt (Real.sqrt_pos.mp (N_positive r hr x)).ne'
  convert hh using 1
  · rfl
  · dsimp [L,N]
    field_simp [(N_positive r hr x).ne']

theorem criticalU_hasDerivAt (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) :
    HasDerivAt (criticalU r) (criticalD r x) x := by
  have hN := (N_positive r hr x).ne'
  have hh := (((lam_hasDerivAt r hx).sub_const (ocP r)).div
    (N_hasDerivAt r hr hx) hN).const_mul CommonQuarter.radius
  convert hh using 1
  · rfl
  · calc
      criticalD r x=CommonQuarter.radius*lamD r x*((N r x)^2-(L r x)^2)/(N r x)^3 := by
        rw [N_square]
        dsimp [criticalD]
        ring
      _=CommonQuarter.radius*((lamD r x*N r x-L r x*(L r x*lamD r x/N r x))/(N r x)^2) := by
        field_simp [hN]

theorem criticalD_nonneg (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) :
    0≤criticalD r x := by
  have hg := (coefficients r hr).2.2.2.1.le
  have hs := (positive_trig (angle_small hx)).2.2.1
  have hR : 0≤CommonQuarter.radius := by linarith [radius_bounds.1]
  dsimp [criticalD,lamD]
  exact div_nonneg (mul_nonneg (mul_nonneg hR (sq_nonneg _))
    (div_nonneg (mul_nonneg hg hs) (sq_nonneg _))) (pow_nonneg (N_positive r hr x).le 3)

theorem critical_comparison_identity (r : Row) {x u : ℝ} (hu : u∈coordinateDomain) :
    (CommonQuarter.radius*L r x)^2-(u*N r x)^2=
      (L r x*V u)^2-(ocQ r*u)^2 := by
  simp only [mul_pow,radius_sq,N_square]
  rw [← V_square hu]
  ring

theorem coordinate_le_critical (r : Row) (hr : Rows r) {x u : ℝ}
    (hx : x∈angleDomain) (hu : u∈coordinateDomain) (hm : Md r u≤lam r x) :
    u≤criticalU r x := by
  have hq : 0<ocQ r := by linarith [(coefficients r hr).2.2.1]
  have hu0 : 0≤u := by linarith [hu.1]
  have hL := L_positive r hr hx
  have hN := N_positive r hr x
  have hV := V_positive hu
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hgap : ocQ r*u≤L r x*V u := (div_le_iff₀ hV).1 (by
    dsimp [Md,L] at hm ⊢
    linarith)
  have hs := mul_nonneg (sub_nonneg.mpr hgap)
    (show 0≤L r x*V u+ocQ r*u by positivity)
  have hid := critical_comparison_identity r (x:=x) hu
  have hleft0 := mul_nonneg hu0 hN.le
  have hright0 := mul_nonneg hR.le hL.le
  have hn : u*N r x≤CommonQuarter.radius*L r x := by nlinarith
  have hh := (le_div_iff₀ hN).2 hn
  simpa [criticalU,mul_div_assoc] using hh

theorem critical_le_coordinate (r : Row) (hr : Rows r) {x u : ℝ}
    (hx : x∈angleDomain) (hu : u∈coordinateDomain) (hm : lam r x≤Md r u) :
    criticalU r x≤u := by
  have hq : 0<ocQ r := by linarith [(coefficients r hr).2.2.1]
  have hu0 : 0≤u := by linarith [hu.1]
  have hL := L_positive r hr hx
  have hN := N_positive r hr x
  have hV := V_positive hu
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hgap : L r x*V u≤ocQ r*u := (le_div_iff₀ hV).1 (by
    dsimp [Md,L] at hm ⊢
    linarith)
  have hs := mul_nonneg (sub_nonneg.mpr hgap)
    (show 0≤L r x*V u+ocQ r*u by positivity)
  have hid := critical_comparison_identity r (x:=x) hu
  have hleft0 := mul_nonneg hu0 hN.le
  have hright0 := mul_nonneg hR.le hL.le
  have hn : CommonQuarter.radius*L r x≤u*N r x := by nlinarith
  have hh := (div_le_iff₀ hN).2 hn
  simpa [criticalU,mul_div_assoc] using hh

theorem critical_coordinate (r : Row) (hr : Rows r) {x : ℝ}
    (hx : x∈angleDomain) (hH : H r x≤0) :
    U x≤criticalU r x ∧ criticalU r x≤outerAxial+1/2 ∧ criticalU r x∈coordinateDomain := by
  have hc : 0<Real.cos x := by linarith [(axial_trig hx).1]
  have hleft : Md r (U x)≤lam r x := (le_div_iff₀ hc).2 (by dsimp [H] at hH; linarith)
  have hu : outerAxial+1/2∈coordinateDomain := by
    constructor <;> linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.1]
  have hright : lam r x≤Md r (outerAxial+1/2) := (div_le_iff₀ hc).2
    (by linarith [upper_target_derivative r hr hx])
  have hl := coordinate_le_critical r hr hx (axial_coordinate hx) hleft
  have hh := critical_le_coordinate r hr hx hu hright
  exact ⟨hl,hh,⟨(axial_coordinate hx).1.trans hl,hh.trans hu.2⟩⟩

theorem X_lower (r : Row) (hr : Rows r) {x : ℝ}
    (hx : x∈angleDomain) (hH : H r x≤0) : (1/2:ℝ)≤X r x := by
  have hc : 0<Real.cos x := by linarith [(axial_trig hx).1]
  apply (le_div_iff₀ hc).2
  have hh := (critical_coordinate r hr hx hH).1
  dsimp [U] at hh
  linarith

theorem X_hasDerivAt (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) :
    HasDerivAt (X r) (Xd r x) x := by
  have hc : Real.cos x≠0 := by linarith [(axial_trig hx).1]
  have hh := (((criticalU_hasDerivAt r hr hx).sub_const 1).sub
    ((Real.hasDerivAt_sin x).const_mul c0)).div (Real.hasDerivAt_cos x) hc
  convert hh using 1
  · rfl
  · dsimp [Xd,X]
    field_simp [hc]
    ring

theorem Xd_lower (r : Row) (hr : Rows r) {x : ℝ}
    (hx : x∈angleDomain) (hH : H r x≤0) : -c0≤Xd r x := by
  have hc : 0≤Real.cos x := by linarith [(axial_trig hx).1]
  have hs := (positive_trig (angle_small hx)).2.2.1
  have ht := mul_nonneg (show 0≤X r x by linarith [X_lower r hr hx hH]) (div_nonneg hs hc)
  have hd := div_nonneg (criticalD_nonneg r hr hx) hc
  dsimp [Xd]
  linarith

/-- The ordinary positive circle support is attained at its tangent point. -/
theorem circle_tangent (r : Row) (hr : Rows r) {u w : ℝ}
    (hu : u∈coordinateDomain) (hw : w=Md r u) :
    (w-ocP r+ocQ r)/2-CommonQuarter.radius*Real.sqrt ((w-ocP r)^2+(ocQ r)^2)=
      M r u-w*(u-1/2) := by
  have hv := V_positive hu
  have hq : 0<ocQ r := by linarith [(coefficients r hr).2.2.1]
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hd : w-ocP r=ocQ r*u/V u := by rw [hw,Md]; ring
  have hs : (CommonQuarter.radius*ocQ r/V u)^2=(w-ocP r)^2+(ocQ r)^2 := by
    rw [hd]
    calc
      (CommonQuarter.radius*ocQ r/V u)^2=(ocQ r)^2*(u^2+(V u)^2)/(V u)^2 := by
        field_simp [hv.ne']
        rw [radius_sq,← V_square hu]
        ring
      _=(ocQ r*u/V u)^2+(ocQ r)^2 := by field_simp [hv.ne']
  have hroot : Real.sqrt ((w-ocP r)^2+(ocQ r)^2)=CommonQuarter.radius*ocQ r/V u := by
    rw [← hs,Real.sqrt_sq (by positivity : 0≤CommonQuarter.radius*ocQ r/V u)]
  rw [hroot,hw]
  dsimp [M,Md]
  field_simp [hv.ne']
  rw [radius_sq,← V_square hu]
  ring

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
end
end
end
