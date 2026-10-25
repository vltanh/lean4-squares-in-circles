module

public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterNegativeSide
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterPositiveInteriorCoordinate

/-!
# Eight squares: all original outer-to-positive-core primary contacts

The arguments are only
the exact intrinsic source/target signs, original endpoint states,
closed angle half, and the original weak source-primary separator.
-/

section
/-!
## All six negative-core primary upper halves

The constant multiplier g leaves the core coefficients with their
original signs: the primary term is nonpositive and the transverse
term nonnegative. The axial core bound therefore applies to either
piece, including its join. The resulting support increases on the
whole closed upper angle half from a fixed value greater than .905.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.Upper
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open MixedQuarter.Reference

def S (r : Row) : ℝ := (ocG r-ocP r+ocQ r)/2-
  CommonQuarter.radius*Real.sqrt ((ocG r-ocP r)^2+(ocQ r)^2)
def F (r : Row) (x : ℝ) : ℝ := Real.pi/2+x+ocC r+S r+
  ocG r/2+(ocG r/2)*Real.cos x-(ocG r/12)*Real.sin x
def Fd (r : Row) (x : ℝ) : ℝ := 1-(ocG r/2)*Real.sin x-(ocG r/12)*Real.cos x

def radiusBox : Interval CommonQuarter.radius :=
  rootSix (Interval.point Q0) 2 (by norm_num) (by norm_num [Interval.point,Q0])
def normBox (r : Row) : Interval (Real.sqrt ((ocG r-ocP r)^2+(ocQ r)^2)) :=
  rootSix (Interval.point ((ocG r-ocP r)^2+(ocQ r)^2)) 2 (by norm_num)
    (by dsimp [Interval.point]; positivity)
def sourceBox (r : Row) : Interval (S r) :=
  (Interval.point ((ocG r-ocP r+ocQ r)/2)).sub (radiusBox.mul (normBox r))
def initialBox (r : Row) : Interval (F r 0) := by
  convert ((halfPi.add (Interval.point (ocC r))).add (sourceBox r)).add (Interval.point (ocG r)) using 1
  dsimp [F]
  simp only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero,add_zero]
  ring

private lemma r83_mpr_lo {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).lo=S.lo := by subst e; rfl
private lemma r83_initial_eq (r : Row) : F r 0=Real.pi/2+ocC r+S r+ocG r := by
  dsimp [F]
  simp only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero,add_zero]
  ring
private lemma r83_initialBox_lo (r : Row) :
    (initialBox r).lo=(((halfPi.add (Interval.point (ocC r))).add (sourceBox r)).add
      (Interval.point (ocG r))).lo :=
  r83_mpr_lo (r83_initial_eq r) _ _

theorem initial (r : Row) (hr : Remaining r) : (181/200:ℝ)<F r 0 := by
  have hh : (181/200:ℝ)<(initialBox r).lo := by
    rw [r83_initialBox_lo]
    rcases (remaining_iff r).1 hr with rfl|rfl|rfl|rfl|rfl|rfl <;>
      dsimp [sourceBox,normBox,radiusBox] <;> mixed_fixed
  exact hh.trans_le (initialBox r).mem.1

theorem F_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (F r) (Fd r x) x := by
  have hh := ((((((hasDerivAt_id' x).const_add (Real.pi/2)).add_const (ocC r)).add_const
    (S r)).add_const (ocG r/2)).fun_add ((Real.hasDerivAt_cos x).const_mul (ocG r/2))).fun_sub
      ((Real.hasDerivAt_sin x).const_mul (ocG r/12))
  exact hh.congr_deriv (by simp only [Fd]; ring)

theorem Fd_positive (r : Row) (hr : Remaining r) {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<Fd r x := by
  have hg := coefficients r hr
  have tr := positive_trig hx
  have hcos : 0≤Real.cos x := by linarith [tr.1]
  have hs := mul_le_mul hg.2.2.1.le tr.2.2.2.1.le tr.2.2.1
    (by norm_num : (0:ℝ)≤1139/1000)
  have hc := mul_le_mul hg.2.2.1.le (Real.cos_le_one x) hcos
    (by norm_num : (0:ℝ)≤1139/1000)
  dsimp [Fd]
  nlinarith

theorem F_monotone (r : Row) (hr : Remaining r) : MonotoneOn (F r) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (F_hasDerivAt r x).continuousAt.continuousWithinAt)
    (fun x _ => F_hasDerivAt r x)
    (fun _ hx => (Fd_positive r hr (Ioo_subset_Icc_self hx)).le)

theorem original_ge_F (r : Row) (hr : Remaining r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle true x)) :
    F r x≤outerCoreCost r a b A B (angle true x) := by
  have hg := (coefficients r hr).2.1
  have tr := positive_trig hx
  obtain ⟨hA0,hA,hB0,hBA,hB⟩ := CoreAngleEndpoint.state_bounds ht
  have hsep := (primary_separator r hr a b A B (angle true x)).1 hm
  rw [angle_width true hx,angle_cos,angle_sin] at hsep
  dsimp [direction] at hsep
  have hp := mul_le_mul_of_nonneg_left hsep hg.le
  have hcircle := outer_circle_lower (X:=ocP r-ocG r) (Y:=-(ocQ r)) hs
  have hnorm : (ocP r-ocG r)^2+(-(ocQ r))^2=(ocG r-ocP r)^2+(ocQ r)^2 := by ring
  rw [hnorm] at hcircle
  have hAcost := mul_le_mul_of_nonneg_right hA (mul_nonneg hg.le tr.2.2.1)
  have hBcost := mul_nonneg (mul_nonneg hg.le (sub_nonneg.mpr (Real.cos_le_one x))) hB0
  rw [primary_cost r hr]
  dsimp [F,S,angle,direction]
  nlinarith only [hp,hcircle,hAcost,hBcost]

theorem original (r : Row) (hr : Remaining r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle true x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle true x) := by
  have hmF := (F_monotone r hr) (by norm_num : (0:ℝ)∈Icc 0 (7/10)) hx hx.1
  have hv : (449/500:ℝ)<F r x := by linarith [initial r hr,hmF]
  exact hv.trans_le (original_ge_F r hr hs ht hx hm)

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.Upper
end
end
end

section
/-!
## Concavity before the unique axial transition

F is the exact circle
support obtained by solving the interior stationarity equation. It agrees
with K at the unique event, and its second derivative is negative on the
entire preceding interval. The original source and target remain in the
last inequality: their separator and circle support imply C >= F.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
open CommonQuarter CorePairGeometry Arithmetic

def F (r : Row) (x : ℝ) : ℝ := Real.pi/2-x+ocC r+
  lam r x*(1+c0*Real.sin x)+(ocG r-ocP r+ocQ r)/2-CommonQuarter.radius*N r x
def Fd (r : Row) (x : ℝ) : ℝ := -1+c0*ocG r-ocG r*X r x*(Real.sin x/Real.cos x)
def Fdd (r : Row) (x : ℝ) : ℝ :=
  -ocG r*(Xd r x*(Real.sin x/Real.cos x)+X r x/(Real.cos x)^2)

theorem F_hasDerivAt (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) :
    HasDerivAt (F r) (Fd r x) x := by
  have hc : Real.cos x≠0 := by linarith [(axial_trig hx).1]
  have hn := (N_positive r hr x).ne'
  have hh := (((((hasDerivAt_id x).const_sub (Real.pi/2)).add_const (ocC r)).add
    ((lam_hasDerivAt r hx).mul (((Real.hasDerivAt_sin x).const_mul c0).const_add 1))).add_const ((ocG r-ocP r+ocQ r)/2)).sub ((N_hasDerivAt r hr hx).const_mul CommonQuarter.radius)
  convert hh using 1
  · rfl
  · dsimp [Fd,X,criticalU,lamD,L,lam]
    field_simp [hc,hn]
    ring

theorem sin_div_cos_hasDerivAt {x : ℝ} (hx : x∈angleDomain) :
    HasDerivAt (fun y => Real.sin y/Real.cos y) (1/(Real.cos x)^2) x := by
  have hc : Real.cos x≠0 := by linarith [(axial_trig hx).1]
  have he : Real.cos x*Real.cos x-Real.sin x*(-Real.sin x)=1 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  convert (Real.hasDerivAt_sin x).div (Real.hasDerivAt_cos x) hc using 1
  rw [he]

theorem Fd_hasDerivAt (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) :
    HasDerivAt (Fd r) (Fdd r x) x := by
  have hh : HasDerivAt (Fd r)
      (-(ocG r*Xd r x*(Real.sin x/Real.cos x)+ocG r*X r x*(1/(Real.cos x)^2))) x :=
    (((X_hasDerivAt r hr hx).const_mul (ocG r)).mul
      (sin_div_cos_hasDerivAt hx)).const_sub (-1+c0*ocG r)
  exact hh.congr_deriv (by simp only [Fdd]; ring)

theorem transition_trig {x : ℝ} (hx : x∈Icc 0 (11/100:ℝ)) :
    0≤Real.sin x/Real.cos x ∧ Real.sin x/Real.cos x<111/1000 ∧
      (Real.cos x)^2≤1 := by
  have hx' : x∈angleDomain := ⟨hx.1,hx.2.trans (by norm_num [cap])⟩
  have hc : 0<Real.cos x := by linarith [(axial_trig hx').1]
  have hs := (positive_trig (angle_small hx')).2.2.1
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hlower := Real.one_sub_sq_div_two_le_cos (x:=x)
  refine ⟨div_nonneg hs hc.le,(div_lt_iff₀ hc).2 ?_,?_⟩
  · have hsin := Real.sin_le hx.1
    nlinarith
  · nlinarith [Real.cos_le_one x]

theorem Fdd_negative (r : Row) (hr : Rows r) {x : ℝ}
    (hx : x∈Icc 0 (11/100:ℝ)) (hH : H r x≤0) : Fdd r x<0 := by
  have hx' : x∈angleDomain := ⟨hx.1,hx.2.trans (by norm_num [cap])⟩
  have hc : 0<Real.cos x := by linarith [(axial_trig hx').1]
  have tr := transition_trig hx
  have hXd := mul_le_mul_of_nonneg_right (Xd_lower r hr hx' hH) tr.1
  have hX : (1/2:ℝ)≤X r x/(Real.cos x)^2 := (le_div_iff₀ (pow_pos hc 2)).2
    (by linarith [X_lower r hr hx' hH,tr.2.2])
  have ht := mul_lt_mul_of_pos_left tr.2.1 (show 0<c0 by norm_num [c0])
  have hpositive : 0<Xd r x*(Real.sin x/Real.cos x)+X r x/(Real.cos x)^2 := by
    norm_num [c0] at ht hXd
    linarith
  change -(ocG r)*(Xd r x*(Real.sin x/Real.cos x)+X r x/(Real.cos x)^2)<0
  exact mul_neg_of_neg_of_pos (by linarith [(coefficients r hr).2.2.2.1]) hpositive

theorem F_support_formula (r : Row) {x : ℝ} (hx : x∈angleDomain) :
    F r x=Real.pi/2-x+ocC r+
      ((lam r x-ocP r+ocQ r)/2-CommonQuarter.radius*N r x)+lam r x*(U x-1/2) := by
  have hh := lam_cos r hx
  dsimp [F,U]
  nlinarith only [hh]

theorem F_zero (r : Row) : F r 0=Reference.alignedInterior r := by
  simp only [F,lam,L,N,Reference.alignedInterior,Real.cos_zero,Real.sin_zero,
    div_one,mul_zero,add_zero,mul_one,sub_zero]

theorem F_at_transition (r : Row) (hr : Rows r) {e : ℝ} (he : IsTransition r e) : F r e=K r e := by
  have he' : e∈angleDomain := ⟨he.1.1.le,he.1.2.le.trans (by norm_num [cap])⟩
  have hc : Real.cos e≠0 := by linarith [(axial_trig he').1]
  have hw : lam r e=Md r (U e) := by
    apply (div_eq_iff hc).2
    have hh := he.2
    dsimp [H] at hh
    linarith
  have hs := circle_tangent r hr (axial_coordinate he') hw
  change (lam r e-ocP r+ocQ r)/2-CommonQuarter.radius*N r e=M r (U e)-lam r e*(U e-1/2) at hs
  rw [F_support_formula r he',hs]
  dsimp [K]
  ring

theorem F_concave (r : Row) (hr : Rows r) {e : ℝ} (he : IsTransition r e) :
    ConcaveOn ℝ (Icc 0 e) (F r) := by
  have hdom : ∀x∈Icc 0 e,x∈angleDomain := by
    intro x hx
    exact ⟨hx.1,(hx.2.trans he.1.2.le).trans (by norm_num [cap])⟩
  have he' := hdom e ⟨he.1.1.le,le_rfl⟩
  apply concave_of_deriv2
    (fun x hx => F_hasDerivAt r hr (hdom x hx))
    (fun x hx => Fd_hasDerivAt r hr (hdom x hx))
  intro x hx
  have hH := (H_strictMono r hr).monotoneOn (hdom x hx) he' hx.2
  rw [he.2] at hH
  exact (Fdd_negative r hr ⟨hx.1,hx.2.trans he.1.2.le⟩ hH).le

theorem interior_lower (r : Row) (hr : Rows r) (hi : Interior r) {e x : ℝ}
    (he : IsTransition r e) (hx : x∈Icc 0 e) : (449/500:ℝ)<F r x := by
  apply concave_gt_of_endpoints (F_concave r hr he) hx
  · rw [F_zero]
    linarith [Reference.aligned_interior r hr hi]
  · rw [F_at_transition r hr he]
    exact axial_lower r hr ⟨he.1.1.le,he.1.2.le.trans (by norm_num [cap])⟩

theorem original_ge_interior (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle false x)) :
    F r x≤outerCoreCost r a b A B (angle false x) := by
  have hd := lower_contact_bounds r hr hs ht hx hm
  have ha := (target_side r hr hs ht hx hm).1
  have hsep := lower_separator r hr hx hm
  rw [ha] at hsep
  have hp : lam r x*(1/2+c0*Real.sin x+(B+1/2)*Real.cos x)≤lam r x*a :=
    mul_le_mul_of_nonneg_left (by dsimp [c0]; linarith) (lam_positive r hr hd.1).le
  have hcircle := outer_circle_lower (X:=ocP r-lam r x) (Y:=-(ocQ r)) hs
  have hnorm : (ocP r-lam r x)^2+(-(ocQ r))^2=(L r x)^2+(ocQ r)^2 := by
    dsimp [L]
    ring
  rw [hnorm] at hcircle
  change -(ocP r-lam r x+ -(ocQ r))/2-CommonQuarter.radius*N r x≤
    (ocP r-lam r x)*a+ -(ocQ r)*b at hcircle
  have hk := lam_cos r hd.1
  have hB : lam r x*B*Real.cos x=ocG r*B := by
    calc
      lam r x*B*Real.cos x=(lam r x*Real.cos x)*B := by ring
      _=ocG r*B := by rw [hk]
  dsimp [F,outerCoreCost,angle,direction,sourceSign,targetSign,WordProblems.sign]
  rw [hr.1,hr.2]
  simp only [Bool.false_eq_true,↓reduceIte]
  push_cast
  linarith only [hp,hcircle,hk,hB]

theorem original_lower (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle false x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle false x) := by
  by_cases hH : 0≤H r x
  · exact original_axial r hr hs ht hx hm hH
  have hx' := (lower_contact_bounds r hr hs ht hx hm).1
  have hnegative : H r x<0 := lt_of_not_ge hH
  have hi : Interior r := by
    by_contra hn
    exact (not_lt_of_ge (always_axial r hr hn hx').le) hnegative
  obtain ⟨e,he,_⟩ := transition_exists_unique r hr hi
  have he' : e∈angleDomain := ⟨he.1.1.le,he.1.2.le.trans (by norm_num [cap])⟩
  have hxe : x≤e := by
    by_contra! hex
    have hh := H_strictMono r hr he' hx' hex
    rw [he.2] at hh
    linarith
  exact (interior_lower r hr hi he ⟨hx.1,hxe⟩).trans_le
    (original_ge_interior r hr hs ht hx hm)

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
end
end
end

section
/-!
## One aligned circle tangent over the entire upper half

The source multiplier is the
maximum of the target slope and the tangent at primary coordinate one.
The core support is the minimum of two increasing smooth functions;
this retains the support kink and both core pieces without an angle
partition. Its aligned value is exactly K(0) or the interior F(0).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
open CommonQuarter CorePairGeometry Arithmetic

def alignedLam (r : Row) : ℝ := max (ocG r) (Md r (3/2))
def circleSupport (r : Row) (w : ℝ) : ℝ :=
  (w-ocP r+ocQ r)/2-CommonQuarter.radius*Real.sqrt ((w-ocP r)^2+(ocQ r)^2)
def upperBase (r : Row) (x : ℝ) : ℝ := Real.pi/2+x+ocC r+circleSupport r (alignedLam r)+
  alignedLam r/2+(alignedLam r/2)*Real.cos x-(alignedLam r/12)*Real.sin x
def upperActive (r : Row) (x : ℝ) : ℝ :=
  upperBase r x-CoreAngleEndpoint.diagonal*(ocG r-alignedLam r*Real.cos x)
def G (r : Row) (x : ℝ) : ℝ :=
  upperBase r x-CoreAngleEndpoint.diagonal*max 0 (ocG r-alignedLam r*Real.cos x)
def upperBaseD (r : Row) (x : ℝ) : ℝ :=
  1-(alignedLam r/2)*Real.sin x-(alignedLam r/12)*Real.cos x
def upperActiveD (r : Row) (x : ℝ) : ℝ :=
  1-alignedLam r*(CoreAngleEndpoint.diagonal+1/2)*Real.sin x-(alignedLam r/12)*Real.cos x

theorem alignedLam_bounds (r : Row) (hr : Rows r) :
    0<alignedLam r ∧ ocG r≤alignedLam r ∧ alignedLam r<57/50 :=
  ⟨(coefficients r hr).2.2.2.1.trans_le (le_max_left _ _),le_max_left _ _,
    Reference.aligned_multiplier r hr⟩

theorem upperBase_hasDerivAt (r : Row) (x : ℝ) :
    HasDerivAt (upperBase r) (upperBaseD r x) x := by
  have h1 : HasDerivAt (fun y => Real.pi/2+y+ocC r+circleSupport r (alignedLam r)+
      alignedLam r/2) 1 x :=
    ((((hasDerivAt_id' x).const_add (Real.pi/2)).add_const (ocC r)).add_const _).add_const _
  have h2 := (h1.fun_add ((Real.hasDerivAt_cos x).const_mul (alignedLam r/2))).fun_sub
    ((Real.hasDerivAt_sin x).const_mul (alignedLam r/12))
  have h3 : HasDerivAt (upperBase r)
      (1+alignedLam r/2*(-Real.sin x)-alignedLam r/12*Real.cos x) x := h2
  exact h3.congr_deriv (by simp only [upperBaseD]; ring)

theorem upperActive_hasDerivAt (r : Row) (x : ℝ) :
    HasDerivAt (upperActive r) (upperActiveD r x) x := by
  have h1 : HasDerivAt (fun y => CoreAngleEndpoint.diagonal*(ocG r-alignedLam r*Real.cos y))
      (CoreAngleEndpoint.diagonal*(-(alignedLam r*(-Real.sin x)))) x :=
    (((Real.hasDerivAt_cos x).const_mul (alignedLam r)).const_sub (ocG r)).const_mul _
  have h2 : HasDerivAt (upperActive r)
      (upperBaseD r x-CoreAngleEndpoint.diagonal*(-(alignedLam r*(-Real.sin x)))) x :=
    (upperBase_hasDerivAt r x).fun_sub h1
  exact h2.congr_deriv (by simp only [upperBaseD,upperActiveD]; ring)

theorem upper_derivatives_positive (r : Row) (hr : Rows r) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : 0<upperBaseD r x ∧ 0<upperActiveD r x := by
  have hw := alignedLam_bounds r hr
  have tr := positive_trig hx
  have hk : 0≤Real.cos x := by linarith [tr.1]
  have hd0 : 0≤CoreAngleEndpoint.diagonal+1/2 := by linarith [CoreAngleEndpoint.diagonal_bounds.1]
  have hd1 : CoreAngleEndpoint.diagonal+1/2≤1059/1000 := by linarith [CoreAngleEndpoint.diagonal_bounds.2]
  have hws := mul_le_mul hw.2.2.le tr.2.2.2.1.le tr.2.2.1 (by norm_num : (0:ℝ)≤57/50)
  have hwk := mul_le_mul hw.2.2.le (Real.cos_le_one x) hk (by norm_num : (0:ℝ)≤57/50)
  have hwd := mul_le_mul hw.2.2.le hd1 hd0 (by norm_num : (0:ℝ)≤57/50)
  have hwds := mul_le_mul hwd tr.2.2.2.1.le tr.2.2.1
    (by norm_num : (0:ℝ)≤(57/50)*(1059/1000))
  constructor <;> dsimp [upperBaseD,upperActiveD] <;> nlinarith

theorem G_eq_min (r : Row) (x : ℝ) : G r x=min (upperBase r x) (upperActive r x) := by
  have hd : 0≤CoreAngleEndpoint.diagonal := by linarith [CoreAngleEndpoint.diagonal_bounds.1]
  by_cases ht : 0≤ocG r-alignedLam r*Real.cos x
  · rw [G,max_eq_right ht,min_eq_right]
    · rfl
    · dsimp [upperActive]
      exact sub_le_self _ (mul_nonneg hd ht)
  · have ht' : ocG r-alignedLam r*Real.cos x≤0 := (lt_of_not_ge ht).le
    rw [G,max_eq_left ht',mul_zero,sub_zero,min_eq_left]
    dsimp [upperActive]
    have hh := mul_nonpos_of_nonneg_of_nonpos hd ht'
    linarith

theorem G_monotone (r : Row) (hr : Rows r) : MonotoneOn (G r) (Icc 0 (7/10)) := by
  have hb : MonotoneOn (upperBase r) (Icc 0 (7/10)) := monoOn_of_hasDeriv_nonneg
    (fun x _ => (upperBase_hasDerivAt r x).continuousAt.continuousWithinAt)
    (fun x _ => upperBase_hasDerivAt r x)
    (fun x hx => (upper_derivatives_positive r hr (Ioo_subset_Icc_self hx)).1.le)
  have ha : MonotoneOn (upperActive r) (Icc 0 (7/10)) := monoOn_of_hasDeriv_nonneg
    (fun x _ => (upperActive_hasDerivAt r x).continuousAt.continuousWithinAt)
    (fun x _ => upperActive_hasDerivAt r x)
    (fun x hx => (upper_derivatives_positive r hr (Ioo_subset_Icc_self hx)).2.le)
  intro x hx y hy hxy
  rw [G_eq_min,G_eq_min]
  exact min_le_min (hb hx hy hxy) (ha hx hy hxy)

theorem G_zero_formula (r : Row) :
    G r 0=Real.pi/2+ocC r+circleSupport r (alignedLam r)+alignedLam r := by
  have hh : ocG r-alignedLam r≤0 := sub_nonpos.mpr (le_max_left _ _)
  simp only [G,upperBase,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero,add_zero]
  rw [max_eq_left hh]
  ring

theorem G_zero_lower (r : Row) (hr : Rows r) : (449/500:ℝ)<G r 0 := by
  rw [G_zero_formula]
  by_cases hg : ocG r≤Md r (3/2)
  · have hw : alignedLam r=Md r (3/2) := max_eq_right hg
    have hs := circle_tangent r hr (show (3/2:ℝ)∈coordinateDomain by norm_num [coordinateDomain]) rfl
    change circleSupport r (Md r (3/2))=M r (3/2)-Md r (3/2)*(3/2-1/2) at hs
    rw [hw,hs]
    have hK := axial_lower r hr (show (0:ℝ)∈angleDomain by norm_num [angleDomain,cap])
    simp only [K,U,Real.sin_zero,Real.cos_zero,mul_zero,add_zero,sub_zero] at hK
    linarith
  · have hg' : Md r (3/2)<ocG r := lt_of_not_ge hg
    have hw : alignedLam r=ocG r := max_eq_left hg'.le
    have hi : Interior r := by
      by_contra hn
      have hh := (Reference.initial_event r hr).2 hn
      simp only [H,U,Real.sin_zero,Real.cos_zero,mul_zero,add_zero,mul_one] at hh
      norm_num at hh
      linarith
    rw [hw]
    have hh := Reference.aligned_interior r hr hi
    dsimp [Reference.alignedInterior,circleSupport] at hh ⊢
    linarith

theorem original_ge_upper (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle true x)) :
    G r x≤outerCoreCost r a b A B (angle true x) := by
  have hw := alignedLam_bounds r hr
  have tr := positive_trig hx
  obtain ⟨hA0,hA,hB0,hBA,hB⟩ := CoreAngleEndpoint.state_bounds ht
  have hsep := hm
  rw [sourcePrimary,angle_width true hx,angle_cos,angle_sin,targetSign_positive hr.2] at hsep
  dsimp [direction] at hsep
  have hp := mul_le_mul_of_nonneg_left hsep hw.1.le
  have hcircle := outer_circle_lower (X:=ocP r-alignedLam r) (Y:=-(ocQ r)) hs
  have hnorm : (ocP r-alignedLam r)^2+(-(ocQ r))^2=
      (alignedLam r-ocP r)^2+(ocQ r)^2 := by ring
  rw [hnorm] at hcircle
  have hAcost := mul_le_mul_of_nonneg_right hA (mul_nonneg hw.1.le tr.2.2.1)
  have hm0 : 0 ≤ max 0 (ocG r-alignedLam r*Real.cos x) := le_max_left _ _
  have hBm := mul_le_mul_of_nonneg_right hB hm0
  have hcoef := mul_le_mul_of_nonneg_right (le_max_right 0 (ocG r-alignedLam r*Real.cos x)) hB0
  have hBcost : -CoreAngleEndpoint.diagonal*max 0 (ocG r-alignedLam r*Real.cos x)≤
      (alignedLam r*Real.cos x-ocG r)*B := by nlinarith only [hBm,hcoef]
  dsimp [G,upperBase,circleSupport,outerCoreCost,angle,direction,sourceSign,targetSign,
    WordProblems.sign]
  rw [hr.1,hr.2]
  simp only [Bool.false_eq_true,↓reduceIte]
  push_cast
  linarith only [hp,hcircle,hAcost,hBcost]

theorem original_upper (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle true x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle true x) :=
  (G_zero_lower r hr).trans_le
    (((G_monotone r hr) (by norm_num : (0:ℝ)∈Icc 0 (7/10)) hx hx.1).trans
      (original_ge_upper r hr hs ht hx hm))

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
open CommonQuarter CorePairGeometry

theorem original (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=true)
    (upper : Bool) {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b A B (angle upper x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle upper x) := by
  cases upper
  · exact original_lower r ⟨hσ,hτ⟩ hs ht hx hm
  · exact original_upper r ⟨hσ,hτ⟩ hs ht hx hm

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
end
end
end
