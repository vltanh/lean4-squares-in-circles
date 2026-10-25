module

public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterPositiveInteriorCoordinate

/-!
# Eight squares: concavity before the unique axial transition

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
