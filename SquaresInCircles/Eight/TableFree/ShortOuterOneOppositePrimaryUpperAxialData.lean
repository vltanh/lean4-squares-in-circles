module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryUpperCurvature

/-!
# The axial reference curve and its whole-interval derivatives

Uncompiled transcription of (13)--(17), (31)--(34) of the complementary
note and (18)--(20), (26), (40) of the three-family note. Every estimate
holds on the entire interval ending at the intrinsic diagonal event.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD)

def K (x : ℝ) : ℝ := contact 0 x+1/2
def v (x : ℝ) : ℝ := arc (contact 0 x)+1/2
def h (x : ℝ) : ℝ := angleSpeed 0 x
def projection (x : ℝ) : ℝ := Real.cos x+rho*Real.sin x
def projectionD (x : ℝ) : ℝ := -Real.sin x+rho*Real.cos x
def F (r : Row) (x : ℝ) : ℝ := value r 0 x
def F1 (r : Row) (x : ℝ) : ℝ := angleFirst r 0 x
def F2 (r : Row) (x : ℝ) : ℝ :=
  sourceDD r (contact 0 x)*(h x)^2-sourceD r (contact 0 x)*(K x-1)
def H (r : Row) (x : ℝ) : ℝ := first r 0 x
def H1 (r : Row) (x : ℝ) : ℝ :=
  -sourceDD r (contact 0 x)*h x*projection x+sourceD r (contact 0 x)*projectionD x

theorem K_formula (x : ℝ) : K x=1+Real.cos x/2-(outerAxial-1/2)*Real.sin x := by
  dsimp [K,contact,SecondWord.SameZero.b]
  rw [SameContact.arc_zero]
  ring
theorem v_formula (x : ℝ) : v x=Real.sqrt (Q0-(K x)^2) := by
  dsimp [v,K,arc]
  ring
theorem h_formula (x : ℝ) : h x=Real.sin x/2+(outerAxial-1/2)*Real.cos x := by
  dsimp [h,angleSpeed,SecondWord.SameZero.v]
  rw [SameContact.arc_zero]
  ring
theorem F_formula (r : Row) (x : ℝ) :
    F r x=Real.pi/2+x+c r+p r*(K x-1/2)-q r*(v x-1/2)-P r*outerAxial := by
  dsimp [F,value,source,target,K,v]
  rw [SameContact.arc_zero]
  ring
theorem F1_formula (r : Row) (x : ℝ) : F1 r x=1-(p r+q r*K x/v x)*h x := by
  dsimp [F1,angleFirst,sourceD,ratio,K,v,h]
  ring
theorem H_formula (r : Row) (x : ℝ) :
    H r x=(p r+q r*K x/v x)*projection x+P r*rho-t r := by
  dsimp [H,first,sourceD,stateSpeed,SecondWord.SameZero.k]
  rw [ratio_zero]
  dsimp [ratio,K,v,projection]
  ring

theorem h_hasDerivAt (x : ℝ) : HasDerivAt h (K x-1) x :=
  (SecondWord.SameZero.v_angle_hasDerivAt 0 x).congr_deriv (by simp only [K]; ring)
theorem projection_hasDerivAt (x : ℝ) : HasDerivAt projection (projectionD x) x :=
  (Real.hasDerivAt_cos x).fun_add ((Real.hasDerivAt_sin x).const_mul rho)
theorem F_hasDerivAt (r : Row) {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    HasDerivAt (F r) (F1 r x) x := value_angle_hasDerivAt r (before_domain he hx)
theorem F1_hasDerivAt (r : Row) {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    HasDerivAt (F1 r) (F2 r x) x := by
  have hh := (((sourceD_hasDerivAt r (before_domain he hx).2.2).comp x
    (SecondWord.SameZero.b_angle_hasDerivAt 0 x)).fun_mul (h_hasDerivAt x)).const_sub 1
  exact hh.congr_deriv (by simp only [F2,h,angleSpeed,contact,Function.comp_apply]; ring)
theorem H_hasDerivAt (r : Row) {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    HasDerivAt (H r) (H1 r x) x := by
  have hh := (((sourceD_hasDerivAt r (before_domain he hx).2.2).comp x
    (SecondWord.SameZero.b_angle_hasDerivAt 0 x)).mul (projection_hasDerivAt x)).add_const (P r*rho-t r)
  convert hh using 1
  · ext y
    dsimp [H,first,stateSpeed,SecondWord.SameZero.k,projection]
    rw [ratio_zero]
    ring
  · dsimp [H1,h]
    ring

theorem axial_primary_range {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    contact 0 x∈Icc outerDiagonal 1 := by
  have hd := before_domain he hx
  have hm := SecondWord.SameZero.b_angle_antitone zero_mem
    (by norm_num : (0:ℝ)∈Icc 0 (7/10)) hd.2.1 hx.1
  have h00 : SecondWord.SameZero.b 0 0=1 := by norm_num [SecondWord.SameZero.b]
  rw [h00] at hm
  exact ⟨hd.2.2.1,hm⟩

theorem axial_bounds {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    (1399/1000:ℝ)<K x ∧ K x≤3/2 ∧ (129/100:ℝ)<v x ∧ v x<(7/5:ℝ) ∧
      (914575671/1000000000:ℝ)<h x ∧ h x<(121072/125000:ℝ) ∧
      0≤Real.sin x ∧ Real.sin x<(27/250:ℝ) := by
  have ha := axial_primary_range he hx
  have hv := Same.Positive.source_root ha
  have hs : Real.sin x<(27/250:ℝ) :=
    (Real.sin_le hx.1).trans_lt (by linarith [hx.2,(event_bounds he).2.1])
  have ht := positive_trig (before_domain he hx).2.1
  have hm : MonotoneOn h (Icc 0 e) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun y _ => (h_hasDerivAt y).continuousAt.continuousWithinAt)
      (fun y _ => h_hasDerivAt y)
    intro y hy
    have hh := (axial_primary_range he (Ioo_subset_Icc_self hy)).1
    dsimp [K]
    linarith [ShortMixedZero.fine_diagonal_bounds.1]
  have hlo := hm (show (0:ℝ)∈Icc 0 e from ⟨le_rfl,by linarith [(event_bounds he).1]⟩) hx hx.1
  rw [h_formula,h_formula] at hlo
  norm_num at hlo
  have hh := mul_le_mul_of_nonneg_left ht.2.1
    (show 0≤outerAxial-1/2 by linarith [ShortOuterZero.fine_axial_bounds.1])
  refine ⟨?_,?_,hv.1,hv.2,?_,?_,ht.2.2.1,hs⟩
  · dsimp [K]
    linarith [ha.1,ShortMixedZero.fine_diagonal_bounds.1]
  · dsimp [K]
    linarith [ha.2]
  · rw [h_formula]
    linarith [ShortOuterZero.fine_axial_bounds.1]
  · rw [h_formula]
    linarith [ShortOuterZero.fine_axial_bounds.2]

theorem projection_early {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    1≤projection x ∧ projection x<(128537/125000:ℝ) ∧
      (5223/20000)*(99417/100000)-27/250<projectionD x ∧ projectionD x<131/500 := by
  have hb := axial_bounds he hx
  have hc := early_cos he hx
  have ht := positive_trig (before_domain he hx).2.1
  have hlow := mul_lt_mul'' rho_bounds.1 hc (by norm_num) (by norm_num)
  have hhi := mul_le_mul_of_nonneg_left ht.2.1 (by linarith [rho_bounds.1] : 0≤rho)
  have hpd : (5223/20000)*(99417/100000)-27/250<projectionD x := by
    dsimp [projectionD]
    linarith [hb.2.2.2.2.2.2.2]
  have hm : MonotoneOn projection (Icc 0 e) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun y _ => (projection_hasDerivAt y).continuousAt.continuousWithinAt)
      (fun y _ => projection_hasDerivAt y)
    intro y hy
    have hc' := early_cos he (Ioo_subset_Icc_self hy)
    have hs' := (axial_bounds he (Ioo_subset_Icc_self hy)).2.2.2.2.2.2.2
    have hh := mul_le_mul rho_bounds.1.le hc'.le (by norm_num)
      (by linarith [rho_bounds.1] : 0≤rho)
    dsimp [projectionD]
    linarith
  have hmono := hm ⟨le_rfl,by linarith [(event_bounds he).1]⟩ hx hx.1
  norm_num [projection] at hmono
  have hprod := mul_lt_mul'' rho_bounds.2 hb.2.2.2.2.2.2.2
    (by linarith [rho_bounds.1]) hb.2.2.2.2.2.2.1
  refine ⟨hmono,?_,hpd,?_⟩
  · dsimp [projection]
    linarith [ht.2.1]
  · dsimp [projectionD]
    linarith [rho_bounds.2,hb.2.2.2.2.2.2.1]

theorem axial_sourceD_upper (r : Row) {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    sourceD r (contact 0 x)<p r+q r*(50/43:ℝ) := by
  have hb := axial_bounds he hx
  have hr : K x/v x<(50/43:ℝ) := by
    apply (div_lt_iff₀ (by linarith [hb.2.2.1] : 0<v x)).2
    linarith [hb.2.1]
  have hq : 0<q r := by linarith [(coefficients r).1]
  have hh := mul_lt_mul_of_pos_left hr hq
  dsimp [sourceD,ratio,K,v] at *
  linarith

theorem axial_curvature_bound (r : Row) {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    q r*Q0*(227/250:ℝ)^2/(7/5:ℝ)^3-(p r+q r*(50/43:ℝ))/2<F2 r x := by
  have hb := axial_bounds he hx
  have hq : 0<q r := by linarith [(coefficients r).1]
  have hD := source_ratioD_lower (before_domain he hx).2.2
  have hsquare : (227/250:ℝ)^2<(h x)^2 := by nlinarith [hb.2.2.2.2.1]
  have h1 := mul_lt_mul_of_pos_left hsquare
    (mul_pos hq (show 0<Q0/(7/5:ℝ)^3 by norm_num [Q0]))
  have h2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hD hq.le) (sq_nonneg (h x))
  have hL := axial_sourceD_upper r he hx
  have hL0 : 0≤ sourceD r (contact 0 x) := by
    linarith [sourceD_lower r (before_domain he hx).2.2,(coefficients r).2.2.1]
  have h3 := mul_le_mul hL.le (show K x-1≤(1/2:ℝ) by linarith [hb.2.1])
    (by linarith [hb.1] : 0≤K x-1) (by linarith)
  have e : q r*Q0*(227/250:ℝ)^2/(7/5:ℝ)^3=q r*(Q0/(7/5:ℝ)^3)*(227/250)^2 := by ring
  dsimp only [F2,sourceDD]
  rw [e]
  linarith only [h1,h2,h3]

theorem axial_curvature_pair (r : Row) (hr : r=3∨r=4) {e x : ℝ}
    (he : IsEvent e) (hx : x∈Icc 0 e) : (1/4:ℝ)<F2 r x := by
  have hh := axial_curvature_bound r he hx
  rcases hr with rfl | rfl <;> norm_num [p,q,Q0] at hh <;> linarith

theorem axial_curvature_one {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    (47/100:ℝ)<F2 1 x := by
  have hh := axial_curvature_bound 1 he hx
  norm_num [p,q,Q0] at hh
  linarith

theorem axial_curvature_zero {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    (99/100:ℝ)<F2 0 x := by
  have hb := axial_bounds he hx
  have hD := source_ratioD_lower (before_domain he hx).2.2
  have hL : sourceD 0 (contact 0 x)<(879/1000:ℝ) := by
    have hh := axial_sourceD_upper 0 he hx
    norm_num [p,q] at hh
    linarith
  have hL0 : 0≤ sourceD 0 (contact 0 x) := by
    have hh := sourceD_lower 0 (before_domain he hx).2.2
    norm_num [p,q] at hh
    linarith
  have hsquare : (914575671/1000000000:ℝ)^2≤(h x)^2 := by nlinarith [hb.2.2.2.2.1]
  have h1 := mul_le_mul
    (mul_le_mul_of_nonneg_left hD (show 0≤q 0 by norm_num [q])) hsquare
    (by positivity) (mul_nonneg (by norm_num [q])
      (SameContact.ratioD_pos (Same.primary_domain (before_domain he hx).2.2)).le)
  have h2 := mul_le_mul hL.le (show K x-1≤(1/2:ℝ) by linarith [hb.2.1])
    (by linarith [hb.1] : 0≤K x-1) (by norm_num)
  dsimp [F2,sourceDD]
  norm_num [q,Q0] at *
  nlinarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper
