module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterOuterPositiveContact

/-!
# The unique positive-core interior circle contact

Uncompiled transcription of section 2.3 of the circle-and-side note.
The stationarity equation is solved in the original shifted source
coordinates. Its positive root lies between the axial contact and the
source-axis endpoint whenever the axial target derivative is nonpositive.
The explicit root differentiates to the same nonnegative derivative
used in the hand proof.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterPositive
open CommonQuarter CorePairGeometry Arithmetic

def lam (r : Row) (x : ℝ) : ℝ := ocG r/Real.cos x
def lamD (r : Row) (x : ℝ) : ℝ := ocG r*Real.sin x/(Real.cos x)^2
def L (r : Row) (x : ℝ) : ℝ := lam r x-ocP r
def N (r : Row) (x : ℝ) : ℝ := Real.sqrt ((L r x)^2+(ocQ r)^2)
def criticalU (r : Row) (x : ℝ) : ℝ := radius*(L r x/N r x)
def criticalD (r : Row) (x : ℝ) : ℝ := radius*(ocQ r)^2*lamD r x/(N r x)^3
def X (r : Row) (x : ℝ) : ℝ := (criticalU r x-1-c0*Real.sin x)/Real.cos x
def Xd (r : Row) (x : ℝ) : ℝ :=
  criticalD r x/Real.cos x-c0+X r x*(Real.sin x/Real.cos x)

theorem p_lt_g (r : Row) (hr : Rows r) : ocP r<ocG r := by
  fin_cases r <;> norm_num [Rows,sourcePositive,targetPositive,ocP,ocG] at hr ⊢

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
  convert (hasDerivAt_const x (ocG r)).div (Real.hasDerivAt_cos x)
    (by linarith [(axial_trig hx).1] : Real.cos x≠0) using 1 <;>
      dsimp [lam,lamD] <;> ring

theorem N_hasDerivAt (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) :
    HasDerivAt (N r) (L r x*lamD r x/N r x) x := by
  have hh := ((((lam_hasDerivAt r hx).sub_const (ocP r)).pow 2).add_const
    ((ocQ r)^2)).sqrt (Real.sqrt_pos.mp (N_positive r hr x)).ne'
  convert hh using 1
  · rfl
  · dsimp [L,N]
    field_simp [(N_positive r hr x).ne']
    ring

theorem criticalU_hasDerivAt (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) :
    HasDerivAt (criticalU r) (criticalD r x) x := by
  have hN := (N_positive r hr x).ne'
  have hh := (((lam_hasDerivAt r hx).sub_const (ocP r)).div
    (N_hasDerivAt r hr hx) hN).const_mul radius
  convert hh using 1
  · rfl
  · calc
      criticalD r x=radius*lamD r x*((N r x)^2-(L r x)^2)/(N r x)^3 := by
        rw [N_square]
        dsimp [criticalD]
        ring
      _=radius*((lamD r x*N r x-L r x*(L r x*lamD r x/N r x))/(N r x)^2) := by
        field_simp [hN]
        ring

theorem criticalD_nonneg (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) :
    0≤criticalD r x := by
  have hg := (coefficients r hr).2.2.2.1.le
  have hs := (positive_trig (angle_small hx)).2.2.1
  have hR : 0≤radius := by linarith [radius_bounds.1]
  dsimp [criticalD,lamD]
  exact div_nonneg (mul_nonneg (mul_nonneg hR (sq_nonneg _))
    (div_nonneg (mul_nonneg hg hs) (sq_nonneg _))) (pow_nonneg (N_positive r hr x).le 3)

theorem critical_comparison_identity (r : Row) {x u : ℝ} (hu : u∈coordinateDomain) :
    (radius*L r x)^2-(u*N r x)^2=
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
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hgap : ocQ r*u≤L r x*V u := (div_le_iff₀ hV).1 (by
    dsimp [Md,L] at hm ⊢
    linarith)
  have hs := mul_nonneg (sub_nonneg.mpr hgap)
    (show 0≤L r x*V u+ocQ r*u by positivity)
  have hid := critical_comparison_identity r (x:=x) hu
  have hleft0 := mul_nonneg hu0 hN.le
  have hright0 := mul_nonneg hR.le hL.le
  have hn : u*N r x≤radius*L r x := by nlinarith
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
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hgap : L r x*V u≤ocQ r*u := (le_div_iff₀ hV).1 (by
    dsimp [Md,L] at hm ⊢
    linarith)
  have hs := mul_nonneg (sub_nonneg.mpr hgap)
    (show 0≤L r x*V u+ocQ r*u by positivity)
  have hid := critical_comparison_identity r (x:=x) hu
  have hleft0 := mul_nonneg hu0 hN.le
  have hright0 := mul_nonneg hR.le hL.le
  have hn : radius*L r x≤u*N r x := by nlinarith
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
    (w-ocP r+ocQ r)/2-radius*Real.sqrt ((w-ocP r)^2+(ocQ r)^2)=
      M r u-w*(u-1/2) := by
  have hv := V_positive hu
  have hq : 0<ocQ r := by linarith [(coefficients r hr).2.2.1]
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hd : w-ocP r=ocQ r*u/V u := by rw [hw,Md]; ring
  have hs : (radius*ocQ r/V u)^2=(w-ocP r)^2+(ocQ r)^2 := by
    rw [hd]
    calc
      (radius*ocQ r/V u)^2=(ocQ r)^2*(u^2+(V u)^2)/(V u)^2 := by
        field_simp [hv.ne']
        rw [radius_sq,← V_square hu]
        ring
      _=(ocQ r*u/V u)^2+(ocQ r)^2 := by field_simp [hv.ne']; ring
  have hroot : Real.sqrt ((w-ocP r)^2+(ocQ r)^2)=radius*ocQ r/V u := by
    rw [← hs,Real.sqrt_sq (by positivity : 0≤radius*ocQ r/V u)]
  rw [hroot,hw]
  dsimp [M,Md]
  field_simp [hv.ne']
  rw [radius_sq,← V_square hu]
  ring

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterPositive
