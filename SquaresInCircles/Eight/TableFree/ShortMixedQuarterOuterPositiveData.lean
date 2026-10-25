module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterReferences
public import SquaresInCircles.Eight.TableFree.CenteredMonomialBounds

/-!
# Exact source labels for outer-to-positive-core primary contacts

Uncompiled transcription of section 2 of the circle-and-side hand note.
The eight rows are intrinsic signed role cases. U is the shifted source
primary coordinate; V is its actual positive circle root. The axial
contact and its first two derivatives are written literally.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterPositive
open CommonQuarter CorePairGeometry Arithmetic

def Rows (r : Row) : Prop := sourcePositive r=false ∧ targetPositive r=true
def Interior (r : Row) : Prop := r=3 ∨ r=7 ∨ r=14 ∨ r=15
def Rising (r : Row) : Prop := r=2 ∨ r=6 ∨ r=7 ∨ r=20 ∨ r=21
def c0 : ℝ := 13/12
def J : ℝ := 205/144
/-- The axial angles end just past the axial event, where `U = outerAxial+1/2` (near .44100),
and before `U` leaves `coordinateDomain` at `383/200` (near .44155). -/
def cap : ℝ := 4413/10000
def coordinateDomain : Set ℝ := Icc (3/2:ℝ) (383/200)
def angleDomain : Set ℝ := Icc 0 cap
def V (U : ℝ) : ℝ := Real.sqrt (Q0-U^2)
def M (r : Row) (U : ℝ) : ℝ := ocP r*(U-1/2)-ocQ r*(V U-1/2)
def Md (r : Row) (U : ℝ) : ℝ := ocP r+ocQ r*U/V U
def Mdd (r : Row) (U : ℝ) : ℝ := ocQ r*Q0/(V U)^3
def Mddd (r : Row) (U : ℝ) : ℝ := 3*ocQ r*Q0*U/(V U)^5
def U (x : ℝ) : ℝ := 1+c0*Real.sin x+Real.cos x/2
def h (x : ℝ) : ℝ := c0*Real.cos x-Real.sin x/2
def curvature (r : Row) (u : ℝ) : ℝ :=
  Mdd r u*(J-(u-1)^2)-Md r u*(u-1)
def curvatureD (r : Row) (u : ℝ) : ℝ :=
  Mddd r u*(J-(u-1)^2)-3*Mdd r u*(u-1)-Md r u
def E (u : ℝ) : ℝ := u^2-(Q0+1-J)*u+Q0
def K (r : Row) (x : ℝ) : ℝ := Real.pi/2-x+ocC r+M r (U x)
def Kd (r : Row) (x : ℝ) : ℝ := -1+Md r (U x)*h x
def Kdd (r : Row) (x : ℝ) : ℝ := curvature r (U x)
def H (r : Row) (x : ℝ) : ℝ := Md r (U x)*Real.cos x-ocG r
def Hd (r : Row) (x : ℝ) : ℝ :=
  Mdd r (U x)*h x*Real.cos x-Md r (U x)*Real.sin x
def reference (r : Row) : ℝ := if r=3 then 1/40 else if r=14 then 59/500 else 2389/20000

theorem rows (r : Row) (hr : Rows r) :
    r=2 ∨ r=3 ∨ r=6 ∨ r=7 ∨ r=14 ∨ r=15 ∨ r=20 ∨ r=21 := by
  fin_cases r <;> simp [Rows,sourcePositive,targetPositive] at hr ⊢

theorem coefficients (r : Row) (hr : Rows r) :
    -(25777/50000:ℝ)≤ocP r ∧ ocP r<(253/1000)*ocQ r ∧
      9593/12500≤ocQ r ∧ 0<ocG r ∧ ocG r≤22771/20000 := by
  rcases rows r hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [ocP,ocQ,ocG]

theorem V_positive {u : ℝ} (hu : u∈coordinateDomain) : 0<V u := by
  have hu2 := pow_le_pow_left₀ (show 0≤u by exact (by norm_num : (0:ℝ)≤3/2).trans hu.1) hu.2 2
  apply Real.sqrt_pos.mpr
  norm_num [Q0] at hu2 ⊢
  nlinarith

theorem V_square {u : ℝ} (hu : u∈coordinateDomain) : (V u)^2+u^2=Q0 := by
  have hh := Real.sq_sqrt ((Real.sqrt_pos.mp (V_positive hu)).le)
  dsimp [V] at *
  linarith

theorem V_bounds {u : ℝ} (hu : u∈coordinateDomain) :
    (249/500:ℝ)<V u ∧ V u<1291/1000 ∧ (V u)^2<833/500 := by
  have hp := V_positive hu
  have hs := V_square hu
  have hu0 : 0≤u := by dsimp [coordinateDomain] at hu; linarith [hu.1]
  have hl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3/2) hu.1 2
  have hh := pow_le_pow_left₀ hu0 hu.2 2
  norm_num [Q0] at hs
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem V_hasDerivAt {u : ℝ} (hu : u∈coordinateDomain) : HasDerivAt V (-u/V u) u := by
  have h1 : HasDerivAt (fun y : ℝ => Q0-y^2) (-(2*u)) u := by
    simpa using (hasDerivAt_pow 2 u).const_sub Q0
  have hh : HasDerivAt V (-(2*u)/(2*Real.sqrt (Q0-u^2))) u :=
    h1.sqrt (Real.sqrt_pos.mp (V_positive hu)).ne'
  exact hh.congr_deriv (by simp only [V]; ring)

theorem M_hasDerivAt (r : Row) {u : ℝ} (hu : u∈coordinateDomain) :
    HasDerivAt (M r) (Md r u) u := by
  have hh : HasDerivAt (M r) (ocP r*1-ocQ r*(-u/V u)) u :=
    (((hasDerivAt_id' u).sub_const (1/2)).const_mul (ocP r)).sub
      (((V_hasDerivAt hu).sub_const (1/2)).const_mul (ocQ r))
  exact hh.congr_deriv (by simp only [Md]; ring)

theorem Md_hasDerivAt (r : Row) {u : ℝ} (hu : u∈coordinateDomain) :
    HasDerivAt (Md r) (Mdd r u) u := by
  have hn := (V_positive hu).ne'
  have hh : HasDerivAt (Md r) ((ocQ r*1*V u-ocQ r*u*(-u/V u))/(V u)^2) u :=
    (((hasDerivAt_id' u).const_mul (ocQ r)).div (V_hasDerivAt hu) hn).const_add (ocP r)
  refine hh.congr_deriv ?_
  simp only [Mdd]
  rw [← V_square hu]
  field_simp
  ring

theorem Mdd_hasDerivAt (r : Row) {u : ℝ} (hu : u∈coordinateDomain) :
    HasDerivAt (Mdd r) (Mddd r u) u := by
  have hn := (V_positive hu).ne'
  have hh := (hasDerivAt_const u (ocQ r*Q0)).div ((V_hasDerivAt hu).pow 3) (pow_ne_zero 3 hn)
  convert hh using 1
  · rfl
  · dsimp [Mdd,Mddd]
    field_simp [hn]
    ring

theorem Md_positive (r : Row) (hr : Rows r) {u : ℝ} (hu : u∈coordinateDomain) : 0<Md r u := by
  have hb := coefficients r hr
  have hV := V_bounds hu
  have hq : 0<ocQ r := by linarith [hb.2.2.1]
  have huq := mul_le_mul_of_nonneg_left hu.1 hq.le
  have hpV := mul_le_mul_of_nonneg_right hb.1 (V_positive hu).le
  have hVmax := mul_le_mul_of_nonpos_left hV.2.1.le (by norm_num : (-(25777/50000):ℝ)≤0)
  have hh : -ocP r<ocQ r*u/V u := (lt_div_iff₀ (V_positive hu)).2 (by nlinarith)
  dsimp [Md]
  linarith

theorem Mdd_positive (r : Row) (hr : Rows r) {u : ℝ} (hu : u∈coordinateDomain) : 0<Mdd r u :=
  div_pos (mul_pos (by linarith [(coefficients r hr).2.2.1]) (by norm_num [Q0]))
    (pow_pos (V_positive hu) 3)

theorem M_monotone (r : Row) (hr : Rows r) : MonotoneOn (M r) coordinateDomain :=
  monoOn_of_hasDeriv_nonneg
    (fun u hu => (M_hasDerivAt r hu).continuousAt.continuousWithinAt)
    (fun u hu => M_hasDerivAt r (Ioo_subset_Icc_self hu))
    (fun u hu => (Md_positive r hr (Ioo_subset_Icc_self hu)).le)

theorem Md_monotone (r : Row) (hr : Rows r) : MonotoneOn (Md r) coordinateDomain :=
  monoOn_of_hasDeriv_nonneg
    (fun u hu => (Md_hasDerivAt r hu).continuousAt.continuousWithinAt)
    (fun u hu => Md_hasDerivAt r (Ioo_subset_Icc_self hu))
    (fun u hu => (Mdd_positive r hr (Ioo_subset_Icc_self hu)).le)

theorem U_hasDerivAt (x : ℝ) : HasDerivAt U (h x) x := by
  have hh : HasDerivAt U (c0*Real.cos x+Real.sin x*0+(-Real.sin x)/2) x := by
    have h1 := (((Real.hasDerivAt_sin x).const_mul c0).const_add 1).add
      ((Real.hasDerivAt_cos x).div_const 2)
    exact h1.congr_deriv (by ring)
  exact hh.congr_deriv (by simp only [h]; ring)
theorem h_hasDerivAt (x : ℝ) : HasDerivAt h (1-U x) x := by
  have hh : HasDerivAt h (c0*(-Real.sin x)-Real.cos x/2) x :=
    ((Real.hasDerivAt_cos x).const_mul c0).sub ((Real.hasDerivAt_sin x).div_const 2)
  exact hh.congr_deriv (by simp only [U]; ring)
theorem h_square (x : ℝ) : (h x)^2=J-(U x-1)^2 := by
  dsimp [h,U,J,c0]
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem h_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<h x := by
  have ht := positive_trig hx
  dsimp [h,c0]
  linarith [ht.1,ht.2.2.2.1]
theorem U_strictMono : StrictMonoOn U (Icc 0 (7/10)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (7/10))
  · exact fun x _ => (U_hasDerivAt x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(U_hasDerivAt x).deriv]
    exact h_positive (Ioo_subset_Icc_self hx)

theorem actual_source {a b : ℝ} (hs : OuterState a b) : V (a+1/2)=b+1/2 := by
  have he : Q0-(a+1/2)^2=(b+1/2)^2 := by linarith [hs.2.2]
  rw [V,he,Real.sqrt_sq (by linarith [hs.1] : 0≤b+1/2)]

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterPositive
