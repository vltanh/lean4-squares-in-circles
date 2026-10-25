module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterReferences
public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroPositiveCore

/-!
# Eight squares: the original six core-source negative families

The original weak separating inequality places the outer target after its exact contact. A
linear functional on this subarc is bounded by its contact and diagonal values
(`outer_subarc_lower`, `contact_or_diagonal`). A positive primary coefficient uses circle
concavity; the two remaining signs use direct monotonicity and the diagonal tangent. The six
families are `opposite_core_negative`.
-/

section
/-!
## Exact source labels for outer-to-positive-core primary contacts

The eight rows are intrinsic signed role cases. U is the shifted source
primary coordinate; V is its actual positive circle root. The axial
contact and its first two derivatives are written literally.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
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
    (fun _ hu => (M_hasDerivAt r hu).continuousAt.continuousWithinAt)
    (fun _ hu => M_hasDerivAt r (Ioo_subset_Icc_self hu))
    (fun _ hu => (Md_positive r hr (Ioo_subset_Icc_self hu)).le)

theorem Md_monotone (r : Row) (hr : Rows r) : MonotoneOn (Md r) coordinateDomain :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hu => (Md_hasDerivAt r hu).continuousAt.continuousWithinAt)
    (fun _ hu => Md_hasDerivAt r (Ioo_subset_Icc_self hu))
    (fun _ hu => (Mdd_positive r hr (Ioo_subset_Icc_self hu)).le)

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

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
end
end
end

section
/-!
## Actual core-source negative zero-edge contacts

The original separator forces the angle below `.32`. The endpoint at
the largest core coordinate is the explicitly rotated circle contact
`(U-1/2,V-1/2)`. Its first derivatives and its speed derivative are proved
on the entire interval. Whenever an original pair is feasible, this
continued contact is on the actual canonical outer arc and precedes the
original outer state.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero.CoreContact

open CommonQuarter CorePairGeometry Arithmetic

def cap : ℝ := 8/25
def Z (x : ℝ) : ℝ := Real.cos x+1/2-CoreAngleEndpoint.diagonal
def Y (x : ℝ) : ℝ := Real.sqrt (Q0-(Z x)^2)
def U (x : ℝ) : ℝ := Real.cos x*Y x-Real.sin x*Z x
def V (x : ℝ) : ℝ := Real.sin x*Y x+Real.cos x*Z x
def speed (x : ℝ) : ℝ := 1-Real.sin x/Y x
def speedD (x : ℝ) : ℝ :=
  (Z x*(Real.sin x)^2-Real.cos x*(Y x)^2)/(Y x)^3
def cutMargin (x : ℝ) : ℝ := CoreAngleEndpoint.diagonal-1/2+
  (outerDiagonal-1/2)*Real.cos x-(outerDiagonal+1/2)*Real.sin x

lemma cap_trig : (3932/12500:ℝ)<Real.sin cap ∧ Real.sin cap<31457/100000 ∧
    (94923/100000:ℝ)<Real.cos cap ∧ Real.cos cap<23731/25000 := by
  have hs := sin_lower_seven (x := cap) (by norm_num [cap])
  have hsU := sin_upper_five (x := cap) (by norm_num [cap])
  have hc := cos_lower_six (x := cap) (by norm_num [cap])
  have hcU := cos_upper_four (x := cap) (by norm_num [cap])
  simp only [cap] at hs hsU hc hcU ⊢
  norm_num at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma trig_bounds {x : ℝ} (hx : x∈Icc 0 cap) :
    0≤Real.sin x ∧ Real.sin x<63/200 ∧ (949/1000:ℝ)<Real.cos x ∧ Real.cos x≤1 := by
  have hcap : cap∈Icc 0 (7/10) := by norm_num [cap]
  have hx' : x∈Icc 0 (7/10) := ⟨hx.1,hx.2.trans hcap.2⟩
  have hs := sin_mono hx' hcap hx.2
  have hc := cos_anti hx' hcap hx.2
  exact ⟨(positive_trig hx').2.2.1,by linarith [cap_trig.2.1],
    by linarith [cap_trig.2.2.1],Real.cos_le_one x⟩

lemma cutMargin_antitone : AntitoneOn cutMargin (Icc 0 (7/10)) := by
  have hd (x : ℝ) : HasDerivAt cutMargin
      (-(outerDiagonal-1/2)*Real.sin x-(outerDiagonal+1/2)*Real.cos x) x := by
    have h : HasDerivAt (fun y => CoreAngleEndpoint.diagonal-1/2+
        (outerDiagonal-1/2)*Real.cos y-(outerDiagonal+1/2)*Real.sin y)
        ((outerDiagonal-1/2)*(-Real.sin x)-(outerDiagonal+1/2)*Real.cos x) x :=
      (((Real.hasDerivAt_cos x).const_mul (outerDiagonal-1/2)).const_add
        (CoreAngleEndpoint.diagonal-1/2)).sub
          ((Real.hasDerivAt_sin x).const_mul (outerDiagonal+1/2))
    exact h.congr_deriv (by ring)
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (hd x).continuousAt.continuousWithinAt
  · exact fun x _ => hd x
  · intro x hx
    have ht := positive_trig (Ioo_subset_Icc_self hx)
    have h₁ := mul_nonneg (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1]) ht.2.2.1
    have h₂ := mul_nonneg (show 0≤outerDiagonal+1/2 by linarith [outer_endpoint_bounds.2.2.1])
      (show 0≤Real.cos x by linarith [ht.1])
    linarith

lemma cutMargin_cap_neg : cutMargin cap<0 := by
  have ht := cap_trig
  have hd := fine_diagonal_bounds
  have hc := CoreAngleEndpoint.diagonal_bounds
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.le
    (show 0≤outerDiagonal-1/2 by linarith [hd.1])
  have hsin := mul_le_mul_of_nonneg_left ht.1.le
    (show 0≤outerDiagonal+1/2 by linarith [hd.1])
  dsimp [cutMargin]
  nlinarith [hd.1,hd.2,hc.2]

theorem original_angle_cut {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) : x<cap := by
  have htr := positive_trig hx
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.2.2
  have htar := outer_bounds ht
  have hA := mul_le_mul_of_nonneg_right htar.1 htr.2.2.1
  have hB := mul_le_mul_of_nonneg_right htar.2.2.2.1 (show 0≤Real.cos x by linarith [htr.1])
  have hh : 0≤cutMargin x := by dsimp [cutMargin]; linarith
  by_contra! hlarge
  have hcap : cap∈Icc 0 (7/10) := by norm_num [cap]
  have hbad := cutMargin_antitone hcap hx hlarge
  linarith [cutMargin_cap_neg]

lemma Z_bounds {x : ℝ} (hx : x∈Icc 0 cap) : (89/100:ℝ)<Z x ∧ Z x<471/500 := by
  have ht := trig_bounds hx
  have hd := CoreAngleEndpoint.diagonal_bounds
  dsimp [Z]
  exact ⟨by linarith [ht.2.2.1,hd.2],by linarith [ht.2.2.2,hd.1]⟩

lemma radicand_pos {x : ℝ} (hx : x∈Icc 0 cap) : 0<Q0-(Z x)^2 := by
  have hz := Z_bounds hx
  norm_num [Q0]
  nlinarith

lemma Y_pos {x : ℝ} (hx : x∈Icc 0 cap) : 0<Y x := Real.sqrt_pos.mpr (radicand_pos hx)
lemma Y_sq {x : ℝ} (hx : x∈Icc 0 cap) : (Y x)^2+(Z x)^2=Q0 := by
  have hs := Real.sq_sqrt (radicand_pos hx).le
  dsimp [Y]
  linarith

lemma Y_bounds {x : ℝ} (hx : x∈Icc 0 cap) : (87/50:ℝ)<Y x ∧ Y x<177/100 := by
  have hy := Y_pos hx
  have hs := Y_sq hx
  have hz := Z_bounds hx
  norm_num [Q0] at hs
  constructor <;> nlinarith [hz.1,hz.2]

lemma Z_hasDerivAt (x : ℝ) : HasDerivAt Z (-Real.sin x) x :=
  ((Real.hasDerivAt_cos x).add_const (1/2)).sub_const CoreAngleEndpoint.diagonal

lemma Y_hasDerivAt {x : ℝ} (hx : x∈Icc 0 cap) :
    HasDerivAt Y (Z x*Real.sin x/Y x) x := by
  have hh : HasDerivAt (fun y => Real.sqrt (Q0-(Z y)^2))
      ((0-(2:ℕ)*Z x^(2-1)*(-Real.sin x))/(2*Real.sqrt (Q0-(Z x)^2))) x :=
    ((hasDerivAt_const x Q0).sub ((Z_hasDerivAt x).pow 2)).sqrt (radicand_pos hx).ne'
  refine hh.congr_deriv ?_
  have hn := (Y_pos hx).ne'
  change (0-(2:ℕ)*Z x^(2-1)*(-Real.sin x))/(2*Y x)=Z x*Real.sin x/Y x
  field_simp
  push_cast
  ring

lemma U_hasDerivAt {x : ℝ} (hx : x∈Icc 0 cap) :
    HasDerivAt U (-V x*speed x) x := by
  have hn := (Y_pos hx).ne'
  have hh := ((Real.hasDerivAt_cos x).mul (Y_hasDerivAt hx)).sub
    ((Real.hasDerivAt_sin x).mul (Z_hasDerivAt x))
  convert hh using 1
  · rfl
  · dsimp [U,V,speed]
    field_simp [hn]
    ring

lemma V_hasDerivAt {x : ℝ} (hx : x∈Icc 0 cap) :
    HasDerivAt V (U x*speed x) x := by
  have hn := (Y_pos hx).ne'
  have hh := ((Real.hasDerivAt_sin x).mul (Y_hasDerivAt hx)).add
    ((Real.hasDerivAt_cos x).mul (Z_hasDerivAt x))
  convert hh using 1
  · rfl
  · dsimp [U,V,speed]
    field_simp [hn]
    ring

lemma speed_hasDerivAt {x : ℝ} (hx : x∈Icc 0 cap) :
    HasDerivAt speed (speedD x) x := by
  have hn := (Y_pos hx).ne'
  have hh := ((Real.hasDerivAt_sin x).div (Y_hasDerivAt hx) hn).const_sub 1
  convert hh using 1
  · rfl
  · dsimp [speed,speedD]
    field_simp [hn]
    ring

lemma speed_pos {x : ℝ} (hx : x∈Icc 0 cap) : 0<speed x := by
  have ht := trig_bounds hx
  have hy := Y_bounds hx
  have hh : Real.sin x/Y x<1 := (div_lt_one (Y_pos hx)).2 (by linarith [ht.2.1,hy.1])
  dsimp [speed]
  linarith

lemma speedD_neg {x : ℝ} (hx : x∈Icc 0 cap) : speedD x<0 := by
  have ht := trig_bounds hx
  have hz := Z_bounds hx
  have hy := Y_bounds hx
  have hs2 := pow_le_pow_left₀ ht.1 ht.2.1.le 2
  have hy2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤87/50) hy.1.le 2
  have h₁ := mul_le_mul hz.2.le hs2 (sq_nonneg (Real.sin x)) (by norm_num)
  have h₂ := mul_le_mul ht.2.2.1.le hy2 (by positivity) (show 0≤Real.cos x by linarith [ht.2.2.1])
  apply div_neg_of_neg_of_pos _ (pow_pos (Y_pos hx) 3)
  nlinarith

lemma coarse_coordinates {x : ℝ} (hx : x∈Icc 0 cap) : (27/20:ℝ)<U x ∧ (21/25:ℝ)<V x := by
  have ht := trig_bounds hx
  have hz := Z_bounds hx
  have hy := Y_bounds hx
  have hcy := mul_le_mul ht.2.2.1.le hy.1.le (by norm_num) (show 0≤Real.cos x by linarith [ht.2.2.1])
  have hsz := mul_le_mul ht.2.1.le hz.2.le (show 0≤Z x by linarith [hz.1]) (by norm_num)
  have hcz := mul_le_mul ht.2.2.1.le hz.1.le (by norm_num) (show 0≤Real.cos x by linarith [ht.2.2.1])
  have hsy := mul_nonneg ht.1 (Y_pos hx).le
  dsimp [U,V]
  exact ⟨by nlinarith,by nlinarith⟩

lemma U_antitone : AntitoneOn U (Icc 0 cap) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x hx => (U_hasDerivAt hx).continuousAt.continuousWithinAt
  · exact fun x hx => U_hasDerivAt (Ioo_subset_Icc_self hx)
  · intro x hx
    have hh := coarse_coordinates (Ioo_subset_Icc_self hx)
    have hs := speed_pos (Ioo_subset_Icc_self hx)
    nlinarith [hh.2]

lemma V_monotone : MonotoneOn V (Icc 0 cap) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x hx => (V_hasDerivAt hx).continuousAt.continuousWithinAt
  · exact fun x hx => V_hasDerivAt (Ioo_subset_Icc_self hx)
  · intro x hx
    exact mul_nonneg (by linarith [(coarse_coordinates (Ioo_subset_Icc_self hx)).1])
      (speed_pos (Ioo_subset_Icc_self hx)).le

lemma endpoint_root : (17671/10000:ℝ)<Y cap ∧ Y cap<17673/10000 := by
  have hcap : cap∈Icc 0 cap := by norm_num [cap]
  have hs := Y_sq hcap
  have hp := Y_pos hcap
  have ht := cap_trig
  have hd := CoreAngleEndpoint.diagonal_bounds
  have hz : (8903/10000:ℝ)<Z cap ∧ Z cap<11129/12500 := by
    dsimp [Z]
    exact ⟨by linarith [ht.2.2.1,hd.2],by linarith [ht.2.2.2,hd.1]⟩
  norm_num [Q0] at hs
  constructor <;> nlinarith [hz.1,hz.2]

lemma endpoint_coordinates : (139/100:ℝ)<U cap ∧ U cap<7/5 ∧
    (7/5:ℝ)<V cap ∧ V cap<141/100 := by
  have ht := cap_trig
  have hy := endpoint_root
  have hd := CoreAngleEndpoint.diagonal_bounds
  have hz : (89/100:ℝ)<Z cap ∧ Z cap<891/1000 := by
    dsimp only [Z]
    exact ⟨by linarith only [ht.2.2.1,hd.2],by linarith only [ht.2.2.2,hd.1]⟩
  have hc0 : 0≤Real.cos cap := (lt_trans (by norm_num) ht.2.2.1).le
  have hs0 : 0≤Real.sin cap := (lt_trans (by norm_num) ht.1).le
  have hy0 : 0≤Y cap := (lt_trans (by norm_num) hy.1).le
  have hz0 : 0≤Z cap := (lt_trans (by norm_num) hz.1).le
  have hcyL := mul_le_mul ht.2.2.1.le hy.1.le (by norm_num) hc0
  have hcyU := mul_le_mul ht.2.2.2.le hy.2.le hy0 (by norm_num)
  have hszL := mul_le_mul ht.1.le hz.1.le (by norm_num) hs0
  have hszU := mul_le_mul ht.2.1.le hz.2.le hz0 (by norm_num)
  have hsyL := mul_le_mul ht.1.le hy.1.le (by norm_num) hs0
  have hsyU := mul_le_mul ht.2.1.le hy.2.le hy0 (by norm_num)
  have hczL := mul_le_mul ht.2.2.1.le hz.1.le (by norm_num) hc0
  have hczU := mul_le_mul ht.2.2.2.le hz.2.le hz0 (by norm_num)
  dsimp only [U,V]
  refine ⟨?_,?_,?_,?_⟩
  · exact lt_of_lt_of_le (by norm_num) (sub_le_sub hcyL hszU)
  · exact lt_of_le_of_lt (sub_le_sub hcyU hszL) (by norm_num)
  · exact lt_of_lt_of_le (by norm_num) (add_le_add hsyL hczL)
  · exact lt_of_le_of_lt (add_le_add hsyU hczU) (by norm_num)

lemma initial_coordinates : (87/50:ℝ)<U 0 ∧ U 0<7/4 ∧
    V 0=3/2-CoreAngleEndpoint.diagonal := by
  have h0 : (0:ℝ)∈Icc 0 cap := by norm_num [cap]
  have hp := Y_pos h0
  have hs := Y_sq h0
  have hd := CoreAngleEndpoint.diagonal_bounds
  have hy : Y 0<(7/4:ℝ) := by
    norm_num [Z,Q0] at hs
    nlinarith [hd.1,hd.2]
  have hU : U 0=Y 0 := by simp [U]
  have hV : V 0=3/2-CoreAngleEndpoint.diagonal := by
    simp only [V,Z,Real.sin_zero,Real.cos_zero]
    ring
  rw [hU,hV]
  exact ⟨(Y_bounds h0).1,hy,rfl⟩

lemma coordinates {x : ℝ} (hx : x∈Icc 0 cap) :
    (139/100:ℝ)<U x ∧ U x<7/4 ∧ (47/50:ℝ)<V x ∧ V x<141/100 := by
  have huL := U_antitone hx (by norm_num [cap]) hx.2
  have huU := U_antitone (by norm_num [cap]) hx hx.1
  have hvL := V_monotone (by norm_num [cap]) hx hx.1
  have hvU := V_monotone hx (by norm_num [cap]) hx.2
  have he := endpoint_coordinates
  have h0 := initial_coordinates
  have hd := CoreAngleEndpoint.diagonal_bounds
  exact ⟨he.1.trans_le huL,huU.trans_lt h0.2.1,
    by linarith [h0.2.2,hd.2],hvU.trans_lt he.2.2.2⟩

lemma circle {x : ℝ} (hx : x∈Icc 0 cap) : (U x)^2+(V x)^2=Q0 := by
  have hid : (U x)^2+(V x)^2=((Real.sin x)^2+(Real.cos x)^2)*((Y x)^2+(Z x)^2) := by
    dsimp [U,V]
    ring
  rw [hid,Real.sin_sq_add_cos_sq,one_mul,Y_sq hx]

lemma contact_equation (x : ℝ) :
    (V x-1/2)*Real.cos x-(U x-1/2)*Real.sin x=
      (1+Real.sin x+Real.cos x)/2-CoreAngleEndpoint.diagonal := by
  have hid : V x*Real.cos x-U x*Real.sin x=Z x := by
    dsimp [V,U]
    linear_combination (Z x)*(Real.sin_sq_add_cos_sq x)
  dsimp [Z] at hid
  linarith

/-- The exact contact belongs to the physical outer arc whenever the
original pair is feasible, and lies before the original outer point. -/
theorem original_contact {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 cap)
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    OuterState (U x-1/2) (V x-1/2) ∧ V x-1/2≤B := by
  have hc := coordinates hx
  have htr := trig_bounds hx
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.2.2
  have he := circle hx
  have hcontact := contact_equation x
  have hB : V x-1/2≤B := by
    by_contra! hbad
    have hA : U x-1/2<A := by
      by_contra! hnot
      have hp : 0≤A+1/2 := by linarith [ht.1,ht.2.1]
      have hsA := pow_le_pow_left₀ hp (show A+1/2≤U x by linarith) 2
      have hsB := mul_pos (show 0<V x-(B+1/2) by linarith)
        (show 0<V x+(B+1/2) by linarith [hc.2.2.1,ht.1])
      linarith [ht.2.2]
    have hprim := mul_le_mul_of_nonneg_right hA.le htr.1
    have hsec := mul_lt_mul_of_pos_right hbad (show 0<Real.cos x by linarith [htr.2.2.1])
    linarith
  have hBm : V x≤outerDiagonal+1/2 := by linarith [(outer_bounds ht).2.2.2.1]
  have hVsq := pow_le_pow_left₀ (show 0≤V x by linarith [hc.2.2.1]) hBm 2
  have hUV : V x≤U x := by
    by_contra! hlt
    have hp := mul_pos (sub_pos.mpr hlt) (show 0<V x+U x by linarith [hc.1,hc.2.2.1])
    linarith [diagonal_circle]
  have hcirc : (U x-1/2+1/2)^2+(V x-1/2+1/2)^2=Q0 := by
    rw [show U x-1/2+1/2=U x by ring,show V x-1/2+1/2=V x by ring]
    exact he
  exact ⟨⟨by linarith [hc.2.2.1],by linarith,hcirc⟩,hB⟩

end SquaresInCircles.Eight.ShortMixedZero.CoreContact
end
end
end

section
/-!
## Whole-interval lower bounds for the core-source negative contacts

The six continued circle contacts have strictly negative second
derivative. Their two endpoint values therefore suffice on the full
geometric interval. The competing diagonal branch is monotone, with
the direction determined by its original role coefficient. All bounds
below use rational endpoint and trigonometric estimates.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero.CoreContact

open CommonQuarter CorePairGeometry Arithmetic

def H (r : Row) (x : ℝ) : ℝ := -x+c r+g r*CoreAngleEndpoint.diagonal-
  p r*(U x-1/2)+q r*(V x-1/2)
def Hd (r : Row) (x : ℝ) : ℝ := -1+speed x*(p r*V x+q r*U x)
def Hdd (r : Row) (x : ℝ) : ℝ :=
  speedD x*(p r*V x+q r*U x)+(speed x)^2*(p r*U x-q r*V x)

lemma H_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 cap) :
    HasDerivAt (H r) (Hd r x) x := by
  have hh : HasDerivAt (fun y => -y+c r+g r*CoreAngleEndpoint.diagonal-
      p r*(U y-1/2)+q r*(V y-1/2))
      (-1-p r*(-V x*speed x)+q r*(U x*speed x)) x :=
    ((((hasDerivAt_id x).neg.add_const (c r)).add_const
      (g r*CoreAngleEndpoint.diagonal)).sub
        (((U_hasDerivAt hx).sub_const (1/2)).const_mul (p r))).add
          (((V_hasDerivAt hx).sub_const (1/2)).const_mul (q r))
  exact hh.congr_deriv (by dsimp [Hd]; ring)

lemma Hd_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 cap) :
    HasDerivAt (Hd r) (Hdd r x) x := by
  have hh : HasDerivAt (fun y => -1+speed y*(p r*V y+q r*U y))
      (speedD x*(p r*V x+q r*U x)+speed x*(p r*(U x*speed x)+q r*(-V x*speed x))) x :=
    ((speed_hasDerivAt hx).mul (((V_hasDerivAt hx).const_mul (p r)).add
      ((U_hasDerivAt hx).const_mul (q r)))).const_add (-1)
  exact hh.congr_deriv (by dsimp [Hdd]; ring)

lemma contact_coefficients (r : Row) {x : ℝ} (hx : x∈Icc 0 cap) :
    0<p r*V x+q r*U x ∧ p r*U x-q r*V x<0 := by
  have hc := coordinates hx
  fin_cases r <;> norm_num [p,q] <;>
    constructor <;> nlinarith [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

lemma Hdd_neg (r : Row) {x : ℝ} (hx : x∈Icc 0 cap) : Hdd r x<0 := by
  have hp := contact_coefficients r hx
  have h₁ := mul_neg_of_neg_of_pos (speedD_neg hx) hp.1
  have h₂ := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (speed x)) hp.2.le
  dsimp [Hdd]
  linarith

lemma H_concave (r : Row) : ConcaveOn ℝ (Icc 0 cap) (H r) :=
  concave_of_deriv2 (fun _ hx => H_hasDerivAt r hx)
    (fun _ hx => Hd_hasDerivAt r hx) (fun _ hx => (Hdd_neg r hx).le)

lemma H_endpoints (r : Row) : (449/500:ℝ)<H r 0 ∧ (449/500:ℝ)<H r cap := by
  have h0 := initial_coordinates
  have he := endpoint_coordinates
  have hd := CoreAngleEndpoint.diagonal_bounds
  have hcap : cap=8/25 := rfl
  constructor
  · rw [H,h0.2.2]
    fin_cases r <;> norm_num [c,p,q,g] <;>
      linarith only [h0.1,h0.2.1,hd.1,hd.2]
  · fin_cases r <;> norm_num [H,c,p,q,g] <;>
      linarith only [he.1,he.2.1,he.2.2.1,he.2.2.2,hd.1,hd.2,hcap]

theorem H_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 cap) : (449/500:ℝ)<H r x :=
  concave_gt_of_endpoints (H_concave r) hx (H_endpoints r).1 (H_endpoints r).2

def G (r : Row) (x : ℝ) : ℝ := -x+c r+(q r-p r)*outerDiagonal+
  g r*(1/2+(1/2+outerDiagonal)*Real.sin x+(1/2-outerDiagonal)*Real.cos x)
def Gd (r : Row) (x : ℝ) : ℝ := -1+
  g r*((1/2+outerDiagonal)*Real.cos x+(outerDiagonal-1/2)*Real.sin x)

lemma G_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (G r) (Gd r x) x := by
  have hh : HasDerivAt (fun y => -y+c r+(q r-p r)*outerDiagonal+
      g r*(1/2+(1/2+outerDiagonal)*Real.sin y+(1/2-outerDiagonal)*Real.cos y))
      (-1+g r*((1/2+outerDiagonal)*Real.cos x+(1/2-outerDiagonal)*(-Real.sin x))) x :=
    (((hasDerivAt_id x).neg.add_const (c r)).add_const
      ((q r-p r)*outerDiagonal)).add
        (((((Real.hasDerivAt_sin x).const_mul (1/2+outerDiagonal)).const_add (1/2)).add
          ((Real.hasDerivAt_cos x).const_mul (1/2-outerDiagonal))).const_mul (g r))
  exact hh.congr_deriv (by dsimp [Gd]; ring)

lemma diagonal_projection_upper (x : ℝ) :
    (1/2+outerDiagonal)*Real.cos x+(outerDiagonal-1/2)*Real.sin x<(73/50:ℝ) := by
  let v := (1/2+outerDiagonal)*Real.cos x+(outerDiagonal-1/2)*Real.sin x
  have he : v^2+((1/2+outerDiagonal)*Real.sin x-(outerDiagonal-1/2)*Real.cos x)^2=
      2*outerDiagonal^2+1/2 := by
    dsimp [v]
    linear_combination (2*outerDiagonal^2+1/2)*(Real.sin_sq_add_cos_sq x)
  have hd := outer_endpoint_bounds
  change v<(73/50:ℝ)
  nlinarith [hd.2.2.1,hd.2.2.2,
    sq_nonneg ((1/2+outerDiagonal)*Real.sin x-(outerDiagonal-1/2)*Real.cos x)]

lemma Gd_small_neg (r : Row) (hr : r=0 ∨ r=3) (x : ℝ) : Gd r x<0 := by
  have hh := mul_lt_mul_of_pos_left (diagonal_projection_upper x) (coefficient_bounds r).1
  rcases hr with rfl | rfl <;> norm_num [Gd,g] at hh ⊢ <;> linarith

lemma Gd_large_pos (r : Row) (h0 : r≠0) (h3 : r≠3)
    {x : ℝ} (hx : x∈Icc 0 cap) : 0<Gd r x := by
  have ht := trig_bounds hx
  have hd := fine_diagonal_bounds
  have hc := mul_le_mul_of_nonneg_left ht.2.2.1.le
    (show 0≤1/2+outerDiagonal by linarith [hd.1])
  have hs := mul_nonneg (show 0≤outerDiagonal-1/2 by linarith [hd.1]) ht.1
  have hv : (1:ℝ)<(1/2+outerDiagonal)*Real.cos x+(outerDiagonal-1/2)*Real.sin x := by
    nlinarith [hd.1]
  have hg : (1:ℝ)<g r := by
    fin_cases r
    · exact absurd rfl h0
    · norm_num [g]
    · norm_num [g]
    · exact absurd rfl h3
    · norm_num [g]
    · norm_num [g]
  have hh := mul_lt_mul_of_pos_left hv (coefficient_bounds r).1
  dsimp [Gd]
  linarith

lemma G_initial (r : Row) : (449/500:ℝ)<G r 0 := by
  have hd := fine_diagonal_bounds
  fin_cases r <;> norm_num [G,c,p,q,g] <;> linarith [hd.1,hd.2]

lemma G_small_terminal (r : Row) (hr : r=0 ∨ r=3) : (449/500:ℝ)<G r cap := by
  have ht := cap_trig
  have hd := fine_diagonal_bounds
  have hs := mul_le_mul_of_nonneg_left ht.1.le
    (show 0≤1/2+outerDiagonal by linarith [hd.1])
  have hc := mul_le_mul_of_nonpos_left ht.2.2.2.le
    (show 1/2-outerDiagonal≤0 by linarith [hd.1])
  have hcap : cap=8/25 := rfl
  rcases hr with rfl | rfl <;> norm_num [G,c,p,q,g] <;>
    linarith [hd.1,hd.2]

theorem G_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 cap) : (449/500:ℝ)<G r x := by
  by_cases hr : r=0 ∨ r=3
  · have hm : AntitoneOn (G r) (Icc 0 cap) :=
      antiOn_of_hasDeriv_nonpos (fun z _ => (G_hasDerivAt r z).continuousAt.continuousWithinAt)
        (fun z _ => G_hasDerivAt r z) (fun z _ => (Gd_small_neg r hr z).le)
    exact (G_small_terminal r hr).trans_le (hm hx (by norm_num [cap]) hx.2)
  · have hm : MonotoneOn (G r) (Icc 0 cap) :=
      monoOn_of_hasDeriv_nonneg (fun z _ => (G_hasDerivAt r z).continuousAt.continuousWithinAt)
        (fun z _ => G_hasDerivAt r z)
        (fun z hz => (Gd_large_pos r (fun h => hr (Or.inl h))
          (fun h => hr (Or.inr h)) (Ioo_subset_Icc_self hz)).le)
    exact (G_initial r).trans_le (hm (by norm_num [cap]) hx hx.1)

end SquaresInCircles.Eight.ShortMixedZero.CoreContact
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero

namespace CoreContact

open CommonQuarter CorePairGeometry Arithmetic

def coeffX (r : Row) (x : ℝ) : ℝ := g r*Real.sin x-p r
def coeffY (r : Row) (x : ℝ) : ℝ := q r-g r*Real.cos x
def base (r : Row) (x : ℝ) : ℝ := -x+c r+g r*(1+Real.sin x+Real.cos x)/2

lemma contact_value (r : Row) (x : ℝ) :
    H r x=base r x+coeffX r x*(U x-1/2)+coeffY r x*(V x-1/2) := by
  have hh := congrArg (fun z : ℝ => g r*z) (contact_equation x)
  dsimp [H,base,coeffX,coeffY]
  nlinarith only [hh]

lemma diagonal_value (r : Row) (x : ℝ) :
    G r x=base r x+(coeffX r x+coeffY r x)*outerDiagonal := by
  dsimp [G,base,coeffX,coeffY]
  ring

lemma outer_subarc_lower {a b A B X Y m : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hb : b≤B)
    (hX : 0≤X) (hl : m≤X*a+Y*b) (hu : m≤(X+Y)*outerDiagonal) :
    m≤X*A+Y*B := by
  have hB := (outer_bounds ht).2.2.2.1
  have hh := Arithmetic.circle_endpoints_lower (v := -1/2) (ρ := CommonQuarter.radius)
    (X := X) (Y := Y) (l := b) (u := outerDiagonal) hX
    (fun z hz => outer_radicand_pos ⟨hs.1.trans hz.1,hz.2⟩) ⟨hb,hB⟩
    (by simpa [← outer_branch hs] using hl)
    (by rw [outer_branch_endpoints.2]; linarith)
  simpa [← outer_branch ht] using hh

lemma outer_primary_order {a b A B : ℝ} (hs : OuterState a b)
    (ht : OuterState A B) (hb : b≤B) : A≤a := by
  have hsq := pow_le_pow_left₀ (show 0≤b+1/2 by linarith [hs.1])
    (show b+1/2≤B+1/2 by linarith) 2
  by_contra! hbad
  have hp := mul_pos (show 0<(A+1/2)-(a+1/2) by linarith)
    (show 0<(A+1/2)+(a+1/2) by linarith [hs.1,hs.2.1,ht.1,ht.2.1])
  nlinarith [hs.2.2,ht.2.2]

lemma contact_or_diagonal (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 cap)
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    min (H r x) (G r x)≤base r x+coeffX r x*A+coeffY r x*B := by
  obtain ⟨hc,hB⟩ := original_contact hs ht hx hm
  have hHv := (min_le_left (H r x) (G r x)).trans_eq (contact_value r x)
  have hGv := (min_le_right (H r x) (G r x)).trans_eq (diagonal_value r x)
  by_cases hX : 0≤coeffX r x
  · have hh := outer_subarc_lower hc ht hB hX
      (m := min (H r x) (G r x)-base r x) (Y := coeffY r x)
      (by linarith) (by linarith)
    linarith
  · have hX' : coeffX r x≤0 := (lt_of_not_ge hX).le
    have htr := trig_bounds hx
    have hr : r=3 ∨ r=5 := by
      fin_cases r <;> norm_num [coeffX,p,g] at hX ⊢ <;> nlinarith [htr.1]
    rcases hr with rfl | rfl
    · have hA := outer_primary_order hc ht hB
      have hY : 0≤coeffY 3 x := by
        norm_num [coeffY,q,g]
        linarith [htr.2.2.2]
      have h₁ := mul_le_mul_of_nonpos_left hA hX'
      have h₂ := mul_le_mul_of_nonneg_left hB hY
      linarith
    · have hsum := (positive_trig
        (show x∈Icc 0 (7/10) from ⟨hx.1,hx.2.trans (by norm_num [cap])⟩)).2.2.2.2.2
      have hder : coeffY 5 x-coeffX 5 x≤0 := by
        norm_num [coeffX,coeffY,p,q,g]
        linarith
      have hh := WrongWordCircleSupport.outer_diagonal_lower ht hX' hder
      linarith

theorem original_cost_lower (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 cap)
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    min (H r x) (G r x)≤-x+c r+g r*b-p r*A+q r*B := by
  have hh := contact_or_diagonal r hs ht hx hm
  have hp := mul_le_mul_of_nonneg_left hm (coefficient_bounds r).1.le
  dsimp [base,coeffX,coeffY] at hh
  nlinarith only [hh,hp]

end CoreContact

open CommonQuarter CorePairGeometry

/-- All six complementary opposite-sign families over their whole negative angle half,
including the original weak contact endpoints. -/
theorem opposite_core_negative (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    (449/500:ℝ)< -x+c r+g r*b-p r*A+q r*B := by
  have hx' : x∈Icc 0 CoreContact.cap := ⟨hx.1,(CoreContact.original_angle_cut hs ht hx hm).le⟩
  exact (lt_min (CoreContact.H_lower r hx') (CoreContact.G_lower r hx')).trans_le
    (CoreContact.original_cost_lower r hs ht hx' hm)

end SquaresInCircles.Eight.ShortMixedZero
end
end
end
