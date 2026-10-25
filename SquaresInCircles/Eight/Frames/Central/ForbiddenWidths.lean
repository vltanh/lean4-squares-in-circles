module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Real.Pi.Bounds
public import SquaresInCircles.Common.Charts
public import SquaresInCircles.Common.Trigonometry

/-!
# Eight squares: continuous forbidden widths: no rectangle rows

The partitions are intrinsic branch changes of the exact geometric endpoint.
One monotone polynomial controls the unique middle-branch minimum. There is
no rational subdivision, list of test rectangles, or table of witnesses.
-/

section
/-!
## A connected interval of forbidden segment directions

This is the geometric part of the central-core argument.
The rectangle argument is independent of any numerical partition. The four
branches of its endpoint function correspond to the corner reaching the
circle, the horizontal side reaching L, and the vertical side reaching r.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CentralForbidden

def L : ℝ := 11/12
def c : ℝ := 7/20
def radiusSq : ℝ := 1733/1800
def r : ℝ := Real.sqrt radiusSq
def φ : ℝ := Real.arctan (c/L)

theorem L_pos : 0<L := by norm_num [L]
theorem c_pos : 0<c := by norm_num [c]
theorem r_pos : 0<r := Real.sqrt_pos.mpr (by norm_num [radiusSq])
theorem r_sq : r^2=L^2+c^2 := by
  rw [r,Real.sq_sqrt (by norm_num [radiusSq])]
  norm_num [radiusSq,L,c]
theorem r_bounds : L<r ∧ r<1 := by
  have hr := r_sq
  have hp := r_pos
  dsimp [L,c] at hr ⊢
  constructor <;> nlinarith

theorem atan_cubic_lower {x : ℝ} (hx : 0≤x) : x-x^3/3≤Real.arctan x := by
  have hh := nonneg_of_deriv_nonneg
    (fun t => Real.arctan t-t+t^3/3)
    ((Real.differentiable_arctan.sub differentiable_id).add (by fun_prop)) (by norm_num)
    (fun t ht => by
      have hd : 0<1+t^2 := by positivity
      have h := ((Real.hasDerivAt_arctan t).sub (hasDerivAt_id t)).add
        ((hasDerivAt_pow 3 t).div_const 3)
      have hderiv : HasDerivAt (fun t => Real.arctan t-t+t^3/3) (t^4/(1+t^2)) t := by
        convert h using 1
        · funext s
          simp only [Pi.add_apply,Pi.sub_apply,id]
        · have hc : ((3:ℕ):ℝ)*t^(3-1)/3=t^2 := by norm_num
          rw [hc]
          field_simp
          ring
      rw [hderiv.deriv]
      positivity) hx
  linarith

theorem atan_upper {x : ℝ} (hx : 0≤x) : Real.arctan x≤x := by
  have hh := nonneg_of_deriv_nonneg
    (fun t => t-Real.arctan t)
    (differentiable_id.sub Real.differentiable_arctan) (by norm_num)
    (fun t ht => by
      have hderiv : HasDerivAt (fun t => t-Real.arctan t) (1-1/(1+t^2)) t :=
        (hasDerivAt_id t).sub (Real.hasDerivAt_arctan t)
      rw [hderiv.deriv]
      have hd : 0<1+t^2 := by positivity
      have hle : 1/(1+t^2)≤1 := (div_le_one hd).mpr (by nlinarith)
      linarith) hx
  linarith

theorem φ_bounds : 9/25<φ ∧ φ<2/5 ∧ 0≤φ ∧ φ<Real.pi/2 := by
  have hl := atan_cubic_lower (show 0≤c/L by norm_num [c,L])
  have hu := atan_upper (show 0≤c/L by norm_num [c,L])
  have hθ := Real.arctan_lt_pi_div_two (c/L)
  dsimp [φ,c,L] at *
  constructor
  · norm_num at hl
    linarith
  constructor
  · norm_num at hu
    linarith
  exact ⟨by linarith,hθ⟩

theorem φ_trig : r*Real.cos φ=L ∧ r*Real.sin φ=c := by
  have hunit := Real.sin_sq_add_cos_sq φ
  have hcos : 0<Real.cos φ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [φ_bounds.2.2.1,Real.pi_pos],φ_bounds.2.2.2⟩
  have htan : Real.sin φ/Real.cos φ=c/L := by
    rw [← Real.tan_eq_sin_div_cos]
    exact Real.tan_arctan _
  have hrelation : L*Real.sin φ=c*Real.cos φ := by
    have h := (div_eq_div_iff (ne_of_gt hcos) (ne_of_gt L_pos)).mp htan
    linarith
  have hr := r_sq
  have hp := r_pos
  have hcroot : r*Real.cos φ=L := by
    have hsq : (r*Real.cos φ)^2=L^2 := by
      linear_combination Real.cos φ^2*hr-(L*Real.sin φ+c*Real.cos φ)*hrelation+L^2*hunit
    exact (sq_eq_sq₀ (mul_pos hp hcos).le L_pos.le).mp hsq
  have hsc : r*Real.sin φ=c := by
    have hid : L*(r*Real.sin φ)=L*c := by
      linear_combination r*hrelation+c*hcroot
    exact mul_left_cancel₀ L_pos.ne' hid
  exact ⟨hcroot,hsc⟩

theorem arccos_L_div_r : Real.arccos (L/r)=φ := by
  have he : L/r=Real.cos φ := (div_eq_iff (ne_of_gt r_pos)).mpr (by linarith [φ_trig.1])
  rw [he,Real.arccos_cos φ_bounds.2.2.1 (by linarith [φ_bounds.2.2.2,Real.pi_pos])]

def Rectangle (A d : ℝ) (p : Point) : Prop :=
  0≤p.1 ∧ p.1≤A ∧ 0≤p.2 ∧ p.2≤d

/-- Radial contraction joins the whole axial arc to the support interval
of one rectangle point. The conclusion includes every intermediate angle. -/
theorem rectangle_segment_interval {A d x y γ : ℝ}
    (hA : L≤A) (hp : Rectangle A d (x,y))
    (hrad : x^2+y^2≤radiusSq) (hγ : 0≤γ ∧ γ≤2)
    (hsupport : L≤x*Real.cos γ+y*Real.sin γ) :
    ∀ β, 0≤β ∧ β≤γ → ∃ v, |v|≤c ∧
      Rectangle A d (pointInDirection (0,0) (β : Direction) L v) := by
  obtain ⟨hx0,hxA,hy0,hyd⟩ := hp
  have hρ₂ : Real.sqrt (x^2+y^2)^2=x^2+y^2 := Real.sq_sqrt (by positivity)
  have hρ₀ : 0≤Real.sqrt (x^2+y^2) := Real.sqrt_nonneg _
  generalize Real.sqrt (x^2+y^2)=ρ at hρ₂ hρ₀
  have hunitγ := Real.sin_sq_add_cos_sq γ
  have hcauchy := cauchy_sq (x,y) (Real.cos γ,Real.sin γ)
  dsimp [dot,normSq] at hcauchy
  have hρL : L≤ρ := by
    rw [show Real.cos γ^2+Real.sin γ^2=1 by linarith,mul_one] at hcauchy
    have hL2 : L^2≤ρ^2 := by
      linarith [mul_le_mul hsupport hsupport L_pos.le (L_pos.le.trans hsupport)]
    exact (abs_le_of_sq_le_sq hL2 hρ₀).trans' (le_abs_self L)
  have hρ : 0<ρ := L_pos.trans_le hρL
  have hxr : -1≤x/ρ ∧ x/ρ≤1 := by
    constructor
    · apply (le_div_iff₀ hρ).mpr
      linarith
    · apply (div_le_iff₀ hρ).mpr
      have hx2 : x^2≤ρ^2 := by linarith [sq_nonneg y]
      linarith [(abs_le_of_sq_le_sq hx2 hρ₀).trans' (le_abs_self x)]
  have hθ₀ : 0≤Real.arccos (x/ρ) := Real.arccos_nonneg _
  have hθ₁ : Real.arccos (x/ρ)≤Real.pi/2 := Real.arccos_le_pi_div_two.mpr (div_nonneg hx0 hρ.le)
  have hcosθ : ρ*Real.cos (Real.arccos (x/ρ))=x := by
    rw [Real.cos_arccos hxr.1 hxr.2]
    field_simp
  generalize Real.arccos (x/ρ)=θ at hθ₀ hθ₁ hcosθ
  have hsinθ : ρ*Real.sin θ=y := by
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hθ₀ (by linarith [Real.pi_pos])
    have hunit := Real.sin_sq_add_cos_sq θ
    have hsq : (ρ*Real.sin θ)^2=y^2 := by
      linear_combination ρ^2*hunit-(ρ*Real.cos θ+x)*hcosθ+hρ₂
    exact (sq_eq_sq₀ (mul_nonneg hρ₀ hs) hy0).mp hsq
  intro β hβ
  by_cases hβθ : β≤θ
  · refine ⟨0,by simpa using c_pos.le,?_⟩
    have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hβ.1,Real.pi_pos]) hθ₁ hβθ
    have hc := cos_sin_nonneg (x := β) ⟨hβ.1,hβθ.trans hθ₁⟩
    have hsin' := mul_le_mul_of_nonneg_left hsin L_pos.le
    have hρ' := mul_le_mul_of_nonneg_right hρL
      (Real.sin_nonneg_of_nonneg_of_le_pi hθ₀ (by linarith [Real.pi_pos]))
    have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one β) L_pos.le
    simp only [Rectangle,pointInDirection,Real.Angle.cos_coe,Real.Angle.sin_coe,
      mul_zero,sub_zero,zero_add,add_zero]
    exact ⟨mul_nonneg hc.1 L_pos.le,by linarith,
      mul_nonneg hc.2 L_pos.le,by linarith⟩
  · replace hβθ := lt_of_not_ge hβθ
    have hid (t : ℝ) : ρ*Real.cos (t-θ)=x*Real.cos t+y*Real.sin t := by
      rw [Real.cos_sub]
      linear_combination Real.cos t*hcosθ+Real.sin t*hsinθ
    have hproj : L≤x*Real.cos β+y*Real.sin β := by
      have hmono := Real.cos_le_cos_of_nonneg_of_le_pi
        (show 0≤β-θ by linarith)
        (show γ-θ≤Real.pi by linarith [hγ.2,hθ₀,Real.pi_gt_three])
        (show β-θ≤γ-θ by linarith [hβ.2])
      have hm := mul_le_mul_of_nonneg_left hmono hρ.le
      rw [hid γ,hid β] at hm
      exact hsupport.trans hm
    obtain ⟨D,hDdef⟩ : ∃ D, D=x*Real.cos β+y*Real.sin β := ⟨_,rfl⟩
    rw [← hDdef] at hproj
    have hD : 0<D := by linarith [L_pos]
    obtain ⟨t,htdef⟩ : ∃ t, t=L/D := ⟨_,rfl⟩
    have ht0 : 0<t := by rw [htdef]; exact div_pos L_pos hD
    have ht1 : t≤1 := by rw [htdef]; exact (div_le_one hD).mpr hproj
    have htD : t*D=L := by rw [htdef]; exact div_mul_cancel₀ L hD.ne'
    have hdot : (t*x)*Real.cos β+(t*y)*Real.sin β=L := by
      linear_combination htD-t*hDdef
    obtain ⟨v,hvdef⟩ : ∃ v, v=-Real.sin β*(t*x)+Real.cos β*(t*y) := ⟨_,rfl⟩
    have hu := Real.sin_sq_add_cos_sq β
    have hpoint : pointInDirection (0,0) (β : Direction) L v=(t*x,t*y) := by
      simp only [pointInDirection,Real.Angle.cos_coe,Real.Angle.sin_coe,Prod.mk.injEq]
      constructor
      · linear_combination (-Real.sin β)*hvdef-Real.cos β*hdot+t*x*hu
      · linear_combination Real.cos β*hvdef-Real.sin β*hdot+t*y*hu
    have hnorm : (t*x)^2+(t*y)^2≤radiusSq := by
      have htu : t^2≤1 := pow_le_one₀ ht0.le ht1
      have hh := mul_le_mul_of_nonneg_right htu (show 0≤x^2+y^2 by positivity)
      have he : (t*x)^2+(t*y)^2=t^2*(x^2+y^2) := by ring
      linarith
    have hv₂ : v^2≤c^2 := by
      have hn := pointInDirection_norm (0,0) (β : Direction) L v
      rw [hpoint] at hn
      simp only [normSq,sub,sub_zero] at hn
      have hr : radiusSq=L^2+c^2 := by norm_num [radiusSq,L,c]
      linarith
    refine ⟨v,abs_le_of_sq_le_sq hv₂ c_pos.le,?_⟩
    rw [hpoint]
    have hx' := mul_le_mul_of_nonneg_right ht1 hx0
    have hy' := mul_le_mul_of_nonneg_right ht1 hy0
    exact ⟨mul_nonneg ht0.le hx0,by linarith,mul_nonneg ht0.le hy0,by linarith⟩

def k (A : ℝ) : ℝ := Real.sqrt (radiusSq-A^2)
def sideAngle (A y : ℝ) : ℝ :=
  Real.arctan (y/A)+Real.arccos (L/Real.sqrt (A^2+y^2))
def E (y : ℝ) : ℝ := Real.arcsin (y/r)+φ
def verticalAngle (y : ℝ) : ℝ := Real.pi/2+Real.arccos (L/y)

def F (A y : ℝ) : ℝ :=
  if y≤k A then sideAngle A y
  else if y≤L then E y
  else if y≤r then verticalAngle y
  else Real.pi/2+φ

/-- The coordinates of a first-quadrant angle, proved without tangent
branch assumptions hidden in a normalization tactic. -/
theorem atan_frame {A y : ℝ} (hA : 0<A) (hy : 0≤y) :
    let ρ := Real.sqrt (A^2+y^2)
    ρ*Real.cos (Real.arctan (y/A))=A ∧
      ρ*Real.sin (Real.arctan (y/A))=y := by
  dsimp only
  have hρ : 0<Real.sqrt (A^2+y^2) := Real.sqrt_pos.mpr (by positivity)
  have hρ₂ : Real.sqrt (A^2+y^2)^2=A^2+y^2 := Real.sq_sqrt (by positivity)
  generalize Real.sqrt (A^2+y^2)=ρ at hρ hρ₂ ⊢
  have hθ : 0≤Real.arctan (y/A) ∧ Real.arctan (y/A)<Real.pi/2 :=
    ⟨Real.arctan_nonneg.mpr (div_nonneg hy hA.le),Real.arctan_lt_pi_div_two _⟩
  have htan : Real.sin (Real.arctan (y/A))/Real.cos (Real.arctan (y/A))=y/A := by
    rw [← Real.tan_eq_sin_div_cos]
    exact Real.tan_arctan _
  generalize Real.arctan (y/A)=θ at hθ htan ⊢
  have hc : 0<Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩
  have hs : 0≤Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
    (by linarith [hθ.2,Real.pi_pos])
  have hcross := (div_eq_div_iff hc.ne' hA.ne').mp htan
  have hunit := Real.sin_sq_add_cos_sq θ
  have hcos : ρ*Real.cos θ=A := by
    have hsq : (ρ*Real.cos θ)^2=A^2 := by
      linear_combination Real.cos θ^2*hρ₂-(Real.sin θ*A+y*Real.cos θ)*hcross+A^2*hunit
    exact (sq_eq_sq₀ (mul_pos hρ hc).le hA.le).mp hsq
  have hsin : ρ*Real.sin θ=y := by
    have hid : A*(ρ*Real.sin θ)=A*y := by
      linear_combination ρ*hcross+y*hcos
    exact mul_left_cancel₀ hA.ne' hid
  exact ⟨hcos,hsin⟩

theorem sideAngle_support {A y : ℝ} (hA : L≤A) (hy : 0≤y)
    (hrad : A^2+y^2≤radiusSq) :
    0≤sideAngle A y ∧ sideAngle A y≤2 ∧
      A*Real.cos (sideAngle A y)+y*Real.sin (sideAngle A y)=L := by
  have hA0 : 0<A := L_pos.trans_le hA
  obtain ⟨hc,hs⟩ := atan_frame hA0 hy
  have hρ0 : 0<Real.sqrt (A^2+y^2) := Real.sqrt_pos.mpr (by positivity)
  have hρ₂ : Real.sqrt (A^2+y^2)^2=A^2+y^2 := Real.sq_sqrt (by positivity)
  have hρr : Real.sqrt (A^2+y^2)≤r := Real.sqrt_le_sqrt hrad
  have hθ : 0≤Real.arctan (y/A) ∧ Real.arctan (y/A)<Real.pi/2 :=
    ⟨Real.arctan_nonneg.mpr (div_nonneg hy hA0.le),Real.arctan_lt_pi_div_two _⟩
  unfold sideAngle
  generalize Real.sqrt (A^2+y^2)=ρ at hc hs hρ0 hρ₂ hρr ⊢
  generalize Real.arctan (y/A)=θ at hc hs hθ ⊢
  have hρL : L≤ρ := by nlinarith [L_pos]
  have hz : -1≤L/ρ ∧ L/ρ≤1 :=
    ⟨by have := div_nonneg L_pos.le hρ0.le; linarith,(div_le_one hρ0).mpr hρL⟩
  have hψ : 0≤Real.arccos (L/ρ) := Real.arccos_nonneg _
  have hψφ : Real.arccos (L/ρ)≤φ := by
    rw [← arccos_L_div_r]
    apply Real.arccos_le_arccos
    exact div_le_div_of_nonneg_left L_pos.le hρ0 hρr
  have hcosψ : Real.cos (Real.arccos (L/ρ))=L/ρ := Real.cos_arccos hz.1 hz.2
  generalize Real.arccos (L/ρ)=ψ at hψ hψφ hcosψ ⊢
  have hprod : ρ*Real.cos ψ=L := by rw [hcosψ]; field_simp
  refine ⟨add_nonneg hθ.1 hψ,?_,?_⟩
  · linarith [Real.pi_lt_d2,φ_bounds.2.1]
  · rw [Real.cos_add,Real.sin_add]
    have hu := Real.sin_sq_add_cos_sq θ
    linear_combination (-(Real.cos θ*Real.cos ψ-Real.sin θ*Real.sin ψ))*hc-
      (Real.sin θ*Real.cos ψ+Real.cos θ*Real.sin ψ)*hs+ρ*Real.cos ψ*hu+hprod

theorem E_support {y : ℝ} (hy : 0≤y) (hyr : y≤r) :
    let x := Real.sqrt (radiusSq-y^2)
    0≤E y ∧ E y≤2 ∧ x*Real.cos (E y)+y*Real.sin (E y)=L := by
  intro x
  have hr₂ : r^2=radiusSq := Real.sq_sqrt (by norm_num [radiusSq])
  have hrad : 0≤radiusSq-y^2 := by nlinarith [r_pos]
  have hx₂ : x^2=radiusSq-y^2 := Real.sq_sqrt hrad
  have hx0 : 0≤x := Real.sqrt_nonneg _
  have hydiv : -1≤y/r ∧ y/r≤1 :=
    ⟨by have := div_nonneg hy r_pos.le; linarith,(div_le_one r_pos).mpr hyr⟩
  have hθ : 0≤Real.arcsin (y/r) ∧ Real.arcsin (y/r)≤Real.pi/2 :=
    ⟨Real.arcsin_nonneg.mpr (div_nonneg hy r_pos.le),Real.arcsin_le_pi_div_two _⟩
  have hsθ : r*Real.sin (Real.arcsin (y/r))=y := by
    rw [Real.sin_arcsin hydiv.1 hydiv.2]
    field_simp [ne_of_gt r_pos]
  unfold E
  generalize Real.arcsin (y/r)=θ at hθ hsθ ⊢
  have hunit := Real.sin_sq_add_cos_sq θ
  have hcθ : r*Real.cos θ=x := by
    have hc : 0≤Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hθ.2⟩
    have hsq : (r*Real.cos θ)^2=x^2 := by
      linear_combination r^2*hunit-(r*Real.sin θ+y)*hsθ+hr₂-hx₂
    exact (sq_eq_sq₀ (mul_nonneg r_pos.le hc) hx0).mp hsq
  refine ⟨add_nonneg hθ.1 φ_bounds.2.2.1,?_,?_⟩
  · linarith [φ_bounds.2.1,Real.pi_lt_d2]
  · rw [Real.cos_add,Real.sin_add]
    linear_combination (-(Real.cos θ*Real.cos φ-Real.sin θ*Real.sin φ))*hcθ-
      (Real.sin θ*Real.cos φ+Real.cos θ*Real.sin φ)*hsθ+r*Real.cos φ*hunit+φ_trig.1

theorem vertical_support {y : ℝ} (hyL : L≤y) (hyr : y≤r) :
    0≤verticalAngle y ∧ verticalAngle y≤2 ∧ y*Real.sin (verticalAngle y)=L := by
  have hy0 : 0<y := L_pos.trans_le hyL
  have hz : -1≤L/y ∧ L/y≤1 :=
    ⟨by have := div_nonneg L_pos.le hy0.le; linarith,(div_le_one hy0).mpr hyL⟩
  have hp : Real.arccos (L/y)≤φ := by
    rw [← arccos_L_div_r]
    apply Real.arccos_le_arccos
    exact div_le_div_of_nonneg_left L_pos.le hy0 hyr
  refine ⟨add_nonneg (by linarith [Real.pi_pos]) (Real.arccos_nonneg _),?_,?_⟩
  · unfold verticalAngle
    linarith [Real.pi_lt_d2,φ_bounds.2.1]
  · simp only [verticalAngle,Real.sin_add,Real.sin_pi_div_two,Real.cos_pi_div_two,
      one_mul,zero_mul,add_zero,Real.cos_arccos hz.1 hz.2]
    field_simp

theorem F_nonneg_le_two {A y : ℝ} (hA : L≤A) (hAr : A<r) (hy : 0≤y) :
    0≤F A y ∧ F A y≤2 := by
  have hA0 := L_pos.trans_le hA
  have hr₂ : r^2=radiusSq := Real.sq_sqrt (by norm_num [radiusSq])
  have hrad : 0≤radiusSq-A^2 := by nlinarith [r_pos]
  have hk₂ : k A^2=radiusSq-A^2 := Real.sq_sqrt hrad
  have hk0 : 0≤k A := Real.sqrt_nonneg _
  unfold F
  split_ifs with h₁ h₂ h₃
  · have hs := sideAngle_support hA hy (by nlinarith [mul_le_mul h₁ h₁ hy hk0])
    exact ⟨hs.1,hs.2.1⟩
  · have hs := E_support hy (h₂.trans r_bounds.1.le)
    exact ⟨hs.1,hs.2.1⟩
  · have hs := vertical_support (le_of_not_ge h₂) h₃
    exact ⟨hs.1,hs.2.1⟩
  · constructor
    · linarith [φ_bounds.2.2.1,Real.pi_pos]
    · linarith [Real.pi_lt_d2,φ_bounds.2.1]

/-- The complete interval of directions has an actual rectangle intersection. -/
theorem F_forbidden {A y : ℝ} (hA : L≤A) (hAr : A<r) (hy : 0≤y) :
    ∀ β, 0≤β ∧ β≤F A y → ∃ v, |v|≤c ∧
      Rectangle A y (pointInDirection (0,0) (β : Direction) L v) := by
  have hA0 := L_pos.trans_le hA
  have hr₂ : r^2=radiusSq := Real.sq_sqrt (by norm_num [radiusSq])
  have hrad : 0≤radiusSq-A^2 := by nlinarith [r_pos]
  have hk₂ : k A^2=radiusSq-A^2 := Real.sq_sqrt hrad
  have hk0 : 0≤k A := Real.sqrt_nonneg _
  by_cases h₁ : y≤k A
  · have hcircle : A^2+y^2≤radiusSq := by nlinarith [mul_le_mul h₁ h₁ hy hk0]
    have hs := sideAngle_support hA hy hcircle
    have hF : F A y=sideAngle A y := by unfold F; rw [ite_eq_left h₁]
    rw [hF]
    exact rectangle_segment_interval hA
      (show Rectangle A y (A,y) from ⟨hA0.le,le_rfl,hy,le_rfl⟩)
      hcircle ⟨hs.1,hs.2.1⟩ hs.2.2.ge
  by_cases h₂ : y≤L
  · have hyr : y≤r := h₂.trans r_bounds.1.le
    have hrad' : 0≤radiusSq-y^2 := by nlinarith [r_pos]
    have hx₂ : Real.sqrt (radiusSq-y^2)^2=radiusSq-y^2 := Real.sq_sqrt hrad'
    have hx0 : 0≤Real.sqrt (radiusSq-y^2) := Real.sqrt_nonneg _
    have hxA : Real.sqrt (radiusSq-y^2)≤A := by
      have hky : k A^2≤y^2 := pow_le_pow_left₀ hk0 (lt_of_not_ge h₁).le 2
      calc Real.sqrt (radiusSq-y^2)≤Real.sqrt (A^2) := Real.sqrt_le_sqrt (by linarith)
        _=A := Real.sqrt_sq hA0.le
    have hs := E_support hy hyr
    have hF : F A y=E y := by unfold F; rw [ite_eq_right h₁,ite_eq_left h₂]
    rw [hF]
    exact rectangle_segment_interval hA
      (show Rectangle A y (Real.sqrt (radiusSq-y^2),y) from ⟨hx0,hxA,hy,le_rfl⟩)
      (by linarith) ⟨hs.1,hs.2.1⟩ hs.2.2.ge
  by_cases h₃ : y≤r
  · have hs := vertical_support (le_of_not_ge h₂) h₃
    have hF : F A y=verticalAngle y := by unfold F; rw [ite_eq_right h₁,ite_eq_right h₂,ite_eq_left h₃]
    rw [hF]
    exact rectangle_segment_interval hA
      (show Rectangle A y (0,y) from ⟨le_rfl,hA0.le,hy,le_rfl⟩)
      (show (0 : ℝ)^2+y^2≤radiusSq by nlinarith [pow_le_pow_left₀ hy h₃ 2])
      ⟨hs.1,hs.2.1⟩ (by rw [zero_mul,zero_add]; exact hs.2.2.ge)
  · have hs := vertical_support r_bounds.1.le le_rfl
    have hangle : verticalAngle r=Real.pi/2+φ := by rw [verticalAngle,arccos_L_div_r]
    rw [hangle] at hs
    have hF : F A y=Real.pi/2+φ := by unfold F; rw [ite_eq_right h₁,ite_eq_right h₂,ite_eq_right h₃]
    rw [hF]
    exact rectangle_segment_interval hA
      (show Rectangle A y (0,r) from ⟨le_rfl,hA0.le,r_pos.le,(lt_of_not_ge h₃).le⟩)
      (show (0 : ℝ)^2+r^2≤radiusSq by linarith)
      ⟨hs.1,hs.2.1⟩ (by rw [zero_mul,zero_add]; exact hs.2.2.ge)

/-- Reflection attaches the lower interval to the upper interval at zero. -/
theorem centered_rectangle_forbidden {A d W : ℝ}
    (hA : L≤A) (hAr : A<r) (hd : 0≤d ∧ d≤1/2)
    (hwidth : W<F A d+F A (1-d)) :
    ∃ l u : ℝ, l≤0 ∧ 0≤u ∧ W<u-l ∧ u-l≤4 ∧
      ∀ β, l≤β ∧ β≤u → ∃ v, |v|≤c ∧
        let p := pointInDirection (0,0) (β : Direction) L v
        0≤p.1 ∧ p.1≤A ∧ -d≤p.2 ∧ p.2≤1-d := by
  have hd' : 0≤1-d := by linarith
  have hF₁ := F_nonneg_le_two hA hAr hd.1
  have hF₂ := F_nonneg_le_two hA hAr hd'
  refine ⟨-F A d,F A (1-d),by linarith,hF₂.1,by linarith,by linarith,?_⟩
  intro β hβ
  by_cases hβ0 : 0≤β
  · obtain ⟨v,hv,hp⟩ := F_forbidden hA hAr hd' β ⟨hβ0,hβ.2⟩
    obtain ⟨h1,h2,h3,h4⟩ := hp
    exact ⟨v,hv,h1,h2,by linarith,h4⟩
  · obtain ⟨v,hv,hp⟩ := F_forbidden hA hAr hd.1 (-β) ⟨by linarith,by linarith [hβ.1]⟩
    obtain ⟨h1,h2,h3,h4⟩ := hp
    refine ⟨-v,by rwa [abs_neg],?_⟩
    simp only [pointInDirection,Real.Angle.cos_coe,Real.Angle.sin_coe,Real.cos_neg,
      Real.sin_neg] at h1 h2 h3 h4 ⊢
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

end SquaresInCircles.Eight.CentralForbidden
end
end
end

section
/-!
## The four exact branches of the forbidden-direction endpoint

Only the geometric transition points k(A), L and r occur.
The derivative formulas, continuity at those points and monotonicity below
are used on whole intervals, never on a dyadic or sampled cover.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CentralForbidden

theorem r_sq_radiusSq : r^2=radiusSq := Real.sq_sqrt (by norm_num [radiusSq])

theorem k_spec {A : ℝ} (hA : L≤A) (hAr : A<r) :
    0<k A ∧ k A^2=radiusSq-A^2 ∧ k A≤c ∧ k A<L := by
  have hA0 := L_pos.trans_le hA
  have hrad : 0<radiusSq-A^2 := by nlinarith [r_sq_radiusSq,r_pos]
  have hk0 : 0<k A := Real.sqrt_pos.mpr hrad
  have hk2 : k A^2=radiusSq-A^2 := Real.sq_sqrt hrad.le
  have hkc : k A≤c := by
    have hle : radiusSq-A^2≤c^2 := by
      linarith [r_sq,r_sq_radiusSq,mul_le_mul hA hA L_pos.le hA0.le]
    calc k A≤Real.sqrt (c^2) := Real.sqrt_le_sqrt hle
      _=c := Real.sqrt_sq c_pos.le
  exact ⟨hk0,hk2,hkc,hkc.trans_lt (by norm_num [L,c])⟩

@[simp] theorem k_L : k L=c := by
  have hc := c_pos
  have hid : radiusSq-L^2=c^2 := by norm_num [radiusSq,L,c]
  rw [k,hid,Real.sqrt_sq hc.le]

theorem sideAngle_mono {A : ℝ} (hA : L≤A) :
    MonotoneOn (sideAngle A) (Ici 0) := by
  intro x hx y hy hxy
  have hA0 := L_pos.trans_le hA
  have hnx : 0<Real.sqrt (A^2+x^2) := Real.sqrt_pos.mpr (by positivity)
  have hroots : Real.sqrt (A^2+x^2)≤Real.sqrt (A^2+y^2) := by
    apply Real.sqrt_le_sqrt
    have hsq := pow_le_pow_left₀ (show (0:ℝ)≤x from hx) hxy 2
    linarith
  have hatan := Real.arctan_mono (div_le_div_of_nonneg_right hxy hA0.le)
  have harccos := Real.arccos_le_arccos
    (div_le_div_of_nonneg_left L_pos.le hnx hroots)
  exact add_le_add hatan harccos

theorem E_mono : Monotone E := by
  intro x y hxy
  exact add_le_add (Real.arcsin_le_arcsin (div_le_div_of_nonneg_right hxy r_pos.le)) le_rfl

theorem sideAngle_k {A : ℝ} (hA : L≤A) (hAr : A<r) :
    sideAngle A (k A)=E (k A) := by
  have hk := k_spec hA hAr
  have hA0 := L_pos.trans_le hA
  have hnorm : Real.sqrt (A^2+k A^2)=r := by
    have hid : A^2+k A^2=radiusSq := by linarith [hk.2.1]
    rw [hid]
    rfl
  have ht := atan_frame hA0 hk.1.le
  rw [hnorm] at ht
  have hsin : Real.sin (Real.arctan (k A/A))=k A/r := by
    exact (eq_div_iff r_pos.ne').mpr (by nlinarith [ht.2])
  have hang : Real.arcsin (k A/r)=Real.arctan (k A/A) := by
    apply Real.arcsin_eq_of_sin_eq hsin
    constructor
    · have hn := Real.arctan_nonneg.mpr (div_nonneg hk.1.le hA0.le)
      linarith [Real.pi_pos]
    · exact (Real.arctan_lt_pi_div_two _).le
  rw [sideAngle,hnorm,arccos_L_div_r,E,hang]

theorem sideAngle_L (y : ℝ) (hy : 0≤y) :
    sideAngle L y=2*Real.arctan (y/L) := by
  have ht := atan_frame L_pos hy
  have hnorm : 0<Real.sqrt (L^2+y^2) := Real.sqrt_pos.mpr (by nlinarith [L_pos])
  have hcos : L/Real.sqrt (L^2+y^2)=Real.cos (Real.arctan (y/L)) := by
    apply (div_eq_iff hnorm.ne').mpr
    nlinarith [ht.1]
  have hθ0 := Real.arctan_nonneg.mpr (div_nonneg hy L_pos.le)
  have hθπ := Real.arctan_lt_pi_div_two (y/L)
  rw [sideAngle,hcos,Real.arccos_cos hθ0 (by linarith [Real.pi_pos])]
  ring

@[simp] theorem E_L : E L=Real.pi/2 := by
  have hsin : Real.sin (Real.pi/2-φ)=L/r := by
    rw [Real.sin_sub,Real.sin_pi_div_two,Real.cos_pi_div_two]
    simp only [one_mul,zero_mul,sub_zero]
    exact (eq_div_iff r_pos.ne').mpr (by nlinarith [φ_trig.1])
  have hang : Real.arcsin (L/r)=Real.pi/2-φ := by
    apply Real.arcsin_eq_of_sin_eq hsin
    constructor <;> linarith [φ_bounds.2.2.1,φ_bounds.2.2.2,Real.pi_pos]
  rw [E,hang]
  ring

@[simp] theorem verticalAngle_L : verticalAngle L=Real.pi/2 := by
  simp [verticalAngle,ne_of_gt L_pos]

@[simp] theorem verticalAngle_r : verticalAngle r=Real.pi/2+φ := by
  rw [verticalAngle,arccos_L_div_r]

theorem F_eq_side {A y : ℝ} (hy : y≤k A) : F A y=sideAngle A y := by
  simp [F,hy]

theorem F_eq_E {A y : ℝ} (hA : L≤A) (hAr : A<r)
    (hy : k A≤y) (hyL : y≤L) : F A y=E y := by
  by_cases he : y=k A
  · rw [he,F_eq_side le_rfl,sideAngle_k hA hAr]
  · have hstrict : ¬y≤k A := by intro hh; exact he (le_antisymm hh hy)
    simp [F,hstrict,hyL]

theorem F_eq_vertical {A y : ℝ} (hA : L≤A) (hAr : A<r)
    (hy : L≤y) (hyr : y≤r) : F A y=verticalAngle y := by
  have hk := (k_spec hA hAr).2.2.2
  by_cases he : y=L
  · rw [he,F_eq_E hA hAr hk.le le_rfl,E_L,verticalAngle_L]
  · have h₁ : ¬y≤k A := by linarith
    have h₂ : ¬y≤L := by intro hh; exact he (le_antisymm hh hy)
    simp [F,h₁,h₂,hyr]

theorem F_eq_constant {A y : ℝ} (hA : L≤A) (hAr : A<r)
    (hy : r≤y) : F A y=Real.pi/2+φ := by
  by_cases he : y=r
  · rw [he,F_eq_vertical hA hAr r_bounds.1.le le_rfl,verticalAngle_r]
  · have hk := (k_spec hA hAr).2.2.2
    simp [F,show ¬y≤k A by linarith [r_bounds.1],
      show ¬y≤L by linarith [r_bounds.1],show ¬y≤r by
        intro hh; exact he (le_antisymm hh hy)]

theorem F_ge_half_pi {A y : ℝ} (hA : L≤A) (hAr : A<r)
    (hy : L≤y) : Real.pi/2≤F A y := by
  by_cases hyr : y≤r
  · rw [F_eq_vertical hA hAr hy hyr,verticalAngle]
    linarith [Real.arccos_nonneg (L/y)]
  · rw [F_eq_constant hA hAr (le_of_not_ge hyr)]
    linarith [φ_bounds.2.2.1]

theorem F_ge_initial_side {A y : ℝ} (hA : L≤A) (hAr : A<r)
    (hy : 0≤y) : sideAngle A 0≤F A y := by
  have hk := k_spec hA hAr
  by_cases hyk : y≤k A
  · rw [F_eq_side hyk]
    exact sideAngle_mono hA (by simp) hy hy
  by_cases hyL : y≤L
  · rw [F_eq_E hA hAr (le_of_not_ge hyk) hyL]
    calc
      sideAngle A 0≤sideAngle A (k A) := sideAngle_mono hA
        (by simp) hk.1.le hk.1.le
      _=E (k A) := sideAngle_k hA hAr
      _≤E y := E_mono (le_of_not_ge hyk)
  · have hfirst : sideAngle A 0≤Real.pi/2 := by
      simp only [sideAngle,zero_div,Real.arctan_zero,zero_add]
      exact Real.arccos_le_pi_div_two.mpr (div_nonneg L_pos.le (Real.sqrt_nonneg _))
    exact hfirst.trans (F_ge_half_pi hA hAr (le_of_not_ge hyL))

/-- Inverse-sine differentiation with the positive circle branch explicit. -/
theorem E_hasDeriv {y : ℝ} (hy : |y|<r) :
    HasDerivAt E (1/Real.sqrt (radiusSq-y^2)) y := by
  have hrad : 0<radiusSq-y^2 := by
    nlinarith [r_sq_radiusSq,r_pos,abs_nonneg y,sq_abs y]
  have hdiv : |y/r|<1 := by
    rw [abs_div,abs_of_pos r_pos]
    exact (div_lt_one r_pos).mpr hy
  have hroot : Real.sqrt (1-(y/r)^2)=Real.sqrt (radiusSq-y^2)/r := by
    have hr0 := r_pos.ne'
    rw [show 1-(y/r)^2=(radiusSq-y^2)/r^2 by rw [div_pow,← r_sq_radiusSq]; field_simp,
      Real.sqrt_div hrad.le,Real.sqrt_sq r_pos.le]
  have hneq₁ : y/r≠-1 := by intro he; simp [he] at hdiv
  have hneq₂ : y/r≠1 := by intro he; simp [he] at hdiv
  have hh := ((Real.hasDerivAt_arcsin hneq₁ hneq₂).comp y
    ((hasDerivAt_id y).div_const r)).add_const φ
  convert hh using 1
  · rfl
  · rw [hroot]
    field_simp [r_pos.ne',ne_of_gt (Real.sqrt_pos.mpr hrad)]

theorem E_deriv_hasDeriv {y : ℝ} (hy : |y|<r) :
    HasDerivAt (fun x => 1/Real.sqrt (radiusSq-x^2))
      (y/(Real.sqrt (radiusSq-y^2))^3) y := by
  have hrad : 0<radiusSq-y^2 := by
    nlinarith [r_sq_radiusSq,r_pos,abs_nonneg y,sq_abs y]
  have hroot := Real.sqrt_pos.mpr hrad
  have hb : HasDerivAt (fun x => radiusSq-x^2) (-(2*y)) y := by
    simpa using (hasDerivAt_pow 2 y).const_sub radiusSq
  have hi := (hb.sqrt hrad.ne').inv hroot.ne'
  convert hi using 1
  · funext x
    rw [one_div]
    rfl
  · field_simp

/-- Convexity applies on the entire positive arc, including both endpoints. -/
theorem E_convex : ConvexOn ℝ (Icc 0 L) E := by
  have hconcave : ConcaveOn ℝ (Icc 0 L) (fun y => -E y) := by
    apply concave_of_deriv2
      (f' := fun y => -(1/Real.sqrt (radiusSq-y^2)))
      (f'' := fun y => -(y/(Real.sqrt (radiusSq-y^2))^3))
    · intro y hy
      exact (E_hasDeriv (by rw [abs_of_nonneg hy.1]; exact hy.2.trans_lt r_bounds.1)).neg
    · intro y hy
      exact (E_deriv_hasDeriv (by rw [abs_of_nonneg hy.1]; exact hy.2.trans_lt r_bounds.1)).neg
    · intro y hy
      exact neg_nonpos.mpr (div_nonneg hy.1 (by positivity))
  have h := hconcave.neg
  convert h using 1
  funext y
  simp

theorem E_symmetric_minimum {d : ℝ} (hd : 0≤d ∧ d≤1)
    (hdL : d≤L) (hother : 1-d≤L) : 2*E (1/2)≤E d+E (1-d) := by
  have hh := E_convex.2 ⟨hd.1,hdL⟩ ⟨by linarith,hother⟩
    (show (0:ℝ)≤1/2 by norm_num) (show (0:ℝ)≤1/2 by norm_num) (by norm_num)
  norm_num [smul_eq_mul] at hh
  have hid : (1/2:ℝ)*d+(1/2)*(1-d)=1/2 := by ring
  rw [hid] at hh
  linarith

theorem atan_side_hasDeriv (y : ℝ) :
    HasDerivAt (fun z => 2*Real.arctan (z/L)) (2*L/(L^2+y^2)) y := by
  have hL := L_pos.ne'
  have h1 : HasDerivAt (fun z => z/L) (1/L) y := (hasDerivAt_id y).div_const L
  have h2 := (Real.hasDerivAt_arctan (y/L)).comp y h1
  have h3 : HasDerivAt (fun z => 2*Real.arctan (z/L)) (2*(1/(1+(y/L)^2)*(1/L))) y :=
    h2.const_mul 2
  convert h3 using 1
  field_simp

theorem vertical_hasDeriv {y : ℝ} (hy : L<y) :
    HasDerivAt verticalAngle
      (L/(y*Real.sqrt (y^2-L^2))) y := by
  have hy0 := L_pos.trans hy
  have hrad : 0<y^2-L^2 := by nlinarith [L_pos]
  have hz : 0<L/y ∧ L/y<1 :=
    ⟨div_pos L_pos hy0,(div_lt_one hy0).mpr hy⟩
  have hroot : Real.sqrt (1-(L/y)^2)=Real.sqrt (y^2-L^2)/y := by
    rw [show 1-(L/y)^2=(y^2-L^2)/y^2 by field_simp,
      Real.sqrt_div hrad.le,Real.sqrt_sq hy0.le]
  have hh := ((Real.hasDerivAt_arccos (by linarith : L/y≠-1)
    (by linarith : L/y≠1)).comp y
      ((hasDerivAt_const y L).div (hasDerivAt_id y) hy0.ne')).const_add (Real.pi/2)
  convert hh using 1
  · rfl
  · rw [hroot]
    field_simp [hy0.ne',ne_of_gt (Real.sqrt_pos.mpr hrad)]
    ring

theorem sideAngle_hasDeriv {A y : ℝ} (hA : L<A) :
    HasDerivAt (sideAngle A)
      ((A+L*y/Real.sqrt (A^2+y^2-L^2))/(A^2+y^2)) y := by
  have hA0 := L_pos.trans hA
  have hn : 0<A^2+y^2 := by positivity
  have hrad : 0<A^2+y^2-L^2 := by nlinarith [L_pos,sq_nonneg y]
  have hN : 0<Real.sqrt (A^2+y^2) := Real.sqrt_pos.mpr hn
  have hD : 0<Real.sqrt (A^2+y^2-L^2) := Real.sqrt_pos.mpr hrad
  have hN₂ : Real.sqrt (A^2+y^2)^2=A^2+y^2 := Real.sq_sqrt hn.le
  have hLN : L<Real.sqrt (A^2+y^2) := by
    nlinarith [L_pos,mul_le_mul hA.le hA.le L_pos.le hA0.le]
  have hratio : 0<L/Real.sqrt (A^2+y^2) ∧ L/Real.sqrt (A^2+y^2)<1 :=
    ⟨div_pos L_pos hN,(div_lt_one hN).mpr hLN⟩
  have hroot : Real.sqrt (1-(L/Real.sqrt (A^2+y^2))^2)=
      Real.sqrt (A^2+y^2-L^2)/Real.sqrt (A^2+y^2) := by
    rw [show 1-(L/Real.sqrt (A^2+y^2))^2=(A^2+y^2-L^2)/Real.sqrt (A^2+y^2)^2 by
      rw [div_pow,hN₂]; field_simp,
      Real.sqrt_div hrad.le,Real.sqrt_sq hN.le]
  have hnorm : HasDerivAt (fun z => Real.sqrt (A^2+z^2)) (y/Real.sqrt (A^2+y^2)) y := by
    have hb : HasDerivAt (fun z => A^2+z^2) (2*y) y := by
      simpa using (hasDerivAt_pow 2 y).const_add (A^2)
    convert hb.sqrt hn.ne' using 1
    field_simp
  have hcos := (Real.hasDerivAt_arccos (by linarith [hratio.1] : -1<L/Real.sqrt (A^2+y^2)).ne'
    hratio.2.ne).comp y ((hasDerivAt_const y L).div hnorm hN.ne')
  have hatan := (Real.hasDerivAt_arctan (y/A)).comp y ((hasDerivAt_id y).div_const A)
  convert hatan.add hcos using 1
  · rfl
  · rw [hroot]
    generalize Real.sqrt (A^2+y^2-L^2)=D at hD ⊢
    generalize Real.sqrt (A^2+y^2)=N at hN hN₂ ⊢
    rw [hN₂]
    field_simp
    ring

end SquaresInCircles.Eight.CentralForbidden
end
end
end

section
/-!
## Fixed endpoint estimates for the continuous forbidden-width proof

These are Taylor inequalities at the three geometric
endpoints and a polynomial with one turning point. They are not a cover of
an angle/state domain. All whole-interval conclusions are in the calculus
modules which consume these fixed inequalities.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CentralForbidden

def C8 (x : ℝ) := 1-x^2/2+x^4/24-x^6/720+x^8/40320
def S9 (x : ℝ) := x-x^3/6+x^5/120-x^7/5040+x^9/362880
def C10 (x : ℝ) := C8 x-x^10/3628800

theorem cos_le_C8 {x : ℝ} (hx : 0≤x) : Real.cos x≤C8 x := by
  have h := nonneg_of_deriv_nonneg (fun t => C8 t-Real.cos t)
    (by dsimp [C8]; fun_prop) (by norm_num [C8])
    (fun t ht => by
      simp (disch := fun_prop) [C8]
      nlinarith [sin_lower_seven ht]) hx
  linarith

theorem sin_le_S9 {x : ℝ} (hx : 0≤x) : Real.sin x≤S9 x := by
  have h := nonneg_of_deriv_nonneg (fun t => S9 t-Real.sin t)
    (by dsimp [S9]; fun_prop) (by norm_num [S9])
    (fun t ht => by
      simp (disch := fun_prop) [S9]
      have hh := cos_le_C8 ht
      dsimp [C8] at hh
      linarith) hx
  linarith

theorem C10_le_cos {x : ℝ} (hx : 0≤x) : C10 x≤Real.cos x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.cos t-C10 t)
    (by dsimp [C10,C8]; fun_prop) (by norm_num [C10,C8])
    (fun t ht => by
      simp (disch := fun_prop) [C10,C8]
      have hh := sin_le_S9 ht
      dsimp [S9] at hh
      linarith) hx
  linarith

def inverseArc (x : ℝ) : ℝ := L*Real.sin x-c*Real.cos x

theorem inverseArc_mono : MonotoneOn inverseArc (Icc 0 (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg (by unfold inverseArc; fun_prop)
    (d := fun x => L*Real.cos x+c*Real.sin x)
  · intro x hx
    have h : HasDerivAt (fun x => L*Real.sin x-c*Real.cos x)
        (L*Real.cos x-c*(-Real.sin x)) x :=
      ((Real.hasDerivAt_sin x).const_mul L).sub ((Real.hasDerivAt_cos x).const_mul c)
    show HasDerivAt (fun x => L*Real.sin x-c*Real.cos x) (L*Real.cos x+c*Real.sin x) x
    convert h using 1
    ring
  · intro x hx
    have ht := cos_sin_nonneg (show 0≤x ∧ x≤Real.pi/2 from ⟨hx.1.le,hx.2.le⟩)
    exact add_nonneg (mul_nonneg L_pos.le ht.1) (mul_nonneg c_pos.le ht.2)

theorem inverseArc_E {y : ℝ} (hy : 0≤y) (hyL : y≤L) :
    inverseArc (E y)=y := by
  have hyr : y≤r := hyL.trans r_bounds.1.le
  have hdiv : -1≤y/r ∧ y/r≤1 :=
    ⟨by have := div_nonneg hy r_pos.le; linarith,(div_le_one r_pos).mpr hyr⟩
  have hs : r*Real.sin (Real.arcsin (y/r))=y := by
    rw [Real.sin_arcsin hdiv.1 hdiv.2]
    field_simp [r_pos.ne']
  have hφ := φ_trig
  have hunit := Real.sin_sq_add_cos_sq φ
  have hscaled : r*inverseArc (E y)=r*y := by
    unfold inverseArc E
    rw [Real.sin_add,Real.cos_add]
    have hcross : L*Real.sin φ-c*Real.cos φ=0 := by
      linear_combination (-Real.sin φ)*hφ.1+Real.cos φ*hφ.2
    have hrad : L*Real.cos φ+c*Real.sin φ=r := by
      linear_combination (-Real.cos φ)*hφ.1-Real.sin φ*hφ.2+r*hunit
    linear_combination Real.sin (Real.arcsin (y/r))*r*hrad +
      Real.cos (Real.arcsin (y/r))*r*hcross + r*hs
  exact (mul_left_cancel₀ r_pos.ne') hscaled

theorem E_lower_of_taylor {x y : ℝ}
    (hx : 0≤x ∧ x≤Real.pi/2) (hy : 0≤y ∧ y≤L)
    (hpoly : L*S9 x-c*C10 x<y) : x<E y := by
  have hs := mul_le_mul_of_nonneg_left (sin_le_S9 hx.1) L_pos.le
  have hc := mul_le_mul_of_nonneg_left (C10_le_cos hx.1) c_pos.le
  have hinv : inverseArc x<y := by dsimp [inverseArc]; linarith
  have hE0 : 0≤E y := (E_support hy.1 (hy.2.trans r_bounds.1.le)).1
  have hEπ : E y≤Real.pi/2 := by simpa using E_mono hy.2
  by_contra! hbad
  have hm := inverseArc_mono ⟨hE0,hEπ⟩ hx hbad
  rw [inverseArc_E hy.1 hy.2] at hm
  linarith

theorem E_endpoint_bounds :
    1437/1000<E (431/500) ∧ 899/1000<E (1/2) ∧ 123/100<E (3/4) := by
  constructor
  · apply E_lower_of_taylor
    · constructor <;> linarith [Real.pi_gt_d2]
    · norm_num [L]
    · norm_num [L,c,S9,C10,C8]
  constructor
  · apply E_lower_of_taylor
    · constructor <;> linarith [Real.pi_gt_d2]
    · norm_num [L]
    · norm_num [L,c,S9,C10,C8]
  · apply E_lower_of_taylor
    · constructor <;> linarith [Real.pi_gt_d2]
    · norm_num [L]
    · norm_num [L,c,S9,C10,C8]

theorem atan_endpoint_bounds :
    149/500<2*Real.arctan ((1379/10000)/L) ∧
      9/50<2*Real.arctan (1/11) := by
  constructor
  · have h := atan_cubic_lower (show 0≤(1379/10000:ℝ)/L by norm_num [L])
    norm_num [L] at h ⊢
    linarith
  · have h := atan_cubic_lower (show (0:ℝ)≤1/11 by norm_num)
    norm_num at h
    linarith

def widthPolynomial (d : ℝ) : ℝ :=
  d^4+6*L^2*d^2-8*L^2*d+4*L^2-3*L^4-4*L^2*c^2

def widthPolynomialDeriv (d : ℝ) : ℝ := 4*d^3+12*L^2*d-8*L^2

theorem widthPolynomial_hasDeriv (d : ℝ) :
    HasDerivAt widthPolynomial (widthPolynomialDeriv d) d := by
  have h := (((hasDerivAt_pow 4 d).add ((hasDerivAt_pow 2 d).const_mul (6*L^2))).sub
    ((hasDerivAt_id d).const_mul (8*L^2))).add_const (4*L^2-3*L^4-4*L^2*c^2)
  convert h using 1
  · funext x
    simp only [widthPolynomial,Pi.add_apply,Pi.sub_apply,id]
    ring
  · norm_num [widthPolynomialDeriv]
    ring

theorem widthPolynomial_deriv_negative {d : ℝ} (hd : 0≤d ∧ d≤c) :
    widthPolynomialDeriv d<0 := by
  have hpow := pow_le_pow_left₀ hd.1 hd.2 3
  have hlin := mul_le_mul_of_nonneg_left hd.2 (show 0≤12*L^2 by positivity)
  dsimp [widthPolynomialDeriv,L,c] at *
  norm_num at *
  linarith

theorem widthPolynomial_antitone : AntitoneOn widthPolynomial (Icc 0 c) := by
  exact antiOn_of_hasDeriv_nonpos
    (fun x _ => (widthPolynomial_hasDeriv x).continuousAt.continuousWithinAt)
    (fun d _ => widthPolynomial_hasDeriv d)
    (fun d hd => (widthPolynomial_deriv_negative ⟨hd.1.le,hd.2.le⟩).le)

theorem widthPolynomial_signs :
    0<widthPolynomial (1379/10000) ∧ widthPolynomial (69/500)<0 := by
  norm_num [widthPolynomial,L,c]

theorem steep_vertical_reserve : 2/L<L/(r*c) := by
  have hid : L^4>4*radiusSq*c^2 := by norm_num [L,c,radiusSq]
  have hr := r_sq_radiusSq
  have hsq : 2*r*c<L^2 := by
    nlinarith [sq_nonneg (L^2+2*r*c),L_pos,c_pos,r_pos]
  apply (div_lt_div_iff₀ L_pos (mul_pos r_pos c_pos)).mpr
  nlinarith

theorem sideAngle_gt_of_support {A y x : ℝ} (hA : L≤A)
    (hy : 0≤y) (_hrad : A^2+y^2≤radiusSq)
    (hx : Real.arctan (y/A)≤x ∧ x≤Real.pi)
    (hs : L<A*Real.cos x+y*Real.sin x) : x<sideAngle A y := by
  have hA0 := L_pos.trans_le hA
  obtain ⟨hc,hsin⟩ := atan_frame hA0 hy
  have hN : 0<Real.sqrt (A^2+y^2) := Real.sqrt_pos.mpr (by positivity)
  have hN₂ : Real.sqrt (A^2+y^2)^2=A^2+y^2 := Real.sq_sqrt (by positivity)
  have hθ0 : 0≤Real.arctan (y/A) := Real.arctan_nonneg.mpr (div_nonneg hy hA0.le)
  unfold sideAngle
  generalize Real.sqrt (A^2+y^2)=N at hc hsin hN hN₂ ⊢
  generalize Real.arctan (y/A)=θ at hc hsin hθ0 hx ⊢
  have hNL : L≤N := by
    have h2 : L^2≤N^2 := by nlinarith [mul_le_mul hA hA L_pos.le hA0.le,sq_nonneg y]
    exact (abs_le_of_sq_le_sq h2 hN.le).trans' (le_abs_self L)
  have hψ0 : 0≤Real.arccos (L/N) := Real.arccos_nonneg _
  have hcosψ : Real.cos (Real.arccos (L/N))=L/N := Real.cos_arccos
    (by have := div_nonneg L_pos.le hN.le; linarith) ((div_le_one hN).mpr hNL)
  generalize Real.arccos (L/N)=ψ at hψ0 hcosψ ⊢
  have hrot : N*Real.cos (x-θ)=A*Real.cos x+y*Real.sin x := by
    rw [Real.cos_sub]
    linear_combination Real.cos x*hc+Real.sin x*hsin
  by_contra! hbad
  have hbad' : ψ≤x-θ := by linarith
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi hψ0
    (show x-θ≤Real.pi by linarith [hx.2]) hbad'
  have hprod := mul_le_mul_of_nonneg_left hm hN.le
  rw [hrot,hcosψ] at hprod
  have he : N*(L/N)=L := by field_simp
  rw [he] at hprod
  linarith

theorem stronger_side_endpoint :
    (1/4:ℝ)<sideAngle (19/20) 0 ∧
      9/25<sideAngle (19/20) (1/12) := by
  constructor
  · apply sideAngle_gt_of_support
    · norm_num [L]
    · norm_num
    · norm_num [radiusSq]
    · constructor
      · norm_num
      · linarith [Real.pi_gt_d2]
    · have hc := cos_lower_six (show (0:ℝ)≤1/4 by norm_num)
      norm_num [L] at hc ⊢
      linarith
  · apply sideAngle_gt_of_support
    · norm_num [L]
    · norm_num
    · norm_num [radiusSq]
    · constructor
      · have ha := atan_upper (show (0:ℝ)≤(1/12)/(19/20) by norm_num)
        norm_num at ha ⊢
        linarith
      · linarith [Real.pi_gt_d2]
    · have hc := cos_lower_six (show (0:ℝ)≤9/25 by norm_num)
      have hs := sin_lower_seven (show (0:ℝ)≤9/25 by norm_num)
      norm_num [L] at hc hs ⊢
      linarith

end SquaresInCircles.Eight.CentralForbidden
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CentralForbidden

def lowerTransition : ℝ := 1-L
def middleWidth (d : ℝ) : ℝ := 2*Real.arctan (d/L)+E (1-d)
def lowerWidth (d : ℝ) : ℝ := 2*Real.arctan (d/L)+verticalAngle (1-d)

theorem middleWidth_hasDeriv {d : ℝ} (hd : lowerTransition≤d ∧ d≤c) :
    HasDerivAt middleWidth
      (2*L/(L^2+d^2)-1/Real.sqrt (radiusSq-(1-d)^2)) d := by
  have he := E_hasDeriv (y := 1-d) (by
    have hpos : 0≤1-d := by dsimp [c] at hd; linarith
    rw [abs_of_nonneg hpos]
    have hL : 1-d≤L := by dsimp [lowerTransition] at hd; linarith
    exact hL.trans_lt r_bounds.1)
  convert (atan_side_hasDeriv d).add
    (he.comp d ((hasDerivAt_const d 1).sub (hasDerivAt_id d))) using 1
  · rfl
  · ring

theorem middle_derivative_nonpositive {d : ℝ}
    (hd : lowerTransition≤d ∧ d≤c) (hP : 0≤widthPolynomial d) :
    2*L/(L^2+d^2)-1/Real.sqrt (radiusSq-(1-d)^2)≤0 := by
  have hd0 : 0≤d := by norm_num [lowerTransition,L] at hd; linarith
  have hother : 0≤1-d ∧ 1-d≤L := by dsimp [lowerTransition,L,c] at hd ⊢; constructor <;> linarith
  have hrad : 0<radiusSq-(1-d)^2 := by
    linarith [pow_le_pow_left₀ hother.1 hother.2 2,r_sq,r_sq_radiusSq,pow_pos c_pos 2]
  let M := Real.sqrt (radiusSq-(1-d)^2)
  have hM : 0<M := Real.sqrt_pos.mpr hrad
  have hM₂ : M^2=radiusSq-(1-d)^2 := Real.sq_sqrt hrad.le
  have hden : 0<L^2+d^2 := add_pos_of_pos_of_nonneg (pow_pos L_pos 2) (sq_nonneg d)
  have hid : (L^2+d^2)^2-(2*L*M)^2=widthPolynomial d := by
    unfold widthPolynomial
    linear_combination (-4*L^2)*hM₂+4*L^2*r_sq_radiusSq-4*L^2*r_sq
  have hcomparison : 2*L*M≤L^2+d^2 :=
    (le_abs_self _).trans (abs_le_of_sq_le_sq (by linarith) hden.le)
  apply sub_nonpos.mpr
  apply (div_le_div_iff₀ hden hM).mpr
  simpa [M] using hcomparison

theorem middle_derivative_nonnegative {d : ℝ}
    (hd : lowerTransition≤d ∧ d≤c) (hP : widthPolynomial d≤0) :
    0≤2*L/(L^2+d^2)-1/Real.sqrt (radiusSq-(1-d)^2) := by
  have hother : 0≤1-d ∧ 1-d≤L := by dsimp [lowerTransition,L,c] at hd ⊢; constructor <;> linarith
  have hrad : 0<radiusSq-(1-d)^2 := by
    linarith [pow_le_pow_left₀ hother.1 hother.2 2,r_sq,r_sq_radiusSq,pow_pos c_pos 2]
  let M := Real.sqrt (radiusSq-(1-d)^2)
  have hM : 0<M := Real.sqrt_pos.mpr hrad
  have hM₂ : M^2=radiusSq-(1-d)^2 := Real.sq_sqrt hrad.le
  have hden : 0<L^2+d^2 := add_pos_of_pos_of_nonneg (pow_pos L_pos 2) (sq_nonneg d)
  have hid : (L^2+d^2)^2-(2*L*M)^2=widthPolynomial d := by
    unfold widthPolynomial
    linear_combination (-4*L^2)*hM₂+4*L^2*r_sq_radiusSq-4*L^2*r_sq
  have hcomparison : L^2+d^2≤2*L*M :=
    (le_abs_self _).trans (abs_le_of_sq_le_sq (by linarith) (mul_pos (mul_pos two_pos L_pos) hM).le)
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ hM hden).mpr
  simpa [M] using hcomparison

/-- The single sign-changing polynomial traps the minimum, not a mesh. -/
theorem middleWidth_lower {d : ℝ} (hd : lowerTransition≤d ∧ d≤c) :
    347/200<middleWidth d := by
  obtain ⟨a,ha_def⟩ : ∃ a : ℝ, a=1379/10000 := ⟨_,rfl⟩
  obtain ⟨b,hb_def⟩ : ∃ b : ℝ, b=69/500 := ⟨_,rfl⟩
  have ha : lowerTransition≤a ∧ a≤c := by rw [ha_def]; norm_num [lowerTransition,L,c]
  have hb : lowerTransition≤b ∧ b≤c := by rw [hb_def]; norm_num [lowerTransition,L,c]
  have hab : a≤b := by rw [ha_def,hb_def]; norm_num
  have hlt0 : 0<lowerTransition := by norm_num [lowerTransition,L]
  have hleft : AntitoneOn middleWidth (Icc lowerTransition a) := by
    apply antiOn_of_hasDeriv_nonpos (by unfold middleWidth E; fun_prop)
      (fun x hx => middleWidth_hasDeriv ⟨hx.1.le,hx.2.le.trans ha.2⟩)
    intro x hx
    apply middle_derivative_nonpositive ⟨hx.1.le,hx.2.le.trans ha.2⟩
    have hP := widthPolynomial_antitone
      ⟨by linarith [hx.1],hx.2.le.trans ha.2⟩
      ⟨by linarith [ha.1],ha.2⟩ hx.2.le
    rw [ha_def] at hP
    exact widthPolynomial_signs.1.le.trans hP
  have hright : MonotoneOn middleWidth (Icc b c) := by
    apply monoOn_of_hasDeriv_nonneg (by unfold middleWidth E; fun_prop)
      (fun x hx => middleWidth_hasDeriv ⟨hb.1.trans hx.1.le,hx.2.le⟩)
    intro x hx
    apply middle_derivative_nonnegative ⟨hb.1.trans hx.1.le,hx.2.le⟩
    have hP := widthPolynomial_antitone ⟨by linarith [hb.1],hb.2⟩
      ⟨by linarith [hx.1,hb.1],hx.2.le⟩ hx.1.le
    rw [hb_def] at hP
    exact hP.trans widthPolynomial_signs.2.le
  have hbase : 347/200<2*Real.arctan (a/L)+E (1-b) := by
    have h₁ := atan_endpoint_bounds.1
    have h₂ := E_endpoint_bounds.1
    have hid : (1:ℝ)-b=431/500 := by rw [hb_def]; norm_num
    rw [hid,ha_def]
    linarith
  have hwindow (x : ℝ) (hx : a≤x ∧ x≤b) :
      2*Real.arctan (a/L)+E (1-b)≤middleWidth x := by
    have h₁ := Real.arctan_mono (div_le_div_of_nonneg_right hx.1 L_pos.le)
    have h₂ := E_mono (show 1-b≤1-x by linarith)
    dsimp [middleWidth]
    linarith
  by_cases hda : d≤a
  · exact hbase.trans_le ((hwindow a ⟨le_rfl,hab⟩).trans
      (hleft ⟨hd.1,hda⟩ ⟨ha.1,le_rfl⟩ hda))
  by_cases hbd : b≤d
  · exact hbase.trans_le ((hwindow b ⟨hab,le_rfl⟩).trans
      (hright ⟨le_rfl,hb.2⟩ ⟨hbd,hd.2⟩ hbd))
  · exact hbase.trans_le (hwindow d ⟨(lt_of_not_ge hda).le,(lt_of_not_ge hbd).le⟩)

theorem lowerWidth_hasDeriv {d : ℝ}
    (hd : 1-r<d ∧ d<lowerTransition) :
    HasDerivAt lowerWidth
      (2*L/(L^2+d^2)-L/((1-d)*Real.sqrt ((1-d)^2-L^2))) d := by
  have hy : L<1-d := by dsimp [lowerTransition] at hd; linarith
  convert (atan_side_hasDeriv d).add
    ((vertical_hasDeriv hy).comp d
      ((hasDerivAt_const d 1).sub (hasDerivAt_id d))) using 1
  · rfl
  · ring

theorem lowerWidth_antitone : AntitoneOn lowerWidth (Icc (1-r) lowerTransition) := by
  apply antiOn_of_hasDeriv_nonpos
    (by
      unfold lowerWidth verticalAngle
      apply ContinuousOn.add
      · fun_prop
      · apply continuous_const.continuousOn.add
        apply Real.continuous_arccos.comp_continuousOn
        apply continuous_const.continuousOn.div
          (by fun_prop)
        intro d hd
        have hpos : L≤1-d := by have h := hd.2; dsimp [lowerTransition] at h; linarith
        exact ne_of_gt (L_pos.trans_le hpos))
    (fun d hd => lowerWidth_hasDeriv hd)
  intro d hd
  have hyL : L<1-d := by have h := hd.2; dsimp [lowerTransition] at h; linarith
  have hyr : 1-d<r := by linarith [hd.1]
  have hy0 := L_pos.trans hyL
  have hrad : 0<(1-d)^2-L^2 := by nlinarith [L_pos]
  have hm := Real.sqrt_pos.mpr hrad
  have hmc : Real.sqrt ((1-d)^2-L^2)≤c := by
    have hsq := pow_le_pow_left₀ hy0.le hyr.le 2
    calc Real.sqrt ((1-d)^2-L^2)≤Real.sqrt (c^2) :=
          Real.sqrt_le_sqrt (by linarith [r_sq])
      _=c := Real.sqrt_sq c_pos.le
  have hprod : (1-d)*Real.sqrt ((1-d)^2-L^2)≤r*c := by
    exact mul_le_mul hyr.le hmc hm.le r_pos.le
  have hsecond : L/(r*c)≤L/((1-d)*Real.sqrt ((1-d)^2-L^2)) :=
    div_le_div_of_nonneg_left L_pos.le (mul_pos hy0 hm) hprod
  have hfirst : 2*L/(L^2+d^2)≤2/L := by
    apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg (pow_pos L_pos 2) (sq_nonneg d)) L_pos).mpr
    nlinarith [sq_nonneg d]
  linarith [steep_vertical_reserve]

theorem first_width_lower {d : ℝ} (hd : 0≤d ∧ d≤1/2) :
    347/200<F L d+F L (1-d) := by
  have hLr := r_bounds.1
  by_cases hsmall : d≤lowerTransition
  · have hdcore : d≤k L := by rw [k_L]; dsimp [lowerTransition,L,c] at hsmall ⊢; linarith
    rw [F_eq_side hdcore,sideAngle_L d hd.1]
    by_cases hfar : r≤1-d
    · rw [F_eq_constant le_rfl hLr hfar]
      have hatan : 0≤Real.arctan (d/L) := Real.arctan_nonneg.mpr (div_nonneg hd.1 L_pos.le)
      linarith [Real.pi_gt_d2,φ_bounds.1]
    · have hyL : L≤1-d := by dsimp [lowerTransition] at hsmall; linarith
      rw [F_eq_vertical le_rfl hLr hyL (le_of_not_ge hfar)]
      have hmono := lowerWidth_antitone
        ⟨by linarith,hsmall⟩ ⟨by linarith [r_bounds.1],le_rfl⟩ hsmall
      have hend : lowerWidth lowerTransition=2*Real.arctan (1/11)+Real.pi/2 := by
        have hrat : lowerTransition/L=(1/11:ℝ) := by norm_num [lowerTransition,L]
        have hid : 1-lowerTransition=L := by unfold lowerTransition; ring
        rw [lowerWidth,hrat,hid,verticalAngle_L]
      rw [hend] at hmono
      change 347/200<lowerWidth d
      linarith [atan_endpoint_bounds.2,Real.pi_gt_d2]
  by_cases hmiddle : d≤c
  · have hdcore : d≤k L := by simpa using hmiddle
    have hyk : k L≤1-d := by rw [k_L]; dsimp [c] at hmiddle ⊢; linarith
    have hyL : 1-d≤L := by dsimp [lowerTransition] at hsmall; linarith
    rw [F_eq_side hdcore,sideAngle_L d hd.1,F_eq_E le_rfl hLr hyk hyL]
    exact middleWidth_lower ⟨(le_of_not_ge hsmall),hmiddle⟩
  · have hdk : k L≤d := by rw [k_L]; exact le_of_not_ge hmiddle
    have hdL : d≤L := by dsimp [L]; linarith
    have hotherk : k L≤1-d := by rw [k_L]; dsimp [c]; linarith
    have hotherL : 1-d≤L := by dsimp [c,L] at hmiddle ⊢; linarith
    rw [F_eq_E le_rfl hLr hdk hdL,F_eq_E le_rfl hLr hotherk hotherL]
    have hc := E_symmetric_minimum ⟨hd.1,by linarith⟩ hdL hotherL
    linarith [E_endpoint_bounds.2.1]

abbrev strongerA : ℝ := 19/20

theorem stronger_k_bounds :
    L<strongerA ∧ strongerA<r ∧ lowerTransition<k strongerA ∧ k strongerA<1/4 := by
  have hAr : strongerA<r := by
    have hr := r_sq_radiusSq
    have hp := r_pos
    dsimp [strongerA,radiusSq] at *
    nlinarith
  have hA : L<strongerA := by norm_num [L,strongerA]
  have hk := k_spec hA.le hAr
  refine ⟨hA,hAr,?_,?_⟩ <;>
    dsimp [lowerTransition,L,strongerA,radiusSq] at * <;> nlinarith

/-- A derivative bound on the entire short-side branch. -/
theorem stronger_side_derivative {d : ℝ}
    (hd : lowerTransition≤d ∧ d≤k strongerA) :
    (5/4:ℝ)<(strongerA+L*d/Real.sqrt (strongerA^2+d^2-L^2))/(strongerA^2+d^2) := by
  have hl : (1/12:ℝ)≤d := by have h := hd.1; norm_num [lowerTransition,L] at h; linarith
  have hd0 : 0<d := by linarith
  have hrad : 0<strongerA^2+d^2-L^2 := by
    norm_num [strongerA,L]
    nlinarith [sq_nonneg d]
  have hM : 0<Real.sqrt (strongerA^2+d^2-L^2) := Real.sqrt_pos.mpr hrad
  have hM₂ : Real.sqrt (strongerA^2+d^2-L^2)^2=strongerA^2+d^2-L^2 := Real.sq_sqrt hrad.le
  have hk := k_spec stronger_k_bounds.1.le stronger_k_bounds.2.1
  have hden : 0<strongerA^2+d^2 := by positivity
  have hdenU : strongerA^2+d^2≤radiusSq := by
    have := pow_le_pow_left₀ hd0.le hd.2 2
    linarith [hk.2.1]
  generalize Real.sqrt (strongerA^2+d^2-L^2)=M at hM hM₂ ⊢
  have hratio : (5/16:ℝ)<d/M := by
    apply (lt_div_iff₀ hM).mpr
    have hd2 : (1/12:ℝ)^2≤d^2 := pow_le_pow_left₀ (by norm_num) hl 2
    have hsq : (5/16*M)^2<d^2 := by
      norm_num [strongerA,L] at hM₂
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 hd0.le hsq
  apply (lt_div_iff₀ hden).mpr
  have hmul : L*(5/16)<L*d/M := by
    rw [mul_div_assoc]
    exact mul_lt_mul_of_pos_left hratio L_pos
  have hreserve : (5/4:ℝ)*radiusSq<19/20+5*L/16 := by norm_num [radiusSq,L]
  simp only [strongerA] at hdenU ⊢
  linarith

theorem stronger_side_tangent {d : ℝ}
    (hd : lowerTransition≤d ∧ d≤k strongerA) :
    sideAngle strongerA lowerTransition+(5/4)*(d-lowerTransition)≤sideAngle strongerA d := by
  let g : ℝ → ℝ := fun x => sideAngle strongerA x-(5/4)*x
  have hgd (x : ℝ) : HasDerivAt g
      ((strongerA+L*x/Real.sqrt (strongerA^2+x^2-L^2))/(strongerA^2+x^2)-5/4) x := by
    have h1 := sideAngle_hasDeriv (y := x) stronger_k_bounds.1
    have h2 : HasDerivAt (fun x : ℝ => (5/4:ℝ)*x) (5/4) x := by
      convert (hasDerivAt_id' x).const_mul (5/4:ℝ) using 1
      ring
    exact h1.sub h2
  have hm : MonotoneOn g (Icc lowerTransition (k strongerA)) :=
    monoOn_of_hasDeriv_nonneg (fun x _ => (hgd x).continuousAt.continuousWithinAt)
      (fun x _ => hgd x)
      (fun x hx => sub_nonneg.mpr (stronger_side_derivative ⟨hx.1.le,hx.2.le⟩).le)
  have hh := hm ⟨le_rfl,stronger_k_bounds.2.2.1.le⟩ hd hd.1
  dsimp only [g] at hh
  linarith

def strongerComparison (d : ℝ) : ℝ :=
  9/25+(5/4)*(d-lowerTransition)+E (1-d)

theorem strongerComparison_antitone :
    AntitoneOn strongerComparison (Icc lowerTransition (1/4)) := by
  apply antiOn_of_hasDeriv_nonpos (by unfold strongerComparison E; fun_prop)
    (d := fun d => 5/4-1/Real.sqrt (radiusSq-(1-d)^2))
  · intro d hd
    have hh := E_hasDeriv (y := 1-d) (by
      rw [abs_of_nonneg (by linarith [hd.2] : 0≤1-d)]
      have hL : 1-d≤L := by have h := hd.1; dsimp [lowerTransition] at h; linarith
      exact hL.trans_lt r_bounds.1)
    convert (((hasDerivAt_id d).sub_const lowerTransition).const_mul (5/4)).const_add (9/25)
      |>.add (hh.comp d ((hasDerivAt_const d 1).sub (hasDerivAt_id d))) using 1
    · rfl
    · ring
  · intro d hd
    have hroot : Real.sqrt (radiusSq-(1-d)^2)<4/5 := by
      apply (Real.sqrt_lt' (by norm_num : (0:ℝ)<4/5)).mpr
      have h := hd.2
      dsimp [radiusSq]
      nlinarith
    have hrad : 0<radiusSq-(1-d)^2 := by
      have hyL : 1-d≤L := by have h := hd.1; dsimp [lowerTransition] at h; linarith
      have hy0 : 0≤1-d := by linarith [hd.2]
      nlinarith [r_bounds.1,r_sq_radiusSq,r_pos]
    have hroot0 := Real.sqrt_pos.mpr hrad
    have hrec : (5/4:ℝ)<1/Real.sqrt (radiusSq-(1-d)^2) := by
      apply (lt_div_iff₀ hroot0).mpr
      nlinarith
    linarith

theorem stronger_width_lower {d : ℝ} (hd : 0≤d ∧ d≤1/2) :
    899/500<F strongerA d+F strongerA (1-d) := by
  have hA := stronger_k_bounds.1.le
  have hAr := stronger_k_bounds.2.1
  by_cases hsmall : d≤lowerTransition
  · have hfirst := F_ge_initial_side hA hAr hd.1
    have hsecond := F_ge_half_pi hA hAr (show L≤1-d by dsimp [lowerTransition] at hsmall; linarith)
    have hside : (1/4:ℝ)<sideAngle strongerA 0 := stronger_side_endpoint.1
    linarith [Real.pi_gt_d2]
  by_cases hmiddle : d≤k strongerA
  · have hdk : lowerTransition≤d := le_of_not_ge hsmall
    have hotherk : k strongerA≤1-d := by linarith [stronger_k_bounds.2.2.2]
    have hotherL : 1-d≤L := by dsimp [lowerTransition] at hdk; linarith
    rw [F_eq_side hmiddle,F_eq_E hA hAr hotherk hotherL]
    have hside := stronger_side_tangent ⟨hdk,hmiddle⟩
    have hstart : 9/25<sideAngle strongerA lowerTransition := by
      have hlt : lowerTransition=1/12 := by norm_num [lowerTransition,L]
      rw [hlt]
      exact stronger_side_endpoint.2
    have hcomp := strongerComparison_antitone
      ⟨hdk,hmiddle.trans stronger_k_bounds.2.2.2.le⟩
      ⟨by norm_num [lowerTransition,L],le_rfl⟩
      (hmiddle.trans stronger_k_bounds.2.2.2.le)
    have hend : 899/500<strongerComparison (1/4) := by
      dsimp [strongerComparison,lowerTransition,L]
      norm_num
      linarith [E_endpoint_bounds.2.2]
    have hcd : strongerComparison d=9/25+(5/4)*(d-lowerTransition)+E (1-d) := rfl
    linarith
  · have hdk : k strongerA≤d := le_of_not_ge hmiddle
    have hdL : d≤L := by dsimp [L]; linarith
    have hotherk : k strongerA≤1-d := by linarith [stronger_k_bounds.2.2.2]
    have hotherL : 1-d≤L := by
      have hdk' := stronger_k_bounds.2.2.1.trans_le hdk
      dsimp [lowerTransition] at hdk'
      linarith
    rw [F_eq_E hA hAr hdk hdL,F_eq_E hA hAr hotherk hotherL]
    have hm := E_symmetric_minimum ⟨hd.1,by linarith⟩ hdL hotherL
    linarith [E_endpoint_bounds.2.1]

/-- The entire interval is forbidden, including all weak rectangle endpoints. -/
theorem bandA_forbidden {d : ℝ} (hd : 0≤d ∧ d≤1/2) :
    ∃ l u : ℝ, l≤0 ∧ 0≤u ∧ (347/200)<u-l ∧ u-l≤4 ∧
      ∀ β, l≤β ∧ β≤u → ∃ v, |v|≤c ∧
        let p := pointInDirection (0,0) (β : Direction) L v
        0≤p.1 ∧ p.1≤(11/12) ∧ -d≤p.2 ∧ p.2≤1-d := by
  exact centered_rectangle_forbidden le_rfl r_bounds.1 hd (first_width_lower hd)

theorem bandB_forbidden {d : ℝ} (hd : 0≤d ∧ d≤1/2) :
    ∃ l u : ℝ, l≤0 ∧ 0≤u ∧ (899/500)<u-l ∧ u-l≤4 ∧
      ∀ β, l≤β ∧ β≤u → ∃ v, |v|≤c ∧
        let p := pointInDirection (0,0) (β : Direction) L v
        0≤p.1 ∧ p.1≤(19/20) ∧ -d≤p.2 ∧ p.2≤1-d := by
  exact centered_rectangle_forbidden stronger_k_bounds.1.le stronger_k_bounds.2.1 hd
    (stronger_width_lower hd)

end SquaresInCircles.Eight.CentralForbidden
end
end
end
