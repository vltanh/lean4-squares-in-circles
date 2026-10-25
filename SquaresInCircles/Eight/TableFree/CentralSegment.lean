module

public import SquaresInCircles.Common.Charts
public import SquaresInCircles.Common.Analysis
public import SquaresInCircles.Common.Trigonometry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A connected interval of forbidden segment directions

Uncompiled draft. This is the geometric part of the central-core argument.
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