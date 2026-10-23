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
    (by fun_prop) (by norm_num)
    (fun t ht => by
      have hd : 0<1+t^2 := by positivity
      have hderiv := (Real.hasDerivAt_arctan t).sub (hasDerivAt_id t)
      have hderiv' := hderiv.add (((hasDerivAt_id t).pow 3).div_const 3)
      rw [hderiv'.deriv]
      field_simp
      positivity) hx
  linarith

theorem atan_upper {x : ℝ} (hx : 0≤x) : Real.arctan x≤x := by
  have hh := nonneg_of_deriv_nonneg
    (fun t => t-Real.arctan t)
    (by fun_prop) (by norm_num)
    (fun t ht => by
      rw [((hasDerivAt_id t).sub (Real.hasDerivAt_arctan t)).deriv]
      have hd : 0<1+t^2 := by positivity
      field_simp
      positivity) hx
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
    exact (div_eq_div_iff (ne_of_gt hcos) (ne_of_gt L_pos)).mp htan
  have hr := r_sq
  have hp := r_pos
  have hLc := mul_pos L_pos hcos
  have hcroot : r*Real.cos φ=L := by
    have hid := congrArg (fun x : ℝ => x^2) hrelation
    have hnorm := congrArg (fun z : ℝ => L^2*z) hunit
    nlinarith [sq_nonneg (r*Real.cos φ+L)]
  have hsc : r*Real.sin φ=c := by
    have hid := congrArg (fun z : ℝ => r*z) hrelation
    nlinarith
  exact ⟨hcroot,hsc⟩

theorem arccos_L_div_r : Real.arccos (L/r)=φ := by
  have he : L/r=Real.cos φ := by exact (div_eq_iff (ne_of_gt r_pos)).mpr φ_trig.1.symm
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
  let ρ := Real.sqrt (x^2+y^2)
  have hρ₂ : ρ^2=x^2+y^2 := Real.sq_sqrt (by positivity)
  have hρ₀ : 0≤ρ := Real.sqrt_nonneg _
  have hunitγ := Real.sin_sq_add_cos_sq γ
  have hcauchy := cauchy_sq (x,y) (Real.cos γ,Real.sin γ)
  dsimp [dot,normSq] at hcauchy
  have hρL : L≤ρ := by nlinarith [L_pos]
  have hρ : 0<ρ := L_pos.trans_le hρL
  have hxr : -1≤x/ρ ∧ x/ρ≤1 := by
    constructor
    · apply (le_div_iff₀ hρ).mpr
      linarith [hp.1]
    · apply (div_le_iff₀ hρ).mpr
      nlinarith [hp.1,sq_nonneg y]
  let θ := Real.arccos (x/ρ)
  have hθ₀ : 0≤θ := Real.arccos_nonneg _
  have hθ₁ : θ≤Real.pi/2 := Real.arccos_le_pi_div_two.mpr (div_nonneg hp.1 hρ.le)
  have hcosθ : ρ*Real.cos θ=x := by
    rw [Real.cos_arccos hxr.1 hxr.2]
    field_simp
  have hsinθ : ρ*Real.sin θ=y := by
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hθ₀ (by linarith [Real.pi_pos])
    have hunit := Real.sin_sq_add_cos_sq θ
    nlinarith [congrArg (fun z : ℝ => ρ^2*z) hunit,
      congrArg (fun z : ℝ => z^2) hcosθ,hp.2.2.1]
  intro β hβ
  by_cases hβθ : β≤θ
  · refine ⟨0,by norm_num [c],?_⟩
    have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hβ.1,Real.pi_pos]) hθ₁ hβθ
    have hc := cos_sin_nonneg (x := β) ⟨hβ.1,hβθ.trans hθ₁⟩
    have hsin' := mul_le_mul_of_nonneg_left hsin L_pos.le
    have hρ' := mul_le_mul_of_nonneg_right hρL
      (Real.sin_nonneg_of_nonneg_of_le_pi hθ₀ (by linarith [Real.pi_pos]))
    have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one β) L_pos.le
    simp only [Rectangle,pointInDirection,Real.Angle.cos_coe,Real.Angle.sin_coe,
      mul_zero,sub_zero,zero_add]
    exact ⟨mul_nonneg L_pos.le hc.1,by linarith,
      mul_nonneg L_pos.le hc.2,by linarith [hp.2.2.2]⟩
  · have hproj : L≤x*Real.cos β+y*Real.sin β := by
      have hmono := Real.cos_le_cos_of_nonneg_of_le_pi
        (show 0≤β-θ by linarith)
        (show γ-θ≤Real.pi by linarith [hγ.2,hθ₀,Real.pi_gt_three])
        (show β-θ≤γ-θ by linarith [hβ.2])
      have hm := mul_le_mul_of_nonneg_left hmono hρ.le
      have hid (t : ℝ) : ρ*Real.cos (t-θ)=x*Real.cos t+y*Real.sin t := by
        rw [Real.cos_sub]
        nlinarith [hcosθ,hsinθ]
      rw [hid γ,hid β] at hm
      exact hsupport.trans hm
    let D := x*Real.cos β+y*Real.sin β
    let t := L/D
    let qx := t*x
    let qy := t*y
    let v := -Real.sin β*qx+Real.cos β*qy
    have hD : 0<D := by dsimp [D]; linarith [L_pos]
    have ht : 0<t ∧ t≤1 := ⟨div_pos L_pos hD,(div_le_one hD).mpr hproj⟩
    have hdot : qx*Real.cos β+qy*Real.sin β=L := by
      dsimp [qx,qy,t,D]
      field_simp [ne_of_gt hD]
      ring
    have hpoint : pointInDirection (0,0) (β : Direction) L v=(qx,qy) := by
      have hu := Real.sin_sq_add_cos_sq β
      apply Prod.ext <;> dsimp [pointInDirection,v]
      · linear_combination qx*hu+Real.cos β*hdot
      · linear_combination qy*hu+Real.sin β*hdot
    have hnorm : qx^2+qy^2≤radiusSq := by
      have htu : t^2≤1 := by nlinarith
      have hh := mul_le_mul_of_nonneg_right htu (show 0≤x^2+y^2 by positivity)
      dsimp [qx,qy]
      nlinarith
    have hv₂ : v^2≤c^2 := by
      have hn := pointInDirection_norm (0,0) (β : Direction) L v
      rw [hpoint] at hn
      dsimp [normSq,sub,L,c,radiusSq] at *
      nlinarith
    refine ⟨v,?_,?_⟩
    · nlinarith [sq_abs v,abs_nonneg v,c_pos]
    · rw [hpoint]
      have hx := mul_le_mul_of_nonneg_right ht.2 hp.1
      have hy := mul_le_mul_of_nonneg_right ht.2 hp.2.2.1
      exact ⟨mul_nonneg ht.1.le hp.1,by dsimp [qx]; linarith [hp.2.1],
        mul_nonneg ht.1.le hp.2.2.1,by dsimp [qy]; linarith [hp.2.2.2]⟩

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
  let ρ := Real.sqrt (A^2+y^2)
  let θ := Real.arctan (y/A)
  have hρ : 0<ρ := Real.sqrt_pos.mpr (by nlinarith)
  have hρ₂ : ρ^2=A^2+y^2 := Real.sq_sqrt (by positivity)
  have hθ : 0≤θ ∧ θ<Real.pi/2 :=
    ⟨Real.arctan_nonneg.mpr (div_nonneg hy hA.le),Real.arctan_lt_pi_div_two _⟩
  have hc : 0<Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩
  have hs : 0≤Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
    (by linarith [hθ.2,Real.pi_pos])
  have htan : Real.sin θ/Real.cos θ=y/A := by
    rw [← Real.tan_eq_sin_div_cos]
    exact Real.tan_arctan _
  have hcross := (div_eq_div_iff hc.ne' hA.ne').mp htan
  have hunit := congrArg (fun z : ℝ => A^2*z) (Real.sin_sq_add_cos_sq θ)
  have hsquare := congrArg (fun z : ℝ => z^2) hcross
  have hcos : ρ*Real.cos θ=A := by nlinarith
  exact ⟨hcos,by nlinarith [congrArg (fun z : ℝ => ρ*z) hcross]⟩

theorem sideAngle_support {A y : ℝ} (hA : L≤A) (hy : 0≤y)
    (hrad : A^2+y^2≤radiusSq) :
    0≤sideAngle A y ∧ sideAngle A y≤2 ∧
      A*Real.cos (sideAngle A y)+y*Real.sin (sideAngle A y)=L := by
  have hA0 : 0<A := L_pos.trans_le hA
  let ρ := Real.sqrt (A^2+y^2)
  let θ := Real.arctan (y/A)
  let ψ := Real.arccos (L/ρ)
  have hρ0 : 0<ρ := Real.sqrt_pos.mpr (by nlinarith)
  have hρ₂ : ρ^2=A^2+y^2 := Real.sq_sqrt (by positivity)
  have hρL : L≤ρ := by nlinarith [L_pos]
  have hρr : ρ≤r := by nlinarith [r_pos,r_sq]
  have hz : -1≤L/ρ ∧ L/ρ≤1 := by
    exact ⟨by positivity,(div_le_one hρ0).mpr hρL⟩
  have hθ : 0≤θ ∧ θ<Real.pi/2 :=
    ⟨Real.arctan_nonneg.mpr (div_nonneg hy hA0.le),Real.arctan_lt_pi_div_two _⟩
  have hψ : 0≤ψ := Real.arccos_nonneg _
  have hψφ : ψ≤φ := by
    rw [← arccos_L_div_r]
    apply Real.arccos_le_arccos
    exact div_le_div_of_nonneg_left L_pos.le hρ0 hρr
  obtain ⟨hc,hs⟩ := atan_frame hA0 hy
  have hcosψ : Real.cos ψ=L/ρ := Real.cos_arccos hz.1 hz.2
  refine ⟨add_nonneg hθ.1 hψ,?_,?_⟩
  · change θ+ψ≤2
    linarith [Real.pi_lt_d2,φ_bounds.2.1]
  · change A*Real.cos (θ+ψ)+y*Real.sin (θ+ψ)=L
    rw [Real.cos_add,Real.sin_add]
    have hu := Real.sin_sq_add_cos_sq θ
    have hρprod : ρ*(A*Real.cos θ+y*Real.sin θ)=ρ^2 := by
      nlinarith [hc,hs,hρ₂]
    have htangent : -A*Real.sin θ+y*Real.cos θ=0 := by nlinarith [hc,hs]
    have hnorm : A*Real.cos θ+y*Real.sin θ=ρ := by nlinarith
    have hprod : ρ*Real.cos ψ=L := (eq_div_iff hρ0.ne').mp hcosψ
    nlinarith

theorem E_support {y : ℝ} (hy : 0≤y) (hyr : y≤r) :
    let x := Real.sqrt (radiusSq-y^2)
    0≤E y ∧ E y≤2 ∧ x*Real.cos (E y)+y*Real.sin (E y)=L := by
  let x := Real.sqrt (radiusSq-y^2)
  have hr₂ : r^2=radiusSq := Real.sq_sqrt (by norm_num [radiusSq])
  have hrad : 0≤radiusSq-y^2 := by nlinarith [r_pos]
  have hx₂ : x^2+y^2=radiusSq := by dsimp [x]; nlinarith [Real.sq_sqrt hrad]
  have hx0 : 0≤x := Real.sqrt_nonneg _
  have hydiv : -1≤y/r ∧ y/r≤1 :=
    ⟨by positivity,(div_le_one r_pos).mpr hyr⟩
  let θ := Real.arcsin (y/r)
  have hθ : 0≤θ ∧ θ≤Real.pi/2 :=
    ⟨Real.arcsin_nonneg.mpr (div_nonneg hy r_pos.le),Real.arcsin_le_pi_div_two _⟩
  have hsθ : r*Real.sin θ=y := by
    rw [Real.sin_arcsin hydiv.1 hydiv.2]
    field_simp [ne_of_gt r_pos]
  have hcθ : r*Real.cos θ=x := by
    have hc := Real.cos_nonneg_of_mem_Icc
      (show θ∈Icc (-Real.pi/2) (Real.pi/2) by constructor <;> linarith [hθ.1,hθ.2,Real.pi_pos])
    have hu := congrArg (fun z : ℝ => r^2*z) (Real.sin_sq_add_cos_sq θ)
    nlinarith [congrArg (fun z : ℝ => z^2) hsθ]
  refine ⟨add_nonneg hθ.1 φ_bounds.2.2.1,?_,?_⟩
  · change θ+φ≤2
    linarith [φ_bounds.2.1,Real.pi_lt_d2]
  · change x*Real.cos (θ+φ)+y*Real.sin (θ+φ)=L
    rw [Real.cos_add,Real.sin_add]
    have hp := φ_trig
    have hz : x*Real.cos θ+y*Real.sin θ=r := by nlinarith [hsθ,hcθ,hx₂]
    have ht : -x*Real.sin θ+y*Real.cos θ=0 := by nlinarith [hsθ,hcθ]
    nlinarith

theorem vertical_support {y : ℝ} (hyL : L≤y) (hyr : y≤r) :
    0≤verticalAngle y ∧ verticalAngle y≤2 ∧ y*Real.sin (verticalAngle y)=L := by
  have hy0 : 0<y := L_pos.trans_le hyL
  have hz : -1≤L/y ∧ L/y≤1 :=
    ⟨by positivity,(div_le_one hy0).mpr hyL⟩
  have hp : Real.arccos (L/y)≤φ := by
    rw [← arccos_L_div_r]
    apply Real.arccos_le_arccos
    exact div_le_div_of_nonneg_left L_pos.le hy0 hyr
  refine ⟨by dsimp [verticalAngle]; positivity,?_,?_⟩
  · dsimp [verticalAngle]
    linarith [Real.pi_lt_d2,φ_bounds.2.1]
  · simp only [verticalAngle,Real.sin_add,Real.sin_pi_div_two,Real.cos_pi_div_two,
      one_mul,zero_mul,add_zero,Real.cos_arccos hz.1 hz.2]
    field_simp [hy0.ne']

theorem F_nonneg_le_two {A y : ℝ} (hA : L≤A) (hAr : A<r) (hy : 0≤y) :
    0≤F A y ∧ F A y≤2 := by
  have hA0 := L_pos.trans_le hA
  have hrad : 0≤radiusSq-A^2 := by
    have hr := r_sq
    dsimp [L,c,radiusSq] at *
    nlinarith [r_pos]
  have hk₂ : k A^2=radiusSq-A^2 := Real.sq_sqrt hrad
  unfold F
  split_ifs with h₁ h₂ h₃
  · exact (sideAngle_support hA hy (by nlinarith [Real.sqrt_nonneg (radiusSq-A^2)])).1,
      (sideAngle_support hA hy (by nlinarith [Real.sqrt_nonneg (radiusSq-A^2)])).2.1
  · exact ⟨(E_support hy (h₂.trans r_bounds.1.le)).1,
      (E_support hy (h₂.trans r_bounds.1.le)).2.1⟩
  · exact ⟨(vertical_support (le_of_not_ge h₂).le h₃).1,
      (vertical_support (le_of_not_ge h₂).le h₃).2.1⟩
  · constructor
    · positivity
    · linarith [Real.pi_lt_d2,φ_bounds.2.1]

/-- The complete interval of directions has an actual rectangle intersection. -/
theorem F_forbidden {A y : ℝ} (hA : L≤A) (hAr : A<r) (hy : 0≤y) :
    ∀ β, 0≤β ∧ β≤F A y → ∃ v, |v|≤c ∧
      Rectangle A y (pointInDirection (0,0) (β : Direction) L v) := by
  have hA0 := L_pos.trans_le hA
  have hr₂ : r^2=radiusSq := Real.sq_sqrt (by norm_num [radiusSq])
  have hrad : 0≤radiusSq-A^2 := by nlinarith [r_pos]
  have hk₂ : k A^2=radiusSq-A^2 := Real.sq_sqrt hrad
  by_cases h₁ : y≤k A
  · have hcircle : A^2+y^2≤radiusSq := by
      nlinarith [Real.sqrt_nonneg (radiusSq-A^2)]
    have hs := sideAngle_support hA hy hcircle
    simpa [F,h₁] using rectangle_segment_interval hA
      (show Rectangle A y (A,y) from ⟨hA0.le,le_rfl,hy,le_rfl⟩)
      hcircle ⟨hs.1,hs.2.1⟩ hs.2.2.ge
  by_cases h₂ : y≤L
  · let x := Real.sqrt (radiusSq-y^2)
    have hyr : y≤r := h₂.trans r_bounds.1.le
    have hrad' : 0≤radiusSq-y^2 := by nlinarith [r_pos]
    have hx₂ : x^2=radiusSq-y^2 := Real.sq_sqrt hrad'
    have hx0 : 0≤x := Real.sqrt_nonneg _
    have hxA : x≤A := by nlinarith [lt_of_not_ge h₁,Real.sqrt_nonneg (radiusSq-A^2)]
    have hs := E_support hy hyr
    simpa [F,h₁,h₂] using rectangle_segment_interval hA
      (show Rectangle A y (x,y) from ⟨hx0,hxA,hy,le_rfl⟩)
      (show x^2+y^2≤radiusSq by linarith) ⟨hs.1,hs.2.1⟩ hs.2.2.ge
  by_cases h₃ : y≤r
  · have hs := vertical_support (le_of_not_ge h₂).le h₃
    simpa [F,h₁,h₂,h₃] using rectangle_segment_interval hA
      (show Rectangle A y (0,y) from ⟨le_rfl,hA0.le,hy,le_rfl⟩)
      (show (0 : ℝ)^2+y^2≤radiusSq by nlinarith [r_pos])
      ⟨hs.1,hs.2.1⟩ (by simpa using hs.2.2.ge)
  · have hs := vertical_support r_bounds.1.le le_rfl
    have hangle : verticalAngle r=Real.pi/2+φ := by rw [verticalAngle,arccos_L_div_r]
    rw [hangle] at hs
    simpa [F,h₁,h₂,h₃] using rectangle_segment_interval hA
      (show Rectangle A y (0,r) from ⟨le_rfl,hA0.le,r_pos.le,(lt_of_not_ge h₃).le⟩)
      (show (0 : ℝ)^2+r^2≤radiusSq by nlinarith)
      ⟨hs.1,hs.2.1⟩ (by simpa using hs.2.2.ge)

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
    exact ⟨v,hv,hp.1,hp.2.1,by linarith [hp.2.2.1],hp.2.2.2⟩
  · obtain ⟨v,hv,hp⟩ := F_forbidden hA hAr hd.1 (-β) ⟨by linarith,by linarith [hβ.1]⟩
    refine ⟨-v,by simpa using hv,?_,?_,?_,?_⟩
    all_goals
      dsimp [Rectangle,pointInDirection] at hp ⊢
      simp only [Real.Angle.cos_coe,Real.Angle.sin_coe,Real.cos_neg,Real.sin_neg] at hp ⊢
      nlinarith [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2]

end SquaresInCircles.Eight.CentralForbidden