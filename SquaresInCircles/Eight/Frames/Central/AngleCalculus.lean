module

public import SquaresInCircles.Eight.Frames.Central.Segment

/-!
# Eight squares: the four exact branches of the forbidden-direction endpoint

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