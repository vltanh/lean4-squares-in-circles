module

public import SquaresInCircles.Eight.TableFree.CentralAngleCalculus

/-!
# Fixed endpoint estimates for the continuous forbidden-width proof

Uncompiled draft. These are Taylor inequalities at the three geometric
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
    (by fun_prop) (by norm_num [C8]) (fun t ht => by
      have hd : HasDerivAt (fun z => C8 z-Real.cos z)
          ((t-t^3/6+t^5/120-t^7/5040)*(-1)+Real.sin t) t := by
        convert (by fun_prop : DifferentiableAt ℝ (fun z => C8 z-Real.cos z) t).hasDerivAt using 1
        simp [C8]
        ring
      have hs := sin_lower_seven ht
      simp [C8] at hd
      rw [hd.deriv]
      linarith) hx
  linarith

theorem sin_le_S9 {x : ℝ} (hx : 0≤x) : Real.sin x≤S9 x := by
  have h := nonneg_of_deriv_nonneg (fun t => S9 t-Real.sin t)
    (by fun_prop) (by norm_num [S9]) (fun t ht => by
      simp (disch := fun_prop) [S9]
      have hh := cos_le_C8 ht
      dsimp [C8] at hh
      linarith) hx
  linarith

theorem C10_le_cos {x : ℝ} (hx : 0≤x) : C10 x≤Real.cos x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.cos t-C10 t)
    (by fun_prop) (by norm_num [C10,C8]) (fun t ht => by
      simp (disch := fun_prop) [C10,C8]
      have hh := sin_le_S9 ht
      dsimp [S9] at hh
      linarith) hx
  linarith

def inverseArc (x : ℝ) : ℝ := L*Real.sin x-c*Real.cos x

theorem inverseArc_mono : MonotoneOn inverseArc (Icc 0 (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg (by fun_prop)
    (d := fun x => L*Real.cos x+c*Real.sin x)
  · intro x hx
    convert ((Real.hasDerivAt_sin x).const_mul L).sub
      ((Real.hasDerivAt_cos x).const_mul c) using 1 <;> dsimp [inverseArc] <;> ring
  · intro x hx
    have ht := cos_sin_nonneg (show 0≤x ∧ x≤Real.pi/2 from ⟨hx.1.le,hx.2.le⟩)
    exact add_nonneg (mul_nonneg L_pos.le ht.1) (mul_nonneg c_pos.le ht.2)

theorem inverseArc_E {y : ℝ} (hy : 0≤y) (hyL : y≤L) :
    inverseArc (E y)=y := by
  have hyr : y≤r := hyL.trans r_bounds.1.le
  have hdiv : -1≤y/r ∧ y/r≤1 :=
    ⟨by positivity,(div_le_one r_pos).mpr hyr⟩
  have hs : r*Real.sin (Real.arcsin (y/r))=y := by
    rw [Real.sin_arcsin hdiv.1 hdiv.2]
    field_simp [r_pos.ne']
  have hφ := φ_trig
  have hr := r_sq
  have hscaled : r*inverseArc (E y)=r*y := by
    dsimp [inverseArc,E]
    rw [Real.sin_add,Real.cos_add]
    have hcross : L*Real.sin φ-c*Real.cos φ=0 := by
      nlinarith [hφ.1,hφ.2,r_pos]
    have hrad : L*Real.cos φ+c*Real.sin φ=r := by
      nlinarith [hφ.1,hφ.2,hr,r_pos]
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
    norm_num [L] at h
    linarith
  · have h := atan_cubic_lower (show (0:ℝ)≤1/11 by norm_num)
    norm_num at h
    linarith

def widthPolynomial (d : ℝ) : ℝ :=
  d^4+6*L^2*d^2-8*L^2*d+4*L^2-3*L^4-4*L^2*c^2

def widthPolynomialDeriv (d : ℝ) : ℝ := 4*d^3+12*L^2*d-8*L^2

theorem widthPolynomial_hasDeriv (d : ℝ) :
    HasDerivAt widthPolynomial (widthPolynomialDeriv d) d := by
  unfold widthPolynomial widthPolynomialDeriv
  convert (((((hasDerivAt_id d).pow 4).add
    (((hasDerivAt_id d).pow 2).const_mul (6*L^2))).sub
    ((hasDerivAt_id d).const_mul (8*L^2))).add_const (4*L^2)).sub_const
      (3*L^4) |>.sub_const (4*L^2*c^2) using 1 <;> ring

theorem widthPolynomial_deriv_negative {d : ℝ} (hd : 0≤d ∧ d≤c) :
    widthPolynomialDeriv d<0 := by
  have hpow := pow_le_pow_left₀ hd.1 hd.2 3
  have hlin := mul_le_mul_of_nonneg_left hd.2 (show 0≤12*L^2 by positivity)
  dsimp [widthPolynomialDeriv,L,c] at *
  norm_num at *
  linarith

theorem widthPolynomial_antitone : AntitoneOn widthPolynomial (Icc 0 c) :=
  antiOn_of_hasDeriv_nonpos (by fun_prop) (fun d _ => widthPolynomial_hasDeriv d)
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
    (hy : 0≤y) (hrad : A^2+y^2≤radiusSq)
    (hx : Real.arctan (y/A)≤x ∧ x≤Real.pi)
    (hs : L<A*Real.cos x+y*Real.sin x) : x<sideAngle A y := by
  have hA0 := L_pos.trans_le hA
  let N := Real.sqrt (A^2+y^2)
  let θ := Real.arctan (y/A)
  let ψ := Real.arccos (L/N)
  have hN : 0<N := Real.sqrt_pos.mpr (by nlinarith)
  have hN₂ : N^2=A^2+y^2 := Real.sq_sqrt (by positivity)
  have hNL : L≤N := by nlinarith [L_pos]
  have hθ0 : 0≤θ := Real.arctan_nonneg.mpr (div_nonneg hy hA0.le)
  have hψ0 : 0≤ψ := Real.arccos_nonneg _
  have hcosψ : Real.cos ψ=L/N := Real.cos_arccos
    (by positivity) ((div_le_one hN).mpr hNL)
  obtain ⟨hc,hsin⟩ := atan_frame hA0 hy
  have hrot : N*Real.cos (x-θ)=A*Real.cos x+y*Real.sin x := by
    rw [Real.cos_sub]
    nlinarith [hc,hsin]
  by_contra! hbad
  have hbad' : ψ≤x-θ := by change x≥θ+ψ at hbad; linarith
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi hψ0
    (show x-θ≤Real.pi by linarith [hx.2]) hbad'
  have hprod := mul_le_mul_of_nonneg_left hm hN.le
  rw [hrot,hcosψ] at hprod
  have he : N*(L/N)=L := by field_simp [hN.ne']
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
    · have hc := cos_lower_two (show (0:ℝ)≤1/4 by norm_num)
      dsimp [L]
      nlinarith
  · apply sideAngle_gt_of_support
    · norm_num [L]
    · norm_num
    · norm_num [radiusSq]
    · constructor
      · have ha := atan_upper (show (0:ℝ)≤(1/12)/(19/20) by norm_num)
        norm_num at ha
        linarith
      · linarith [Real.pi_gt_d2]
    · have hc := cos_lower_two (show (0:ℝ)≤9/25 by norm_num)
      have hs := sin_lower_three (show (0:ℝ)≤9/25 by norm_num)
      dsimp [L]
      nlinarith

end SquaresInCircles.Eight.CentralForbidden