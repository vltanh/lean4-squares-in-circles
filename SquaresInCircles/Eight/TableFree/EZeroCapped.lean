module

public import SquaresInCircles.Eight.TableFree.EZeroScalar

/-!
# The intrinsic cap reduction for the full E-zero scalar

Uncompiled draft.  The only angular cut is the unique geometric crossing
of the increasing endpoint bound with the diagonal circle cap.  Each
variable is moved down to that crossing only in a scalar majorant.  No
replacement square or physical contact is asserted by this comparison.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.EZeroCapped
open EZeroFunctions EZeroNested EZeroHessian

def W (e : ℝ) : ℝ := Real.sqrt (qCap-(5/2-capped e)^2)
def Yc (e : ℝ) : ℝ := 2-W e
def Xc (e : ℝ) : ℝ := Real.sqrt (qCap-(Yc e)^2)-1
def Fc (e d : ℝ) : ℝ := capped d+Xc e*Real.cos (e+d)-Yc e*Real.sin (e+d)

theorem diagonal_bounds : (79/100 : ℝ)<diagonalCoordinate qCap ∧
    diagonalCoordinate qCap<9/10 := by
  have hs := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
  have hn := Real.sqrt_nonneg (qCap/2)
  dsimp [diagonalCoordinate,qCap]
  constructor <;> nlinarith

theorem crossing : ∃c∈Ioo (0:ℝ) (11/100),h c=diagonalCoordinate qCap := by
  have h0 : h 0<diagonalCoordinate qCap := by
    have hr := rho_sq (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
    have hp := rho_pos (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
    have hs := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
    have hn := Real.sqrt_nonneg (qCap/2)
    norm_num [u,qCap] at hr
    dsimp [h,diagonalCoordinate,qCap]
    nlinarith
  have h1 : diagonalCoordinate qCap<h (11/100) := by
    have ht : (11/100 : ℝ)∈Icc 0 (7/10) := by norm_num
    have hp := uj_bounds ht
    have hb := trig_bracket (l := (11/100 : ℝ)) (u := (11/100 : ℝ))
      (by norm_num) (by linarith [Real.pi_gt_three]) (by constructor <;> rfl)
    have hv := v_bounds
    have hmul := mul_le_mul (show (1829/2000 : ℝ)≤v by linarith) hb.1
      (by norm_num : (0:ℝ)≤11/100-(11/100)^3/6) (by linarith : 0≤v)
    have hu : u (11/100)<1397/1000 := by
      dsimp [u]
      norm_num at hb hmul
      linarith [hb.2.2.2]
    have hu2 := pow_le_pow_left₀ hp.1.le hu.le 2
    have hr := rho_sq ht
    have hrp := rho_pos ht
    have hs := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
    have hn := Real.sqrt_nonneg (qCap/2)
    dsimp [h,diagonalCoordinate,qCap] at *
    nlinarith
  have hc : ContinuousOn h (Icc (0:ℝ) (11/100)) := fun t ht =>
    (h_hasDerivAt ⟨ht.1,by linarith [ht.2]⟩).continuousAt.continuousWithinAt
  obtain ⟨c,hc',heq⟩ := intermediate_value_Icc (show (0:ℝ)≤11/100 by norm_num) hc
    (show diagonalCoordinate qCap∈Icc (h 0) (h (11/100)) from ⟨h0.le,h1.le⟩)
  refine ⟨c,⟨?_,?_⟩,heq⟩
  · apply lt_of_le_of_ne hc'.1
    intro hz
    rw [← hz] at heq
    linarith
  · apply lt_of_le_of_ne hc'.2
    intro hz
    rw [hz] at heq
    linarith

theorem clipped_representation {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) :
    ∃x∈Icc (0:ℝ) (11/100),x≤t ∧ capped t=h x ∧
      W t=w x ∧ Yc t=Y x ∧ Xc t=X x := by
  obtain ⟨c,hc,heq⟩ := crossing
  let x := min t c
  have hc' : c∈Icc (0:ℝ) (7/10) := ⟨hc.1.le,by linarith [hc.2]⟩
  have hx : x∈Icc (0:ℝ) (11/100) :=
    ⟨le_min ht.1 hc.1.le,(min_le_right _ _).trans hc.2.le⟩
  have hcap : capped t=h x := by
    by_cases htc : t≤c
    · have hm := h_monotone ht hc' htc
      rw [heq] at hm
      simp [capped,x,min_eq_left htc,min_eq_right hm]
    · have hm := h_monotone hc' ht (le_of_not_ge htc)
      rw [heq] at hm
      simp [capped,x,min_eq_right (le_of_not_ge htc),min_eq_left hm,heq]
  refine ⟨x,hx,min_le_left _ _,hcap,?_,?_,?_⟩ <;>
    simp [W,Yc,Xc,w,Y,X,A,r,hcap]

theorem nested_bounds {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) :
    (199/200 : ℝ)<W t ∧ W t<117/100 ∧
      (83/100 : ℝ)<Yc t ∧ Yc t<101/100 ∧
      (7/10 : ℝ)<Xc t ∧ Xc t<4/5 := by
  obtain ⟨x,hx,hxt,hcap,hw,hy,hX⟩ := clipped_representation ht
  have hb := bounds hx
  rw [hw,hy,hX]
  exact ⟨hb.w_bounds.1,hb.w_bounds.2,hb.Y_bounds.1,hb.Y_bounds.2,
    hb.X_bounds.1,hb.X_bounds.2⟩

theorem W_sq {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) :
    (W t)^2=qCap-(5/2-capped t)^2 := by
  obtain ⟨x,hx,hxt,hcap,hw,hy,hX⟩ := clipped_representation ht
  rw [hw,hcap]
  simpa [A] using w_sq hx

theorem corner_square {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) :
    (Xc t+1)^2+(Yc t)^2=qCap := by
  obtain ⟨x,hx,hxt,hcap,hw,hy,hX⟩ := clipped_representation ht
  rw [hy,hX]
  dsimp [X]
  nlinarith [r_sq hx]

theorem capped_bounds {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) :
    (79/100 : ℝ)<capped t ∧ capped t<9/10 := by
  obtain ⟨x,hx,hxt,hcap,_,_,_⟩ := clipped_representation ht
  refine ⟨by rw [hcap]; exact (small_h hx).1,?_⟩
  exact (min_le_left _ _).trans_lt diagonal_bounds.2

theorem maximum {e d : ℝ} (he : 0≤e) (hd : 0≤d) (ha : e+d≤7/10) :
    Fc e d<(1499702/1000000 : ℝ) := by
  have he' : e∈Icc 0 (7/10 : ℝ) := ⟨he,by linarith⟩
  have hd' : d∈Icc 0 (7/10 : ℝ) := ⟨hd,by linarith⟩
  obtain ⟨x,hx,hxe,hce,hw,hy,hX⟩ := clipped_representation he'
  obtain ⟨y,hy',hyd,hcd,_,_,_⟩ := clipped_representation hd'
  have hb := bounds hx
  have hsum : x+y≤e+d := add_le_add hxe hyd
  have hxy : 0≤x+y := add_nonneg hx.1 hy'.1
  have hcos : Real.cos (e+d)≤Real.cos (x+y) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hxy (by linarith [Real.pi_gt_three]) hsum
  have hsin : Real.sin (x+y)≤Real.sin (e+d) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_gt_three])
      (by linarith [Real.pi_gt_three]) hsum
  have hcx := mul_le_mul_of_nonneg_left hcos (show 0≤X x by linarith [hb.X_bounds.1])
  have hsy := mul_le_mul_of_nonneg_left hsin (show 0≤Y x by linarith [hb.Y_bounds.1])
  have hbound : Fc e d≤F x y := by
    dsimp [Fc,F]
    rw [hcd,hy,hX]
    linarith
  exact hbound.trans_lt (EZeroScalar.maximum hx hy')

end SquaresInCircles.Eight.TableFree.EZeroCapped
