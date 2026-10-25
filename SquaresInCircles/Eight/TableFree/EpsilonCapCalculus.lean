module

public import SquaresInCircles.Eight.TableFree.EZeroCapEndpoints

/-!
# Primary derivatives of the actual epsilon-zero hard cap

Uncompiled draft.  The primary variable ranges over [.5,1.155] and the
angle over [0,.22].  All radicals are positive on this full rectangle.
The formulas are differentiated directly; later rate bounds are applied
only to the smaller active diagonal-cap rectangle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.EpsilonCapCalculus

def R (x : ℝ) : ℝ := Real.sqrt (qCap-(x+1/2)^2)
def f (x : ℝ) : ℝ := R x-1/2
def ratio (x : ℝ) : ℝ := (x+1/2)/R x
def C (t x : ℝ) : ℝ := 2-R x+Real.cos t
def w (t x : ℝ) : ℝ := Real.sqrt (qCap-(C t x)^2)
def H (t x : ℝ) : ℝ := Real.cos t*w t x-Real.sin t*C t x
def J (t x : ℝ) : ℝ := Real.sin t+Real.cos t*C t x/w t x
def K (t x : ℝ) : ℝ := ratio x*J t x
def Kx (t x : ℝ) : ℝ :=
  Real.cos t*qCap*(ratio x)^2/(w t x)^3+J t x*qCap/(R x)^3
def corner (t x : ℝ) : ℝ := C t x*Real.cos t+w t x*Real.sin t
def drift (t x : ℝ) : ℝ := w t x-Real.sin t
def Jt (t x : ℝ) : ℝ :=
  (H t x*drift t x*w t x-corner t x*C t x*Real.sin t)/(w t x)^3
def Kt (t x : ℝ) : ℝ := ratio x*Jt t x

theorem R_bounds {x : ℝ} (hx : x∈Icc (1/2 : ℝ) (231/200)) :
    (27/25 : ℝ)<R x ∧ R x<171/100 := by
  have ha : 0≤qCap-(x+1/2)^2 := by
    have hs := pow_le_pow_left₀ (show 0≤x+1/2 by linarith [hx.1])
      (show x+1/2≤331/200 by linarith [hx.2]) 2
    dsimp [qCap]
    nlinarith
  have hs := Real.sq_sqrt ha
  have hn := Real.sqrt_nonneg (qCap-(x+1/2)^2)
  have hL := pow_le_pow_left₀ (show (0:ℝ)≤1 by norm_num)
    (show 1≤x+1/2 by linarith [hx.1]) 2
  have hU := pow_le_pow_left₀ (show 0≤x+1/2 by linarith [hx.1])
    (show x+1/2≤331/200 by linarith [hx.2]) 2
  dsimp [R,qCap]
  dsimp [qCap] at hs
  exact ⟨by nlinarith,by nlinarith⟩

theorem R_pos {x : ℝ} (hx : x∈Icc (1/2 : ℝ) (231/200)) : 0<R x :=
  lt_trans (by norm_num) (R_bounds hx).1

theorem R_sq {x : ℝ} (hx : x∈Icc (1/2 : ℝ) (231/200)) :
    (R x)^2=qCap-(x+1/2)^2 := by
  apply Real.sq_sqrt
  have hp := R_pos hx
  exact (Real.sqrt_pos.mp hp).le

theorem C_bounds {t x : ℝ} (ht : t∈Icc 0 (11/50 : ℝ))
    (hx : x∈Icc (1/2 : ℝ) (231/200)) :
    (63/50 : ℝ)<C t x ∧ C t x<48/25 := by
  have hr := R_bounds hx
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have hsq := pow_le_pow_left₀ ht.1 ht.2 2
  have hc1 := Real.cos_le_one t
  dsimp [C]
  constructor <;> nlinarith

theorem C_pos {t x : ℝ} (ht : t∈Icc 0 (11/50 : ℝ))
    (hx : x∈Icc (1/2 : ℝ) (231/200)) : 0<C t x :=
  lt_trans (by norm_num) (C_bounds ht hx).1

theorem w_pos {t x : ℝ} (ht : t∈Icc 0 (11/50 : ℝ))
    (hx : x∈Icc (1/2 : ℝ) (231/200)) : 0<w t x := by
  have hc := C_bounds ht hx
  have hsq := pow_le_pow_left₀ (show 0≤C t x by linarith [hc.1]) hc.2.le 2
  apply Real.sqrt_pos.mpr
  dsimp [qCap]
  nlinarith

theorem w_sq {t x : ℝ} (ht : t∈Icc 0 (11/50 : ℝ))
    (hx : x∈Icc (1/2 : ℝ) (231/200)) :
    (w t x)^2=qCap-(C t x)^2 :=
  Real.sq_sqrt (Real.sqrt_pos.mp (w_pos ht hx)).le

theorem ratio_pos {x : ℝ} (hx : x∈Icc (1/2 : ℝ) (231/200)) : 0<ratio x :=
  div_pos (by linarith [hx.1]) (R_pos hx)

theorem J_pos {t x : ℝ} (ht : t∈Icc 0 (11/50 : ℝ))
    (hx : x∈Icc (1/2 : ℝ) (231/200)) : 0<J t x := by
  have ht' : t∈Icc 0 (7/10 : ℝ) := ⟨ht.1,by linarith [ht.2]⟩
  have hc : 0<Real.cos t := by linarith [(transport_trig ht').1]
  exact add_pos_of_nonneg_of_pos (transport_trig ht').2.2.1
    (div_pos (mul_pos hc (C_pos ht hx)) (w_pos ht hx))

theorem K_pos {t x : ℝ} (ht : t∈Icc 0 (11/50 : ℝ))
    (hx : x∈Icc (1/2 : ℝ) (231/200)) : 0<K t x :=
  mul_pos (ratio_pos hx) (J_pos ht hx)

theorem R_hasDerivAt {x : ℝ} (hx : x∈Icc (1/2 : ℝ) (231/200)) :
    HasDerivAt R (-ratio x) x := by
  have hr : qCap-(x+1/2)^2≠0 := (Real.sqrt_pos.mp (R_pos hx)).ne'
  have hh := ((((hasDerivAt_id x).add_const (1/2)).pow 2).const_sub qCap).sqrt hr
  convert hh using 1
  · rfl
  · dsimp [ratio,R]
    field_simp [(R_pos hx).ne']

theorem f_hasDerivAt {x : ℝ} (hx : x∈Icc (1/2 : ℝ) (231/200)) :
    HasDerivAt f (-ratio x) x := (R_hasDerivAt hx).sub_const (1/2)

theorem ratio_hasDerivAt {x : ℝ} (hx : x∈Icc (1/2 : ℝ) (231/200)) :
    HasDerivAt ratio (qCap/(R x)^3) x := by
  have hh := ((hasDerivAt_id x).add_const (1/2)).div (R_hasDerivAt hx) (R_pos hx).ne'
  convert hh using 1
  · rfl
  · dsimp [ratio]
    rw [show qCap=(R x)^2+(x+1/2)^2 by linarith [R_sq hx]]
    field_simp [(R_pos hx).ne']
    ring

theorem C_x_hasDerivAt {t x : ℝ} (hx : x∈Icc (1/2 : ℝ) (231/200)) :
    HasDerivAt (C t) (ratio x) x := by
  have h := ((R_hasDerivAt hx).const_sub 2).add_const (Real.cos t)
  rw [neg_neg] at h
  exact h

theorem w_x_hasDerivAt {t x : ℝ} (ht : t∈Icc 0 (11/50 : ℝ))
    (hx : x∈Icc (1/2 : ℝ) (231/200)) :
    HasDerivAt (w t) (-C t x*ratio x/w t x) x := by
  have hr : qCap-(C t x)^2≠0 := (Real.sqrt_pos.mp (w_pos ht hx)).ne'
  have hh := (((C_x_hasDerivAt hx).pow 2).const_sub qCap).sqrt hr
  convert hh using 1
  · rfl
  · dsimp [w]
    field_simp [(w_pos ht hx).ne']

theorem H_x_hasDerivAt {t x : ℝ} (ht : t∈Icc 0 (11/50 : ℝ))
    (hx : x∈Icc (1/2 : ℝ) (231/200)) :
    HasDerivAt (H t) (-K t x) x := by
  have hh := ((w_x_hasDerivAt ht hx).const_mul (Real.cos t)).sub
    ((C_x_hasDerivAt (t := t) hx).const_mul (Real.sin t))
  convert hh using 1
  · rfl
  · dsimp [K,J]
    ring

theorem J_x_hasDerivAt {t x : ℝ} (ht : t∈Icc 0 (11/50 : ℝ))
    (hx : x∈Icc (1/2 : ℝ) (231/200)) :
    HasDerivAt (J t) (Real.cos t*qCap*ratio x/(w t x)^3) x := by
  have hh := (((C_x_hasDerivAt (t := t) hx).const_mul (Real.cos t)).div
    (w_x_hasDerivAt ht hx) (w_pos ht hx).ne').const_add (Real.sin t)
  convert hh using 1
  · rfl
  · rw [show qCap=(w t x)^2+(C t x)^2 by linarith [w_sq ht hx]]
    field_simp [(w_pos ht hx).ne']
    ring

theorem K_x_hasDerivAt {t x : ℝ} (ht : t∈Icc 0 (11/50 : ℝ))
    (hx : x∈Icc (1/2 : ℝ) (231/200)) :
    HasDerivAt (K t) (Kx t x) x := by
  convert (ratio_hasDerivAt hx).mul (J_x_hasDerivAt ht hx) using 1
  · rfl
  · dsimp [Kx]
    ring

theorem Kx_pos {t x : ℝ} (ht : t∈Icc 0 (11/50 : ℝ))
    (hx : x∈Icc (1/2 : ℝ) (231/200)) : 0<Kx t x := by
  have hc : 0<Real.cos t := by
    linarith [(transport_trig (show t∈Icc 0 (7/10 : ℝ) from ⟨ht.1,by linarith [ht.2]⟩)).1]
  have hq : 0<qCap := by norm_num [qCap]
  exact add_pos (div_pos (mul_pos (mul_pos hc hq) (sq_pos_of_pos (ratio_pos hx)))
    (pow_pos (w_pos ht hx) 3))
    (div_pos (mul_pos (J_pos ht hx) hq) (pow_pos (R_pos hx) 3))

theorem C_t_hasDerivAt (t x : ℝ) :
    HasDerivAt (fun z => C z x) (-Real.sin t) t :=
  (Real.hasDerivAt_cos t).const_add (2-R x)

theorem w_t_hasDerivAt {t x : ℝ} (ht : t∈Icc 0 (11/50 : ℝ))
    (hx : x∈Icc (1/2 : ℝ) (231/200)) :
    HasDerivAt (fun z => w z x) (C t x*Real.sin t/w t x) t := by
  have hr : qCap-(C t x)^2≠0 := (Real.sqrt_pos.mp (w_pos ht hx)).ne'
  have hh := (((C_t_hasDerivAt t x).pow 2).const_sub qCap).sqrt hr
  convert hh using 1
  · rfl
  · dsimp [w]
    field_simp [(w_pos ht hx).ne']

theorem J_t_hasDerivAt {t x : ℝ} (ht : t∈Icc 0 (11/50 : ℝ))
    (hx : x∈Icc (1/2 : ℝ) (231/200)) :
    HasDerivAt (fun z => J z x) (Jt t x) t := by
  have hh := (Real.hasDerivAt_sin t).add
    (((Real.hasDerivAt_cos t).mul (C_t_hasDerivAt t x)).div
      (w_t_hasDerivAt ht hx) (w_pos ht hx).ne')
  convert hh using 1
  · rfl
  · dsimp [Jt,H,corner,drift]
    field_simp [(w_pos ht hx).ne']
    ring

theorem K_t_hasDerivAt {t x : ℝ} (ht : t∈Icc 0 (11/50 : ℝ))
    (hx : x∈Icc (1/2 : ℝ) (231/200)) :
    HasDerivAt (fun z => K z x) (Kt t x) t :=
  (J_t_hasDerivAt ht hx).const_mul (ratio x)

theorem H_antitone {t : ℝ} (ht : t∈Icc 0 (11/50 : ℝ)) :
    AntitoneOn (H t) (Icc (1/2 : ℝ) (231/200)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x hx => (H_x_hasDerivAt ht hx).continuousAt.continuousWithinAt
  · exact fun x hx => H_x_hasDerivAt ht (Ioo_subset_Icc_self hx)
  · exact fun x hx => neg_nonpos.mpr (K_pos ht (Ioo_subset_Icc_self hx)).le

theorem f_antitone : AntitoneOn f (Icc (1/2 : ℝ) (231/200)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x hx => (f_hasDerivAt hx).continuousAt.continuousWithinAt
  · exact fun x hx => f_hasDerivAt (Ioo_subset_Icc_self hx)
  · exact fun x hx => neg_nonpos.mpr (ratio_pos (Ioo_subset_Icc_self hx)).le

theorem K_monotone {t : ℝ} (ht : t∈Icc 0 (11/50 : ℝ)) :
    MonotoneOn (K t) (Icc (1/2 : ℝ) (231/200)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x hx => (K_x_hasDerivAt ht hx).continuousAt.continuousWithinAt
  · exact fun x hx => K_x_hasDerivAt ht (Ioo_subset_Icc_self hx)
  · exact fun x hx => (Kx_pos ht (Ioo_subset_Icc_self hx)).le

theorem cap_eq (t x : ℝ) : H t x=HardSplitCap.cap qCap (3/2-f x) t := by
  have he : (3/2 : ℝ)-(R x-1/2)+Real.cos t=2-R x+Real.cos t := by ring
  simp only [H,HardSplitCap.cap,HardSplitCap.root,HardSplitCap.contact,w,C,f,he]

end SquaresInCircles.Eight.TableFree.EpsilonCapCalculus
