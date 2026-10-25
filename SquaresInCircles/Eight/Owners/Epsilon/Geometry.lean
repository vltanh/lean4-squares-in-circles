module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.E.ZeroCapEndpoints
public import SquaresInCircles.Eight.Owners.E.ZeroHessian
public import SquaresInCircles.Eight.Owners.Endpoint.Principles
public import SquaresInCircles.Eight.Owners.Hard.SplitCycle
public import SquaresInCircles.Eight.Owners.Ordered.CancelingSplit
public import SquaresInCircles.Eight.Words.Aligned.CycleBounds

/-!
# Eight squares: E cannot share H's frame in the actual aligned hard chain

The original EH axis bounds H's primary coordinate by
the original E tangent.  The original E circle then supplies D's primary
bound through DE3.  Both actual middle circles lie below the corresponding
hard caps.  The same-radius split and the scalar monotonicity theorem
exclude both endpoint choices, without reflecting E or discarding its
original circle slack.
-/

section
/-!
## Primary derivatives of the actual epsilon-zero hard cap

The primary variable ranges over [.5,1.155] and the
angle over [0,.22].  All radicals are positive on this full rectangle.
The formulas are differentiated directly; later rate bounds are applied
only to the smaller active diagonal-cap rectangle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EpsilonCapCalculus

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

end SquaresInCircles.Eight.EpsilonCapCalculus
end
end
end

section
/-!
## The primary loss dominates angular gain on the active epsilon-zero arc

The primary variable ranges continuously from the
diagonal coordinate to one and the angle from zero to .11.  The actual
cap derivatives satisfy K_x>4 and 0<K_theta<1.2 throughout this rectangle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EpsilonActiveRates
open EpsilonCapCalculus

theorem diagonal_bounds : (899/1000 : ℝ)<diagonalCoordinate qCap ∧
    diagonalCoordinate qCap<9/10 := by
  have hs := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
  have hn := Real.sqrt_nonneg (qCap/2)
  dsimp [diagonalCoordinate,qCap]
  constructor <;> nlinarith

theorem primary_mem {x : ℝ} (hx : x∈Icc (diagonalCoordinate qCap) 1) :
    x∈Icc (1/2 : ℝ) (231/200) :=
  ⟨by linarith [hx.1,diagonal_bounds.1],by linarith [hx.2]⟩

structure Bounds (t x : ℝ) : Prop where
  cos_lower : (19879/20000 : ℝ)<Real.cos t
  sin_bounds : Real.sin t∈Icc 0 (11/100 : ℝ)
  R_bounds : R x∈Ioo (129/100 : ℝ) (7/5)
  ratio_bounds : 1≤ratio x ∧ ratio x<6/5
  C_bounds : C t x∈Ioo (159/100 : ℝ) (171/100)
  w_bounds : w t x∈Ioo (199/200 : ℝ) (6/5)
  H_bounds : (4/5 : ℝ)<H t x ∧ H t x≤w t x
  corner_bounds : 0<corner t x ∧ corner t x<2
  drift_bounds : (22/25 : ℝ)<drift t x ∧ drift t x≤w t x

theorem bounds {t x : ℝ} (ht : t∈Icc 0 (11/100 : ℝ))
    (hx : x∈Icc (diagonalCoordinate qCap) 1) : Bounds t x := by
  have ht' : t∈Icc 0 (11/50 : ℝ) := ⟨ht.1,by linarith [ht.2]⟩
  have hx' := primary_mem hx
  have hrp := R_pos hx'
  have hrs := R_sq hx'
  have hwp := w_pos ht' hx'
  have hws := w_sq ht' hx'
  have hdq := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
  have hdn := Real.sqrt_nonneg (qCap/2)
  have hxx : Real.sqrt (qCap/2)≤x+1/2 := by
    dsimp [diagonalCoordinate] at hx
    linarith [hx.1]
  have hxlo := pow_le_pow_left₀ hdn hxx 2
  have hxhi := pow_le_pow_left₀ (show 0≤x+1/2 by linarith [hx'.1])
    (show x+1/2≤3/2 by linarith [hx.2]) 2
  have hR : R x∈Ioo (129/100 : ℝ) (7/5) := by
    show (129/100 : ℝ)<Real.sqrt (qCap-(x+1/2)^2) ∧ Real.sqrt (qCap-(x+1/2)^2)<7/5
    have h1 : (9789/2500:ℝ)/2≤(x+1/2)^2 := by rw [← hdq]; exact hxlo
    constructor
    · exact (Real.lt_sqrt (by norm_num)).2 (by norm_num [qCap]; linarith)
    · exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num [qCap]; linarith)
  have hratio : 1≤ratio x ∧ ratio x<6/5 := by
    dsimp [ratio]
    constructor
    · apply (le_div_iff₀ hrp).2
      have h1 : qCap-(x+1/2)^2≤(x+1/2)^2 := by linarith
      calc 1*R x = Real.sqrt (qCap-(x+1/2)^2) := one_mul _
        _ ≤ Real.sqrt ((x+1/2)^2) := Real.sqrt_le_sqrt h1
        _ = x+1/2 := Real.sqrt_sq (by linarith [hx'.1])
    · apply (div_lt_iff₀ hrp).2
      linarith [hR.1,hx.2]
  have hcos : (19879/20000 : ℝ)<Real.cos t := by
    have hs := pow_le_pow_left₀ ht.1 ht.2 2
    have hc := Real.one_sub_sq_div_two_le_cos (x := t)
    by_cases hz : t=11/100
    · subst t
      have hb := cos_lower_six (show (0:ℝ)≤11/100 by norm_num)
      norm_num at hb
      linarith
    · have hlt : t<11/100 := lt_of_le_of_ne ht.2 hz
      have hsq : t^2<(11/100 : ℝ)^2 := by
        have hp := mul_pos (sub_pos.mpr hlt) (show (0:ℝ)<11/100+t by linarith [ht.1])
        nlinarith
      linarith
  have hsin : Real.sin t∈Icc 0 (11/100 : ℝ) :=
    ⟨Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2,Real.pi_gt_three]),
      (Real.sin_le ht.1).trans ht.2⟩
  have hc1 := Real.cos_le_one t
  have hC : C t x∈Ioo (159/100 : ℝ) (171/100) := by
    dsimp [C]
    exact ⟨by linarith [hR.2],by linarith [hR.1]⟩
  have hClo := pow_le_pow_left₀ (show (0:ℝ)≤159/100 by norm_num) hC.1.le 2
  have hChi := pow_le_pow_left₀ (show 0≤C t x by linarith [hC.1]) hC.2.le 2
  have hw : w t x∈Ioo (199/200 : ℝ) (6/5) := by
    show (199/200 : ℝ)<Real.sqrt (qCap-(C t x)^2) ∧ Real.sqrt (qCap-(C t x)^2)<6/5
    constructor
    · exact (Real.lt_sqrt (by norm_num)).2 (by norm_num [qCap]; linarith)
    · exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num [qCap]; linarith)
  have hH : (4/5 : ℝ)<H t x ∧ H t x≤w t x := by
    have hcw := mul_lt_mul_of_pos_right hcos hwp
    have hcw' := mul_lt_mul_of_pos_left hw.1 (show (0:ℝ)<19879/20000 by norm_num)
    have hsc := mul_le_mul hsin.2 hC.2.le (show 0≤C t x by linarith [hC.1]) (by norm_num)
    have hcwU := mul_le_mul_of_nonneg_right hc1 hwp.le
    have hsc0 := mul_nonneg hsin.1 (show 0≤C t x by linarith [hC.1])
    dsimp [H]
    exact ⟨by linarith,by linarith⟩
  have hcpos : 0<corner t x := add_pos_of_pos_of_nonneg
    (mul_pos (show 0<C t x by linarith [hC.1]) (show 0<Real.cos t by linarith))
    (mul_nonneg hwp.le hsin.1)
  have hnorm : (corner t x)^2+(H t x)^2=qCap := by
    calc
      (corner t x)^2+(H t x)^2=
          ((Real.sin t)^2+(Real.cos t)^2)*((C t x)^2+(w t x)^2) := by
        dsimp [corner,H]
        ring
      _ = qCap := by rw [Real.sin_sq_add_cos_sq,one_mul,hws]; ring
  have hcorner : corner t x<2 := by
    by_contra! h2
    have h4 := mul_le_mul h2 h2 (by norm_num) (by linarith)
    have hH2 := sq_nonneg (H t x)
    have hQ : qCap<4 := by norm_num [qCap]
    generalize qCap = Q at hnorm hQ
    linarith
  refine ⟨hcos,hsin,hR,hratio,hC,hw,hH,⟨hcpos,hcorner⟩,?_⟩
  dsimp [drift]
  exact ⟨by linarith [hw.1,hsin.2],by linarith [hsin.1]⟩


theorem Kx_lower {t x : ℝ} (ht : t∈Icc 0 (11/100 : ℝ))
    (hx : x∈Icc (diagonalCoordinate qCap) 1) : (4:ℝ)<Kx t x := by
  have hb := bounds ht hx
  have hp := w_pos (show t∈Icc 0 (11/50 : ℝ) from ⟨ht.1,by linarith [ht.2]⟩) (primary_mem hx)
  have hR := R_pos (primary_mem hx)
  have hratio2 : 1≤(ratio x)^2 := by nlinarith [sq_nonneg (ratio x-1),hb.ratio_bounds.1]
  have hcq : (99/100 : ℝ)*(39/10)<Real.cos t*qCap := by
    dsimp [qCap]
    linarith [hb.cos_lower]
  have hcqp : 0≤Real.cos t*qCap := by
    exact mul_nonneg (by linarith [hb.cos_lower]) (by norm_num [qCap])
  have hnum := mul_le_mul_of_nonneg_left hratio2 hcqp
  have hw3 := pow_lt_pow_left₀ hb.w_bounds.2 hp.le (by decide : (3:ℕ)≠0)
  have hfirst : (99/100 : ℝ)*(39/10)/(6/5)^3<
      Real.cos t*qCap*(ratio x)^2/(w t x)^3 := by
    apply (lt_div_iff₀ (pow_pos hp 3)).2
    have hh := mul_lt_mul_of_pos_left hw3 (show (0:ℝ)<(99/100)*(39/10)/(6/5)^3 by norm_num)
    norm_num at hh
    nlinarith
  have hCratio : (53/40 : ℝ)<C t x/w t x :=
    (lt_div_iff₀ hp).2 (by linarith [hb.C_bounds.1,hb.w_bounds.2])
  have hJ : (5247/4000 : ℝ)<J t x := by
    have hmul := mul_lt_mul_of_pos_left hCratio (show 0<Real.cos t by linarith [hb.cos_lower])
    dsimp [J]
    rw [mul_div_assoc]
    nlinarith [hb.sin_bounds.1,hb.cos_lower]
  have hR3 := pow_lt_pow_left₀ hb.R_bounds.2 hR.le (by decide : (3:ℕ)≠0)
  have hsecond : (5247/4000 : ℝ)*(39/10)/(7/5)^3<J t x*qCap/(R x)^3 := by
    apply (lt_div_iff₀ (pow_pos hR 3)).2
    have hh := mul_lt_mul_of_pos_left hR3 (show (0:ℝ)<(5247/4000)*(39/10)/(7/5)^3 by norm_num)
    have hn : (5247/4000 : ℝ)*(39/10)<J t x*qCap := by
      dsimp [qCap]
      linarith
    norm_num at hh
    linarith
  have hsum : (4:ℝ)<(99/100)*(39/10)/(6/5)^3+(5247/4000)*(39/10)/(7/5)^3 := by
    norm_num
  dsimp [Kx]
  linarith


theorem Jt_bounds {t x : ℝ} (ht : t∈Icc 0 (11/100 : ℝ))
    (hx : x∈Icc (diagonalCoordinate qCap) 1) : 0<Jt t x ∧ Jt t x≤1 := by
  have hb := bounds ht hx
  have hwp : 0<w t x := by linarith [hb.w_bounds.1]
  have hdp : 0<drift t x := by linarith [hb.drift_bounds.1]
  have hHp : 0<H t x := by linarith [hb.H_bounds.1]
  have hCp : 0<C t x := by linarith [hb.C_bounds.1]
  have hleft : (4/5 : ℝ)*(22/25)*(99/100)<H t x*drift t x*w t x := by
    have h1 := mul_lt_mul_of_pos_right hb.H_bounds.1 hdp
    have h2 := mul_lt_mul_of_pos_left hb.drift_bounds.1 (show (0:ℝ)<4/5 by norm_num)
    have h3 := mul_lt_mul_of_pos_right (lt_trans h2 h1) hwp
    nlinarith [hb.w_bounds.1]
  have hright : corner t x*C t x*Real.sin t≤(2:ℝ)*(171/100)*(11/100) := by
    have h1 := mul_le_mul hb.corner_bounds.2.le hb.C_bounds.2.le hCp.le (by norm_num)
    exact mul_le_mul h1 hb.sin_bounds.2 hb.sin_bounds.1 (by norm_num)
  have hright0 : 0≤corner t x*C t x*Real.sin t :=
    mul_nonneg (mul_nonneg hb.corner_bounds.1.le hCp.le) hb.sin_bounds.1
  have hleftU : H t x*drift t x*w t x≤(w t x)^3 := by
    have h1 := mul_le_mul hb.H_bounds.2 hb.drift_bounds.2 hdp.le hwp.le
    have h2 := mul_le_mul_of_nonneg_right h1 hwp.le
    nlinarith
  dsimp [Jt]
  exact ⟨div_pos (by nlinarith) (pow_pos hwp 3),
    (div_le_one (pow_pos hwp 3)).2 (by linarith)⟩

theorem Kt_bounds {t x : ℝ} (ht : t∈Icc 0 (11/100 : ℝ))
    (hx : x∈Icc (diagonalCoordinate qCap) 1) : 0<Kt t x ∧ Kt t x<6/5 := by
  have hr := (bounds ht hx).ratio_bounds
  have hj := Jt_bounds ht hx
  have hp : 0<ratio x := by linarith
  have hu := mul_le_mul_of_nonneg_left hj.2 hp.le
  exact ⟨mul_pos hp hj.1,by dsimp [Kt]; nlinarith⟩

theorem primary_growth {t x y : ℝ} (ht : t∈Icc 0 (11/100 : ℝ))
    (hx : x∈Icc (diagonalCoordinate qCap) 1)
    (hy : y∈Icc (diagonalCoordinate qCap) 1) (hxy : x≤y) :
    4*(y-x)≤K t y-K t x := by
  have ht' : t∈Icc 0 (11/50 : ℝ) := ⟨ht.1,by linarith [ht.2]⟩
  exact derivative_reserve
    (fun z hz => (K_x_hasDerivAt ht' (primary_mem hz)).continuousAt.continuousWithinAt)
    (fun z hz => K_x_hasDerivAt ht' (primary_mem (Ioo_subset_Icc_self hz)))
    (fun z hz => (Kx_lower ht (Ioo_subset_Icc_self hz)).le) hx hy hxy

theorem angular_growth {t x : ℝ} (ht : t∈Icc 0 (11/100 : ℝ))
    (hx : x∈Icc (diagonalCoordinate qCap) 1) :
    K 0 x≤K t x ∧ K t x-K 0 x≤(6/5)*t := by
  have hder (z : ℝ) (hz : z∈Icc 0 (11/100 : ℝ)) :=
    K_t_hasDerivAt (show z∈Icc 0 (11/50 : ℝ) from ⟨hz.1,by linarith [hz.2]⟩) (primary_mem hx)
  have hmono : MonotoneOn (fun z => K z x) (Icc 0 (11/100 : ℝ)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z hz => (hder z hz).continuousAt.continuousWithinAt
    · exact fun z hz => hder z (Ioo_subset_Icc_self hz)
    · exact fun z hz => (Kt_bounds (Ioo_subset_Icc_self hz) hx).1.le
  have hupper := derivative_reserve
    (f := fun z => -K z x) (df := fun z => -Kt z x) (k := -(6/5 : ℝ))
    (fun z hz => (hder z hz).neg.continuousAt.continuousWithinAt)
    (fun z hz => (hder z (Ioo_subset_Icc_self hz)).neg)
    (fun z hz => by linarith [(Kt_bounds (Ioo_subset_Icc_self hz) hx).2])
    (show (0:ℝ)∈Icc 0 (11/100) by norm_num) ht ht.1
  exact ⟨hmono (by norm_num) ht ht.1,by linarith⟩

end SquaresInCircles.Eight.EpsilonActiveRates
end
end
end

section
/-!
## The original E transverse parameter and the active cap comparison

The scalar g is computed from the same original E
circle at every tangent b.  Its decrease is bounded between zero and one.
If D's diagonal cap is inactive, the actual total angle is below .11 and
the primary K reserve dominates the angular K gain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EpsilonTangent
open EpsilonCapCalculus

def g (a b : ℝ) : ℝ := (1+Real.cos a+Real.sin a)/2-EpsilonCapCalculus.f b*Real.sin a-b*Real.cos a
def decrease (a b : ℝ) : ℝ := Real.cos a-ratio b*Real.sin a

theorem E_root_bounds {b : ℝ} (hb : b∈Icc (0:ℝ) (31/200)) :
    (9/5 : ℝ)<R b ∧ R b<383/200 ∧ (R b)^2=qCap-(b+1/2)^2 := by
  have hlo : 0≤b+1/2 := by linarith [hb.1]
  have hhi : b+1/2≤131/200 := by linarith [hb.2]
  have hs := pow_le_pow_left₀ hlo hhi 2
  have hr : 0≤qCap-(b+1/2)^2 := by dsimp [qCap]; nlinarith
  have hsq := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg (qCap-(b+1/2)^2)
  have hlow := pow_le_pow_left₀ (show (0:ℝ)≤1/2 by norm_num)
    (show 1/2≤b+1/2 by linarith [hb.1]) 2
  dsimp [R,qCap]
  dsimp [qCap] at hsq
  exact ⟨by nlinarith,by nlinarith,hsq⟩

theorem E_ratio_bounds {b : ℝ} (hb : b∈Icc (0:ℝ) (31/200)) :
    0<ratio b ∧ ratio b<1 := by
  have hr := E_root_bounds hb
  have hp : 0<R b := by linarith [hr.1]
  dsimp [ratio]
  exact ⟨div_pos (by linarith [hb.1]) hp,
    (div_lt_one hp).2 (by linarith [hb.2,hr.1])⟩

theorem E_f_hasDerivAt {b : ℝ} (hb : b∈Icc (0:ℝ) (31/200)) :
    HasDerivAt EpsilonCapCalculus.f (-ratio b) b := by
  have hr := E_root_bounds hb
  have hp : 0<R b := by linarith [hr.1]
  have hne : qCap-(b+1/2)^2≠0 := by nlinarith [hr.2.2]
  have hh := (((((hasDerivAt_id b).add_const (1/2)).pow 2).const_sub qCap).sqrt hne).sub_const
    (1/2)
  convert hh using 1
  · rfl
  · dsimp [ratio,R]
    field_simp

theorem decrease_bounds {a b : ℝ} (ha : a∈Icc 0 (11/50 : ℝ))
    (hb : b∈Icc (0:ℝ) (31/200)) : 0<decrease a b ∧ decrease a b≤1 := by
  have ht : a∈Icc 0 (7/10 : ℝ) := ⟨ha.1,by linarith [ha.2]⟩
  have hh := transport_trig ht
  have hr := E_ratio_bounds hb
  have hmul := mul_le_mul_of_nonneg_right hr.2.le hh.2.2.1
  have hmul0 := mul_nonneg hr.1.le hh.2.2.1
  dsimp [decrease]
  exact ⟨by linarith [hh.2.2.2.2],by linarith [hh.2.1]⟩

theorem g_hasDerivAt {a b : ℝ} (hb : b∈Icc (0:ℝ) (31/200)) :
    HasDerivAt (g a) (-decrease a b) b := by
  have hf := E_f_hasDerivAt hb
  have hh := ((hf.const_mul (Real.sin a)).const_sub ((1+Real.cos a+Real.sin a)/2)).fun_sub
    ((hasDerivAt_id' b).mul_const (Real.cos a))
  convert hh using 1
  · funext x
    simp only [g]
    ring
  · dsimp [decrease]
    ring

theorem g_antitone {a : ℝ} (ha : a∈Icc 0 (11/50 : ℝ)) :
    AntitoneOn (g a) (Icc (0:ℝ) (31/200)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun b hb => (g_hasDerivAt hb).continuousAt.continuousWithinAt
  · exact fun b hb => g_hasDerivAt (Ioo_subset_Icc_self hb)
  · exact fun b hb => (neg_nonpos.mpr (decrease_bounds ha (Ioo_subset_Icc_self hb)).1.le)

theorem g_bounds {a b : ℝ} (ha : a∈Icc 0 (11/50 : ℝ))
    (hb : b∈Icc (0:ℝ) (31/200)) : (1/2 : ℝ)<g a b ∧ g a b≤1-b := by
  have ht : a∈Icc 0 (7/10 : ℝ) := ⟨ha.1,by linarith [ha.2]⟩
  have hh := transport_trig ht
  have hr := E_root_bounds hb
  have hf : (1/2 : ℝ)<EpsilonCapCalculus.f b ∧ EpsilonCapCalculus.f b<283/200 := by
    dsimp [EpsilonCapCalculus.f]
    exact ⟨by linarith [hr.1],by linarith [hr.2.1]⟩
  have hs : Real.sin a≤11/50 := (Real.sin_le ha.1).trans ha.2
  have hfs := mul_le_mul hf.2.le hs hh.2.2.1 (by norm_num)
  have hbc := mul_le_mul_of_nonneg_left hh.2.1 hb.1
  have hw : 1≤(1+Real.cos a+Real.sin a)/2 := by
    rw [← edgeWidth_positive_formula ht]
    exact edgeWidth_ge_one _
  have hterm1 := mul_nonpos_of_nonpos_of_nonneg (show b-1/2≤0 by linarith [hb.2])
    (show 0≤1-Real.cos a by linarith [hh.2.1])
  have hterm2 := mul_nonneg (show 0≤EpsilonCapCalculus.f b-1/2 by linarith [hf.1]) hh.2.2.1
  have heq : g a b=1-b+(b-1/2)*(1-Real.cos a)-(EpsilonCapCalculus.f b-1/2)*Real.sin a := by
    dsimp [g]
    ring
  constructor
  · dsimp [g]
    linarith [hb.2]
  · rw [heq]
    linarith

theorem g_zero (a : ℝ) : g a 0=EZeroFunctions.u a-1/2 := by
  dsimp [g,EZeroFunctions.u,EpsilonCapCalculus.f,R,EZeroFunctions.v]
  simp only [zero_add,zero_mul,sub_zero]
  norm_num
  ring

theorem g_zero_endpoint : g (11/100) 0<diagonalCoordinate qCap := by
  have hb := trig_bracket (l := (11/100 : ℝ)) (u := (11/100 : ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) (by constructor <;> rfl)
  have hv := EZeroFunctions.v_bounds
  have hs : (1097/10000 : ℝ)<Real.sin (11/100) := by norm_num at hb; linarith [hb.1]
  have hc : Real.cos (11/100)<(497/500 : ℝ) := by norm_num at hb; linarith [hb.2.2.2]
  have hvs : (457/500 : ℝ)*(1097/10000)<EZeroFunctions.v*Real.sin (11/100) := by
    have h1 := mul_lt_mul_of_pos_right (show (457/500 : ℝ)<EZeroFunctions.v by linarith)
      (show 0<Real.sin (11/100) by linarith)
    have h2 := mul_lt_mul_of_pos_left hs (show (0:ℝ)<457/500 by norm_num)
    linarith
  rw [g_zero]
  dsimp [EZeroFunctions.u]
  linarith [EpsilonActiveRates.diagonal_bounds.1]

theorem active_angle {a b : ℝ} (ha : a∈Icc 0 (11/50 : ℝ))
    (hb : b∈Icc (0:ℝ) (31/200)) (hactive : diagonalCoordinate qCap≤g a b) :
    a∈Icc 0 (11/100 : ℝ) := by
  have hmono := g_antitone ha (show (0:ℝ)∈Icc 0 (31/200) by norm_num) hb hb.1
  refine ⟨ha.1,?_⟩
  by_contra! hbad
  have hu := EZeroFunctions.u_antitone (show (11/100 : ℝ)∈Icc 0 (7/10) by norm_num)
    (show a∈Icc 0 (7/10 : ℝ) from ⟨ha.1,by linarith [ha.2]⟩) hbad.le
  rw [g_zero] at hmono
  have he := g_zero_endpoint
  rw [g_zero] at he
  linarith

theorem initial_deficit {a : ℝ} (ha : a∈Icc 0 (11/100 : ℝ)) :
    (891/1000 : ℝ)*a≤1-g a 0 := by
  have hder (t : ℝ) : HasDerivAt (fun z => -EZeroFunctions.u z) (EZeroFunctions.j t) t := by
    have h := (EZeroFunctions.u_hasDerivAt t).const_sub 0
    simp only [zero_sub,neg_neg] at h
    exact h
  have hrate (t : ℝ) (ht : t∈Ioo 0 (11/100 : ℝ)) : (891/1000 : ℝ)≤EZeroFunctions.j t := by
    have htrig := EZeroHessian.trig (show t∈Icc 0 (11/100 : ℝ) from Ioo_subset_Icc_self ht)
      (show (0:ℝ)∈Icc 0 (11/100) by norm_num)
    have hv := EZeroFunctions.v_bounds
    have hc : (99/100 : ℝ)<Real.cos t := by
      have hsq := pow_le_pow_left₀ ht.1.le ht.2.le 2
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := t)]
    have hs : 0≤Real.sin t := by simpa using htrig.2.2.1
    have hm := mul_lt_mul_of_pos_right (show (457/500 : ℝ)<EZeroFunctions.v by linarith)
      (show 0<Real.cos t by linarith)
    dsimp [EZeroFunctions.j]
    nlinarith
  have hh := derivative_reserve
    (fun t _ => (hder t).continuousAt.continuousWithinAt)
    (fun t _ => hder t) hrate
    (show (0:ℝ)∈Icc 0 (11/100) by norm_num) ha ha.1
  rw [g_zero]
  norm_num [EZeroFunctions.u] at hh ⊢
  linarith

theorem active_K {a b : ℝ} (ha : a∈Icc 0 (11/50 : ℝ))
    (hb : b∈Icc (0:ℝ) (31/200)) (hactive : diagonalCoordinate qCap≤g a b) :
    K a (g a b)≤K 0 1 ∧ K 0 (g a b)≤K a 1 := by
  have has := active_angle ha hb hactive
  have hg := g_bounds ha hb
  have hx : g a b∈Icc (diagonalCoordinate qCap) 1 := ⟨hactive,by linarith [hg.2,hb.1]⟩
  have h1 : (1:ℝ)∈Icc (diagonalCoordinate qCap) 1 :=
    ⟨by linarith [EpsilonActiveRates.diagonal_bounds.2],le_rfl⟩
  have hp := EpsilonActiveRates.primary_growth has hx h1 hx.2
  have hangle := EpsilonActiveRates.angular_growth has h1
  have hgb := g_antitone ha (show (0:ℝ)∈Icc 0 (31/200) by norm_num) hb hb.1
  have hdef := initial_deficit has
  have hm := K_monotone (show (0:ℝ)∈Icc 0 (11/50) by norm_num)
    (EpsilonActiveRates.primary_mem hx) (by norm_num) hx.2
  exact ⟨by linarith,hm.trans hangle.1⟩

end SquaresInCircles.Eight.EpsilonTangent
end
end
end

section
/-!
## Both epsilon-zero endpoint cap sums decrease with the original E tangent

The derivative is nonpositive whenever the D cap is
active.  Past its intrinsic clipping point only the decreasing H cap
remains.  This proves the full comparison with b=0, including a weak tie
at the diagonal cap, without assuming a stationary E tangent.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EpsilonScalar
open EpsilonCapCalculus EpsilonTangent

def raw (a t u b : ℝ) : ℝ := H t (1+b)+H u (g a b)
def value (a t u b : ℝ) : ℝ := H t (1+b)+H u (max (diagonalCoordinate qCap) (g a b))

theorem shifted_primary {b : ℝ} (hb : b∈Icc (0:ℝ) (31/200)) :
    1+b∈Icc (1/2 : ℝ) (231/200) := ⟨by linarith [hb.1],by linarith [hb.2]⟩

theorem g_primary {a b : ℝ} (ha : a∈Icc 0 (11/50 : ℝ))
    (hb : b∈Icc (0:ℝ) (31/200)) : g a b∈Icc (1/2 : ℝ) (231/200) := by
  have hh := g_bounds ha hb
  exact ⟨hh.1.le,by linarith [hh.2,hb.1]⟩

theorem raw_hasDerivAt {a t u b : ℝ}
    (ha : a∈Icc 0 (11/50 : ℝ)) (ht : t∈Icc 0 (11/50 : ℝ))
    (hu : u∈Icc 0 (11/50 : ℝ)) (hb : b∈Icc (0:ℝ) (31/200)) :
    HasDerivAt (raw a t u) (-K t (1+b)+K u (g a b)*decrease a b) b := by
  have hH := (H_x_hasDerivAt ht (shifted_primary hb)).comp b ((hasDerivAt_id b).const_add 1)
  have hD := (H_x_hasDerivAt hu (g_primary ha hb)).comp b (g_hasDerivAt hb)
  convert hH.add hD using 1
  · rfl
  · ring

theorem raw_derivative_nonpos {a t u b : ℝ}
    (ha : a∈Icc 0 (11/50 : ℝ)) (hb : b∈Icc (0:ℝ) (31/200))
    (hend : (t=0 ∧ u=a) ∨ (t=a ∧ u=0))
    (hactive : diagonalCoordinate qCap≤g a b) :
    -K t (1+b)+K u (g a b)*decrease a b≤0 := by
  have hK := active_K ha hb hactive
  have hdec := decrease_bounds ha hb
  rcases hend with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have hmono := K_monotone (show (0:ℝ)∈Icc 0 (11/50) by norm_num)
      (show (1:ℝ)∈Icc (1/2) (231/200) by norm_num) (shifted_primary hb) (by linarith [hb.1])
    have hmul := mul_le_mul_of_nonneg_left hdec.2 (K_pos ha (g_primary ha hb)).le
    nlinarith [hK.1]
  · have hmono := K_monotone ha (show (1:ℝ)∈Icc (1/2) (231/200) by norm_num)
      (shifted_primary hb) (by linarith [hb.1])
    have hmul := mul_le_mul_of_nonneg_left hdec.2
      (K_pos (show (0:ℝ)∈Icc 0 (11/50) by norm_num) (g_primary ha hb)).le
    nlinarith [hK.2]

theorem active_raw_nonincrease {a t u b : ℝ}
    (ha : a∈Icc 0 (11/50 : ℝ)) (hb : b∈Icc (0:ℝ) (31/200))
    (hend : (t=0 ∧ u=a) ∨ (t=a ∧ u=0))
    (hactive : diagonalCoordinate qCap≤g a b) : raw a t u b≤raw a t u 0 := by
  have ht : t∈Icc 0 (11/50 : ℝ) := by
    rcases hend with ⟨h1,_⟩ | ⟨h1,_⟩
    · rw [h1]; exact ⟨le_rfl,by norm_num⟩
    · rw [h1]; exact ha
  have hu : u∈Icc 0 (11/50 : ℝ) := by
    rcases hend with ⟨_,h2⟩ | ⟨_,h2⟩
    · rw [h2]; exact ha
    · rw [h2]; exact ⟨le_rfl,by norm_num⟩
  have hsub (z : ℝ) (hz : z∈Icc (0:ℝ) b) : z∈Icc (0:ℝ) (31/200) :=
    ⟨hz.1,hz.2.trans hb.2⟩
  have hm : AntitoneOn (raw a t u) (Icc (0:ℝ) b) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun z hz => (raw_hasDerivAt ha ht hu (hsub z hz)).continuousAt.continuousWithinAt
    · exact fun z hz => raw_hasDerivAt ha ht hu (hsub z (Ioo_subset_Icc_self hz))
    · intro z hz
      have hzg := g_antitone ha (hsub z (Ioo_subset_Icc_self hz)) hb hz.2.le
      exact raw_derivative_nonpos ha (hsub z (Ioo_subset_Icc_self hz)) hend (hactive.trans hzg)
  exact hm ⟨le_rfl,hb.1⟩ ⟨hb.1,le_rfl⟩ hb.1

theorem value_eq_raw {a t u b : ℝ} (hactive : diagonalCoordinate qCap≤g a b) :
    value a t u b=raw a t u b := by simp [value,raw,max_eq_right hactive]

theorem nonincrease {a t u b : ℝ}
    (ha : a∈Icc 0 (11/50 : ℝ)) (hb : b∈Icc (0:ℝ) (31/200))
    (hend : (t=0 ∧ u=a) ∨ (t=a ∧ u=0)) : value a t u b≤value a t u 0 := by
  have ht : t∈Icc 0 (11/50 : ℝ) := by
    rcases hend with ⟨h1,_⟩ | ⟨h1,_⟩
    · rw [h1]; exact ⟨le_rfl,by norm_num⟩
    · rw [h1]; exact ha
  have hb0 : (0:ℝ)∈Icc 0 (31/200) := by norm_num
  have hgb := g_antitone ha hb0 hb hb.1
  by_cases h0 : g a 0≤diagonalCoordinate qCap
  · have hbc := hgb.trans h0
    have hm := H_antitone ht (shifted_primary hb0) (shifted_primary hb) (by linarith [hb.1])
    simp only [value,max_eq_left hbc,max_eq_left h0,add_zero] at hm ⊢
    linarith
  · have h0a : diagonalCoordinate qCap≤g a 0 := (le_of_not_ge h0)
    by_cases hba : diagonalCoordinate qCap≤g a b
    · rw [value_eq_raw hba,value_eq_raw h0a]
      exact active_raw_nonincrease ha hb hend hba
    · have hbl : g a b<diagonalCoordinate qCap := lt_of_not_ge hba
      have hcont : ContinuousOn (fun z => -g a z) (Icc (0:ℝ) b) := fun z hz =>
        (g_hasDerivAt (show z∈Icc (0:ℝ) (31/200) from
          ⟨hz.1,hz.2.trans hb.2⟩)).neg.continuousAt.continuousWithinAt
      obtain ⟨z,hz,hzeq⟩ := intermediate_value_Icc hb.1 hcont
        (show -diagonalCoordinate qCap∈Icc (-g a 0) (-g a b) by constructor <;> linarith)
      have hz' : z∈Icc (0:ℝ) (31/200) := ⟨hz.1,hz.2.trans hb.2⟩
      have hzg : g a z=diagonalCoordinate qCap := by linarith
      have hzvalue : value a t u z≤value a t u 0 := by
        rw [value_eq_raw hzg.ge,value_eq_raw h0a]
        exact active_raw_nonincrease ha hz' hend hzg.ge
      have hH := H_antitone ht (shifted_primary hz') (shifted_primary hb) (by linarith [hz.2])
      have hvalue : value a t u b≤value a t u z := by
        simp only [value,max_eq_left hbl.le,hzg,max_self]
        linarith
      exact hvalue.trans hzvalue

theorem diagonal_self : EpsilonCapCalculus.f (diagonalCoordinate qCap)=diagonalCoordinate qCap := by
  have hs := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
  have harg : qCap-(diagonalCoordinate qCap+1/2)^2=qCap/2 := by
    rw [diagonalCoordinate,sub_add_cancel,hs]
    ring
  rw [EpsilonCapCalculus.f,EpsilonCapCalculus.R,harg,diagonalCoordinate]

theorem f_one : EpsilonCapCalculus.f 1=EZeroFunctions.capped 0 := by
  have hc : diagonalCoordinate qCap∈Icc (1/2 : ℝ) (231/200) := by
    constructor <;> linarith [EpsilonActiveRates.diagonal_bounds.1,EpsilonActiveRates.diagonal_bounds.2]
  have hmono := f_antitone hc (show (1:ℝ)∈Icc (1/2) (231/200) by norm_num)
    (show diagonalCoordinate qCap≤1 by linarith [EpsilonActiveRates.diagonal_bounds.2])
  rw [diagonal_self] at hmono
  have hh : EZeroFunctions.h 0=EpsilonCapCalculus.f 1 := by
    norm_num [EZeroFunctions.h,EZeroFunctions.rho,EZeroFunctions.u,EpsilonCapCalculus.f,R]
  simp [EZeroFunctions.capped,hh,min_eq_right hmono]

theorem f_g_zero (a : ℝ) : EpsilonCapCalculus.f (g a 0)=EZeroFunctions.h a := by
  rw [g_zero]
  simp only [EpsilonCapCalculus.f,R,sub_add_cancel,EZeroFunctions.h,EZeroFunctions.rho]

theorem clipped_initial {a : ℝ} (ha : a∈Icc 0 (11/50 : ℝ)) :
    EpsilonCapCalculus.f (max (diagonalCoordinate qCap) (g a 0))=EZeroFunctions.capped a := by
  have hc : diagonalCoordinate qCap∈Icc (1/2 : ℝ) (231/200) := by
    constructor <;> linarith [EpsilonActiveRates.diagonal_bounds.1,EpsilonActiveRates.diagonal_bounds.2]
  have hg := g_primary ha (show (0:ℝ)∈Icc 0 (31/200) by norm_num)
  by_cases hcg : diagonalCoordinate qCap≤g a 0
  · have hm := f_antitone hc hg hcg
    rw [diagonal_self,f_g_zero] at hm
    simp [max_eq_right hcg,f_g_zero,EZeroFunctions.capped,min_eq_right hm]
  · have hgc : g a 0≤diagonalCoordinate qCap := le_of_not_ge hcg
    have hm := f_antitone hg hc hgc
    rw [diagonal_self,f_g_zero] at hm
    simp [max_eq_left hgc,diagonal_self,EZeroFunctions.capped,min_eq_left hm]

theorem initial_value {a t u : ℝ} (ha : a∈Icc 0 (11/50 : ℝ)) :
    value a t u 0=
      HardSplitCap.cap qCap (3/2-EZeroFunctions.capped 0) t+
        HardSplitCap.cap qCap (3/2-EZeroFunctions.capped a) u := by
  simp only [value,add_zero,cap_eq,f_one,clipped_initial ha]

theorem strict_bound {a t u b : ℝ}
    (ha : a∈Icc 0 (11/50 : ℝ)) (hb : b∈Icc (0:ℝ) (31/200))
    (hend : (t=0 ∧ u=a) ∨ (t=a ∧ u=0)) : value a t u b<2 := by
  apply (nonincrease ha hb hend).trans_lt
  rw [initial_value ha]
  rcases hend with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · rw [h1,h2]
    simpa using EZeroCapEndpoints.first_endpoint (show (0:ℝ)≤0 by norm_num) ha.1
      (show (0:ℝ)+a≤7/10 by linarith [ha.2])
  · rw [h1,h2]
    simpa using EZeroCapEndpoints.second_endpoint (show (0:ℝ)≤0 by norm_num) ha.1
      (show (0:ℝ)+a≤7/10 by linarith [ha.2])

end SquaresInCircles.Eight.EpsilonScalar
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EpsilonGeometry
open EpsilonCapCalculus EpsilonTangent EpsilonScalar

theorem tangent_of_primary {P : SignedPoint} {x : ℝ}
    (hPc : P.Contained qCap) (hy : 0≤P.y)
    (hx : x∈Icc (1/2 : ℝ) (231/200)) (hxa : x≤P.a) : P.y≤EpsilonCapCalculus.f x := by
  have hcircle : (P.a+1/2)^2+(P.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hy] using hPc
  have hprimary := pow_le_pow_left₀ (show 0≤x+1/2 by linarith [hx.1])
    (show x+1/2≤P.a+1/2 by linarith) 2
  have hr := R_sq hx
  have hp := R_pos hx
  dsimp [EpsilonCapCalculus.f]
  nlinarith

theorem E_primary {P : SignedPoint} {b : ℝ}
    (_hPs : P.Sorted) (hPc : P.Contained qCap)
    (hb : b∈Icc (0:ℝ) (31/200)) (hy : P.y= -b) : P.a≤EpsilonCapCalculus.f b := by
  have hcircle : (P.a+1/2)^2+(b+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,hy,abs_neg,abs_of_nonneg hb.1] using hPc
  have hr := E_root_bounds hb
  dsimp [EpsilonCapCalculus.f]
  nlinarith

/-- A bound on the outer tangent gives an upper hard cap on the actual
middle tangent.  Only the source circle and its actual separator are
used; no contact equality or independent cap feasibility is assumed. -/
theorem cap_majorizes {P : SignedPoint} {t x z : ℝ}
    (hPs : P.Sorted) (hPy : 0≤P.y) (hPc : P.Contained qCap)
    (ht : t∈Icc 0 (11/50 : ℝ)) (hx : x∈Icc (1/2 : ℝ) (231/200))
    (hz : z≤EpsilonCapCalculus.f x)
    (hsep : 1+edgeWidth t≤z+P.a*Real.cos t-P.y*Real.sin t) :
    P.y+1/2≤H t x := by
  let X := P.a+1/2
  let Z := P.y+1/2
  let p := X*Real.cos t-Z*Real.sin t
  let r := X*Real.sin t+Z*Real.cos t
  have ht' : t∈Icc 0 (7/10 : ℝ) := ⟨ht.1,by linarith [ht.2]⟩
  have htrig := transport_trig ht'
  have hcos : 0≤Real.cos t := by linarith [htrig.1]
  have hsin : 0≤Real.sin t := htrig.2.2.1
  have hcircle : X^2+Z^2≤qCap := by
    simpa [X,Z,SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hPy] using hPc
  have hcontact : C t x≤p := by
    rw [edgeWidth_positive_formula ht'] at hsep
    dsimp [EpsilonCapCalculus.f] at hz
    dsimp [C,p,X,Z]
    linarith
  have hcpos := C_pos ht hx
  have hpsq := pow_le_pow_left₀ hcpos.le hcontact 2
  have hrot : p^2+r^2=X^2+Z^2 := by
    calc
      p^2+r^2=((Real.sin t)^2+(Real.cos t)^2)*(X^2+Z^2) := by
        dsimp [p,r]
        ring
      _ = X^2+Z^2 := by rw [Real.sin_sq_add_cos_sq,one_mul]
  have hr0 : 0≤r := add_nonneg
    (mul_nonneg (by dsimp [X]; linarith [hPs.1]) hsin)
    (mul_nonneg (by dsimp [Z]; linarith) hcos)
  have hwp := w_pos ht hx
  have hws := w_sq ht hx
  have hrw : r≤w t x := by nlinarith
  have hZ : Z=Real.cos t*r-Real.sin t*p := by
    calc
      Z=Z*((Real.sin t)^2+(Real.cos t)^2) := by rw [Real.sin_sq_add_cos_sq,mul_one]
      _ = Real.cos t*r-Real.sin t*p := by dsimp [p,r]; ring
  have hcr := mul_le_mul_of_nonneg_left hrw hcos
  have hsp := mul_le_mul_of_nonneg_left hcontact hsin
  change Z≤H t x
  rw [hZ]
  dsimp [H]
  linarith

theorem clipped_primary_mem {a b : ℝ}
    (ha : a∈Icc 0 (11/50 : ℝ)) (hb : b∈Icc (0:ℝ) (31/200)) :
    max (diagonalCoordinate qCap) (g a b)∈Icc (1/2 : ℝ) (231/200) := by
  have hg := g_primary ha hb
  have hc := EpsilonActiveRates.diagonal_bounds
  exact ⟨le_trans (by linarith [hc.1]) (le_max_left _ _),
    max_le (by linarith [hc.2]) hg.2⟩

end EpsilonGeometry

namespace SignedCycle
open Candidate EpsilonGeometry

private theorem feasible_quarter (C : SignedCycle) {i k : Vertex} (hw : Candidate.word i=1)
    (hk : next i=k) (j : Fin 4) :
    C.Feasible i j ↔ edgeWidth (C.theta k-C.theta i)≤
      quarterProjection (C.point i) (C.point k) (C.theta k-C.theta i) j := by
  subst hk
  simp only [Feasible,slack,edge,delta,hw,one_ne_zero,↓reduceIte,sub_nonneg]

private theorem feasible_congr {C C' : SignedCycle} {i k : Vertex} (hk : next i=k) {j : Fin 4}
    (h1 : C'.point i=C.point i) (h2 : C'.theta i=C.theta i)
    (h3 : C'.point k=C.point k) (h4 : C'.theta k=C.theta k) :
    C'.Feasible i j ↔ C.Feasible i j := by
  subst hk
  simp only [Feasible,slack,edge,delta,h1,h2,h3,h4]

/-- The actual E=H constraints bound both outer tangents by the same
original E parameter.  Their common angle and the E parameter bounds
come from the original aligned chain, not from a supplied scalar domain. -/
theorem HardInput.epsilon_zero_caps {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A)
    (hEHframe : I.cycle.theta E=I.cycle.theta H)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) :
    let a := I.cycle.theta H-I.cycle.theta D
    let b := -(I.cycle.point E).y
    a∈Icc 0 (11/50 : ℝ) ∧ b∈Icc 0 (31/200 : ℝ) ∧
      (I.cycle.point H).y≤EpsilonCapCalculus.f (1+b) ∧
      -(I.cycle.point D).y≤EpsilonCapCalculus.f
        (max (diagonalCoordinate qCap) (EpsilonTangent.g a b)) := by
  dsimp only
  let a := I.cycle.theta H-I.cycle.theta D
  let b := -(I.cycle.point E).y
  show a∈Icc 0 (11/50 : ℝ) ∧ b∈Icc 0 (31/200 : ℝ) ∧
      (I.cycle.point H).y≤EpsilonCapCalculus.f (1+b) ∧
      -(I.cycle.point D).y≤EpsilonCapCalculus.f
        (max (diagonalCoordinate qCap) (EpsilonTangent.g a b))
  have hbounds := I.aligned_bounds hq hHG hAB hTD hleft hright
  have ha : a∈Icc 0 (11/50 : ℝ) := ⟨hbounds.span_nonneg,hbounds.span_lt.le⟩
  have hb0 : 0≤b := neg_nonneg.mpr I.E_nonpos
  have h0 : edgeWidth 0=1 := by
    rw [edgeWidth_positive_formula (by norm_num)]; norm_num
  have hEH' : 1≤(I.cycle.point H).a-b := by
    have h := (feasible_quarter I.cycle (i := E) (k := H) (by decide) (by decide) 1).1 hEH
    have h' : edgeWidth (I.cycle.theta H-I.cycle.theta E)≤(I.cycle.point H).a+
        (I.cycle.point E).a*Real.sin (I.cycle.theta H-I.cycle.theta E)+
        (I.cycle.point E).y*Real.cos (I.cycle.theta H-I.cycle.theta E) := h
    rw [hEHframe,sub_self,Real.sin_zero,Real.cos_zero,h0] at h'
    dsimp [b]
    linarith
  have hb : b∈Icc (0:ℝ) (31/200) := ⟨hb0,by linarith [hbounds.H_primary.2]⟩
  have hc (i : Vertex) : (I.cycle.point i).Contained qCap := (I.necessary.contained i).trans hq
  have hHcap := tangent_of_primary (hc H) I.anchors_normal.H_nonneg
    (EpsilonScalar.shifted_primary hb) (show 1+b≤(I.cycle.point H).a by linarith)
  have hEcap := E_primary (I.necessary.sorted E) (hc E) hb
    (show (I.cycle.point E).y= -b by dsimp [b]; ring)
  have hDE' : edgeWidth a≤(I.cycle.point D).a+
      (I.cycle.point E).a*Real.sin a+b*Real.cos a := by
    have h := (feasible_quarter I.cycle (i := D) (k := E) (by decide) (by decide) 3).1 hDE
    have h' : edgeWidth (I.cycle.theta E-I.cycle.theta D)≤(I.cycle.point D).a+
        (I.cycle.point E).a*Real.sin (I.cycle.theta E-I.cycle.theta D)-
        (I.cycle.point E).y*Real.cos (I.cycle.theta E-I.cycle.theta D) := h
    rw [hEHframe] at h'
    dsimp [a,b]
    linarith
  have ha' : a∈Icc 0 (7/10 : ℝ) := ⟨ha.1,by linarith [ha.2]⟩
  have hEprod := mul_le_mul_of_nonneg_right hEcap (transport_trig ha').2.2.1
  have hgD : EpsilonTangent.g a b≤(I.cycle.point D).a := by
    rw [edgeWidth_positive_formula ha'] at hDE'
    dsimp [EpsilonTangent.g]
    linarith
  have hDnormal : 0≤(I.cycle.point D).reflect.y := by
    dsimp [SignedPoint.reflect]
    linarith [I.anchors_normal.D_nonpos]
  have hDcap := tangent_of_primary
    (P := (I.cycle.point D).reflect) (by simpa using hc D) hDnormal
    (EpsilonScalar.g_primary ha hb) (by simpa [SignedPoint.reflect] using hgD)
  have hDdiagonal : -(I.cycle.point D).y≤diagonalCoordinate qCap := by
    simpa [abs_of_nonpos I.anchors_normal.D_nonpos] using
      SignedPoint.contained_minor_le_diagonal (I.necessary.sorted D) (hc D)
  refine ⟨ha,hb,hHcap,?_⟩
  by_cases hg : diagonalCoordinate qCap≤EpsilonTangent.g a b
  · rw [max_eq_right hg]
    simpa [SignedPoint.reflect] using hDcap
  · rw [max_eq_left (le_of_not_ge hg),EpsilonScalar.diagonal_self]
    exact hDdiagonal

/-- Both actual split endpoints contradict the cap sum. -/
theorem HardInput.epsilon_zero_endpoint_impossible {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A)
    (hend : I.cycle.theta A=I.cycle.theta H ∨ I.cycle.theta A=I.cycle.theta D)
    (hEHframe : I.cycle.theta E=I.cycle.theta H)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) : False := by
  let a := I.cycle.theta H-I.cycle.theta D
  let b := -(I.cycle.point E).y
  let t := I.cycle.theta H-I.cycle.theta A
  let u := I.cycle.theta A-I.cycle.theta D
  obtain ⟨ha,hb,hHcap,hDcap⟩ := I.epsilon_zero_caps hq hHG hAB hTD hleft hright hEHframe hDE hEH
  have hsplit : (t=0 ∧ u=a) ∨ (t=a ∧ u=0) := by
    rcases hend with h | h
    · left; dsimp [t,u,a]; rw [h]; simp
    · right; dsimp [t,u,a]; rw [h]; simp
  have ht : t∈Icc 0 (11/50 : ℝ) := by
    rcases hsplit with ⟨h1,_⟩ | ⟨h1,_⟩
    · rw [h1]; norm_num
    · rw [h1]; exact ha
  have hu : u∈Icc 0 (11/50 : ℝ) := by
    rcases hsplit with ⟨_,h1⟩ | ⟨_,h1⟩
    · rw [h1]; exact ha
    · rw [h1]; norm_num
  have hc (i : Vertex) : (I.cycle.point i).Contained qCap := (I.necessary.contained i).trans hq
  have hcomp := I.aligned_composites hHG hAB hTD
  have hAcap := cap_majorizes (I.necessary.sorted A) I.anchors_normal.A_nonneg (hc A)
    ht (EpsilonScalar.shifted_primary hb) hHcap hcomp.1
  have hBcap := cap_majorizes (P := (I.cycle.point B).reflect)
    (by simpa using I.necessary.sorted B)
    (by dsimp [SignedPoint.reflect]; linarith [I.anchors_normal.B_nonpos])
    (by simpa using hc B) hu (clipped_primary_mem ha hb) hDcap
    (by simpa [u,SignedPoint.reflect,sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hcomp.2.1)
  have hsum : 2≤EpsilonScalar.value a t u b := by
    dsimp [EpsilonScalar.value]
    dsimp [SignedPoint.reflect] at hBcap
    linarith [hcomp.2.2]
  exact (not_lt_of_ge hsum) (EpsilonScalar.strict_bound ha hb hsplit)

/-- E=H is excluded before any source equality is used.  The split keeps
the literal H, D and E points, frames, circles, and original mixed axes. -/
theorem HardInput.aligned_epsilon_zero_impossible {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A)
    (hEHframe : I.cycle.theta E=I.cycle.theta H)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) : False := by
  obtain ⟨J,hend,hJAB,hnon,hstrict,hfixed⟩ := I.split_with_source_loss hq hHG hAB.symm hTD
    (by simpa [hHG] using hleft) (by simpa [hTD] using hright)
  have hH := hfixed H (by decide) (by decide)
  have hG := hfixed G (by decide) (by decide)
  have hT := hfixed T (by decide) (by decide)
  have hD := hfixed D (by decide) (by decide)
  have hE := hfixed E (by decide) (by decide)
  have hJHG : J.cycle.theta G=J.cycle.theta H := by rw [hG.2,hH.2,hHG]
  have hJTD : J.cycle.theta T=J.cycle.theta D := by rw [hT.2,hD.2,hTD]
  have hJend : J.cycle.theta A=J.cycle.theta H ∨ J.cycle.theta A=J.cycle.theta D := by
    simpa [hJHG,hJTD] using hend
  have horder : J.cycle.theta D≤J.cycle.theta H := by
    rw [hD.2,hH.2]
    exact hright.trans hleft
  have hJleft : J.cycle.theta A≤J.cycle.theta H := by
    rcases hJend with h | h
    · exact h.le
    · rw [h]; exact horder
  have hJright : J.cycle.theta D≤J.cycle.theta A := by
    rcases hJend with h | h
    · rw [h]; exact horder
    · exact h.ge
  have hJEHframe : J.cycle.theta E=J.cycle.theta H := by rw [hE.2,hH.2,hEHframe]
  have hJDE : J.cycle.Feasible D 3 :=
    (feasible_congr (by decide) hD.1 hD.2 hE.1 hE.2).2 hDE
  have hJEH : J.cycle.Feasible E 1 :=
    (feasible_congr (by decide) hE.1 hE.2 hH.1 hH.2).2 hEH
  exact J.epsilon_zero_endpoint_impossible hq hJHG hJAB hJTD hJleft hJright hJend hJEHframe hJDE hJEH

end SignedCycle
end SquaresInCircles.Eight
end
end
