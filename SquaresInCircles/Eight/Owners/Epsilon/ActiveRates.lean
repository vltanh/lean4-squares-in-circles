module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.Endpoint.Principles
public import SquaresInCircles.Eight.Owners.Epsilon.CapCalculus

/-!
# Eight squares: the primary loss dominates angular gain on the active epsilon-zero arc

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
