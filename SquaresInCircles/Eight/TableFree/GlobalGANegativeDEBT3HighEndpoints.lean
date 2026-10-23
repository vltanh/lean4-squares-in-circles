module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3HighTransferData

/-!
# All four actual high-T endpoints for negative DE3 / positive BT3

Uncompiled Section 8.2. The three zero-DE endpoints retain the original
H/G/B negative norm. At equal angles the actual secant-D norm is scaled
by the positive original cosine; it is not replaced by an unrotated
norm. Every norm mass and numerator comes from its whole native interval.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.HighTransfer
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open PositiveTD.Certificate (S9 S11 C10 C12 taylor_bounds num4_transfer)
open Certificate (HighCase)

lemma qStar_upper {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    max (l θ) (m θ)≤aeval (native θ) Certificate.highQStar := by
  have hh := NegativeDEPositiveTD.Certificate.qStar_lower .atA hθ
  simpa [Certificate.highQStar,Certificate.theta,Certificate.theta_eval,Certificate.highL_eval,
    HighShape.native_total,NegativeDEPositiveTD.Certificate.qStar,
    NegativeDEPositiveTD.Certificate.l_eval,NegativeDEPositiveTD.Explicit.splitM,
    NegativeDEPositiveTD.Explicit.splitT,NegativeDEPositiveTD.Explicit.m,
    PositiveTD.Certificate.h,Certificate.h,l,m,Explicit.l,Explicit.m] using hh

def negativeNorm (r : HighCase) (θ : ℝ) : Fin 4→ℝ :=
  ![pairNorm (k θ) 1 (if r=.H then -θ else 0),
    pairNorm (k θ) (l θ) (if r=.G then -θ else 0),
    pairNorm (l θ) (m θ) (if r=.B then -θ else 0),pairNorm 1 (c θ) 0]
def negativeA (r : HighCase) (θ : ℝ) : ℝ := base θ+
  (if r=.H then 1 else if r=.G then l θ else max (l θ) (m θ))*(Real.cos θ-1)

theorem negative_norm_bound (r : HighCase) (hr : r≠.equal) {θ : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 4) :
    (negativeNorm r θ i)^2≤aeval (native θ) (Certificate.highP r i) := by
  have hb := Explicit.high_bounds hθ
  have hk : 0<k θ := by linarith [hb.k_lower]
  have hl : 0<l θ := by linarith [hb.l_lower]
  have hm : 0<m θ := by linarith [hb.m_lower]
  have ht := taylor_bounds (Explicit.frame_domain .high hθ)
  have hzero := norm_bounds hθ
  have hnegative {p q : ℝ} (hp : 0<p) (hq : 0<q) :
      (pairNorm p q (-θ))^2≤p^2+q^2-2*p*q*aeval θ S11 := by
    have hh := NonnegativeTotals.Analytic.norm_negative_square hp hq (Explicit.frame_domain .high hθ)
    have hsin := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤2*p*q by positivity)
    linarith
  have hH := hnegative hk (by norm_num : (0:ℝ)<1)
  have hG := hnegative hk hl
  have hB := hnegative hl hm
  cases r <;> norm_num at hr <;> fin_cases i <;>
    simp only [negativeNorm,Certificate.highP,Certificate.highNormZero,Certificate.highIndex,
      Certificate.highProduct,Matrix.cons_val_succ,Matrix.cons_val_zero,
      if_true,if_false,reduceCtorEq,Fin.castSucc_mk,map_sub,map_add,map_mul,map_pow,map_one,
      aeval_C,aeval_comp,Certificate.theta_eval,Certificate.highK_eval,
      Certificate.highL_eval,Certificate.highM_eval,HighShape.native_total] at *
  all_goals first
    | simpa only [one_pow,add_comm] using hH
    | exact hG
    | exact hB
    | exact hzero 0
    | exact hzero 1
    | exact hzero 2
    | exact hzero 3

theorem negative_nonradical_lower (r : HighCase) (hr : r≠.equal) {θ : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    aeval (native θ) (Certificate.highA r)≤negativeA r θ := by
  have hb := base_lower hθ
  have ht := taylor_bounds (Explicit.frame_domain .high hθ)
  have hl : 0≤l θ := by linarith [(Explicit.high_bounds hθ).l_lower]
  have hG := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1) hl
  have hq := qStar_upper hθ
  have hq0 : 0≤aeval (native θ) Certificate.highQStar := (hl.trans (le_max_left _ _)).trans hq
  have hB0 := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1) hq0
  have hB1 := mul_le_mul_of_nonpos_right hq (sub_nonpos.mpr (Real.cos_le_one θ))
  cases r <;> norm_num at hr <;>
    simp only [Certificate.highA,Certificate.highIndex,Certificate.highCosineCoefficient,
      if_true,if_false,reduceCtorEq,Matrix.cons_val_succ,Matrix.cons_val_zero,
      map_add,map_mul,map_sub,map_one,aeval_comp,Certificate.theta_eval,
      Certificate.highL_eval,HighShape.native_total,negativeA,one_mul] <;>
    linarith [ht.2.2.2.2.1]

theorem negative_identity (r : HighCase) (hr : r≠.equal) {θ : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Explicit.fullBaseline .high 0 θ 0+Explicit.V .high θ (Certificate.highIndex r) θ=
      negativeA r θ-R*(negativeNorm r θ 0+negativeNorm r θ 1+
        negativeNorm r θ 2+negativeNorm r θ 3) := by
  rw [baseline_identity hθ]
  cases r <;> norm_num at hr <;>
    simp only [negativeA,negativeNorm,norms,Certificate.highIndex,Explicit.V,Explicit.p,Explicit.q,
      Matrix.cons_val_succ,Matrix.cons_val_zero,if_true,if_false,reduceCtorEq,one_mul,V,
      TwoPositive.Certificate.sorted_pair_norm] <;> ring

theorem zero_positive (i : Fin 3) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    0<Explicit.fullBaseline .high 0 θ 0+Explicit.V .high θ i θ := by
  have hrow (r : HighCase) (hr : r≠.equal) :
      0<Explicit.fullBaseline .high 0 θ 0+Explicit.V .high θ (Certificate.highIndex r) θ := by
    have hx := HighShape.native_domain hθ
    have hn (j : Fin 4) : 0≤negativeNorm r θ j := by fin_cases j <;> exact Real.sqrt_nonneg _
    have hh := num4_transfer
      (Certificate.high_mass_positive r 0 hx) (Certificate.high_mass_positive r 1 hx)
      (Certificate.high_mass_positive r 2 hx) (Certificate.high_mass_positive r 3 hx)
      (hn 0) (hn 1) (hn 2) (hn 3)
      (negative_norm_bound r hr hθ 0) (negative_norm_bound r hr hθ 1)
      (negative_norm_bound r hr hθ 2) (negative_norm_bound r hr hθ 3)
      (negative_nonradical_lower r hr hθ) (Certificate.high_numerator_positive r hx)
    rwa [negative_identity r hr hθ]
  fin_cases i
  · exact hrow .H (by decide)
  · exact hrow .G (by decide)
  · exact hrow .B (by decide)

def equalNorm (θ : ℝ) : Fin 4→ℝ :=
  ![Real.cos θ*norms θ 0,Real.cos θ*norms θ 1,Real.cos θ*norms θ 2,
    Real.cos θ*pairNorm (Explicit.sec θ) (c θ) 0]
def equalA (θ : ℝ) : ℝ := Real.cos θ*(base θ-1)+1+Explicit.K*Real.sin θ

lemma scaled_D_square {θ : ℝ} (hθ : θ∈Icc 0 frameCap) :
    (equalNorm θ 3)^2=1+(c θ)^2*(Real.cos θ)^2 := by
  have hc := NegativeESecant.cos_pos hθ
  simp only [equalNorm,Matrix.cons_val_succ,Matrix.cons_val_zero,mul_pow,
    NonnegativeTotals.Analytic.norm_zero_square]
  dsimp [Explicit.sec,NegativeELargeA.secant]
  field_simp [hc.ne']
  ring

theorem equal_norm_bound {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 4) :
    (equalNorm θ i)^2≤aeval (native θ) (Certificate.highP .equal i) := by
  have hf := Explicit.frame_domain .high hθ
  have hcos := NegativeDEPositiveTD.Certificate.cosine_square_upper hf
  have hzero := norm_bounds hθ
  have hC := HighShape.coefficient_majorant hθ
  have hc0 : 0≤c θ := by
    linarith [(Explicit.high_c hθ ⟨by linarith [hθ.1],le_rfl⟩).1,(Explicit.high_bounds hθ).m_lower]
  have hC2 := pow_le_pow_left₀ hc0 hC 2
  have hprod := mul_le_mul hC2 hcos (sq_nonneg (Real.cos θ)) (sq_nonneg (aeval (native θ) Certificate.highC))
  fin_cases i
  · simpa [equalNorm,Certificate.highP,Certificate.highNormZero,aeval_comp,
      Certificate.theta_eval,HighShape.native_total] using
      NegativeDEPositiveTD.Certificate.scaled_norm_bound hf (hzero 0)
  · simpa [equalNorm,Certificate.highP,Certificate.highNormZero,aeval_comp,
      Certificate.theta_eval,HighShape.native_total] using
      NegativeDEPositiveTD.Certificate.scaled_norm_bound hf (hzero 1)
  · simpa [equalNorm,Certificate.highP,Certificate.highNormZero,aeval_comp,
      Certificate.theta_eval,HighShape.native_total] using
      NegativeDEPositiveTD.Certificate.scaled_norm_bound hf (hzero 2)
  · rw [scaled_D_square hf]
    simpa [Certificate.highP,aeval_comp,Certificate.theta_eval,HighShape.native_total] using
      add_le_add_left hprod 1

theorem equal_nonradical_lower {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    aeval (native θ) (Certificate.highA .equal)≤equalA θ := by
  have ht := taylor_bounds (Explicit.frame_domain .high hθ)
  have hc := NegativeESecant.cos_pos (Explicit.frame_domain .high hθ)
  have hpoly := base_polynomial_positive hθ
  have hbase := sub_le_sub_right (base_lower hθ) 1
  have hprod := mul_le_mul ht.2.2.2.2.1 hbase
    (by simpa only [map_sub,map_one] using hpoly.le) hc.le
  have hs := mul_le_mul_of_nonneg_left ht.2.1 (show (0:ℝ)≤13/12 by norm_num)
  simp only [Certificate.highA,if_pos rfl,map_add,map_mul,map_sub,map_one,
    aeval_C,aeval_comp,Certificate.theta_eval,HighShape.native_total]
  dsimp [equalA,Explicit.K,Certificate.K]
  linarith

theorem equal_identity {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Real.cos θ*Explicit.fullBaseline .high 0 θ θ=
      equalA θ-R*(equalNorm θ 0+equalNorm θ 1+equalNorm θ 2+equalNorm θ 3) := by
  have hc := NegativeESecant.cos_pos (Explicit.frame_domain .high hθ)
  have hid : Explicit.fullBaseline .high 0 θ θ=Explicit.fullBaseline .high 0 θ 0+
      (Explicit.sec θ-1)/2+Explicit.K*Real.tan θ-
        (fullSupport (Explicit.sec θ) (c θ)-fullSupport 1 (c θ)) := by
    simp [Explicit.fullBaseline,Explicit.sec,NegativeELargeA.secant,c]
    ring
  rw [hid,baseline_identity hθ,fullSupport_pair (Explicit.sec θ) (c θ),fullSupport_pair 1 (c θ)]
  dsimp [equalA,equalNorm,norms]
  rw [Real.tan_eq_sin_div_cos]
  dsimp [Explicit.sec,NegativeELargeA.secant]
  field_simp [hc.ne']
  ring

theorem equal_positive {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    0<Explicit.fullBaseline .high 0 θ θ := by
  have hx := HighShape.native_domain hθ
  have hc := NegativeESecant.cos_pos (Explicit.frame_domain .high hθ)
  have hn (i : Fin 4) : 0≤equalNorm θ i := by
    fin_cases i <;> exact mul_nonneg hc.le (Real.sqrt_nonneg _)
  have hh := num4_transfer
    (Certificate.high_mass_positive .equal 0 hx) (Certificate.high_mass_positive .equal 1 hx)
    (Certificate.high_mass_positive .equal 2 hx) (Certificate.high_mass_positive .equal 3 hx)
    (hn 0) (hn 1) (hn 2) (hn 3)
    (equal_norm_bound hθ 0) (equal_norm_bound hθ 1)
    (equal_norm_bound hθ 2) (equal_norm_bound hθ 3)
    (equal_nonradical_lower hθ) (Certificate.high_numerator_positive .equal hx)
  rw [←equal_identity hθ] at hh
  exact (mul_pos_iff_of_pos_left hc).mp hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.HighTransfer
