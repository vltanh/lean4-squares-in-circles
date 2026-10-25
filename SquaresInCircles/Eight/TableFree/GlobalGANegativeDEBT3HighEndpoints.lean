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

private lemma r72_nt (θ : ℝ) : native θ+(Certificate.L:ℝ)=θ := by simp [native]

private lemma r72_K (θ : ℝ) : aeval (native θ) Certificate.highK=k θ := by
  rw [Certificate.highK_eval,r72_nt]

private lemma r72_L (θ : ℝ) : aeval (native θ) Certificate.highL=l θ := by
  rw [Certificate.highL_eval,r72_nt]

private lemma r72_M (θ : ℝ) : aeval (native θ) Certificate.highM=m θ := by
  rw [Certificate.highM_eval,r72_nt]

private lemma r72_comp (θ : ℝ) (P : ℚ[X]) :
    aeval (native θ) (P.comp Certificate.theta)=aeval θ P := by
  rw [aeval_comp,Certificate.theta_eval,r72_nt]

lemma qStar_upper {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    max (l θ) (m θ)≤aeval (native θ) Certificate.highQStar := by
  have hh := NegativeDEPositiveTD.Certificate.qStar_lower .atA hθ
  have h1 : aeval θ NegativeDEPositiveTD.Certificate.qStar=l θ+3/20*(7/10-θ) := by
    simp only [NegativeDEPositiveTD.Certificate.qStar,map_add,map_mul,map_sub,aeval_C,aeval_X,
      NegativeDEPositiveTD.Certificate.l_eval]
    norm_num [PositiveTD.Certificate.h]
    rfl
  have h2 : aeval (native θ) Certificate.highQStar=l θ+3/20*(7/10-θ) := by
    simp only [Certificate.highQStar,map_add,map_mul,map_sub,aeval_C,r72_L,
      Certificate.theta_eval,r72_nt]
    norm_num [Certificate.h]
  have h3 : NegativeDEPositiveTD.Explicit.splitM .high .atA θ=m θ := by
    simp [NegativeDEPositiveTD.Explicit.splitM,NegativeDEPositiveTD.Explicit.splitT,
      NegativeDEPositiveTD.Explicit.m,m,Explicit.m]
  rw [h1,h3] at hh
  rw [h2]
  exact hh

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
  have hm : 0 < m θ := by linarith [hb.m_lower]
  have hf := Explicit.frame_domain .high hθ
  have ht := taylor_bounds hf
  have hzero := norm_bounds hθ
  have hnegative {p q : ℝ} (hp : 0<p) (hq : 0<q) :
      (pairNorm p q (-θ))^2≤p^2+q^2-2*p*q*aeval θ S11 := by
    have hh := NonnegativeTotals.Analytic.norm_negative_square hp hq hf
    have hsin := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤2*p*q by positivity)
    linarith
  have hH := hnegative hk (by norm_num : (0:ℝ)<1)
  have hG := hnegative hk hl
  have hB := hnegative hl hm
  have hS := r72_comp θ S11
  have h0 := hzero 0
  have h1 := hzero 1
  have h2 := hzero 2
  have h3 := hzero 3
  obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by revert i; decide
  all_goals
    cases r <;> (try exact absurd rfl hr) <;>
    simp (config := {decide := true}) only [negativeNorm,norms,Certificate.highP,
      Certificate.highNormZero,Certificate.highIndex,Certificate.highProduct,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.head_cons,Matrix.tail_cons,Fin.isValue,
      ↓reduceIte,sub_zero,map_sub,map_add,map_mul,map_pow,map_one,aeval_C,eq_ratCast,
      Rat.cast_ofNat,hS,r72_K,r72_L,r72_M] at h0 h1 h2 h3 ⊢
  all_goals first
    | assumption
    | linarith only [hH]
    | linarith only [hG]
    | linarith only [hB]

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
  have hC := r72_comp θ C10
  cases r <;> (try exact absurd rfl hr) <;>
    simp (config := {decide := true}) only [Certificate.highA,Certificate.highIndex,
      Certificate.highCosineCoefficient,↓reduceIte,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      map_add,map_mul,map_sub,map_one,hC,r72_L,negativeA,one_mul] <;>
    linarith [ht.2.2.2.2.1]

theorem negative_identity (r : HighCase) (hr : r≠.equal) {θ : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Explicit.fullBaseline .high 0 θ 0+Explicit.V .high θ (Certificate.highIndex r) θ=
      negativeA r θ-R*(negativeNorm r θ 0+negativeNorm r θ 1+
        negativeNorm r θ 2+negativeNorm r θ 3) := by
  rw [baseline_identity hθ]
  cases r <;> (try exact absurd rfl hr) <;>
    simp (config := {decide := true}) only [negativeA,negativeNorm,norms,Certificate.highIndex,
      Explicit.V,Explicit.p,Explicit.q,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,↓reduceIte,
      one_mul,OrdinaryAngleConcavity.V,TwoPositive.Certificate.sorted_pair_norm] <;> ring

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
  simp only [equalNorm,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,mul_pow,
    NonnegativeTotals.Analytic.norm_zero_square,Explicit.sec,NegativeELargeA.secant]
  field_simp

theorem equal_norm_bound {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 4) :
    (equalNorm θ i)^2≤aeval (native θ) (Certificate.highP .equal i) := by
  have hf := Explicit.frame_domain .high hθ
  have hcos := NegativeDEPositiveTD.Certificate.cosine_square_upper hf
  have hzero := norm_bounds hθ
  have hC := HighShape.coefficient_majorant hθ
  have hc0 : 0≤c θ := by
    linarith [(Explicit.high_c hθ ⟨by linarith [hθ.1],le_rfl⟩).1,
      (Explicit.high_bounds hθ).m_lower]
  have hC2 := pow_le_pow_left₀ hc0 hC 2
  have hprod := mul_le_mul hC2 hcos (sq_nonneg (Real.cos θ))
    (sq_nonneg (aeval (native θ) Certificate.highC))
  have hC12 := r72_comp θ C12
  obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by revert i; decide
  all_goals simp (config := {decide := true}) only [Certificate.highP,↓reduceIte]
  all_goals try simp only [equalNorm,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,map_mul,map_pow,hC12,mul_pow]
  · exact mul_le_mul hcos (hzero 0) (sq_nonneg _) (sq_nonneg _)
  · exact mul_le_mul hcos (hzero 1) (sq_nonneg _) (sq_nonneg _)
  · exact mul_le_mul hcos (hzero 2) (sq_nonneg _) (sq_nonneg _)
  · change (equalNorm θ 3)^2≤_
    rw [scaled_D_square hf]
    simp only [map_add,map_one,map_mul,map_pow,hC12]
    linarith

theorem equal_nonradical_lower {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    aeval (native θ) (Certificate.highA .equal)≤equalA θ := by
  have ht := taylor_bounds (Explicit.frame_domain .high hθ)
  have hc := NegativeESecant.cos_pos (Explicit.frame_domain .high hθ)
  have hpoly := base_polynomial_positive hθ
  have hbase := sub_le_sub_right (base_lower hθ) 1
  have hpoly' : 0≤aeval (native θ) Certificate.highBase-1 := by
    simpa only [map_sub,map_one] using hpoly.le
  have hprod := mul_le_mul ht.2.2.2.2.1 hbase hpoly' hc.le
  have hs := mul_le_mul_of_nonneg_left ht.2.1 (show (0:ℝ)≤13/12 by norm_num)
  have hK : algebraMap ℚ ℝ Certificate.K=13/12 := by norm_num [Certificate.K]
  simp only [Certificate.highA,↓reduceIte,map_add,map_mul,map_sub,map_one,aeval_C,
    r72_comp,hK]
  simp only [equalA,Explicit.K]
  linarith

theorem equal_identity {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Real.cos θ*Explicit.fullBaseline .high 0 θ θ=
      equalA θ-R*(equalNorm θ 0+equalNorm θ 1+equalNorm θ 2+equalNorm θ 3) := by
  have hc := NegativeESecant.cos_pos (Explicit.frame_domain .high hθ)
  have hid : Explicit.fullBaseline .high 0 θ θ=Explicit.fullBaseline .high 0 θ 0+
      (Explicit.sec θ-1)/2+Explicit.K*Real.tan θ-
        (fullSupport (Explicit.sec θ) (c θ)-fullSupport 1 (c θ)) := by
    simp only [Explicit.fullBaseline,Explicit.sec,NegativeELargeA.secant,Real.cos_zero,
      Real.tan_zero,div_one,zero_add,mul_zero]
    ring
  rw [hid,baseline_identity hθ,fullSupport_pair (c θ) (Explicit.sec θ),
    fullSupport_pair (c θ) 1,pairNorm_symm (c θ) (Explicit.sec θ),pairNorm_symm (c θ) 1]
  simp only [equalA,equalNorm,norms,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  rw [Real.tan_eq_sin_div_cos]
  simp only [Explicit.sec,NegativeELargeA.secant]
  field_simp
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
