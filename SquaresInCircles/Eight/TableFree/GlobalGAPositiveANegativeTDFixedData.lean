module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveANegativeTDASupport

/-!
# The fixed high-A negative-TD2 stress and its intrinsic endpoint reserves

Uncompiled transcription of (14)--(16), (22)--(23), and (36)--(42) in the
positive-A/negative-TD2 hand proof. All displayed decimals are the exact
rational enclosures used there. The fourth coefficient pair repeats H,
as required by the actual sorted-D negative minorant.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveANegativeTD.Fixed
open Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity OrdinaryNegativeSlope

abbrev k : ℝ := 3/4
abbrev l : ℝ := 19/20
abbrev c : ℝ := 27/20
abbrev L : ℝ := 1/6
abbrev span : ℝ := 8/15
abbrev speed : ℝ := (9/10)*c

def p : Fin 4→ℝ := ![k,k,l,k]
def q : Fin 4→ℝ := ![l,1,c,1]

def base : ℝ := k+2*l+2*c+2-
  fullSupport 1 k-fullSupport l k-fullSupport c l-(1+c)*diagonal

def normZeroLower : Fin 4→ℝ := ![12103/10000,5/4,16507/10000,5/4]
def normZeroUpper : Fin 4→ℝ := ![12104/10000,5/4,16508/10000,5/4]
def normLeftUpper : Fin 4→ℝ := ![11085/10000,11462/10000,15165/10000,11462/10000]
def normCapUpper : Fin 4→ℝ := ![7396/10000,7722/10000,10357/10000,7722/10000]
def normSpanUpper : Fin 4→ℝ := ![14797/10000,15249/10000,20073/10000,15249/10000]

theorem coefficients (i : Fin 4) :
    0<p i ∧ p i≤q i ∧ (2/3)*q i≤p i ∧ (3/4:ℝ)≤p i ∧
      (19/20:ℝ)≤q i ∧ q i≤27/20 := by
  fin_cases i <;> norm_num [p,q,k,l,c]

theorem norm_zero (i : Fin 4) :
    normZeroLower i≤pairNorm (p i) (q i) 0 ∧
      pairNorm (p i) (q i) 0≤normZeroUpper i := by
  have hh := coefficients i
  have hs := pairNorm_sq hh.1 (hh.1.trans_le hh.2.1) (t:=0) (by norm_num [frameCap])
  have hp := pairNorm_pos hh.1 (hh.1.trans_le hh.2.1) (t:=0) (by norm_num [frameCap])
  fin_cases i <;>
    norm_num [p,q,normZeroLower,normZeroUpper,k,l,c,pairEnergy,pairProduct] at hs hp ⊢ <;>
    constructor <;> nlinarith

theorem norm_left (i : Fin 4) : pairNorm (p i) (q i) (-L)<normLeftUpper i := by
  have hh := coefficients i
  have hs := pairNorm_sq hh.1 (hh.1.trans_le hh.2.1) (t:= -L) (by norm_num [L,frameCap])
  have hp := pairNorm_pos hh.1 (hh.1.trans_le hh.2.1) (t:= -L) (by norm_num [L,frameCap])
  have ht := sin_lower_seven (show (0:ℝ)≤L by norm_num [L])
  fin_cases i <;>
    norm_num [p,q,normLeftUpper,k,l,c,L,pairEnergy,pairProduct,Real.sin_neg] at hs hp ht ⊢ <;>
    nlinarith

theorem norm_cap (i : Fin 4) : pairNorm (p i) (q i) (-frameCap)<normCapUpper i := by
  have hh := coefficients i
  have hs := pairNorm_sq hh.1 (hh.1.trans_le hh.2.1)
    (t:= -frameCap) (by norm_num [frameCap])
  have hp := pairNorm_pos hh.1 (hh.1.trans_le hh.2.1)
    (t:= -frameCap) (by norm_num [frameCap])
  have ht := cap_trig.1
  fin_cases i <;>
    norm_num [p,q,normCapUpper,k,l,c,pairEnergy,pairProduct,Real.sin_neg,
      Arithmetic.sin7,frameCap] at hs hp ht ⊢ <;> nlinarith

theorem norm_span (i : Fin 4) : pairNorm (p i) (q i) span<normSpanUpper i := by
  have hh := coefficients i
  have hs := pairNorm_sq hh.1 (hh.1.trans_le hh.2.1) (t:=span) (by norm_num [span,frameCap])
  have hp := pairNorm_pos hh.1 (hh.1.trans_le hh.2.1) (t:=span) (by norm_num [span,frameCap])
  have ht := Arithmetic.sin_le_sin9 (show (0:ℝ)≤span by norm_num [span])
  fin_cases i <;>
    norm_num [p,q,normSpanUpper,k,l,c,span,pairEnergy,pairProduct,Arithmetic.sin9] at hs hp ht ⊢ <;>
    nlinarith

theorem radius_norm_zero_lower (i : Fin 4) :
    (1978787/1000000)*normZeroLower i<R*pairNorm (p i) (q i) 0 := by
  have hlo : 0<normZeroLower i := by fin_cases i <;> norm_num [normZeroLower]
  have h₁ := mul_lt_mul_of_pos_right radius_bounds.1 hlo
  have h₂ := mul_le_mul_of_nonneg_left (norm_zero i).1 (Real.sqrt_nonneg qCap)
  linarith

theorem radius_norm_zero_upper (i : Fin 4) :
    R*pairNorm (p i) (q i) 0<(1978788/1000000)*normZeroUpper i := by
  have hhi : 0<normZeroUpper i := by fin_cases i <;> norm_num [normZeroUpper]
  have h₁ := mul_lt_mul_of_pos_right radius_bounds.2 hhi
  have h₂ := mul_le_mul_of_nonneg_left (norm_zero i).2 (Real.sqrt_nonneg qCap)
  linarith

theorem base_lower : -(3/125:ℝ)<base := by
  have hG := radius_norm_zero_upper 0
  have hH := radius_norm_zero_upper 1
  have hB := radius_norm_zero_upper 2
  have hd := diagonal_bounds.2
  rw [base,fullSupport_pair k 1,fullSupport_pair k l,fullSupport_pair l c]
  norm_num [p,q,normZeroUpper,k,l,c] at hG hH hB ⊢
  linarith

theorem negative_endpoint_derivative (i : Fin 4) :
    (4/5:ℝ)<Vd R (p i) (q i) frameCap := by
  have hcoef := coefficients i
  have hN := pairNorm_pos hcoef.1 (hcoef.1.trans_le hcoef.2.1)
    (t:= -frameCap) (by norm_num [frameCap])
  have ht := transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hRcos := mul_le_mul radius_bounds.1.le ht.1.le
    (by norm_num : (0:ℝ)≤7648/10000) (Real.sqrt_nonneg qCap)
  have hqpos : 0<q i := hcoef.1.trans_le hcoef.2.1
  have hsU := mul_le_mul_of_nonneg_left ht.2.2.2.1.le hqpos.le
  have hNp := mul_le_mul
    (show 4/5+q i*Real.sin frameCap≤4/5+q i*(6443/10000) by linarith)
    (norm_cap i).le hN.le (by positivity : 0≤4/5+q i*(6443/10000))
  have hnum := mul_le_mul_of_nonneg_left hRcos
    (mul_nonneg hcoef.1.le hqpos.le)
  have hcross : (4/5+q i*Real.sin frameCap)*pairNorm (p i) (q i) (-frameCap)<
      R*p i*q i*Real.cos frameCap := by
    fin_cases i <;> norm_num [p,q,normCapUpper,k,l,c] at hNp hnum ⊢ <;> nlinarith
  have hd := (lt_div_iff₀ hN).2 hcross
  dsimp [Vd,mixedNDerivative,normD1,pairProduct]
  simp only [zero_sub,Real.cos_neg]
  nlinarith only [hd]

theorem negative_derivative (i : Fin 4) {b : ℝ} (hb : b∈Icc 0 frameCap) :
    (4/5:ℝ)<Vd R (p i) (q i) b := by
  have hc := coefficients i
  exact (negative_endpoint_derivative i).trans_le
    (Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1
      (by linarith [hc.2.2.1]) hb (by norm_num [frameCap]) hb.2)

theorem negative_growth (i : Fin 4) {a b : ℝ}
    (ha : a∈Icc 0 frameCap) (hb : b∈Icc 0 frameCap) (hab : a≤b) :
    (4/5)*(b-a)≤V R (p i) (q i) b-V R (p i) (q i) a := by
  have hc := coefficients i
  exact derivative_reserve
    (fun x hx => (V_hasDerivAt hc.1 (hc.1.trans_le hc.2.1) hx).continuousAt.continuousWithinAt)
    (fun x hx => V_hasDerivAt hc.1 (hc.1.trans_le hc.2.1) (Ioo_subset_Icc_self hx))
    (fun x hx => (negative_derivative i (Ioo_subset_Icc_self hx)).le) ha hb hab

theorem pure_endpoint_reserves (i : Fin 4) :
    (3/500:ℝ)<base+l*TwoPositive.ASupport.charge L+V R (p i) (q i) L ∧
    (3/500:ℝ)<base+l*TwoPositive.ASupport.charge frameCap+V R (p i) (q i) frameCap := by
  have hn0 := radius_norm_zero_lower i
  have hnL := radius_norm_upper
    (show 0<normLeftUpper i by fin_cases i <;> norm_num [normLeftUpper]) (norm_left i)
  have hnh := radius_norm_upper
    (show 0<normCapUpper i by fin_cases i <;> norm_num [normCapUpper]) (norm_cap i)
  have hAL := ABounds.charge_left_lower
  have hAh := ABounds.charge_cap_lower
  have hCL := cos_lower_six (show (0:ℝ)≤L by norm_num [L])
  have hCh := cos_lower_six (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hb := base_lower
  fin_cases i <;>
    norm_num [p,q,normZeroLower,normLeftUpper,normCapUpper,k,l,c,L,frameCap]
      at hn0 hnL hnh hAL hAh hCL hCh ⊢ <;>
    constructor <;> dsimp [V] <;> norm_num [k,l,c,L] at * <;> linarith

theorem positive_endpoint_reserves (i : Fin 4) :
    (8/25:ℝ)<base+l*TwoPositive.ASupport.charge L+speed*frameCap+U R (p i) (q i) span ∧
    (149/1000:ℝ)<base+l*TwoPositive.ASupport.charge frameCap+speed*frameCap := by
  have hn0 := radius_norm_zero_lower i
  have hnD := radius_norm_upper
    (show 0<normSpanUpper i by fin_cases i <;> norm_num [normSpanUpper]) (norm_span i)
  have hAL := ABounds.charge_left_lower
  have hAh := ABounds.charge_cap_lower
  have hC := cos_lower_six (show (0:ℝ)≤span by norm_num [span])
  have hS := sin_lower_seven (show (0:ℝ)≤span by norm_num [span])
  have hb := base_lower
  fin_cases i <;>
    norm_num [p,q,normZeroLower,normSpanUpper,k,l,c,L,span,frameCap]
      at hn0 hnD hAL hAh hC hS ⊢ <;>
    constructor <;> dsimp [U,phi] <;> norm_num [k,l,c,L,span,speed,frameCap] at * <;> linarith

theorem middle_left_reserve :
    (27/1000:ℝ)<base+l*TwoPositive.ASupport.charge L+speed*L := by
  have hb := base_lower
  have hA := ABounds.charge_left_lower
  norm_num [l,speed,c,L] at *
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveANegativeTD.Fixed
