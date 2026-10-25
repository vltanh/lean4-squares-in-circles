module

public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeADCorrection
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveASupport
public import SquaresInCircles.Eight.Arithmetic.HighOrderTaylor
public import SquaresInCircles.Eight.Frames.Ordinary.AngleConcavity

/-!
# Eight squares: intrinsic endpoint certificates for the large-A negative-E stress

The three ordinary pairs are H, G, B. The fourth repeats H for the
negative part of the sorted-D minorant. All norm comparisons use positive
squaring and alternating Taylor bounds at the displayed intrinsic angles.
The two combined gains have independent positive endpoint certificates.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeELargeA
open Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open Arithmetic HighOrderTaylor

abbrev L : ℝ := 1/6
abbrev u : ℝ := 1/4
abbrev span : ℝ := 8/15
abbrev radiusLo : ℝ := 1978787507/1000000000
abbrev radiusHi : ℝ := 494696877/250000000
abbrev diagonalHi : ℝ := 449607033/500000000

def p : Fin 4→ℝ := ![k,k,l,k]
def q : Fin 4→ℝ := ![1,l,c,1]
def base : ℝ := k+2*l+2*c+2-
  fullSupport 1 k-fullSupport l k-fullSupport c l-(1+c)*GlobalGA.Secondary.diagonal
def g (s : ℝ) : ℝ := K*Real.sin s-beta*(1-Real.cos s)
def jointGain (w : ℝ) : ℝ := if w≤u then g w else g u+M*(w-u)

def normZeroLower : Fin 4→ℝ := ![1230483/1000000,1161673/1000000,751439/500000,1230483/1000000]
def normZeroUpper : Fin 4→ℝ := ![307621/250000,580837/500000,1502879/1000000,307621/250000]
def normLeftUpper : Fin 4→ℝ := ![141211/125000,1063979/1000000,275453/200000,141211/125000]
def normCapUpper : Fin 4→ℝ := ![384149/500000,355361/500000,923977/1000000,384149/500000]
def normCutPositiveUpper : Fin 4→ℝ := ![639033/500000,603859/500000,195263/125000,639033/500000]
def normCutNegativeUpper : Fin 4→ℝ := ![117948/125000,88283/100000,143073/125000,117948/125000]
def normSpanUpper : Fin 4→ℝ := ![748857/500000,354951/250000,458761/250000,748857/500000]

theorem coefficients (i : Fin 4) :
    0<p i ∧ p i≤q i ∧ (2/3)*q i≤p i ∧ k≤p i ∧ l≤q i ∧ q i≤c := by
  fin_cases i <;> norm_num [p,q,k,l,c]

theorem radius_tight : radiusLo<R ∧ R<radiusHi := by
  have h := radius_sq
  have hpos := Real.sqrt_nonneg qCap
  constructor <;> norm_num [radiusLo,radiusHi,qCap] at * <;> nlinarith

theorem diagonal_tight : GlobalGA.Secondary.diagonal<diagonalHi := by
  have h := diagonal_circle
  have hpos : 0≤GlobalGA.Secondary.diagonal+1/2 := by linarith [diagonal_bounds.1]
  norm_num [diagonalHi,qCap] at *
  nlinarith

theorem norm_zero (i : Fin 4) :
    normZeroLower i<pairNorm (p i) (q i) 0 ∧
      pairNorm (p i) (q i) 0<normZeroUpper i := by
  rw [pairNorm_zero]
  have hl : 0≤normZeroLower i := by fin_cases i <;> norm_num [normZeroLower]
  have hu : 0<normZeroUpper i := by fin_cases i <;> norm_num [normZeroUpper]
  rw [Real.lt_sqrt hl,Real.sqrt_lt' hu]
  fin_cases i <;> norm_num [p,q,normZeroLower,normZeroUpper,k,l,c]

theorem norm_negative_endpoints (i : Fin 4) :
    pairNorm (p i) (q i) (-L)<normLeftUpper i ∧
    pairNorm (p i) (q i) (-frameCap)<normCapUpper i ∧
    pairNorm (p i) (q i) (-(frameCap-u))<normCutNegativeUpper i := by
  have hc := coefficients i
  have hL := pairNorm_sq hc.1 (hc.1.trans_le hc.2.1) (t:= -L) (by norm_num [L,frameCap])
  have hh := pairNorm_sq hc.1 (hc.1.trans_le hc.2.1) (t:= -frameCap) (by norm_num [frameCap])
  have hu := pairNorm_sq hc.1 (hc.1.trans_le hc.2.1) (t:= -(frameCap-u))
    (by norm_num [u,frameCap])
  have hLp := pairNorm_pos hc.1 (hc.1.trans_le hc.2.1) (t:= -L) (by norm_num [L,frameCap])
  have hhp := pairNorm_pos hc.1 (hc.1.trans_le hc.2.1) (t:= -frameCap) (by norm_num [frameCap])
  have hup := pairNorm_pos hc.1 (hc.1.trans_le hc.2.1) (t:= -(frameCap-u))
    (by norm_num [u,frameCap])
  have hSL := S11_le_sin (show (0:ℝ)≤L by norm_num [L])
  have hSh := S11_le_sin (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hSu := S11_le_sin (show (0:ℝ)≤frameCap-u by norm_num [u,frameCap])
  fin_cases i <;>
    norm_num [p,q,normLeftUpper,normCapUpper,normCutNegativeUpper,k,l,c,L,u,frameCap,
      pairEnergy,pairProduct,Real.sin_neg,S11,sin9,sin7] at hL hh hu hLp hhp hup hSL hSh hSu ⊢ <;>
    constructor <;> first | nlinarith | constructor <;> nlinarith

theorem norm_positive_endpoints (i : Fin 4) :
    pairNorm (p i) (q i) (u-L)<normCutPositiveUpper i ∧
    pairNorm (p i) (q i) span<normSpanUpper i := by
  have hc := coefficients i
  have hu := pairNorm_sq hc.1 (hc.1.trans_le hc.2.1) (t:=u-L) (by norm_num [u,L,frameCap])
  have hh := pairNorm_sq hc.1 (hc.1.trans_le hc.2.1) (t:=span) (by norm_num [span,frameCap])
  have hup := pairNorm_pos hc.1 (hc.1.trans_le hc.2.1) (t:=u-L) (by norm_num [u,L,frameCap])
  have hhp := pairNorm_pos hc.1 (hc.1.trans_le hc.2.1) (t:=span) (by norm_num [span,frameCap])
  have hSu := sin_le_sin9 (show (0:ℝ)≤u-L by norm_num [u,L])
  have hSh := sin_le_sin9 (show (0:ℝ)≤ span by norm_num [span])
  fin_cases i <;>
    norm_num [p,q,normCutPositiveUpper,normSpanUpper,k,l,c,u,L,span,
      pairEnergy,pairProduct,sin9,sin7] at hu hh hup hhp hSu hSh ⊢ <;>
    constructor <;> nlinarith

theorem radius_norm_upper {n b : ℝ} (hb : 0<b) (hn : n≤b) : R*n<radiusHi*b := by
  have h₁ := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg qCap)
  have h₂ := mul_lt_mul_of_pos_right radius_tight.2 hb
  exact h₁.trans_lt h₂

theorem radius_norm_zero_lower (i : Fin 4) :
    radiusLo*normZeroLower i<R*pairNorm (p i) (q i) 0 := by
  have hlo : 0<normZeroLower i := by fin_cases i <;> norm_num [normZeroLower]
  have h₁ := mul_lt_mul_of_pos_right radius_tight.1 hlo
  have h₂ := mul_le_mul_of_nonneg_left (norm_zero i).1.le (Real.sqrt_nonneg qCap)
  exact h₁.trans_le h₂

theorem base_lower : -(2093/100000:ℝ)<base := by
  have hH := radius_norm_upper
    (show 0<normZeroUpper 0 by norm_num [normZeroUpper]) (norm_zero 0).2.le
  have hG := radius_norm_upper
    (show 0<normZeroUpper 1 by norm_num [normZeroUpper]) (norm_zero 1).2.le
  have hB := radius_norm_upper
    (show 0<normZeroUpper 2 by norm_num [normZeroUpper]) (norm_zero 2).2.le
  have hd := diagonal_tight
  rw [base,fullSupport_pair k 1,fullSupport_pair k l,fullSupport_pair l c]
  norm_num [p,q,normZeroUpper,k,l,c,radiusHi,diagonalHi] at hH hG hB hd ⊢
  linarith

theorem charge_short {a : ℝ} (ha : a=L ∨ a=u) :
    (if a=L then -(7933/50000:ℝ) else -(12091/50000))<TwoPositive.ASupport.charge a := by
  have ha0 : 0≤a := by rcases ha with rfl|rfl <;> norm_num [L,u]
  have haα : a≤TwoPositive.ASupport.alpha := by
    rcases ha with rfl|rfl <;> dsimp [L,u] <;> linarith [TwoPositive.ASupport.alpha_bounds.1]
  rw [TwoPositive.ASupport.charge,ite_eq_left haα]
  have hC := cos10_le_cos ha0
  have hS := sin_le_sin9 ha0
  have hs0 : 0≤Real.sin a := (transport_trig (show a∈Icc 0 frameCap by
    rcases ha with rfl|rfl <;> norm_num [L,u,frameCap])).2.2.1
  have hm := mul_le_mul_of_nonneg_right
    (show axial-1/2≤114322/125000 by linarith [axial_bounds.2]) hs0
  rcases ha with rfl|rfl <;>
    norm_num [L,u,cos10,cos8,sin9,sin7,TwoPositive.ASupport.axialCharge] at hC hS hm ⊢ <;>
    linarith

theorem charge_cap_lower : -(71283/100000:ℝ)<TwoPositive.ASupport.charge frameCap := by
  rw [TwoPositive.ASupport.charge,ite_eq_right (not_le.mpr TwoPositive.ASupport.alpha_bounds.2)]
  dsimp only [TwoPositive.ASupport.circleCharge]
  rw [show frameCap/2=7/20 by norm_num [frameCap],show frameCap=7/10 from rfl]
  have hS := S11_le_sin (show (0:ℝ)≤7/10 by norm_num)
  have hH := sin_le_sin9 (show (0:ℝ)≤7/20 by norm_num)
  have hs0 := (TwoPositive.ASupport.half_trig
    (show (7/10:ℝ)∈Icc 0 frameCap by norm_num [frameCap])).1
  rw [show (7/10:ℝ)/2=7/20 by norm_num] at hs0
  have hm := mul_le_mul_of_nonneg_right radius_tight.2.le hs0
  norm_num [S11,sin9,sin7] at hS hH
  simp only [radiusHi] at hm
  linarith

theorem gain_endpoints : (17063/100000:ℝ)<g L ∧ (12381/50000:ℝ)<g u := by
  have hSL := S11_le_sin (show (0:ℝ)≤L by norm_num [L])
  have hCL := cos10_le_cos (show (0:ℝ)≤L by norm_num [L])
  have hSu := S11_le_sin (show (0:ℝ)≤u by norm_num [u])
  have hCu := cos10_le_cos (show (0:ℝ)≤u by norm_num [u])
  norm_num [L,u,S11,sin9,sin7,cos10,cos8] at hSL hCL hSu hCu
  constructor <;> dsimp [g,K,beta] <;> linarith

def leftReserve : Fin 4→ℝ := ![491/25000,147/10000,413/6250,491/25000]
def capReserve : Fin 4→ℝ := ![139/20000,247/50000,4813/25000,139/20000]
def cutPositiveReserve : Fin 4→ℝ := ![4471/100000,191/4000,1869/50000,4471/100000]
def cutNegativeReserve : Fin 4→ℝ := ![1083/25000,1797/50000,8269/50000,1083/25000]
def jointCapReserve : Fin 4→ℝ := ![28807/100000,3826/12500,23237/100000,28807/100000]
def linearCapReserve : Fin 4→ℝ := ![3017/10000,31971/100000,123/500,3017/10000]

theorem negative_endpoint_reserves (i : Fin 4) :
    leftReserve i<base+l*TwoPositive.ASupport.charge L+V R (p i) (q i) L ∧
    capReserve i<base+l*TwoPositive.ASupport.charge frameCap+V R (p i) (q i) frameCap ∧
    cutNegativeReserve i<base+l*TwoPositive.ASupport.charge frameCap+g u+
      V R (p i) (q i) (frameCap-u) := by
  have hn0 := radius_norm_zero_lower i
  have hnL := radius_norm_upper
    (show 0<normLeftUpper i by fin_cases i <;> norm_num [normLeftUpper]) (norm_negative_endpoints i).1.le
  have hnh := radius_norm_upper
    (show 0<normCapUpper i by fin_cases i <;> norm_num [normCapUpper]) (norm_negative_endpoints i).2.1.le
  have hnu := radius_norm_upper
    (show 0<normCutNegativeUpper i by fin_cases i <;> norm_num [normCutNegativeUpper])
    (norm_negative_endpoints i).2.2.le
  have hAL : -(7933/50000:ℝ)<TwoPositive.ASupport.charge L := by
    simpa using charge_short (a:=L) (Or.inl rfl)
  have hAh := charge_cap_lower
  have hgu := gain_endpoints.2
  have hCL := cos10_le_cos (show (0:ℝ)≤L by norm_num [L])
  have hCh := cos10_le_cos (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hCu := cos10_le_cos (show (0:ℝ)≤frameCap-u by norm_num [frameCap,u])
  have hb := base_lower
  simp only [V]
  fin_cases i <;>
    norm_num [p,q,normZeroLower,normLeftUpper,normCapUpper,normCutNegativeUpper,
      k,l,c,L,u,frameCap,radiusLo,radiusHi,cos10,cos8,leftReserve,capReserve,cutNegativeReserve]
      at hn0 hnL hnh hnu hAL hAh hgu hCL hCh hCu hb ⊢ <;>
    refine ⟨?_,?_,?_⟩ <;> linarith

theorem positive_endpoint_reserves (i : Fin 4) :
    cutPositiveReserve i<base+l*TwoPositive.ASupport.charge L+g u+U R (p i) (q i) (u-L) ∧
    jointCapReserve i<base+l*TwoPositive.ASupport.charge L+g u+M*(frameCap-u)+
      U R (p i) (q i) span ∧
    linearCapReserve i<base+l*TwoPositive.ASupport.charge L+M*frameCap+
      U R (p i) (q i) span := by
  have hn0 := radius_norm_zero_lower i
  have hnu := radius_norm_upper
    (show 0<normCutPositiveUpper i by fin_cases i <;> norm_num [normCutPositiveUpper])
    (norm_positive_endpoints i).1.le
  have hnh := radius_norm_upper
    (show 0<normSpanUpper i by fin_cases i <;> norm_num [normSpanUpper])
    (norm_positive_endpoints i).2.le
  have hAL : -(7933/50000:ℝ)<TwoPositive.ASupport.charge L := by
    simpa using charge_short (a:=L) (Or.inl rfl)
  have hgu := gain_endpoints.2
  have hCu := cos10_le_cos (show (0:ℝ)≤u-L by norm_num [u,L])
  have hSu := S11_le_sin (show (0:ℝ)≤u-L by norm_num [u,L])
  have hCh := cos10_le_cos (show (0:ℝ) ≤ span by norm_num [span])
  have hSh := S11_le_sin (show (0:ℝ) ≤ span by norm_num [span])
  have hb := base_lower
  simp only [U,PositiveAngularEnvelope.phi]
  fin_cases i <;>
    norm_num [p,q,normZeroLower,normCutPositiveUpper,normSpanUpper,k,l,c,M,L,u,span,frameCap,
      radiusLo,radiusHi,cos10,cos8,S11,sin9,sin7,cutPositiveReserve,jointCapReserve,linearCapReserve]
      at hn0 hnu hnh hAL hgu hCu hSu hCh hSh hb ⊢ <;>
    refine ⟨?_,?_,?_⟩ <;> linarith

theorem zero_increment_reserves :
    (117/25000:ℝ)<base+l*TwoPositive.ASupport.charge L+g L ∧
    (283/50000:ℝ)<base+l*TwoPositive.ASupport.charge u+g u ∧
    (907/20000:ℝ)<base+l*TwoPositive.ASupport.charge frameCap+g u+M*(frameCap-u) ∧
    (411/50000:ℝ)<base+l*TwoPositive.ASupport.charge L+M*L ∧
    (369/6250:ℝ)<base+l*TwoPositive.ASupport.charge frameCap+M*frameCap := by
  have hb := base_lower
  have hAL : -(7933/50000:ℝ)<TwoPositive.ASupport.charge L := by
    simpa using charge_short (a:=L) (Or.inl rfl)
  have hAu : -(12091/50000:ℝ)<TwoPositive.ASupport.charge u := by
    simpa [L,u] using charge_short (a:=u) (Or.inr rfl)
  have hAh := charge_cap_lower
  have hgL := gain_endpoints.1
  have hgu := gain_endpoints.2
  norm_num [l,L,u,M,frameCap] at *
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

end SquaresInCircles.Eight.GlobalGA.NegativeELargeA
