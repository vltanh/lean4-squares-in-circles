module

public import SquaresInCircles.Eight.TableFree.OrdinaryAngleConcavity
public import SquaresInCircles.Eight.Arithmetic.Taylor

/-!
# Exact fixed-force radicals for the global high-GA stress

Uncompiled translation of the fixed secondary-owner stress.  The
comparisons are direct positive square comparisons at the intrinsic
ends of the entire frame interval.  They are unrelated to an angle
partition or a generated coefficient inventory.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
open PositiveAngularEnvelope PairNormCalculus

abbrev R : ℝ := Real.sqrt qCap
abbrev k : ℝ := 31/40
abbrev l : ℝ := 31/20
abbrev charge : ℝ := 21/20
abbrev axial : ℝ := Real.sqrt (qCap-1/4)-1/2
abbrev diagonal : ℝ := diagonalCoordinate qCap

theorem radius_sq : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])

theorem radius_bounds : (1978787/1000000:ℝ)<R ∧ R<1978788/1000000 := by
  have hs := radius_sq
  have hp := Real.sqrt_nonneg qCap
  norm_num [qCap] at hs
  constructor <;> nlinarith

theorem axial_bounds : (14145756/10000000:ℝ)<axial ∧ axial<14145757/10000000 := by
  have hs := Real.sq_sqrt (show 0≤qCap-1/4 by norm_num [qCap])
  have hp := Real.sqrt_nonneg (qCap-1/4)
  norm_num [qCap] at hs
  dsimp [axial]
  constructor <;> nlinarith

theorem diagonal_bounds : (8992140/10000000:ℝ)<diagonal ∧ diagonal<8992141/10000000 := by
  have hs := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
  have hp := Real.sqrt_nonneg (qCap/2)
  norm_num [qCap] at hs
  dsimp [diagonal,diagonalCoordinate]
  constructor <;> nlinarith

theorem cap_trig :
    Arithmetic.sin7 frameCap≤Real.sin frameCap ∧
    Real.sin frameCap≤Arithmetic.sin9 frameCap ∧
    1-frameCap^2/2+frameCap^4/24-frameCap^6/720≤Real.cos frameCap ∧
    Real.cos frameCap≤Arithmetic.cos8 frameCap := by
  have hh : (0:ℝ)≤frameCap := by norm_num [frameCap]
  exact ⟨sin_lower_seven hh,Arithmetic.sin_le_sin9 hh,
    cos_lower_six hh,Arithmetic.cos_le_cos8 hh⟩

theorem G_zero_norm :
    (17329526/10000000:ℝ)<pairNorm k l 0 ∧
      pairNorm k l 0<17329527/10000000 := by
  have hs := pairNorm_sq (p:=k) (q:=l) (t:=0)
    (by norm_num [k]) (by norm_num [l]) (by norm_num [frameCap])
  have hp := pairNorm_pos (p:=k) (q:=l) (t:=0)
    (by norm_num [k]) (by norm_num [l]) (by norm_num [frameCap])
  norm_num [pairEnergy,pairProduct,k,l] at hs
  constructor <;> nlinarith

theorem H_zero_norm :
    (12651580/10000000:ℝ)<pairNorm k 1 0 ∧
      pairNorm k 1 0<12651581/10000000 := by
  have hs := pairNorm_sq (p:=k) (q:=1) (t:=0)
    (by norm_num [k]) (by norm_num) (by norm_num [frameCap])
  have hp := pairNorm_pos (p:=k) (q:=1) (t:=0)
    (by norm_num [k]) (by norm_num) (by norm_num [frameCap])
  norm_num [pairEnergy,pairProduct,k] at hs
  constructor <;> nlinarith

theorem G_positive_norm : pairNorm k l frameCap<(21332741/10000000:ℝ) := by
  have hs := pairNorm_sq (p:=k) (q:=l) (t:=frameCap)
    (by norm_num [k]) (by norm_num [l]) (by norm_num [frameCap])
  have ht := cap_trig.2.1
  norm_num [pairEnergy,pairProduct,k,l,Arithmetic.sin9,Arithmetic.sin7,frameCap] at hs ht
  nlinarith [Real.sqrt_nonneg (k^2+l^2+2*k*l*Real.sin frameCap)]

theorem G_negative_norm : pairNorm k l (-frameCap)<(12063965/10000000:ℝ) := by
  have hs := pairNorm_sq (p:=k) (q:=l) (t:= -frameCap)
    (by norm_num [k]) (by norm_num [l]) (by norm_num [frameCap])
  have ht := cap_trig.1
  norm_num [pairEnergy,pairProduct,k,l,Real.sin_neg,Arithmetic.sin7,frameCap] at hs ht
  nlinarith [Real.sqrt_nonneg (k^2+l^2+2*k*l*Real.sin (-frameCap))]

theorem H_positive_norm : pairNorm k 1 frameCap<(16121920/10000000:ℝ) := by
  have hs := pairNorm_sq (p:=k) (q:=1) (t:=frameCap)
    (by norm_num [k]) (by norm_num) (by norm_num [frameCap])
  have ht := cap_trig.2.1
  norm_num [pairEnergy,pairProduct,k,Arithmetic.sin9,Arithmetic.sin7,frameCap] at hs ht
  nlinarith [Real.sqrt_nonneg (k^2+1^2+2*k*1*Real.sin frameCap)]

theorem H_negative_norm : pairNorm k 1 (-frameCap)<(7759432/10000000:ℝ) := by
  have hs := pairNorm_sq (p:=k) (q:=1) (t:= -frameCap)
    (by norm_num [k]) (by norm_num) (by norm_num [frameCap])
  have ht := cap_trig.1
  norm_num [pairEnergy,pairProduct,k,Real.sin_neg,Arithmetic.sin7,frameCap] at hs ht
  nlinarith [Real.sqrt_nonneg (k^2+1^2+2*k*1*Real.sin (-frameCap))]

theorem B_norm_scale (t : ℝ) : pairNorm l 2 t=2*pairNorm k 1 t := by
  unfold pairNorm
  rw [show l^2+2^2+2*l*2*Real.sin t=
    4*(k^2+1^2+2*k*1*Real.sin t) by norm_num [k,l]; ring]
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
  norm_num

theorem radius_norm_lower {n b : ℝ} (hb : 0<b) (hn : b<n) :
    (1978787/1000000)*b<R*n := by
  have hR : 0<R := by linarith [radius_bounds.1]
  exact (mul_lt_mul_of_pos_right radius_bounds.1 hb).trans
    (mul_lt_mul_of_pos_left hn hR)

theorem radius_norm_upper {n b : ℝ} (hb : 0<b) (hn : n<b) :
    R*n<(1978788/1000000)*b := by
  have hR : 0<R := by linarith [radius_bounds.1]
  exact (mul_lt_mul_of_pos_left hn hR).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 hb)

end SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
