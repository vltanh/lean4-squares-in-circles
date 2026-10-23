module

public import SquaresInCircles.Eight.TableFree.SecondOuterFifthCalculus
public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroContact
public import SquaresInCircles.Eight.TableFree.SecondOuterGeneralReference
public import SquaresInCircles.Eight.TableFree.SecondOuterSourceReference

/-!
# The original P/J stationary curve

Uncompiled source draft.  Angular stationarity determines the target
circle coordinate from the original source coordinate.  The definitions
below retain that exact circle relation; no critical point is selected
or assumed to exist.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def p (t : ℝ) : ℝ := PLabel.d1 t
def E (t : ℝ) : ℝ := PLabel.d2 t-(t-1/2)*(p t)^3
def ED (t : ℝ) : ℝ :=
  PLabel.d3 t-(p t)^3-3*(t-1/2)*(p t)^2*PLabel.d2 t
def criticalU (t : ℝ) : ℝ := (Q0+1-(t-1/2)^2-1/(p t)^2)/2
def criticalV (t : ℝ) : ℝ := Real.sqrt (Q0-(criticalU t)^2)
def criticalRatio (t : ℝ) : ℝ := criticalV t/criticalU t
def criticalRatioD (t : ℝ) : ℝ :=
  -Q0*E t/((criticalU t)^2*criticalV t*(p t)^3)
def sourceInterval : Set ℝ := Icc (3/5) outerDiagonal

lemma source_domain {t : ℝ} (ht : t∈sourceInterval) : t∈Icc 0 outerDiagonal :=
  ⟨by linarith [ht.1],ht.2⟩

lemma p_positive {t : ℝ} (ht : t∈Icc 0 outerDiagonal) : 0<p t := by
  dsimp [p]
  linarith [(P_first_bounds ht).1]

lemma p_hasDerivAt {t : ℝ} (ht : t∈Icc 0 outerDiagonal) :
    HasDerivAt p (PLabel.d2 t) t := PLabel.d1_hasDerivAt (outer_domain ht)

lemma E_hasDerivAt {t : ℝ} (ht : t∈Icc 0 outerDiagonal) :
    HasDerivAt E (ED t) t := by
  convert (PLabel.d2_hasDerivAt (outer_domain ht)).sub
    (((hasDerivAt_id t).sub_const (1/2)).mul ((p_hasDerivAt ht).pow 3)) using 1 <;>
    dsimp [E,ED] <;> ring

lemma criticalU_hasDerivAt {t : ℝ} (ht : t∈Icc 0 outerDiagonal) :
    HasDerivAt criticalU (E t/(p t)^3) t := by
  have hp := p_positive ht
  have hd := (((((hasDerivAt_id t).sub_const (1/2)).pow 2).const_sub
    (Q0+1)).sub ((hasDerivAt_const t (1:ℝ)).div ((p_hasDerivAt ht).pow 2)
      (pow_ne_zero 2 hp.ne'))).div_const 2
  convert hd using 1
  · rfl
  · dsimp [E]
    field_simp [hp.ne']
    ring

lemma criticalV_sq {t : ℝ} (hr : 0≤Q0-(criticalU t)^2) :
    (criticalV t)^2=Q0-(criticalU t)^2 := Real.sq_sqrt hr

lemma criticalRatio_hasDerivAt {t : ℝ} (ht : t∈Icc 0 outerDiagonal)
    (hu : 0<criticalU t) (hr : 0<Q0-(criticalU t)^2) :
    HasDerivAt criticalRatio (criticalRatioD t) t := by
  have hp := p_positive ht
  have hv : 0<criticalV t := Real.sqrt_pos.mpr hr
  have hV := (((criticalU_hasDerivAt ht).pow 2).const_sub Q0).sqrt hr.ne'
  have hd := hV.div (criticalU_hasDerivAt ht) hu.ne'
  convert hd using 1
  · rfl
  · dsimp [criticalRatioD]
    change -Q0*E t/((criticalU t)^2*criticalV t*(p t)^3)=_
    field_simp [hp.ne',hu.ne',hv.ne']
    linear_combination -(E t)*criticalV_sq hr.le

lemma stationary_coordinate {B x : ℝ} (hd : Domain B x)
    (hstat : angleFirst PLabel B x=0) : criticalU (b B x)=U B := by
  have hp := p_positive hd.2.2
  have hv := v_positive hd.1 hd.2.1
  have hvp : p (b B x)*v B x=1 := by
    dsimp [p,angleFirst] at *
    linarith
  have hv2 : (v B x)^2=1/(p (b B x))^2 := by
    apply (eq_div_iff (pow_ne_zero 2 hp.ne')).2
    nlinarith [sq_nonneg (p (b B x)*v B x-1)]
  have hn := norm_identity hd.1 x
  rw [hv2] at hn
  dsimp [criticalU,NegativeTwo.Inverse.q] at *
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ
