module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2SignedCurvature

/-!
# The ordinary curvature constants used by the negative-A angle argument

Uncompiled transcription of (20)--(23) in the angle companion. The lower
bound on the first curvature derivative uses its displayed interior
minimum. The three restricted-ratio rows are positive-square comparisons
at the prescribed coefficient endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Curvature
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds

def shapeC1q (r : ℝ) : ℝ := R*r*(1-r^2+r^4)/(shape r)^5
def shapeD0q (r : ℝ) : ℝ := R*r/shape r
def criticalSquare : ℝ := (7+Real.sqrt 21)/14
def criticalRatio : ℝ := Real.sqrt criticalSquare

theorem radius_bounds : (197/100:ℝ)<R ∧ R<(494697/250000:ℝ) := by
  constructor
  · exact (Real.lt_sqrt (by norm_num)).mpr (by norm_num [qCap])
  · exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num [qCap])

theorem shapeC0q_hasDerivAt (r : ℝ) :
    HasDerivAt (shapeC0q R) (R*r*(2-r^2)/(shape r)^5) r := by
  have hraw := (((hasDerivAt_id r).pow 2).const_mul R).div
    ((shape_hasDerivAt r).pow 3) (pow_ne_zero 3 (shape_pos r).ne')
  have hs := (shape_pos r).ne'
  refine hraw.congr_deriv ?_
  rw [show R*r*(2-r^2)/(shape r)^5=R*r*(2*(shape r)^2-3*r^2)/(shape r)^5 by
    rw [shape_sq]; ring]
  simp only [Pi.pow_apply,id]
  field_simp
  ring

theorem shapeC1q_hasDerivAt (r : ℝ) :
    HasDerivAt shapeC1q (R*(1-7*r^2+7*r^4)/(shape r)^7) r := by
  have hnum := ((hasDerivAt_id r).const_mul R).mul
    (((hasDerivAt_const r (1:ℝ)).sub ((hasDerivAt_id r).pow 2)).add ((hasDerivAt_id r).pow 4))
  have hraw := hnum.div ((shape_hasDerivAt r).pow 5) (pow_ne_zero 5 (shape_pos r).ne')
  have hs := (shape_pos r).ne'
  refine hraw.congr_deriv ?_
  rw [show R*(1-7*r^2+7*r^4)/(shape r)^7=
      R*((1-3*r^2+5*r^4)*(shape r)^2-5*r^2*(1-r^2+r^4))/(shape r)^7 by
    rw [shape_sq]; ring]
  simp only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,id]
  field_simp
  ring

theorem shapeD0q_hasDerivAt (r : ℝ) :
    HasDerivAt shapeD0q (R/(shape r)^3) r := by
  have hraw := ((hasDerivAt_id r).const_mul R).div (shape_hasDerivAt r) (shape_pos r).ne'
  have hs := (shape_pos r).ne'
  refine hraw.congr_deriv ?_
  rw [show R/(shape r)^3=R*((shape r)^2-r^2)/(shape r)^3 by rw [shape_sq]; ring]
  simp only [id]
  field_simp

theorem shapeC0q_monotone : MonotoneOn (shapeC0q R) (Icc (0:ℝ) 1) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun r _ => (shapeC0q_hasDerivAt r).continuousAt.continuousWithinAt)
    (fun r _ => shapeC0q_hasDerivAt r)
  intro r hr
  have hr2 : r^2≤1 := by
    simpa using pow_le_pow_left₀ hr.1.le hr.2.le 2
  exact div_nonneg
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg qCap) hr.1.le) (by linarith))
    (pow_nonneg (shape_pos r).le 5)

theorem shapeD0q_monotone : MonotoneOn shapeD0q (Icc (0:ℝ) 1) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun r _ => (shapeD0q_hasDerivAt r).continuousAt.continuousWithinAt)
    (fun r _ => shapeD0q_hasDerivAt r)
  intro r hr
  exact div_nonneg (Real.sqrt_nonneg qCap) (pow_nonneg (shape_pos r).le 3)

theorem shapeC1q_restricted_antitone :
    AntitoneOn shapeC1q (Icc (1/2:ℝ) (21/25:ℝ)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun r _ => (shapeC1q_hasDerivAt r).continuousAt.continuousWithinAt)
    (fun r _ => shapeC1q_hasDerivAt r)
  intro r hr
  have hr0 : 0≤r := by linarith [hr.1]
  have hrlo : (1/4:ℝ)≤r^2 := by nlinarith [hr.1]
  have hrhi : r^2≤(3/4:ℝ) := by
    have hh := pow_le_pow_left₀ hr0 hr.2.le 2
    nlinarith
  have hprod := mul_nonpos_of_nonneg_of_nonpos
    (sub_nonneg.mpr hrlo) (sub_nonpos.mpr hrhi)
  have hnum : 1-7*r^2+7*r^4≤0 := by nlinarith
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg qCap) hnum)
    (pow_nonneg (shape_pos r).le 7)

theorem critical_data :
    (827/1000:ℝ)<criticalSquare ∧ criticalSquare<(207/250:ℝ) ∧
    (909/1000:ℝ)<criticalRatio ∧ criticalRatio<1 ∧
    criticalRatio^2=criticalSquare ∧
    1-criticalSquare+criticalSquare^2=(6/7:ℝ) := by
  have hs0 := Real.sqrt_nonneg (21:ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤21)
  have hlo : (827/1000:ℝ)<criticalSquare := by
    dsimp [criticalSquare]
    nlinarith
  have hhi : criticalSquare<(207/250:ℝ) := by
    dsimp [criticalSquare]
    nlinarith
  have hcrit0 : 0≤criticalRatio := Real.sqrt_nonneg criticalSquare
  have hcrit2 : criticalRatio^2=criticalSquare :=
    Real.sq_sqrt (by linarith)
  refine ⟨hlo,hhi,?_,?_,hcrit2,?_⟩
  · nlinarith
  · nlinarith
  · dsimp [criticalSquare]
    nlinarith

theorem critical_is_minimum {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    shapeC1q criticalRatio≤ shapeC1q r := by
  obtain ⟨hcL,hcU,hcrL,hcrU,hcr2,hcEq⟩ := critical_data
  have hroot : 1-7*criticalSquare+7*criticalSquare^2=0 := by linarith
  have hpoly (r : ℝ) : 1-7*r^2+7*r^4=
      7*(r^2-criticalSquare)*(r^2+criticalSquare-1) := by
    linear_combination hroot
  by_cases hrc : r≤criticalRatio
  · have hm : AntitoneOn shapeC1q (Icc (1/2:ℝ) criticalRatio) := by
      apply antiOn_of_hasDeriv_nonpos
        (fun r _ => (shapeC1q_hasDerivAt r).continuousAt.continuousWithinAt)
        (fun r _ => shapeC1q_hasDerivAt r)
      intro r hr'
      have hr0 : 0≤r := by linarith [hr'.1]
      have hhi : r^2≤criticalSquare := by
        have hh := pow_le_pow_left₀ hr0 hr'.2.le 2
        nlinarith
      have hnum : 1-7*r^2+7*r^4≤0 := by
        rw [hpoly]
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sub_nonpos.mpr hhi))
          (by nlinarith [hr'.1])
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg qCap) hnum)
        (pow_nonneg (shape_pos r).le 7)
    exact hm ⟨hr.1,hrc⟩ ⟨by linarith,le_rfl⟩ hrc
  · have hrc' : criticalRatio≤r := (lt_of_not_ge hrc).le
    have hm : MonotoneOn shapeC1q (Icc criticalRatio 1) := by
      apply monoOn_of_hasDeriv_nonneg
        (fun r _ => (shapeC1q_hasDerivAt r).continuousAt.continuousWithinAt)
        (fun r _ => shapeC1q_hasDerivAt r)
      intro r hr'
      have hcrit0 : 0≤criticalRatio := Real.sqrt_nonneg criticalSquare
      have hlo : criticalSquare≤r^2 := by
        have hh := pow_le_pow_left₀ hcrit0 hr'.1.le 2
        nlinarith
      have hnum : 0≤1-7*r^2+7*r^4 := by
        rw [hpoly]
        exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hlo))
          (by linarith)
      exact div_nonneg (mul_nonneg (Real.sqrt_nonneg qCap) hnum)
        (pow_nonneg (shape_pos r).le 7)
    exact hm ⟨le_rfl,hcrU.le⟩ ⟨hrc',hr.2⟩ hrc'

theorem critical_lower : (1/3:ℝ)<shapeC1q criticalRatio := by
  obtain ⟨hcL,hcU,hcrL,hcrU,hcr2,hcEq⟩ := critical_data
  have hn0 := shape_pos criticalRatio
  have hn2 := shape_sq criticalRatio
  have hnU : shape criticalRatio<(1353/1000:ℝ) := by nlinarith
  have hs : (shape criticalRatio)^5=(1+criticalSquare)^2*shape criticalRatio := by
    calc
      (shape criticalRatio)^5=((shape criticalRatio)^2)^2*shape criticalRatio := by ring
      _=(1+criticalSquare)^2*shape criticalRatio := by rw [shape_sq,hcr2]
  have hden : (shape criticalRatio)^5<
      (457/250:ℝ)^2*(1353/1000:ℝ) := by
    rw [hs]
    have ha0 : 0≤1+criticalSquare := by linarith
    have ha2 : (1+criticalSquare)^2<(457/250:ℝ)^2 := by nlinarith
    exact mul_lt_mul'' ha2 hnU (sq_nonneg _) hn0.le
  have hnum : (197/100:ℝ)*(909/1000:ℝ)*(6/7:ℝ)<
      R*criticalRatio*(1-criticalRatio^2+criticalRatio^4) := by
    have hp : 1-criticalRatio^2+criticalRatio^4=(6/7:ℝ) := by
      rw [show criticalRatio^4=(criticalRatio^2)^2 by ring,hcr2]
      exact hcEq
    rw [hp]
    exact mul_lt_mul_of_pos_right
      (mul_lt_mul'' radius_bounds.1 hcrL (by norm_num) (by norm_num))
      (by norm_num)
  have hreserve : (0:ℝ)<
      3*(197/100:ℝ)*(6/7:ℝ)*(909/1000:ℝ)-(457/250:ℝ)^2*(1353/1000:ℝ) := by
    norm_num
  unfold shapeC1q
  apply (lt_div_iff₀ (pow_pos hn0 5)).2
  linarith

theorem shapeC1q_lower {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    (1/3:ℝ)<shapeC1q r := critical_lower.trans_le (critical_is_minimum hr)

theorem shapeD0q_upper {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    shapeD0q r<(7/5:ℝ) := by
  have hm := shapeD0q_monotone ⟨by linarith [hr.1],hr.2⟩
    (show (1:ℝ)∈Icc (0:ℝ) 1 by norm_num) hr.2
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have he : shapeD0q 1<(7/5:ℝ) := by
    unfold shapeD0q
    apply quotient_lt_of_square (shape_pos 1) (by norm_num)
    rw [shape_sq]
    norm_num [qCap] at hR2 ⊢
    nlinarith
  exact hm.trans_lt he

theorem constants_normalize {p q : ℝ} (hp : 0<p) (hq : 0<q) :
    curvatureSlope R p q=q*shapeC1q (p/q) ∧
    slopeZero p q=q*shapeD0q (p/q) := by
  obtain ⟨_,hC1,_,_⟩ := curvature_constants_normalize (R:=R) hp hq
  constructor
  · rw [hC1]
    unfold shapeC1p shapeC1q
    field_simp
  · have hN : pairNorm p q 0=q*shape (p/q) := by
      rw [pairNorm_zero]
      have he : p^2+q^2=q^2*(1+(p/q)^2) := by field_simp; ring
      rw [he,Real.sqrt_mul (sq_nonneg q),Real.sqrt_sq hq.le]
      rfl
    unfold slopeZero shapeD0q pairProduct
    rw [hN]
    field_simp [(shape_pos (p/q)).ne']

theorem universal_constants {p q : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) :
    curvatureZero R p q<(7/10:ℝ)*q ∧
    (1/3:ℝ)*q<curvatureSlope R p q ∧
    slopeZero p q<(7/5:ℝ)*q := by
  have hq := hp.trans_le hpq
  have hr : p/q∈Icc (1/2:ℝ) 1 := by
    constructor
    · exact (le_div_iff₀ hq).2 (by linarith)
    · exact (div_le_one hq).2 hpq
  obtain ⟨hC1,hD0⟩ := constants_normalize hp hq
  obtain ⟨_,_,hC0,_⟩ := curvature_constants_normalize (R:=R) hp hq
  refine ⟨?_,?_,?_⟩
  · rw [hC0]
    exact (mul_lt_mul_of_pos_left
      (shapeC0q_lt (le_of_eq (Real.sq_sqrt (by norm_num [qCap]))) hr) hq).trans_eq
        (mul_comm q (7/10:ℝ))
  · rw [hC1]
    simpa [mul_comm] using mul_lt_mul_of_pos_left (shapeC1q_lower hr) hq
  · rw [hD0]
    simpa [mul_comm] using mul_lt_mul_of_pos_left (shapeD0q_upper hr) hq

inductive Restricted where
  | wide | middle | narrow
  deriving DecidableEq

instance : Fintype Restricted where
  elems := {.wide, .middle, .narrow}
  complete x := by cases x <;> decide

def ratioEnd : Restricted→ℚ
  | .wide=>21/25 | .middle=>187/250 | .narrow=>33/50
def C0End : Restricted→ℚ
  | .wide=>627/1000 | .middle=>569/1000 | .narrow=>251/500
def D0End : Restricted→ℚ
  | .wide=>1273/1000 | .middle=>593/500 | .narrow=>109/100

theorem restricted_square_reserves (j : Restricted) :
    (0:ℚ)<C0End j ∧ 0<D0End j ∧
    0<(C0End j)^2*(1+(ratioEnd j)^2)^3-
      (39156/10000:ℚ)*(ratioEnd j)^4 ∧
    0<(D0End j)^2*(1+(ratioEnd j)^2)-
      (39156/10000:ℚ)*(ratioEnd j)^2 := by
  cases j <;> norm_num [C0End,D0End,ratioEnd]

theorem restricted_endpoints (j : Restricted) :
    shapeC0q R (ratioEnd j)<(C0End j:ℝ) ∧
    shapeD0q (ratioEnd j)<(D0End j:ℝ) := by
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hsq0 : R^2*(ratioEnd j:ℝ)^4<
      (C0End j:ℝ)^2*(1+(ratioEnd j:ℝ)^2)^3 := by
    have hh : ((39156/10000*ratioEnd j^4:ℚ):ℝ)<((C0End j^2*(1+ratioEnd j^2)^3:ℚ):ℝ) := by
      exact_mod_cast sub_pos.mp (restricted_square_reserves j).2.2.1
    push_cast at hh
    rw [hR2,show qCap=39156/10000 by norm_num [qCap]]
    exact hh
  have hsqD : R^2*(ratioEnd j:ℝ)^2<
      (D0End j:ℝ)^2*(1+(ratioEnd j:ℝ)^2) := by
    have hh : ((39156/10000*ratioEnd j^2:ℚ):ℝ)<((D0End j^2*(1+ratioEnd j^2):ℚ):ℝ) := by
      exact_mod_cast sub_pos.mp (restricted_square_reserves j).2.2.2
    push_cast at hh
    rw [hR2,show qCap=39156/10000 by norm_num [qCap]]
    exact hh
  constructor
  · unfold shapeC0q
    apply quotient_lt_of_square (pow_pos (shape_pos _) 3)
      (by exact_mod_cast (restricted_square_reserves j).1)
    calc
      (R*(ratioEnd j:ℝ)^2)^2=R^2*(ratioEnd j:ℝ)^4 := by ring
      _<(C0End j:ℝ)^2*(1+(ratioEnd j:ℝ)^2)^3 := hsq0
      _=(C0End j:ℝ)^2*((shape (ratioEnd j))^3)^2 := by
        rw [show ((shape (ratioEnd j))^3)^2=((shape (ratioEnd j))^2)^3 by ring,shape_sq]
  · unfold shapeD0q
    apply quotient_lt_of_square (shape_pos _)
      (by exact_mod_cast (restricted_square_reserves j).2.1)
    simpa [mul_pow,shape_sq] using hsqD

theorem wide_C1_endpoint : (173/500:ℝ)<shapeC1q (21/25:ℝ) := by
  have hR0 : 0<R := lt_trans (by norm_num) radius_bounds.1
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hnum0 : 0<R*(21/25:ℝ)*(1-(21/25:ℝ)^2+(21/25:ℝ)^4) := by positivity
  have hden0 := pow_pos (shape_pos (21/25:ℝ)) 5
  have hsq : ((173/500:ℝ)*(shape (21/25:ℝ))^5)^2<
      (R*(21/25:ℝ)*(1-(21/25:ℝ)^2+(21/25:ℝ)^4))^2 := by
    have hp : ((shape (21/25:ℝ))^5)^2=(1+(21/25:ℝ)^2)^5 := by
      rw [show ((shape (21/25:ℝ))^5)^2=((shape (21/25:ℝ))^2)^5 by ring,shape_sq]
    simp only [mul_pow,hp,hR2]
    norm_num [qCap]
  unfold shapeC1q
  apply (lt_div_iff₀ hden0).2
  exact lt_of_pow_lt_pow_left₀ 2 hnum0.le hsq

theorem restricted_constants (j : Restricted) {p q : ℝ}
    (hp : 0<p) (hpq : p≤q) (hpr : p≤(ratioEnd j:ℝ)*q) :
    curvatureZero R p q<(C0End j:ℝ)*q ∧
    slopeZero p q<(D0End j:ℝ)*q := by
  have hq := hp.trans_le hpq
  have hr0 : 0≤p/q := div_nonneg hp.le hq.le
  have hr1 : p/q≤1 := (div_le_one hq).2 hpq
  have hre : p/q≤(ratioEnd j:ℝ) := (div_le_iff₀ hq).2 hpr
  have he : (ratioEnd j:ℝ)∈Icc (0:ℝ) 1 := by
    cases j <;> norm_num [ratioEnd]
  obtain ⟨_,_,hC0,_⟩ := curvature_constants_normalize (R:=R) hp hq
  obtain ⟨_,hD0⟩ := constants_normalize hp hq
  constructor
  · rw [hC0]
    have hh := (shapeC0q_monotone ⟨hr0,hr1⟩ he hre).trans_lt
      (restricted_endpoints j).1
    simpa [mul_comm] using mul_lt_mul_of_pos_left hh hq
  · rw [hD0]
    have hh := (shapeD0q_monotone ⟨hr0,hr1⟩ he hre).trans_lt
      (restricted_endpoints j).2
    simpa [mul_comm] using mul_lt_mul_of_pos_left hh hq

theorem restricted_C1 {p q : ℝ} (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hpr : p≤(21/25:ℝ)*q) :
    (173/500:ℝ)*q<curvatureSlope R p q := by
  have hq := hp.trans_le hpq
  have hr : p/q∈Icc (1/2:ℝ) (21/25:ℝ) := by
    exact ⟨(le_div_iff₀ hq).2 (by linarith),(div_le_iff₀ hq).2 hpr⟩
  have hm := shapeC1q_restricted_antitone hr
    (show (21/25:ℝ)∈Icc (1/2:ℝ) (21/25:ℝ) by norm_num) hr.2
  rw [(constants_normalize hp hq).1]
  simpa [mul_comm] using mul_lt_mul_of_pos_left (wide_C1_endpoint.trans_le hm) hq

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Curvature
