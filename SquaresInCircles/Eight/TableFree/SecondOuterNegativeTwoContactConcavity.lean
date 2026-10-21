module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoContactPolynomials
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoContactInverse

/-!
# Strict concavity of the actual fixed-target inverse contact

The target is kept fixed on its original circle.  The two geometric
source halves use the exact polynomials proved in the preceding module,
the source circle, and the inverse-contact norm identity.  Together they
prove strict concavity on the complete closed source interval, including
both signs of the shifted target coordinate.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.ContactCurvature

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open Inverse (q N K brace factorD)

lemma circle_ratio {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (U b)^2+(ratio b)^2*(U b)^2=Q0 := by
  have hu := U_positive (outer_domain hb)
  have hr : ratio b*U b=W b := by
    change (W b/U b)*U b=W b
    field_simp [hu.ne']
  have hr2 : (ratio b)^2*(U b)^2=(W b)^2 := by
    calc
      _=(ratio b*U b)^2 := by ring
      _=(W b)^2 := by rw [hr]
  rw [hr2]
  exact UW_circle (outer_domain hb)

lemma late_coordinate {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (hhalf : 1/2≤b) :
    U b∈ContactPolynomial.late := by
  have hu := UW_bounds hb
  have hc := UW_circle (outer_domain hb)
  have hw : 1≤W b := by dsimp [W]; linarith
  refine ⟨hu.1.le,?_⟩
  norm_num [Q0] at hc
  nlinarith

lemma early_coordinate {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (hhalf : b≤1/2) :
    U b∈ContactPolynomial.early := by
  have hu := UW_bounds hb
  have hc := UW_circle (outer_domain hb)
  have hw : W b≤1 := by dsimp [W]; linarith
  refine ⟨?_,hu.2.1.le⟩
  norm_num [Q0] at hc
  nlinarith [hu.2.2.1]

lemma late_speed_data {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hhalf : 1/2≤b)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    (3739/2500:ℝ)≤q (U b) ∧ (1557/1250:ℝ)≤(ContactInverse.speed z b)^2 ∧
      (223/200:ℝ)<ContactInverse.speed z b := by
  have hd := ContactInverse.data hb hz
  have hu := late_coordinate hb hhalf
  have hq : (3739/2500:ℝ)≤q (U b) := by
    norm_num [q,Inverse.q,Q0]
    linarith [hu.2]
  have hz2 : z^2≤(1/4:ℝ) := by nlinarith [hz.1,hz.2]
  have hv2 : (1557/1250:ℝ)≤(ContactInverse.speed z b)^2 := by
    linarith [hd.2.2.2.2.2]
  exact ⟨hq,hv2,by nlinarith [hd.2.2.2.2.1]⟩

lemma late_brace {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hhalf : 1/2≤b)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    |brace (U b) (ratio b) (ContactInverse.speed z b)|<(7/50:ℝ) := by
  have hd := ContactInverse.data hb hz
  have hh := late_speed_data hb hhalf hz
  have hq : 0<q (U b) := by linarith [hh.1]
  have hv := hd.2.2.2.2.1
  have hr := outer_ratio_bounds hb
  have hr2 : (ratio b)^2≤1 := by nlinarith [hr.1,hr.2.1]
  have hz2 : z^2≤(1/4:ℝ) := by nlinarith [hz.1,hz.2]
  have hnum := mul_le_mul hr2 hz2 (sq_nonneg z) (by norm_num : (0:ℝ)≤1)
  have hden := mul_le_mul hh.1 hh.2.1 (by norm_num : (0:ℝ)≤1557/1250) hq.le
  have hcor : (ratio b)^2*z^2/(q (U b)*(ContactInverse.speed z b)^2)<69/500 := by
    apply (div_lt_iff₀ (mul_pos hq (sq_pos_of_pos hv))).2
    nlinarith
  have hcor0 : 0≤(ratio b)^2*z^2/(q (U b)*(ContactInverse.speed z b)^2) := by
    positivity
  have he := Inverse.brace_identity hd.1.ne' hq.ne' hv.ne'
    (circle_ratio hb) hd.2.2.2.2.2
  have hK := ContactPolynomial.late_K0 (late_coordinate hb hhalf)
  dsimp [OppositeTwo.Inverse.mass] at hK
  rw [abs_lt]
  constructor <;> linarith

lemma late_inverse_upper {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hhalf : 1/2≤b)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    PJCritical.inverseTarget (U b) (ratio b) z (ContactInverse.speed z b)<187/1000 := by
  have hd := ContactInverse.data hb hz
  have hh := late_speed_data hb hhalf hz
  have hr := outer_ratio_bounds hb
  have hr0 : 0<ratio b := by linarith [hr.1]
  have hf := mul_lt_mul_of_pos_left
    (ContactPolynomial.late_factorD (late_coordinate hb hhalf)) hr0
  have hfirst : -ratio b*factorD (U b)<18/125 := by nlinarith [hr.2.1]
  have hzabs : |z|≤(1/2:ℝ) := abs_le.mpr ⟨hz.1,by linarith [hz.2]⟩
  have hbabs := late_brace hb hhalf hz
  have hprod : |z*brace (U b) (ratio b) (ContactInverse.speed z b)|<7/100 := by
    rw [abs_mul]
    have hle := mul_le_mul_of_nonneg_right hzabs (abs_nonneg _)
    nlinarith
  have hq : 0<q (U b) := by linarith [hh.1]
  have hden := mul_lt_mul hh.1 hh.2.2 (by norm_num : (0:ℝ)≤223/200) hq
  have hmiddle : z/(q (U b)*ContactInverse.speed z b)*
      brace (U b) (ratio b) (ContactInverse.speed z b)<43/1000 := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (mul_pos hq hd.2.2.2.2.1)).2
    have hp := (le_abs_self (z*brace (U b) (ratio b) (ContactInverse.speed z b))).trans_lt hprod
    nlinarith
  dsimp [PJCritical.inverseTarget,PJCritical.heightFactorD]
  linarith

lemma source_half_second : (11/50:ℝ)<PLabel.d2 (1/2) := by
  have hb : (1/2:ℝ)∈Icc 0 outerDiagonal :=
    Asymmetric.rational_outer_mem (by constructor <;> norm_num)
  have hh := PLabel.second_chart_reference (outer_domain hb)
    (l := (1707512811079/1000000000000:ℝ))
    (u := (42687820277/25000000000:ℝ))
    (dlo := (11/50:ℝ)) (dhi := (23/100:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [PLabel,W,Q0]) (by norm_num [PLabel,W,Q0])
  exact hh.1

lemma R_identity (u : ℝ) : ContactPolynomial.R u=
    K u*(q u-1/4)-(1/4)*u*(Q0-u^2) := by
  norm_num [ContactPolynomial.R,K,Inverse.K,q,Inverse.q,Q0]
  ring

lemma early_brace_positive {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hhalf : b≤1/2)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    0<brace (U b) (ratio b) (ContactInverse.speed z b) := by
  have hd := ContactInverse.data hb hz
  have hu := early_coordinate hb hhalf
  have hq : 0<q (U b) := by linarith [Inverse.actual_q_positive hb]
  have hv := hd.2.2.2.2.1
  have hc := UW_circle (outer_domain hb)
  have hcircle : Q0-(U b)^2=(W b)^2 := by linarith
  have hr2 : (ratio b)^2*(U b)^2=(W b)^2 := by
    linarith [circle_ratio hb]
  have hK := ContactPolynomial.K_positive hu
  have hR := ContactPolynomial.R_positive hu
  have hz2 : z^2≤(1/4:ℝ) := by nlinarith [hz.1,hz.2]
  have hproduct := mul_nonneg (show 0≤(1/4:ℝ)-z^2 by linarith)
    (show 0≤K (U b)+U b*(W b)^2 by positivity)
  have he := Inverse.brace_identity hd.1.ne' hq.ne' hv.ne'
    (circle_ratio hb) hd.2.2.2.2.2
  have hmass : brace (U b) (ratio b) (ContactInverse.speed z b)*
      ((U b)^3*q (U b)*(ContactInverse.speed z b)^2)=
      K (U b)*(q (U b)-z^2)-U b*(W b)^2*z^2 := by
    rw [he]
    field_simp [hd.1.ne',hq.ne',hv.ne']
    linear_combination (U b*z^2)*hr2-
      K (U b)*hd.2.2.2.2.2
  have hRid := R_identity (U b)
  rw [hcircle] at hRid
  have hmasspos : 0<(U b)^3*q (U b)*(ContactInverse.speed z b)^2 := by positivity
  by_contra hbad
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hbad) hmasspos.le
  nlinarith

lemma early_inverse_negative {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hhalf : b≤1/2)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    PJCritical.inverseTarget (U b) (ratio b) z (ContactInverse.speed z b)<0 := by
  have hd := ContactInverse.data hb hz
  have hu := early_coordinate hb hhalf
  have hq : 0<q (U b) := by linarith [Inverse.actual_q_positive hb]
  have hv := hd.2.2.2.2.1
  have hN := ContactPolynomial.N_positive hu
  have hK := ContactPolynomial.K_positive hu
  have hr : 0<ratio b := by linarith [(outer_ratio_bounds hb).1]
  have hbrace := early_brace_positive hb hhalf hz
  have hfactor : 0<factorD (U b) := by
    exact div_pos hN (mul_pos (sq_pos_of_pos hd.1) (sq_pos_of_pos hq))
  by_cases hz0 : 0≤z
  · have hz2 : z^2≤(4/25:ℝ) := by nlinarith [hz.2]
    have hspeed : 0≤(ContactInverse.speed z b)^2-(q (U b)-4/25) := by
      linarith [hd.2.2.2.2.2]
    have hc := UW_circle (outer_domain hb)
    have hcircle : Q0-(U b)^2=(W b)^2 := by linarith
    have hreserve := ContactPolynomial.A_positive hu
    have hnonneg := mul_nonneg
      (mul_nonneg (sq_nonneg (W b)) (sq_nonneg (N (U b)))) hspeed
    have hsquares : (W b*N (U b)*ContactInverse.speed z b)^2-
        ((2/5)*K (U b))^2=ContactPolynomial.A (U b)+
          (W b)^2*(N (U b))^2*((ContactInverse.speed z b)^2-(q (U b)-4/25)) := by
      dsimp [ContactPolynomial.A]
      rw [hcircle]
      ring
    have hleft : 0<W b*N (U b)*ContactInverse.speed z b := by positivity
    have hright : 0≤(2/5:ℝ)*K (U b) := by positivity
    have hgap : (2/5)*K (U b)<W b*N (U b)*ContactInverse.speed z b := by
      nlinarith
    have htarget := mul_le_mul_of_nonneg_right hz.2 hK.le
    have hnum : -W b*N (U b)*ContactInverse.speed z b+z*K (U b)<0 := by
      linarith
    have he := Inverse.brace_identity hd.1.ne' hq.ne' hv.ne'
      (circle_ratio hb) hd.2.2.2.2.2
    have hcor : 0≤(ratio b)^2*z^2/(q (U b)*(ContactInverse.speed z b)^2) := by positivity
    have hupper : brace (U b) (ratio b) (ContactInverse.speed z b)≤
        K (U b)/((U b)^3*q (U b)) := by linarith
    have hweight : 0≤z/(q (U b)*ContactInverse.speed z b) := by positivity
    have hle := mul_le_mul_of_nonneg_left hupper hweight
    have hsum : -ratio b*factorD (U b)+
        z/(q (U b)*ContactInverse.speed z b)*(K (U b)/((U b)^3*q (U b)))=
        (-W b*N (U b)*ContactInverse.speed z b+z*K (U b))/
          ((U b)^3*(q (U b))^2*ContactInverse.speed z b) := by
      dsimp [ratio,factorD,Inverse.factorD,U,W]
      field_simp [show arc b+1/2≠0 from hd.1.ne',hq.ne',hv.ne']
      ring
    have hdiv : (-W b*N (U b)*ContactInverse.speed z b+z*K (U b))/
        ((U b)^3*(q (U b))^2*ContactInverse.speed z b)<0 :=
      div_neg_of_neg_of_pos hnum (by positivity)
    dsimp [PJCritical.inverseTarget,PJCritical.heightFactorD]
    linarith
  · have hweight : z/(q (U b)*ContactInverse.speed z b)≤0 :=
      div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hz0) (by positivity)
    have hmiddle := mul_nonpos_of_nonpos_of_nonneg hweight hbrace.le
    have hfirst := mul_pos hr hfactor
    dsimp [PJCritical.inverseTarget,PJCritical.heightFactorD]
    linarith

theorem inverse_minus_source_second {b z : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    PJCritical.inverseTarget (U b) (ratio b) z (ContactInverse.speed z b)-PLabel.d2 b<0 := by
  rcases le_total b (1/2) with hhalf|hhalf
  · linarith [early_inverse_negative hb hhalf hz,P_second_positive hb]
  · have hh := P_second_monotone
      (show (1/2:ℝ)∈Icc 0 outerDiagonal from
        Asymmetric.rational_outer_mem (by constructor <;> norm_num)) hb hhalf
    linarith [late_inverse_upper hb hhalf hz,source_half_second]

def fixedCost (z b : ℝ) : ℝ := Real.pi/2-ContactInverse.angle z b-P b+T (z+1/2)
def fixedFirst (z b : ℝ) : ℝ := -ContactInverse.first z b-PLabel.d1 b
def fixedSecond (z b : ℝ) : ℝ :=
  PJCritical.inverseTarget (U b) (ratio b) z (ContactInverse.speed z b)-PLabel.d2 b

lemma fixedCost_hasDerivAt {b z : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    HasDerivAt (fixedCost z) (fixedFirst z b) b := by
  convert (((ContactInverse.angle_hasDerivAt hb hz).const_sub (Real.pi/2)).sub
    (PLabel.outer_hasDerivAt (outer_domain hb))).add_const (T (z+1/2)) using 1 <;>
    dsimp [fixedCost,fixedFirst,P] <;> ring

lemma fixedFirst_hasDerivAt {b z : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    HasDerivAt (fixedFirst z) (fixedSecond z b) b := by
  convert (ContactInverse.first_hasDerivAt hb hz).neg.sub
    (PLabel.d1_hasDerivAt (outer_domain hb)) using 1 <;>
    dsimp [fixedFirst,fixedSecond,ContactInverse.second] <;> ring

theorem fixedCost_concave {z : ℝ} (hz : z∈Icc (-(1/2)) (2/5)) :
    ConcaveOn ℝ (Icc 0 outerDiagonal) (fixedCost z) :=
  concave_of_deriv2
    (fun b hb => fixedCost_hasDerivAt hb hz)
    (fun b hb => fixedFirst_hasDerivAt hb hz)
    (fun b hb => (inverse_minus_source_second hb hz).le)

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.ContactCurvature
