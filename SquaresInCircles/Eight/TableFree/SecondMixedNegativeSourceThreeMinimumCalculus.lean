module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeSourceThreeMinimumData

/-!
# Derivatives of the exact negative-core angle minimum

The phase and stationary sine contribution are differentiated separately.
Their third derivatives reduce to the two explicit height polynomials
D0 and Ch. All radicals are the original circle radical or the positive
stationary radical, with their domains established before division.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Minimum
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

lemma U_hasDerivAt {B : ℝ} (hB : B∈targets) : HasDerivAt U (-ratio B) B :=
  (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain (target_domain hB))).add_const (1/2)

lemma P_hasDerivAt {B : ℝ} (hB : B∈targets) : HasDerivAt P (-ratio B) B :=
  (U_hasDerivAt hB).sub_const 1

lemma V_hasDerivAt (B : ℝ) : HasDerivAt V 1 B := (hasDerivAt_id B).add_const (1/2)

lemma T_hasDerivAt {B : ℝ} (hB : B∈targets) : HasDerivAt T (2*ratio B) B := by
  convert ((U_hasDerivAt hB).const_mul 2).const_sub (Q0+1) using 1 <;> dsimp [T] <;> ring

lemma S_hasDerivAt {h B : ℝ} (hh : h∈slopes) (hB : B∈targets) :
    HasDerivAt (S h) (h^2*ratio B/S h B) B := by
  have hrad : h^2*T B-1≠0 := (Real.sqrt_pos.mp (S_positive hh hB)).ne'
  convert ((((T_hasDerivAt hB).const_mul (h^2)).sub_const 1).sqrt hrad) using 1 <;>
    dsimp [S] <;> ring

lemma beta_hasDerivAt {B : ℝ} (hB : B∈targets) : HasDerivAt beta (betaD B) B := by
  have hp := P_positive hB
  have ht : 0<T B := by linarith [(T_bounds hB).1]
  have hu := U_positive (outer_domain (target_domain hB))
  have hq := UW_circle (outer_domain (target_domain hB))
  have hratio : ratio B=V B/U B := rfl
  have hnum : P B+V B*ratio B=(Q0-U B)/U B := by
    rw [hratio]
    dsimp [P,V,W] at *
    field_simp [hu.ne']
    nlinarith [hq]
  have hden : 1+(V B/P B)^2=T B/(P B)^2 := by
    have hc := circle_phase hB
    field_simp [hp.ne']
    nlinarith
  have hd := (Real.hasDerivAt_arctan (V B/P B)).comp B
    ((V_hasDerivAt B).div (P_hasDerivAt hB) hp.ne')
  convert hd using 1
  · rfl
  · dsimp [betaD]
    have hnum' : 1*P B-V B*(-ratio B)=(Q0-U B)/U B := by linarith [hnum]
    rw [hnum',hden]
    field_simp [hp.ne',ht.ne',hu.ne']
    ring

lemma baseE_hasDerivAt (u : ℝ) : HasDerivAt baseE (baseEd u) u := by
  convert (((((hasDerivAt_id u).pow 2).const_mul 2).sub
    ((hasDerivAt_id u).const_mul (4*Q0))).add_const (Q0*(Q0+1))) using 1 <;>
    dsimp [baseE,baseEd] <;> ring

lemma betaD_hasDerivAt {B : ℝ} (hB : B∈targets) :
    HasDerivAt betaD (betaDD B) B := by
  have hu := U_positive (outer_domain (target_domain hB))
  have ht : 0<T B := by linarith [(T_bounds hB).1]
  have hd := ((U_hasDerivAt hB).const_sub Q0).div
    ((U_hasDerivAt hB).mul (T_hasDerivAt hB)) (mul_ne_zero hu.ne' ht.ne')
  convert hd using 1
  · rfl
  · dsimp [betaDD,baseE]
    dsimp [ratio,U,V,T]
    field_simp [hu.ne',ht.ne']
    ring

lemma betaDD_hasDerivAt {B : ℝ} (hB : B∈targets) :
    HasDerivAt betaDD (betaDDD B) B := by
  have hu := U_positive (outer_domain (target_domain hB))
  have ht : 0<T B := by linarith [(T_bounds hB).1]
  have hcircle : (V B)^2=Q0-(U B)^2 := by
    have hc := UW_circle (outer_domain (target_domain hB))
    dsimp [V,W] at *
    nlinarith
  have hA : A0 (U B)=baseE (U B)*(U B)^2*T B-
      (V B)^2*(baseEd (U B)*U B*T B-baseE (U B)*(3*T B-4*U B)) := by
    rw [hcircle]
    rfl
  have hd := (((baseE_hasDerivAt (U B)).comp B (U_hasDerivAt hB)).mul
    (V_hasDerivAt B)).div (((U_hasDerivAt hB).pow 3).mul ((T_hasDerivAt hB).pow 2))
      (mul_ne_zero (pow_ne_zero _ hu.ne') (pow_ne_zero _ ht.ne'))
  convert hd using 1
  · rfl
  · dsimp only [betaDDD]
    rw [hA]
    dsimp [ratio,U,V]
    field_simp [hu.ne',ht.ne']
    ring

lemma stationary_hasDerivAt {h B : ℝ} (hh : h∈slopes) (hB : B∈targets) :
    HasDerivAt (fun y => Real.arctan (S h y)-S h y) (-R h B) B := by
  have hs := S_positive hh hB
  have ht : 0<T B := by linarith [(T_bounds hB).1]
  have hh0 : h≠0 := ne_of_gt (by linarith [hh.1])
  have hsum : 1+(S h B)^2=h^2*T B := by linarith [S_sq hh hB]
  have hcalc : 1/(1+(S h B)^2)*(h^2*ratio B/S h B)-h^2*ratio B/S h B=
      -ratio B*S h B/T B := by
    calc
      _ = -(h^2*ratio B/S h B)*(S h B)^2/(1+(S h B)^2) := by
        field_simp [show 1+(S h B)^2≠0 by positivity,hs.ne']
        ring
      _ = _ := by
        rw [hsum]
        field_simp [hs.ne',ht.ne',hh0]
        ring
  have hd := ((Real.hasDerivAt_arctan (S h B)).comp B (S_hasDerivAt hh hB)).sub
    (S_hasDerivAt hh hB)
  convert hd using 1
  · rfl
  · dsimp [R]
    linarith [hcalc]

lemma R_hasDerivAt {h B : ℝ} (hh : h∈slopes) (hB : B∈targets) :
    HasDerivAt (R h) (RD h B) B := by
  have hs := S_positive hh hB
  have ht : 0<T B := by linarith [(T_bounds hB).1]
  have hd := ((ShortOuterOne.SameContact.ratio_hasDerivAt
    (outer_domain (target_domain hB))).mul (S_hasDerivAt hh hB)).div (T_hasDerivAt hB) ht.ne'
  convert hd using 1 <;> dsimp [R,RD]
  field_simp [hs.ne',ht.ne']
  ring

lemma RD_hasDerivAt {h B : ℝ} (hh : h∈slopes) (hB : B∈targets) :
    HasDerivAt (RD h) (RDD h B) B := by
  have hs := S_positive hh hB
  have ht : 0<T B := by linarith [(T_bounds hB).1]
  have hr := ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain (target_domain hB))
  have hrd := ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain (target_domain hB))
  have hd0 := (hrd.mul (S_hasDerivAt hh hB)).div (T_hasDerivAt hB) ht.ne'
  have hd1 := ((hr.pow 2).const_mul (h^2)).div
    ((S_hasDerivAt hh hB).mul (T_hasDerivAt hB)) (mul_ne_zero hs.ne' ht.ne')
  have hd2 := (((hr.pow 2).const_mul 2).mul (S_hasDerivAt hh hB)).div
    ((T_hasDerivAt hB).pow 2) (pow_ne_zero _ ht.ne')
  convert (hd0.add hd1).sub hd2 using 1 <;> dsimp [RD,RDD]
  field_simp [hs.ne',ht.ne']
  ring

lemma RDD_identity {h B : ℝ} (hh : h∈slopes) (hB : B∈targets) :
    RDD h B=V B*Ch h (U B)/((U B)^5*(T B)^3*(S h B)^3) := by
  have hu := U_positive (outer_domain (target_domain hB))
  have hs := S_positive hh hB
  have ht : 0<T B := by linarith [(T_bounds hB).1]
  have hv2 : (V B)^2=Q0-(U B)^2 := by
    have hc := UW_circle (outer_domain (target_domain hB))
    dsimp [V,W] at *
    nlinarith
  calc
    RDD h B = V B*(3*Q0*(T B)^2*((S h B)^2)^2+
      3*h^2*Q0*U B*(T B)^2*(S h B)^2-h^4*(V B)^2*(U B)^2*(T B)^2-
      6*Q0*U B*T B*((S h B)^2)^2-
      4*h^2*(V B)^2*(U B)^2*T B*(S h B)^2+
      8*(V B)^2*(U B)^2*((S h B)^2)^2)/((U B)^5*(T B)^3*(S h B)^3) := by
        dsimp [RDD,ratio,ratioD,ratioDD,U,V]
        field_simp [hu.ne',hs.ne',ht.ne']
        ring
    _ = _ := by rw [hv2,S_sq hh hB]; dsimp [Ch,T]; ring

lemma E_hasDerivAt {h B : ℝ} (hh : h∈slopes) (hB : B∈targets) :
    HasDerivAt (E h) (E1 h B) B := by
  convert (((((beta_hasDerivAt hB).add (stationary_hasDerivAt hh hB)).sub_const e).
    sub_const (epsilon h)).add_const (h/2)).sub
      (LLabel.outer_hasDerivAt (outer_domain (target_domain hB))) using 1 <;>
    dsimp [E,E1,L] <;> ring

lemma E1_hasDerivAt {h B : ℝ} (hh : h∈slopes) (hB : B∈targets) :
    HasDerivAt (E1 h) (E2 h B) B := by
  convert ((betaD_hasDerivAt hB).sub (R_hasDerivAt hh hB)).sub
    (LLabel.d1_hasDerivAt (outer_domain (target_domain hB))) using 1 <;> rfl

lemma E2_hasDerivAt {h B : ℝ} (hh : h∈slopes) (hB : B∈targets) :
    HasDerivAt (E2 h) (E3 h B) B := by
  convert ((betaDD_hasDerivAt hB).sub (RD_hasDerivAt hh hB)).sub
    (LLabel.d2_hasDerivAt (outer_domain (target_domain hB))) using 1 <;> rfl

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Minimum
