module

public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.SourceThreeMinimumPolynomials
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.TargetTwoCornerCalculus

/-!
# Eight squares: exact endpoint references for the whole corner

There are two interior-minimum references and one late diagonal
reference. Their trigonometric and core-diagonal cages are fixed
rational inequalities; the polynomial evaluations are exact.
-/

section
/-!
## Derivatives of the exact negative-core angle minimum

The phase and stationary sine contribution are differentiated separately.
Their third derivatives reduce to the two explicit height polynomials
D0 and Ch. All radicals are the original circle radical or the positive
stationary radical, with their domains established before division.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

lemma U_hasDerivAt {B : ℝ} (hB : B∈targets) : HasDerivAt U (-ratio B) B :=
  (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain (target_domain hB))).add_const (1/2)

lemma P_hasDerivAt {B : ℝ} (hB : B∈targets) : HasDerivAt P (-ratio B) B :=
  (U_hasDerivAt hB).sub_const 1

lemma V_hasDerivAt (B : ℝ) : HasDerivAt V 1 B := (hasDerivAt_id B).add_const (1/2)

lemma T_hasDerivAt {B : ℝ} (hB : B∈targets) : HasDerivAt T (2*ratio B) B := by
  exact (((U_hasDerivAt hB).const_mul 2).const_sub (Q0+1)).congr_deriv (by ring)

lemma S_hasDerivAt {h B : ℝ} (hh : h∈slopes) (hB : B∈targets) :
    HasDerivAt (S h) (h^2*ratio B/S h B) B := by
  have hrad : h^2*T B-1≠0 := (Real.sqrt_pos.mp (S_positive hh hB)).ne'
  exact ((((T_hasDerivAt hB).const_mul (h^2)).sub_const 1).sqrt hrad).congr_deriv
    (by simp only [S]; ring)

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

lemma baseE_hasDerivAt (u : ℝ) : HasDerivAt baseE (baseEd u) u := by
  exact (((((hasDerivAt_id' u).pow 2).const_mul 2).sub
    ((hasDerivAt_id' u).const_mul (4*Q0))).add_const (Q0*(Q0+1))).congr_deriv
      (by simp only [baseEd]; norm_num; ring)

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
  · have hr : ratio B=V B/U B := rfl
    simp only [betaDDD,Pi.mul_apply,Pi.pow_apply,Function.comp_apply]
    rw [hA,hr]
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
  have hd := ((Real.hasDerivAt_arctan (S h B)).comp B (S_hasDerivAt hh hB)).sub
    (S_hasDerivAt hh hB)
  exact hd.congr_deriv (by rw [hcalc]; simp only [R]; ring)

lemma R_hasDerivAt {h B : ℝ} (hh : h∈slopes) (hB : B∈targets) :
    HasDerivAt (R h) (RD h B) B := by
  have hs := S_positive hh hB
  have ht : 0<T B := by linarith [(T_bounds hB).1]
  have hd := ((ShortOuterOne.SameContact.ratio_hasDerivAt
    (outer_domain (target_domain hB))).mul (S_hasDerivAt hh hB)).div (T_hasDerivAt hB) ht.ne'
  exact hd.congr_deriv (by simp only [RD,Pi.mul_apply]; field_simp)

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
  exact ((hd0.add hd1).sub hd2).congr_deriv
    (by simp only [RDD,Pi.mul_apply,Pi.pow_apply]; field_simp; ring)

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
    _ = _ := by rw [hv2,S_sq hh hB]; dsimp [Ch,T]; ring

lemma E_hasDerivAt {h B : ℝ} (hh : h∈slopes) (hB : B∈targets) :
    HasDerivAt (E h) (E1 h B) B := by
  have hd := (((((beta_hasDerivAt hB).add (stationary_hasDerivAt hh hB)).sub_const e).sub_const
    (epsilon h)).add_const (h/2)).sub
      (LLabel.outer_hasDerivAt (outer_domain (target_domain hB)))
  convert hd using 1
  · funext y
    simp only [E,L,Pi.sub_apply,Pi.add_apply]
    ring
  · simp only [E1]
    ring

lemma E1_hasDerivAt {h B : ℝ} (hh : h∈slopes) (hB : B∈targets) :
    HasDerivAt (E1 h) (E2 h B) B := by
  convert ((betaD_hasDerivAt hB).sub (R_hasDerivAt hh hB)).sub
    (LLabel.d1_hasDerivAt (outer_domain (target_domain hB))) using 1 <;> rfl

lemma E2_hasDerivAt {h B : ℝ} (hh : h∈slopes) (hB : B∈targets) :
    HasDerivAt (E2 h) (E3 h B) B := by
  convert ((betaDD_hasDerivAt hB).sub (RD_hasDerivAt hh hB)).sub
    (LLabel.d2_hasDerivAt (outer_domain (target_domain hB))) using 1 <;> rfl

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum
end
end
end

section
/-!
## Concave first derivatives on both complete minimum intervals

The positive denominator difference puts the phase's third derivative
below one. The positive stationary numerator subtracts another positive
quantity. The literal L label has third derivative above one, proving
strict negativity on each complete target interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratioD ratioDD)

lemma first_slope : g∈slopes := by norm_num [slopes,g,EdgeThreeAligned.gn]
lemma second_slope : (39/40:ℝ)∈slopes := by norm_num [slopes,g,EdgeThreeAligned.gn]

lemma label_third_large {B : ℝ} (hB : B∈targets) : (1:ℝ)<LLabel.d3 B := by
  have hu := U_positive (outer_domain (target_domain hB))
  have hcube := pow_le_pow_left₀ hu.le (show U B≤2 by linarith [(U_bounds hB).2]) 3
  have hr : (1/4:ℝ)<ratioD B := by
    change (1/4:ℝ)<Q0/(U B)^3
    apply (lt_div_iff₀ (pow_pos hu 3)).2
    norm_num [Q0] at *
    linarith
  have hrd := ratioDD_positive (target_domain hB)
  have hp := mul_nonneg hB.1 hrd.le
  dsimp [RoleLabel.d3,LLabel]
  nlinarith

lemma phase_third_upper {B : ℝ} (hB : B∈targets) : betaDDD B<1 := by
  have hu := U_positive (outer_domain (target_domain hB))
  have ht : 0<T B := by linarith [(T_bounds hB).1]
  have hp := Polynomials.D0_positive ⟨(U_bounds hB).1.le,(U_bounds hB).2.le⟩
  dsimp [betaDDD]
  apply (div_lt_one (mul_pos (pow_pos hu 5) (pow_pos ht 3))).2
  dsimp [D0,T] at *
  linarith

lemma stationary_third_positive {h B : ℝ} (hh : h∈slopes) (hB : B∈targets)
    (hpoly : 0<Ch h (U B)) : 0<RDD h B := by
  rw [RDD_identity hh hB]
  have hu := U_positive (outer_domain (target_domain hB))
  have ht : 0<T B := by linarith [(T_bounds hB).1]
  have hs := S_positive hh hB
  have hv : 0<V B := by dsimp [V]; linarith [hB.1]
  positivity

lemma first_third_negative {B : ℝ} (hB : B∈targets) : E3 g B<0 := by
  have hpoly := Polynomials.Ch_first_positive ⟨(U_bounds hB).1.le,(U_bounds hB).2.le⟩
  have hr := stationary_third_positive first_slope hB hpoly
  dsimp [E3]
  linarith [phase_third_upper hB,label_third_large hB]

lemma second_height {B : ℝ} (hB : B∈Icc (9/20:ℝ) (27/50)) : U B∈Icc (42/25:ℝ) (87/50) := by
  have hd : B∈targets := ⟨by linarith [hB.1],hB.2⟩
  have hu := U_bounds hd
  have hq := UW_circle (outer_domain (target_domain hd))
  have hv2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤19/20)
    (show (19/20:ℝ)≤B+1/2 by linarith [hB.1]) 2
  refine ⟨hu.1.le,?_⟩
  dsimp [W] at hq
  norm_num [Q0] at hq
  nlinarith

lemma second_third_negative {B : ℝ} (hB : B∈Icc (9/20:ℝ) (27/50)) : E3 (39/40) B<0 := by
  have hd : B∈targets := ⟨by linarith [hB.1],hB.2⟩
  have hpoly := Polynomials.Ch_second_positive (second_height hB)
  have hr := stationary_third_positive second_slope hd hpoly
  dsimp [E3]
  linarith [phase_third_upper hd,label_third_large hd]

lemma first_second_antitone : AntitoneOn (E2 g) targets :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hB => (E2_hasDerivAt first_slope hB).continuousAt.continuousWithinAt)
    (fun _ hB => E2_hasDerivAt first_slope (Ioo_subset_Icc_self hB))
    (fun _ hB => (first_third_negative (Ioo_subset_Icc_self hB)).le)

lemma second_second_antitone : AntitoneOn (E2 (39/40)) (Icc (9/20:ℝ) (27/50)) :=
  antiOn_of_hasDeriv_nonpos
    (fun B hB => (E2_hasDerivAt second_slope (show B∈targets from ⟨by linarith [hB.1],hB.2⟩)).continuousAt.continuousWithinAt)
    (fun B hB => E2_hasDerivAt second_slope (show B∈targets from ⟨by linarith [hB.1],hB.2.le⟩))
    (fun B hB => (second_third_negative (Ioo_subset_Icc_self hB)).le)

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum
end
end
end

section
/-!
## The original lower primary contact for the negative core

The weak primary separator forces the source onto its straight side.
Its exact contact coordinate increases with angle on the full lower
half and remains below A-1. On the later zero-entry range the contact
cost is strictly concave.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Primary
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig)

def k : ℝ := 13/12
def b (A φ : ℝ) : ℝ := (A-1/2-k*Real.cos φ)/Real.sin φ-1/2
def b1 (A φ : ℝ) : ℝ := (k-(A-1/2)*Real.cos φ)/(Real.sin φ)^2
def b2 (A φ : ℝ) : ℝ := (A-1/2)/Real.sin φ-
  2*(k-(A-1/2)*Real.cos φ)*Real.cos φ/(Real.sin φ)^3
def F (A B φ : ℝ) : ℝ := sideValue (b A φ) B φ
def F1 (A φ : ℝ) : ℝ := 1-(g-2*z*b A φ)*b1 A φ
def F2 (A φ : ℝ) : ℝ := 2*z*(b1 A φ)^2-(g-2*z*b A φ)*b2 A φ

lemma sine_positive {φ : ℝ} (hφ : Lower φ) : 0<Real.sin φ := by linarith [(lower_trig hφ).1]

lemma equation {A φ : ℝ} (hφ : Lower φ) :
    (b A φ+1/2)*Real.sin φ+k*Real.cos φ=A-1/2 := by
  dsimp [b]
  field_simp [(sine_positive hφ).ne']
  ring

lemma b_hasDerivAt {A φ : ℝ} (hφ : Lower φ) : HasDerivAt (b A) (b1 A φ) φ := by
  have hs := sine_positive hφ
  have hd := ((((Real.hasDerivAt_cos φ).const_mul k).const_sub (A-1/2)).div
    (Real.hasDerivAt_sin φ) hs.ne').sub_const (1/2)
  convert hd using 1
  · rfl
  · dsimp [b1]
    field_simp [hs.ne']
    nlinarith [congrArg (fun x : ℝ => k*x) (Real.sin_sq_add_cos_sq φ)]

lemma b1_hasDerivAt {A φ : ℝ} (hφ : Lower φ) : HasDerivAt (b1 A) (b2 A φ) φ := by
  have hs := sine_positive hφ
  have hn : HasDerivAt (fun x => k-(A-1/2)*Real.cos x) ((A-1/2)*Real.sin φ) φ := by
    have h := ((Real.hasDerivAt_cos φ).const_mul (A-1/2)).const_sub k
    exact h.congr_deriv (by ring)
  have hdn : HasDerivAt (fun x => (Real.sin x)^2) (2*Real.sin φ*Real.cos φ) φ := by
    have h := (Real.hasDerivAt_sin φ).pow 2
    exact h.congr_deriv (by norm_num)
  have hd := hn.div hdn (pow_ne_zero 2 hs.ne')
  have hf : b1 A=fun x => (k-(A-1/2)*Real.cos x)/(Real.sin x)^2 := rfl
  rw [hf]
  refine hd.congr_deriv ?_
  simp only [b2]
  field_simp

lemma first_identity {A φ : ℝ} (hφ : Lower φ) :
    b1 A φ=k-(b A φ+1/2)*(Real.cos φ/Real.sin φ) := by
  dsimp [b1,b]
  field_simp [(sine_positive hφ).ne']
  nlinarith [congrArg (fun x : ℝ => k*x) (Real.sin_sq_add_cos_sq φ)]

lemma second_identity {A φ : ℝ} (hφ : Lower φ) :
    b2 A φ=(b A φ+1/2)*(1+2*(Real.cos φ/Real.sin φ)^2)-k*(Real.cos φ/Real.sin φ) := by
  dsimp [b2,b]
  field_simp [(sine_positive hφ).ne']
  nlinarith [congrArg (fun x : ℝ => 2*k*Real.cos φ*x) (Real.sin_sq_add_cos_sq φ)]

lemma b1_positive {A B φ : ℝ} (ht : OuterState A B) (hφ : Lower φ) : 0<b1 A φ := by
  have hAlo : (89/100:ℝ)<A := outer_endpoint_bounds.2.2.1.trans_le (outer_bounds ht).1
  have hAhi := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  have hp := mul_nonneg (show 0≤A-1/2 by linarith)
    (show 0≤1-Real.cos φ by linarith [Real.cos_le_one φ])
  apply div_pos _ (pow_pos (sine_positive hφ) 2)
  dsimp [k]
  nlinarith

lemma b_monotone {A B : ℝ} (ht : OuterState A B) :
    MonotoneOn (b A) (Icc lowerAngle (Real.pi/2)) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hφ => (b_hasDerivAt hφ).continuousAt.continuousWithinAt)
    (fun _ hφ => b_hasDerivAt (Ioo_subset_Icc_self hφ))
    (fun _ hφ => (b1_positive ht (Ioo_subset_Icc_self hφ)).le)

lemma b_upper {A B φ : ℝ} (ht : OuterState A B) (hφ : Lower φ) : b A φ≤A-1 := by
  have htr := lower_trig hφ
  have hAlo : (89/100:ℝ)<A := outer_endpoint_bounds.2.2.1.trans_le (outer_bounds ht).1
  have hAhi := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  have hp := mul_nonneg (show 0≤A-1/2 by linarith)
    (show 0≤Real.sin φ+Real.cos φ-1 by linarith [htr.2.2.2.2])
  have hq := mul_nonneg (show 0≤k-(A-1/2) by dsimp [k]; linarith) htr.2.2.1
  apply (mul_le_mul_iff_left₀ (sine_positive hφ)).mp
  nlinarith [equation (A := A) hφ]

lemma b_aligned (A : ℝ) : b A (Real.pi/2)=A-1 := by norm_num [b,k]; ring

lemma original_contact {a b₀ A B φ : ℝ} (hs : CoreState a b₀)
    (ht : OuterState A B) (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤-a*Real.cos φ-b₀*Real.sin φ+A) :
    a=7/12 ∧ 0≤b A φ ∧ b A φ<(83/200:ℝ) ∧ 1≤A ∧ F A B φ≤value a b₀ B φ := by
  have hcore := CoreAngleEndpoint.state_bounds hs
  have htr := lower_trig hφ
  have hAhi := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  have hside : b₀<1/2 := by
    by_contra hn
    have hb : 1/2≤b₀ := le_of_not_gt hn
    have ha : 1/2≤a := hb.trans hcore.2.2.2.1
    have hp := mul_nonneg (sub_nonneg.mpr ha) htr.2.2.1
    have hq := mul_nonneg (sub_nonneg.mpr hb) (sine_positive hφ).le
    nlinarith [htr.2.2.2.2]
  have ha := (CommonQuarter.core_small_side hs hside).1
  have he := equation (A := A) hφ
  have hbc : b₀≤b A φ := by
    apply (mul_le_mul_iff_left₀ (sine_positive hφ)).mp
    rw [ha] at hsep
    dsimp [k] at he
    nlinarith
  have hu := b_upper ht hφ
  have hm := EdgeThreeAligned.sideH_mono hcore.2.2.1
    (show b A φ≤1/2 by linarith) hbc
  refine ⟨ha,by linarith [hcore.2.2.1],by linarith,by linarith [hcore.2.2.1],?_⟩
  dsimp [F,sideValue,value,EdgeThreeAligned.negativeSideCost,EdgeThreeAligned.negativeCost]
  rw [ha,EdgeThreeAligned.sideH_eq]
  linarith

lemma F_hasDerivAt {A B φ : ℝ} (hφ : Lower φ) : HasDerivAt (F A B) (F1 A φ) φ := by
  have h := ((hasDerivAt_id φ).sub
    ((((b_hasDerivAt (A := A) hφ).const_mul g).const_add e).sub
      (((b_hasDerivAt (A := A) hφ).pow 2).const_mul z))).sub_const (L B)
  exact h.congr_deriv (by simp only [F1]; push_cast; ring)

lemma F1_hasDerivAt {A φ : ℝ} (hφ : Lower φ) : HasDerivAt (F1 A) (F2 A φ) φ := by
  have h := ((((b_hasDerivAt (A := A) hφ).const_mul (2*z)).const_sub g).mul
    (b1_hasDerivAt (A := A) hφ)).const_sub 1
  exact h.congr_deriv (by simp only [F2]; ring)

lemma late_lower {φ : ℝ} (hφ : φ∈LPrimaryZero.angles) : Lower φ :=
  ⟨by dsimp [lowerAngle]; linarith [hφ.1,pi_hand_enclosure.2],hφ.2⟩

lemma curvature_negative {A B φ : ℝ} (ht : OuterState A B)
    (hφ : φ∈LPrimaryZero.angles) (hb : 0≤b A φ) : F2 A φ<0 := by
  have hl := late_lower hφ
  have htr := LPrimaryZero.trig hφ
  have hs := sine_positive hl
  have hu : b A φ<(83/200:ℝ) :=
    (b_upper ht hl).trans_lt (by linarith [(outer_bounds ht).2.1,outer_endpoint_bounds.2.1])
  let t := Real.cos φ/Real.sin φ
  have ht0 : 0≤t := div_nonneg htr.2.2.1 hs.le
  have hthi : t<(261/1000:ℝ) := by
    apply (div_lt_iff₀ hs).2
    linarith [htr.1,htr.2.2.2]
  have hd := b1_positive ht hl
  have hdhi : b1 A φ≤k := by
    have hp := mul_nonneg (show 0≤b A φ+1/2 by linarith) ht0
    rw [first_identity hl]
    linarith
  have hd2 : (b1 A φ)^2≤(13/12:ℝ)^2 := by
    exact pow_le_pow_left₀ hd.le (by simpa [k] using hdhi) 2
  have hdd : (21/100:ℝ)<b2 A φ := by
    have hp := mul_nonneg hb (show 0≤1+2*t^2 by positivity)
    have hsq := sq_nonneg t
    rw [second_identity hl]
    change (21/100:ℝ)<(b A φ+1/2)*(1+2*t^2)-k*t
    dsimp [k]
    nlinarith
  have hcoef : (47/50:ℝ)<g-2*z*b A φ := by
    dsimp [g,z,EdgeThreeAligned.gn,EdgeThreeAligned.zn]
    linarith
  have hproduct := mul_le_mul hcoef.le hdd.le (by norm_num : (0:ℝ)≤21/100)
    (by linarith : 0≤g-2*z*b A φ)
  have hz : z=2667/50000 := by norm_num [z,EdgeThreeAligned.zn]
  simp only [F2]
  rw [hz] at hproduct ⊢
  norm_num at hd2
  linarith

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Primary
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Corner
open CommonQuarter CorePairGeometry Arithmetic

abbrev dc := CoreAngleEndpoint.diagonal

lemma diagonal_label : (28058641/50000000:ℝ)<MixedThree.negativeCore dc dc := by
  have hh := CoreAngleEndpoint.diagonal_bounds
  have hp := pow_le_pow_left₀ (by linarith [hh.1] : 0≤dc) hh.2.le 2
  dsimp [MixedThree.negativeCore]
  nlinarith [hh.1,hh.2]

private lemma diagonal_cage {φ sl su cl cu : ℝ} (hsl : 0≤ sl) (hcl : 0≤cl)
    (hs : sl≤Real.sin φ ∧ Real.sin φ≤ su) (hc : cl≤Real.cos φ ∧ Real.cos φ≤cu) :
    1+(26473139/25000000)*cl-(5892557/100000000)*su≤u dc φ ∧
    u dc φ≤1+(105892557/100000000)*cu-(1473139/25000000)*sl ∧
    (26473139/25000000)*sl+(1473139/25000000)*cl≤ speed dc φ ∧
    speed dc φ≤(105892557/100000000)*su+(5892557/100000000)*cu := by
  have hd := CoreAngleEndpoint.diagonal_bounds
  have hdp : 0≤dc+1/2 := by linarith [hd.1]
  have hdm : 0≤dc-1/2 := by linarith [hd.1]
  have hcpL := mul_le_mul (show (26473139/25000000:ℝ)≤dc+1/2 by linarith [hd.1]) hc.1 hcl hdp
  have hcpU := mul_le_mul (show dc+1/2≤(105892557/100000000:ℝ) by linarith [hd.2]) hc.2
    (hcl.trans hc.1) (by norm_num : (0:ℝ)≤105892557/100000000)
  have hsmL := mul_le_mul (show (1473139/25000000:ℝ)≤dc-1/2 by linarith [hd.1]) hs.1 hsl hdm
  have hsmU := mul_le_mul (show dc-1/2≤(5892557/100000000:ℝ) by linarith [hd.2]) hs.2
    (hsl.trans hs.1) (by norm_num : (0:ℝ)≤5892557/100000000)
  have hspL := mul_le_mul (show (26473139/25000000:ℝ)≤dc+1/2 by linarith [hd.1]) hs.1 hsl hdp
  have hspU := mul_le_mul (show dc+1/2≤(105892557/100000000:ℝ) by linarith [hd.2]) hs.2
    (hsl.trans hs.1) (by norm_num : (0:ℝ)≤105892557/100000000)
  have hcmL := mul_le_mul (show (1473139/25000000:ℝ)≤dc-1/2 by linarith [hd.1]) hc.1 hcl hdm
  have hcmU := mul_le_mul (show dc-1/2≤(5892557/100000000:ℝ) by linarith [hd.2]) hc.2
    (hcl.trans hc.1) (by norm_num : (0:ℝ)≤5892557/100000000)
  simp only [u,speed,MixedCorner.diagonal]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma diagonal_reference_trig :
    (43346261/50000000:ℝ)<Real.sin (1049/1000) ∧ Real.sin (1049/1000)<86692523/100000000 ∧
    (24921911/50000000:ℝ)<Real.cos (1049/1000) ∧ Real.cos (1049/1000)<49843823/100000000 := by
  have hs := HighOrderTaylor.S15_le_sin (x := (1049/1000:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (1049/1000:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (1049/1000:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (1049/1000:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S11,HighOrderTaylor.S13,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma join_reference_trig :
    (9168031/10000000:ℝ)<Real.sin (29/25) ∧ Real.sin (29/25)<11460039/12500000 ∧
    (4991744/12500000:ℝ)<Real.cos (29/25) ∧ Real.cos (29/25)<19966977/50000000 := by
  have hs := HighOrderTaylor.S15_le_sin (x := (29/25:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (29/25:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (29/25:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (29/25:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S11,HighOrderTaylor.S13,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma late_reference_trig :
    (11140092/12500000:ℝ)<Real.sin (11/10) ∧ Real.sin (11/10)<89120737/100000000 ∧
    (11339903/25000000:ℝ)<Real.cos (11/10) ∧ Real.cos (11/10)<45359613/100000000 := by
  have hs := HighOrderTaylor.S15_le_sin (x := (11/10:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (11/10:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (11/10:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (11/10:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S11,HighOrderTaylor.S13,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma diagonal_reference_coordinates :
    (147672490/100000000:ℝ)≤u dc (1049/1000) ∧ u dc (1049/1000)≤147672494/100000000 ∧
    (94738001/100000000:ℝ)≤ speed dc (1049/1000) ∧ speed dc (1049/1000)≤47369003/50000000 := by
  have hh := diagonal_cage (by norm_num) (by norm_num)
    ⟨diagonal_reference_trig.1.le,diagonal_reference_trig.2.1.le⟩
    ⟨diagonal_reference_trig.2.2.1.le,diagonal_reference_trig.2.2.2.le⟩
  norm_num at hh
  exact ⟨by linarith [hh.1],by linarith [hh.2.1],by linarith [hh.2.2.1],by linarith [hh.2.2.2]⟩

lemma join_reference_coordinates :
    (143261781/100000000:ℝ)≤u (1/2) (29/25) ∧ u (1/2) (29/25)≤17907723/12500000 ∧
    (19864067/20000000:ℝ)≤ speed (1/2) (29/25) ∧ speed (1/2) (29/25)≤99320339/100000000 := by
  simp only [u,speed,MixedCorner.join]
  exact ⟨by linarith [join_reference_trig.2.2.1],by linarith [join_reference_trig.2.2.2],
    by linarith [join_reference_trig.1],by linarith [join_reference_trig.2.1]⟩

lemma late_reference_coordinates :
    (2855619/2000000:ℝ)≤u dc (11/10) ∧ u dc (11/10)≤7139049/5000000 ∧
    (1940901/2000000:ℝ)≤ speed dc (11/10) ∧ speed dc (11/10)≤9704509/10000000 := by
  have hh := diagonal_cage (by norm_num) (by norm_num)
    ⟨late_reference_trig.1.le,late_reference_trig.2.1.le⟩
    ⟨late_reference_trig.2.2.1.le,late_reference_trig.2.2.2.le⟩
  norm_num at hh
  exact ⟨by linarith [hh.1],by linarith [hh.2.1],by linarith [hh.2.2.1],by linarith [hh.2.2.2]⟩

private lemma reference_transfer {B φ ul uu vl vu : ℝ}
    (hu : ul≤u B φ ∧ u B φ≤uu) (hv : vl≤ speed B φ ∧ speed B φ≤vu)
    (hl : ul∈PHeightBounds.heights) (hh : uu∈PHeightBounds.heights) (hvl : 0≤vl) :
    PHeightTaylor.poly ul≤PHeightTaylor.poly (u B φ) ∧
    PHeightTaylor.d1 ul*vl≤PHeightTaylor.d1 (u B φ)*speed B φ ∧
    PHeightTaylor.d1 (u B φ)*speed B φ≤PHeightTaylor.d1 uu*vu := by
  have hud : u B φ∈PHeightBounds.heights := ⟨hl.1.trans hu.1,hu.2.trans hh.2⟩
  have hdl := PHeightTaylor.d1_monotone hl hud hu.1
  have hdu := PHeightTaylor.d1_monotone hud hh hu.2
  exact ⟨PHeightTaylor.poly_monotone hl hud hu.1,
    mul_le_mul hdl hv.1 hvl (PHeightTaylor.d1_positive hud).le,
    mul_le_mul hdu hv.2 (hvl.trans hv.1) (PHeightTaylor.d1_positive hh).le⟩

lemma diagonal_reference : (11222/12500:ℝ)<f dc (1049/1000) ∧
    |fAngle dc (1049/1000)|<(1/1000:ℝ) := by
  have hc := diagonal_reference_coordinates
  have hh := reference_transfer ⟨hc.1,hc.2.1⟩ ⟨hc.2.2.1,hc.2.2.2⟩
    (by norm_num [PHeightBounds.heights]) (by norm_num [PHeightBounds.heights]) (by norm_num)
  norm_num [PHeightTaylor.poly,PHeightTaylor.d1,PHeightTaylor.c0,PHeightTaylor.c1,
    PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r] at hh
  constructor
  · dsimp [f,PHeightTaylor.poly,PHeightTaylor.c0,PHeightTaylor.c1,
      PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r]
    rw [MixedCorner.diagonal]
    linarith [diagonal_label]
  · rw [abs_lt]
    dsimp [fAngle,PHeightTaylor.d1,PHeightTaylor.c1,PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r]
    constructor <;> linarith [hh.2.1,hh.2.2]

lemma join_reference : (45011/50000:ℝ)<f (1/2) (29/25) ∧
    |fAngle (1/2) (29/25)|<(1/2500:ℝ) := by
  have hc := join_reference_coordinates
  have hh := reference_transfer ⟨hc.1,hc.2.1⟩ ⟨hc.2.2.1,hc.2.2.2⟩
    (by norm_num [PHeightBounds.heights]) (by norm_num [PHeightBounds.heights]) (by norm_num)
  norm_num [PHeightTaylor.poly,PHeightTaylor.d1,PHeightTaylor.c0,PHeightTaylor.c1,
    PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r] at hh
  constructor
  · simp only [f,MixedCorner.join]
    norm_num [MixedThree.negativeCore]
    dsimp [PHeightTaylor.poly,PHeightTaylor.c0,PHeightTaylor.c1,
      PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r]
    linarith [hh.1]
  · rw [abs_lt]
    dsimp [fAngle,PHeightTaylor.d1,PHeightTaylor.c1,PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r]
    constructor <;> linarith [hh.2.1,hh.2.2]

lemma late_reference : (89849/100000:ℝ)<f dc (11/10) ∧ 0<fAngle dc (11/10) := by
  have hc := late_reference_coordinates
  have hh := reference_transfer ⟨hc.1,hc.2.1⟩ ⟨hc.2.2.1,hc.2.2.2⟩
    (by norm_num [PHeightBounds.heights]) (by norm_num [PHeightBounds.heights]) (by norm_num)
  norm_num [PHeightTaylor.poly,PHeightTaylor.d1,PHeightTaylor.c0,PHeightTaylor.c1,
    PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r] at hh
  constructor
  · dsimp [f,PHeightTaylor.poly,PHeightTaylor.c0,PHeightTaylor.c1,
      PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r]
    rw [MixedCorner.diagonal]
    linarith [diagonal_label]
  · dsimp [fAngle,PHeightTaylor.d1,PHeightTaylor.c1,PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r]
    linarith [hh.2.2]

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Corner
end
end
end
