module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3EndpointSupport

/-!
# The thirty-four original EH1/BT3 norm comparisons

Uncompiled Section 8. A negative endpoint modifies one of H, G, B;
a positive endpoint modifies H, B, or the actual two-angle D norm.
Only the positive D norm uses the tilted-coefficient upper bound.
The sorted small-low D term is absent from both sides of the same
three-norm identity, rather than silently replaced by a full norm.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.EndpointNorms
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open Certificate EndpointInputs EndpointSupport
open PositiveTD.Certificate (taylor_bounds)

abbrev pAt (r : Row) (ep : Split) (x : ℝ) : ℝ :=
  min (pairA r x (index r)) (pairB r ep x (index r))
abbrev qAt (r : Row) (ep : Split) (x : ℝ) : ℝ :=
  max (pairA r x (index r)) (pairB r ep x (index r))

def signedAngle (r : Row) (x : ℝ) (i : Fin 4) : ℝ :=
  if equal r ∨ i≠index r then 0 else if positive r then argument r x else -argument r x

def normAt (r : Row) (ep : Split) (x : ℝ) (i : Fin 4) : ℝ :=
  if active r i then pairNorm (pairA r x i) (pairB r ep x i) (signedAngle r x i) else 0

def actualExtra (r : Row) (ep : Split) (x : ℝ) : ℝ :=
  if equal r then 0
  else if positive r then pAt r ep x*(PositiveAngularEnvelope.phi (argument r x)-1)-(1/200)*argument r x
  else qAt r ep x*(Real.cos (argument r x)-1)

def actualA (r : Row) (ep : Split) (x : ℝ) : ℝ :=
  actualBase r ep x+charge (family r) (gainArgument r (thetaAt r x))+actualExtra r ep x

def increment (r : Row) (ep : Split) (x : ℝ) : ℝ :=
  if equal r then 0
  else if positive r then U R (pAt r ep x) (qAt r ep x) (argument r x)-(1/200)*argument r x
  else V R (pAt r ep x) (qAt r ep x) (argument r x)

def value (r : Row) (ep : Split) (x : ℝ) : ℝ :=
  baseline (family r) (thetaAt r x) (aAt ep (thetaAt r x)) (zAt ep (thetaAt r x))+
    charge (family r) (gainArgument r (thetaAt r x))+increment r ep x

lemma norm_nonnegative (r : Row) (ep : Split) (x : ℝ) (i : Fin 4) :
    0≤normAt r ep x i := by
  unfold normAt
  split <;> first | exact Real.sqrt_nonneg _ | exact le_rfl

lemma sorted_norm (a b t : ℝ) : pairNorm (min a b) (max a b) t=pairNorm a b t := by
  rcases le_total a b with h|h
  · rw [min_eq_left h,max_eq_right h]
  · rw [min_eq_right h,max_eq_left h,pairNorm_symm]

lemma active_index (r : Row) : active r (index r) := by
  cases r <;> simp [active,family,index]

lemma negative_index (r : Row) (he : equal r=false) (hn : positive r=false) :
    index r≠(3:Fin 4) := by
  cases r with
  | lowEqual => simp [equal] at he
  | lowNegative => decide
  | smallHigh i => fin_cases i <;> decide
  | farPositive i => simp [positive] at hn
  | farNegative i => fin_cases i <;> decide
  | farEqual => simp [equal] at he
  | farHigh i upper => fin_cases i <;> simp [index]

lemma zero_square_bound (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) (i : Fin 4) :
    (pairA r x i)^2+(pairB r ep x i)^2≤aeval x (normZero r ep i) := by
  have hc := c_upper r ep hx
  have hc0 := (c_positive r ep hx).le
  have hsq := pow_le_pow_left₀ hc0 hc 2
  fin_cases i <;> simp [pairA,pairB,normZero]
  · linarith
  · linarith

lemma product_nonnegative (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) (i : Fin 4) : 0≤aeval x (product r ep i) := by
  have hp := coefficient_bounds r hx
  have hc := (c_positive r ep hx).le.trans (c_upper r ep hx)
  fin_cases i <;> simp [product]
  · exact hp.1.le
  · exact mul_nonneg hp.1.le hp.2.1.le
  · exact mul_nonneg hp.2.1.le hp.2.2.1.le
  · exact hc

lemma product_upper (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) (i : Fin 4) :
    pairA r x i*pairB r ep x i≤aeval x (product r ep i) := by
  fin_cases i <;> simp [pairA,pairB,product]
  exact c_upper r ep hx

lemma product_exact (r : Row) (ep : Split) (x : ℝ) (i : Fin 4) (hi : i≠3) :
    aeval x (product r ep i)=pairA r x i*pairB r ep x i := by
  fin_cases i <;> simp_all [pairA,pairB,product]

lemma norm_square_bound (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) (i : Fin 4) :
    (normAt r ep x i)^2≤aeval x (P r ep i) := by
  by_cases hi : active r i
  · have hp := pair_positive r ep hx i
    have hz := zero_square_bound r ep hx i
    have hd := argument_domain r hx
    have ht := taylor_bounds hd
    by_cases he : equal r ∨ i≠index r
    · have hn := NonnegativeTotals.Analytic.norm_zero_square (pairA r x i) (pairB r ep x i)
      simpa only [normAt,ite_eq_left hi,signedAngle,ite_eq_left he,P,map_add,map_zero,add_zero,hn] using hz
    · have heq : equal r=false := by cases h : equal r <;> simp_all
      have hii : i=index r := by tauto
      by_cases hr : positive r
      · have hprod := mul_le_mul (product_upper r ep hx i) ht.2.2.1
          (transport_trig hd).2.2.1 (product_nonnegative r ep hx i)
        have hn := PairNormCalculus.pairNorm_sq hp.1 hp.2
          (show |argument r x|≤frameCap by rw [abs_of_nonneg hd.1]; exact hd.2)
        simp only [PairNormCalculus.pairEnergy,PairNormCalculus.pairProduct] at hn
        simp only [normAt,ite_eq_left hi,signedAngle,ite_eq_right he,ite_eq_left hr,P,
          map_add,map_mul,aeval_C,eq_ratCast,aeval_comp,d_eval]
        push_cast
        nlinarith only [hz,hprod,hn]
      · have hfalse : positive r=false := by cases h : positive r <;> simp_all
        have hin : i≠3 := by simpa only [hii] using negative_index r heq hfalse
        have hprod := mul_le_mul_of_nonneg_left ht.2.1 (mul_nonneg hp.1.le hp.2.le)
        have hn := PairNormCalculus.pairNorm_sq hp.1 hp.2
          (show |-argument r x|≤frameCap by rw [abs_neg,abs_of_nonneg hd.1]; exact hd.2)
        simp only [PairNormCalculus.pairEnergy,PairNormCalculus.pairProduct,Real.sin_neg] at hn
        simp only [normAt,ite_eq_left hi,signedAngle,ite_eq_right he,ite_eq_right hr,P,
          map_add,map_neg,map_mul,aeval_C,eq_ratCast,aeval_comp,d_eval,product_exact r ep x i hin]
        push_cast
        nlinarith only [hz,hprod,hn]
  · simp [normAt,P,hi]

lemma extra_lower (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) :
    aeval x (if equal r then 0 else if positive r then positiveExtra r else negativeExtra r)≤
      actualExtra r ep x := by
  have hd := argument_domain r hx
  have ht := taylor_bounds hd
  by_cases he : equal r
  · simp [actualExtra,he]
  · by_cases hp : positive r
    · have hcoeff := positive_coefficient_identity r ep hx (by simpa using hp)
      have hpos := pair_positive r ep hx (index r)
      have hm : 0≤pAt r ep x := le_min hpos.1.le hpos.2.le
      have hphi : aeval (argument r x) PositiveTD.Certificate.C10+
          aeval (argument r x) PositiveTD.Certificate.S11-1≤
            PositiveAngularEnvelope.phi (argument r x)-1 := by
        dsimp [PositiveAngularEnvelope.phi]
        linarith [ht.2.2.2.2.1,ht.2.1]
      have hh := mul_le_mul_of_nonneg_left hphi hm
      simp only [ite_eq_right he,ite_eq_left hp,actualExtra,positiveExtra,
        map_sub,map_mul,map_add,map_one,aeval_C,eq_ratCast,aeval_comp,d_eval]
      rw [←hcoeff]
      push_cast
      linarith only [hh]
    · have heq : equal r=false := by cases h : equal r <;> simp_all
      have hpq : positive r=false := by cases h : positive r <;> simp_all
      have hcoeff := negative_coefficient_bound r ep hx heq hpq
      have hpos := pair_positive r ep hx (index r)
      have hq : 0≤aeval x (larger r (index r)) :=
        (hpos.1.le.trans (le_max_left _ _)).trans hcoeff
      have h₁ := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1) hq
      have h₂ := mul_le_mul_of_nonpos_right hcoeff
        (sub_nonpos.mpr (Real.cos_le_one (argument r x)))
      simp only [ite_eq_right he,ite_eq_right hp,actualExtra,negativeExtra,
        map_mul,map_sub,map_one,aeval_comp,d_eval]
      linarith only [h₁,h₂]

lemma nonradical_lower (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) : aeval x (A r ep)≤actualA r ep x := by
  have hb := base_lower r ep hx
  have hg := gain_lower r hx
  have he := extra_lower r ep hx
  simpa only [Certificate.A,map_add,actualA] using add_le_add (add_le_add hb hg) he

lemma norm_sum_identity (r : Row) (ep : Split) (x : ℝ) (he : equal r=false) :
    (∑i,normAt r ep x i)=(∑i,zeroNorm r ep x i)-
      pairNorm (pairA r x (index r)) (pairB r ep x (index r)) 0+
      pairNorm (pairA r x (index r)) (pairB r ep x (index r))
        (if positive r then argument r x else -argument r x) := by
  let b := pairNorm (pairA r x (index r)) (pairB r ep x (index r))
      (if positive r then argument r x else -argument r x)-
    pairNorm (pairA r x (index r)) (pairB r ep x (index r)) 0
  have hi : ∀i,normAt r ep x i=zeroNorm r ep x i+if i=index r then b else 0 := by
    intro i
    by_cases hii : i=index r
    · subst i
      simp only [normAt,zeroNorm,active_index,if_true,signedAngle,he,
        Bool.false_eq_true,ne_eq,not_true_eq_false,or_self,if_false]
      dsimp [b]
      ring
    · simp [normAt,zeroNorm,signedAngle,he,hii]
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  dsimp [b]
  ring

lemma scalar_identity (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) : value r ep x=actualA r ep x-R*∑i,normAt r ep x i := by
  rw [value,baseline_identity r ep hx]
  by_cases he : equal r
  · simp only [actualA,actualExtra,increment,if_pos he]
    have hn : ∀i,normAt r ep x i=zeroNorm r ep x i := by
      intro i
      simp [normAt,zeroNorm,signedAngle,he]
    simp_rw [hn]
    ring
  · have heq : equal r=false := by cases h : equal r <;> simp_all
    rw [norm_sum_identity r ep x heq]
    by_cases hp : positive r
    · simp only [actualA,actualExtra,increment,if_neg he,if_pos hp,U,
        pAt,qAt,sorted_norm]
      ring
    · simp only [actualA,actualExtra,increment,if_neg he,if_neg hp,V,
        pAt,qAt,sorted_norm]
      ring

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.EndpointNorms
