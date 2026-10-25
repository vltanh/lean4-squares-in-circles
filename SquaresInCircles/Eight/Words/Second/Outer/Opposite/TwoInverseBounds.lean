module

public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoInverse

/-!
# Eight squares: whole-domain bounds for the physical inverse-contact derivative

The interval is the complete shifted outer-circle range.  Three
rational functions are controlled by concavity and their two physical
range endpoints.  The remaining derivative is bounded by a circle
support and one quintic, whose single expansion has a positive
quadratic reserve on the whole range.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo.Inverse

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio)

abbrev q := NegativeTwo.Inverse.q
abbrev N := NegativeTwo.Inverse.N
abbrev factor := NegativeTwo.Inverse.factor
abbrev K := NegativeTwo.Inverse.K
def interval : Set ℝ := Icc (1399/1000) (383/200)
def mass (u : ℝ) : ℝ := u^3*q u
def massD (u : ℝ) : ℝ := 3*(Q0+1)*u^2-8*u^3
def massDD (u : ℝ) : ℝ := 6*(Q0+1)*u-24*u^2

lemma range_data {u : ℝ} (hu : u∈interval) :
    0<u ∧ (1357/1250:ℝ)≤q u := by
  constructor
  · linarith [hu.1]
  · norm_num [q,NegativeTwo.Inverse.q,Q0]
    linarith [hu.2]

lemma mass_hasDerivAt (u : ℝ) : HasDerivAt mass (massD u) u := by
  have hd := ((hasDerivAt_id' u).fun_pow 3).fun_mul (NegativeTwo.Inverse.q_hasDerivAt u)
  exact hd.congr_deriv (by dsimp [massD,NegativeTwo.Inverse.q]; norm_num; ring)

lemma massD_hasDerivAt (u : ℝ) : HasDerivAt massD (massDD u) u := by
  have hd := (((hasDerivAt_id' u).fun_pow 2).const_mul (3*(Q0+1))).fun_sub
    (((hasDerivAt_id' u).fun_pow 3).const_mul 8)
  exact hd.congr_deriv (by dsimp [massDD]; norm_num; ring)

lemma mass_lower {u : ℝ} (hu : u∈interval) : (4:ℝ)< mass u := by
  have hh := positive_of_second_nonpos (f := fun t => mass t-4)
    (d := massD) (dd := massDD) hu
    (fun t _ => (mass_hasDerivAt t).sub_const 4)
    (fun t _ => massD_hasDerivAt t)
    (fun t ht => by
      have hp := mul_nonneg (show 0≤t by linarith [ht.1])
        (show 0≤4*t-(Q0+1) by norm_num [Q0]; linarith [ht.1])
      dsimp [massDD]
      nlinarith)
    (by norm_num [mass,q,NegativeTwo.Inverse.q,Q0])
    (by norm_num [mass,q,NegativeTwo.Inverse.q,Q0])
  linarith

lemma factor_upper {u : ℝ} (hu : u∈interval) : factor u<963/1000 := by
  have hd := range_data hu
  have hq : 0<q u := by linarith [hd.2]
  apply (div_lt_iff₀ (mul_pos hd.1 hq)).2
  have hp := mul_nonneg (sub_nonneg.mpr hu.1) (sub_nonneg.mpr hu.2)
  dsimp [q,NegativeTwo.Inverse.q]
  norm_num [Q0]
  nlinarith [hu.1,hu.2]

lemma K_lower {u : ℝ} (hu : u∈interval) : -(1/200:ℝ)<K u := by
  have hpos : 0≤3*(u+59/20) := by linarith [hu.1]
  have hp := mul_nonneg (sq_nonneg (u-59/40)) hpos
  have he : K u=K (59/40)+(21/8000)*(u-59/40)+
      3*(u-59/40)^2*(u+59/20) := by
    norm_num [K,NegativeTwo.Inverse.K,Q0]
    ring
  rw [he]
  norm_num [K,NegativeTwo.Inverse.K,Q0]
  nlinarith [hu.1]

def upperNumerator (u : ℝ) : ℝ := (371/1000)*mass u-K u
def upperD (u : ℝ) : ℝ :=
  -(371/125)*u^3+3*((371/1000)*(Q0+1)-3)*u^2+5*Q0
def upperDD (u : ℝ) : ℝ :=
  -(1113/125)*u^2+6*((371/1000)*(Q0+1)-3)*u

lemma upper_hasDerivAt (u : ℝ) : HasDerivAt upperNumerator (upperD u) u := by
  have hK := ((((hasDerivAt_id' u).fun_pow 3).const_mul 3).fun_sub
    ((hasDerivAt_id' u).const_mul (5*Q0))).add_const (Q0*(Q0+1))
  exact (((mass_hasDerivAt u).const_mul (371/1000)).fun_sub hK).congr_deriv
    (by dsimp [upperD,massD]; norm_num; ring)

lemma upperD_hasDerivAt (u : ℝ) : HasDerivAt upperD (upperDD u) u := by
  have hd := ((((hasDerivAt_id' u).fun_pow 3).const_mul (-(371/125:ℝ))).fun_add
    (((hasDerivAt_id' u).fun_pow 2).const_mul (3*((371/1000)*(Q0+1)-3)))).add_const (5*Q0)
  exact hd.congr_deriv (by dsimp [upperDD]; norm_num; ring)

lemma upper_positive {u : ℝ} (hu : u∈interval) : 0<upperNumerator u :=
  positive_of_second_nonpos hu
    (fun t _ => upper_hasDerivAt t) (fun t _ => upperD_hasDerivAt t)
    (fun t ht => by
      have hp : 0≤t := by linarith [ht.1]
      norm_num [upperDD,Q0]
      nlinarith [sq_nonneg t])
    (by norm_num [upperNumerator,mass,K,NegativeTwo.Inverse.K,q,NegativeTwo.Inverse.q,Q0])
    (by norm_num [upperNumerator,mass,K,NegativeTwo.Inverse.K,q,NegativeTwo.Inverse.q,Q0])

lemma K0_bounds {u : ℝ} (hu : u∈interval) :
    -(1/500:ℝ)<K u/mass u ∧ K u/mass u<371/1000 := by
  have hm := mass_lower hu
  have hm0 : 0< mass u := by linarith
  constructor
  · apply (lt_div_iff₀ hm0).2
    linarith [K_lower hu]
  · apply (div_lt_iff₀ hm0).2
    have hh := upper_positive hu
    dsimp [upperNumerator] at hh
    linarith

def quintic (u : ℝ) : ℝ :=
  (351/2000)*u^3*(q u)^2-(Q0-(37/20)*u)*N u

lemma quintic_expansion (t : ℝ) :
    quintic (9/5+t)=512687530359/1562500000000-
      (884171885847/312500000000)*t+
      (849004292517/62500000000)*t^2-
      (19499756129/12500000000)*t^3+
      (3584061/1250000)*t^4+(351/500)*t^5 := by
  norm_num [quintic,q,N,NegativeTwo.Inverse.q,NegativeTwo.Inverse.N,Q0]
  ring

lemma quintic_positive {u : ℝ} (hu : u∈interval) : (17/100:ℝ)<quintic u := by
  let t : ℝ := u-9/5
  have ht : |t|≤401/1000 := by
    rw [abs_le]
    dsimp [t]
    constructor <;> linarith [hu.1,hu.2]
  have ht2 := sq_abs t
  have ht3 : |t^3|≤(401/1000)*t^2 := by
    rw [abs_pow]
    have hh := mul_le_mul_of_nonneg_right ht (sq_nonneg t)
    nlinarith
  have hp3 := pow_le_pow_left₀ (abs_nonneg t) ht 3
  have ht5 : |t^5|≤(401/1000)^3*t^2 := by
    rw [abs_pow]
    have hh := mul_le_mul_of_nonneg_right hp3 (sq_nonneg t)
    nlinarith
  have h3 := (abs_le.mp ht3).2
  have h5 := (abs_le.mp ht5).1
  have h4 : 0≤t^4 := by positivity
  have he := quintic_expansion t
  have hut : 9/5+t=u := by dsimp [t]; ring
  rw [hut] at he
  have hlin : -(283/100)*|t|≤-(884171885847/312500000000)*t := by
    nlinarith [le_abs_self t,neg_le_abs t,abs_nonneg t]
  have hlower : (41/125)-(283/100)*|t|+(129/10)*t^2<quintic u := by
    nlinarith [sq_nonneg t]
  have hsq := sq_nonneg (|t|-283/2580)
  nlinarith

lemma circle_support {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (37/20)*U b+(351/500)*W b<Q0 := by
  have hc := UW_circle (outer_domain hb)
  have hu := U_positive (outer_domain hb)
  have hw : 0<W b := by dsimp [W]; linarith [hb.1]
  have hs := sq_nonneg ((37/20)*W b-(351/500)*U b)
  have he : ((37/20)*U b+(351/500)*W b)^2+
      ((37/20)*W b-(351/500)*U b)^2=
      ((37/20:ℝ)^2+(351/500:ℝ)^2)*Q0 := by
    linear_combination ((37/20:ℝ)^2+(351/500:ℝ)^2)*hc
  norm_num [Q0] at he ⊢
  nlinarith

lemma actual_height_derivative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    ratio b*PJCritical.heightFactorD (U b)<1/4 := by
  have hu := U_positive (outer_domain hb)
  have hi : U b∈interval := ⟨(UW_bounds hb).1.le,(UW_bounds hb).2.1.le⟩
  have hq : 0<q (U b) := by linarith [(range_data hi).2]
  have hw : 0≤W b := by dsimp [W]; linarith [hb.1]
  have he : ratio b*PJCritical.heightFactorD (U b)=
      W b*N (U b)/((U b)^3*(q (U b))^2) := by
    dsimp [ratio,PJCritical.heightFactorD,NegativeTwo.Inverse.factorD,U,W]
    field_simp [hu.ne',hq.ne']
  rw [he]
  apply (div_lt_iff₀ (mul_pos (pow_pos hu 3) (sq_pos_of_pos hq))).2
  by_cases hN : N (U b)≤0
  · have hp := mul_nonpos_of_nonneg_of_nonpos hw hN
    have hd := mul_pos (pow_pos hu 3) (sq_pos_of_pos hq)
    nlinarith
  · have hNpos : 0<N (U b) := lt_of_not_ge hN
    have hs := mul_lt_mul_of_pos_right (circle_support hb) hNpos
    have hp := quintic_positive hi
    dsimp [quintic] at hp
    nlinarith

end SquaresInCircles.Eight.SecondWord.OppositeTwo.Inverse
