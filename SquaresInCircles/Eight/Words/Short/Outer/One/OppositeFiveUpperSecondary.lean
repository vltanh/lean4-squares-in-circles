module

public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveData
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates

/-!
# Eight squares: both upper secondary owners on opposite edge five

The two completed circle squares use the written constants mu and nu.
The prescribed quadratic maximizer has positive multiplier, and the
single displayed quartic proves monotonicity on the entire angle half: on `[0, 3/8]` it is a
positive combination of the products `x^i (3/8 - x)^(4 - i)` (`quartic_lower`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive.UpperSecondary
open CommonQuarter CorePairGeometry Arithmetic Polynomial

def mu : ℝ := 11/200
def nu : ℝ := 41/125
def aQ : ℚ := 9575/1804
def b0Q (r : Bool) : ℚ := qQ r/(2*(11/200))
def bcQ (r : Bool) : ℚ := 1-PQ r/(2*(41/125))
def bsQ (r : Bool) : ℚ := 1-tQ r/(2*(41/125))
def a : ℝ := aQ
def b (r : Bool) (u : ℝ) : ℝ :=
  (b0Q r:ℝ)+(bcQ r:ℝ)*Real.cos u+(bsQ r:ℝ)*Real.sin u
def bD (r : Bool) (u : ℝ) : ℝ :=
  -(bcQ r:ℝ)*Real.sin u+(bsQ r:ℝ)*Real.cos u
def k0 (r : Bool) : ℝ := c+(-p r+q r+P r+t r)/2-Q0*(mu+nu)-
  ((p r)^2+(q r)^2)/(4*mu)-((P r)^2+(t r)^2)/(4*nu)
def value (r : Bool) (u : ℝ) : ℝ := Real.pi/2+u+k0 r+(b r u)^2/(4*a)
def first (r : Bool) (u : ℝ) : ℝ := 1+b r u*bD r u/(2*a)
def quartic (r : Bool) : ℚ[X] :=
  (1+X^2)^2+
    (C (b0Q r)*(1+X^2)+C (bcQ r)*(1-X^2)+C (2*bsQ r)*X)*
      (C (-2*bcQ r)*X+C (bsQ r)*(1-X^2))*C (1/(2*aQ))

lemma a_identity : a=1/(4*mu)+1/(4*nu) := by norm_num [a,aQ,mu,nu]
lemma a_positive : 0<a := by norm_num [a,aQ]
lemma b_identity (r : Bool) (u : ℝ) : b r u=q r/(2*mu)+
    (1-P r/(2*nu))*Real.cos u+(1-t r/(2*nu))*Real.sin u := by
  simp [b,b0Q,bcQ,bsQ,q,P,t,mu,nu]
lemma b_positive (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) : 0<b r u := by
  have ht := positive_trig hu
  cases r <;> norm_num [b,b0Q,bcQ,bsQ,qQ,PQ,tQ] <;>
    linarith [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1]

lemma b_hasDerivAt (r : Bool) (u : ℝ) : HasDerivAt (b r) (bD r u) u := by
  have hh := (((Real.hasDerivAt_cos u).const_mul (bcQ r:ℝ)).const_add (b0Q r:ℝ)).fun_add
    ((Real.hasDerivAt_sin u).const_mul (bsQ r:ℝ))
  exact hh.congr_deriv (by simp only [bD]; ring)
lemma value_hasDerivAt (r : Bool) (u : ℝ) : HasDerivAt (value r) (first r u) u := by
  have hh := (((hasDerivAt_id' u).const_add (Real.pi/2)).add_const (k0 r)).fun_add
    (((b_hasDerivAt r u).fun_pow 2).div_const (4*a))
  refine hh.congr_deriv ?_
  have ha := a_positive.ne'
  simp only [first]
  field_simp
  norm_num
  ring

lemma quartic_lower (r : Bool) {x : ℝ} (hx : x∈Icc 0 (3/8:ℝ)) :
    (17/50:ℝ)<aeval x (quartic r) := by
  have h2 : 0≤3/8-x := sub_nonneg.2 hx.2
  have hb := And.intro (pow_nonneg hx.1 4) <| And.intro (mul_nonneg (pow_nonneg hx.1 3) h2) <|
    And.intro (mul_nonneg (pow_nonneg hx.1 2) (pow_nonneg h2 2)) <|
    And.intro (mul_nonneg hx.1 (pow_nonneg h2 3)) (pow_nonneg h2 4)
  cases r <;>
    simp only [quartic,b0Q,bcQ,bsQ,qQ,PQ,tQ,aQ,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,
      aeval_X,eq_ratCast] <;>
    push_cast <;>
    linarith [hb.1,hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2]

lemma first_identity (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) :
    (1+(half u)^2)^2*first r u=aeval (half u) (quartic r) := by
  have ht := half_trig hu
  have hd : 1+(half u)^2≠0 := by positivity
  dsimp [first,b,bD,quartic]
  simp only [map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  rw [ht.1,ht.2]
  push_cast
  dsimp [a]
  field_simp [hd,show (aQ:ℝ)≠0 by norm_num [aQ]]

lemma first_positive (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) : 0<first r u := by
  have hq := quartic_lower r ⟨(half_bounds hu).1,(half_bounds hu).2.le⟩
  rw [←first_identity r hu] at hq
  exact (mul_pos_iff_of_pos_left (by positivity : 0<(1+(half u)^2)^2)).mp (by linarith)

lemma monotone (r : Bool) : MonotoneOn (value r) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun u _ => (value_hasDerivAt r u).continuousAt.continuousWithinAt)
    (fun u _ => value_hasDerivAt r u)
    (fun u hu => (first_positive r (Ioo_subset_Icc_self hu)).le)

lemma initial (r : Bool) : (8981/10000:ℝ)<value r 0 := by
  have hp : (314159/200000:ℝ)<Real.pi/2 := by linarith [pi_hand_enclosure.1]
  cases r <;> norm_num [value,k0,b,b0Q,bcQ,bsQ,a,aQ,mu,nu,c,p,q,P,t,pQ,qQ,PQ,tQ,Q0] <;>
    linarith

lemma circle_square {a b X Y m : ℝ} (hs : OuterState a b) (hm : 0< m) :
    -m*Q0-(X^2+Y^2)/(4*m)≤X*(a+1/2)+Y*(b+1/2) := by
  have hsq := add_nonneg (sq_nonneg (2*m*(a+1/2)+X)) (sq_nonneg (2*m*(b+1/2)+Y))
  have he : (2*m*(a+1/2)+X)^2+(2*m*(b+1/2)+Y)^2=
      4*m*(m*Q0+(X^2+Y^2)/(4*m)+X*(a+1/2)+Y*(b+1/2)) := by
    have hd : 4*m*((X^2+Y^2)/(4*m))=X^2+Y^2 := by
      field_simp [hm.ne']
    linear_combination 4*m^2*hs.2.2-hd
  have hh : 0≤ m*Q0+(X^2+Y^2)/(4*m)+X*(a+1/2)+Y*(b+1/2) := by
    apply (mul_nonneg_iff_of_pos_left (by positivity : 0<4*m)).mp
    rw [←he]
    exact hsq
  linarith

lemma original_lower (r : Bool) {a b A B u : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hu : u∈Icc 0 (7/10))
    (hm : (1+Real.cos u+Real.sin u)/2≤-b+A*Real.cos u+B*Real.sin u) :
    value r u≤Real.pi/2+u+c+p r*a-q r*b-P r*A-t r*B := by
  obtain ⟨l,hl_def⟩ : ∃ l,l=UpperSecondary.b r u/(2*UpperSecondary.a) := ⟨_,rfl⟩
  have hl : 0≤l := hl_def ▸ (div_pos (b_positive r hu) (by linarith [a_positive])).le
  have hsrc := circle_square (X:=p r) (Y:=l-q r) (m:=mu) hs (by norm_num [mu])
  have htgt := circle_square (X:=-(P r)-l*Real.cos u) (Y:=-(t r)-l*Real.sin u)
    (m:=nu) ht (by norm_num [nu])
  have hsep := mul_le_mul_of_nonneg_left hm hl
  have hcircle := Real.sin_sq_add_cos_sq u
  have hquad :
      -mu*Q0-((p r)^2+(l-q r)^2)/(4*mu)-nu*Q0-
        ((-(P r)-l*Real.cos u)^2+(-(t r)-l*Real.sin u)^2)/(4*nu)+
          l*(Real.cos u+Real.sin u)=
      k0 r-c-(-p r+q r+P r+t r)/2+(UpperSecondary.b r u*l-UpperSecondary.a*l^2) := by
    rw [b_identity r u,a_identity]
    simp only [k0,mu,nu]
    linear_combination (-125/164)*l^2*hcircle
  have hopt : UpperSecondary.b r u*l-UpperSecondary.a*l^2=
      (UpperSecondary.b r u)^2/(4*UpperSecondary.a) := by
    rw [hl_def]
    field_simp [a_positive.ne']
    ring
  rw [hopt] at hquad
  dsimp only [value]
  linarith only [hsrc,htgt,hsep,hquad]

theorem original (r : Bool) {a b A B u : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hu : u∈Icc 0 (7/10))
    (hm : (1+Real.cos u+Real.sin u)/2≤-b+A*Real.cos u+B*Real.sin u) :
    (8981/10000:ℝ)<Real.pi/2+u+c+p r*a-q r*b-P r*A-t r*B :=
  ((initial r).trans_le ((monotone r) (by norm_num) hu hu.1)).trans_le
    (original_lower r hs ht hu hm)

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive.UpperSecondary
