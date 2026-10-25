module

public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Words.Common.JumpTwo
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterReferences
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveLowerPrimaryReference
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveUpperPrimary
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryNegativeGeometry
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryUpperAxial
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryUpperDiagonalData

/-!
# Eight squares: the exceptional upper primary owner's complete diagonal branch

The two polynomial signs are used exactly in the two signs of z to
bound omega'. The resulting angular curvature, join value and join
slope imply the stated .9004 reference bound on the entire branch.
-/

section
/-!
## The two upper A-primary supports

The source is the actual axial endpoint and the target uses the stated
whole-circle norm. Its exact perpendicular-square identity supplies the
Cauchy derivative bound on the whole upper angle half.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.EdgeFive.APrimary.Upper
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open ShortWord.MixedQuarter.Reference

def normA (r : Row) : ℝ := P r^2+t r^2+(4/5:ℝ)^2
def normB (r : Row) : ℝ := -(8/5)*t r
def normC (r : Row) : ℝ := (8/5)*P r
def N (r : Row) (x : ℝ) : ℝ := CircularNorm.norm (normA r) (normB r) (normC r) x
def G (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2+x+c r+(p r-4/5)*outerAxial+(4/5+P r+t r)/2+(4/5)*Real.sin x-CommonQuarter.radius*N r x
def first (r : Row) (x : ℝ) : ℝ :=
  1+(4/5)*Real.cos x-CommonQuarter.radius*CircularNorm.d1 (normA r) (normB r) (normC r) x

theorem energy_identity (r : Row) (x : ℝ) :
    CircularNorm.energy (normA r) (normB r) (normC r) x=
      (P r+(4/5)*Real.sin x)^2+(t r-(4/5)*Real.cos x)^2 := by
  dsimp [CircularNorm.energy,normA,normB,normC]
  linear_combination -(16/25:ℝ)*(Real.sin_sq_add_cos_sq x)
theorem energy_positive (r : Row) (hr : ARows r) (x : ℝ) :
    0<CircularNorm.energy (normA r) (normB r) (normC r) x := by
  have ht : 0<t r-(4/5)*Real.cos x := by linarith [(A_bounds r hr).2.2.1,Real.cos_le_one x]
  rw [energy_identity]
  nlinarith [sq_nonneg (P r+(4/5)*Real.sin x)]
theorem norm_positive (r : Row) (hr : ARows r) (x : ℝ) : 0<N r x :=
  CircularNorm.norm_pos (energy_positive r hr x)
theorem norm_sq (r : Row) (hr : ARows r) (x : ℝ) :
    (N r x)^2=(P r+(4/5)*Real.sin x)^2+(t r-(4/5)*Real.cos x)^2 := by
  exact (CircularNorm.norm_sq (energy_positive r hr x).le).trans (energy_identity r x)
theorem norm_hasDerivAt (r : Row) (hr : ARows r) (x : ℝ) :
    HasDerivAt (N r) (CircularNorm.d1 (normA r) (normB r) (normC r) x) x :=
  CircularNorm.norm_hasDerivAt (energy_positive r hr x)
theorem perpendicular_square (r : Row) (hr : ARows r) (x : ℝ) :
    (N r x)^2-(P r*Real.cos x+t r*Real.sin x)^2=
      (P r*Real.sin x-t r*Real.cos x+4/5)^2 := by
  have hn := norm_sq r hr x
  linear_combination hn+((16/25:ℝ)-P r^2-t r^2)*(Real.sin_sq_add_cos_sq x)
theorem cauchy (r : Row) (hr : ARows r) (x : ℝ) :
    |P r*Real.cos x+t r*Real.sin x|≤N r x := by
  have hh := perpendicular_square r hr x
  have hn := norm_positive r hr x
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (P r*Real.sin x-t r*Real.cos x+4/5)]
theorem norm_derivative_upper (r : Row) (hr : ARows r) (x : ℝ) :
    CircularNorm.d1 (normA r) (normB r) (normC r) x≤4/5 := by
  have hn := norm_positive r hr x
  have hh := (le_abs_self _).trans (cauchy r hr x)
  have he : CircularNorm.d1 (normA r) (normB r) (normC r) x=
      ((4/5)*(P r*Real.cos x+t r*Real.sin x))/N r x := by
    dsimp [CircularNorm.d1,CircularNorm.slope,normB,normC]
    change _/(2*N r x)=_
    field_simp [hn.ne']
    ring
  rw [he]
  apply (div_le_iff₀ hn).mpr
  nlinarith
theorem G_hasDerivAt (r : Row) (hr : ARows r) (x : ℝ) :
    HasDerivAt (G r) (first r x) x := by
  have h := (((hasDerivAt_id x).const_add
    (Real.pi/2+c r+(p r-4/5)*outerAxial+(4/5+P r+t r)/2)).add
      ((Real.hasDerivAt_sin x).const_mul (4/5))).sub
        ((norm_hasDerivAt r hr x).const_mul CommonQuarter.radius)
  convert h using 1
  · funext y; simp only [G,Pi.add_apply,Pi.sub_apply,id_eq]; ring
  · simp only [first]
theorem first_positive (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<first r x := by
  have hh := mul_le_mul_of_nonneg_left (norm_derivative_upper r hr x)
    (show 0≤CommonQuarter.radius by linarith [radius_bounds.1])
  dsimp [first]
  linarith [(positive_trig hx).1,radius_fine.2]
theorem G_monotone (r : Row) (hr : ARows r) : MonotoneOn (G r) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (G_hasDerivAt r hr x).continuousAt.continuousWithinAt)
    (fun x _ => G_hasDerivAt r hr x)
    (fun _ hx => (first_positive r hr (Ioo_subset_Icc_self hx)).le)

theorem initial (r : Row) (hr : ARows r) : (1449/1250:ℝ)<G r 0 := by
  -- the evaluation of `initialBox` at the angle zero, with a rational root bound for the norm
  have hn := norm_sq r hr 0
  have hp := (norm_positive r hr 0).le
  have hR := radius_fine
  have ha := ShortOuterZero.fine_axial_bounds
  have hpi := pi_hand_enclosure
  simp only [Real.sin_zero,Real.cos_zero,mul_zero,add_zero,mul_one] at hn
  simp only [G,Real.sin_zero,mul_zero,add_zero]
  rcases hr with rfl|rfl
  · norm_num [c,p,P,t] at hn ⊢
    have hN : N 0 0<221005/1000000 :=
      lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hn]; norm_num)
    have hRN := mul_le_mul hR.2.le hN.le hp (by norm_num)
    linarith
  · norm_num [c,p,P,t] at hn ⊢
    have hN : N 1 0<211874/1000000 :=
      lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hn]; norm_num)
    have hRN := mul_le_mul hR.2.le hN.le hp (by norm_num)
    linarith
theorem lower (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (1449/1250:ℝ)<G r x := (initial r hr).trans_le (G_monotone r hr (by norm_num) hx hx.1)

theorem original (r : Row) (hr : ARows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Primary r true a b A B x) : (1449/1250:ℝ)<cost r true a b A B x := by
  have hcoeff := coefficient_bounds r
  have hsource := ShortWord.MixedQuarter.outer_axial_lower (X:=p r-4/5) (Y:=q r) hs
    (by linarith [hcoeff.1]) (by linarith [hcoeff.2.2.1])
  have hdir : direction true = 1 := by
    simp [direction,ShortWord.MixedQuarter.direction]
  have he : Real.sqrt ((-P r-(4/5)*Real.sin x)^2+((4/5)*Real.cos x-t r)^2)=N r x := by
    dsimp only [N,CircularNorm.norm]
    congr 1
    rw [energy_identity]
    ring
  have htarg := outer_circle_lower (X:=-P r-(4/5)*Real.sin x) (Y:=(4/5)*Real.cos x-t r) ht
  rw [he] at htarg
  have hh := primary_support r true (lam:=4/5) (by norm_num) hm
    (S:=(p r-4/5)*outerAxial)
    (T:= -((-P r-(4/5)*Real.sin x)+((4/5)*Real.cos x-t r))/2-CommonQuarter.radius*N r x)
    (by rw [A_sign hr]; linarith [hsource])
    (by rw [A_sign hr,hdir]; linarith [htarg])
  have hv := lower r hr hx
  have hang : angle true x=Real.pi/2+x := by
    simp only [angle,ShortWord.MixedQuarter.angle,hdir]; ring
  rw [hang] at hh
  simp only [G,width] at hv hh
  linarith

end SquaresInCircles.Eight.ShortOuterOne.EdgeFive.APrimary.Upper
end
end
end

section
/-!
## The two lower A-primary supports and both halves

The original weak separator forces the angle cap `x < .226` (`forced_cap`), by the same geometric
argument as for the negative primary families (`Opposite.Primary.Negative.forced_cap`). Both target
endpoints then increase (`GA_monotone`, `GD_monotone`); the diagonal initial value is no smaller
than the axial one (`diagonal_initial`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.EdgeFive.APrimary
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open ShortWord.MixedQuarter.Reference
abbrev cap := Opposite.Primary.Negative.cap

def GA (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2-x+c r+(p r-1-P r)*outerAxial+1/2+Real.cos x/2+(1/2+outerAxial)*Real.sin x
def GD (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2-x+c r+(p r-1)*outerAxial-(P r+t r)*outerDiagonal+1/2+
    (1/2+outerDiagonal)*(Real.cos x+Real.sin x)
def GAd (x : ℝ) : ℝ := -1-Real.sin x/2+(1/2+outerAxial)*Real.cos x
def GDd (x : ℝ) : ℝ := -1+(1/2+outerDiagonal)*(Real.cos x-Real.sin x)

theorem forced_cap (r : Row) (hr : ARows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Primary r false a b A B x) : x<cap := by
  apply Opposite.Primary.Negative.forced_cap hs ht hx
  have hd : direction false = -1 := by
    simp [direction,ShortWord.MixedQuarter.direction]
  dsimp only [Primary] at hm
  rw [A_sign hr,hd] at hm
  simp only [width] at hm
  simp only [Opposite.Primary.width]
  linarith
theorem GA_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (GA r) (GAd x) x := by
  have h := ((((hasDerivAt_id x).neg).const_add
    (Real.pi/2+c r+(p r-1-P r)*outerAxial+1/2)).add
      ((Real.hasDerivAt_cos x).div_const 2)).add
        ((Real.hasDerivAt_sin x).const_mul (1/2+outerAxial))
  convert h using 1
  · funext y; simp only [GA,Pi.add_apply,Pi.neg_apply,id_eq]; ring
  · simp only [GAd]; ring
theorem GD_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (GD r) (GDd x) x := by
  have h := (((hasDerivAt_id x).neg).const_add
    (Real.pi/2+c r+(p r-1)*outerAxial-(P r+t r)*outerDiagonal+1/2)).add
      (((Real.hasDerivAt_cos x).add (Real.hasDerivAt_sin x)).const_mul (1/2+outerDiagonal))
  convert h using 1
  · funext y; simp only [GD,Pi.add_apply,Pi.neg_apply,id_eq]; ring
  · simp only [GDd]; ring
theorem GAd_positive {x : ℝ} (hx : x∈Icc 0 cap) : 0<GAd x := by
  have tr := Opposite.Primary.Negative.small_trig hx
  have ha : (957/500:ℝ)<1/2+outerAxial := by linarith [ShortOuterZero.fine_axial_bounds.1]
  have hh := mul_lt_mul'' ha tr.1 (by norm_num) (by norm_num)
  dsimp [GAd]
  linarith [tr.2.2]
theorem GDd_positive {x : ℝ} (hx : x∈Icc 0 cap) : 0<GDd x := by
  have tr := Opposite.Primary.Negative.small_trig hx
  have hd : (1399/1000:ℝ)<1/2+outerDiagonal := by linarith [ShortMixedZero.fine_diagonal_bounds.1]
  have hc : (749/1000:ℝ)<Real.cos x-Real.sin x := by linarith [tr.1,tr.2.2]
  have hh := mul_lt_mul'' hd hc (by norm_num) (by norm_num)
  dsimp [GDd]
  linarith
theorem GA_monotone (r : Row) : MonotoneOn (GA r) (Icc 0 cap) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (GA_hasDerivAt r x).continuousAt.continuousWithinAt)
    (fun x _ => GA_hasDerivAt r x)
    (fun _ hx => (GAd_positive (Ioo_subset_Icc_self hx)).le)
theorem GD_monotone (r : Row) : MonotoneOn (GD r) (Icc 0 cap) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (GD_hasDerivAt r x).continuousAt.continuousWithinAt)
    (fun x _ => GD_hasDerivAt r x)
    (fun _ hx => (GDd_positive (Ioo_subset_Icc_self hx)).le)

theorem initial (r : Row) (hr : ARows r) : (2697/2500:ℝ)<GA r 0 := by
  -- the lower endpoint of `initialBox` before its cast to `Interval (GA r 0)`
  let X := ((halfPi.add (Interval.point (c r))).add
    ((Interval.point (p r-1-P r)).mul axial)).add (Interval.point 1)
  have he : GA r 0=Real.pi/2+c r+(p r-1-P r)*outerAxial+1 := by
    simp only [GA,Real.sin_zero,Real.cos_zero]; ring
  have hh : (2697/2500:ℝ)<X.lo := by
    rcases hr with rfl|rfl <;> dsimp [X,c,p,P] <;> mixed_fixed
  rw [he]
  exact hh.trans_le X.mem.1
theorem diagonal_initial (r : Row) (_hr : ARows r) : GA r 0≤GD r 0 := by
  have hc := coefficient_bounds r
  have hP := mul_nonneg hc.2.1 (show 0≤outerAxial-outerDiagonal by
    linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2])
  have ht := mul_nonneg (show 0≤1-t r by linarith [hc.2.2.2.2.2])
    (show 0≤outerDiagonal by linarith [outer_endpoint_bounds.2.2.1])
  simp only [GA,GD,Real.sin_zero,Real.cos_zero]
  nlinarith
theorem axial_lower (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 cap) :
    (2697/2500:ℝ)<GA r x :=
  (initial r hr).trans_le (GA_monotone r (by norm_num [cap,Opposite.Primary.Negative.cap]) hx hx.1)
theorem diagonal_lower (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 cap) :
    (2697/2500:ℝ)<GD r x :=
  ((initial r hr).trans_le (diagonal_initial r hr)).trans_le
    (GD_monotone r (by norm_num [cap,Opposite.Primary.Negative.cap]) hx hx.1)

theorem lower_original (r : Row) (hr : ARows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Primary r false a b A B x) : (2697/2500:ℝ)<cost r false a b A B x := by
  have hsmall : x∈Icc 0 cap := ⟨hx.1,(forced_cap r hr hs ht hx hm).le⟩
  have tr := Opposite.Primary.Negative.small_trig hsmall
  have hc := coefficient_bounds r
  have hdir : direction false = -1 := by
    simp [direction,ShortWord.MixedQuarter.direction]
  have hsource := ShortWord.MixedQuarter.outer_axial_lower (X:=p r-1) (Y:=q r) hs
    (by linarith [hc.1]) (by linarith [hc.2.2.1])
  have hY : 0≤Real.cos x-t r := by linarith [tr.1,hc.2.2.2.2.2]
  have htarget := outer_endpoint_support (X:= -P r+Real.sin x) (Y:=Real.cos x-t r) ht hY
  rw [show -P r+Real.sin x+(Real.cos x-t r)=-P r+Real.sin x+Real.cos x-t r by ring] at htarget
  have hh := primary_support r false (lam:=1) (by norm_num) hm
    (S:=(p r-1)*outerAxial)
    (T:=min ((-P r+Real.sin x)*outerAxial)
      ((-P r+Real.sin x+Real.cos x-t r)*outerDiagonal))
    (by rw [A_sign hr]; linarith [hsource])
    (by rw [A_sign hr,hdir]; linarith [htarget])
  have hang : angle false x=Real.pi/2-x := by
    simp only [angle,ShortWord.MixedQuarter.angle,hdir]; ring
  rw [hang] at hh
  rcases le_total ((-P r+Real.sin x)*outerAxial)
    ((-P r+Real.sin x+Real.cos x-t r)*outerDiagonal) with hsplit|hsplit
  · rw [min_eq_left hsplit] at hh
    have hv := axial_lower r hr hsmall
    simp only [GA,width] at hv hh
    linarith
  · rw [min_eq_right hsplit] at hh
    have hv := diagonal_lower r hr hsmall
    simp only [GD,width] at hv hh
    linarith

theorem original (r : Row) (hr : ARows r) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Primary r upper a b A B x) : (2697/2500:ℝ)<cost r upper a b A B x := by
  cases upper
  · exact lower_original r hr hs ht hx hm
  · linarith [Upper.original r hr hs ht hx hm]

end SquaresInCircles.Eight.ShortOuterOne.EdgeFive.APrimary
end
end
end

section
/-!
## Both upper secondary owners on opposite edge five

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
    (fun _ hu => (first_positive r (Ioo_subset_Icc_self hu)).le)

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
end
end
end

section
/-!
## The six prescribed lower-half multipliers and scalar endpoints

The six source radical upper bounds are the displayed fixed rationals.
They prove the displayed source supports directly by positive squaring.
Axial monotonicity and diagonal concavity hold on the whole feasible
interval, before any fixed endpoint value is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Negative
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open ShortWord.MixedQuarter.Reference

def weight : Row→ℝ := ![93308/100000,11625/10000,100982/100000,108532/100000,110143/100000,112741/100000]
def normUpper : Row→ℝ := ![1880509701/1000000000,1386761738/1000000000,
  1332148407/1000000000,1176679496/1000000000,1452999491/1000000000,1241873719/1000000000]
def supportLower : Row→ℝ := ![-2397276/1000000,-1768154/1000000,-1696710/1000000,
  -1498695/1000000,-1850634/1000000,-1581731/1000000]
def S (r : Row) : ℝ := (weight r+q r-p r)/2-
  CommonQuarter.radius*Real.sqrt ((p r-weight r)^2+(q r)^2)
def X (r : Row) (x : ℝ) : ℝ := -P r+weight r*Real.sin x
def Y (r : Row) (x : ℝ) : ℝ := weight r*Real.cos x-t r
def axialValue (r : Row) (x : ℝ) : ℝ := Real.pi/2-x+c r+S r-P r*outerAxial+
  weight r/2+(weight r/2)*Real.cos x+weight r*(1/2+outerAxial)*Real.sin x
def axialD (r : Row) (x : ℝ) : ℝ :=
  -1-(weight r/2)*Real.sin x+weight r*(1/2+outerAxial)*Real.cos x
def diagonalValue (r : Row) (x : ℝ) : ℝ := Real.pi/2-x+c r+S r-(P r+t r)*outerDiagonal+
  weight r/2+weight r*(1/2+outerDiagonal)*(Real.sin x+Real.cos x)
def diagonalD (r : Row) (x : ℝ) : ℝ :=
  -1+weight r*(1/2+outerDiagonal)*(Real.cos x-Real.sin x)
def diagonalDD (r : Row) (x : ℝ) : ℝ :=
  -weight r*(1/2+outerDiagonal)*(Real.sin x+Real.cos x)

theorem weight_bounds (r : Row) : (23327/25000:ℝ)≤weight r ∧ weight r≤93/80 := by
  fin_cases r <;> norm_num [weight]
theorem weight_positive (r : Row) : 0<weight r := by linarith [(weight_bounds r).1]
theorem P_nonpositive (r : Row) (hr : r≠1) : P r≤0 := by
  fin_cases r
  all_goals first
    | (exfalso; exact hr rfl)
    | norm_num [P]

theorem source_norm_upper (r : Row) : Real.sqrt ((p r-weight r)^2+(q r)^2)<normUpper r := by
  have hs := Real.sq_sqrt (show 0≤(p r-weight r)^2+(q r)^2 by positivity)
  have hp := Real.sqrt_nonneg ((p r-weight r)^2+(q r)^2)
  fin_cases r <;> norm_num [p,q,weight,normUpper] at hs ⊢ <;> nlinarith

theorem source_support_lower (r : Row) : supportLower r<S r := by
  have hr := ShortWord.MixedQuarter.Reference.radius_fine
  have hn := source_norm_upper r
  have hp := Real.sqrt_nonneg ((p r-weight r)^2+(q r)^2)
  have hprod := mul_lt_mul'' hr.2 hn (by linarith [hr.1]) hp
  fin_cases r <;> norm_num [S,supportLower,weight,normUpper,p,q] at hprod ⊢ <;> linarith

theorem axial_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (axialValue r) (axialD r x) x := by
  have hh := (((((hasDerivAt_id' x).const_sub (Real.pi/2)).add_const (c r)).add_const (S r)
    ).sub_const (P r*outerAxial)).add_const (weight r/2)
  have hh' := (hh.fun_add ((Real.hasDerivAt_cos x).const_mul (weight r/2))).fun_add
    ((Real.hasDerivAt_sin x).const_mul (weight r*(1/2+outerAxial)))
  exact hh'.congr_deriv (by simp only [axialD]; ring)

theorem axialD_positive (r : Row) {x : ℝ} (hx : x∈Icc 0 cap) : (63/100:ℝ)<axialD r x := by
  have tr := small_trig hx
  have ha := ShortOuterZero.fine_axial_bounds.1
  have hp := mul_lt_mul'' (show (1914575671/1000000000:ℝ)<1/2+outerAxial by linarith)
    tr.1 (by norm_num) (by norm_num)
  have hbracket : (1/2+outerAxial)*Real.cos x-Real.sin x/2>
      (1914575671/1000000000:ℝ)*(6091/6250)-(22409/100000)/2 := by linarith [tr.2.2]
  have hmul := mul_le_mul_of_nonneg_right (weight_bounds r).1
    (show 0≤(1/2+outerAxial)*Real.cos x-Real.sin x/2 by linarith)
  have hlower := mul_lt_mul_of_pos_left hbracket (by norm_num : (0:ℝ)<23327/25000)
  dsimp [axialD]
  linarith only [hmul,hlower]

theorem axial_monotone (r : Row) : MonotoneOn (axialValue r) (Icc 0 cap) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (axial_hasDerivAt r x).continuousAt.continuousWithinAt)
    (fun x _ => axial_hasDerivAt r x)
    (fun x hx => by linarith [axialD_positive r (Ioo_subset_Icc_self hx)])

theorem diagonal_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (diagonalValue r) (diagonalD r x) x := by
  have hh := (((((hasDerivAt_id' x).const_sub (Real.pi/2)).add_const (c r)).add_const (S r)
    ).sub_const ((P r+t r)*outerDiagonal)).add_const (weight r/2)
  have hh' := hh.fun_add (((Real.hasDerivAt_sin x).fun_add (Real.hasDerivAt_cos x)).const_mul
    (weight r*(1/2+outerDiagonal)))
  exact hh'.congr_deriv (by simp only [diagonalD]; ring)
theorem diagonalD_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (diagonalD r) (diagonalDD r x) x := by
  have hh := (((Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)).const_mul
    (weight r*(1/2+outerDiagonal))).const_add (-1)
  exact hh.congr_deriv (by simp only [diagonalDD]; ring)
theorem diagonal_concave (r : Row) : ConcaveOn ℝ (Icc 0 cap) (diagonalValue r) := by
  apply concave_of_deriv2 (fun x _ => diagonal_hasDerivAt r x)
    (fun x _ => diagonalD_hasDerivAt r x)
  intro x hx
  have tr := small_trig hx
  dsimp [diagonalDD]
  have hh := mul_nonneg (mul_nonneg (weight_positive r).le
    (show 0≤1/2+outerDiagonal by linarith [outer_endpoint_bounds.2.2.1]))
    (show 0≤Real.sin x+Real.cos x by linarith [tr.1,tr.2.1])
  nlinarith

theorem axial_initial (r : Row) : threshold r<axialValue r 0 := by
  have hS := source_support_lower r
  have ha := ShortOuterZero.fine_axial_bounds
  have hpi : (314159/200000:ℝ)<Real.pi/2 := by linarith [pi_hand_enclosure.1]
  fin_cases r <;> norm_num [threshold,axialValue,c,p,q,P,t,weight,supportLower] at hS ⊢ <;> linarith

theorem diagonal_initial (r : Row) (hr : r≠1) : threshold r<diagonalValue r 0 := by
  have hS := source_support_lower r
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hpi : (314159/200000:ℝ)<Real.pi/2 := by linarith [pi_hand_enclosure.1]
  fin_cases r
  all_goals first
    | (exfalso; exact hr rfl)
    | (norm_num [threshold,diagonalValue,c,p,q,P,t,weight,supportLower] at hS ⊢; linarith)

private theorem r85_cast_lo {a b : ℝ} (h : Interval a=Interval b) (I : Interval b) (e : a=b) :
    (h.mpr I).lo=I.lo := by
  subst e
  rfl

def diagonalCapBox (r : Row) : Interval (diagonalValue r cap-S r) := by
  convert (((((halfPi.sub (Interval.point cap)).add (Interval.point (c r))).sub
    ((Interval.point (P r+t r)).mul ShortWord.MixedQuarter.Reference.diagonal)).add (Interval.point (weight r/2))).add (((Interval.point (weight r)).mul ((Interval.point (1/2)).add ShortWord.MixedQuarter.Reference.diagonal)).mul ((sine (by norm_num [cap] : 0≤cap)).add (cosine (by norm_num [cap] : 0≤cap))))) using 1
  dsimp [diagonalValue]
  ring

theorem diagonal_final (r : Row) (hr : r≠1) : (9309/10000:ℝ)<diagonalValue r cap := by
  have hh : (9309/10000:ℝ)<supportLower r+(diagonalCapBox r).lo := by
    unfold diagonalCapBox
    rw [r85_cast_lo _ _ (by dsimp [diagonalValue]; ring)]
    fin_cases r <;> norm_num at hr <;> dsimp [cap,c,P,t,weight,supportLower] <;> mixed_fixed
  have hb := (diagonalCapBox r).mem.1
  linarith [source_support_lower r]

theorem axial_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 cap) : threshold r<axialValue r x :=
  (axial_initial r).trans_le ((axial_monotone r) (by norm_num [cap]) hx hx.1)
theorem diagonal_lower (r : Row) (hr : r≠1) {x : ℝ} (hx : x∈Icc 0 cap) : threshold r<diagonalValue r x := by
  apply concave_gt_of_endpoints (diagonal_concave r) hx (diagonal_initial r hr)
  have hh := diagonal_final r hr
  dsimp [threshold]
  split_ifs <;> linarith

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Negative
end
end
end

section
/-!
## The two whole-branch polynomials for the exceptional primary owner

The positive-coordinate branch retains its affine radical lower bound.
Each displayed polynomial has an increasing derivative whose final
value is still negative, so its fixed final value bounds the complete
interval. The split is exactly the sign of the contact coordinate z.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper.OnePolynomial
open CommonQuarter CorePairGeometry Arithmetic

def N (s : ℝ) : ℝ := 2/5+(27563/10000)*s+(2/5)*s^2
def lowerT (s : ℝ) : ℝ := 19379/10000+(51/500)*s
def rootPolynomial : ℚ[X] :=
  C (14359/100000000)+C (4046684/10000000)*X-C (252601/250000)*X^2
def nonnegativePolynomial : ℚ[X] :=
  C (84442089456547/100000000000000)-C (24201302831342/10000000000000)*X+
    C (955780925704/1000000000000)*X^2+C (21490674984/100000000000)*X^3+
      C (36126167/100000000)*X^4+C (3723/200000)*X^5
def negativePolynomial : ℚ[X] :=
  C (12383828123/10000000000)-C (27563/10000)*X+
    C (13013321/10000000)*X^2+C (17667/40000)*X^4

lemma root_identity (s : ℝ) :
    aeval s rootPolynomial=Q0-(2/5-s)^2-(lowerT s)^2 := by
  norm_num [rootPolynomial,lowerT,Q0]
  ring

theorem lowerT_square {s : ℝ} (hs : s∈Icc (0:ℝ) (2/5)) :
    0≤Q0-(2/5-s)^2-(lowerT s)^2 := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (2/5)) (fun x : ℝ => aeval x rootPolynomial) :=
    concave_of_deriv2
      (fun x _ => CenteredMonomialBounds.aeval_hasDerivAt rootPolynomial x)
      (fun x _ => CenteredMonomialBounds.aeval_hasDerivAt rootPolynomial.derivative x)
      (fun x _ => by norm_num [rootPolynomial])
  have hh : (0:ℝ)<aeval s rootPolynomial := concave_gt_of_endpoints hc hs
    (by norm_num [rootPolynomial]) (by norm_num [rootPolynomial])
  rw [root_identity] at hh
  exact hh.le

lemma nonnegative_identity (s : ℝ) : aeval s nonnegativePolynomial=
    (73/100)*lowerT s*(lowerT s-1+s^2/2)^2-N s := by
  norm_num [nonnegativePolynomial,lowerT,N]
  ring

lemma nonnegative_derivative_increases :
    MonotoneOn (fun s : ℝ => aeval s nonnegativePolynomial.derivative) (Icc (0:ℝ) (2/5)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun s _ => (CenteredMonomialBounds.aeval_hasDerivAt nonnegativePolynomial.derivative s).continuousAt.continuousWithinAt)
    (fun s _ => CenteredMonomialBounds.aeval_hasDerivAt nonnegativePolynomial.derivative s)
  intro s hs
  have hs0 : 0≤ s := hs.1.le
  norm_num [nonnegativePolynomial]
  positivity

lemma nonnegative_derivative_final :
    aeval (2/5:ℝ) nonnegativePolynomial.derivative< -(29/20:ℝ) := by
  norm_num [nonnegativePolynomial]

lemma nonnegative_value_final : (13/250:ℝ)<aeval (2/5:ℝ) nonnegativePolynomial := by
  norm_num [nonnegativePolynomial]

lemma nonnegative_decreases :
    AntitoneOn (fun s : ℝ => aeval s nonnegativePolynomial) (Icc (0:ℝ) (2/5)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun s _ => (CenteredMonomialBounds.aeval_hasDerivAt nonnegativePolynomial s).continuousAt.continuousWithinAt)
    (fun s _ => CenteredMonomialBounds.aeval_hasDerivAt nonnegativePolynomial s)
  intro s hs
  have hh := nonnegative_derivative_increases (Ioo_subset_Icc_self hs)
    (by norm_num : (2/5:ℝ)∈Icc (0:ℝ) (2/5)) hs.2.le
  linarith [nonnegative_derivative_final]

theorem nonnegative_polynomial {s : ℝ} (hs : s∈Icc (0:ℝ) (2/5)) :
    0<(73/100)*lowerT s*(lowerT s-1+s^2/2)^2-N s := by
  have hh := nonnegative_decreases hs (by norm_num : (2/5:ℝ)∈Icc (0:ℝ) (2/5)) hs.2
  have hpos : (0:ℝ)<aeval s nonnegativePolynomial := by linarith [nonnegative_value_final]
  simpa only [nonnegative_identity] using hpos

lemma negative_identity (s : ℝ) : aeval s negativePolynomial=
    (9/10)*(1963/1000)*(963/1000+s^2/2)^2-N s := by
  norm_num [negativePolynomial,N]
  ring

lemma negative_derivative_increases :
    MonotoneOn (fun s : ℝ => aeval s negativePolynomial.derivative) (Icc (0:ℝ) (129/200)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun s _ => (CenteredMonomialBounds.aeval_hasDerivAt negativePolynomial.derivative s).continuousAt.continuousWithinAt)
    (fun s _ => CenteredMonomialBounds.aeval_hasDerivAt negativePolynomial.derivative s)
  intro s hs
  norm_num [negativePolynomial]
  positivity

lemma negative_derivative_final :
    aeval (129/200:ℝ) negativePolynomial.derivative< -(3/5:ℝ) := by
  norm_num [negativePolynomial]

lemma negative_value_final : (39/500:ℝ)<aeval (129/200:ℝ) negativePolynomial := by
  norm_num [negativePolynomial]

lemma negative_decreases :
    AntitoneOn (fun s : ℝ => aeval s negativePolynomial) (Icc (0:ℝ) (129/200)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun s _ => (CenteredMonomialBounds.aeval_hasDerivAt negativePolynomial s).continuousAt.continuousWithinAt)
    (fun s _ => CenteredMonomialBounds.aeval_hasDerivAt negativePolynomial s)
  intro s hs
  have hh := negative_derivative_increases (Ioo_subset_Icc_self hs)
    (by norm_num : (129/200:ℝ)∈Icc (0:ℝ) (129/200)) hs.2.le
  linarith [negative_derivative_final]

theorem negative_polynomial {s : ℝ} (hs : s∈Icc (0:ℝ) (129/200)) :
    0<(9/10)*(1963/1000)*(963/1000+s^2/2)^2-N s := by
  have hh := negative_decreases hs (by norm_num : (129/200:ℝ)∈Icc (0:ℝ) (129/200)) hs.2
  have hpos : (0:ℝ)<aeval s negativePolynomial := by linarith [negative_value_final]
  simpa only [negative_identity] using hpos

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper.OnePolynomial
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper.OneDiagonal
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open ShortWord.MixedQuarter.Reference

def numerator (x : ℝ) : ℝ := z0+(Q0-1-z0^2)*Real.sin x+z0*(Real.sin x)^2

theorem numerator_bounds {x : ℝ} (hx : DiagonalDomain x) :
    0<numerator x ∧ numerator x≤OnePolynomial.N (Real.sin x) := by
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hz0 : (499/1250:ℝ)<z0 ∧ z0<(2/5:ℝ) := by
    dsimp [z0,SecondWord.SameZero.PJ.Diagonal.z₀]
    constructor <;> linarith [ShortMixedZero.fine_diagonal_bounds.1,ShortMixedZero.fine_diagonal_bounds.2]
  have hcoef : 0<Q0-1-z0^2 ∧ Q0-1-z0^2<(27563/10000:ℝ) := by
    have hlo := mul_lt_mul'' hz0.1 hz0.1 (by norm_num) (by norm_num)
    have hhi := mul_lt_mul'' hz0.2 hz0.2 (by linarith [hz0.1]) (by linarith [hz0.1])
    norm_num [Q0]
    constructor <;> linarith
  have hterm := mul_nonneg hcoef.1.le ht.2.2.1
  have hterm2 := mul_nonneg (by linarith [hz0.1] : 0 ≤ z0) (sq_nonneg (Real.sin x))
  have hh := mul_le_mul_of_nonneg_right hcoef.2.le ht.2.2.1
  have hh2 := mul_le_mul_of_nonneg_right hz0.2.le (sq_nonneg (Real.sin x))
  dsimp [numerator,OnePolynomial.N]
  constructor <;> linarith

theorem omegaD_formula (x : ℝ) : omegaD x=numerator x/(T x)^3 := by
  dsimp [omegaD,SecondWord.SameZero.PJ.Diagonal.factorD,numerator]
  ring

theorem omega_comparison {x m α : ℝ} (hx : DiagonalDomain x)
    (hα : 0≤α) (hm : 1< m) (hmT : m≤T x)
    (hpoly : OnePolynomial.N (Real.sin x)<α*m*(m-1+(Real.sin x)^2/2)^2) :
    omegaD x≤α*(omega x)^2 := by
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hcos := cosine_upper_square (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hT : 0<T x := by linarith [hm,hmT]
  have hg0 : 0≤ m-1+(Real.sin x)^2/2 := by nlinarith [sq_nonneg (Real.sin x)]
  have hg1 : m-1+(Real.sin x)^2/2≤T x-Real.cos x := by linarith
  have hsquare : (m-1+(Real.sin x)^2/2)^2≤(T x-Real.cos x)^2 := by nlinarith
  have hp := mul_le_mul (mul_le_mul_of_nonneg_left hmT hα) hsquare
    (sq_nonneg (m-1+(Real.sin x)^2/2))
    (mul_nonneg hα hT.le)
  have hn := (numerator_bounds hx).2
  have hclear : numerator x≤α*T x*(T x-Real.cos x)^2 := by linarith
  rw [omegaD_formula]
  dsimp [omega,SecondWord.SameZero.PJ.Diagonal.factor]
  apply (div_le_iff₀ (pow_pos hT 3)).2
  field_simp [hT.ne']
  nlinarith

theorem nonnegative_factor {x : ℝ} (hx : DiagonalDomain x) (hz : 0≤z x) :
    omegaD x≤(73/100:ℝ)*(omega x)^2 := by
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hs : Real.sin x∈Icc (0:ℝ) (2/5) := by
    dsimp [z,SecondWord.SameZero.PJ.Diagonal.Z,SecondWord.SameZero.PJ.Diagonal.z₀] at hz
    exact ⟨ht.2.2.1,by linarith [ShortMixedZero.fine_diagonal_bounds.2]⟩
  have hm : 1<OnePolynomial.lowerT (Real.sin x) := by
    dsimp [OnePolynomial.lowerT]
    linarith [hs.1]
  have hT : OnePolynomial.lowerT (Real.sin x)≤T x := by
    have hp := OnePolynomial.lowerT_square hs
    have hz' : z x≤(2/5:ℝ)-Real.sin x := by
      dsimp [z,SecondWord.SameZero.PJ.Diagonal.Z,SecondWord.SameZero.PJ.Diagonal.z₀]
      linarith [ShortMixedZero.fine_diagonal_bounds.2]
    have hrad := (diagonal_radical hx).2.2
    have hTpos := (diagonal_radical hx).1
    nlinarith
  exact omega_comparison hx (by norm_num) hm hT
    (by linarith [OnePolynomial.nonnegative_polynomial hs])

theorem negative_factor {x : ℝ} (hx : DiagonalDomain x) (hz : z x<0) :
    omegaD x≤(9/10:ℝ)*(omega x)^2 := by
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hpoly := OnePolynomial.negative_polynomial
    (show Real.sin x∈Icc (0:ℝ) (129/200) from ⟨ht.2.2.1,by linarith [ht.2.2.2.1]⟩)
  apply omega_comparison hx (by norm_num : (0:ℝ)≤9/10)
    (by norm_num : (1:ℝ)<1963/1000) (negative_z_data hx hz).2.2.1.le
  linarith

theorem diagonal_ratio_increasing {e : ℝ} (he : IsEvent e) :
    StrictMonoOn (fun x => V x/U x) (Icc e (7/10)) := by
  have hint : interior (Icc e (7/10:ℝ)) = Ioo e (7/10) := interior_Icc
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc e (7/10))
    (f' := fun x => Q0*omega x/(U x)^2)
  · exact fun x hx =>
      (diagonal_ratio_hasDerivAt (after_diagonal_domain he hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [hint] at hx ⊢
    exact (diagonal_ratio_hasDerivAt
      (after_diagonal_domain he (Ioo_subset_Icc_self hx))).hasDerivWithinAt
  · intro x hx
    rw [hint] at hx
    have hd := after_diagonal_domain he (Ioo_subset_Icc_self hx)
    exact div_pos (mul_pos (by norm_num [Q0])
      (by linarith [(diagonal_omega_bounds hd).1]))
      (pow_pos (by linarith [(diagonal_coordinate_bounds hd).1]) 2)

theorem negative_ratio {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) (hz : z x<0) :
    (499/1250:ℝ)<V x/U x := by
  have hslo : Real.sin e<z0 := by
    dsimp [z0,SecondWord.SameZero.PJ.Diagonal.z₀]
    linarith [(event_trig he).2.1,ShortMixedZero.fine_diagonal_bounds.1]
  have hshi : z0<Real.sin x := by dsimp [z,SecondWord.SameZero.PJ.Diagonal.Z] at hz; linarith
  obtain ⟨y,hy,hyEq⟩ := intermediate_value_Icc hx.1 Real.continuous_sin.continuousOn
    (show z0∈Icc (Real.sin e) (Real.sin x) from ⟨hslo.le,hshi.le⟩)
  have hxy : y<x := by
    apply lt_of_le_of_ne hy.2
    intro h
    subst y
    linarith
  have hy' : y∈Icc e (7/10) := ⟨hy.1,hy.2.trans hx.2⟩
  have hd := after_diagonal_domain he hy'
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hd.1)
  have hT := (diagonal_radical hd).1
  have hz0 : 0<z0 := by linarith [hslo,(event_trig he).1]
  have hZ : SecondWord.SameZero.PJ.Diagonal.Z y=0 := by
    dsimp [SecondWord.SameZero.PJ.Diagonal.Z]; rw [hyEq]; ring
  have hratio : z0≤V y/U y := by
    apply (le_div_iff₀ (by linarith [(diagonal_coordinate_bounds hd).1] : 0<U y)).2
    have hp := mul_nonneg (mul_nonneg (by linarith : 0≤T y) hz0.le) (sub_nonneg.mpr ht.2.1)
    dsimp [U,V,SecondWord.SameZero.PJ.Diagonal.horizontal,SecondWord.SameZero.PJ.Diagonal.vertical]
    rw [hZ,hyEq]
    linarith
  have hm := diagonal_ratio_increasing he hy' hx hxy
  have hz0' : (499/1250:ℝ)<z0 := by
    dsimp [z0,SecondWord.SameZero.PJ.Diagonal.z₀]
    linarith [ShortMixedZero.fine_diagonal_bounds.1]
  exact hz0'.trans_le (hratio.trans hm.le)

theorem H_positive {x : ℝ} (hx : DiagonalDomain x) : 0<t 1*U x-P 1*V x := by
  have hc := diagonal_coordinate_bounds hx
  norm_num [P,t]
  nlinarith [hc.1,hc.2.2.2.1]

theorem curvature_from_factor {x α u r w : ℝ} (hx : DiagonalDomain x)
    (hα : omegaD x≤α*(omega x)^2)
    (hu : 0<u) (hU : u<U x) (hr : r≤V x/U x)
    (hw : 0<w) (hω : w<omega x)
    (hcoef : 0<(P 1-α*t 1)+(t 1+α*P 1)*r)
    (hcoef' : 0≤t 1+α*P 1) :
    w^2*u*((P 1-α*t 1)+(t 1+α*P 1)*r)<G2 1 x := by
  have hU0 : 0<U x := hu.trans hU
  have hratio : r*U x≤V x := (le_div_iff₀ hU0).1 hr
  have hrprod := mul_le_mul_of_nonneg_left hratio hcoef'
  have hbracket : u*((P 1-α*t 1)+(t 1+α*P 1)*r)<
      P 1*U x+t 1*V x-α*(t 1*U x-P 1*V x) := by
    have hp := mul_lt_mul_of_pos_right hU hcoef
    linarith
  have hw2 : w^2<(omega x)^2 := by
    have h := mul_self_lt_mul_self hw.le hω
    linarith
  have hpos : 0<u*((P 1-α*t 1)+(t 1+α*P 1)*r) := mul_pos hu hcoef
  have hprod := mul_lt_mul'' hw2 hbracket (sq_nonneg w) hpos.le
  have hdrop := mul_le_mul_of_nonneg_right hα (H_positive hx).le
  dsimp only [G2]
  linarith

theorem curvature {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    (1/50:ℝ)<G2 1 x := by
  have hd := after_diagonal_domain he hx
  by_cases hz : 0≤z x
  · have hh := curvature_from_factor hd (nonnegative_factor hd hz)
      (by norm_num : (0:ℝ)<9/5) (nonnegative_z_geometry hd hz).2.1
      (show (5223/20000:ℝ)≤V x/U x from rho_bounds.1.le.trans (diagonal_ratio hd).2)
      (by norm_num : (0:ℝ)<483/1000) (diagonal_omega_bounds hd).1
      (by norm_num [P,t]) (by norm_num [P,t])
    norm_num [P,t] at hh
    linarith
  · have hzn := lt_of_not_ge hz
    have hh := curvature_from_factor hd (negative_factor hd hzn)
      (by norm_num : (0:ℝ)<1399/1000)
      (show (1399/1000:ℝ)<U x by linarith [(diagonal_coordinate_bounds hd).1])
      (negative_ratio he hx hzn).le
      (by norm_num : (0:ℝ)<133/250) (negative_z_data hd hzn).2.2.2
      (by norm_num [P,t]) (by norm_num [P,t])
    norm_num [P,t] at hh
    linarith

theorem J_increasing {e : ℝ} (he : IsEvent e) : MonotoneOn (J 1) (Icc e (7/10)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun x hx => (J_hasDerivAt 1 (after_diagonal_domain he hx)).continuousAt.continuousWithinAt)
    (fun x hx => J_hasDerivAt 1 (after_diagonal_domain he (Ioo_subset_Icc_self hx)))
  intro x hx
  have hd := after_diagonal_domain he (Ioo_subset_Icc_self hx)
  have hc := diagonal_coordinate_bounds hd
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hd.1)
  have hw := diagonal_omega_bounds hd
  have hU : 0<U x := by linarith [hc.1]
  have hid : J1 1 x*(U x)^2=(p 1+q 1)*z x*U x+
      ((p 1+q 1)*Real.sin x+P 1)*Q0*omega x := by
    dsimp [J1]
    field_simp [hU.ne']
  have hpositive : 0<J1 1 x*(U x)^2 := by
    rw [hid]
    by_cases hz : 0≤z x
    · have h1 := mul_nonneg (mul_nonneg (by norm_num [p,q] : 0≤p 1+q 1) hz) hU.le
      have h2 : 0<((p 1+q 1)*Real.sin x+P 1)*Q0*omega x := by
        apply mul_pos
        · apply mul_pos
          · norm_num [p,q,P]
            nlinarith [ht.2.2.1]
          · norm_num [Q0]
        · linarith [hw.1]
      linarith
    · have hn := negative_z_data hd (lt_of_not_ge hz)
      have hzlo := (diagonal_z_bounds hd).1
      have hUhi : U x<(494697/250000:ℝ) :=
        (diagonal_U_le_T hd).trans_lt ((diagonal_radical hd).2.1.trans_lt radius_fine.2)
      have hnegative := mul_le_mul
        (show -z x≤(123/500:ℝ) by linarith) hUhi.le hU.le (by norm_num)
      have hpositive := mul_le_mul
        (show (p 1+q 1)*(499/1250)+P 1≤(p 1+q 1)*Real.sin x+P 1 by
          norm_num [p,q,P]; nlinarith [hn.1]) hn.2.2.2.le
          (by norm_num) (by norm_num [p,q,P]; nlinarith [hn.1])
      norm_num [p,q,P,Q0] at hpositive ⊢
      nlinarith
  exact ((mul_pos_iff_of_pos_right (pow_pos hU 2)).1 hpositive).le

theorem J_lower {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    -(71/1000:ℝ)<J 1 x := by
  have hm := J_increasing he ⟨le_rfl,(event_bounds he).2.2.2⟩ hx hx.1
  rw [J_at_event 1 he] at hm
  exact (H_one_at_event he).trans_le hm

theorem join_value {e : ℝ} (he : IsEvent e) : (225169/250000:ℝ)<G 1 e := by
  have heq := diagonal_at_event_coordinates he
  rw [G,heq.1,heq.2]
  have hp : (314159/200000:ℝ)<Real.pi/2 := by linarith [pi_hand_enclosure.1]
  have ha := ShortOuterZero.fine_axial_bounds.2
  have hd := ShortMixedZero.fine_diagonal_bounds.2
  norm_num [c,p,q,P,t]
  linarith [(event_bounds he).1]

private theorem r86_mpr_lo {a b : ℝ} (e : a=b) (h : Interval a=Interval b) (X : Interval b) :
    (h.mpr X).lo=X.lo := by
  subst e
  rfl
private theorem r86_mpr_hi {a b : ℝ} (e : a=b) (h : Interval a=Interval b) (X : Interval b) :
    (h.mpr X).hi=X.hi := by
  subst e
  rfl

def joinCosBox {e : ℝ} (he : IsEvent e) : Interval (Real.cos e) :=
  Interval.of_bounds ⟨(event_trig he).2.2.1.le,(event_trig he).2.2.2.le⟩
def joinSinBox {e : ℝ} (he : IsEvent e) : Interval (Real.sin e) :=
  Interval.of_bounds ⟨(event_trig he).1.le,(event_trig he).2.1.le⟩
def joinTBox {e : ℝ} (he : IsEvent e) : Interval (T e) := by
  convert (((axial.add (Interval.point (1/2))).mul (joinCosBox he)).add
    ((Interval.point (1/2)).mul (joinSinBox he))) using 1
  have hp := (diagonal_projection (diagonal_at_event he).1).1
  rw [(diagonal_at_event_coordinates he).1,(diagonal_at_event_coordinates he).2] at hp
  linarith

theorem join_slope {e : ℝ} (he : IsEvent e) : -(7/2500:ℝ)<G1 1 e := by
  have hTe : T e=(outerAxial+1/2)*Real.cos e+1/2*Real.sin e := by
    have hp := (diagonal_projection (diagonal_at_event he).1).1
    rw [(diagonal_at_event_coordinates he).1,(diagonal_at_event_coordinates he).2] at hp
    linarith
  have hlo : (joinTBox he).lo=(((axial.add (Interval.point (1/2))).mul (joinCosBox he)).add
      ((Interval.point (1/2)).mul (joinSinBox he))).lo := r86_mpr_lo hTe _ _
  have hhi : (joinTBox he).hi=(((axial.add (Interval.point (1/2))).mul (joinCosBox he)).add
      ((Interval.point (1/2)).mul (joinSinBox he))).hi := r86_mpr_hi hTe _ _
  have hden : 0<(joinTBox he).lo := by
    rw [hlo]
    dsimp [joinCosBox,joinSinBox]
    mixed_fixed
  let W := (Interval.point 1).sub ((joinCosBox he).div (joinTBox he) hden)
  let H := ((Interval.point (t 1)).mul (axial.add (Interval.point (1/2)))).sub
    (Interval.point (P 1/2))
  let E := (Interval.point 1).sub (H.mul W)
  have hv : E.lo≤G1 1 e := by
    have hh := E.mem.1
    dsimp [E,H,W,G1,omega,SecondWord.SameZero.PJ.Diagonal.factor] at *
    rw [(diagonal_at_event_coordinates he).1,(diagonal_at_event_coordinates he).2]
    linarith
  have hnum : -(7/2500:ℝ)<E.lo := by
    dsimp only [E,H,W]
    norm_num [Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.mul,
      Interval.div,Interval.inv,axial,hlo,hhi,joinCosBox,joinSinBox,t,P]
  exact hnum.trans_le hv

theorem reference_lower {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    (2251/2500:ℝ)<G 1 x := by
  have ht := curvature_tangent hx ⟨le_rfl,(event_bounds he).2.2.2⟩
    (fun u hu => G_hasDerivAt 1 (after_diagonal_domain he hu))
    (fun u hu => G1_hasDerivAt 1 (after_diagonal_domain he hu))
    (fun u hu => (curvature he hu).le)
  have hp := mul_le_mul_of_nonneg_right (join_slope he).le (sub_nonneg.mpr hx.1)
  have hs := sq_nonneg ((1/50)*(x-e)-7/2500)
  nlinarith [join_value he]

theorem after_contact {B e x : ℝ} (he : IsEvent e) (hd : Domain B x) (hx : e≤x) :
    (4489/5000:ℝ)<value 1 B x := by
  have hx' : x∈Icc e (7/10) := ⟨hx,hd.2.1.2⟩
  have hxd := after_diagonal_domain he hx'
  have hD := diagonal_contact_domain hxd
  have hJ := J_lower he hx'
  rw [J_first 1 hxd] at hJ
  have hh := contact_remainder 1 hD hd (diagonal_lower_target hd hxd)
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)≤71/1000) hJ.le
    (fun E hE => by simpa [curvatureFloor] using
      (Upper.curvature 1 (between_domain hD hd hE)).le)
  have hG := reference_lower he hx'
  rw [G_value 1 hxd] at hG
  norm_num at hh
  linarith

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper.OneDiagonal
end
end
end
