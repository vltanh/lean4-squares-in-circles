module

public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterReferences
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveLowerPrimaryReference
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryUpperAxial
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryUpperDiagonalData

/-!
# Eight squares: the remaining reflected edge-2 upper primary owner

The diagonal endpoint derivative is bounded in the three intrinsic
sign cases of its displayed factors. The same global state curvature
then covers its possible interior contact minimum.
-/

section
/-!
## The prescribed A-secondary circle supports

These are
the two original A tuples, with the stated multiplier on each complete
angle half. The moving norm and both derivatives remain explicit.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.EdgeFive.ASecondary
open CommonQuarter CorePairGeometry Arithmetic

def weight (r : Row) (upper : Bool) : ℝ :=
  if upper then 3/4 else if r=0 then q r else 439/500
def source (r : Row) (upper : Bool) : ℝ :=
  if upper then p r*outerAxial else if r=0 then 0 else
    -(p r+q r-weight r upper)/2-CommonQuarter.radius*Real.sqrt (p r^2+(q r-weight r upper)^2)
def normA (r : Row) (upper : Bool) : ℝ := P r^2+t r^2+weight r upper^2
def normB (r : Row) (upper : Bool) : ℝ := 2*weight r upper*P r
def normC (r : Row) (upper : Bool) : ℝ := 2*direction upper*weight r upper*t r
def N (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  CircularNorm.norm (normA r upper) (normB r upper) (normC r upper) x
def F (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  angle upper x+c r+source r upper+(weight r upper+P r+t r)/2+
    weight r upper*Real.cos x+(1+direction upper)/2*weight r upper*Real.sin x-CommonQuarter.radius*N r upper x
def first (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  direction upper-weight r upper*Real.sin x+(1+direction upper)/2*weight r upper*Real.cos x-
    CommonQuarter.radius*CircularNorm.d1 (normA r upper) (normB r upper) (normC r upper) x
def second (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  -weight r upper*Real.cos x-(1+direction upper)/2*weight r upper*Real.sin x-
    CommonQuarter.radius*CircularNorm.d2 (normA r upper) (normB r upper) (normC r upper) x

theorem weight_bounds (r : Row) (hr : ARows r) (upper : Bool) :
    (3/4:ℝ)≤weight r upper ∧ weight r upper≤439/500 := by
  rcases hr with rfl|rfl <;> cases upper <;> norm_num [weight,q]
theorem weight_positive (r : Row) (hr : ARows r) (upper : Bool) : 0<weight r upper := by
  linarith [(weight_bounds r hr upper).1]
theorem lower_weight (r : Row) (hr : ARows r) :
    (21721/25000:ℝ)≤weight r false ∧ (20762/25000:ℝ)≤t r := by
  rcases hr with rfl|rfl <;> norm_num [weight,q,t]
theorem energy_identity (r : Row) (upper : Bool) (x : ℝ) :
    CircularNorm.energy (normA r upper) (normB r upper) (normC r upper) x=
      (P r+weight r upper*Real.cos x)^2+(t r+direction upper*weight r upper*Real.sin x)^2 := by
  have hd : direction upper^2=1 := by
    cases upper <;> norm_num [direction,ShortWord.MixedQuarter.direction]
  dsimp only [CircularNorm.energy,normA,normB,normC]
  linear_combination -(weight r upper)^2*(Real.sin_sq_add_cos_sq x)-
    (weight r upper)^2*(Real.sin x)^2*hd
theorem energy_positive (r : Row) (hr : ARows r) (upper : Bool) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) :
    0<CircularNorm.energy (normA r upper) (normB r upper) (normC r upper) x := by
  have hP := (A_bounds r hr).1
  have hw := weight_positive r hr upper
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  have hh : 0<P r+weight r upper*Real.cos x := by nlinarith [mul_pos hw hc]
  rw [energy_identity]
  nlinarith [sq_nonneg (t r+direction upper*weight r upper*Real.sin x)]
theorem norm_positive (r : Row) (hr : ARows r) (upper : Bool) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : 0<N r upper x :=
  CircularNorm.norm_pos (energy_positive r hr upper hx)
theorem norm_sq (r : Row) (hr : ARows r) (upper : Bool) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) :
    (N r upper x)^2=normA r upper+normB r upper*Real.cos x+normC r upper*Real.sin x :=
  CircularNorm.norm_sq (energy_positive r hr upper hx).le
theorem norm_initial (r : Row) (upper : Bool) :
    (N r upper 0)^2=(P r+weight r upper)^2+t r^2 := by
  have he : CircularNorm.energy (normA r upper) (normB r upper) (normC r upper) 0=
      (P r+weight r upper)^2+t r^2 := by
    simp [CircularNorm.energy,normA,normB,normC]
    ring
  dsimp [N,CircularNorm.norm]
  rw [he,Real.sq_sqrt (by positivity)]
theorem norm_hasDerivAt (r : Row) (hr : ARows r) (upper : Bool) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (N r upper) (CircularNorm.d1 (normA r upper) (normB r upper) (normC r upper) x) x :=
  CircularNorm.norm_hasDerivAt (energy_positive r hr upper hx)
theorem norm_first (r : Row) (hr : ARows r) (upper : Bool) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) :
    CircularNorm.d1 (normA r upper) (normB r upper) (normC r upper) x=
      weight r upper*(-P r*Real.sin x+direction upper*t r*Real.cos x)/N r upper x := by
  have hn := (norm_positive r hr upper hx).ne'
  unfold CircularNorm.d1
  change CircularNorm.slope (normB r upper) (normC r upper) x/(2*N r upper x)=_
  simp only [CircularNorm.slope,normB,normC]
  rw [div_eq_div_iff (mul_ne_zero two_ne_zero hn) hn]
  ring
theorem F_hasDerivAt (r : Row) (hr : ARows r) (upper : Bool) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : HasDerivAt (F r upper) (first r upper x) x := by
  have h := (((((hasDerivAt_id x).const_mul (direction upper)).const_add
    (Real.pi/2+c r+source r upper+(weight r upper+P r+t r)/2)).add
      ((Real.hasDerivAt_cos x).const_mul (weight r upper))).add
        ((Real.hasDerivAt_sin x).const_mul ((1+direction upper)/2*weight r upper))).sub
          ((norm_hasDerivAt r hr upper hx).const_mul CommonQuarter.radius)
  convert h using 1
  · funext y
    simp only [F,angle,ShortWord.MixedQuarter.angle,Pi.add_apply,Pi.sub_apply,id_eq]
    ring
  · simp only [first]; ring
theorem first_hasDerivAt (r : Row) (hr : ARows r) (upper : Bool) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : HasDerivAt (first r upper) (second r upper x) x := by
  have h := ((((Real.hasDerivAt_sin x).const_mul (-weight r upper)).const_add (direction upper)).add
    ((Real.hasDerivAt_cos x).const_mul ((1+direction upper)/2*weight r upper))).sub
      ((CircularNorm.d1_hasDerivAt (energy_positive r hr upper hx)).const_mul CommonQuarter.radius)
  convert h using 1
  · funext y
    simp only [first,Pi.add_apply,Pi.sub_apply]
    ring
  · simp only [second]; ring

theorem source_lower (r : Row) (hr : ARows r) (upper : Bool) {a b : ℝ}
    (hs : OuterState a b) : source r upper≤p r*a+(q r-weight r upper)*b := by
  cases upper
  · rcases hr with rfl|rfl
    · norm_num [source,weight,p,q]
    · have h := outer_circle_lower (X:=p 1) (Y:=q 1-weight 1 false) hs
      have hsrc : source 1 false=-(p 1+(q 1-weight 1 false))/2-
          CommonQuarter.radius*Real.sqrt (p 1^2+(q 1-weight 1 false)^2) := by
        simp [source]; ring
      rw [hsrc]
      exact h
  · have hp := (coefficient_bounds r).1
    have hq : 0≤q r-weight r true := by
      dsimp [weight]
      linarith [(coefficient_bounds r).2.2.1]
    exact ShortWord.MixedQuarter.outer_axial_lower hs hp hq
theorem original_lower (r : Row) (hr : ARows r) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (_hx : x∈Icc 0 (7/10))
    (hm : Secondary r upper a b A B x) : F r upper x≤cost r upper a b A B x := by
  have he : Real.sqrt ((-P r-weight r upper*Real.cos x)^2+
      (-direction upper*weight r upper*Real.sin x-t r)^2)=N r upper x := by
    dsimp only [N,CircularNorm.norm]
    congr 1
    rw [energy_identity]
    ring
  have htarg := outer_circle_lower (X:=-P r-weight r upper*Real.cos x)
    (Y:=-direction upper*weight r upper*Real.sin x-t r) ht
  rw [he] at htarg
  have hh := secondary_support r upper (lam:=weight r upper) (weight_positive r hr upper).le hm
    (S:=source r upper)
    (T:= -((-P r-weight r upper*Real.cos x)+(-direction upper*weight r upper*Real.sin x-t r))/2-
      CommonQuarter.radius*N r upper x)
    (by rw [A_sign hr]; linarith [source_lower r hr upper hs])
    (by rw [A_sign hr]; linarith [htarg])
  simp only [F,width] at hh ⊢
  linarith

end SquaresInCircles.Eight.ShortOuterOne.EdgeFive.ASecondary
end
end
end

section
/-!
## The A-secondary endpoint comparisons

The lower-half cap retains the strict .8981 reserve. All radicals are
enclosed by positive rational square refinements at the stated endpoints;
these are proof expressions, with no certificate evaluation performed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.EdgeFive.ASecondary.Endpoint
open CommonQuarter Arithmetic StationaryPrimitives
open ShortWord.MixedQuarter.Reference

theorem upper_norm_initial (r : Row) (hr : ARows r) : (63/50:ℝ)<N r true 0 := by
  have hn := norm_positive r hr true (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
  have hs := norm_initial r true
  rcases hr with rfl|rfl <;> norm_num [P,t,weight] at hs <;> nlinarith
theorem lower_norm_initial (r : Row) (hr : ARows r) : N r false 0<343/250 := by
  have hn := norm_positive r hr false (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
  have hs := norm_initial r false
  rcases hr with rfl|rfl <;> norm_num [P,t,q,weight] at hs <;> nlinarith
theorem lower_coef (r : Row) (hr : ARows r) :
    (129/200:ℝ)*(N r false 0)^2<2*weight r false*t r := by
  rw [norm_initial]
  rcases hr with rfl|rfl <;> norm_num [P,t,q,weight]
theorem lower_curvature_reserve (r : Row) (hr : ARows r) :
    CommonQuarter.radius*N r false 0<4*weight r false := by
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hh := mul_lt_mul_of_pos_left (lower_norm_initial r hr) hR
  have hlam := (lower_weight r hr).1
  nlinarith [radius_fine.2]

def sourceBox (r : Row) (upper : Bool) : Interval (source r upper) := by
  cases upper
  · by_cases h : r=0
    · subst r
      exact Interval.point 0
    · let X := Interval.point (p r^2+(q r-weight r false)^2)
      let S := rootSix X 1 (by norm_num) (by dsimp [X,Interval.point]; positivity)
      convert (Interval.point (-(p r+q r-weight r false)/2)).sub (circleRadius.mul S) using 1
      simp [source,h]
  · exact (Interval.point (p r)).mul axial

-- The three endpoint values below evaluate `initialBox` and `capBox`; the radicals are bounded
-- by rational roots checked on their squares.
theorem upper_initial (r : Row) (hr : ARows r) : (4619/5000:ℝ)<F r true 0 := by
  have hn := (norm_positive r hr true (show (0:ℝ)∈Icc 0 (7/10) by norm_num)).le
  have hs := norm_initial r true
  have hR := radius_fine
  have ha := ShortOuterZero.fine_axial_bounds
  have hpi := pi_hand_enclosure
  have hF : F r true 0=Real.pi/2+c r+p r*outerAxial+(3/4+P r+t r)/2+3/4-CommonQuarter.radius*N r true 0 := by
    simp [F,ShortWord.MixedQuarter.angle,source,weight]
  rw [hF]
  rcases hr with rfl|rfl
  · norm_num [P,t,weight] at hs
    norm_num [c,p,P,t]
    have hN : N 0 true 0<1278391531/1000000000 :=
      lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hs]; norm_num)
    have hRN := mul_le_mul hR.2.le hN.le hn (by norm_num)
    linarith
  · norm_num [P,t,weight] at hs
    norm_num [c,p,P,t]
    have hN : N 1 true 0<1269119199/1000000000 :=
      lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hs]; norm_num)
    have hRN := mul_le_mul hR.2.le hN.le hn (by norm_num)
    linarith
theorem lower_initial (r : Row) (hr : ARows r) : (4587/5000:ℝ)<F r false 0 := by
  have hn := (norm_positive r hr false (show (0:ℝ)∈Icc 0 (7/10) by norm_num)).le
  have hs := norm_initial r false
  have hR := radius_fine
  have hpi := pi_hand_enclosure
  have hF : F r false 0=Real.pi/2+c r+source r false+(weight r false+P r+t r)/2+
      weight r false-CommonQuarter.radius*N r false 0 := by
    simp [F,ShortWord.MixedQuarter.angle]
  rw [hF]
  rcases hr with rfl|rfl
  · norm_num [P,t,q,weight] at hs
    norm_num [c,P,t,q,weight,source]
    have hN : N 0 false 0<1370599828/1000000000 :=
      lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hs]; norm_num)
    have hRN := mul_le_mul hR.2.le hN.le hn (by norm_num)
    linarith
  · norm_num [P,t,q,weight] at hs
    have hsrc : source 1 false=-(p 1+q 1-weight 1 false)/2-
        CommonQuarter.radius*Real.sqrt (p 1^2+(q 1-weight 1 false)^2) := by
      simp [source]
    have hq : Real.sqrt (p 1^2+(q 1-weight 1 false)^2)<198072921/1000000000 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num [p,q,weight]
    have hq0 := Real.sqrt_nonneg (p 1^2+(q 1-weight 1 false)^2)
    rw [hsrc]
    generalize Real.sqrt (p 1^2+(q 1-weight 1 false)^2)=S at hq hq0 ⊢
    have hRq := mul_le_mul hR.2.le hq.le hq0 (by norm_num)
    norm_num [c,p,P,t,q,weight]
    have hN : N 1 false 0<1368474721/1000000000 :=
      lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hs]; norm_num)
    have hRN := mul_le_mul hR.2.le hN.le hn (by norm_num)
    linarith
theorem lower_terminal (r : Row) (hr : ARows r) : (8981/10000:ℝ)<F r false (7/10) := by
  have hx : (7/10:ℝ)∈Icc 0 (7/10) := by norm_num
  have hn := (norm_positive r hr false hx).le
  have hs := norm_sq r hr false hx
  have hR := radius_fine
  have hpi := pi_hand_enclosure
  have tb := trig_taylor_bounds (show (0:ℝ)≤7/10 by norm_num)
  norm_num [sin7,sin9,cos8,cos10] at tb
  have hd : direction false=-1 := by simp [direction,ShortWord.MixedQuarter.direction]
  have hF : F r false (7/10)=Real.pi/2-7/10+c r+source r false+(weight r false+P r+t r)/2+
      weight r false*Real.cos (7/10)-CommonQuarter.radius*N r false (7/10) := by
    simp only [F,angle,ShortWord.MixedQuarter.angle,hd]; ring
  rw [hF]
  simp only [normA,normB,normC,hd] at hs
  rcases hr with rfl|rfl
  · norm_num [P,t,q,weight] at hs
    norm_num [c,P,t,q,weight,source]
    have hN : N 0 false (7/10)<9246267/10000000 :=
      lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hs]; linarith [tb.1,tb.2.2.2])
    have hRN := mul_le_mul hR.2.le hN.le hn (by norm_num)
    linarith [tb.2.2.1]
  · norm_num [P,t,q,weight] at hs
    have hsrc : source 1 false=-(p 1+q 1-weight 1 false)/2-
        CommonQuarter.radius*Real.sqrt (p 1^2+(q 1-weight 1 false)^2) := by
      simp [source]
    have hq : Real.sqrt (p 1^2+(q 1-weight 1 false)^2)<198072921/1000000000 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num [p,q,weight]
    have hq0 := Real.sqrt_nonneg (p 1^2+(q 1-weight 1 false)^2)
    rw [hsrc]
    generalize Real.sqrt (p 1^2+(q 1-weight 1 false)^2)=S at hq hq0 ⊢
    have hRq := mul_le_mul hR.2.le hq.le hq0 (by norm_num)
    norm_num [c,p,P,t,q,weight]
    have hN : N 1 false (7/10)<9201443/10000000 :=
      lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hs]; linarith [tb.1,tb.2.2.2])
    have hRN := mul_le_mul hR.2.le hN.le hn (by norm_num)
    linarith [tb.2.2.1]

end SquaresInCircles.Eight.ShortOuterOne.EdgeFive.ASecondary.Endpoint
end
end
end

section
/-!
## The four complete A-secondary angle halves

The upper numerator decreases
while its norm increases. On the lower half, the exact norm defect
retains the cosine factor; the circle-norm curvature identity then gives
concavity on the complete interval. No angle subdivision is introduced.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.EdgeFive.ASecondary
open CommonQuarter CorePairGeometry Arithmetic

def numerator (r : Row) (x : ℝ) : ℝ := t r*Real.cos x-P r*Real.sin x
def numeratorD (r : Row) (x : ℝ) : ℝ := -t r*Real.sin x-P r*Real.cos x
theorem numerator_hasDerivAt (r : Row) (x : ℝ) :
    HasDerivAt (numerator r) (numeratorD r x) x := by
  have h := ((Real.hasDerivAt_cos x).const_mul (t r)).sub
    ((Real.hasDerivAt_sin x).const_mul (P r))
  convert h using 1
  · funext y; simp only [numerator,Pi.sub_apply]
  · simp only [numeratorD]; ring
theorem numerator_positive (r : Row) (hr : ARows r) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : 0<numerator r x := by
  have hc := A_bounds r hr
  have tr := positive_trig hx
  have ht : 0<t r := by linarith [hc.2.2.1]
  have htc := mul_lt_mul_of_pos_left tr.1 ht
  have htt := mul_lt_mul_of_pos_right hc.2.2.1 (by norm_num : (0:ℝ)<191/250)
  have hPs := mul_le_mul hc.2.1.le tr.2.2.2.1.le tr.2.2.1 (by norm_num : (0:ℝ)≤219/1000)
  dsimp [numerator]
  nlinarith
theorem numerator_antitone (r : Row) (hr : ARows r) :
    AntitoneOn (numerator r) (Icc 0 (7/10)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun x _ => (numerator_hasDerivAt r x).continuousAt.continuousWithinAt)
    (fun x _ => numerator_hasDerivAt r x)
  intro x hx
  have tr := positive_trig (Ioo_subset_Icc_self hx)
  have hp := mul_nonneg (show 0≤P r by linarith [(A_bounds r hr).1])
    (show 0≤Real.cos x by linarith [tr.1])
  have ht := mul_nonneg (show 0≤t r by linarith [(A_bounds r hr).2.2.1]) tr.2.2.1
  dsimp [numeratorD]
  linarith
theorem upper_norm_monotone (r : Row) (hr : ARows r) :
    MonotoneOn (N r true) (Icc 0 (7/10)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun x hx => (norm_hasDerivAt r hr true hx).continuousAt.continuousWithinAt)
    (fun x hx => norm_hasDerivAt r hr true (Ioo_subset_Icc_self hx))
  intro x hx
  have hxc := Ioo_subset_Icc_self hx
  rw [norm_first r hr true hxc]
  have hp := numerator_positive r hr hxc
  have hn := norm_positive r hr true hxc
  have hd : direction true=1 := by simp [direction,ShortWord.MixedQuarter.direction]
  have hw : weight r true=3/4 := by simp [weight]
  rw [hd,hw]
  apply div_nonneg
  · dsimp [numerator] at hp
    linarith
  · exact hn.le
theorem upper_ratio (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    numerator r x/N r true x<663/1000 := by
  have h0 : (0:ℝ)∈Icc 0 (7/10) := by norm_num
  have hm := numerator_antitone r hr h0 hx hx.1
  have hN := (Endpoint.upper_norm_initial r hr).trans_le (upper_norm_monotone r hr h0 hx hx.1)
  have ht := (A_bounds r hr).2.2.2
  have hn0 : numerator r 0=t r := by simp [numerator]
  rw [hn0] at hm
  apply (div_lt_iff₀ (norm_positive r hr true hx)).mpr
  linarith
theorem upper_first (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (1/10:ℝ)<first r true x := by
  have hd : direction true=1 := by simp [direction,ShortWord.MixedQuarter.direction]
  have hw : weight r true=3/4 := by simp [weight]
  have he : CircularNorm.d1 (normA r true) (normB r true) (normC r true) x=
      (3/4)*(numerator r x/N r true x) := by
    rw [norm_first r hr true hx,hd,hw]
    dsimp only [numerator]
    ring
  have hd' := mul_lt_mul_of_pos_left (upper_ratio r hr hx) (by norm_num : (0:ℝ)<3/4)
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hh := mul_lt_mul_of_pos_left hd' hR
  have tr := positive_trig hx
  dsimp only [first]
  rw [he,hd,hw]
  linarith [ShortWord.MixedQuarter.Reference.radius_fine.2,tr.1,tr.2.2.2.1]
theorem upper_monotone (r : Row) (hr : ARows r) : MonotoneOn (F r true) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x hx => (F_hasDerivAt r hr true hx).continuousAt.continuousWithinAt)
    (fun x hx => F_hasDerivAt r hr true (Ioo_subset_Icc_self hx))
    (fun x hx => by linarith [upper_first r hr (Ioo_subset_Icc_self hx)])
theorem upper_lower (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (4619/5000:ℝ)<F r true x :=
  (Endpoint.upper_initial r hr).trans_le (upper_monotone r hr (by norm_num) hx hx.1)

theorem lower_norm_defect (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (N r false x)^2-(N r false 0)^2*(Real.cos x)^2=
      (N r false 0)^2*(Real.sin x)^2-2*weight r false*P r*(1-Real.cos x)-
        2*weight r false*t r*Real.sin x := by
  have hn := norm_sq r hr false hx
  have h0 := norm_initial r false
  have hd : direction false= -1 := by simp [direction,ShortWord.MixedQuarter.direction]
  simp only [normA,normB,normC,hd] at hn
  linear_combination hn-h0-(N r false 0)^2*(Real.sin_sq_add_cos_sq x)
theorem lower_norm_cos (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    N r false x≤N r false 0*Real.cos x := by
  have tr := positive_trig hx
  have hcoef := Endpoint.lower_coef r hr
  have hDs := mul_le_mul_of_nonneg_left tr.2.2.2.1.le (sq_nonneg (N r false 0))
  have hin : (N r false 0)^2*Real.sin x-2*weight r false*t r≤0 := by nlinarith
  have hlast := mul_nonpos_of_nonneg_of_nonpos tr.2.2.1 hin
  have hdef := lower_norm_defect r hr hx
  have hP : 0≤P r := by linarith [(A_bounds r hr).1]
  have hw := (weight_positive r hr false).le
  have hdrop := mul_nonneg (mul_nonneg hw hP) (show 0≤1-Real.cos x by linarith [Real.cos_le_one x])
  have hN := norm_positive r hr false hx
  have hN0 := norm_positive r hr false (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
  have hright := mul_pos hN0 (show 0<Real.cos x by linarith [tr.1])
  nlinarith
theorem lower_second (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    second r false x<0 := by
  have hd : direction false= -1 := by simp [direction,ShortWord.MixedQuarter.direction]
  have hcoef : (normB r false)^2+(normC r false)^2≤(normA r false)^2 := by
    rcases hr with rfl|rfl <;> norm_num [normA,normB,normC,weight,P,t,q,hd]
  have hc := CircularNorm.curvature_lower (energy_positive r hr false hx) hcoef
  have hR : 0≤CommonQuarter.radius := by linarith [radius_bounds.1]
  have hm := mul_le_mul_of_nonneg_left hc hR
  have hn := mul_le_mul_of_nonneg_left (lower_norm_cos r hr hx) hR
  have hreserve := Endpoint.lower_curvature_reserve r hr
  have hcos : 0<Real.cos x := by linarith [(positive_trig hx).1]
  have hnegative := mul_neg_of_pos_of_neg hcos
    (show -weight r false+CommonQuarter.radius*N r false 0/4<0 by linarith)
  dsimp only [second]
  rw [hd]
  change CommonQuarter.radius*(-N r false x/4)≤_ at hm
  linarith only [hm,hn,hnegative]
theorem lower_concave (r : Row) (hr : ARows r) : ConcaveOn ℝ (Icc 0 (7/10)) (F r false) :=
  concave_of_deriv2 (fun _ hx => F_hasDerivAt r hr false hx)
    (fun _ hx => first_hasDerivAt r hr false hx) (fun _ hx => (lower_second r hr hx).le)
theorem lower_lower (r : Row) (hr : ARows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (8981/10000:ℝ)<F r false x := by
  apply concave_gt_of_endpoints (lower_concave r hr) hx
  · linarith [Endpoint.lower_initial r hr]
  · exact Endpoint.lower_terminal r hr

theorem original (r : Row) (hr : ARows r) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Secondary r upper a b A B x) : (8981/10000:ℝ)<cost r upper a b A B x := by
  have hh := original_lower r hr upper hs ht hx hm
  cases upper
  · exact (lower_lower r hr hx).trans_le hh
  · linarith [upper_lower r hr hx]

end SquaresInCircles.Eight.ShortOuterOne.EdgeFive.ASecondary
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper
open CommonQuarter CorePairGeometry Arithmetic

def zeroDiagonalLower (s : ℝ) : ℝ :=
  (p 0+q 0)-t 0+P 0*(499/1250)/(969/500)+
  ((p 0+q 0)*(499/1250)/(969/500)+P 0*(1-1/(969/500)))*s+
  (p 0+q 0)*(1-1/(969/500)-1/(441/250))*s^2

theorem zeroDiagonalLower_bound {s : ℝ} (hs : s∈Icc (499/1250:ℝ) (129/200)) :
    -(187/1000:ℝ)<zeroDiagonalLower s := by
  have hc : ConcaveOn ℝ (Icc (499/1250:ℝ) (129/200)) zeroDiagonalLower := by
    apply concave_of_deriv2
      (f':=fun u => ((p 0+q 0)*(499/1250)/(969/500)+P 0*(1-1/(969/500)))+
        2*(p 0+q 0)*(1-1/(969/500)-1/(441/250))*u)
      (f'':=fun _ => 2*(p 0+q 0)*(1-1/(969/500)-1/(441/250)))
    · intro u _
      have h := (((hasDerivAt_id' u).const_mul
        ((p 0+q 0)*(499/1250)/(969/500)+P 0*(1-1/(969/500)))).const_add
          ((p 0+q 0)-t 0+P 0*(499/1250)/(969/500))).fun_add
            ((hasDerivAt_pow 2 u).const_mul ((p 0+q 0)*(1-1/(969/500)-1/(441/250))))
      convert h using 1
      · funext w
        simp only [zeroDiagonalLower]
      · norm_num
        ring
    · intro u _
      have h := ((hasDerivAt_id' u).const_mul
        (2*(p 0+q 0)*(1-1/(969/500)-1/(441/250)))).const_add
          ((p 0+q 0)*(499/1250)/(969/500)+P 0*(1-1/(969/500)))
      exact h.congr_deriv (by ring)
    · intro u _
      norm_num [p,q]
  exact concave_gt_of_endpoints hc hs
    (by norm_num [zeroDiagonalLower,p,q,P,t]) (by norm_num [zeroDiagonalLower,p,q,P,t])

theorem negative_z_ratio_lower {x : ℝ} (hx : DiagonalDomain x) (hz : z x<0) :
    Real.sin x+(499/1250-Real.sin x)/(969/500)≤V x/U x := by
  have hn := negative_z_data hx hz
  have hr := diagonal_radical hx
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1)
  have hU := (diagonal_coordinate_bounds hx).1
  have hzl : (499/1250:ℝ)-Real.sin x≤z x := by
    dsimp [z,SecondWord.SameZero.PJ.Diagonal.Z,SecondWord.SameZero.PJ.Diagonal.z₀]
    linarith [ShortMixedZero.fine_diagonal_bounds.1]
  have hkz := mul_le_mul_of_nonpos_right ht.2.1 hz.le
  have hcut := mul_le_mul_of_nonpos_left hr.1.le
    (show (499/1250-Real.sin x)/(969/500:ℝ)≤0 by linarith [hn.1])
  have hlower0 : 0≤Real.sin x+(499/1250-Real.sin x)/(969/500:ℝ) := by linarith [hn.1]
  have hUT := mul_le_mul_of_nonneg_left (diagonal_U_le_T hx) hlower0
  apply (le_div_iff₀ (by linarith : 0<U x)).2
  dsimp [V,SecondWord.SameZero.PJ.Diagonal.vertical]
  nlinarith

theorem J_zero_lower {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    -(27/125:ℝ)<J 0 x := by
  have hd := after_diagonal_domain he hx
  have ht := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hd.1)
  have hc := diagonal_coordinate_bounds hd
  have hcos := cosine_lower_square (SecondWord.SameZero.PJ.Diagonal.angle_mem hd.1)
  have hs0 : (10679/100000:ℝ)<Real.sin x := by
    exact (event_trig he).1.trans_le
      (sin_mono (event_bounds he).2.2 (SecondWord.SameZero.PJ.Diagonal.angle_mem hd.1) hx.1)
  by_cases hfactor : (p 0+q 0)*Real.sin x+P 0<0
  · have hs : Real.sin x<(67/500:ℝ) := by norm_num [p,q,P] at hfactor; linarith
    have hcos' : (9909/10000:ℝ)<Real.cos x := by
      nlinarith [Real.sin_sq_add_cos_sq x,ht.1,ht.2.2.1]
    have hp := mul_le_mul_of_nonpos_left hc.2.2.2.2.2.le hfactor.le
    norm_num [J,p,q,P,t] at hp ⊢
    nlinarith
  · have hf := le_of_not_gt hfactor
    by_cases hz : 0≤z x
    · have hr := (nonnegative_z_geometry hd hz).2.2
      have hp := mul_le_mul_of_nonneg_left hr hf
      have hs := sq_nonneg (2*(433/1000)*(68355/100000)*Real.sin x-9133/100000)
      have hsquare := sq_nonneg (Real.sin x)
      norm_num [p,q,P] at hp hf
      norm_num [J,p,q,P,t]
      nlinarith
    · have hzn := lt_of_not_ge hz
      have hn := negative_z_data hd hzn
      have hratio := negative_z_ratio_lower hd hzn
      have hp := mul_le_mul_of_nonneg_left hratio hf
      have hvalue := zeroDiagonalLower_bound
        (show Real.sin x∈Icc (499/1250:ℝ) (129/200) from
          ⟨hn.1.le,by linarith [ht.2.2.2.1]⟩)
      norm_num [p,q,P] at hp hf
      dsimp [zeroDiagonalLower] at hvalue
      norm_num [J,p,q,P,t] at hvalue ⊢
      nlinarith

theorem G_zero_lower {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    (1159/1250:ℝ)<G 0 x := by
  have hmono := G_simple_increasing 0 (Or.inl rfl) he
    ⟨le_rfl,(event_bounds he).2.2.2⟩ hx hx.1
  rw [G_at_event 0 he] at hmono
  have hF := F_zero_increasing he
    (show (134/1250:ℝ)∈Icc 0 e from ⟨by norm_num,(event_bounds he).1.le⟩)
    ⟨by linarith [(event_bounds he).1],le_rfl⟩ (event_bounds he).1.le
  exact Reference.zero_value_at_event_lower.trans_le (hF.trans hmono)

theorem after_zero {B e x : ℝ} (he : IsEvent e) (hd : Domain B x) (hx : e≤x) :
    (449/500:ℝ)<value 0 B x := by
  have hx' : x∈Icc e (7/10) := ⟨hx,hd.2.1.2⟩
  have hxD := after_diagonal_domain he hx'
  have hD := diagonal_contact_domain hxD
  have hJ := J_zero_lower he hx'
  rw [J_first 0 hxD] at hJ
  have hh := contact_remainder 0 hD hd (diagonal_lower_target hd hxD)
    (by norm_num : (0:ℝ)<43/50) (by norm_num : (0:ℝ)≤27/125) hJ.le
    (fun E hE => by
      have h := (curvature 0 (between_domain hD hd hE)).le
      have h0 : curvatureFloor 0=43/50 := by norm_num [curvatureFloor]
      rw [h0] at h
      exact h)
  have hG := G_zero_lower he hx'
  rw [G_value 0 hxD] at hG
  norm_num at hh
  linarith

theorem zero_contact {B x : ℝ} (hd : Domain B x) : (449/500:ℝ)<value 0 B x := by
  obtain ⟨e,he⟩ := exists_event
  rcases le_total x e with hx | hx
  · exact before_zero he hd hx
  · exact after_zero he hd hx

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper
end
end
end
