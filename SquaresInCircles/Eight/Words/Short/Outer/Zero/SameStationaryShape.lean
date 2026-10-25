module

public import SquaresInCircles.Eight.Owners.SplitConcavityTools
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroPositiveSpeeds
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameEvent

/-!
# Eight squares: the two concave stationary heights

The derivative of G is
positive on the full source arc. Its two written sign comparisons give
the source cutoffs; endpoint chords and the one written tangent then
bound the complete possible height ranges.
-/

section
/-!
## The exact coupled stationary coordinate of a favorable zero contact

At an angular stationary point, the original circle identity determines
the target height from the unchanged source coordinate. The second
angular derivative and the target derivative are then literal functions
of that same coordinate, not independent relaxed variables.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Same.Stationary
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open SecondWord (U W outer_domain outer_zero_mem UW_circle U_positive)

def z (b : ℝ) : ℝ := b-1/2
def mass (r : Row) (b : ℝ) : ℝ := (z b)^2+1/(l r b)^2
def height (r : Row) (b : ℝ) : ℝ := (Q0+1-mass r b)/2
def G (r : Row) (b : ℝ) : ℝ := z b-alpha r b/(l r b)^3
def GD (r : Row) (b : ℝ) : ℝ :=
  1-3*(-p r)*Q0*(q r*W b+p r*U b)/((U b)^5*(l r b)^4)
def targetRatio (u : ℝ) : ℝ := Real.sqrt (Q0-u^2)/u
def f (u : ℝ) : ℝ := (Q0-u)/(u*(Q0+1-2*u))
def stationaryTarget (r : Row) (b : ℝ) : ℝ :=
  f (height r b)+targetRatio (height r b)*(P r+z b*l r b/mass r b)-t r

def sourceDomain : Set ℝ := Icc (293/1000) outerDiagonal

lemma source_outer {b : ℝ} (hb : b∈sourceDomain) : b∈Icc 0 outerDiagonal :=
  ⟨by linarith [hb.1],hb.2⟩

lemma mass_positive (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : 0< mass r b := by
  have hl := l_positive r hb
  dsimp [mass]
  positivity

lemma mass_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (mass r) (2*G r b) b := by
  have hl := l_positive r hb
  have hd := (((hasDerivAt_id b).sub_const (1/2)).pow 2).add
    ((hasDerivAt_const b (1:ℝ)).div ((l_hasDerivAt r hb).pow 2)
      (pow_ne_zero 2 hl.ne'))
  convert hd using 1
  · rfl
  · dsimp [G,z]
    field_simp [hl.ne']
    ring

lemma height_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (height r) (-G r b) b := by
  exact (((mass_hasDerivAt r hb).const_sub (Q0+1)).div_const 2).congr_deriv (by ring)

lemma G_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (G r) (GD r b) b := by
  have hl := l_positive r hb
  have hu := U_positive (outer_domain hb)
  have hc := UW_circle (outer_domain hb)
  have hd := ((hasDerivAt_id b).sub_const (1/2)).sub
    ((alpha_hasDerivAt r hb).div ((l_hasDerivAt r hb).pow 3) (pow_ne_zero 3 hl.ne'))
  refine hd.congr_deriv ?_
  have hD : ratioD b=Q0/(U b)^3 := rfl
  have hDD : ratioDD b=3*Q0*(W b)/(U b)^5 := rfl
  have hR : ratio b=W b/U b := rfl
  have hL : l r b*U b=q r*U b-p r*W b := by
    simp only [l,hR]
    field_simp
  simp only [Pi.pow_apply,GD,alpha,hD,hDD,show (3:ℕ)-1=2 from rfl,Nat.cast_ofNat]
  rw [←hc]
  field_simp
  linear_combination (3*p r*(U b^2+W b^2)*W b)*hL

lemma angular_speed {B x : ℝ} (r : Row) (hd : Domain B x)
    (hstat : angleFirst r B x=0) : speed B x=1/l r (contact B x) := by
  have hl := l_positive r hd.2.2
  dsimp [angleFirst] at hstat
  apply (eq_div_iff hl.ne').2
  nlinarith

lemma actual_height {B x : ℝ} (r : Row) (hd : Domain B x)
    (hstat : angleFirst r B x=0) : height r (contact B x)=U B := by
  have hsp : SecondWord.SameZero.v B x=1/l r (SecondWord.SameZero.b B x) :=
    angular_speed r hd hstat
  have hn := SecondWord.SameZero.norm_identity hd.1 x
  rw [hsp,div_pow,one_pow] at hn
  simp only [height,mass,z,SecondWord.NegativeTwo.Inverse.q] at hn ⊢
  linarith

lemma actual_ratio {B x : ℝ} (r : Row) (hd : Domain B x)
    (hstat : angleFirst r B x=0) : targetRatio (height r (contact B x))=ratio B := by
  rw [actual_height r hd hstat]
  have hc := UW_circle (outer_domain hd.1)
  have hw : 0≤W B := by dsimp [W]; linarith [hd.1.1]
  have he : Q0-(U B)^2=(W B)^2 := by linarith
  rw [targetRatio,he,Real.sqrt_sq hw]
  rfl

lemma actual_second {B x : ℝ} (r : Row) (hd : Domain B x)
    (hstat : angleFirst r B x=0) :
    angleSecond r B x= -l r (contact B x)*G r (contact B x) := by
  have hl := l_positive r hd.2.2
  rw [angleSecond,angular_speed r hd hstat]
  dsimp [G,z]
  field_simp [hl.ne']
  ring

lemma actual_target {B x : ℝ} (r : Row) (hd : Domain B x)
    (hstat : angleFirst r B x=0) : targetFirst r B x=stationaryTarget r (contact B x) := by
  have hl := l_positive r hd.2.2
  have hu := U_positive (outer_domain hd.1)
  have hq : 0<SecondWord.NegativeTwo.Inverse.q (U B) := by
    linarith [SecondWord.NegativeTwo.Inverse.actual_q_positive hd.1]
  have hsp : SecondWord.SameZero.v B x=1/l r (SecondWord.SameZero.b B x) :=
    angular_speed r hd hstat
  have hmass : mass r (contact B x)=SecondWord.NegativeTwo.Inverse.q (U B) := by
    have hn := SecondWord.SameZero.norm_identity hd.1 x
    rw [hsp,div_pow,one_pow] at hn
    simp only [mass,z]
    linarith
  have hproj := SecondWord.SameZero.projection_identity hd.1 hd.2.1
  rw [hsp] at hproj
  have e1 : SecondWord.SameZero.k B x/(1/l r (SecondWord.SameZero.b B x))=
      SecondWord.SameZero.k B x*l r (SecondWord.SameZero.b B x) := by
    field_simp
  have e2 : W B*(SecondWord.SameZero.b B x-1/2)/
      (U B*SecondWord.NegativeTwo.Inverse.q (U B)*(1/l r (SecondWord.SameZero.b B x)))=
      W B*(SecondWord.SameZero.b B x-1/2)*l r (SecondWord.SameZero.b B x)/
        (U B*SecondWord.NegativeTwo.Inverse.q (U B)) := by
    field_simp
  rw [e1,e2] at hproj
  rw [stationaryTarget,actual_ratio r hd hstat,actual_height r hd hstat,hmass]
  have hf : f (U B)=SecondWord.NegativeTwo.Inverse.factor (U B) := rfl
  rw [hf]
  simp only [targetFirst,z]
  rw [show ratio B=W B/U B from rfl]
  linear_combination hproj

lemma f_hasDerivAt {u : ℝ} (hu : u≠0) (hq : Q0+1-2*u≠0) :
    HasDerivAt f
      ((4*Q0*u-2*u^2-Q0*(Q0+1))/(u^2*(Q0+1-2*u)^2)) u := by
  have hd := ((hasDerivAt_id' u).const_sub Q0).div
    ((hasDerivAt_id' u).mul (((hasDerivAt_id' u).const_mul 2).const_sub (Q0+1)))
    (mul_ne_zero hu hq)
  refine hd.congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero hu hq))
    (mul_ne_zero (pow_ne_zero 2 hu) (pow_ne_zero 2 hq))]
  ring

lemma f_monotone : MonotoneOn f (Icc (1747/1000:ℝ) (951/500)) := by
  have hpos {u : ℝ} (hu : u∈Icc (1747/1000:ℝ) (951/500)) :
      0<u ∧ 0<Q0+1-2*u := by
    norm_num [Q0]
    constructor <;> linarith [hu.1,hu.2]
  apply monoOn_of_hasDeriv_nonneg
    (fun u hu => (f_hasDerivAt (hpos hu).1.ne' (hpos hu).2.ne').continuousAt.continuousWithinAt)
    (fun u hu => f_hasDerivAt (hpos (Ioo_subset_Icc_self hu)).1.ne'
      (hpos (Ioo_subset_Icc_self hu)).2.ne')
  intro u hu
  have hp := mul_nonneg (show 0≤u-1747/1000 by linarith [hu.1])
    (show 0≤4*Q0-2*(u+1747/1000) by norm_num [Q0]; linarith [hu.2])
  have hn : 0≤4*Q0*u-2*u^2-Q0*(Q0+1) := by
    norm_num [Q0] at hp ⊢
    nlinarith
  exact div_nonneg hn (mul_nonneg (sq_nonneg _) (sq_nonneg _))

lemma row_zero_target_negative {b : ℝ} (hb : b∈sourceDomain) (hG : G 0 b≤0) :
    stationaryTarget 0 b<0 := by
  have hbhalf : b≤1/2 := by norm_num [G,z,alpha,p] at hG; exact hG
  have hH : height 0 b∈Icc (1747/1000:ℝ) (38021/20000) := by
    norm_num [height,mass,z,l,p,q,Q0]
    constructor <;> nlinarith [hb.1,hbhalf]
  have hu0 : 0<height 0 b := by linarith [hH.1]
  have hr : 0≤targetRatio (height 0 b) := div_nonneg (Real.sqrt_nonneg _) hu0.le
  have hl := l_positive (0:Row) (source_outer hb)
  have hz : z b≤0 := by dsimp [z]; linarith
  have hbracket : P 0+z b*l 0 b/mass 0 b≤0 := by
    norm_num [P]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hz hl.le)
      (mass_positive (0:Row) (source_outer hb)).le
  have hprod := mul_nonpos_of_nonneg_of_nonpos hr hbracket
  have hmono := f_monotone ⟨hH.1,by linarith [hH.2]⟩ (by norm_num) hH.2
  have href : f (38021/20000)-t 0< -(47/1000:ℝ) := by norm_num [f,t,Q0]
  dsimp [stationaryTarget]
  linarith

end SquaresInCircles.Eight.ShortOuterZero.Same.Stationary
end
end
end

section
/-!
## The written concave target-ratio tangent

The target ratio is concave on
one complete height interval. Its tangent at 1.84 is bounded by the
written affine function; the endpoint radical is checked by squaring.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Same.Stationary
open CommonQuarter CorePairGeometry Arithmetic

abbrev ratioDomain : Set ℝ := Icc (4369/2500) (92117/50000)
def targetRoot (u : ℝ) : ℝ := Real.sqrt (Q0-u^2)
def targetRatioD (u : ℝ) : ℝ := -Q0/(u^2*targetRoot u)
def targetRatioDD (u : ℝ) : ℝ :=
  Q0*(2*Q0-3*u^2)/(u^3*(targetRoot u)^3)

lemma targetRoot_data {u : ℝ} (hu : u∈Icc (1747/1000:ℝ) (951/500)) :
    0<u ∧ 0<targetRoot u ∧ (targetRoot u)^2=Q0-u^2 := by
  have hp : 0<Q0-u^2 := by norm_num [Q0]; nlinarith [hu.1,hu.2]
  exact ⟨by linarith [hu.1],Real.sqrt_pos.mpr hp,Real.sq_sqrt hp.le⟩

lemma targetRoot_hasDerivAt {u : ℝ} (hu : u∈Icc (1747/1000:ℝ) (951/500)) :
    HasDerivAt targetRoot (-u/targetRoot u) u := by
  have h := targetRoot_data hu
  have hn : Q0-u^2≠0 := by nlinarith [h.2.1,h.2.2]
  have hp := ((hasDerivAt_pow 2 u).const_sub Q0).sqrt hn
  refine hp.congr_deriv ?_
  change _=-u/Real.sqrt (Q0-u^2)
  have hr : Real.sqrt (Q0-u^2)≠0 := h.2.1.ne'
  field_simp
  push_cast
  ring

lemma targetRatio_hasDerivAt {u : ℝ} (hu : u∈Icc (1747/1000:ℝ) (951/500)) :
    HasDerivAt targetRatio (targetRatioD u) u := by
  have h := targetRoot_data hu
  convert (targetRoot_hasDerivAt hu).div (hasDerivAt_id u) h.1.ne' using 1
  · rfl
  · dsimp [targetRatioD]
    field_simp [h.1.ne',h.2.1.ne']
    nlinarith [h.2.2]

lemma targetRatioD_hasDerivAt {u : ℝ} (hu : u∈Icc (1747/1000:ℝ) (951/500)) :
    HasDerivAt targetRatioD (targetRatioDD u) u := by
  have h := targetRoot_data hu
  have hd := (hasDerivAt_const u (-Q0)).div
    (((hasDerivAt_id u).pow 2).mul (targetRoot_hasDerivAt hu))
    (mul_ne_zero (pow_ne_zero 2 h.1.ne') h.2.1.ne')
  convert hd using 1
  · rfl
  · dsimp [targetRatioDD]
    field_simp [h.1.ne',h.2.1.ne']
    nlinarith [h.2.2]

lemma ratio_domain_inclusion {u : ℝ} (hu : u∈ratioDomain) :
    u∈Icc (1747/1000:ℝ) (951/500) := ⟨by linarith [hu.1],by linarith [hu.2]⟩

lemma targetRatio_concave : ConcaveOn ℝ ratioDomain targetRatio :=
  concave_of_deriv2
    (fun u hu => targetRatio_hasDerivAt (ratio_domain_inclusion hu))
    (fun u hu => targetRatioD_hasDerivAt (ratio_domain_inclusion hu))
    (fun u hu => by
      have h := targetRoot_data (ratio_domain_inclusion hu)
      have hn : 2*Q0-3*u^2≤0 := by norm_num [Q0]; nlinarith [hu.1]
      dsimp only [targetRatioDD]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num [Q0]) hn)
        (mul_pos (pow_pos h.1 3) (pow_pos h.2.1 3)).le)

lemma tangent_reference : targetRatio (46/25)<(19783/50000:ℝ) ∧
    |targetRatioD (46/25)+158863/100000|<(1/100000:ℝ) := by
  have h := targetRoot_data (show (46/25:ℝ)∈Icc (1747/1000) (951/500) by norm_num)
  have h2 : (targetRoot (46/25))^2=53/100 := by rw [h.2.2]; norm_num [Q0]
  have hroot : (72801/100000:ℝ)<targetRoot (46/25) ∧
      targetRoot (46/25)<728011/1000000 := by
    constructor <;> nlinarith [h.2.1]
  have hpos : 0<(46/25:ℝ)^2*targetRoot (46/25) := mul_pos (by norm_num) h.2.1
  constructor
  · change targetRoot (46/25)/(46/25)<19783/50000
    rw [div_lt_iff₀ (by norm_num)]
    linarith [hroot.2]
  · rw [abs_lt]
    dsimp only [targetRatioD]
    rw [neg_div]
    constructor
    · have hh : Q0/((46/25)^2*targetRoot (46/25))<158864/100000 := by
        rw [div_lt_iff₀ hpos]
        norm_num [Q0]
        linarith [hroot.1]
      linarith
    · have hh : 158862/100000<Q0/((46/25)^2*targetRoot (46/25)) := by
        rw [lt_div_iff₀ hpos]
        norm_num [Q0]
        linarith [hroot.2]
      linarith

lemma targetRatio_tangent {u : ℝ} (hu : u∈ratioDomain) :
    targetRatio u<(82969/25000:ℝ)-(158863/100000)*u := by
  have ht := SplitConcavityTools.tangent_upper targetRatio_concave
    (show (46/25:ℝ)∈ratioDomain by norm_num [ratioDomain]) hu
    (targetRatio_hasDerivAt (by norm_num))
  have hd := tangent_reference.2
  have hdist : |u-46/25|≤(1/10:ℝ) := by
    rw [abs_le]
    constructor <;> linarith [hu.1,hu.2]
  have hp : |(targetRatioD (46/25)+158863/100000)*(u-46/25)|≤(1/100000)*(1/10:ℝ) := by
    rw [abs_mul]
    exact mul_le_mul hd.le hdist (abs_nonneg _) (by norm_num)
  have he := (abs_le.mp hp).2
  nlinarith [tangent_reference.1]

lemma targetRatio_nonneg {u : ℝ} (hu : 0<u) : 0≤targetRatio u :=
  div_nonneg (Real.sqrt_nonneg _) hu.le

lemma targetRatio_upper {u lo k : ℝ}
    (hu : u∈Icc (1747/1000:ℝ) (951/500)) (hlo : 0≤lo) (hul : lo≤u)
    (hk : 0<k) (hbound : Q0<lo^2*(1+k^2)) : targetRatio u<k := by
  have h := targetRoot_data hu
  have hs := pow_le_pow_left₀ hlo hul 2
  have hm := mul_le_mul_of_nonneg_right hs (by positivity : 0≤1+k^2)
  have hsq : (targetRoot u)^2<(k*u)^2 := by nlinarith [h.2.2]
  have hp := mul_pos hk h.1
  have hroot : targetRoot u<k*u := by nlinarith
  exact (div_lt_iff₀ h.1).2 hroot

end SquaresInCircles.Eight.ShortOuterZero.Same.Stationary
end
end
end

section
/-!
## Stationary references for the coupled rows

Every box carries its exact expression. The only source coordinates evaluated are `.293`, `.6`,
`.77` and `.78` (`initial_slopes`, `row_one_end`, `row_three_end`, `row_three_tangent`); the
variable source intervals are not partitioned.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Same.Stationary.References
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra
open SecondWord.OppositeZero.Reference (rootAt rootAt_lo_positive)

abbrev referenceDomain : Set ℝ := Icc 0 (9/10)

def slopeBox (r : Row) (b : ℝ) (hb : b∈referenceDomain) : Interval (l r b) :=
  (Interval.point (q r)).sub ((Interval.point (p r)).mul
    (ratioBox (Interval.point b) (rootAt b hb) (rootAt_lo_positive hb)))
def alphaBox (r : Row) (b : ℝ) (hb : b∈referenceDomain) : Interval (alpha r b) :=
  (Interval.point (-p r)).mul (ratioDBox (rootAt b hb) (rootAt_lo_positive hb))
def massBox (r : Row) (b : ℝ) (hb : b∈referenceDomain)
    (hl : 0<(slopeBox r b hb).lo) : Interval (mass r b) :=
  (Interval.point (b-1/2)).square.add
    ((Interval.point 1).div (slopeBox r b hb).square (Interval.square_lo_pos hl))
def heightBox (r : Row) (b : ℝ) (hb : b∈referenceDomain)
    (hl : 0<(slopeBox r b hb).lo) : Interval (height r b) :=
  ((Interval.point (Q0+1)).sub (massBox r b hb hl)).div (Interval.point 2)
    (by norm_num [Interval.point])
def GBox (r : Row) (b : ℝ) (hb : b∈referenceDomain)
    (hl : 0<(slopeBox r b hb).lo) : Interval (G r b) :=
  (Interval.point (b-1/2)).sub ((alphaBox r b hb).div
    (slopeBox r b hb).cube (Interval.cube_lo_pos hl))

macro "stationary_reference_arithmetic" : tactic => `(tactic|
  norm_num [slopeBox,alphaBox,massBox,heightBox,GBox,
    SecondWord.OppositeZero.Reference.rootAt,rootThree,rootStep,ratioBox,ratioDBox,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,Interval.mul,
    Interval.square,Interval.cube,Interval.div,Interval.inv,p,q,Q0])

private lemma r90_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r90_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl
private lemma r90_mp_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).lo = S.lo := by subst e; rfl
private lemma r90_mp_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).hi = S.hi := by subst e; rfl

private lemma r90_rootAt_lo {b : ℝ} (hb : b∈Icc 0 (9/10)) : (rootAt b hb).lo =
    (rootThree (Interval.point (Q0-(b+1/2)^2)) (2-b/2) (by linarith [hb.2])
      (by norm_num [Interval.point,Q0]; nlinarith [hb.1,hb.2])).lo := by
  unfold SecondWord.OppositeZero.Reference.rootAt
  rw [r90_mpr_lo, r90_mp_lo]
  all_goals simp [SecondWord.U,ShortOuterOne.SameContact.arc]
private lemma r90_rootAt_hi {b : ℝ} (hb : b∈Icc 0 (9/10)) : (rootAt b hb).hi =
    (rootThree (Interval.point (Q0-(b+1/2)^2)) (2-b/2) (by linarith [hb.2])
      (by norm_num [Interval.point,Q0]; nlinarith [hb.1,hb.2])).hi := by
  unfold SecondWord.OppositeZero.Reference.rootAt
  rw [r90_mpr_hi, r90_mp_hi]
  all_goals simp [SecondWord.U,ShortOuterOne.SameContact.arc]

local macro "r90_arith" : tactic => `(tactic|
  norm_num [slopeBox,alphaBox,massBox,heightBox,GBox,r90_rootAt_lo,r90_rootAt_hi,
    rootThree,rootStep,ratioBox,ratioDBox,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,Interval.mul,
    Interval.square,Interval.cube,Interval.div,Interval.inv,p,q,Q0])

lemma initial_slopes : (23/25:ℝ)<l 1 (293/1000) ∧ (17/20:ℝ)<l 3 (293/1000) := by
  have h1 := (slopeBox 1 (293/1000) (by norm_num)).mem.1
  have h3 := (slopeBox 3 (293/1000) (by norm_num)).mem.1
  have r1 : (23/25:ℝ)<(slopeBox 1 (293/1000) (by norm_num)).lo := by r90_arith
  have r3 : (17/20:ℝ)<(slopeBox 3 (293/1000) (by norm_num)).lo := by r90_arith
  exact ⟨r1.trans_le h1,r3.trans_le h3⟩

lemma row_one_end : (19/5000:ℝ)<G 1 (3/5) ∧ |G 1 (3/5)|<(1/250:ℝ) ∧
    (923/500:ℝ)<height 1 (3/5) ∧ height 1 (3/5)<4723/2500 ∧
      l 1 (3/5)<943/1000 := by
  have hl : 0<(slopeBox 1 (3/5) (by norm_num)).lo := by r90_arith
  let D := GBox 1 (3/5) (by norm_num) hl
  let H := heightBox 1 (3/5) (by norm_num) hl
  have rD : (19/5000:ℝ)<D.lo ∧ D.hi<(1/250:ℝ) := by
    dsimp only [D]
    constructor <;> r90_arith
  have rH : (923/500:ℝ)<H.lo ∧ H.hi<(4723/2500:ℝ) := by
    dsimp only [H]
    constructor <;> r90_arith
  have rL : (slopeBox 1 (3/5) (by norm_num)).hi<(943/1000:ℝ) := by r90_arith
  exact ⟨rD.1.trans_le D.mem.1,abs_lt.mpr ⟨by linarith [D.mem.1],D.mem.2.trans_lt rD.2⟩,
    rH.1.trans_le H.mem.1,H.mem.2.trans_lt rH.2,
    (slopeBox 1 (3/5) (by norm_num)).mem.2.trans_lt rL⟩

lemma row_one_initial : (923/500:ℝ)<height 1 (293/1000) := by
  have hl : 0<(slopeBox 1 (293/1000) (by norm_num)).lo := by r90_arith
  let H := heightBox 1 (293/1000) (by norm_num) hl
  have h : (923/500:ℝ)<H.lo := by dsimp only [H]; r90_arith
  exact h.trans_le H.mem.1

lemma row_three_end : (73/10000:ℝ)<G 3 (39/50) ∧
    (46057/25000:ℝ)<height 3 (39/50) ∧ l 3 (39/50)<233/250 := by
  have hl : 0<(slopeBox 3 (39/50) (by norm_num)).lo := by r90_arith
  let D := GBox 3 (39/50) (by norm_num) hl
  let H := heightBox 3 (39/50) (by norm_num) hl
  have hD : (73/10000:ℝ)<D.lo := by dsimp only [D]; r90_arith
  have hH : (46057/25000:ℝ)<H.lo := by dsimp only [H]; r90_arith
  have hL : (slopeBox 3 (39/50) (by norm_num)).hi<(233/250:ℝ) := by r90_arith
  exact ⟨hD.trans_le D.mem.1,hH.trans_le H.mem.1,
    (slopeBox 3 (39/50) (by norm_num)).mem.2.trans_lt hL⟩

lemma row_three_initial : (4369/2500:ℝ)<height 3 (293/1000) := by
  have hl : 0<(slopeBox 3 (293/1000) (by norm_num)).lo := by r90_arith
  let H := heightBox 3 (293/1000) (by norm_num) hl
  have h : (4369/2500:ℝ)<H.lo := by dsimp only [H]; r90_arith
  exact h.trans_le H.mem.1

lemma row_three_tangent : height 3 (77/100)<1842327/1000000 ∧
    |G 3 (77/100)|<(1/125000:ℝ) := by
  have hl : 0<(slopeBox 3 (77/100) (by norm_num)).lo := by r90_arith
  let D := GBox 3 (77/100) (by norm_num) hl
  let H := heightBox 3 (77/100) (by norm_num) hl
  have hH : H.hi<(1842327/1000000:ℝ) := by dsimp only [H]; r90_arith
  have hDl : -(1/125000:ℝ)<D.lo := by dsimp only [D]; r90_arith
  have hDu : D.hi<(1/125000:ℝ) := by dsimp only [D]; r90_arith
  exact ⟨H.mem.2.trans_lt hH,abs_lt.mpr ⟨hDl.trans_le D.mem.1,D.mem.2.trans_lt hDu⟩⟩

end SquaresInCircles.Eight.ShortOuterZero.Same.Stationary.References
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Same.Stationary
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open SecondWord (U W outer_domain outer_zero_mem UW_circle U_positive)

def Curved (r : Row) : Prop := r=1 ∨ r=3
def slopeFloor (r : Row) : ℝ := if r=1 then 23/25 else 17/20

lemma curved_coupled {r : Row} (hr : Curved r) : Coupled r := by
  unfold Coupled
  rcases hr with rfl | rfl <;> decide

lemma slope_lower (r : Row) (hr : Curved r) {b : ℝ} (hb : b∈sourceDomain) :
    slopeFloor r<l r b := by
  have hstart : (293/1000:ℝ)∈Icc 0 outerDiagonal :=
    SecondWord.Asymmetric.rational_outer_mem (by norm_num)
  have hm := l_monotone r (curved_coupled hr) hstart (source_outer hb) hb.1
  rcases hr with rfl | rfl <;> norm_num [slopeFloor] <;>
    linarith [References.initial_slopes.1,References.initial_slopes.2]

lemma G_derivative_positive (r : Row) (hr : Curved r) {b : ℝ}
    (hb : b∈sourceDomain) : 0<GD r b := by
  have hbi := source_outer hb
  have hu := U_positive (outer_domain hbi)
  have hU : (1399/1000:ℝ)<U b := (SecondWord.UW_bounds hbi).1
  have hw : 0≤W b ∧ W b<(7/5:ℝ) := by
    dsimp [W]
    constructor <;> linarith [hbi.1,hbi.2,outer_endpoint_bounds.2.2.2]
  have hl := l_positive r hbi
  have hfloor := slope_lower r hr hb
  have hf0 : 0<slopeFloor r := by
    rcases hr with rfl | rfl <;> norm_num [slopeFloor]
  have hu5 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hU.le 5
  have hl4 := pow_le_pow_left₀ hf0.le hfloor.le 4
  have hden := mul_le_mul hu5 hl4 (pow_nonneg hf0.le 4) (pow_nonneg hu.le 5)
  have hden0 : 0<(U b)^5*(l r b)^4 := mul_pos (pow_pos hu 5) (pow_pos hl 4)
  have hp : p r≤0 := (coupled_signs r (curved_coupled hr)).1
  have hpu := mul_nonpos_of_nonpos_of_nonneg hp hu.le
  have hq := (coefficient_signs r).1
  have hqw := mul_le_mul_of_nonneg_left hw.2.le hq.le
  have hn : q r*W b+p r*U b≤q r*(7/5) := by linarith
  have hcoef : 0≤3*(-p r)*Q0 :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by norm_num [Q0])
  have hnum := mul_le_mul_of_nonneg_left hn hcoef
  have hreserve : 3*(-p r)*Q0*q r*(7/5)<
      (1399/1000:ℝ)^5*(slopeFloor r)^4 := by
    rcases hr with rfl | rfl <;> norm_num [p,q,Q0,slopeFloor]
  have hquot : 3*(-p r)*Q0*(q r*W b+p r*U b)/((U b)^5*(l r b)^4)<1 := by
    apply (div_lt_one hden0).2
    nlinarith
  dsimp only [GD]
  linarith

lemma G_monotone (r : Row) (hr : Curved r) : MonotoneOn (G r) sourceDomain :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hb => (G_hasDerivAt r (source_outer hb)).continuousAt.continuousWithinAt)
    (fun _ hb => G_hasDerivAt r (source_outer (Ioo_subset_Icc_self hb)))
    (fun _ hb => (G_derivative_positive r hr (Ioo_subset_Icc_self hb)).le)

lemma height_concave (r : Row) (hr : Curved r) : ConcaveOn ℝ sourceDomain (height r) :=
  concave_of_deriv2
    (fun _ hb => height_hasDerivAt r (source_outer hb))
    (fun _ hb => (G_hasDerivAt r (source_outer hb)).neg)
    (fun _ hb => neg_nonpos.mpr (G_derivative_positive r hr hb).le)

lemma row_one_source {b : ℝ} (hb : b∈sourceDomain) (hG : G 1 b≤0) : b<(3/5:ℝ) := by
  by_contra! hn
  have hpoint : (3/5:ℝ)∈sourceDomain :=
    ⟨by norm_num,(SecondWord.Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hm := G_monotone 1 (Or.inl rfl) hpoint hb hn
  linarith [References.row_one_end.1]

lemma row_three_source {b : ℝ} (hb : b∈sourceDomain) (hG : G 3 b≤0) : b<(39/50:ℝ) := by
  by_contra! hn
  have hpoint : (39/50:ℝ)∈sourceDomain :=
    ⟨by norm_num,(SecondWord.Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hm := G_monotone 3 (Or.inr rfl) hpoint hb hn
  linarith [References.row_three_end.1]

lemma row_one_height {b : ℝ} (hb : b∈Icc (293/1000:ℝ) (3/5)) :
    (923/500:ℝ)<height 1 b ∧ height 1 b<1891/1000 ∧ l 1 b<943/1000 := by
  have hlast : (3/5:ℝ)∈sourceDomain :=
    ⟨by norm_num,(SecondWord.Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hfirst : (293/1000:ℝ)∈sourceDomain := ⟨le_rfl,by linarith [hlast.2]⟩
  have hbd : b∈sourceDomain := ⟨hb.1,hb.2.trans hlast.2⟩
  have hc := height_concave 1 (Or.inl rfl)
  have hmin := hc.min_le_of_mem_Icc hfirst hlast hb
  have hlo : (923/500:ℝ)<height 1 b :=
    (lt_min References.row_one_initial References.row_one_end.2.2.1).trans_le hmin
  have htan := SplitConcavityTools.tangent_upper hc hlast hbd
    (height_hasDerivAt 1 (source_outer hlast))
  have hG := abs_lt.mp References.row_one_end.2.1
  have hpay := mul_le_mul_of_nonneg_left
    (show G 1 (3/5)≤(1/250:ℝ) by linarith [hG.2])
    (show 0≤(3/5:ℝ)-b by linarith [hb.2])
  have hl := l_monotone 1 (curved_coupled (Or.inl rfl)) (source_outer hbd)
    (source_outer hlast) hb.2
  exact ⟨hlo,by linarith [hb.1,References.row_one_end.2.2.2.1],
    hl.trans_lt References.row_one_end.2.2.2.2⟩

def chordHeight (b : ℝ) : ℝ :=
  4369/2500+(2367/25000)/(487/1000)*(b-293/1000)

lemma row_three_chord {b : ℝ} (hb : b∈Icc (293/1000:ℝ) (39/50)) :
    chordHeight b<height 3 b := by
  have hlast : (39/50:ℝ)∈sourceDomain :=
    ⟨by norm_num,(SecondWord.Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hfirst : (293/1000:ℝ)∈sourceDomain := ⟨le_rfl,by linarith [hlast.2]⟩
  have hh := SplitConcavityTools.chord (height_concave 3 (Or.inr rfl))
    hfirst hlast (by norm_num) hb
  have hleft := mul_le_mul_of_nonneg_left References.row_three_initial.le
    (sub_nonneg.mpr hb.2)
  have hright := mul_le_mul_of_nonneg_left References.row_three_end.2.1.le
    (sub_nonneg.mpr hb.1)
  by_cases hfirsteq : b=293/1000
  · subst b
    simpa [chordHeight] using References.row_three_initial
  · have hstrict := mul_lt_mul_of_pos_left References.row_three_end.2.1
      (show 0<b-293/1000 by exact sub_pos.mpr (lt_of_le_of_ne hb.1 (Ne.symm hfirsteq)))
    dsimp [chordHeight]
    nlinarith

lemma row_three_height {b : ℝ} (hb : b∈Icc (293/1000:ℝ) (39/50)) :
    (4369/2500:ℝ)<height 3 b ∧ height 3 b<92117/50000 ∧ l 3 b<233/250 := by
  have hlast : (39/50:ℝ)∈sourceDomain :=
    ⟨by norm_num,(SecondWord.Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hbd : b∈sourceDomain := ⟨hb.1,hb.2.trans hlast.2⟩
  have href : (77/100:ℝ)∈sourceDomain := ⟨by norm_num,by linarith [hlast.2]⟩
  have htan := SplitConcavityTools.tangent_upper (height_concave 3 (Or.inr rfl))
    href hbd (height_hasDerivAt 3 (source_outer href))
  have habs : |b-77/100|≤(477/1000:ℝ) := by
    rw [abs_le]
    constructor <;> linarith [hb.1,hb.2]
  have hpay : |G 3 (77/100)*(b-77/100)|≤(1/125000)*(477/1000:ℝ) := by
    rw [abs_mul]
    exact mul_le_mul References.row_three_tangent.2.le habs (abs_nonneg _)
      (by norm_num)
  have hchord := row_three_chord hb
  have hl := l_monotone 3 (curved_coupled (Or.inr rfl)) (source_outer hbd)
    (source_outer hlast) hb.2
  refine ⟨?_,?_,hl.trans_lt References.row_three_end.2.2⟩
  · dsimp only [chordHeight] at hchord
    linarith [hb.1]
  · have hp := (abs_le.mp hpay).1
    linarith [References.row_three_tangent.1]

end SquaresInCircles.Eight.ShortOuterZero.Same.Stationary
end
end
end
