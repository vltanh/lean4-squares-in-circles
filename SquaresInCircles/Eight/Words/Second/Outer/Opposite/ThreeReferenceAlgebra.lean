module

public import SquaresInCircles.Eight.Owners.Stationary.TerminalWeights
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeData
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoAxialCalculus

/-!
# Eight squares: exact radical enclosures at named opposite edge-three references

A positive rational seed gives a rational upper square-root bound by
the arithmetic-geometric mean identity; division gives the matching
lower bound.  Three explicit refinements are used at individual fixed
references.  Each enclosure remains attached to its actual expression.
There is no domain subdivision or evaluated certificate.
-/

section
/-!
## The literal opposite-sign edge-three pair

The source is the original negative role-three state and the target is
the original positive role-four state.  Every displayed contact bound
is obtained from its unchanged weak forward axis.  No active-contact
assumption is added to these original-coordinate statements.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def value (b B φ : ℝ) : ℝ := φ-T b-L B
abbrev bOne : ℝ := OppositeTwo.bOne
def lowerSecondary (y x : ℝ) : ℝ :=
  (arc y-1/2)*Real.cos x-(y+1/2)*Real.sin x-1/2
def upperSecondary (y x : ℝ) : ℝ :=
  (arc y-1/2)*Real.cos x+(y-1/2)*Real.sin x-1/2
def lowerPrimary (y x : ℝ) : ℝ :=
  1/2+(arc y+1/2)*Real.sin x+(y+1/2)*Real.cos x
def upperPrimary (y x : ℝ) : ℝ :=
  1/2+(y+1/2)*Real.cos x-(arc y-1/2)*Real.sin x

lemma cost_identity {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B) :
    SecondWord.cost 3 .outer .outer false true a b A B φ=value b B φ := by
  unfold value
  rw [show T b=TLabel.eval a b from TLabel.outer_actual hs,
    show L B=LLabel.eval A B from LLabel.outer_actual ht]
  norm_num [SecondWord.cost,label,QuarterWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,TLabel,LLabel,RoleLabel.eval]
  ring

lemma lower_source_secondary {a b A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) 1 (Real.pi/2-x)) :
    b≤lowerSecondary B x := by
  have hw := NegativeTwo.lower_width hx
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
  dsimp [lowerSecondary]
  rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  linarith

lemma upper_source_secondary {a b A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) 1 (Real.pi/2+x)) :
    b≤upperSecondary B x := by
  have hw := NegativeTwo.upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  dsimp [upperSecondary]
  rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  linarith

lemma lower_target_primary {a b A B x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) 1 (Real.pi/2-x)) :
    lowerPrimary b x≤A := by
  have hw := NegativeTwo.lower_width hx
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
  dsimp [lowerPrimary]
  rw [(ShortOuterOne.SameContact.actual_arc hs).1]
  linarith

lemma upper_target_primary {a b A B x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) 1 (Real.pi/2+x)) :
    upperPrimary b x≤A := by
  have hw := NegativeTwo.upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  dsimp [upperPrimary]
  rw [(ShortOuterOne.SameContact.actual_arc hs).1]
  linarith

lemma lower_target_secondary {a b A B x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) 1 (Real.pi/2-x)) :
    B≤lowerSecondary b x := by
  have hw := NegativeTwo.lower_width hx
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
  dsimp [lowerSecondary]
  rw [(ShortOuterOne.SameContact.actual_arc hs).1]
  linarith

lemma upper_target_secondary {a b A B x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) 1 (Real.pi/2+x)) :
    B≤upperSecondary b x := by
  have hw := NegativeTwo.upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  dsimp [upperSecondary]
  rw [(ShortOuterOne.SameContact.actual_arc hs).1]
  linarith

lemma lower_source_primary {a b A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) 1 (Real.pi/2-x)) :
    lowerPrimary B x≤a := by
  have hw := NegativeTwo.lower_width hx
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
  dsimp [lowerPrimary]
  rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  linarith

lemma upper_source_primary {a b A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) :
    upperPrimary B x≤a := by
  have hw := NegativeTwo.upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  dsimp [upperPrimary]
  rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  linarith

lemma lowerPrimary_zero (y : ℝ) : lowerPrimary y 0=1+y := by
  simp [lowerPrimary]
  ring
lemma upperPrimary_zero (y : ℝ) : upperPrimary y 0=1+y := by
  simp [upperPrimary]
  ring

end SquaresInCircles.Eight.SecondWord.OppositeThree
end
end
end

section
/-!
## The two aligned opposite edge-three contacts

The two orders share one physical circle chart and one differentiation argument. Their inner
coordinate is `j y = arc y - 1`, derived from the aligned separator. The cost `cost` and its three
derivatives `first`, `second` and `third` are defined on the whole closed domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.Aligned
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def inner (reverse : Bool) : RoleLabel := if reverse then LLabel else TLabel
def outer (reverse : Bool) : RoleLabel := if reverse then TLabel else LLabel
def j (y : ℝ) : ℝ := arc y-1
def cost (reverse : Bool) (y : ℝ) : ℝ :=
  Real.pi/2-(inner reverse).outer (j y)-(outer reverse).outer y
def first (reverse : Bool) (y : ℝ) : ℝ :=
  (inner reverse).d1 (j y)*ratio y-(outer reverse).d1 y
def second (reverse : Bool) (y : ℝ) : ℝ :=
  -(inner reverse).d2 (j y)*(ratio y)^2+
    (inner reverse).d1 (j y)*ratioD y-(outer reverse).d2 y
def third (reverse : Bool) (y : ℝ) : ℝ :=
  (inner reverse).d3 (j y)*(ratio y)^3-
    3*(inner reverse).d2 (j y)*ratio y*ratioD y+
      (inner reverse).d1 (j y)*ratioDD y-(outer reverse).d3 y

lemma mem_outer {y : ℝ} (hy : y∈Icc 0 bOne) : y∈Icc 0 outerDiagonal :=
  ⟨hy.1,hy.2.trans OppositeTwo.bOne_mem.2⟩

lemma j_bounds {y : ℝ} (hy : y∈Icc 0 bOne) : 0≤j y ∧ j y<2073/5000 := by
  have hlo := ShortOuterOne.SameContact.arc_antitone (outer_domain (mem_outer hy))
    (outer_domain OppositeTwo.bOne_mem) hy.2
  rw [OppositeTwo.bOne_arc] at hlo
  have hhi := (CommonQuarter.outer_bounds
    (ShortOuterOne.SameContact.arc_state (mem_outer hy))).2.1
  dsimp [j]
  exact ⟨by linarith,by linarith [ShortOuterZero.fine_axial_bounds.2]⟩

lemma j_mem {y : ℝ} (hy : y∈Icc 0 bOne) : j y∈Icc 0 outerDiagonal :=
  ⟨(j_bounds hy).1,by linarith [(j_bounds hy).2,fine_outer_endpoint_bounds.2]⟩

lemma coordinates {y : ℝ} (hy : y∈Icc 0 bOne) :
    (3/2:ℝ)≤U y ∧ W y<1291/1000 ∧ ratio y<861/1000 := by
  have hj := j_bounds hy
  have hw : W y<1291/1000 := by
    dsimp [W]
    linarith [hy.2,OppositeTwo.bOne_bounds.2]
  have hu : (3/2:ℝ)≤U y := by dsimp [U,j] at *; linarith [hj.1]
  refine ⟨hu,hw,?_⟩
  change W y/U y<861/1000
  apply (div_lt_iff₀ (U_positive (outer_domain (mem_outer hy)))).2
  linarith

lemma j_hasDerivAt {y : ℝ} (hy : y∈Icc 0 bOne) :
    HasDerivAt j (-ratio y) y :=
  (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain (mem_outer hy))).sub_const 1

lemma cost_hasDerivAt (reverse : Bool) {y : ℝ} (hy : y∈Icc 0 bOne) :
    HasDerivAt (cost reverse) (first reverse y) y := by
  have hi := ((inner reverse).outer_hasDerivAt (outer_domain (j_mem hy))).comp y
    (j_hasDerivAt hy)
  have ho := (outer reverse).outer_hasDerivAt (outer_domain (mem_outer hy))
  exact ((hi.const_sub (Real.pi/2)).fun_sub ho).congr_deriv (by dsimp [first]; ring)

lemma first_hasDerivAt (reverse : Bool) {y : ℝ} (hy : y∈Icc 0 bOne) :
    HasDerivAt (first reverse) (second reverse y) y := by
  have hi := ((inner reverse).d1_hasDerivAt (outer_domain (j_mem hy))).comp y
    (j_hasDerivAt hy)
  have hr := ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain (mem_outer hy))
  have ho := (outer reverse).d1_hasDerivAt (outer_domain (mem_outer hy))
  exact ((hi.fun_mul hr).fun_sub ho).congr_deriv
    (by simp only [Function.comp_apply,second]; ring)

lemma second_hasDerivAt (reverse : Bool) {y : ℝ} (hy : y∈Icc 0 bOne) :
    HasDerivAt (second reverse) (third reverse y) y := by
  have hi := ((inner reverse).d1_hasDerivAt (outer_domain (j_mem hy))).comp y
    (j_hasDerivAt hy)
  have hi2 := ((inner reverse).d2_hasDerivAt (outer_domain (j_mem hy))).comp y
    (j_hasDerivAt hy)
  have hr := ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain (mem_outer hy))
  have hr2 := ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain (mem_outer hy))
  have ho := (outer reverse).d2_hasDerivAt (outer_domain (mem_outer hy))
  exact (((hi2.neg.fun_mul (hr.fun_pow 2)).fun_add (hi.fun_mul hr2)).fun_sub ho).congr_deriv
    (by simp only [Function.comp_apply,third]; norm_num; ring)

lemma forward_value (y : ℝ) : cost false y=OppositeThree.value (j y) y (Real.pi/2) := rfl
lemma reverse_value (y : ℝ) : cost true y=OppositeThree.value y (j y) (Real.pi/2) := by
  dsimp [cost,inner,outer,OppositeThree.value,T,L]
  ring

end SquaresInCircles.Eight.SecondWord.OppositeThree.Aligned
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.ReferenceAlgebra
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open StationaryPrimitives (Interval)

def rootStep {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    Interval (Real.sqrt x) := by
  let u : ℝ := (s+X.hi/s)/2
  have hx : 0≤x := hX.trans X.mem.1
  have hhi : 0≤X.hi := hx.trans X.mem.2
  have hu : 0<u := by dsimp [u]; positivity
  have he : 4*u^2-4*X.hi=(s-X.hi/s)^2 := by
    dsimp [u]
    field_simp [hs.ne']
    ring
  have hu2 : X.hi≤u^2 := by nlinarith [sq_nonneg (s-X.hi/s)]
  have hr := Real.sqrt_nonneg x
  have hr2 := Real.sq_sqrt hx
  have hrhi : Real.sqrt x≤u := by nlinarith [X.mem.2]
  refine ⟨X.lo/u,u,?_,hrhi⟩
  apply (div_le_iff₀ hu).2
  have hp := mul_le_mul_of_nonneg_left hrhi hr
  nlinarith [X.mem.1]

lemma rootStep_hi_pos {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    0<(rootStep X s hs hX).hi := by
  have hh : 0≤X.hi := hX.trans (X.mem.1.trans X.mem.2)
  dsimp [rootStep]
  positivity

def rootThree {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    Interval (Real.sqrt x) := by
  let X₀ := rootStep X s hs hX
  have h₀ : 0<X₀.hi := rootStep_hi_pos X s hs hX
  let X₁ := rootStep X X₀.hi h₀ hX
  have h₁ : 0<X₁.hi := rootStep_hi_pos X X₀.hi h₀ hX
  exact rootStep X X₁.hi h₁ hX

def radicand {y : ℝ} (Y : Interval y) : Interval (Q0-(y+1/2)^2) :=
  (Interval.point Q0).sub ((Y.add (Interval.point (1/2))).square)

def shifted {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) : Interval (U y) := by
  have hh := rootThree (radicand Y) s hs hr
  convert hh using 1
  dsimp [U,arc]
  ring

def coordinate {y : ℝ} (Y : Interval (U y)) : Interval (arc y) := by
  have hh := Y.sub (Interval.point (1/2))
  convert hh using 1
  dsimp [U]
  ring

def ratioBox {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    Interval (ratio y) :=
  (Y.add (Interval.point (1/2))).div X hX

def ratioDBox {y : ℝ} (X : Interval (U y)) (hX : 0<X.lo) :
    Interval (ratioD y) :=
  (Interval.point Q0).div X.cube (Interval.cube_lo_pos hX)

def ratioDDBox {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    Interval (ratioDD y) := by
  let Z := ((Interval.point (3*Q0)).mul (Y.add (Interval.point (1/2)))).div
    (X.cube.mul X.square)
    (Interval.mul_lo_pos (Interval.cube_lo_pos hX) (Interval.square_lo_pos hX))
  convert Z using 1
  dsimp [ratioDD,U]
  congr 1
  ring

def labelBox (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    Interval (H.outer y) := by
  let Z := ((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add ((Interval.point H.s).mul ((coordinate X).mul Y))
  convert Z using 1
  dsimp [RoleLabel.outer,RoleLabel.eval]
  ring

def firstBox (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y))
    (hX : 0<X.lo) : Interval (H.d1 y) :=
  ((((Interval.point H.q).add ((Interval.point (2*H.r)).mul Y)).add ((Interval.point H.s).mul (coordinate X))).sub
      (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioBox Y X hX)))

def secondBox (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y))
    (hX : 0<X.lo) : Interval (H.d2 y) :=
  (((Interval.point (2*H.r)).sub ((Interval.point (2*H.s)).mul (ratioBox Y X hX))).sub (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioDBox X hX)))

def thirdBox (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y))
    (hX : 0<X.lo) : Interval (H.d3 y) :=
  (((Interval.point (-3*H.s)).mul (ratioDBox X hX)).sub
    (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioDDBox Y X hX)))

def piBox : Interval Real.pi :=
  Interval.of_bounds ⟨pi_hand_enclosure.1.le,pi_hand_enclosure.2.le⟩

def jBox {y : ℝ} (X : Interval (U y)) : Interval (Aligned.j y) := by
  have hh := X.sub (Interval.point (3/2))
  convert hh using 1
  dsimp [Aligned.j,U]
  ring

def alignedBox (reverse : Bool) {y : ℝ}
    (Y : Interval y) (X : Interval (U y)) (J : Interval (U (Aligned.j y))) :
    Interval (Aligned.cost reverse y) :=
  (((piBox.div (Interval.point 2) (by norm_num [Interval.point])).sub (labelBox (Aligned.inner reverse) (jBox X) J)).sub (labelBox (Aligned.outer reverse) Y X))

def alignedFirstBox (reverse : Bool) {y : ℝ}
    (Y : Interval y) (X : Interval (U y)) (J : Interval (U (Aligned.j y)))
    (hX : 0<X.lo) (hJ : 0<J.lo) : Interval (Aligned.first reverse y) :=
  (((firstBox (Aligned.inner reverse) (jBox X) J hJ).mul (ratioBox Y X hX)).sub (firstBox (Aligned.outer reverse) Y X hX))

def alignedSecondBox (reverse : Bool) {y : ℝ}
    (Y : Interval y) (X : Interval (U y)) (J : Interval (U (Aligned.j y)))
    (hX : 0<X.lo) (hJ : 0<J.lo) : Interval (Aligned.second reverse y) :=
  (((((secondBox (Aligned.inner reverse) (jBox X) J hJ).neg).mul (ratioBox Y X hX).square).add ((firstBox (Aligned.inner reverse) (jBox X) J hJ).mul (ratioDBox X hX))).sub (secondBox (Aligned.outer reverse) Y X hX))

end SquaresInCircles.Eight.SecondWord.OppositeThree.ReferenceAlgebra
end
end
end
