module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Words.Common.JumpTwo
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeReferenceAlgebra
public import SquaresInCircles.Eight.Words.Second.WordData

/-!
# Eight squares: whole-domain growth of the L height label

The positive third and fourth derivatives give global slope control (`third_positive`,
`fourth_positive`). On the zero-source height interval `zero` the fourth derivative exceeds six
times the third (`fourth_growth`). Two increasing derivative differences then give the single
third-derivative estimate `third_dominates` used by the retained primary contact curve.
-/

section
/-!
## An exact endpoint loss from an upper curvature bound

Subtracting the endpoint-vanishing quadratic produces a concave
function. Its two endpoint values and one square completion bound the
whole closed interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord
open CommonQuarter CorePairGeometry Arithmetic

theorem curvature_chord_lower {f d dd : ℝ→ℝ} {l u x κ m : ℝ}
    (hx : x∈Icc l u) (hκ : 0≤κ)
    (hf : ∀t∈Icc l u,HasDerivAt f (d t) t)
    (hd : ∀t∈Icc l u,HasDerivAt d (dd t) t)
    (hdd : ∀t∈Icc l u,dd t≤κ) (hl : m<f l) (hu : m<f u) :
    m-κ*(u-l)^2/8<f x := by
  let g : ℝ→ℝ := fun t => f t-(κ/2)*(t-l)*(t-u)
  let gd : ℝ→ℝ := fun t => d t-(κ/2)*(2*t-l-u)
  have hq (t : ℝ) : HasDerivAt (fun y : ℝ => (κ/2)*(y-l)*(y-u)) ((κ/2)*(2*t-l-u)) t := by
    have h := (((hasDerivAt_id t).sub_const l).mul ((hasDerivAt_id t).sub_const u)).const_mul
      (κ/2)
    convert h using 1
    · funext y
      simp only [id,Pi.mul_apply]
      ring
    · simp only [id]
      ring
  have hq2 (t : ℝ) : HasDerivAt (fun y : ℝ => (κ/2)*(2*y-l-u)) κ t := by
    have h := ((((hasDerivAt_id t).const_mul 2).sub_const l).sub_const u).const_mul (κ/2)
    convert h using 1
    · funext y
      simp only [id]
    · ring
  have hg {t : ℝ} (ht : t∈Icc l u) : HasDerivAt g (gd t) t := (hf t ht).sub (hq t)
  have hgd {t : ℝ} (ht : t∈Icc l u) : HasDerivAt gd (dd t-κ) t := (hd t ht).sub (hq2 t)
  have hc : ConcaveOn ℝ (Icc l u) g := concave_of_deriv2
    (fun _ ht => hg ht) (fun _ ht => hgd ht) (fun t ht => sub_nonpos.mpr (hdd t ht))
  have hh := concave_gt_of_endpoints hc hx
    (show m<g l by simpa [g] using hl) (show m<g u by simpa [g] using hu)
  have hp := mul_nonneg hκ (sq_nonneg (2*x-l-u))
  dsimp only [g] at hh
  nlinarith

end SquaresInCircles.Eight.SecondWord
end
end
end

section
/-!
## Exact height coordinates for the mixed outer labels

The height radical is differentiated on its full positive domain.
One four-coefficient expression gives the negative P, T and L labels
and their first five derivatives.  All circle identities are equalities
at the unchanged original outer point.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord
open CommonQuarter CorePairGeometry Arithmetic

structure HeightLabel where
  c : ℝ
  v : ℝ
  k : ℝ
  w : ℝ

namespace HeightLabel

def root (u : ℝ) : ℝ := Real.sqrt (Q0-u^2)

lemma root_pos {u : ℝ} (hu : 0<Q0-u^2) : 0<root u := Real.sqrt_pos.mpr hu
lemma root_sq {u : ℝ} (hu : 0<Q0-u^2) : (root u)^2=Q0-u^2 := Real.sq_sqrt hu.le

lemma root_cage {u l r : ℝ} (hl : 0≤l) (hr : 0<r)
    (hlo : l^2<Q0-u^2) (hhi : Q0-u^2<r^2) : l<root u ∧ root u<r := by
  have hu : 0<Q0-u^2 := by nlinarith [sq_nonneg l]
  have hp := root_pos hu
  have hs := root_sq hu
  constructor <;> nlinarith

lemma root_hasDerivAt {u : ℝ} (hu : 0<Q0-u^2) : HasDerivAt root (-u/root u) u := by
  convert (((hasDerivAt_id u).pow 2).const_sub Q0).sqrt hu.ne' using 1
  · rfl
  · dsimp [root]
    ring

def eval (H : HeightLabel) (u : ℝ) : ℝ :=
  H.c-H.v*u^2-H.k*u/2-(H.w-H.k*u)*root u
def d1 (H : HeightLabel) (u : ℝ) : ℝ :=
  -2*H.v*u-H.k/2+(H.k*Q0+H.w*u-2*H.k*u^2)/root u
def d2 (H : HeightLabel) (u : ℝ) : ℝ :=
  -2*H.v+(H.w*Q0-3*H.k*Q0*u+2*H.k*u^3)/(root u)^3
def d3 (H : HeightLabel) (u : ℝ) : ℝ :=
  3*Q0*(H.w*u-H.k*Q0)/(root u)^5
def d4 (H : HeightLabel) (u : ℝ) : ℝ :=
  3*Q0*(H.w*(Q0+4*u^2)-5*H.k*Q0*u)/(root u)^7
def d5 (H : HeightLabel) (u : ℝ) : ℝ :=
  15*Q0*(H.w*u*(3*Q0+4*u^2)-H.k*Q0*(Q0+6*u^2))/(root u)^9

private lemma Q0_root_eq {u : ℝ} (hu : 0<Q0-u^2) : Q0=(root u)^2+u^2 := by
  rw [root_sq hu]; ring

local macro "height_algebra" h:term : tactic => `(tactic|
  (rw [Q0_root_eq $h]
   field_simp [(root_pos $h).ne']
   ring))

lemma eval_hasDerivAt (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) :
    HasDerivAt H.eval (H.d1 u) u := by
  have hd := ((((hasDerivAt_const u H.c).sub (((hasDerivAt_id u).pow 2).const_mul H.v)).sub
    (((hasDerivAt_id u).const_mul H.k).div_const 2)).sub
      ((((hasDerivAt_id u).const_mul H.k).const_sub H.w).mul (root_hasDerivAt hu)))
  convert hd using 1
  · rfl
  · dsimp [d1]
    height_algebra hu

lemma d1_hasDerivAt (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) :
    HasDerivAt H.d1 (H.d2 u) u := by
  have hn := (((hasDerivAt_id u).const_mul H.w).const_add (H.k*Q0)).sub
    (((hasDerivAt_id u).pow 2).const_mul (2*H.k))
  have hd := (((hasDerivAt_id u).const_mul (-2*H.v)).sub_const (H.k/2)).add
    (hn.div (root_hasDerivAt hu) (root_pos hu).ne')
  convert hd using 1
  · ext x
    dsimp [d1]
  · dsimp [d2]
    height_algebra hu

lemma d2_hasDerivAt (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) :
    HasDerivAt H.d2 (H.d3 u) u := by
  have hn := ((((hasDerivAt_id u).const_mul (3*H.k*Q0)).const_sub (H.w*Q0)).add
    (((hasDerivAt_id u).pow 3).const_mul (2*H.k)))
  have hd := (hn.div ((root_hasDerivAt hu).pow 3) (pow_ne_zero 3 (root_pos hu).ne')).const_add (-2*H.v)
  convert hd using 1
  · rfl
  · dsimp [d3]
    height_algebra hu

lemma d3_hasDerivAt (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) :
    HasDerivAt H.d3 (H.d4 u) u := by
  have hn := (((hasDerivAt_id u).const_mul H.w).sub_const (H.k*Q0)).const_mul (3*Q0)
  have hd := hn.div ((root_hasDerivAt hu).pow 5) (pow_ne_zero 5 (root_pos hu).ne')
  convert hd using 1
  · rfl
  · dsimp [d4]
    height_algebra hu

lemma d4_hasDerivAt (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) :
    HasDerivAt H.d4 (H.d5 u) u := by
  have hn := ((((((hasDerivAt_id u).pow 2).const_mul 4).const_add Q0).const_mul H.w).sub
    ((hasDerivAt_id u).const_mul (5*H.k*Q0))).const_mul (3*Q0)
  have hd := hn.div ((root_hasDerivAt hu).pow 7) (pow_ne_zero 7 (root_pos hu).ne')
  convert hd using 1
  · rfl
  · dsimp [d5]
    height_algebra hu

lemma d1_mul (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) :
    H.d1 u*root u=(-2*H.v*u-H.k/2)*root u+H.k*Q0+H.w*u-2*H.k*u^2 := by
  dsimp [d1]
  field_simp [(root_pos hu).ne']
  ring

lemma d2_mul (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) :
    H.d2 u*(root u)^3= -2*H.v*(root u)^3+H.w*Q0-3*H.k*Q0*u+2*H.k*u^3 := by
  dsimp [d2]
  field_simp [(root_pos hu).ne']
  ring

lemma d3_mul (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) :
    H.d3 u*(root u)^5=3*Q0*(H.w*u-H.k*Q0) := by
  dsimp [d3]
  field_simp [(root_pos hu).ne']

lemma fourth_growth_identity (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) (r : ℝ) :
    (H.d4 u-r*H.d3 u)*(root u)^7=
      3*Q0*(H.w*(Q0-u^2)+(5*u-r*(Q0-u^2))*(H.w*u-H.k*Q0)) := by
  dsimp [d3,d4]
  height_algebra hu

lemma actual_root {a b : ℝ} (hs : OuterState a b) : root (a+1/2)=b+1/2 := by
  have hrad : Q0-(a+1/2)^2=(b+1/2)^2 := by linarith [hs.2.2]
  dsimp [root]
  rw [hrad,Real.sqrt_sq_eq_abs,abs_of_nonneg (by linarith [hs.1])]

end HeightLabel

def LHeight : HeightLabel := ⟨1074925961/125000000,37437/25000,94721/50000,629979/100000⟩

lemma LHeight_actual {a b : ℝ} (hs : OuterState a b) : LHeight.eval (a+1/2)= -L b := by
  have hc := hs.2.2
  norm_num [Q0] at hc
  rw [HeightLabel.eval,HeightLabel.actual_root hs,
    show L b=LLabel.eval a b from LLabel.outer_actual hs]
  norm_num [LHeight,LLabel,RoleLabel.eval]
  linear_combination -(37437/25000)*hc

end SquaresInCircles.Eight.SecondWord
end
end
end

section
/-!
## Individual references for the whole L-height derivative argument

Every radical enclosure is evaluated at a named analytic reference.
Whole-interval monotonicity and convexity, rather than a continuous
cover, propagate these comparisons.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.LHeightReference
open CommonQuarter CorePairGeometry Arithmetic HeightLabel
open StationaryPrimitives (Interval)
open OppositeThree.ReferenceAlgebra (rootStep rootThree)

def rootAt (u s : ℝ) (hs : 0<s) (hu : 0≤Q0-u^2) : Interval (root u) :=
  rootThree (Interval.point (Q0-u^2)) s hs hu

def firstBox (u : ℝ) (R : Interval (root u)) (hR : 0<R.lo) : Interval (LHeight.d1 u) :=
  (Interval.point (-2*LHeight.v*u-LHeight.k/2)).add
    ((Interval.point (LHeight.k*Q0+LHeight.w*u-2*LHeight.k*u^2)).div R hR)

def secondBox (u : ℝ) (R : Interval (root u)) (hR : 0<R.lo) : Interval (LHeight.d2 u) :=
  (Interval.point (-2*LHeight.v)).add
    ((Interval.point (LHeight.w*Q0-3*LHeight.k*Q0*u+2*LHeight.k*u^3)).div R.cube
      (Interval.cube_lo_pos hR))

def thirdBox (u : ℝ) (R : Interval (root u)) (hR : 0<R.lo) : Interval (LHeight.d3 u) := by
  let P := R.square.mul R.cube
  have hP : 0<P.lo := Interval.mul_lo_pos (Interval.square_lo_pos hR) (Interval.cube_lo_pos hR)
  convert (Interval.point (3*Q0*(LHeight.w*u-LHeight.k*Q0))).div P hP using 1
  dsimp [HeightLabel.d3]; congr 1; ring

local macro "height_reference" : tactic => `(tactic|
  norm_num [rootAt,rootThree,rootStep,firstBox,secondBox,thirdBox,LHeight,Q0,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.inv,Interval.div])

/-- The enclosure of a transported interval is the transported enclosure. -/
private lemma r29_cast_lo {v w : ℝ} (hvw : v=w) (h : Interval v=Interval w) (x : Interval v) :
    (cast h x).lo=x.lo := by
  subst hvw
  rfl

private lemma r29_thirdBox_lo (u : ℝ) (R : Interval (root u)) (hR : 0<R.lo) :
    (thirdBox u R hR).lo=((Interval.point (3*Q0*(LHeight.w*u-LHeight.k*Q0))).div
      (R.square.mul R.cube)
      (Interval.mul_lo_pos (Interval.square_lo_pos hR) (Interval.cube_lo_pos hR))).lo := by
  unfold thirdBox
  dsimp only
  exact r29_cast_lo (by dsimp [HeightLabel.d3]; ring) _ _

lemma initial_third : (47/20:ℝ)<LHeight.d3 (171/125) := by
  let R := rootAt (171/125) (143/100) (by norm_num) (by norm_num [Q0])
  have hR : 0<R.lo := by dsimp [R]; height_reference
  let D := thirdBox (171/125) R hR
  have hh : (47/20:ℝ)<D.lo := by
    dsimp only [D]
    rw [r29_thirdBox_lo]
    dsimp [R]; height_reference
  exact hh.trans_le D.mem.1

lemma stationary_reference : (479/500:ℝ)<LHeight.d1 (161/100) ∧
    |LHeight.d2 (161/100)|<(61/1000:ℝ) := by
  let R := rootAt (161/100) (23/20) (by norm_num) (by norm_num [Q0])
  have hR : 0<R.lo := by dsimp [R]; height_reference
  let F := firstBox (161/100) R hR
  let D := secondBox (161/100) R hR
  have hf : (479/500:ℝ)<F.lo := by dsimp [F,R]; height_reference
  have hl : -(61/1000:ℝ)<D.lo := by dsimp [D,R]; height_reference
  have hu : D.hi<(61/1000:ℝ) := by dsimp [D,R]; height_reference
  exact ⟨hf.trans_le F.mem.1,abs_lt.mpr ⟨hl.trans_le D.mem.1,D.mem.2.trans_lt hu⟩⟩

lemma low_second : LHeight.d2 (8/5)<(-9/100:ℝ) := by
  let R := rootAt (8/5) (117/100) (by norm_num) (by norm_num [Q0])
  have hR : 0<R.lo := by dsimp [R]; height_reference
  let D := secondBox (8/5) R hR
  have hh : D.hi<(-9/100:ℝ) := by dsimp [D,R]; height_reference
  exact D.mem.2.trans_lt hh

lemma high_second : (4/5:ℝ)<LHeight.d2 (33/20) := by
  let R := rootAt (33/20) (11/10) (by norm_num) (by norm_num [Q0])
  have hR : 0<R.lo := by dsimp [R]; height_reference
  let D := secondBox (33/20) R hR
  have hh : (4/5:ℝ)<D.lo := by dsimp [D,R]; height_reference
  exact hh.trans_le D.mem.1

lemma late_second : LHeight.d2 (81/50)<(23/100:ℝ) := by
  let R := rootAt (81/50) (57/50) (by norm_num) (by norm_num [Q0])
  have hR : 0<R.lo := by dsimp [R]; height_reference
  let D := secondBox (81/50) R hR
  have hh : D.hi<(23/100:ℝ) := by dsimp [D,R]; height_reference
  exact D.mem.2.trans_lt hh

lemma zero_initial : LHeight.d1 (159/100)<1 ∧ LHeight.d2 (159/100)<0 ∧
    (13:ℝ)<LHeight.d3 (159/100) := by
  let R := rootAt (159/100) (59/50) (by norm_num) (by norm_num [Q0])
  have hR : 0<R.lo := by dsimp [R]; height_reference
  let F := firstBox (159/100) R hR
  let D := secondBox (159/100) R hR
  let T := thirdBox (159/100) R hR
  have hf : F.hi<(1:ℝ) := by dsimp [F,R]; height_reference
  have hd : D.hi<(0:ℝ) := by dsimp [D,R]; height_reference
  have ht : (13:ℝ)<T.lo := by
    dsimp only [T]
    rw [r29_thirdBox_lo]
    dsimp [R]; height_reference
  exact ⟨F.mem.2.trans_lt hf,D.mem.2.trans_lt hd,ht.trans_le T.mem.1⟩

end SquaresInCircles.Eight.SecondWord.LHeightReference
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.LHeightBounds
open CommonQuarter CorePairGeometry Arithmetic HeightLabel

def heights : Set ℝ := Icc (171/125) (383/200)
def zero : Set ℝ := Icc (159/100) (44/25)

lemma domain {u : ℝ} (hu : u∈heights) : 0<Q0-u^2 := by
  have hs := pow_le_pow_left₀ (by linarith [hu.1] : 0≤u) hu.2 2
  norm_num [Q0]
  nlinarith

lemma zero_subset : zero⊆heights := fun u hu => ⟨by linarith [hu.1],by linarith [hu.2]⟩

lemma numerator_positive {u : ℝ} (hu : u∈heights) : 0<LHeight.w*u-LHeight.k*Q0 := by
  norm_num [LHeight,Q0]
  nlinarith [hu.1]

lemma third_positive {u : ℝ} (hu : u∈heights) : 0<LHeight.d3 u := by
  exact div_pos (mul_pos (by norm_num [Q0] : (0:ℝ)<3*Q0) (numerator_positive hu))
    (pow_pos (root_pos (domain hu)) 5)

lemma fourth_positive {u : ℝ} (hu : u∈heights) : 0<LHeight.d4 u := by
  have hn := numerator_positive hu
  have hr := domain hu
  have hu0 : 0<u := by linarith [hu.1]
  have hw : 0<LHeight.w := by norm_num [LHeight]
  have he : LHeight.w*(Q0+4*u^2)-5*LHeight.k*Q0*u=
      LHeight.w*(Q0-u^2)+5*u*(LHeight.w*u-LHeight.k*Q0) := by ring
  have hp : 0<LHeight.w*(Q0+4*u^2)-5*LHeight.k*Q0*u := by rw [he]; positivity
  exact div_pos (mul_pos (by norm_num [Q0] : (0:ℝ)<3*Q0) hp)
    (pow_pos (root_pos hr) 7)

lemma third_monotone : MonotoneOn LHeight.d3 heights :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hu => (LHeight.d3_hasDerivAt (domain hu)).continuousAt.continuousWithinAt)
    (fun _ hu => LHeight.d3_hasDerivAt (domain (Ioo_subset_Icc_self hu)))
    (fun _ hu => (fourth_positive (Ioo_subset_Icc_self hu)).le)

lemma second_monotone : MonotoneOn LHeight.d2 heights :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hu => (LHeight.d2_hasDerivAt (domain hu)).continuousAt.continuousWithinAt)
    (fun _ hu => LHeight.d2_hasDerivAt (domain (Ioo_subset_Icc_self hu)))
    (fun _ hu => (third_positive (Ioo_subset_Icc_self hu)).le)

lemma third_lower {u : ℝ} (hu : u∈heights) : (47/20:ℝ)<LHeight.d3 u :=
  LHeightReference.initial_third.trans_le
    (third_monotone (by norm_num [heights]) hu hu.1)

lemma first_lower {u : ℝ} (hu : u∈heights) : (19/20:ℝ)<LHeight.d1 u := by
  have ht := curvature_tangent (f := LHeight.d1) (d := LHeight.d2) (dd := LHeight.d3)
    (κ := 2) hu (show (161/100:ℝ)∈heights by norm_num [heights])
    (fun y hy => LHeight.d1_hasDerivAt (domain hy))
    (fun y hy => LHeight.d2_hasDerivAt (domain hy))
    (fun y hy => by linarith [third_lower hy])
  have hd := abs_lt.mp LHeightReference.stationary_reference.2
  have hsq : (LHeight.d2 (161/100))^2<(61/1000:ℝ)^2 := by nlinarith
  have hp := sq_nonneg (u-161/100+LHeight.d2 (161/100)/2)
  nlinarith [LHeightReference.stationary_reference.1]

lemma eval_monotone : MonotoneOn LHeight.eval heights :=
  monoOn_of_hasDeriv_nonneg
    (fun u hu => (LHeight.eval_hasDerivAt (domain hu)).continuousAt.continuousWithinAt)
    (fun u hu => LHeight.eval_hasDerivAt (domain (Ioo_subset_Icc_self hu)))
    (fun u hu => by linarith [first_lower (Ioo_subset_Icc_self hu)])

lemma second_negative_below {u : ℝ} (hu : u∈heights) (hcut : u≤8/5) : LHeight.d2 u<0 := by
  have hm := second_monotone hu (by norm_num [heights]) hcut
  linarith [LHeightReference.low_second]

lemma first_antitone_low : AntitoneOn LHeight.d1 (Icc (171/125) (8/5)) :=
  antiOn_of_hasDeriv_nonpos
    (fun u hu => (LHeight.d1_hasDerivAt (domain ⟨hu.1,by linarith [hu.2]⟩)).continuousAt.continuousWithinAt)
    (fun u hu => LHeight.d1_hasDerivAt (domain ⟨hu.1.le,by linarith [hu.2]⟩))
    (fun u hu => (second_negative_below ⟨hu.1.le,by linarith [hu.2]⟩ hu.2.le).le)

lemma first_monotone_high : MonotoneOn LHeight.d1 (Icc (33/20) (383/200)) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro u hu
    exact (LHeight.d1_hasDerivAt (domain ⟨by linarith [hu.1],hu.2⟩)).continuousAt.continuousWithinAt
  · intro u hu
    exact LHeight.d1_hasDerivAt (domain ⟨by linarith [hu.1],hu.2.le⟩)
  · intro u hu
    have hm := second_monotone (by norm_num [heights]) ⟨by linarith [hu.1],hu.2.le⟩ hu.1.le
    linarith [LHeightReference.high_second]

lemma second_upper_late {u : ℝ} (hu : u∈Icc (3/2) (81/50)) : LHeight.d2 u<(23/100:ℝ) :=
  (second_monotone ⟨by linarith [hu.1],by linarith [hu.2]⟩
    (by norm_num [heights]) hu.2).trans_lt LHeightReference.late_second

lemma fourth_growth {u : ℝ} (hu : u∈zero) : 6*LHeight.d3 u<LHeight.d4 u := by
  have hd := domain (zero_subset hu)
  have hn := numerator_positive (zero_subset hu)
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤159/100) hu.1 2
  have hdiff : 0<u-(Q0-u^2) := by norm_num [Q0]; nlinarith [hu.1]
  have hcoef : 0<LHeight.w-(LHeight.w*u-LHeight.k*Q0) := by
    norm_num [LHeight,Q0]
    nlinarith [hu.2]
  have hp : 0<3*Q0*((LHeight.w-(LHeight.w*u-LHeight.k*Q0))*(Q0-u^2)+
      5*(LHeight.w*u-LHeight.k*Q0)*(u-(Q0-u^2))) := by
    have hQ : 0<Q0 := by norm_num [Q0]
    positivity
  have he := LHeight.fourth_growth_identity hd 6
  have hrewrite : LHeight.w*(Q0-u^2)+(5*u-6*(Q0-u^2))*(LHeight.w*u-LHeight.k*Q0)=
      (LHeight.w-(LHeight.w*u-LHeight.k*Q0))*(Q0-u^2)+
        5*(LHeight.w*u-LHeight.k*Q0)*(u-(Q0-u^2)) := by ring
  rw [hrewrite] at he
  apply (mul_lt_mul_iff_left₀ (pow_pos (root_pos hd) 7)).mp
  nlinarith

lemma third_above_twice_second {u : ℝ} (hu : u∈zero) : 2*LHeight.d2 u<LHeight.d3 u := by
  have hf {y : ℝ} (hy : y∈zero) : HasDerivAt (fun z => LHeight.d3 z-2*LHeight.d2 z)
      (LHeight.d4 y-2*LHeight.d3 y) y :=
    (LHeight.d3_hasDerivAt (domain (zero_subset hy))).sub
      ((LHeight.d2_hasDerivAt (domain (zero_subset hy))).const_mul 2)
  have hm : MonotoneOn (fun z => LHeight.d3 z-2*LHeight.d2 z) zero :=
    monoOn_of_hasDeriv_nonneg
      (fun y hy => (hf hy).continuousAt.continuousWithinAt)
      (fun y hy => hf (Ioo_subset_Icc_self hy))
      (fun y hy => by linarith [fourth_growth (Ioo_subset_Icc_self hy),
        third_positive (zero_subset (Ioo_subset_Icc_self hy))])
  have hh := hm (by norm_num [zero]) hu hu.1
  linarith [LHeightReference.zero_initial.2.1,LHeightReference.zero_initial.2.2]

lemma third_dominates {u : ℝ} (hu : u∈zero) :
    2*LHeight.d1 u+5*max (LHeight.d2 u) 0<LHeight.d3 u := by
  have hf {y : ℝ} (hy : y∈zero) : HasDerivAt (fun z => LHeight.d3 z-2*LHeight.d1 z)
      (LHeight.d4 y-2*LHeight.d2 y) y :=
    (LHeight.d3_hasDerivAt (domain (zero_subset hy))).sub
      ((LHeight.d1_hasDerivAt (domain (zero_subset hy))).const_mul 2)
  have hg {y : ℝ} (hy : y∈zero) :
      HasDerivAt (fun z => LHeight.d3 z-2*LHeight.d1 z-5*LHeight.d2 z)
        (LHeight.d4 y-2*LHeight.d2 y-5*LHeight.d3 y) y :=
    (hf hy).sub ((LHeight.d2_hasDerivAt (domain (zero_subset hy))).const_mul 5)
  have hmF : MonotoneOn (fun z => LHeight.d3 z-2*LHeight.d1 z) zero :=
    monoOn_of_hasDeriv_nonneg
      (fun y hy => (hf hy).continuousAt.continuousWithinAt)
      (fun y hy => hf (Ioo_subset_Icc_self hy))
      (fun y hy => by linarith [fourth_growth (Ioo_subset_Icc_self hy),
        third_above_twice_second (Ioo_subset_Icc_self hy),
        third_positive (zero_subset (Ioo_subset_Icc_self hy))])
  have hmG : MonotoneOn (fun z => LHeight.d3 z-2*LHeight.d1 z-5*LHeight.d2 z) zero :=
    monoOn_of_hasDeriv_nonneg
      (fun y hy => (hg hy).continuousAt.continuousWithinAt)
      (fun y hy => hg (Ioo_subset_Icc_self hy))
      (fun y hy => by linarith [fourth_growth (Ioo_subset_Icc_self hy),
        third_above_twice_second (Ioo_subset_Icc_self hy)])
  have hF := hmF (by norm_num [zero]) hu hu.1
  have hG := hmG (by norm_num [zero]) hu hu.1
  have href := LHeightReference.zero_initial
  by_cases hsign : 0≤LHeight.d2 u
  · rw [max_eq_left hsign]
    linarith
  · rw [max_eq_right (not_le.mp hsign).le]
    linarith

end SquaresInCircles.Eight.SecondWord.LHeightBounds
end
end
end
