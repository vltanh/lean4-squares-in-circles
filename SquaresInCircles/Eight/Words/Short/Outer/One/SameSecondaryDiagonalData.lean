module

public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeAligned
public import SquaresInCircles.Eight.Words.Short.Outer.One.RoleFourScalars
public import SquaresInCircles.Eight.Words.Short.Outer.One.SamePositiveGeometry

/-!
# Eight squares: the actual late source-diagonal secondary arc and its speed

The two coordinates are those of the already constructed exact circle
rotation, exchanged after the simultaneous-diagonal event. The speed
and its second derivative retain the factor and its exact derivatives.
-/

section
/-!
## The named aligned values for the paired same-sign owners

All enclosures remain attached to the actual circle roots. The only
interior reference is 517/10000; 1/80 is the stated initial-derivative
reference. No variable-domain grid is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Reference
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio)
open StationaryPrimitives (Interval)
open SecondWord (U)
open SecondWord.OppositeThree.ReferenceAlgebra

def valueBox (r : Row) {B : ℝ} (Y : Interval B)
    (T : Interval (U B)) (S : Interval (U (1-B))) : Interval (aligned r B) := by
  convert ((((((piBox.div (Interval.point 2) (by norm_num [Interval.point])).add
    (Interval.point (c r))).add
      ((Interval.point (p r)).mul ((Interval.point 1).sub Y))).sub
        ((Interval.point (q r)).mul (coordinate S))).sub
          ((Interval.point (P r)).mul (coordinate T))).add ((Interval.point (t r)).mul Y))
    using 1
  dsimp [aligned,source,target]
  ring

def firstBox (r : Row) {B : ℝ} (Y : Interval B)
    (T : Interval (U B)) (S : Interval (U (1-B))) (hT : 0<T.lo) (hS : 0<S.lo) :
    Interval (alignedD r B) := by
  convert ((((Interval.point (-p r)).sub
    ((Interval.point (q r)).mul (ratioBox ((Interval.point 1).sub Y) S hS))).add
      ((Interval.point (P r)).mul (ratioBox Y T hT))).add (Interval.point (t r))) using 1
  dsimp [alignedD,sourceD,targetD]
  ring

def angleBox (r : Row) {B : ℝ} (Y : Interval B)
    (T : Interval (U B)) (S : Interval (U (1-B))) (hS : 0<S.lo) :
    Interval (initialAngle r B) := by
  convert (Interval.point 1).sub
    (((Interval.point (p r)).add
      ((Interval.point (q r)).mul (ratioBox ((Interval.point 1).sub Y) S hS))).mul
        (T.sub (Interval.point 1))) using 1
  dsimp [initialAngle,sourceD,U]
  ring

private lemma r87_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r87_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl

private lemma r87_shifted_eq {y : ℝ} : U y = Real.sqrt (Q0-(y+1/2)^2) := by dsimp [U,arc]; ring
private lemma r87_shifted_lo {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).lo = (rootThree (radicand Y) s hs hr).lo :=
  r87_mpr_lo r87_shifted_eq (congrArg _ r87_shifted_eq) _
private lemma r87_shifted_hi {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).hi = (rootThree (radicand Y) s hs hr).hi :=
  r87_mpr_hi r87_shifted_eq (congrArg _ r87_shifted_eq) _

private lemma r87_coordinate_eq {y : ℝ} : arc y = U y-1/2 := by dsimp [U]; ring
private lemma r87_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r87_mpr_lo r87_coordinate_eq (congrArg _ r87_coordinate_eq) _
private lemma r87_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r87_mpr_hi r87_coordinate_eq (congrArg _ r87_coordinate_eq) _

private lemma r87_value_eq (r : Row) {B : ℝ} : aligned r B =
    Real.pi/2+c r+p r*(1-B)-q r*arc (1-B)-P r*arc B+t r*B := by
  dsimp [aligned,source,target]; ring
private lemma r87_valueBox_lo (r : Row) {B : ℝ} (Y : Interval B)
    (T : Interval (U B)) (S : Interval (U (1-B))) :
    (valueBox r Y T S).lo = ((((((piBox.div (Interval.point 2) (by norm_num [Interval.point])).add
      (Interval.point (c r))).add
        ((Interval.point (p r)).mul ((Interval.point 1).sub Y))).sub
          ((Interval.point (q r)).mul (coordinate S))).sub
            ((Interval.point (P r)).mul (coordinate T))).add ((Interval.point (t r)).mul Y)).lo :=
  r87_mpr_lo (r87_value_eq r) (congrArg _ (r87_value_eq r)) _

private lemma r87_first_eq (r : Row) {B : ℝ} : alignedD r B =
    -p r-q r*ratio (1-B)+P r*ratio B+t r := by
  dsimp [alignedD,sourceD,targetD]; ring
private lemma r87_firstBox_hi (r : Row) {B : ℝ} (Y : Interval B)
    (T : Interval (U B)) (S : Interval (U (1-B))) (hT : 0<T.lo) (hS : 0<S.lo) :
    (firstBox r Y T S hT hS).hi = ((((Interval.point (-p r)).sub
      ((Interval.point (q r)).mul (ratioBox ((Interval.point 1).sub Y) S hS))).add
        ((Interval.point (P r)).mul (ratioBox Y T hT))).add (Interval.point (t r))).hi :=
  r87_mpr_hi (r87_first_eq r) (congrArg _ (r87_first_eq r)) _
private lemma r87_firstBox_lo (r : Row) {B : ℝ} (Y : Interval B)
    (T : Interval (U B)) (S : Interval (U (1-B))) (hT : 0<T.lo) (hS : 0<S.lo) :
    (firstBox r Y T S hT hS).lo = ((((Interval.point (-p r)).sub
      ((Interval.point (q r)).mul (ratioBox ((Interval.point 1).sub Y) S hS))).add
        ((Interval.point (P r)).mul (ratioBox Y T hT))).add (Interval.point (t r))).lo :=
  r87_mpr_lo (r87_first_eq r) (congrArg _ (r87_first_eq r)) _

private lemma r87_angle_eq (r : Row) {B : ℝ} : initialAngle r B =
    1-(p r+q r*ratio (1-B))*(U B-1) := by
  dsimp [initialAngle,sourceD,U]; ring
private lemma r87_angleBox_lo (r : Row) {B : ℝ} (Y : Interval B)
    (T : Interval (U B)) (S : Interval (U (1-B))) (hS : 0<S.lo) :
    (angleBox r Y T S hS).lo = ((Interval.point 1).sub
      (((Interval.point (p r)).add
        ((Interval.point (q r)).mul (ratioBox ((Interval.point 1).sub Y) S hS))).mul
          (T.sub (Interval.point 1)))).lo :=
  r87_mpr_lo (r87_angle_eq r) (congrArg _ (r87_angle_eq r)) _

local macro "same_aligned_reference" : tactic => `(tactic|
  norm_num [r87_valueBox_lo,r87_firstBox_lo,r87_firstBox_hi,r87_angleBox_lo,piBox,
    r87_coordinate_lo,r87_coordinate_hi,r87_shifted_lo,r87_shifted_hi,radicand,rootThree,rootStep,
    ratioBox,Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.div,Interval.inv,Q0,c,p,q,P,t,eta])

lemma diagonal_endpoints (r : Row) (hr : r=1 ∨ r=2) :
    (8981/10000:ℝ)<aligned r b0 := by
  let D := RoleFour.dBox
  let Y := (Interval.point 1).sub D
  have hrad : 0≤(radicand Y).lo := by
    norm_num [Y,D,RoleFour.dBox,radicand,Interval.of_bounds,Interval.point,
      Interval.add,Interval.sub,Interval.neg,Interval.square,Interval.mul,Q0]
  let T := shifted Y (19/10) (by norm_num) hrad
  let S : Interval (U (1-(1-outerDiagonal))) := Interval.of_bounds
    (show U (1-(1-outerDiagonal))∈Icc (1399214065109/1000000000000:ℝ)
      (1399214065110/1000000000000) from by
        have hh : 1-(1-outerDiagonal)=outerDiagonal := by ring
        have hd : outerDiagonal+1/2=Real.sqrt (Q0/2) := by dsimp [outerDiagonal]; ring
        rw [hh,U,SameContact.arc_diagonal,hd]
        constructor
        · exact Real.le_sqrt_of_sq_le (by norm_num [Q0])
        · rw [Real.sqrt_le_left (by norm_num)]; norm_num [Q0])
  have hlo : (8981/10000:ℝ)<(valueBox r Y T S).lo := by
    rcases hr with rfl | rfl <;>
      dsimp [Y,D,T,S] <;> norm_num [RoleFour.dBox] <;> same_aligned_reference
  exact hlo.trans_le (valueBox r Y T S).mem.1

lemma convex_reference :
    (89811/100000:ℝ)<aligned 0 (517/10000)-(alignedD 0 (517/10000))^2/2 := by
  let Y := Interval.point (517/10000:ℝ)
  let Z := (Interval.point 1).sub Y
  have hY : 0≤(radicand Y).lo := by dsimp [Y]; same_aligned_reference
  have hZ : 0≤(radicand Z).lo := by dsimp [Z,Y]; same_aligned_reference
  let T := shifted Y (19/10) (by norm_num) hY
  let S := shifted Z (27/20) (by norm_num) hZ
  have hT : 0<T.lo := by dsimp [T,Y]; same_aligned_reference
  have hS : 0<S.lo := by dsimp [S,Z,Y]; same_aligned_reference
  let V := valueBox 0 Y T S
  let D := firstBox 0 Y T S hT hS
  let L := V.sub (D.square.mul (Interval.point (1/2)))
  have hlo : (89811/100000:ℝ)<L.lo := by
    dsimp [L,V,D,T,S,Z,Y]
    same_aligned_reference
  have hh := hlo.trans_le L.mem.1
  linarith

lemma eta_values (r : Row) : (89908/100000:ℝ)<aligned r eta := by
  let Y := Interval.point eta
  let Z := (Interval.point 1).sub Y
  have hY : 0≤(radicand Y).lo := by dsimp [Y]; same_aligned_reference
  have hZ : 0≤(radicand Z).lo := by dsimp [Z,Y]; same_aligned_reference
  let T := shifted Y (19/10) (by norm_num) hY
  let S := shifted Z (13/10) (by norm_num) hZ
  have hlo : (89908/100000:ℝ)<(valueBox r Y T S).lo := by
    fin_cases r <;> dsimp [T,S,Z,Y] <;> same_aligned_reference
  exact hlo.trans_le (valueBox r Y T S).mem.1

lemma eta_derivative : alignedD 0 eta<0 := by
  let Y := Interval.point eta
  let Z := (Interval.point 1).sub Y
  have hY : 0≤(radicand Y).lo := by dsimp [Y]; same_aligned_reference
  have hZ : 0≤(radicand Z).lo := by dsimp [Z,Y]; same_aligned_reference
  let T := shifted Y (19/10) (by norm_num) hY
  let S := shifted Z (13/10) (by norm_num) hZ
  have hT : 0<T.lo := by dsimp [T,Y]; same_aligned_reference
  have hS : 0<S.lo := by dsimp [S,Z,Y]; same_aligned_reference
  have hhi : (firstBox 0 Y T S hT hS).hi<0 := by
    dsimp [T,S,Z,Y]
    same_aligned_reference
  exact (firstBox 0 Y T S hT hS).mem.2.trans_lt hhi

lemma angle_zero (r : Row) : -(1/50:ℝ)< initialAngle r 0 := by
  let Y := Interval.point (0:ℝ)
  let Z := (Interval.point 1).sub Y
  have hY : 0≤(radicand Y).lo := by dsimp [Y]; same_aligned_reference
  have hZ : 0≤(radicand Z).lo := by dsimp [Z,Y]; same_aligned_reference
  let T := shifted Y (19/10) (by norm_num) hY
  let S := shifted Z (13/10) (by norm_num) hZ
  have hS : 0<S.lo := by dsimp [S,Z,Y]; same_aligned_reference
  have hlo : -(1/50:ℝ)<(angleBox r Y T S hS).lo := by
    fin_cases r <;> dsimp [T,S,Z,Y] <;> same_aligned_reference
  exact hlo.trans_le (angleBox r Y T S hS).mem.1

lemma angle_eta (r : Row) : 0< initialAngle r eta := by
  let Y := Interval.point eta
  let Z := (Interval.point 1).sub Y
  have hY : 0≤(radicand Y).lo := by dsimp [Y]; same_aligned_reference
  have hZ : 0≤(radicand Z).lo := by dsimp [Z,Y]; same_aligned_reference
  let T := shifted Y (19/10) (by norm_num) hY
  let S := shifted Z (13/10) (by norm_num) hZ
  have hS : 0<S.lo := by dsimp [S,Z,Y]; same_aligned_reference
  have hlo : 0<(angleBox r Y T S hS).lo := by
    fin_cases r <;> dsimp [T,S,Z,Y] <;> same_aligned_reference
  exact hlo.trans_le (angleBox r Y T S hS).mem.1

end SquaresInCircles.Eight.ShortOuterOne.Same.Reference
end
end
end

section
/-!
## Every aligned state for the paired same-sign owners

Two rows decrease to the diagonal endpoint. The first row uses its
single strongly convex scalar and the stated interior reference.
The final theorem starts with the weak original aligned separator.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD)

lemma eta_mem : eta∈Icc 0 b0 := ⟨by norm_num [eta],by dsimp [eta]; linarith [b0_bounds.1]⟩

lemma alignedD_zero_monotone : MonotoneOn (alignedD 0) (Icc 0 b0) :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => (alignedD_hasDerivAt 0 hB).continuousAt.continuousWithinAt)
    (fun B hB => alignedD_hasDerivAt 0 (Ioo_subset_Icc_self hB))
    (fun B hB => by linarith [aligned_curvature (Ioo_subset_Icc_self hB)])

lemma aligned_later_antitone (r : Row) (hr : r=1 ∨ r=2) :
    AntitoneOn (aligned r) (Icc 0 b0) := antiOn_of_hasDeriv_nonpos
  (fun _ hB => (aligned_hasDerivAt r hB).continuousAt.continuousWithinAt)
  (fun _ hB => aligned_hasDerivAt r (Ioo_subset_Icc_self hB))
  (fun _ hB => (aligned_later_derivative r hr (Ioo_subset_Icc_self hB)).le)

theorem aligned_lower (r : Row) {B : ℝ} (hB : B∈Icc 0 b0) :
    (8981/10000:ℝ)<aligned r B := by
  by_cases hzero : r=0
  · subst r
    have href : (517/10000:ℝ)∈Icc 0 b0 :=
      ⟨by norm_num,by linarith [b0_bounds.1]⟩
    have hh := CenteredMonomialBounds.second_derivative_tangent_lower
      (κ := (1:ℝ)) (fun y hy => aligned_hasDerivAt 0 hy)
      (fun y hy => alignedD_hasDerivAt 0 hy)
      (fun y hy => (aligned_curvature hy).le) href hB
    have hs := sq_nonneg (B-517/10000+alignedD 0 (517/10000))
    nlinarith [Reference.convex_reference]
  · have hr : r=1 ∨ r=2 := by fin_cases r <;> simp_all
    exact (Reference.diagonal_endpoints r hr).trans_le
      (aligned_later_antitone r hr hB ⟨b0_mem.1,le_rfl⟩ hB.2)

lemma aligned_initial_antitone (r : Row) : AntitoneOn (aligned r) (Icc 0 eta) := by
  have hdom : ∀B∈Icc 0 eta,B∈Icc 0 b0 := fun B hB => ⟨hB.1,hB.2.trans eta_mem.2⟩
  apply antiOn_of_hasDeriv_nonpos
  · intro B hB
    exact (aligned_hasDerivAt r (hdom B hB)).continuousAt.continuousWithinAt
  · intro B hB
    exact aligned_hasDerivAt r (hdom B (Ioo_subset_Icc_self hB))
  · intro B hB
    by_cases hzero : r=0
    · subst r
      have hh := alignedD_zero_monotone (hdom B (Ioo_subset_Icc_self hB)) eta_mem hB.2.le
      exact hh.trans Reference.eta_derivative.le
    · have hr : r=1 ∨ r=2 := by fin_cases r <;> simp_all
      exact (aligned_later_derivative r hr (hdom B (Ioo_subset_Icc_self hB))).le

lemma aligned_initial_lower (r : Row) {B : ℝ} (hB : B∈Icc 0 eta) :
    (89908/100000:ℝ)<aligned r B :=
  (Reference.eta_values r).trans_le
    (aligned_initial_antitone r hB ⟨eta_mem.1,le_rfl⟩ hB.2)

lemma initialAngle_monotone (r : Row) : MonotoneOn (initialAngle r) (Icc 0 b0) := by
  intro B hB D hD hBD
  have hdB := aligned_domains hB
  have hdD := aligned_domains hD
  have hr := SameContact.ratio_monotone (primary_domain hdD.2.2)
    (primary_domain hdB.2.2) (by linarith)
  have hq : 0≤q r := by fin_cases r <;> norm_num [q]
  have hsource : sourceD r (1-D)≤ sourceD r (1-B) := by
    have hh := mul_le_mul_of_nonneg_left hr hq
    dsimp [sourceD]
    linarith
  have harc := SameContact.arc_antitone (SameContact.outer_domain hdB.1)
    (SameContact.outer_domain hdD.1) hBD
  have hproduct := mul_le_mul hsource (show arc D-1/2≤arc B-1/2 by linarith)
    (show 0≤arc D-1/2 by linarith [aligned_target_root hD])
    (show 0≤ sourceD r (1-B) by linarith [sourceD_lower r hdB.2.2])
  dsimp [initialAngle]
  linarith

lemma initialAngle_lower (r : Row) {B : ℝ} (hB : B∈Icc 0 b0) :
    -(1/50:ℝ)< initialAngle r B :=
  (Reference.angle_zero r).trans_le
    (initialAngle_monotone r ⟨le_rfl,b0_mem.1⟩ hB hB.1)

lemma initialAngle_negative_location (r : Row) {B : ℝ} (hB : B∈Icc 0 b0)
    (hne : initialAngle r B<0) : B<eta := by
  by_contra! hbad
  have hh := initialAngle_monotone r eta_mem hB hbad
  linarith [Reference.angle_eta r]

/-- The original aligned primary separator, including source-diagonal slack. -/
theorem aligned_original (r : Row) {a b A B : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hm : 1≤a+B) :
    (8981/10000:ℝ)<Real.pi/2+c r+p r*a-q r*b-P r*A+t r*B := by
  have ha : a∈Icc outerDiagonal outerAxial := ⟨(outer_bounds hs).1,(outer_bounds hs).2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hsource : source r a=p r*a-q r*b := by rw [source,(SameContact.actual_arc hs).2]
  have htarget : target r B= -P r*A+t r*B := by rw [target,(SameContact.actual_arc ht).1]
  by_cases hsmall : B≤b0
  · have hd := aligned_domains ⟨hB.1,hsmall⟩
    have hmono := source_monotone r hd.2.2 ha (by linarith)
    have hh := aligned_lower r ⟨hB.1,hsmall⟩
    dsimp [aligned] at hh
    rw [hsource] at hmono
    rw [htarget] at hh
    linarith
  · have hd : outerDiagonal∈Icc outerDiagonal outerAxial := ⟨le_rfl,SameContact.diagonal_le_axial⟩
    have hmonoS := source_monotone r hd ha ha.1
    have hmonoT := target_monotone r b0_mem hB (le_of_not_ge hsmall)
    have hh := aligned_lower r (show b0∈Icc 0 b0 from ⟨b0_mem.1,le_rfl⟩)
    have he : 1-b0=outerDiagonal := by dsimp [b0]; ring
    dsimp [aligned] at hh
    rw [he] at hh
    rw [hsource] at hmonoS
    rw [htarget] at hmonoT
    linarith

end SquaresInCircles.Eight.ShortOuterOne.Same
end
end
end

section
/-!
## The complete same-sign source-diagonal primary arc

The circle rotation is the existing exact primary-diagonal geometry.
The cost is concave until the unique simultaneous-diagonal event.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Diagonal
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc)
open StationaryPrimitives (Interval)
open SecondWord.SameZero.PJ.Reference (sinBox cosBox)

abbrev Z := SecondWord.NegativeTwo.PrimaryDiagonal.Z
abbrev Y := SecondWord.NegativeTwo.PrimaryDiagonal.Y
abbrev horizontal := SecondWord.NegativeTwo.PrimaryDiagonal.horizontal
abbrev vertical := SecondWord.NegativeTwo.PrimaryDiagonal.vertical
abbrev height := SecondWord.NegativeTwo.PrimaryDiagonal.height
abbrev factor := SecondWord.NegativeTwo.PrimaryDiagonal.factor
abbrev factorD := SecondWord.NegativeTwo.PrimaryDiagonal.factorD
abbrev Domain := SecondWord.NegativeTwo.PrimaryDiagonal.Domain

def joinContact (x : ℝ) : ℝ :=
  1/2+(1/2-outerDiagonal)*Real.cos x+(outerDiagonal+1/2)*Real.sin x
def joinSpeed (x : ℝ) : ℝ :=
  (outerDiagonal-1/2)*Real.sin x+(outerDiagonal+1/2)*Real.cos x
def IsEvent (e : ℝ) : Prop := e∈Ioo (2779/5000:ℝ) (5559/10000) ∧ joinContact e=outerDiagonal

lemma joinContact_hasDerivAt (x : ℝ) : HasDerivAt joinContact (joinSpeed x) x := by
  convert (((Real.hasDerivAt_cos x).const_mul (1/2-outerDiagonal)).const_add (1/2)).add
    ((Real.hasDerivAt_sin x).const_mul (outerDiagonal+1/2)) using 1
  · funext y; simp only [joinContact,Pi.add_apply]
  · simp only [joinSpeed]; ring

lemma joinContact_strictMono : StrictMonoOn joinContact (Icc 0 (7/10)) := by
  apply strict_increase_of_reserve
    (fun x _ => (joinContact_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x _ => joinContact_hasDerivAt x) (show (0:ℝ)<1 by norm_num)
  intro x hx
  have ht := positive_trig (Ioo_subset_Icc_self hx)
  have hs := mul_nonneg (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1]) ht.2.2.1
  have hc := mul_le_mul (show (139/100:ℝ)≤outerDiagonal+1/2 by linarith [outer_endpoint_bounds.2.2.1])
    (show (191/250:ℝ)≤Real.cos x by linarith [ht.1]) (by norm_num)
    (show 0≤outerDiagonal+1/2 by linarith [outer_endpoint_bounds.2.2.1])
  dsimp [joinSpeed]
  nlinarith

def joinBox (x : ℝ) (hx : 0≤x) : Interval (joinContact x) := by
  convert (((Interval.point (1/2)).add
    (((Interval.point (1/2)).sub RoleFour.dBox).mul (cosBox x hx))).add
      ((RoleFour.dBox.add (Interval.point (1/2))).mul (sinBox x hx))) using 1
  dsimp [joinContact]

private lemma r87_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r87_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl

private lemma r87_join_eq {x : ℝ} : joinContact x =
    1/2+(1/2-outerDiagonal)*Real.cos x+(outerDiagonal+1/2)*Real.sin x := rfl
private lemma r87_joinBox_lo (x : ℝ) (hx : 0≤x) : (joinBox x hx).lo = (((Interval.point (1/2)).add
    (((Interval.point (1/2)).sub RoleFour.dBox).mul (cosBox x hx))).add
      ((RoleFour.dBox.add (Interval.point (1/2))).mul (sinBox x hx))).lo :=
  r87_mpr_lo r87_join_eq (congrArg _ r87_join_eq) _
private lemma r87_joinBox_hi (x : ℝ) (hx : 0≤x) : (joinBox x hx).hi = (((Interval.point (1/2)).add
    (((Interval.point (1/2)).sub RoleFour.dBox).mul (cosBox x hx))).add
      ((RoleFour.dBox.add (Interval.point (1/2))).mul (sinBox x hx))).hi :=
  r87_mpr_hi r87_join_eq (congrArg _ r87_join_eq) _

lemma join_endpoints : joinContact (2779/5000)<outerDiagonal ∧
    outerDiagonal<joinContact (5559/10000) := by
  have hl := (joinBox (2779/5000) (by norm_num)).mem
  have hu := (joinBox (5559/10000) (by norm_num)).mem
  have hL : (joinBox (2779/5000) (by norm_num)).hi<RoleFour.dBox.lo := by
    norm_num [r87_joinBox_hi,RoleFour.dBox,SecondWord.SameZero.PJ.Reference.sinBox,
      SecondWord.SameZero.PJ.Reference.cosBox,Interval.of_bounds,Interval.point,Interval.add,
      Interval.sub,Interval.neg,Interval.mul,HighOrderTaylor.S17,HighOrderTaylor.S15,
      HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C18,HighOrderTaylor.C16,
      HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8]
  have hU : RoleFour.dBox.hi<(joinBox (5559/10000) (by norm_num)).lo := by
    norm_num [r87_joinBox_lo,RoleFour.dBox,SecondWord.SameZero.PJ.Reference.sinBox,
      SecondWord.SameZero.PJ.Reference.cosBox,Interval.of_bounds,Interval.point,Interval.add,
      Interval.sub,Interval.neg,Interval.mul,HighOrderTaylor.S17,HighOrderTaylor.S15,
      HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C18,HighOrderTaylor.C16,
      HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8]
  exact ⟨hl.2.trans_lt (hL.trans_le RoleFour.dBox.mem.1),
    RoleFour.dBox.mem.2.trans_lt (hU.trans_le hu.1)⟩

theorem exists_event : ∃e,IsEvent e := by
  have hc : Continuous joinContact := by
    have he : joinContact = fun x =>
        1/2+(1/2-outerDiagonal)*Real.cos x+(outerDiagonal+1/2)*Real.sin x := rfl
    rw [he]; fun_prop
  obtain ⟨e,he,heq⟩ := intermediate_value_Icc
    (show (2779/5000:ℝ)≤5559/10000 by norm_num) hc.continuousOn
    (show outerDiagonal∈Icc (joinContact (2779/5000)) (joinContact (5559/10000)) from
      ⟨join_endpoints.1.le,join_endpoints.2.le⟩)
  have hl : (2779/5000:ℝ)<e := lt_of_le_of_ne he.1 (by
    intro hh
    rw [←hh] at heq
    linarith [join_endpoints.1])
  have hu : e<(5559/10000:ℝ) := lt_of_le_of_ne he.2 (by
    intro hh
    rw [hh] at heq
    linarith [join_endpoints.2])
  exact ⟨e,⟨hl,hu⟩,heq⟩

lemma event_angle {e : ℝ} (he : IsEvent e) : e∈Icc 0 (7/10) :=
  ⟨by linarith [he.1.1],by linarith [he.1.2]⟩

lemma diagonal_state : OuterState outerDiagonal outerDiagonal :=
  ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl,by nlinarith [diagonal_circle]⟩

lemma event_height {e : ℝ} (he : IsEvent e) : height e=outerDiagonal := by
  apply SecondWord.NegativeTwo.PrimaryDiagonal.original_height diagonal_state (event_angle he)
  simpa [SecondWord.NegativeTwo.lowerSource,joinContact] using he.2

lemma before_event {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) : Domain x := by
  have hx' : x∈Icc 0 (7/10) := ⟨hx.1,hx.2.trans (event_angle he).2⟩
  have hh := SecondWord.NegativeTwo.PrimaryDiagonal.height_monotone hx' (event_angle he) hx.2
  exact ⟨hx',hh.trans (event_height he).le⟩

lemma bounded_by_event {e x : ℝ} (he : IsEvent e) (hx : Domain x) : x≤e := by
  by_contra! hbad
  have hh := SecondWord.NegativeTwo.PrimaryDiagonal.height_half_monotone
    (event_angle he) hx.1 hbad.le
  have h1 : SecondWord.NegativeTwo.PrimaryDiagonal.height e=outerDiagonal := event_height he
  have h2 : SecondWord.NegativeTwo.PrimaryDiagonal.height x≤outerDiagonal := hx.2
  simp only at hh
  linarith

lemma physical_state {x : ℝ} (hx : Domain x) : OuterState (horizontal x-1/2) (height x) := by
  have hc := SecondWord.NegativeTwo.PrimaryDiagonal.circle hx.1
  have hp := SecondWord.NegativeTwo.PrimaryDiagonal.coordinates_positive hx.1
  have hB := SecondWord.NegativeTwo.PrimaryDiagonal.target_mem hx
  have h2 : vertical x-1/2≤outerDiagonal := hx.2
  have hV : vertical x≤outerDiagonal+1/2 := by linarith
  have hV2 := pow_le_pow_left₀ hp.2.le hV 2
  have horder : vertical x≤horizontal x := by nlinarith [diagonal_circle]
  refine ⟨hB.1,?_,?_⟩
  · change vertical x-1/2≤horizontal x-1/2
    linarith
  · change (horizontal x-1/2+1/2)^2+(vertical x-1/2+1/2)^2=Q0
    nlinarith only [hc]

lemma actual_arc {x : ℝ} (hx : Domain x) : arc (height x)=horizontal x-1/2 :=
  (SameContact.actual_arc (physical_state hx)).1

def cost (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2-x+c r+(p r-q r)*outerDiagonal-P r*(horizontal x-1/2)+t r*(vertical x-1/2)
def first (r : Row) (x : ℝ) : ℝ := -1+(t r*horizontal x+P r*vertical x)*factor x
def second (r : Row) (x : ℝ) : ℝ :=
  (P r*horizontal x-t r*vertical x)*(factor x)^2+
    (t r*horizontal x+P r*vertical x)*factorD x

lemma cost_hasDerivAt (r : Row) {x : ℝ} (hx : Domain x) :
    HasDerivAt (cost r) (first r x) x := by
  convert (((((hasDerivAt_id x).neg).const_add
    (Real.pi/2+c r+(p r-q r)*outerDiagonal)).sub
      (((SecondWord.NegativeTwo.PrimaryDiagonal.horizontal_hasDerivAt hx.1).sub_const
        (1/2)).const_mul (P r))).add
          (((SecondWord.NegativeTwo.PrimaryDiagonal.vertical_hasDerivAt hx.1).sub_const
            (1/2)).const_mul (t r))) using 1
  · funext y
    simp only [cost,horizontal,vertical,Pi.add_apply,Pi.sub_apply,Pi.neg_apply,id_eq]
    ring
  · simp only [first,horizontal,vertical,factor,SecondWord.NegativeTwo.PrimaryDiagonal.speed]
    ring

lemma first_hasDerivAt (r : Row) {x : ℝ} (hx : Domain x) :
    HasDerivAt (first r) (second r x) x := by
  convert ((((SecondWord.NegativeTwo.PrimaryDiagonal.horizontal_hasDerivAt hx.1).const_mul
    (t r)).add ((SecondWord.NegativeTwo.PrimaryDiagonal.vertical_hasDerivAt hx.1).const_mul
      (P r))).mul (SecondWord.NegativeTwo.PrimaryDiagonal.factor_hasDerivAt hx.1)).const_add (-1)
    using 1
  · funext y
    simp only [first,horizontal,vertical,factor,Pi.add_apply,Pi.mul_apply]
  · simp only [second,horizontal,vertical,factor,factorD,Pi.add_apply,
      SecondWord.NegativeTwo.PrimaryDiagonal.speed]
    ring

lemma curvature_negative (r : Row) {x : ℝ} (hx : Domain x) : second r x<0 := by
  have hp := SecondWord.NegativeTwo.PrimaryDiagonal.coordinates_positive hx.1
  have hf := SecondWord.NegativeTwo.PrimaryDiagonal.factor_bounds hx.1
  have hfd := SecondWord.NegativeTwo.PrimaryDiagonal.factorD_negative hx.1
  have hstate := physical_state hx
  have h21 : vertical x-1/2≤horizontal x-1/2 := hstate.2.1
  have horder : vertical x≤horizontal x := by linarith
  have hP : P r≤0 := (coefficient_bounds r).2.2.2.2.1
  have ht : 0<t r := by fin_cases r <;> norm_num [t]
  have hX : P r*horizontal x-t r*vertical x<0 := by
    have h1 := mul_nonpos_of_nonpos_of_nonneg hP (by linarith [hp.1] : 0≤horizontal x)
    have h2 := mul_pos ht hp.2
    linarith
  have hY : 0<t r*horizontal x+P r*vertical x := by
    have h1 := mul_le_mul_of_nonpos_left horder hP
    have h2 := mul_pos (coefficient_bounds r).2.2.2.2.2.1
      (show 0<horizontal x by linarith [hp.1])
    nlinarith
  have hfirst := mul_neg_of_neg_of_pos hX (pow_pos (by linarith [hf.1] : 0<factor x) 2)
  have hsecond := mul_neg_of_pos_of_neg hY hfd
  dsimp only [second]
  linarith

lemma initial_value (r : Row) : cost r 0=aligned r b0 := by
  have hz : height 0=1-outerDiagonal := SecondWord.NegativeTwo.PrimaryDiagonal.height_zero
  have h0 : Domain 0 := by
    refine ⟨by norm_num,?_⟩
    rw [SecondWord.NegativeTwo.PrimaryDiagonal.height_zero]
    simpa [b0] using b0_mem.2
  have harc := actual_arc h0
  rw [hz] at harc
  have hV : vertical 0-1/2=b0 := SecondWord.NegativeTwo.PrimaryDiagonal.height_zero
  have he : 1-b0=outerDiagonal := by dsimp [b0]; ring
  dsimp [cost,aligned,source,target]
  rw [he,SameContact.arc_diagonal,hV,←harc]
  dsimp [b0]
  ring

lemma final_value (r : Row) {e : ℝ} (he : IsEvent e) : (361/400:ℝ)<cost r e := by
  have hed := before_event he (show e∈Icc 0 e from ⟨(event_angle he).1,le_rfl⟩)
  have hA := actual_arc hed
  rw [event_height he,SameContact.arc_diagonal] at hA
  have hB : vertical e-1/2=outerDiagonal := event_height he
  have hp := pi_hand_enclosure.1
  have hd := ShortMixedZero.fine_diagonal_bounds
  dsimp [cost]
  rw [←hA,hB]
  fin_cases r <;> norm_num [c,p,q,P,t] <;> linarith [he.1.2]

theorem cost_lower (r : Row) {x : ℝ} (hx : Domain x) : (8981/10000:ℝ)<cost r x := by
  obtain ⟨e,he⟩ := exists_event
  have hdom := fun y hy => before_event he (show y∈Icc 0 e from hy)
  have hc : ConcaveOn ℝ (Icc 0 e) (cost r) := concave_of_deriv2
    (fun y hy => cost_hasDerivAt r (hdom y hy))
    (fun y hy => first_hasDerivAt r (hdom y hy))
    (fun y hy => (curvature_negative r (hdom y hy)).le)
  apply concave_gt_of_endpoints hc ⟨hx.1.1,bounded_by_event he hx⟩
  · rw [initial_value]
    exact aligned_lower r ⟨b0_mem.1,le_rfl⟩
  · linarith [final_value r he]

theorem original_contact (r : Row) {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hc : 1/2+(1/2-B)*Real.cos x+(A+1/2)*Real.sin x=outerDiagonal) :
    (8981/10000:ℝ)<Real.pi/2-x+c r+(p r-q r)*outerDiagonal-P r*A+t r*B := by
  have hh := SecondWord.NegativeTwo.PrimaryDiagonal.original_height ht hx
    (by simpa [SecondWord.NegativeTwo.lowerSource] using hc)
  have hh' : height x=B := hh
  have hd : Domain x := ⟨hx,by rw [hh]; exact (outer_bounds ht).2.2.2.1⟩
  have hA := actual_arc hd
  rw [hh',(SameContact.actual_arc ht).1] at hA
  have hB : vertical x-1/2=B := hh
  have hb := cost_lower r hd
  dsimp [cost] at hb
  rw [←hA,hB] at hb
  exact hb

end SquaresInCircles.Eight.ShortOuterOne.Same.Diagonal
end
end
end

section
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.SourceDiagonal
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc)
open Diagonal (Z Y horizontal vertical height factor factorD)

abbrev offset := SecondWord.NegativeTwo.PrimaryDiagonal.offset
def numerator (x : ℝ) : ℝ :=
  (1-Q0+offset^2)*Real.cos x+offset*(1+(Real.cos x)^2)
def numeratorD (x : ℝ) : ℝ :=
  (Q0-1-offset^2-2*offset*Real.cos x)*Real.sin x
def factorDD (x : ℝ) : ℝ :=
  numeratorD x/(Y x)^3-3*numerator x*Z x*Real.sin x/(Y x)^5
def speed (x : ℝ) : ℝ := vertical x*factor x
def speedD (x : ℝ) : ℝ := horizontal x*(factor x)^2+vertical x*factorD x
def speedDD (x : ℝ) : ℝ :=
  -vertical x*(factor x)^3+3*horizontal x*factor x*factorD x+vertical x*factorDD x
def cost (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2-x+c r+(t r-P r)*outerDiagonal+p r*(vertical x-1/2)-q r*(horizontal x-1/2)
def first (r : Row) (x : ℝ) : ℝ :=
  -1+q r*speed x+p r*horizontal x*factor x

lemma numerator_identity {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    factorD x*(Y x)^3=numerator x :=
  SecondWord.NegativeTwo.PrimaryDiagonal.factorD_numerator hx

lemma numerator_hasDerivAt (x : ℝ) : HasDerivAt numerator (numeratorD x) x := by
  convert ((Real.hasDerivAt_cos x).const_mul (1-Q0+offset^2)).add
    ((((Real.hasDerivAt_cos x).pow 2).const_add 1).const_mul offset) using 1
  · funext y; simp only [numerator,Pi.add_apply,Pi.pow_apply]
  · simp only [numeratorD]; ring

lemma factorD_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt factorD (factorDD x) x := by
  have hy : 0<Y x := by linarith [(SecondWord.NegativeTwo.PrimaryDiagonal.radical_data hx).2.2.1]
  have hlocal : factorD=ᶠ[𝓝 x] (fun y => numerator y/(Y y)^3) := by
    have hY : Continuous Y := by
      show Continuous (fun y => Real.sqrt (Q0-(Real.cos y+offset)^2))
      fun_prop
    have hO : IsOpen {y : ℝ | 0<Y y} := isOpen_lt continuous_const hY
    filter_upwards [hO.mem_nhds hy] with y hy'
    dsimp [factorD,SecondWord.NegativeTwo.PrimaryDiagonal.factorD,numerator,
      Y,SecondWord.NegativeTwo.PrimaryDiagonal.Y,Z,SecondWord.NegativeTwo.PrimaryDiagonal.Z]
    have hrad : 0≤Q0-(Real.cos y+offset)^2 := by
      have hh : 0<Real.sqrt (Q0-(Real.cos y+offset)^2) := hy'
      exact (Real.sqrt_pos.mp hh).le
    have hs := Real.sq_sqrt hrad
    congr 1
    linear_combination (Real.cos y+offset)*(Real.sin_sq_add_cos_sq y)-Real.cos y*hs
  have hd := (numerator_hasDerivAt x).div
    ((SecondWord.NegativeTwo.PrimaryDiagonal.Y_hasDerivAt hx).pow 3) (pow_ne_zero _ hy.ne')
  have he : HasDerivAt (fun y => numerator y/(Y y)^3) (factorDD x) x := by
    convert hd using 1
    simp only [factorDD,Pi.pow_apply]
    field_simp
    ring
  exact he.congr_of_eventuallyEq hlocal

lemma factorDD_nonnegative {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0≤factorDD x := by
  have ht := positive_trig hx
  have hdata := SecondWord.NegativeTwo.PrimaryDiagonal.radical_data hx
  have ho := SecondWord.NegativeTwo.PrimaryDiagonal.offset_bounds
  have hy : 0<Y x := by linarith [hdata.2.2.1]
  have hN : numerator x<0 := by
    rw [←numerator_identity hx]
    exact mul_neg_of_neg_of_pos
      (SecondWord.NegativeTwo.PrimaryDiagonal.factorD_negative hx) (pow_pos hy 3)
  have hcoef : 0≤Q0-1-offset^2-2*offset*Real.cos x := by
    have hp := mul_nonpos_of_nonpos_of_nonneg (show offset≤0 by linarith [ho.2])
      (show 0≤Real.cos x by linarith [ht.1])
    norm_num [Q0]
    nlinarith
  have hN' : 0≤numeratorD x := mul_nonneg hcoef ht.2.2.1
  have hfirst := div_nonneg hN' (pow_nonneg hy.le 3)
  have hsecond := div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hN] : 3*numerator x≤0) hdata.1.le)
      ht.2.2.1) (pow_nonneg hy.le 5)
  dsimp [factorDD]
  linarith

lemma factorD_monotone : MonotoneOn factorD (Icc 0 (7/10)) := monoOn_of_hasDeriv_nonneg
  (fun _ hx => (factorD_hasDerivAt hx).continuousAt.continuousWithinAt)
  (fun _ hx => factorD_hasDerivAt (Ioo_subset_Icc_self hx))
  (fun _ hx => factorDD_nonnegative (Ioo_subset_Icc_self hx))

lemma speed_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) : HasDerivAt speed (speedD x) x := by
  convert (SecondWord.NegativeTwo.PrimaryDiagonal.vertical_hasDerivAt hx).mul
    (SecondWord.NegativeTwo.PrimaryDiagonal.factor_hasDerivAt hx) using 1
  · funext y; simp only [speed,vertical,factor,Pi.mul_apply]
  · simp only [speedD,horizontal,vertical,factor,factorD,
      SecondWord.NegativeTwo.PrimaryDiagonal.speed]
    ring

lemma speedD_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) : HasDerivAt speedD (speedDD x) x := by
  convert ((SecondWord.NegativeTwo.PrimaryDiagonal.horizontal_hasDerivAt hx).mul
    ((SecondWord.NegativeTwo.PrimaryDiagonal.factor_hasDerivAt hx).pow 2)).add
      ((SecondWord.NegativeTwo.PrimaryDiagonal.vertical_hasDerivAt hx).mul
        (factorD_hasDerivAt hx)) using 1
  · funext y
    simp only [speedD,horizontal,vertical,factor,factorD,Pi.add_apply,Pi.mul_apply,Pi.pow_apply]
  · simp only [speedDD,horizontal,vertical,factor,factorD,Pi.pow_apply,
      SecondWord.NegativeTwo.PrimaryDiagonal.speed]
    ring

lemma event_coordinates {e : ℝ} (he : Diagonal.IsEvent e) :
    horizontal e=outerDiagonal+1/2 ∧ vertical e=outerDiagonal+1/2 := by
  have hB := Diagonal.event_height he
  have hc := SecondWord.NegativeTwo.PrimaryDiagonal.circle (Diagonal.event_angle he)
  have hp := SecondWord.NegativeTwo.PrimaryDiagonal.coordinates_positive (Diagonal.event_angle he)
  change vertical e-1/2=outerDiagonal at hB
  exact ⟨by nlinarith [diagonal_circle,outer_endpoint_bounds.2.2.1],by linarith⟩

lemma cost_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (cost r) (first r x) x := by
  convert (((((hasDerivAt_id x).neg).const_add
    (Real.pi/2+c r+(t r-P r)*outerDiagonal)).add
      (((SecondWord.NegativeTwo.PrimaryDiagonal.vertical_hasDerivAt hx).sub_const
        (1/2)).const_mul (p r))).sub
          (((SecondWord.NegativeTwo.PrimaryDiagonal.horizontal_hasDerivAt hx).sub_const
            (1/2)).const_mul (q r))) using 1
  · funext y
    simp only [cost,horizontal,vertical,Pi.add_apply,Pi.sub_apply,Pi.neg_apply,id_eq]
    ring
  · simp only [first,speed,horizontal,vertical,factor,
      SecondWord.NegativeTwo.PrimaryDiagonal.speed]
    ring

lemma original_coordinates {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (he : 1/2+(1/2-A)*Real.cos x+(1/2+B)*Real.sin x=outerDiagonal) :
    vertical x=A+1/2 ∧ horizontal x=B+1/2 := by
  let T : ℝ := (A+1/2)*Real.sin x+(B+1/2)*Real.cos x
  have htr := positive_trig hx
  have hT : 0<T := by
    have hs := mul_nonneg (show 0≤A+1/2 by linarith [ht.1,ht.2.1]) htr.2.2.1
    have hc := mul_pos (show 0<B+1/2 by linarith [ht.1])
      (show 0<Real.cos x by linarith [htr.1])
    dsimp [T]
    linarith
  have hZ : Z x=(A+1/2)*Real.cos x-(B+1/2)*Real.sin x := by
    dsimp [Z,SecondWord.NegativeTwo.PrimaryDiagonal.Z,offset,
      SecondWord.NegativeTwo.PrimaryDiagonal.offset]
    linarith
  have hcircle : T^2+(Z x)^2=Q0 := by
    rw [hZ]
    dsimp [T]
    linear_combination ht.2.2+((A+1/2)^2+(B+1/2)^2)*(Real.sin_sq_add_cos_sq x)
  have hY : Y x=T := by
    have hd := SecondWord.NegativeTwo.PrimaryDiagonal.radical_data hx
    nlinarith [hd.2.2.1,hd.2.2.2.2]
  constructor
  · show Y x*Real.sin x+Z x*Real.cos x=A+1/2
    rw [hY,hZ]
    dsimp [T]
    linear_combination (A+1/2)*(Real.sin_sq_add_cos_sq x)
  · show Y x*Real.cos x-Z x*Real.sin x=B+1/2
    rw [hY,hZ]
    dsimp [T]
    linear_combination (B+1/2)*(Real.sin_sq_add_cos_sq x)

lemma original_after_event {A B e x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (he : Diagonal.IsEvent e)
    (hc : 1/2+(1/2-A)*Real.cos x+(1/2+B)*Real.sin x=outerDiagonal) : e≤x := by
  have hh := original_coordinates ht hx hc
  have hA := (outer_bounds ht).1
  by_contra! hbad
  have hm := SecondWord.NegativeTwo.PrimaryDiagonal.height_half_monotone hx
    (Diagonal.event_angle he) hbad.le
  have hE : SecondWord.NegativeTwo.PrimaryDiagonal.height e=outerDiagonal :=
    Diagonal.event_height he
  simp only at hm
  rw [hE] at hm
  change vertical x-1/2-x/2≤outerDiagonal-e/2 at hm
  rw [hh.1] at hm
  linarith

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.SourceDiagonal
end
end
end
