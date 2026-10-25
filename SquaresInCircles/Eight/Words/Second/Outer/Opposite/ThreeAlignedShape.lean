module

public import SquaresInCircles.Eight.Words.Second.Outer.LBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeReferenceAlgebra

/-!
# Eight squares: whole-domain curvature of both aligned opposite contacts

The first contact has decreasing second derivative on its entire arc.
The reverse contact uses a single uniformly convex auxiliary coefficient
and the exact circle relation for its slope.  All estimates hold through
the closed zero-coordinate and primary-one endpoints.
-/

section
/-!
## Individual references for the two aligned opposite contacts

These are substitutions at the two named aligned reference points, the
actual primary-one endpoint, and the one reference for the auxiliary
curvature coefficient.  All radicals use their own circle equations.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.Aligned
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open StationaryPrimitives (Interval)
open ReferenceAlgebra

private lemma r36_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r36_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl

private lemma r36_shifted_eq {y : ℝ} : U y = Real.sqrt (Q0-(y+1/2)^2) := by dsimp [U,arc]; ring
private lemma r36_shifted_lo {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).lo = (rootThree (radicand Y) s hs hr).lo :=
  r36_mpr_lo r36_shifted_eq (congrArg _ r36_shifted_eq) _
private lemma r36_shifted_hi {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).hi = (rootThree (radicand Y) s hs hr).hi :=
  r36_mpr_hi r36_shifted_eq (congrArg _ r36_shifted_eq) _

private lemma r36_coordinate_eq {y : ℝ} : arc y = U y-1/2 := by dsimp [U]; ring
private lemma r36_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r36_mpr_lo r36_coordinate_eq (congrArg _ r36_coordinate_eq) _
private lemma r36_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r36_mpr_hi r36_coordinate_eq (congrArg _ r36_coordinate_eq) _

private lemma r36_jBox_eq {y : ℝ} : j y = U y-3/2 := by dsimp [j,U]; ring
private lemma r36_jBox_lo {y : ℝ} (X : Interval (U y)) :
    (jBox X).lo = (X.sub (Interval.point (3/2))).lo :=
  r36_mpr_lo r36_jBox_eq (congrArg _ r36_jBox_eq) _
private lemma r36_jBox_hi {y : ℝ} (X : Interval (U y)) :
    (jBox X).hi = (X.sub (Interval.point (3/2))).hi :=
  r36_mpr_hi r36_jBox_eq (congrArg _ r36_jBox_eq) _

private lemma r36_label_eq (H : RoleLabel) {y : ℝ} :
    H.outer y = H.c+H.p*(arc y)+H.q*y+H.r*y^2+H.s*(arc y*y) := by
  dsimp [RoleLabel.outer,RoleLabel.eval]; ring
private lemma r36_labelBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).lo = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).lo :=
  r36_mpr_lo (r36_label_eq H) (congrArg _ (r36_label_eq H)) _
private lemma r36_labelBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).hi = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).hi :=
  r36_mpr_hi (r36_label_eq H) (congrArg _ (r36_label_eq H)) _

private lemma r36_ratioDD_eq {y : ℝ} : ratioDD y = 3*Q0*(y+1/2)/((U y)^3*(U y)^2) := by
  dsimp [ratioDD,U]; ring
private lemma r36_ratioDDBox_lo {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDDBox Y X hX).lo = (((Interval.point (3*Q0)).mul (Y.add (Interval.point (1/2)))).div
      (X.cube.mul X.square)
      (Interval.mul_lo_pos (Interval.cube_lo_pos hX) (Interval.square_lo_pos hX))).lo :=
  r36_mpr_lo r36_ratioDD_eq (congrArg _ r36_ratioDD_eq) _
private lemma r36_ratioDDBox_hi {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDDBox Y X hX).hi = (((Interval.point (3*Q0)).mul (Y.add (Interval.point (1/2)))).div
      (X.cube.mul X.square)
      (Interval.mul_lo_pos (Interval.cube_lo_pos hX) (Interval.square_lo_pos hX))).hi :=
  r36_mpr_hi r36_ratioDD_eq (congrArg _ r36_ratioDD_eq) _

local macro "opposite_reference" : tactic => `(tactic|
  norm_num [alignedBox,alignedFirstBox,alignedSecondBox,r36_labelBox_lo,r36_labelBox_hi,
    firstBox,secondBox,thirdBox,ratioBox,ratioDBox,r36_ratioDDBox_lo,r36_ratioDDBox_hi,
    r36_coordinate_lo,r36_coordinate_hi,r36_jBox_lo,r36_jBox_hi,r36_shifted_lo,r36_shifted_hi,
    radicand,rootThree,rootStep,
    piBox,inner,outer,TLabel,LLabel,Q0,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.inv,Interval.div])
def reference (reverse : Bool) : ℝ :=
  if reverse then 11941893/20000000 else 137071377/200000000
def referenceBox (reverse : Bool) : Interval (reference reverse) := Interval.point _
def referenceU (reverse : Bool) : Interval (U (reference reverse)) :=
  shifted (referenceBox reverse) (if reverse then 17/10 else 8/5)
    (by cases reverse <;> norm_num)
    (by cases reverse <;> norm_num [referenceBox,reference,radicand,
      Interval.point,Interval.add,Interval.sub,Interval.square,Interval.mul,Q0])
def referenceJ (reverse : Bool) : Interval (U (j (reference reverse))) :=
  shifted (jBox (referenceU reverse)) (19/10) (by norm_num)
    (by cases reverse <;> dsimp [referenceU,referenceBox,reference] <;> opposite_reference)

lemma reference_mem (reverse : Bool) : reference reverse∈Icc 0 bOne := by
  have hb := OppositeTwo.bOne_bounds.1
  cases reverse <;> norm_num [reference] <;> linarith

lemma referenceU_positive (reverse : Bool) : 0<(referenceU reverse).lo := by
  cases reverse <;> dsimp [referenceU,referenceBox,reference] <;> opposite_reference
lemma referenceJ_positive (reverse : Bool) : 0<(referenceJ reverse).lo := by
  cases reverse <;> dsimp [referenceJ,referenceU,referenceBox,reference] <;> opposite_reference

lemma forward_reference_value : (898079/1000000:ℝ)<cost false (reference false) := by
  let Z := alignedBox false (referenceBox false) (referenceU false) (referenceJ false)
  have hh : (898079/1000000:ℝ)<Z.lo := by
    dsimp [Z,referenceJ,referenceU,referenceBox,reference]
    opposite_reference
  exact hh.trans_le Z.mem.1

lemma reverse_reference_value : (4488901/5000000:ℝ)<cost true (reference true) := by
  let Z := alignedBox true (referenceBox true) (referenceU true) (referenceJ true)
  have hh : (4488901/5000000:ℝ)<Z.lo := by
    dsimp [Z,referenceJ,referenceU,referenceBox,reference]
    opposite_reference
  exact hh.trans_le Z.mem.1

lemma reference_first (reverse : Bool) : |first reverse (reference reverse)|<1/1000000 := by
  let Z := alignedFirstBox reverse (referenceBox reverse) (referenceU reverse) (referenceJ reverse)
    (referenceU_positive reverse) (referenceJ_positive reverse)
  have hb : -(1/1000000:ℝ)<Z.lo ∧ Z.hi<(1/1000000:ℝ) := by
    cases reverse <;> dsimp [Z,referenceJ,referenceU,referenceBox,reference] <;> opposite_reference
  exact abs_lt.mpr ⟨hb.1.trans_le Z.mem.1,Z.mem.2.trans_lt hb.2⟩

def endpointBox : Interval bOne :=
  Interval.of_bounds ⟨OppositeTwo.bOne_bounds.1.le,OppositeTwo.bOne_bounds.2.le⟩
def endpointU : Interval (U bOne) := by
  have he : U bOne=(3/2:ℝ) := by dsimp [U]; rw [OppositeTwo.bOne_arc]; norm_num
  rw [he]
  exact Interval.point _
private lemma r36_endpoint_eq : U bOne=(3/2:ℝ) := by
  dsimp [U]; rw [OppositeTwo.bOne_arc]; norm_num
private lemma r36_endpointU_lo : endpointU.lo = 3/2 :=
  r36_mpr_lo r36_endpoint_eq (congrArg _ r36_endpoint_eq) (Interval.point (3/2:ℝ))
private lemma r36_endpointU_hi : endpointU.hi = 3/2 :=
  r36_mpr_hi r36_endpoint_eq (congrArg _ r36_endpoint_eq) (Interval.point (3/2:ℝ))

local macro "endpoint_reference" : tactic => `(tactic|
  norm_num [r36_endpointU_lo,r36_endpointU_hi,alignedBox,alignedFirstBox,alignedSecondBox,r36_labelBox_lo,r36_labelBox_hi,
    firstBox,secondBox,thirdBox,ratioBox,ratioDBox,r36_ratioDDBox_lo,r36_ratioDDBox_hi,
    r36_coordinate_lo,r36_coordinate_hi,r36_jBox_lo,r36_jBox_hi,r36_shifted_lo,r36_shifted_hi,
    radicand,rootThree,rootStep,
    piBox,inner,outer,TLabel,LLabel,Q0,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.inv,Interval.div])

def endpointJ : Interval (U (j bOne)) :=
  shifted (jBox endpointU) (19/10) (by norm_num)
    (by endpoint_reference)

lemma forward_endpoint_curvature : (11/50:ℝ)<second false bOne := by
  let Z := alignedSecondBox false endpointBox endpointU endpointJ
    (by endpoint_reference)
    (by dsimp [endpointJ]; endpoint_reference)
  have hh : (11/50:ℝ)<Z.lo := by
    dsimp [Z,endpointBox,endpointJ]
    endpoint_reference
  exact hh.trans_le Z.mem.1

def coefficient (y : ℝ) : ℝ := LLabel.d1 (j y)-(95769/100000)*y
def coefficientFirst (y : ℝ) : ℝ := -LLabel.d2 (j y)*ratio y-95769/100000
def coefficientSecond (y : ℝ) : ℝ :=
  LLabel.d3 (j y)*(ratio y)^2-LLabel.d2 (j y)*ratioD y

def coefficientU : Interval (U (5781/10000)) :=
  shifted (Interval.point (5781/10000)) (17/10) (by norm_num) (by opposite_reference)
def coefficientJ : Interval (U (j (5781/10000))) :=
  shifted (jBox coefficientU) (19/10) (by norm_num)
    (by dsimp [coefficientU]; opposite_reference)

lemma coefficient_reference :
    (343739/1000000:ℝ)<coefficient (5781/10000) ∧
      |coefficientFirst (5781/10000)|<1/10000 := by
  have hU : 0<coefficientU.lo := by dsimp [coefficientU]; opposite_reference
  have hJ : 0<coefficientJ.lo := by dsimp [coefficientJ,coefficientU]; opposite_reference
  let V := (firstBox LLabel (jBox coefficientU) coefficientJ hJ).sub
    (Interval.point ((95769/100000)*(5781/10000)))
  let D := (((secondBox LLabel (jBox coefficientU) coefficientJ hJ).neg).mul
    (ratioBox (Interval.point (5781/10000)) coefficientU hU)).sub
      (Interval.point (95769/100000))
  have hb : (343739/1000000:ℝ)<V.lo ∧ -(1/10000:ℝ)<D.lo ∧ D.hi<(1/10000:ℝ) := by
    dsimp [V,D,coefficientJ,coefficientU]; opposite_reference
  exact ⟨hb.1.trans_le V.mem.1,abs_lt.mpr ⟨hb.2.1.trans_le D.mem.1,D.mem.2.trans_lt hb.2.2⟩⟩

def zeroU : Interval (U 0) :=
  shifted (Interval.point 0) (19/10) (by norm_num) (by opposite_reference)
def shortU : Interval (U (83/200)) :=
  shifted (Interval.point (83/200)) (9/5) (by norm_num) (by opposite_reference)
def innerEndU : Interval (U (2073/5000)) :=
  shifted (Interval.point (2073/5000)) (9/5) (by norm_num) (by opposite_reference)

lemma T_zero_second : -(267/200:ℝ)<TLabel.d2 0 := by
  let Z := secondBox TLabel (Interval.point 0) zeroU (by dsimp [zeroU]; opposite_reference)
  have hh : -(267/200:ℝ)<Z.lo := by dsimp [Z,zeroU]; opposite_reference
  exact hh.trans_le Z.mem.1

lemma T_short_third : TLabel.d3 (83/200)<117/50 := by
  let Z := thirdBox TLabel (Interval.point (83/200)) shortU
    (by dsimp [shortU]; opposite_reference)
  have hh : Z.hi<(117/50:ℝ) := by dsimp [Z,shortU]; opposite_reference
  exact Z.mem.2.trans_lt hh

lemma L_inner_end_second : LLabel.d2 (2073/5000)< -(9/20:ℝ) := by
  let Z := secondBox LLabel (Interval.point (2073/5000)) innerEndU
    (by dsimp [innerEndU]; opposite_reference)
  have hh : Z.hi< -(9/20:ℝ) := by dsimp [Z,innerEndU]; opposite_reference
  exact Z.mem.2.trans_lt hh

lemma L_zero_third : (317/100:ℝ)<LLabel.d3 0 := by
  let Z := thirdBox LLabel (Interval.point 0) zeroU (by dsimp [zeroU]; opposite_reference)
  have hh : (317/100:ℝ)<Z.lo := by dsimp [Z,zeroU]; opposite_reference
  exact hh.trans_le Z.mem.1

lemma L_half_first_sharp : (62481/100000:ℝ)<LLabel.d1 (1/2) := by
  let X := shifted (Interval.point (1/2)) (17/10) (by norm_num) (by opposite_reference)
  let Z := firstBox LLabel (Interval.point (1/2)) X (by dsimp [X]; opposite_reference)
  have hh : (62481/100000:ℝ)<Z.lo := by dsimp [Z,X]; opposite_reference
  exact hh.trans_le Z.mem.1

end SquaresInCircles.Eight.SecondWord.OppositeThree.Aligned
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.Aligned
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

lemma T_second_lower {y : ℝ} (hy : y∈Icc 0 outerDiagonal) :
    -(267/200:ℝ)<TLabel.d2 y :=
  T_zero_second.trans_le (T_second_monotone outer_zero_mem hy hy.1)

lemma T_inner_third {y : ℝ} (hy : y∈Icc 0 bOne) : TLabel.d3 (j y)<117/50 := by
  have he : (83/200:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  exact (T_third_monotone (j_mem hy) he (by linarith [(j_bounds hy).2])).trans_lt T_short_third

lemma L_inner_second {y : ℝ} (hy : y∈Icc 0 bOne) : LLabel.d2 (j y)< -(9/20:ℝ) := by
  have he : (2073/5000:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  exact (L_second_monotone (j_mem hy) he (j_bounds hy).2.le).trans_lt L_inner_end_second

lemma L_third_lower {y : ℝ} (hy : y∈Icc 0 outerDiagonal) : (317/100:ℝ)<LLabel.d3 y :=
  L_zero_third.trans_le (L_third_monotone outer_zero_mem hy hy.1)

lemma forward_third_negative {y : ℝ} (hy : y∈Icc 0 bOne) : third false y<0 := by
  have hdom := mem_outer hy
  have hj := j_mem hy
  have hu := U_positive (outer_domain hdom)
  have hw : 0<W y := by dsimp [W]; linarith [hy.1]
  have hub := (UW_bounds hdom).2.1
  have hwb := (coordinates hy).2.1
  have hcircle := UW_circle (outer_domain hdom)
  have hUW : U y*W y≤Q0/2 := by nlinarith [sq_nonneg (U y-W y)]
  have hM : (U y)^2*(W y)^3≤(383/200:ℝ)^2*(1291/1000)^3 :=
    mul_le_mul (pow_le_pow_left₀ hu.le hub.le 2)
      (pow_le_pow_left₀ hw.le hwb.le 3) (pow_nonneg hw.le 3) (by norm_num)
  have h1 := mul_le_mul (T_inner_third hy).le hM
    (mul_nonneg (sq_nonneg _) (pow_nonneg hw.le 3)) (by norm_num : (0:ℝ)≤117/50)
  have h2 := mul_le_mul
    (show -TLabel.d2 (j y)≤(267/200:ℝ) by linarith [T_second_lower hj]) hUW
    (mul_nonneg hu.le hw.le) (by norm_num : (0:ℝ)≤267/200)
  have h3 := mul_le_mul (T_first_upper hj).le hwb.le hw.le
    (by norm_num : (0:ℝ)≤1069/1000)
  have hscalar : (third false y+LLabel.d3 y)*(U y)^5=
      TLabel.d3 (j y)*(U y)^2*(W y)^3-
        3*TLabel.d2 (j y)*Q0*U y*W y+3*TLabel.d1 (j y)*Q0*W y := by
    have hr : ratio y=W y/U y := rfl
    have hD : ratioD y=Q0/(U y)^3 := rfl
    have hDD : ratioDD y=3*Q0*W y/(U y)^5 := rfl
    simp only [third,inner,outer,Bool.false_eq_true,↓reduceIte,hr,hD,hDD]
    field_simp
    ring
  have hlast := LLabel.third_numerator (outer_domain hdom)
  norm_num [LLabel,Q0] at hlast hscalar hUW h2
  have hp := pow_pos hu 5
  have hneg : third false y*(U y)^5<0 := by linarith
  exact neg_of_mul_neg_left hneg hp.le

lemma forward_second_antitone : AntitoneOn (second false) (Icc 0 bOne) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hy => (second_hasDerivAt false hy).continuousAt.continuousWithinAt)
    (fun _ hy => second_hasDerivAt false (Ioo_subset_Icc_self hy))
    (fun _ hy => (forward_third_negative (Ioo_subset_Icc_self hy)).le)

lemma forward_curvature {y : ℝ} (hy : y∈Icc 0 bOne) : (11/50:ℝ)<second false y :=
  forward_endpoint_curvature.trans_le
    (forward_second_antitone hy ⟨OppositeTwo.bOne_mem.1,le_rfl⟩ hy.2)

lemma coefficient_hasDerivAt {y : ℝ} (hy : y∈Icc 0 bOne) :
    HasDerivAt coefficient (coefficientFirst y) y := by
  have hd := ((LLabel.d1_hasDerivAt (outer_domain (j_mem hy))).comp y
    (j_hasDerivAt hy)).fun_sub ((hasDerivAt_id' y).const_mul (95769/100000))
  exact hd.congr_deriv (by dsimp [coefficientFirst]; ring)

lemma coefficientFirst_hasDerivAt {y : ℝ} (hy : y∈Icc 0 bOne) :
    HasDerivAt coefficientFirst (coefficientSecond y) y := by
  have hi := (LLabel.d2_hasDerivAt (outer_domain (j_mem hy))).comp y (j_hasDerivAt hy)
  have hr := ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain (mem_outer hy))
  exact ((hi.fun_neg.fun_mul hr).sub_const (95769/100000)).congr_deriv
    (by simp only [Function.comp_apply,coefficientSecond]; ring)

lemma coefficient_curvature {y : ℝ} (hy : y∈Icc 0 bOne) : (1/4:ℝ)<coefficientSecond y := by
  have hp := mul_nonneg (L_third_positive (j_mem hy)).le (sq_nonneg (ratio y))
  have hD := outer_ratioD_lower (mem_outer hy)
  have hl := L_inner_second hy
  have hm := mul_lt_mul''
    (show (9/20:ℝ)< -LLabel.d2 (j y) by linarith) hD
    (by norm_num : (0:ℝ)≤9/20) (by norm_num : (0:ℝ)≤557/1000)
  dsimp [coefficientSecond]
  linarith

lemma coefficient_lower {y : ℝ} (hy : y∈Icc 0 bOne) : (17/50:ℝ)<coefficient y := by
  have href : (5781/10000:ℝ)∈Icc 0 bOne :=
    ⟨by norm_num,by linarith [OppositeTwo.bOne_bounds.1]⟩
  have ht := curvature_tangent (f := coefficient) (d := coefficientFirst)
    (dd := coefficientSecond) (κ := (1/4:ℝ)) hy href
    (fun t ht => coefficient_hasDerivAt ht)
    (fun t ht => coefficientFirst_hasDerivAt ht)
    (fun t ht => (coefficient_curvature ht).le)
  have hd := abs_lt.mp coefficient_reference.2
  have hs : (coefficientFirst (5781/10000))^2<(1/10000:ℝ)^2 := by nlinarith
  have hp := sq_nonneg ((y-5781/10000)/4+coefficientFirst (5781/10000))
  nlinarith [coefficient_reference.1]

lemma ratioD_quadratic_lower {y : ℝ} (hy : y∈Icc 0 outerDiagonal) :
    (1/2:ℝ)+(3/4)*(ratio y)^2<ratioD y := by
  have hu := U_positive (outer_domain hy)
  have hh := (UW_bounds hy).2.1
  have hc := UW_circle (outer_domain hy)
  have hs : (U y)^2≤(383/200:ℝ)^2 := pow_le_pow_left₀ hu.le hh.le 2
  have hb : 0≤3*Q0-(U y)^2-(383/200)*U y-(383/200)^2 := by
    norm_num [Q0]
    nlinarith
  have hp := mul_nonneg (show 0≤(383/200:ℝ)-U y by linarith) hb
  have hf : 0<Q0+(U y)^3/4-(3/4)*Q0*U y := by
    norm_num [Q0] at hp ⊢
    nlinarith
  have he : (ratioD y-1/2-(3/4)*(ratio y)^2)*(U y)^3=
      Q0+(U y)^3/4-(3/4)*Q0*U y := by
    dsimp [ratioD,ratio]
    change (Q0/(U y)^3-1/2-(3/4)*(W y/U y)^2)*(U y)^3=_
    field_simp [hu.ne']
    nlinarith [hc]
  have hp3 := pow_pos hu 3
  nlinarith

lemma reverse_curvature {y : ℝ} (hy : y∈Icc 0 bOne) : (87/100:ℝ)<second true y := by
  have hdom := mem_outer hy
  have hr := outer_ratio_bounds hdom
  have hrhi := (coordinates hy).2.2
  have hD := ratioD_quadratic_lower hdom
  have hA := coefficient_lower hy
  have hL := L_inner_second hy
  have hprod := mul_lt_mul'' hA hD
    (by norm_num : (0:ℝ)≤17/50) (by positivity : (0:ℝ)≤1/2+(3/4)*(ratio y)^2)
  have hsq := mul_nonneg
    (show 0≤-LLabel.d2 (j y)-9/20 by linarith) (sq_nonneg (ratio y))
  have he : second true y=91744/50000-(95769/50000)*ratio y-
      LLabel.d2 (j y)*(ratio y)^2+coefficient y*ratioD y := by
    simp only [second,inner,outer,coefficient,RoleLabel.d2,TLabel,↓reduceIte]
    ring
  have hpoly := mul_nonneg
    (show 0≤(861/1000:ℝ)-ratio y by linarith)
    (show 0≤95769/50000-(141/200)*(ratio y+861/1000) by linarith)
  rw [he]
  nlinarith

end SquaresInCircles.Eight.SecondWord.OppositeThree.Aligned
end
end
end
