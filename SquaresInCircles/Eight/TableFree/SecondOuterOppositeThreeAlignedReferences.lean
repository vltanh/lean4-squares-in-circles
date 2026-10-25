module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeReferenceAlgebra

/-!
# Individual references for the two aligned opposite contacts

These are substitutions at the two named aligned reference points, the
actual primary-one endpoint, and the one reference for the auxiliary
curvature coefficient.  All radicals use their own circle equations.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.Aligned
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

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.Aligned
