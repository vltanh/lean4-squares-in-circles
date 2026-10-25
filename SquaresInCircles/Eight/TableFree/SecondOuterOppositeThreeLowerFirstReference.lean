module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerFirstCurvature

/-!
# The one interior reference for the first lower-secondary minimum

The value uses a direct trigonometric comparison with the exact
inverse phase.  The two derivatives and label values are exact radical
enclosures at this one rational point.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerFirst
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open LowerContact LowerGeometry LowerInverse
open StationaryPrimitives (Interval)
open ReferenceAlgebra LowerAlgebra

def referenceFree : ℝ := 1469521/25000000
def referenceOuter : ℝ := 16700143/50000000
def referenceAngle : ℝ := 127303/500000

lemma reference_free_mem : referenceFree∈Icc 0 (1/10) := by norm_num [referenceFree]
lemma reference_outer_mem : referenceOuter∈Icc 0 (2/5) := by norm_num [referenceOuter]

private lemma r82_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r82_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl

private lemma r82_shifted_eq {y : ℝ} : U y = Real.sqrt (Q0-(y+1/2)^2) := by dsimp [U,arc]; ring
private lemma r82_shifted_lo {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).lo = (rootThree (radicand Y) s hs hr).lo :=
  r82_mpr_lo r82_shifted_eq (congrArg _ r82_shifted_eq) _
private lemma r82_shifted_hi {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).hi = (rootThree (radicand Y) s hs hr).hi :=
  r82_mpr_hi r82_shifted_eq (congrArg _ r82_shifted_eq) _

private lemma r82_coordinate_eq {y : ℝ} : arc y = U y-1/2 := by dsimp [U]; ring
private lemma r82_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r82_mpr_lo r82_coordinate_eq (congrArg _ r82_coordinate_eq) _
private lemma r82_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r82_mpr_hi r82_coordinate_eq (congrArg _ r82_coordinate_eq) _

private lemma r82_label_eq (H : RoleLabel) {y : ℝ} :
    H.outer y = H.c+H.p*(arc y)+H.q*y+H.r*y^2+H.s*(arc y*y) := by
  dsimp [RoleLabel.outer,RoleLabel.eval]; ring
private lemma r82_labelBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).lo = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).lo :=
  r82_mpr_lo (r82_label_eq H) (congrArg _ (r82_label_eq H)) _
private lemma r82_labelBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).hi = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).hi :=
  r82_mpr_hi (r82_label_eq H) (congrArg _ (r82_label_eq H)) _

local macro "lower_reference" : tactic => `(tactic|
  norm_num [freeFirstBox,outerFirstBox,inverseFirstBox,qBox,factorBox,speedBox,
    r82_labelBox_lo,r82_labelBox_hi,firstBox,ratioBox,r82_coordinate_lo,r82_coordinate_hi,
    r82_shifted_lo,r82_shifted_hi,radicand,rootThree,rootStep,
    LowerContact.inner,LowerContact.outer,TLabel,LLabel,Q0,
    referenceFree,referenceOuter,referenceAngle,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.inv,Interval.div])

def referenceFreeU : Interval (U referenceFree) :=
  shifted (Interval.point referenceFree) (19/10) (by norm_num) (by lower_reference)
def referenceOuterU : Interval (U referenceOuter) :=
  shifted (Interval.point referenceOuter) (9/5) (by norm_num) (by lower_reference)
def referenceSpeed : Interval (speed (referenceFree+1/2) referenceOuter) :=
  speedBox (Interval.point (referenceFree+1/2)) (qBox referenceOuterU) 1 (by norm_num)
    (by dsimp [referenceOuterU]; lower_reference)

lemma reference_gradient :
    |freeFirst false referenceFree referenceOuter|<(1/1000000:ℝ) ∧
      |outerFirst false referenceFree referenceOuter|<(1/1000000:ℝ) := by
  have hu : 0<referenceFreeU.lo := by dsimp [referenceFreeU]; lower_reference
  have hU : 0<referenceOuterU.lo := by dsimp [referenceOuterU]; lower_reference
  have hq : 0<(qBox referenceOuterU).lo := by dsimp [referenceOuterU]; lower_reference
  have hv : 0<referenceSpeed.lo := by dsimp [referenceSpeed,referenceOuterU]; lower_reference
  let D := freeFirstBox false (Interval.point referenceFree) referenceFreeU referenceSpeed hu hv
  let E := outerFirstBox false (Interval.point (referenceFree+1/2))
    (Interval.point referenceOuter) referenceOuterU referenceSpeed hU hq hv
  have hdlo : -(1/1000000:ℝ)<D.lo := by
    dsimp [D,referenceSpeed,referenceFreeU,referenceOuterU]; lower_reference
  have hdhi : D.hi<(1/1000000:ℝ) := by
    dsimp [D,referenceSpeed,referenceFreeU,referenceOuterU]; lower_reference
  have helo : -(1/1000000:ℝ)<E.lo := by
    dsimp [E,referenceSpeed,referenceOuterU]; lower_reference
  have hehi : E.hi<(1/1000000:ℝ) := by
    dsimp [E,referenceSpeed,referenceOuterU]; lower_reference
  exact ⟨abs_lt.mpr ⟨hdlo.trans_le D.mem.1,D.mem.2.trans_lt hdhi⟩,
    abs_lt.mpr ⟨helo.trans_le E.mem.1,E.mem.2.trans_lt hehi⟩⟩

lemma reference_labels :
    T referenceFree<(7725599/100000000:ℝ) ∧
      L referenceOuter<(1364633/4000000:ℝ) := by
  let D := labelBox TLabel (Interval.point referenceFree) referenceFreeU
  let E := labelBox LLabel (Interval.point referenceOuter) referenceOuterU
  have hd : D.hi<(7725599/100000000:ℝ) := by dsimp [D,referenceFreeU]; lower_reference
  have he : E.hi<(1364633/4000000:ℝ) := by dsimp [E,referenceOuterU]; lower_reference
  exact ⟨D.mem.2.trans_lt hd,E.mem.2.trans_lt he⟩

lemma reference_contact_after :
    (arc referenceOuter-1/2)*Real.cos referenceAngle-
      (referenceOuter+1/2)*Real.sin referenceAngle≤referenceFree+1/2 := by
  have hx : referenceAngle∈Icc 0 (7/10) := by norm_num [referenceAngle]
  have htrig := positive_trig hx
  have hc := cos_le_cos8 hx.1
  have hs := (trig_taylor_bounds hx.1).1
  have hu : U referenceOuter<(8972234/5000000:ℝ) := by
    have hh : referenceOuterU.hi<(8972234/5000000:ℝ) := by
      dsimp [referenceOuterU]; lower_reference
    exact referenceOuterU.mem.2.trans_lt hh
  have hup : 0≤arc referenceOuter-1/2 := by
    have h := (early_U reference_outer_mem).1
    dsimp [U] at h
    linarith
  have hup' : arc referenceOuter-1/2≤(3972234/5000000:ℝ) := by
    dsimp [U] at hu
    linarith
  have hcos := mul_le_mul hup' hc (by linarith [htrig.1]) (by norm_num)
  have hsin := mul_le_mul_of_nonneg_left hs
    (by norm_num [referenceOuter] : 0≤referenceOuter+1/2)
  norm_num [referenceAngle,referenceOuter,referenceFree,sin7,cos8] at hcos hsin ⊢
  linarith

lemma reference_value : (35911/40000:ℝ)<LowerContact.cost false referenceFree referenceOuter := by
  have hb : referenceFree∈Icc 0 (83/200) :=
    ⟨reference_free_mem.1,by linarith [reference_free_mem.2]⟩
  have hB := full_domain ⟨reference_outer_mem.1,by linarith [reference_outer_mem.2]⟩
  have hphase := phase_lower hB (short_shift hb)
    (show referenceAngle∈Icc 0 (7/10) by norm_num [referenceAngle]) reference_contact_after
  have hT := reference_labels.1
  have hL := reference_labels.2
  dsimp [LowerContact.cost,LowerContact.inner,LowerContact.outer,T,L] at *
  norm_num [referenceAngle] at hphase
  linarith [pi_hand_enclosure.1]

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerFirst
