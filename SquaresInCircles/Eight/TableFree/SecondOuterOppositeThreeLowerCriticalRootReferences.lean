module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerCriticalExit

/-!
# The two named scalar critical roots

The selector distinguishes only the two individual references `.495`
and `.5`.  Each root is located by exact endpoint comparisons in the
strictly increasing scalar equation, not by a cover of source states.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerCritical
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open ReferenceAlgebra LowerAlgebra LowerEnvelope

def probeSource (late : Bool) : ℝ := if late then 1/2 else 99/200
def probeLo (late : Bool) : ℝ :=
  if late then 12539102082/100000000000 else 12421535815/100000000000
def probeHi (late : Bool) : ℝ :=
  if late then 12539102083/100000000000 else 12421535816/100000000000
def probePoint (late : Bool) : ℝ := if late then halfPoint else referencePoint

/-! Endpoint equations for each enclosure: evaluating by rewriting instead of unfolding the
definitions, which carry their membership proofs. -/
private lemma r95_mul_lo {x y : ℝ} (X : Interval x) (Y : Interval y) :
    (X.mul Y).lo = min (min (X.lo*Y.lo) (X.lo*Y.hi)) (min (X.hi*Y.lo) (X.hi*Y.hi)) := rfl
private lemma r95_mul_hi {x y : ℝ} (X : Interval x) (Y : Interval y) :
    (X.mul Y).hi = max (max (X.lo*Y.lo) (X.lo*Y.hi)) (max (X.hi*Y.lo) (X.hi*Y.hi)) := rfl
private lemma r95_inv_lo {x : ℝ} (X : Interval x) (h : 0<X.lo) : (X.inv h).lo = 1/X.hi := rfl
private lemma r95_inv_hi {x : ℝ} (X : Interval x) (h : 0<X.lo) : (X.inv h).hi = 1/X.lo := rfl
private lemma r95_add_lo {x y : ℝ} (X : Interval x) (Y : Interval y) : (X.add Y).lo = X.lo+Y.lo := rfl
private lemma r95_add_hi {x y : ℝ} (X : Interval x) (Y : Interval y) : (X.add Y).hi = X.hi+Y.hi := rfl
private lemma r95_sub_lo {x y : ℝ} (X : Interval x) (Y : Interval y) : (X.sub Y).lo = X.lo-Y.hi := rfl
private lemma r95_sub_hi {x y : ℝ} (X : Interval x) (Y : Interval y) : (X.sub Y).hi = X.hi-Y.lo := rfl
private lemma r95_neg_lo {x : ℝ} (X : Interval x) : X.neg.lo = -X.hi := rfl
private lemma r95_neg_hi {x : ℝ} (X : Interval x) : X.neg.hi = -X.lo := rfl
private lemma r95_point_lo (x : ℝ) : (Interval.point x).lo = x := rfl
private lemma r95_point_hi (x : ℝ) : (Interval.point x).hi = x := rfl
private lemma r95_of_bounds_lo {x a b : ℝ} (h : x∈Set.Icc a b) : (Interval.of_bounds h).lo = a := rfl
private lemma r95_of_bounds_hi {x a b : ℝ} (h : x∈Set.Icc a b) : (Interval.of_bounds h).hi = b := rfl
private lemma r95_rootStep_lo {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    (rootStep X s hs hX).lo = X.lo/((s+X.hi/s)/2) := rfl
private lemma r95_rootStep_hi {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    (rootStep X s hs hX).hi = (s+X.hi/s)/2 := rfl
private lemma r95_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r95_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl
private lemma r95_square_lo {x : ℝ} (X : Interval x) :
    (X.square).lo = (X.mul X).lo := rfl
private lemma r95_square_hi {x : ℝ} (X : Interval x) :
    (X.square).hi = (X.mul X).hi := rfl
private lemma r95_cube_lo {x : ℝ} (X : Interval x) :
    (X.cube).lo = (X.square.mul X).lo := rfl
private lemma r95_cube_hi {x : ℝ} (X : Interval x) :
    (X.cube).hi = (X.square.mul X).hi := rfl
private lemma r95_div_lo {x y : ℝ} (X : Interval x) (Y : Interval y) (h : 0<Y.lo) :
    (X.div Y h).lo = (X.mul (Y.inv h)).lo := rfl
private lemma r95_div_hi {x y : ℝ} (X : Interval x) (Y : Interval y) (h : 0<Y.lo) :
    (X.div Y h).hi = (X.mul (Y.inv h)).hi := rfl
private lemma r95_rootThree_lo {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    (rootThree X s hs hX).lo = (rootStep X _ (rootStep_hi_pos X _ (rootStep_hi_pos X s hs hX) hX) hX).lo := rfl
private lemma r95_rootThree_hi {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    (rootThree X s hs hX).hi = (rootStep X _ (rootStep_hi_pos X _ (rootStep_hi_pos X s hs hX) hX) hX).hi := rfl
private lemma r95_radicand_lo {y : ℝ} (Y : Interval y) :
    (radicand Y).lo = ((Interval.point Q0).sub ((Y.add (Interval.point (1/2))).square)).lo := rfl
private lemma r95_radicand_hi {y : ℝ} (Y : Interval y) :
    (radicand Y).hi = ((Interval.point Q0).sub ((Y.add (Interval.point (1/2))).square)).hi := rfl
private lemma r95_ratioBox_lo {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioBox Y X hX).lo = ((Y.add (Interval.point (1/2))).div X hX).lo := rfl
private lemma r95_ratioBox_hi {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioBox Y X hX).hi = ((Y.add (Interval.point (1/2))).div X hX).hi := rfl
private lemma r95_ratioDBox_lo {y : ℝ} (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDBox X hX).lo = ((Interval.point Q0).div X.cube (Interval.cube_lo_pos hX)).lo := rfl
private lemma r95_ratioDBox_hi {y : ℝ} (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDBox X hX).hi = ((Interval.point Q0).div X.cube (Interval.cube_lo_pos hX)).hi := rfl
private lemma r95_firstBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (firstBox H Y X hX).lo = ((((Interval.point H.q).add ((Interval.point (2*H.r)).mul Y)).add ((Interval.point H.s).mul (coordinate X))).sub
      (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioBox Y X hX))).lo := rfl
private lemma r95_firstBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (firstBox H Y X hX).hi = ((((Interval.point H.q).add ((Interval.point (2*H.r)).mul Y)).add ((Interval.point H.s).mul (coordinate X))).sub
      (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioBox Y X hX))).hi := rfl
private lemma r95_secondBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (secondBox H Y X hX).lo = (((Interval.point (2*H.r)).sub ((Interval.point (2*H.s)).mul (ratioBox Y X hX))).sub
      (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioDBox X hX))).lo := rfl
private lemma r95_secondBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (secondBox H Y X hX).hi = (((Interval.point (2*H.r)).sub ((Interval.point (2*H.s)).mul (ratioBox Y X hX))).sub
      (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioDBox X hX))).hi := rfl
private lemma r95_thirdBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (thirdBox H Y X hX).lo = (((Interval.point (-3*H.s)).mul (ratioDBox X hX)).sub
      (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioDDBox Y X hX))).lo := rfl
private lemma r95_thirdBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (thirdBox H Y X hX).hi = (((Interval.point (-3*H.s)).mul (ratioDBox X hX)).sub
      (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioDDBox Y X hX))).hi := rfl
private lemma r95_qBox_lo {u : ℝ} (X : Interval u) :
    (LowerAlgebra.qBox X).lo = ((Interval.point (Q0+1)).sub ((Interval.point 2).mul X)).lo := rfl
private lemma r95_qBox_hi {u : ℝ} (X : Interval u) :
    (LowerAlgebra.qBox X).hi = ((Interval.point (Q0+1)).sub ((Interval.point 2).mul X)).hi := rfl
private lemma r95_factorBox_lo {u : ℝ} (X : Interval u) (Q : Interval (LowerInverse.q u)) (hU : 0<X.lo) (hQ : 0<Q.lo) :
    (LowerAlgebra.factorBox X Q hU hQ).lo = (((Interval.point Q0).sub X).div (X.mul Q) (Interval.mul_lo_pos hU hQ)).lo := rfl
private lemma r95_factorBox_hi {u : ℝ} (X : Interval u) (Q : Interval (LowerInverse.q u)) (hU : 0<X.lo) (hQ : 0<Q.lo) :
    (LowerAlgebra.factorBox X Q hU hQ).hi = (((Interval.point Q0).sub X).div (X.mul Q) (Interval.mul_lo_pos hU hQ)).hi := rfl
private lemma r95_factorDBox_lo {u : ℝ} (X : Interval u) (Q : Interval (LowerInverse.q u)) (hU : 0<X.lo) (hQ : 0<Q.lo) :
    (LowerAlgebra.factorDBox X Q hU hQ).lo = (((((Interval.point (4*Q0)).mul X).sub ((Interval.point 2).mul X.square)).sub
      (Interval.point (Q0*(Q0+1)))).div (X.square.mul Q.square)
      (Interval.mul_lo_pos (Interval.square_lo_pos hU) (Interval.square_lo_pos hQ))).lo := rfl
private lemma r95_factorDBox_hi {u : ℝ} (X : Interval u) (Q : Interval (LowerInverse.q u)) (hU : 0<X.lo) (hQ : 0<Q.lo) :
    (LowerAlgebra.factorDBox X Q hU hQ).hi = (((((Interval.point (4*Q0)).mul X).sub ((Interval.point 2).mul X.square)).sub
      (Interval.point (Q0*(Q0+1)))).div (X.square.mul Q.square)
      (Interval.mul_lo_pos (Interval.square_lo_pos hU) (Interval.square_lo_pos hQ))).hi := rfl
private lemma r95_speedBox_lo {z y : ℝ} (Z : Interval z) (Q : Interval (LowerInverse.q (U y))) (s : ℝ) (hs : 0<s)
    (hr : 0≤(Q.sub Z.square).lo) :
    (LowerAlgebra.speedBox Z Q s hs hr).lo = (rootThree (Q.sub Z.square) s hs hr).lo := rfl
private lemma r95_speedBox_hi {z y : ℝ} (Z : Interval z) (Q : Interval (LowerInverse.q (U y))) (s : ℝ) (hs : 0<s)
    (hr : 0≤(Q.sub Z.square).lo) :
    (LowerAlgebra.speedBox Z Q s hs hr).hi = (rootThree (Q.sub Z.square) s hs hr).hi := rfl
private lemma r95_inverseFirstBox_lo {z y : ℝ} (Z : Interval z) (X : Interval (U y))
    (R : Interval (ShortOuterOne.SameContact.ratio y)) (Q : Interval (LowerInverse.q (U y)))
    (V : Interval (LowerInverse.speed z y)) (hX : 0<X.lo) (hQ : 0<Q.lo) (hV : 0<V.lo) :
    (LowerAlgebra.inverseFirstBox Z X R Q V hX hQ hV).lo = ((LowerAlgebra.factorBox X Q hX hQ).sub ((Z.mul R).div (Q.mul V) (Interval.mul_lo_pos hQ hV))).lo := rfl
private lemma r95_inverseFirstBox_hi {z y : ℝ} (Z : Interval z) (X : Interval (U y))
    (R : Interval (ShortOuterOne.SameContact.ratio y)) (Q : Interval (LowerInverse.q (U y)))
    (V : Interval (LowerInverse.speed z y)) (hX : 0<X.lo) (hQ : 0<Q.lo) (hV : 0<V.lo) :
    (LowerAlgebra.inverseFirstBox Z X R Q V hX hQ hV).hi = ((LowerAlgebra.factorBox X Q hX hQ).sub ((Z.mul R).div (Q.mul V) (Interval.mul_lo_pos hQ hV))).hi := rfl
private lemma r95_outerFirstBox_lo (reverse : Bool) {b B : ℝ} (Z : Interval (b+1/2)) (Y : Interval B) (X : Interval (U B))
    (V : Interval (LowerInverse.speed (b+1/2) B)) (hX : 0<X.lo) (hQ : 0<(LowerAlgebra.qBox X).lo)
    (hV : 0<V.lo) :
    (LowerAlgebra.outerFirstBox reverse Z Y X V hX hQ hV).lo = ((LowerAlgebra.inverseFirstBox Z X (ratioBox Y X hX) (LowerAlgebra.qBox X) V hX hQ hV).sub
      (firstBox (LowerContact.outer reverse) Y X hX)).lo := rfl
private lemma r95_outerFirstBox_hi (reverse : Bool) {b B : ℝ} (Z : Interval (b+1/2)) (Y : Interval B) (X : Interval (U B))
    (V : Interval (LowerInverse.speed (b+1/2) B)) (hX : 0<X.lo) (hQ : 0<(LowerAlgebra.qBox X).lo)
    (hV : 0<V.lo) :
    (LowerAlgebra.outerFirstBox reverse Z Y X V hX hQ hV).hi = ((LowerAlgebra.inverseFirstBox Z X (ratioBox Y X hX) (LowerAlgebra.qBox X) V hX hQ hV).sub
      (firstBox (LowerContact.outer reverse) Y X hX)).hi := rfl
private lemma r95_zBox_lo {B : ℝ} (Y : Interval B) :
    (LowerEnvelope.zBox Y).lo = (Y.add (Interval.point (1/2))).lo := rfl
private lemma r95_zBox_hi {B : ℝ} (Y : Interval B) :
    (LowerEnvelope.zBox Y).hi = (Y.add (Interval.point (1/2))).hi := rfl
private lemma r95_pBox_lo {B : ℝ} (Y : Interval B) (X : Interval (U B)) (hX : 0<X.lo) :
    (LowerEnvelope.pBox Y X hX).lo = (firstBox LLabel Y X hX).lo := rfl
private lemma r95_pBox_hi {B : ℝ} (Y : Interval B) (X : Interval (U B)) (hX : 0<X.lo) :
    (LowerEnvelope.pBox Y X hX).hi = (firstBox LLabel Y X hX).hi := rfl
private lemma r95_ellBox_lo {B : ℝ} (Y : Interval B) (X : Interval (U B)) (hX : 0<X.lo) :
    (LowerEnvelope.ellBox Y X hX).lo = (secondBox LLabel Y X hX).lo := rfl
private lemma r95_ellBox_hi {B : ℝ} (Y : Interval B) (X : Interval (U B)) (hX : 0<X.lo) :
    (LowerEnvelope.ellBox Y X hX).hi = (secondBox LLabel Y X hX).hi := rfl
private lemma r95_SBox_lo {B : ℝ} (Y : Interval B) (P : Interval (LowerEnvelope.p B)) (hP : 0<P.lo) :
    (LowerEnvelope.SBox Y P hP).lo = ((LowerEnvelope.zBox Y).square.add ((Interval.point 1).div P.square (Interval.square_lo_pos hP))).lo := rfl
private lemma r95_SBox_hi {B : ℝ} (Y : Interval B) (P : Interval (LowerEnvelope.p B)) (hP : 0<P.lo) :
    (LowerEnvelope.SBox Y P hP).hi = ((LowerEnvelope.zBox Y).square.add ((Interval.point 1).div P.square (Interval.square_lo_pos hP))).hi := rfl
private lemma r95_hBox_lo {B : ℝ} (Y : Interval B) (P : Interval (LowerEnvelope.p B)) :
    (LowerEnvelope.hBox Y P).lo = ((LowerEnvelope.zBox Y).mul P).lo := rfl
private lemma r95_hBox_hi {B : ℝ} (Y : Interval B) (P : Interval (LowerEnvelope.p B)) :
    (LowerEnvelope.hBox Y P).hi = ((LowerEnvelope.zBox Y).mul P).hi := rfl
private lemma r95_h₁Box_lo {B : ℝ} (Y : Interval B) (P : Interval (LowerEnvelope.p B)) (E : Interval (LowerEnvelope.ell B)) :
    (LowerEnvelope.h₁Box Y P E).lo = (P.add ((LowerEnvelope.zBox Y).mul E)).lo := rfl
private lemma r95_h₁Box_hi {B : ℝ} (Y : Interval B) (P : Interval (LowerEnvelope.p B)) (E : Interval (LowerEnvelope.ell B)) :
    (LowerEnvelope.h₁Box Y P E).hi = (P.add ((LowerEnvelope.zBox Y).mul E)).hi := rfl
private lemma r95_markerBox_lo {B : ℝ} (P : Interval (LowerEnvelope.p B)) (E : Interval (LowerEnvelope.ell B)) :
    (LowerEnvelope.markerBox P E).lo = (E.neg.sub ((Interval.point (3/2)).mul P)).lo := rfl
private lemma r95_markerBox_hi {B : ℝ} (P : Interval (LowerEnvelope.p B)) (E : Interval (LowerEnvelope.ell B)) :
    (LowerEnvelope.markerBox P E).hi = (E.neg.sub ((Interval.point (3/2)).mul P)).hi := rfl
private lemma r95_slopeRatioBox_lo {B : ℝ} (P : Interval (LowerEnvelope.p B)) (E : Interval (LowerEnvelope.ell B)) (hP : 0<P.lo) :
    (LowerEnvelope.slopeRatioBox P E hP).lo = (E.neg.div P.square (Interval.square_lo_pos hP)).lo := rfl
private lemma r95_slopeRatioBox_hi {B : ℝ} (P : Interval (LowerEnvelope.p B)) (E : Interval (LowerEnvelope.ell B)) (hP : 0<P.lo) :
    (LowerEnvelope.slopeRatioBox P E hP).hi = (E.neg.div P.square (Interval.square_lo_pos hP)).hi := rfl
private lemma r95_DBox_lo {B : ℝ} (Y : Interval B) (P : Interval (LowerEnvelope.p B)) (E : Interval (LowerEnvelope.ell B))
    (hP : 0<P.lo) :
    (LowerEnvelope.DBox Y P E hP).lo = ((LowerEnvelope.zBox Y).sub (E.div P.cube (Interval.cube_lo_pos hP))).lo := rfl
private lemma r95_DBox_hi {B : ℝ} (Y : Interval B) (P : Interval (LowerEnvelope.p B)) (E : Interval (LowerEnvelope.ell B))
    (hP : 0<P.lo) :
    (LowerEnvelope.DBox Y P E hP).hi = ((LowerEnvelope.zBox Y).sub (E.div P.cube (Interval.cube_lo_pos hP))).hi := rfl
private lemma r95_g₁Box_lo {B : ℝ} (H : Interval (LowerEnvelope.h B)) (Q : Interval (LowerEnvelope.S B)) (hQ : 0<Q.lo) :
    (LowerEnvelope.g₁Box H Q hQ).lo = (H.neg.div ((Interval.point 2).mul Q) (Interval.mul_lo_pos (by norm_num [Interval.point]) hQ)).lo := rfl
private lemma r95_g₁Box_hi {B : ℝ} (H : Interval (LowerEnvelope.h B)) (Q : Interval (LowerEnvelope.S B)) (hQ : 0<Q.lo) :
    (LowerEnvelope.g₁Box H Q hQ).hi = (H.neg.div ((Interval.point 2).mul Q) (Interval.mul_lo_pos (by norm_num [Interval.point]) hQ)).hi := rfl
private lemma r95_g₂Box_lo {B : ℝ} (H : Interval (LowerEnvelope.h B)) (H₁ : Interval (LowerEnvelope.h₁ B))
    (Q : Interval (LowerEnvelope.S B)) (D₀ : Interval (LowerEnvelope.D B)) (hQ : 0<Q.lo) (hD : 0<D₀.lo) :
    (LowerEnvelope.g₂Box H H₁ Q D₀ hQ hD).lo = ((H.div ((Interval.point 2).mul Q.square)
      (Interval.mul_lo_pos (by norm_num [Interval.point]) (Interval.square_lo_pos hQ))).sub
      (H₁.div (((Interval.point 4).mul Q).mul D₀)
        (Interval.mul_lo_pos (Interval.mul_lo_pos (by norm_num [Interval.point]) hQ) hD))).lo := rfl
private lemma r95_g₂Box_hi {B : ℝ} (H : Interval (LowerEnvelope.h B)) (H₁ : Interval (LowerEnvelope.h₁ B))
    (Q : Interval (LowerEnvelope.S B)) (D₀ : Interval (LowerEnvelope.D B)) (hQ : 0<Q.lo) (hD : 0<D₀.lo) :
    (LowerEnvelope.g₂Box H H₁ Q D₀ hQ hD).hi = ((H.div ((Interval.point 2).mul Q.square)
      (Interval.mul_lo_pos (by norm_num [Interval.point]) (Interval.square_lo_pos hQ))).sub
      (H₁.div (((Interval.point 4).mul Q).mul D₀)
        (Interval.mul_lo_pos (Interval.mul_lo_pos (by norm_num [Interval.point]) hQ) hD))).hi := rfl
private lemma r95_shifted_eq {y : ℝ} : U y = Real.sqrt (Q0-(y+1/2)^2) := by
  dsimp [U,ShortOuterOne.SameContact.arc]; ring
private lemma r95_shifted_lo {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).lo = (rootThree (radicand Y) s hs hr).lo :=
  r95_mpr_lo r95_shifted_eq (congrArg _ r95_shifted_eq) _
private lemma r95_shifted_hi {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).hi = (rootThree (radicand Y) s hs hr).hi :=
  r95_mpr_hi r95_shifted_eq (congrArg _ r95_shifted_eq) _
private lemma r95_coordinate_eq {y : ℝ} : ShortOuterOne.SameContact.arc y = U y-1/2 := by
  dsimp [U]; ring
private lemma r95_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r95_mpr_lo r95_coordinate_eq (congrArg _ r95_coordinate_eq) _
private lemma r95_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r95_mpr_hi r95_coordinate_eq (congrArg _ r95_coordinate_eq) _
private lemma r95_ratioDD_eq {y : ℝ} :
    ShortOuterOne.SameContact.ratioDD y = 3*Q0*(y+1/2)/((U y)^3*(U y)^2) := by
  dsimp [ShortOuterOne.SameContact.ratioDD,U]; ring
private lemma r95_ratioDDBox_lo {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDDBox Y X hX).lo = (((Interval.point (3*Q0)).mul (Y.add (Interval.point (1/2)))).div
      (X.cube.mul X.square)
      (Interval.mul_lo_pos (Interval.cube_lo_pos hX) (Interval.square_lo_pos hX))).lo :=
  r95_mpr_lo r95_ratioDD_eq (congrArg _ r95_ratioDD_eq) _
private lemma r95_ratioDDBox_hi {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDDBox Y X hX).hi = (((Interval.point (3*Q0)).mul (Y.add (Interval.point (1/2)))).div
      (X.cube.mul X.square)
      (Interval.mul_lo_pos (Interval.cube_lo_pos hX) (Interval.square_lo_pos hX))).hi :=
  r95_mpr_hi r95_ratioDD_eq (congrArg _ r95_ratioDD_eq) _
private lemma r95_label_eq (H : RoleLabel) {y : ℝ} :
    H.outer y = H.c+H.p*(ShortOuterOne.SameContact.arc y)+H.q*y+H.r*y^2+
      H.s*(ShortOuterOne.SameContact.arc y*y) := by
  dsimp [RoleLabel.outer,RoleLabel.eval]; ring
private lemma r95_labelBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).lo = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).lo :=
  r95_mpr_lo (r95_label_eq H) (congrArg _ (r95_label_eq H)) _
private lemma r95_labelBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).hi = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).hi :=
  r95_mpr_hi (r95_label_eq H) (congrArg _ (r95_label_eq H)) _

attribute [local simp ↓] r95_mul_lo r95_mul_hi r95_inv_lo r95_inv_hi r95_add_lo r95_add_hi
  r95_sub_lo r95_sub_hi r95_neg_lo r95_neg_hi r95_point_lo r95_point_hi r95_of_bounds_lo
  r95_of_bounds_hi r95_rootStep_lo r95_rootStep_hi r95_square_lo r95_square_hi r95_cube_lo
  r95_cube_hi r95_div_lo r95_div_hi r95_rootThree_lo r95_rootThree_hi r95_radicand_lo
  r95_radicand_hi r95_ratioBox_lo r95_ratioBox_hi r95_ratioDBox_lo r95_ratioDBox_hi r95_firstBox_lo
  r95_firstBox_hi r95_secondBox_lo r95_secondBox_hi r95_thirdBox_lo r95_thirdBox_hi r95_qBox_lo
  r95_qBox_hi r95_factorBox_lo r95_factorBox_hi r95_factorDBox_lo r95_factorDBox_hi r95_speedBox_lo
  r95_speedBox_hi r95_inverseFirstBox_lo r95_inverseFirstBox_hi r95_outerFirstBox_lo
  r95_outerFirstBox_hi r95_zBox_lo r95_zBox_hi r95_pBox_lo r95_pBox_hi r95_ellBox_lo r95_ellBox_hi
  r95_SBox_lo r95_SBox_hi r95_hBox_lo r95_hBox_hi r95_h₁Box_lo r95_h₁Box_hi r95_markerBox_lo
  r95_markerBox_hi r95_slopeRatioBox_lo r95_slopeRatioBox_hi r95_DBox_lo r95_DBox_hi r95_g₁Box_lo
  r95_g₁Box_hi r95_g₂Box_lo r95_g₂Box_hi r95_shifted_lo r95_shifted_hi r95_coordinate_lo
  r95_coordinate_hi r95_ratioDDBox_lo r95_ratioDDBox_hi r95_labelBox_lo r95_labelBox_hi

local macro "critical_reference" : tactic => `(tactic|
  norm_num [LLabel,TLabel,Q0,LowerContact.inner,LowerContact.outer,probeSource,probeLo,probeHi])

def probeSourceU (late : Bool) : Interval (U (probeSource late)) :=
  shifted (Interval.point (probeSource late)) (17/10) (by norm_num)
    (by cases late <;> critical_reference)
def probeLoU (late : Bool) : Interval (U (probeLo late)) :=
  shifted (Interval.point (probeLo late)) (19/10) (by norm_num)
    (by cases late <;> critical_reference)
def probeHiU (late : Bool) : Interval (U (probeHi late)) :=
  shifted (Interval.point (probeHi late)) (19/10) (by norm_num)
    (by cases late <;> critical_reference)

private lemma r95_sourceRadicand (late : Bool) :
    0≤(radicand (Interval.point (probeSource late))).lo := by
  cases late <;> critical_reference
private lemma r95_loRadicand (late : Bool) : 0≤(radicand (Interval.point (probeLo late))).lo := by
  cases late <;> critical_reference
private lemma r95_hiRadicand (late : Bool) : 0≤(radicand (Interval.point (probeHi late))).lo := by
  cases late <;> critical_reference
private lemma r95_probeSourceU_lo (late : Bool) : (probeSourceU late).lo =
    (shifted (Interval.point (probeSource late)) (17/10) (by norm_num) (r95_sourceRadicand late)).lo :=
  rfl
private lemma r95_probeSourceU_hi (late : Bool) : (probeSourceU late).hi =
    (shifted (Interval.point (probeSource late)) (17/10) (by norm_num) (r95_sourceRadicand late)).hi :=
  rfl
private lemma r95_probeLoU_lo (late : Bool) : (probeLoU late).lo =
    (shifted (Interval.point (probeLo late)) (19/10) (by norm_num) (r95_loRadicand late)).lo := rfl
private lemma r95_probeLoU_hi (late : Bool) : (probeLoU late).hi =
    (shifted (Interval.point (probeLo late)) (19/10) (by norm_num) (r95_loRadicand late)).hi := rfl
private lemma r95_probeHiU_lo (late : Bool) : (probeHiU late).lo =
    (shifted (Interval.point (probeHi late)) (19/10) (by norm_num) (r95_hiRadicand late)).lo := rfl
private lemma r95_probeHiU_hi (late : Bool) : (probeHiU late).hi =
    (shifted (Interval.point (probeHi late)) (19/10) (by norm_num) (r95_hiRadicand late)).hi := rfl
attribute [local simp ↓] r95_probeSourceU_lo r95_probeSourceU_hi r95_probeLoU_lo r95_probeLoU_hi
  r95_probeHiU_lo r95_probeHiU_hi

/-! The radicals rounded outward (sixteen decimals at the probe points, twelve for the
speeds), so that the substitutions below work with short numerals. -/
private lemma r95_LoU_bounds (late : Bool) :
    (if late then (18773614652159339/10000000000000000:ℝ) else 18777526958174410/10000000000000000)≤(probeLoU late).lo ∧
      (probeLoU late).hi≤(if late then (18773614652159340/10000000000000000:ℝ) else 18777526958174411/10000000000000000) := by
  cases late <;> critical_reference
private def r95_LoU (late : Bool) : Interval (U (probeLo late)) :=
  (probeLoU late).tighten _ _ (r95_LoU_bounds late).1 (r95_LoU_bounds late).2
private lemma r95_LoU_lo (late : Bool) : (r95_LoU late).lo=(if late then (18773614652159339/10000000000000000:ℝ) else 18777526958174410/10000000000000000) := rfl
private lemma r95_LoU_hi (late : Bool) : (r95_LoU late).hi=(if late then (18773614652159340/10000000000000000:ℝ) else 18777526958174411/10000000000000000) := rfl
attribute [local simp ↓] r95_LoU_lo r95_LoU_hi
private lemma r95_HiU_bounds (late : Bool) :
    (if late then (18773614652126027/10000000000000000:ℝ) else 18777526958141167/10000000000000000)≤(probeHiU late).lo ∧
      (probeHiU late).hi≤(if late then (18773614652126028/10000000000000000:ℝ) else 18777526958141168/10000000000000000) := by
  cases late <;> critical_reference
private def r95_HiU (late : Bool) : Interval (U (probeHi late)) :=
  (probeHiU late).tighten _ _ (r95_HiU_bounds late).1 (r95_HiU_bounds late).2
private lemma r95_HiU_lo (late : Bool) : (r95_HiU late).lo=(if late then (18773614652126027/10000000000000000:ℝ) else 18777526958141167/10000000000000000) := rfl
private lemma r95_HiU_hi (late : Bool) : (r95_HiU late).hi=(if late then (18773614652126028/10000000000000000:ℝ) else 18777526958141168/10000000000000000) := rfl
attribute [local simp ↓] r95_HiU_lo r95_HiU_hi
private lemma r95_SourceU_bounds (late : Bool) :
    (if late then (17075128110793195/10000000000000000:ℝ) else 17104312321750909/10000000000000000)≤(probeSourceU late).lo ∧
      (probeSourceU late).hi≤(if late then (17075128110793196/10000000000000000:ℝ) else 17104312321750910/10000000000000000) := by
  cases late <;> critical_reference
private def r95_SourceU (late : Bool) : Interval (U (probeSource late)) :=
  (probeSourceU late).tighten _ _ (r95_SourceU_bounds late).1 (r95_SourceU_bounds late).2
private lemma r95_SourceU_lo (late : Bool) : (r95_SourceU late).lo=(if late then (17075128110793195/10000000000000000:ℝ) else 17104312321750909/10000000000000000) := rfl
private lemma r95_SourceU_hi (late : Bool) : (r95_SourceU late).hi=(if late then (17075128110793196/10000000000000000:ℝ) else 17104312321750910/10000000000000000) := rfl
attribute [local simp ↓] r95_SourceU_lo r95_SourceU_hi

lemma probe_scalar_bracket (late : Bool) :
    S (probeLo late)<LowerInverse.q (U (probeSource late)) ∧
      LowerInverse.q (U (probeSource late))<S (probeHi late) := by
  have hl : 0<(r95_LoU late).lo := by cases late <;> critical_reference
  have hr : 0<(r95_HiU late).lo := by cases late <;> critical_reference
  let P₀ := pBox (Interval.point (probeLo late)) (r95_LoU late) hl
  let P₁ := pBox (Interval.point (probeHi late)) (r95_HiU late) hr
  have hp₀ : 0<P₀.lo := by cases late <;> dsimp only [P₀] <;> critical_reference
  have hp₁ : 0<P₁.lo := by cases late <;> dsimp only [P₁] <;> critical_reference
  let S₀ := SBox (Interval.point (probeLo late)) P₀ hp₀
  let S₁ := SBox (Interval.point (probeHi late)) P₁ hp₁
  let Q := qBox (r95_SourceU late)
  have h₀ : S₀.hi<Q.lo := by
    cases late <;> dsimp only [S₀,P₀,Q] <;> critical_reference
  have h₁ : Q.hi<S₁.lo := by
    cases late <;> dsimp only [S₁,P₁,Q] <;> critical_reference
  exact ⟨S₀.mem.2.trans_lt (h₀.trans_le Q.mem.1),Q.mem.2.trans_lt (h₁.trans_le S₁.mem.1)⟩


lemma probe_bracket (late : Bool) : probeLo late<probePoint late ∧ probePoint late<probeHi late := by
  have hb : probeSource late∈Icc 0 (3/5) := by cases late <;> norm_num [probeSource]
  have hl : probeLo late∈Icc (3/100) (3/20) := by cases late <;> norm_num [probeLo]
  have hu : probeHi late∈Icc (3/100) (3/20) := by cases late <;> norm_num [probeHi]
  have hh := parameter_bracket hb hl hu (probe_scalar_bracket late).1 (probe_scalar_bracket late).2
  cases late <;> simpa [probePoint,probeSource,halfPoint,referencePoint] using hh

lemma probe_source (late : Bool) : source (probePoint late)=probeSource late := by
  cases late
  · exact reference_source
  · exact half_source

lemma probe_domain (late : Bool) : Domain (probePoint late) := by
  cases late
  · exact reference_domain
  · exact half_domain

def probeBox (late : Bool) : Interval (probePoint late) :=
  Interval.of_bounds ⟨(probe_bracket late).1.le,(probe_bracket late).2.le⟩
def probeU (late : Bool) : Interval (U (probePoint late)) :=
  shifted (probeBox late) (19/10) (by norm_num)
    (by cases late <;> dsimp [probeBox] <;> critical_reference)
def probeSpeed (late : Bool) :
    Interval (LowerInverse.speed (probePoint late+1/2) (probeSource late)) :=
  speedBox ((probeBox late).add (Interval.point (1/2))) (qBox (probeSourceU late))
    (21/20) (by norm_num)
    (by cases late <;> dsimp [probeBox,probeSourceU] <;> critical_reference)

private lemma r95_probeBox_lo (late : Bool) : (probeBox late).lo=probeLo late := rfl
private lemma r95_probeBox_hi (late : Bool) : (probeBox late).hi=probeHi late := rfl
attribute [local simp ↓] r95_probeBox_lo r95_probeBox_hi
private lemma r95_speedRadicand (late : Bool) :
    0≤((qBox (probeSourceU late)).sub (((probeBox late).add (Interval.point (1/2))).square)).lo := by
  cases late <;> critical_reference
private lemma r95_probeSpeed_lo (late : Bool) : (probeSpeed late).lo =
    (speedBox ((probeBox late).add (Interval.point (1/2))) (qBox (probeSourceU late))
      (21/20) (by norm_num) (r95_speedRadicand late)).lo := rfl
private lemma r95_probeSpeed_hi (late : Bool) : (probeSpeed late).hi =
    (speedBox ((probeBox late).add (Interval.point (1/2))) (qBox (probeSourceU late))
      (21/20) (by norm_num) (r95_speedRadicand late)).hi := rfl
attribute [local simp ↓] r95_probeSpeed_lo r95_probeSpeed_hi
private lemma r95_Speed_bounds (late : Bool) :
    (if late then (1053309284538/1000000000000:ℝ) else 1051233904644/1000000000000)≤(probeSpeed late).lo ∧
      (probeSpeed late).hi≤(if late then (1053309284550/1000000000000:ℝ) else 1051233904657/1000000000000) := by
  cases late <;> critical_reference
private def r95_Speed (late : Bool) : Interval (LowerInverse.speed (probePoint late+1/2) (probeSource late)) :=
  (probeSpeed late).tighten _ _ (r95_Speed_bounds late).1 (r95_Speed_bounds late).2
private lemma r95_Speed_lo (late : Bool) : (r95_Speed late).lo=(if late then (1053309284538/1000000000000:ℝ) else 1051233904644/1000000000000) := rfl
private lemma r95_Speed_hi (late : Bool) : (r95_Speed late).hi=(if late then (1053309284550/1000000000000:ℝ) else 1051233904657/1000000000000) := rfl
attribute [local simp ↓] r95_Speed_lo r95_Speed_hi

lemma half_first : (1/4000:ℝ)<first halfPoint := by
  have hu : 0<(r95_SourceU true).lo := by critical_reference
  have hq : 0<(qBox (r95_SourceU true)).lo := by critical_reference
  have hv : 0<(r95_Speed true).lo := by critical_reference
  let Z := outerFirstBox true ((probeBox true).add (Interval.point (1/2)))
    (Interval.point (probeSource true)) (r95_SourceU true) (r95_Speed true) hu hq hv
  have hh : (1/4000:ℝ)<Z.lo := by
    dsimp only [Z]; critical_reference
  have hval : (1/4000:ℝ)<LowerContact.outerFirst true halfPoint (1/2) := hh.trans_le Z.mem.1
  have he := actual_first half_domain.1
  rw [half_source] at he
  rwa [he] at hval

lemma reference_first : |first referencePoint|<(1/10000:ℝ) := by
  have hu : 0<(r95_SourceU false).lo := by critical_reference
  have hq : 0<(qBox (r95_SourceU false)).lo := by critical_reference
  have hv : 0<(r95_Speed false).lo := by critical_reference
  let Z := outerFirstBox true ((probeBox false).add (Interval.point (1/2)))
    (Interval.point (probeSource false)) (r95_SourceU false) (r95_Speed false) hu hq hv
  have hl : -(1/10000:ℝ)<Z.lo := by
    dsimp only [Z]; critical_reference
  have hh : Z.hi<(1/10000:ℝ) := by
    dsimp only [Z]; critical_reference
  have hval : |LowerContact.outerFirst true referencePoint (99/200)|<(1/10000:ℝ) :=
    abs_lt.mpr ⟨hl.trans_le Z.mem.1,Z.mem.2.trans_lt hh⟩
  have he := actual_first reference_domain.1
  rw [reference_source] at he
  rwa [he] at hval

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerCritical
