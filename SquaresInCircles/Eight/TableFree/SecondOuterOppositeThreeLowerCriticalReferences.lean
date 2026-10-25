module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerCriticalRootReferences

/-!
# Curvature and value at the two individual critical references

The half-coordinate curvature is an exact substitution in the proved
envelope formula.  The earlier value uses a direct Taylor comparison
with the actual inverse contact angle.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerCritical
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open LowerInverse LowerEnvelope
open StationaryPrimitives (Interval)
open ReferenceAlgebra LowerAlgebra

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

private lemma r95_sourceRadicand (late : Bool) :
    0≤(radicand (Interval.point (probeSource late))).lo := by
  cases late <;> critical_reference
private lemma r95_probeSourceU_lo (late : Bool) : (probeSourceU late).lo =
    (shifted (Interval.point (probeSource late)) (17/10) (by norm_num) (r95_sourceRadicand late)).lo :=
  rfl
private lemma r95_probeSourceU_hi (late : Bool) : (probeSourceU late).hi =
    (shifted (Interval.point (probeSource late)) (17/10) (by norm_num) (r95_sourceRadicand late)).hi :=
  rfl
private lemma r95_probeBox_lo (late : Bool) : (probeBox late).lo=probeLo late := rfl
private lemma r95_probeBox_hi (late : Bool) : (probeBox late).hi=probeHi late := rfl
attribute [local simp ↓] r95_probeSourceU_lo r95_probeSourceU_hi r95_probeBox_lo r95_probeBox_hi
private lemma r95_boxRadicand (late : Bool) : 0≤(radicand (probeBox late)).lo := by
  cases late <;> critical_reference
private lemma r95_probeU_lo (late : Bool) : (probeU late).lo =
    (shifted (probeBox late) (19/10) (by norm_num) (r95_boxRadicand late)).lo := rfl
private lemma r95_probeU_hi (late : Bool) : (probeU late).hi =
    (shifted (probeBox late) (19/10) (by norm_num) (r95_boxRadicand late)).hi := rfl
attribute [local simp ↓] r95_probeU_lo r95_probeU_hi

/-! The two radicals at the half reference rounded outward to twelve decimals, so that the
curvature substitution works with short numerals. -/
private lemma r95_halfU_bounds : (1877361465209/1000000000000:ℝ)≤(probeU true).lo ∧
    (probeU true).hi≤1877361465216/1000000000000 := by critical_reference
private lemma r95_halfSourceU_bounds : (1707512811079/1000000000000:ℝ)≤(probeSourceU true).lo ∧
    (probeSourceU true).hi≤1707512811080/1000000000000 := by critical_reference
private def r95_halfU : Interval (U (probePoint true)) :=
  (probeU true).tighten _ _ r95_halfU_bounds.1 r95_halfU_bounds.2
private def r95_halfSourceU : Interval (U (probeSource true)) :=
  (probeSourceU true).tighten _ _ r95_halfSourceU_bounds.1 r95_halfSourceU_bounds.2
private lemma r95_halfU_lo : r95_halfU.lo=1877361465209/1000000000000 := rfl
private lemma r95_halfU_hi : r95_halfU.hi=1877361465216/1000000000000 := rfl
private lemma r95_halfSourceU_lo : r95_halfSourceU.lo=1707512811079/1000000000000 := rfl
private lemma r95_halfSourceU_hi : r95_halfSourceU.hi=1707512811080/1000000000000 := rfl
attribute [local simp ↓] r95_halfU_lo r95_halfU_hi r95_halfSourceU_lo r95_halfSourceU_hi

lemma half_second : (3/50:ℝ)<second halfPoint := by
  let Y := probeBox true
  let X₀ := r95_halfU
  have hX : 0<X₀.lo := by dsimp only [X₀]; critical_reference
  let P := pBox Y X₀ hX
  let E := ellBox Y X₀ hX
  have hP : 0<P.lo := by dsimp only [P,Y,X₀]; critical_reference
  let Q := SBox Y P hP
  let H := hBox Y P
  let J := h₁Box Y P E
  let D₀ := DBox Y P E hP
  have hQ : 0<Q.lo := by dsimp only [Q,P,Y,X₀]; critical_reference
  have hD : 0<D₀.lo := by dsimp only [D₀,P,E,Y,X₀]; critical_reference
  let G₁ := g₁Box H Q hQ
  let G₂ := g₂Box H J Q D₀ hQ hD
  let V := r95_halfSourceU
  have hV : 0<V.lo := by dsimp only [V]; critical_reference
  let Q₀ := qBox V
  have hQ₀ : 0<Q₀.lo := by dsimp only [Q₀,V]; critical_reference
  let R := ratioBox (Interval.point (probeSource true)) V hV
  let R₁ := ratioDBox V hV
  let F := factorDBox V Q₀ hV hQ₀
  let T := secondBox TLabel (Interval.point (probeSource true)) V hV
  let Z := ((((R.mul F).neg).add (((Interval.point 4).mul R.square).mul G₂)).add
    (((Interval.point 2).mul R₁).mul G₁)).sub T
  have hh : (3/50:ℝ)<Z.lo := by
    dsimp only [Z,T,F,R,R₁,V,Q₀,G₁,G₂,H,J,D₀,Q,P,E,Y,X₀]
    critical_reference
  have hv := hh.trans_le Z.mem.1
  dsimp [second]
  rw [half_source]
  simpa [probeSource,probePoint] using hv

def referenceAngle : ℝ := 84219/1000000

lemma reference_labels : T (99/200)<(208793/500000:ℝ) ∧
    L referencePoint<(171201/1000000:ℝ) := by
  let T := labelBox TLabel (Interval.point (probeSource false)) (probeSourceU false)
  let L₀ := labelBox LLabel (probeBox false) (probeU false)
  have ht : T.hi<(208793/500000:ℝ) := by dsimp only [T]; critical_reference
  have hl : L₀.hi<(171201/1000000:ℝ) := by dsimp only [L₀]; critical_reference
  exact ⟨T.mem.2.trans_lt ht,L₀.mem.2.trans_lt hl⟩

lemma reference_contact_after :
    (arc (99/200)-1/2)*Real.cos referenceAngle-
      ((99/200:ℝ)+1/2)*Real.sin referenceAngle≤referencePoint+1/2 := by
  have hx : referenceAngle∈Icc 0 (7/10) := by norm_num [referenceAngle]
  have htrig := positive_trig hx
  have hc := cos_le_cos8 hx.1
  have hs := (trig_taylor_bounds hx.1).1
  have hu : U (99/200)<(17104313/10000000:ℝ) := by
    have hh : (probeSourceU false).hi<(17104313/10000000:ℝ) := by
      critical_reference
    exact (probeSourceU false).mem.2.trans_lt hh
  have hup : arc (99/200)-1/2≤(7104313/10000000:ℝ) := by dsimp [U] at hu; linarith
  have hcos := mul_le_mul hup hc (by linarith [htrig.1]) (by norm_num)
  have hsin := mul_le_mul_of_nonneg_left hs
    (by norm_num : 0≤(99/200:ℝ)+1/2)
  have hpoint := (probe_bracket false).1
  norm_num [probePoint,probeLo] at hpoint
  norm_num [referenceAngle,sin7,cos8] at hcos hsin ⊢
  linarith

lemma reference_value : (89779/100000:ℝ)<cost referencePoint := by
  have hb : (99/200:ℝ)∈Icc 0 outerDiagonal :=
    LowerGeometry.full_domain (by norm_num)
  have hz := shift_mem reference_domain.1
  have hphase := LowerInverse.phase_lower hb hz
    (show referenceAngle∈Icc 0 (7/10) by norm_num [referenceAngle]) reference_contact_after
  have hT := reference_labels.1
  have hL := reference_labels.2
  dsimp only [cost,LowerContact.cost,LowerContact.inner,LowerContact.outer]
  rw [reference_source]
  change (89779/100000:ℝ)<Real.pi/2+LowerInverse.phase (z referencePoint) (99/200)-
    L referencePoint-T (99/200)
  norm_num [referenceAngle] at hphase
  linarith [pi_hand_enclosure.1]

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerCritical
