module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerEnvelopeAlgebra

/-!
# The two endpoints of the whole target-envelope interval

All comparisons are at `.03` or `.15`, and at the two source endpoints
needed to place their complete critical continuation.  There is no
cover of source or target coordinates.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerEnvelope
open CommonQuarter CorePairGeometry Arithmetic
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

local macro "envelope_reference" : tactic => `(tactic|
  (simp only [r95_mul_lo,r95_mul_hi,r95_inv_lo,r95_inv_hi,r95_add_lo,r95_add_hi,r95_sub_lo,r95_sub_hi,
    r95_neg_lo,r95_neg_hi,r95_point_lo,r95_point_hi,r95_of_bounds_lo,r95_of_bounds_hi,r95_rootStep_lo,r95_rootStep_hi,
    r95_square_lo,r95_square_hi,r95_cube_lo,r95_cube_hi,r95_div_lo,r95_div_hi,r95_rootThree_lo,r95_rootThree_hi,
    r95_radicand_lo,r95_radicand_hi,r95_ratioBox_lo,r95_ratioBox_hi,r95_ratioDBox_lo,r95_ratioDBox_hi,r95_firstBox_lo,r95_firstBox_hi,
    r95_secondBox_lo,r95_secondBox_hi,r95_thirdBox_lo,r95_thirdBox_hi,r95_qBox_lo,r95_qBox_hi,r95_factorBox_lo,r95_factorBox_hi,
    r95_factorDBox_lo,r95_factorDBox_hi,r95_speedBox_lo,r95_speedBox_hi,r95_inverseFirstBox_lo,r95_inverseFirstBox_hi,r95_outerFirstBox_lo,r95_outerFirstBox_hi,
    r95_zBox_lo,r95_zBox_hi,r95_pBox_lo,r95_pBox_hi,r95_ellBox_lo,r95_ellBox_hi,r95_SBox_lo,r95_SBox_hi,
    r95_hBox_lo,r95_hBox_hi,r95_h₁Box_lo,r95_h₁Box_hi,r95_markerBox_lo,r95_markerBox_hi,r95_slopeRatioBox_lo,r95_slopeRatioBox_hi,
    r95_DBox_lo,r95_DBox_hi,r95_g₁Box_lo,r95_g₁Box_hi,r95_g₂Box_lo,r95_g₂Box_hi,r95_shifted_lo,r95_shifted_hi,
    r95_coordinate_lo,r95_coordinate_hi,r95_ratioDDBox_lo,r95_ratioDDBox_hi,r95_labelBox_lo,r95_labelBox_hi]
   norm_num [LLabel,Q0]))

def leftU : Interval (U (3/100)) :=
  shifted (Interval.point (3/100)) (19/10) (by norm_num) (by envelope_reference)
def rightU : Interval (U (3/20)) :=
  shifted (Interval.point (3/20)) (19/10) (by norm_num) (by envelope_reference)
def sourceEndU : Interval (U (3/5)) :=
  shifted (Interval.point (3/5)) (33/20) (by norm_num) (by envelope_reference)

/-! The four radicals rounded outward to ten decimals, so that later substitutions stay small. -/
private lemma r95_leftU : (19064889194/10000000000:ℝ)≤leftU.lo ∧ leftU.hi≤19064889195/10000000000 := by
  dsimp only [leftU]; envelope_reference
private lemma r95_rightU : (18689836810/10000000000:ℝ)≤rightU.lo ∧ rightU.hi≤18689836811/10000000000 := by
  dsimp only [rightU]; envelope_reference
private lemma r95_sourceEndU :
    (16448708155/10000000000:ℝ) ≤ sourceEndU.lo ∧ sourceEndU.hi ≤ 16448708156/10000000000 := by
  dsimp only [sourceEndU]; envelope_reference
private lemma r95_zeroU :
    (19145756710/10000000000:ℝ)≤Aligned.zeroU.lo ∧ Aligned.zeroU.hi≤19145756711/10000000000 := by
  dsimp only [Aligned.zeroU]; envelope_reference
private def r95_L : Interval (U (3/100)) := leftU.tighten _ _ r95_leftU.1 r95_leftU.2
private def r95_R : Interval (U (3/20)) := rightU.tighten _ _ r95_rightU.1 r95_rightU.2
private def r95_E : Interval (U (3/5)) := sourceEndU.tighten _ _ r95_sourceEndU.1 r95_sourceEndU.2
private def r95_Z : Interval (U 0) := Aligned.zeroU.tighten _ _ r95_zeroU.1 r95_zeroU.2
private lemma r95_L_lo : r95_L.lo=19064889194/10000000000 := rfl
private lemma r95_L_hi : r95_L.hi=19064889195/10000000000 := rfl
private lemma r95_R_lo : r95_R.lo=18689836810/10000000000 := rfl
private lemma r95_R_hi : r95_R.hi=18689836811/10000000000 := rfl
private lemma r95_E_lo : r95_E.lo=16448708155/10000000000 := rfl
private lemma r95_E_hi : r95_E.hi=16448708156/10000000000 := rfl
private lemma r95_Z_lo : r95_Z.lo=19145756710/10000000000 := rfl
private lemma r95_Z_hi : r95_Z.hi=19145756711/10000000000 := rfl
attribute [local simp] r95_L_lo r95_L_hi r95_R_lo r95_R_hi r95_E_lo r95_E_hi r95_Z_lo r95_Z_hi

lemma endpoint_label_bounds :
    p (3/100)<(1117/1000:ℝ) ∧ (911/1000:ℝ)<p (3/20) ∧
    -(191/100:ℝ)<ell (3/100) ∧ ell (3/20)< -(753/500:ℝ) ∧
    (129/40:ℝ)<LLabel.d3 (3/100) ∧ LLabel.d3 (3/20)<438/125 := by
  have hl : 0<r95_L.lo := by rw [r95_L_lo]; norm_num
  have hr : 0<r95_R.lo := by rw [r95_R_lo]; norm_num
  let P₀ := pBox (Interval.point (3/100)) r95_L hl
  let P₁ := pBox (Interval.point (3/20)) r95_R hr
  let E₀ := ellBox (Interval.point (3/100)) r95_L hl
  let E₁ := ellBox (Interval.point (3/20)) r95_R hr
  let T₀ := thirdBox LLabel (Interval.point (3/100)) r95_L hl
  let T₁ := thirdBox LLabel (Interval.point (3/20)) r95_R hr
  have hp₀ : P₀.hi<(1117/1000:ℝ) := by dsimp only [P₀]; envelope_reference
  have hp₁ : (911/1000:ℝ)<P₁.lo := by dsimp only [P₁]; envelope_reference
  have he₀ : -(191/100:ℝ)<E₀.lo := by dsimp only [E₀]; envelope_reference
  have he₁ : E₁.hi< -(753/500:ℝ) := by dsimp only [E₁]; envelope_reference
  have ht₀ : (129/40:ℝ)<T₀.lo := by dsimp only [T₀]; envelope_reference
  have ht₁ : T₁.hi<(438/125:ℝ) := by dsimp only [T₁]; envelope_reference
  exact ⟨P₀.mem.2.trans_lt hp₀,hp₁.trans_le P₁.mem.1,he₀.trans_le E₀.mem.1,
    E₁.mem.2.trans_lt he₁,ht₀.trans_le T₀.mem.1,T₁.mem.2.trans_lt ht₁⟩

lemma endpoint_product_bounds :
    (591/1000:ℝ)<h (3/100) ∧ h (3/100)<74/125 ∧
    (591/1000:ℝ)<h (3/20) ∧ h₁ (3/100)<21/200 ∧
    -(69/1000:ℝ)<h₁ (3/20) ∧ 0< marker (3/20) ∧ slopeRatio (3/20)<227/125 := by
  have hl : 0<r95_L.lo := by rw [r95_L_lo]; norm_num
  have hr : 0<r95_R.lo := by rw [r95_R_lo]; norm_num
  let P₀ := pBox (Interval.point (3/100)) r95_L hl
  let P₁ := pBox (Interval.point (3/20)) r95_R hr
  let E₀ := ellBox (Interval.point (3/100)) r95_L hl
  let E₁ := ellBox (Interval.point (3/20)) r95_R hr
  have hp : 0<P₁.lo := by dsimp only [P₁]; envelope_reference
  let H₀ := hBox (Interval.point (3/100)) P₀
  let H₁ := hBox (Interval.point (3/20)) P₁
  let J₀ := h₁Box (Interval.point (3/100)) P₀ E₀
  let J₁ := h₁Box (Interval.point (3/20)) P₁ E₁
  let M := markerBox P₁ E₁
  let K := slopeRatioBox P₁ E₁ hp
  have hH₀l : (591/1000:ℝ)<H₀.lo := by dsimp only [H₀,P₀]; envelope_reference
  have hH₀h : H₀.hi<(74/125:ℝ) := by dsimp only [H₀,P₀]; envelope_reference
  have hH₁ : (591/1000:ℝ)<H₁.lo := by dsimp only [H₁,P₁]; envelope_reference
  have hJ₀ : J₀.hi<(21/200:ℝ) := by dsimp only [J₀,P₀,E₀]; envelope_reference
  have hJ₁ : -(69/1000:ℝ)<J₁.lo := by dsimp only [J₁,P₁,E₁]; envelope_reference
  have hM : 0<M.lo := by dsimp only [M,P₁,E₁]; envelope_reference
  have hK : K.hi<(227/125:ℝ) := by dsimp only [K,P₁,E₁]; envelope_reference
  exact ⟨hH₀l.trans_le H₀.mem.1,H₀.mem.2.trans_lt hH₀h,hH₁.trans_le H₁.mem.1,
    J₀.mem.2.trans_lt hJ₀,hJ₁.trans_le J₁.mem.1,hM.trans_le M.mem.1,K.mem.2.trans_lt hK⟩

lemma continuation_endpoints :
    S (3/100)<LowerInverse.q (U 0) ∧ LowerInverse.q (U (3/5))<S (3/20) := by
  have hl : 0<r95_L.lo := by rw [r95_L_lo]; norm_num
  have hr : 0<r95_R.lo := by rw [r95_R_lo]; norm_num
  let P₀ := pBox (Interval.point (3/100)) r95_L hl
  let P₁ := pBox (Interval.point (3/20)) r95_R hr
  have hp₀ : 0<P₀.lo := by dsimp only [P₀]; envelope_reference
  have hp₁ : 0<P₁.lo := by dsimp only [P₁]; envelope_reference
  let S₀ := SBox (Interval.point (3/100)) P₀ hp₀
  let S₁ := SBox (Interval.point (3/20)) P₁ hp₁
  let Q₀ := qBox r95_Z
  let Q₁ := qBox r95_E
  have h₀ : S₀.hi<Q₀.lo := by dsimp only [S₀,P₀,Q₀]; envelope_reference
  have h₁ : Q₁.hi<S₁.lo := by dsimp only [S₁,P₁,Q₁]; envelope_reference
  exact ⟨S₀.mem.2.trans_lt (h₀.trans_le Q₀.mem.1),Q₁.mem.2.trans_lt (h₁.trans_le S₁.mem.1)⟩

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerEnvelope
