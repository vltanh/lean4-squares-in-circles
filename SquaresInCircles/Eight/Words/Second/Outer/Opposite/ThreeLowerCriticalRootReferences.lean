module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerFirstThird

/-!
# Eight squares: the two named scalar critical roots

The selector distinguishes only the two individual references `.495`
and `.5`.  Each root is located by exact endpoint comparisons in the
strictly increasing scalar equation, not by a cover of source states.
-/

section
/-!
## The target envelope of the reverse lower-secondary contact

The critical equation is the explicit scalar equation `S(B)=q(b)`.
Its envelope derivatives are defined and differentiated here without
assuming an inverse function or a stationary curve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerEnvelope
open CommonQuarter CorePairGeometry Arithmetic
open LowerInverse LowerGeometry

def p (B : ℝ) : ℝ := LLabel.d1 B
def ell (B : ℝ) : ℝ := LLabel.d2 B
def z (B : ℝ) : ℝ := B+1/2
def S (B : ℝ) : ℝ := (z B)^2+1/(p B)^2
def h (B : ℝ) : ℝ := z B*p B
def h₁ (B : ℝ) : ℝ := p B+z B*ell B
def h₂ (B : ℝ) : ℝ := 2*ell B+z B*LLabel.d3 B
def D (B : ℝ) : ℝ := z B-ell B/(p B)^3
def D₁ (B : ℝ) : ℝ := 1-LLabel.d3 B/(p B)^3+3*(ell B)^2/(p B)^4
def g₁ (B : ℝ) : ℝ := -h B/(2*S B)
def g₂ (B : ℝ) : ℝ := h B/(2*(S B)^2)-h₁ B/(4*S B*D B)
def g₃ (B : ℝ) : ℝ :=
  -h₂ B/(8*S B*(D B)^2)+h₁ B/(2*(S B)^2*D B)+
    h₁ B*D₁ B/(8*S B*(D B)^3)-h B/(S B)^3
def marker (B : ℝ) : ℝ := -ell B-(3/2)*p B
def slopeRatio (B : ℝ) : ℝ := -ell B/(p B)^2

lemma p_positive {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : 0<p B := by
  have hh := L_first_lower hB
  dsimp [p]
  linarith

lemma ell_negative {B : ℝ} (hB : B∈Icc 0 (83/200)) : ell B<0 := by
  have hh := L_second_early (show B∈Icc 0 (1/2) from ⟨hB.1,by linarith [hB.2]⟩)
  exact hh

lemma S_positive {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : 0<S B := by
  have hp := p_positive hB
  dsimp [S]
  positivity

lemma D_positive {B : ℝ} (hB : B∈Icc 0 (83/200)) : 0<D B := by
  have hp := p_positive (LowerFirst.short_domain hB)
  have he := ell_negative hB
  have hz : 0<z B := by dsimp [z]; linarith [hB.1]
  have hq : ell B/(p B)^3<0 := div_neg_of_neg_of_pos he (pow_pos hp 3)
  dsimp [D]
  linarith

lemma p_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : HasDerivAt p (ell B) B :=
  LLabel.d1_hasDerivAt (outer_domain hB)
lemma ell_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt ell (LLabel.d3 B) B := LLabel.d2_hasDerivAt (outer_domain hB)
lemma z_hasDerivAt (B : ℝ) : HasDerivAt z 1 B := (hasDerivAt_id B).add_const (1/2)

lemma S_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : HasDerivAt S (2*D B) B := by
  have hp := p_positive hB
  have hd := ((z_hasDerivAt B).pow 2).add
    ((hasDerivAt_const B (1:ℝ)).div ((p_hasDerivAt hB).pow 2) (pow_ne_zero 2 hp.ne'))
  convert hd using 1
  · rfl
  · dsimp [D]
    field_simp [hp.ne']
    ring

lemma h_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : HasDerivAt h (h₁ B) B := by
  have hd := (z_hasDerivAt B).mul (p_hasDerivAt hB)
  have e : h₁ B=1*p B+z B*ell B := by dsimp only [h₁]; ring
  rw [e]
  exact hd

lemma h₁_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : HasDerivAt h₁ (h₂ B) B := by
  have hd := (p_hasDerivAt hB).add ((z_hasDerivAt B).mul (ell_hasDerivAt hB))
  have e : h₂ B=ell B+(1*ell B+z B*LLabel.d3 B) := by dsimp only [h₂]; ring
  rw [e]
  exact hd

lemma D_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : HasDerivAt D (D₁ B) B := by
  have hp := p_positive hB
  have hd := (z_hasDerivAt B).sub
    ((ell_hasDerivAt hB).div ((p_hasDerivAt hB).pow 3) (pow_ne_zero 3 hp.ne'))
  convert hd using 1
  · rfl
  · dsimp [D₁]
    field_simp [hp.ne']
    ring

lemma g₁_hasDerivAt {B : ℝ} (hB : B∈Icc 0 (83/200)) :
    HasDerivAt g₁ (2*D B*g₂ B) B := by
  have hf := LowerFirst.short_domain hB
  have hs := S_positive hf
  have hd := D_positive hB
  convert (h_hasDerivAt hf).neg.div ((S_hasDerivAt hf).const_mul 2)
    (mul_ne_zero (by norm_num) hs.ne') using 1
  · rfl
  · dsimp [g₂]
    field_simp [hs.ne',hd.ne']
    ring

lemma g₂_hasDerivAt {B : ℝ} (hB : B∈Icc 0 (83/200)) :
    HasDerivAt g₂ (2*D B*g₃ B) B := by
  have hf := LowerFirst.short_domain hB
  have hs := S_positive hf
  have hd := D_positive hB
  have hleft := (h_hasDerivAt hf).div (((S_hasDerivAt hf).pow 2).const_mul 2)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hs.ne'))
  have hright := (h₁_hasDerivAt hf).div
    (((S_hasDerivAt hf).const_mul 4).mul (D_hasDerivAt hf))
    (mul_ne_zero (mul_ne_zero (by norm_num) hs.ne') hd.ne')
  convert hleft.sub hright using 1
  · rfl
  · dsimp [g₃]
    field_simp [hs.ne',hd.ne']
    ring

lemma marker_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt marker (-LLabel.d3 B-(3/2)*ell B) B := by
  exact (ell_hasDerivAt hB).neg.sub ((p_hasDerivAt hB).const_mul (3/2))

lemma slopeRatio_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt slopeRatio ((2*(ell B)^2-p B*LLabel.d3 B)/(p B)^3) B := by
  have hp := p_positive hB
  convert (ell_hasDerivAt hB).neg.div ((p_hasDerivAt hB).pow 2) (pow_ne_zero 2 hp.ne') using 1
  · rfl
  · simp only [Pi.neg_apply,Pi.pow_apply]
    field_simp [hp.ne']
    ring

lemma S_monotone : MonotoneOn S (Icc 0 (83/200)) :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => (S_hasDerivAt (LowerFirst.short_domain hB)).continuousAt.continuousWithinAt)
    (fun B hB => S_hasDerivAt (LowerFirst.short_domain (Ioo_subset_Icc_self hB)))
    (fun B hB => by linarith [D_positive (Ioo_subset_Icc_self hB)])

lemma p_antitone : AntitoneOn p (Icc 0 (83/200)) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hB => (p_hasDerivAt (LowerFirst.short_domain hB)).continuousAt.continuousWithinAt)
    (fun _ hB => p_hasDerivAt (LowerFirst.short_domain (Ioo_subset_Icc_self hB)))
    (fun _ hB => (ell_negative (Ioo_subset_Icc_self hB)).le)

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerEnvelope
end
end
end

section
/-!
## Exact arithmetic transport for the target envelope

These expressions retain the actual label and its circle radical.
They are used only at named endpoint and critical-root references.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerEnvelope
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open ReferenceAlgebra

def zBox {B : ℝ} (Y : Interval B) : Interval (z B) := Y.add (Interval.point (1/2))
def pBox {B : ℝ} (Y : Interval B) (X : Interval (U B)) (hX : 0<X.lo) : Interval (p B) :=
  firstBox LLabel Y X hX
def ellBox {B : ℝ} (Y : Interval B) (X : Interval (U B)) (hX : 0<X.lo) : Interval (ell B) :=
  secondBox LLabel Y X hX
def SBox {B : ℝ} (Y : Interval B) (P : Interval (p B)) (hP : 0<P.lo) : Interval (S B) :=
  (zBox Y).square.add ((Interval.point 1).div P.square (Interval.square_lo_pos hP))
def hBox {B : ℝ} (Y : Interval B) (P : Interval (p B)) : Interval (h B) := (zBox Y).mul P
def h₁Box {B : ℝ} (Y : Interval B) (P : Interval (p B)) (E : Interval (ell B)) : Interval (h₁ B) :=
  P.add ((zBox Y).mul E)
def markerBox {B : ℝ} (P : Interval (p B)) (E : Interval (ell B)) : Interval (marker B) :=
  E.neg.sub ((Interval.point (3/2)).mul P)
def slopeRatioBox {B : ℝ} (P : Interval (p B)) (E : Interval (ell B))
    (hP : 0<P.lo) : Interval (slopeRatio B) := E.neg.div P.square (Interval.square_lo_pos hP)
def DBox {B : ℝ} (Y : Interval B) (P : Interval (p B)) (E : Interval (ell B))
    (hP : 0<P.lo) : Interval (D B) := (zBox Y).sub (E.div P.cube (Interval.cube_lo_pos hP))
def g₁Box {B : ℝ} (H : Interval (h B)) (Q : Interval (S B)) (hQ : 0<Q.lo) : Interval (g₁ B) :=
  H.neg.div ((Interval.point 2).mul Q) (Interval.mul_lo_pos (by norm_num [Interval.point]) hQ)
def g₂Box {B : ℝ} (H : Interval (h B)) (H₁ : Interval (h₁ B))
    (Q : Interval (S B)) (D₀ : Interval (D B)) (hQ : 0<Q.lo) (hD : 0<D₀.lo) : Interval (g₂ B) :=
  (H.div ((Interval.point 2).mul Q.square)
    (Interval.mul_lo_pos (by norm_num [Interval.point]) (Interval.square_lo_pos hQ))).sub
    (H₁.div (((Interval.point 4).mul Q).mul D₀)
      (Interval.mul_lo_pos (Interval.mul_lo_pos (by norm_num [Interval.point]) hQ) hD))

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerEnvelope
end
end
end

section
/-!
## The two endpoints of the whole target-envelope interval

All comparisons are at `.03` or `.15`, and at the two source endpoints
needed to place their complete critical continuation.  There is no
cover of source or target coordinates.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerEnvelope
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

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerEnvelope
end
end
end

section
/-!
## Whole-interval shape of the target envelope

Monotonicity and concavity propagate the two endpoint substitutions
over the entire continued target interval.  The derivative estimates
retain the dependence between the target slope and its curvature.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerEnvelope
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)

lemma mem_short {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : B∈Icc 0 (83/200) :=
  ⟨by linarith [hB.1],by linarith [hB.2]⟩
lemma mem_outer {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : B∈Icc 0 outerDiagonal :=
  LowerFirst.short_domain (mem_short hB)

lemma label_bounds {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    (911/1000:ℝ)<p B ∧ p B<1117/1000 ∧
    -(191/100:ℝ)<ell B ∧ ell B< -(753/500:ℝ) ∧
    (129/40:ℝ)<LLabel.d3 B ∧ LLabel.d3 B<438/125 := by
  rcases endpoint_label_bounds with ⟨hp₀,hp₁,he₀,he₁,ht₀,ht₁⟩
  have hpL := p_antitone (by norm_num : (3/100:ℝ)∈Icc 0 (83/200)) (mem_short hB) hB.1
  have hpR := p_antitone (mem_short hB) (by norm_num : (3/20:ℝ)∈Icc 0 (83/200)) hB.2
  have heL := L_second_monotone (mem_outer (by norm_num : (3/100:ℝ)∈Icc (3/100) (3/20)))
    (mem_outer hB) hB.1
  have heR := L_second_monotone (mem_outer hB)
    (mem_outer (by norm_num : (3/20:ℝ)∈Icc (3/100) (3/20))) hB.2
  have htL := L_third_monotone (mem_outer (by norm_num : (3/100:ℝ)∈Icc (3/100) (3/20)))
    (mem_outer hB) hB.1
  have htR := L_third_monotone (mem_outer hB)
    (mem_outer (by norm_num : (3/20:ℝ)∈Icc (3/100) (3/20))) hB.2
  exact ⟨hp₁.trans_le hpR,hpL.trans_lt hp₀,he₀.trans_le heL,heR.trans_lt he₁,
    ht₀.trans_le htL,htR.trans_lt ht₁⟩

lemma product_second_bounds {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    -(264/125:ℝ)<h₂ B ∧ h₂ B< -(367/500:ℝ) := by
  rcases label_bounds hB with ⟨hp0,hp1,he0,he1,ht0,ht1⟩
  have hz : z B∈Icc (53/100:ℝ) (13/20) := by
    dsimp [z]
    constructor <;> linarith [hB.1,hB.2]
  let Z : Interval (z B) := Interval.of_bounds hz
  let E : Interval (ell B) := Interval.of_bounds ⟨he0.le,he1.le⟩
  let T : Interval (LLabel.d3 B) := Interval.of_bounds ⟨ht0.le,ht1.le⟩
  let H := ((Interval.point 2).mul E).add (Z.mul T)
  have hl : -(264/125:ℝ)<H.lo := by
    norm_num [H,E,Z,T,Interval.point,Interval.of_bounds,Interval.mul,Interval.add]
  have hh : H.hi< -(367/500:ℝ) := by
    norm_num [H,E,Z,T,Interval.point,Interval.of_bounds,Interval.mul,Interval.add]
  exact ⟨hl.trans_le H.mem.1,H.mem.2.trans_lt hh⟩

lemma product_first_antitone : AntitoneOn h₁ (Icc (3/100) (3/20)) :=
  antiOn_of_hasDeriv_nonpos
    (fun B hB => (h₁_hasDerivAt (mem_outer hB)).continuousAt.continuousWithinAt)
    (fun B hB => h₁_hasDerivAt (mem_outer (Ioo_subset_Icc_self hB)))
    (fun B hB => by linarith [(product_second_bounds (Ioo_subset_Icc_self hB)).2])

lemma product_first_bounds {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    -(69/1000:ℝ)<h₁ B ∧ h₁ B<21/200 := by
  have hl := product_first_antitone hB (by norm_num) hB.2
  have hh := product_first_antitone (by norm_num) hB hB.1
  rcases endpoint_product_bounds with ⟨_,_,_,hleft,hright,_,_⟩
  exact ⟨hright.trans_le hl,hh.trans_lt hleft⟩

lemma product_bounds {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    (591/1000:ℝ)<h B ∧ h B<121/200 := by
  have hconc : ConcaveOn ℝ (Icc (3/100) (3/20)) h :=
    concave_of_deriv2 (fun t ht => h_hasDerivAt (mem_outer ht))
      (fun t ht => h₁_hasDerivAt (mem_outer ht))
      (fun t ht => by linarith [(product_second_bounds ht).2])
  rcases endpoint_product_bounds with ⟨hl,hh,hr,_,_,_,_⟩
  have hlo := concave_gt_of_endpoints hconc hB hl hr
  have hd {t : ℝ} (ht : t∈Icc (3/100) (3/20)) :
      HasDerivAt (fun y => (21/200)*y-h y) (21/200-h₁ t) t :=
    (((hasDerivAt_id' t).const_mul (21/200)).fun_sub (h_hasDerivAt (mem_outer ht))).congr_deriv
      (by ring)
  have hm : MonotoneOn (fun y => (21/200)*y-h y) (Icc (3/100) (3/20)) :=
    monoOn_of_hasDeriv_nonneg (fun t ht => (hd ht).continuousAt.continuousWithinAt)
      (fun t ht => hd (Ioo_subset_Icc_self ht))
      (fun t ht => by linarith [(product_first_bounds (Ioo_subset_Icc_self ht)).2])
  have hmB := hm (by norm_num) hB hB.1
  exact ⟨hlo,by nlinarith [hB.2]⟩

lemma marker_positive {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : 0< marker B := by
  have hm : AntitoneOn marker (Icc (3/100) (3/20)) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro t ht
      exact (marker_hasDerivAt (mem_outer ht)).continuousAt.continuousWithinAt
    · intro t ht
      exact marker_hasDerivAt (mem_outer (Ioo_subset_Icc_self ht))
    · intro t ht
      rcases label_bounds (Ioo_subset_Icc_self ht) with ⟨_,_,he,_,hthird,_⟩
      linarith
  have hh := hm hB (by norm_num) hB.2
  rcases endpoint_product_bounds with ⟨_,_,_,_,_,hp,_⟩
  exact hp.trans_le hh

lemma S_bounds {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    (27/25:ℝ)<S B ∧ S B<163/100 := by
  have hp := label_bounds hB
  let P : Interval (p B) := Interval.of_bounds ⟨hp.1.le,hp.2.1.le⟩
  let Y : Interval B := Interval.of_bounds hB
  have hP : 0<P.lo := by norm_num [P,Interval.of_bounds]
  let Q := SBox Y P hP
  have hl : (27/25:ℝ)<Q.lo := by
    norm_num [Q,Y,P,SBox,zBox,Interval.of_bounds,Interval.point,Interval.add,
      Interval.square,Interval.mul,Interval.div,Interval.inv]
  have hh : Q.hi<(163/100:ℝ) := by
    norm_num [Q,Y,P,SBox,zBox,Interval.of_bounds,Interval.point,Interval.add,
      Interval.square,Interval.mul,Interval.div,Interval.inv]
  exact ⟨hl.trans_le Q.mem.1,Q.mem.2.trans_lt hh⟩

lemma D_large {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : (3/2)*S B<D B := by
  have hp := p_positive (mem_outer hB)
  have hm := marker_positive hB
  have hz : 0<z B ∧ z B<2/3 := by dsimp [z]; constructor <;> linarith [hB.1,hB.2]
  have he : D B-(3/2)*S B=z B*(1-(3/2)*z B)+marker B/(p B)^3 := by
    dsimp [D,S,marker]
    field_simp [hp.ne']
    ring
  have hfirst := mul_pos hz.1 (show 0<1-(3/2)*z B by linarith [hz.2])
  have hlast := div_pos hm (pow_pos hp 3)
  linarith

lemma curvature_square_bounds {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    p B*LLabel.d3 B<2*(ell B)^2 := by
  rcases label_bounds hB with ⟨hp0,hp1,he0,he1,ht0,ht1⟩
  have hp := mul_lt_mul'' hp1 ht1 (by linarith) (by linarith)
  have he : (753/500:ℝ)^2<(ell B)^2 := by nlinarith
  nlinarith

lemma slopeRatio_bound {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    0<slopeRatio B ∧ slopeRatio B<227/125 := by
  have hp := p_positive (mem_outer hB)
  have he := ell_negative (mem_short hB)
  have hlo : 0<slopeRatio B := by dsimp [slopeRatio]; exact div_pos (neg_pos.mpr he) (pow_pos hp 2)
  have hm : MonotoneOn slopeRatio (Icc (3/100) (3/20)) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (slopeRatio_hasDerivAt (mem_outer ht)).continuousAt.continuousWithinAt)
      (fun t ht => slopeRatio_hasDerivAt (mem_outer (Ioo_subset_Icc_self ht)))
      (fun t ht => div_nonneg (by linarith [curvature_square_bounds (Ioo_subset_Icc_self ht)])
        (pow_nonneg (p_positive (mem_outer (Ioo_subset_Icc_self ht))).le 3))
  have hh := hm hB (by norm_num) hB.2
  rcases endpoint_product_bounds with ⟨_,_,_,_,_,_,hhi⟩
  exact ⟨hlo,hh.trans_lt hhi⟩

lemma D_first_bounds {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : 0<D₁ B ∧ D₁ B<43/5 := by
  have hp := p_positive (mem_outer hB)
  have heq : D₁ B=1+(3*(ell B)^2-p B*LLabel.d3 B)/(p B)^4 := by
    dsimp [D₁]
    field_simp [hp.ne']
    ring
  have hnum : 0<3*(ell B)^2-p B*LLabel.d3 B := by
    nlinarith [curvature_square_bounds hB,sq_nonneg (ell B)]
  have hlo : 0<D₁ B := by rw [heq]; positivity
  have hd := label_bounds hB
  have hk := slopeRatio_bound hB
  let P : Interval (p B) := Interval.of_bounds ⟨hd.1.le,hd.2.1.le⟩
  let T : Interval (LLabel.d3 B) := Interval.of_bounds ⟨hd.2.2.2.2.1.le,hd.2.2.2.2.2.le⟩
  let K : Interval (slopeRatio B) := Interval.of_bounds ⟨hk.1.le,hk.2.le⟩
  have hP : 0<P.lo := by norm_num [P,Interval.of_bounds]
  let V := ((Interval.point 1).sub (T.div P.cube (Interval.cube_lo_pos hP))).add
    ((Interval.point 3).mul K.square)
  have hhi : V.hi<(43/5:ℝ) := by
    norm_num [V,T,P,K,Interval.of_bounds,Interval.point,Interval.sub,Interval.add,
      Interval.square,Interval.cube,Interval.mul,Interval.div,Interval.inv]
  have he : D₁ B=1-LLabel.d3 B/(p B)^3+3*(slopeRatio B)^2 := by
    dsimp [D₁,slopeRatio]
    field_simp [hp.ne']
  exact ⟨hlo,by rw [he]; exact V.mem.2.trans_lt hhi⟩

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerEnvelope
end
end
end

section
/-!
## An explicit parameterization of the reverse critical curve

The free target coordinate `B` is the parameter. The source coordinate `source B` is recovered
by the original circle radical from the scalar critical equation. This gives ordinary
derivatives (`first`, `second`, `third`) without an implicit inverse.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerCritical
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open LowerInverse LowerEnvelope

def height (B : ℝ) : ℝ := (Q0+1-S B)/2
def width (B : ℝ) : ℝ := Real.sqrt (Q0-(height B)^2)
def source (B : ℝ) : ℝ := width B-1/2
def sourceD (B : ℝ) : ℝ := height B*D B/width B
def Domain (B : ℝ) : Prop := B∈Icc (3/100) (3/20) ∧ source B∈Icc 0 (3/5)
def cost (B : ℝ) : ℝ := LowerContact.cost true B (source B)
def first (B : ℝ) : ℝ :=
  factor (U (source B))+2*ratio (source B)*g₁ B-TLabel.d1 (source B)
def second (B : ℝ) : ℝ :=
  -ratio (source B)*factorD (U (source B))+4*(ratio (source B))^2*g₂ B+
    2*ratioD (source B)*g₁ B-TLabel.d2 (source B)
def third (B : ℝ) : ℝ :=
  LowerInverse.X (source B)-TLabel.d3 (source B)+8*(ratio (source B))^3*g₃ B+
    12*ratio (source B)*ratioD (source B)*g₂ B+2*ratioDD (source B)*g₁ B

lemma height_bounds {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    (41/25:ℝ)<height B ∧ height B<193/100 := by
  have hh := S_bounds hB
  dsimp [height]
  norm_num [Q0]
  constructor <;> linarith

lemma width_data {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    0<width B ∧ (width B)^2+(height B)^2=Q0 := by
  have hu := height_bounds hB
  have hrad : 0<Q0-(height B)^2 := by norm_num [Q0]; nlinarith [hu.1,hu.2]
  exact ⟨Real.sqrt_pos.2 hrad,by dsimp [width]; rw [Real.sq_sqrt hrad.le]; ring⟩

lemma source_U {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : U (source B)=height B := by
  have hw := width_data hB
  have hu : 0<height B := by linarith [(height_bounds hB).1]
  have he : Q0-(width B)^2=(height B)^2 := by linarith
  calc
    U (source B)=Real.sqrt (Q0-(width B)^2) := by dsimp [U,arc,source]; ring_nf
    _=height B := by rw [he,Real.sqrt_sq_eq_abs,abs_of_pos hu]

lemma source_W (B : ℝ) : W (source B)=width B := by dsimp [W,source]; ring

lemma source_q {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : q (U (source B))=S B := by
  rw [source_U hB]
  dsimp [q,NegativeTwo.Inverse.q,height]
  ring

lemma height_hasDerivAt {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    HasDerivAt height (-D B) B := by
  have h := ((S_hasDerivAt (mem_outer hB)).const_sub (Q0+1)).div_const 2
  have hf : height = fun x => (Q0+1-S x)/2 := rfl
  rw [hf]
  convert h using 1
  ring

lemma source_hasDerivAt {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    HasDerivAt source (sourceD B) B := by
  have hw := width_data hB
  have hrad : Q0-(height B)^2≠0 := by nlinarith [hw.1,hw.2]
  convert ((((height_hasDerivAt hB).pow 2).const_sub Q0).sqrt hrad).sub_const (1/2)
    using 1
  · rfl
  · dsimp [sourceD,width]
    field_simp [show Real.sqrt (Q0-(height B)^2)≠0 from hw.1.ne']

lemma sourceD_positive {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : 0<sourceD B := by
  have hu : 0<height B := by linarith [(height_bounds hB).1]
  have hd := D_positive (mem_short hB)
  have hw := (width_data hB).1
  dsimp [sourceD]
  positivity

lemma source_strictMono : StrictMonoOn source (Icc (3/100) (3/20)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
  · intro B hB
    exact (source_hasDerivAt hB).continuousAt.continuousWithinAt
  · intro B hB
    exact (source_hasDerivAt (interior_subset hB)).hasDerivWithinAt
  · intro B hB
    exact sourceD_positive (interior_subset hB)

lemma source_monotone : MonotoneOn source (Icc (3/100) (3/20)) := source_strictMono.monotoneOn

lemma domain_between {l u B : ℝ} (hl : Domain l) (hu : Domain u) (hB : B∈Icc l u) : Domain B := by
  have ht : B∈Icc (3/100) (3/20) := ⟨hl.1.1.trans hB.1,hB.2.trans hu.1.2⟩
  exact ⟨ht,⟨hl.2.1.trans (source_monotone hl.1 ht hB.1),
    (source_monotone ht hu.1 hB.2).trans hu.2.2⟩⟩

lemma source_domain {B : ℝ} (hB : Domain B) : source B∈Icc 0 outerDiagonal :=
  LowerGeometry.full_domain ⟨hB.2.1,by linarith [hB.2.2]⟩

lemma shift_mem {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : z B∈LowerInverse.shifts := by
  dsimp [z,LowerInverse.shifts,OppositeTwo.PrimaryInverse.shifts]
  constructor <;> linarith [hB.1,hB.2]

lemma source_ratio_identity {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    ratio (source B)*sourceD B=D B := by
  have hu : 0<height B := by linarith [(height_bounds hB).1]
  have hw := (width_data hB).1
  change W (source B)/U (source B)*(height B*D B/width B)=D B
  rw [source_U hB,source_W]
  field_simp [hu.ne',hw.ne']

lemma source_eq_of_S {B b : ℝ} (hB : B∈Icc (3/100) (3/20))
    (hb : b∈Icc 0 (3/5)) (he : S B=q (U b)) : source B=b := by
  have hu : height B=U b := by
    dsimp [height]
    rw [he]
    dsimp [q,NegativeTwo.Inverse.q]
    ring
  have hw := width_data hB
  have hc := UW_circle (outer_domain (LowerGeometry.full_domain ⟨hb.1,by linarith [hb.2]⟩))
  rw [hu] at hw
  have hv : 0<W b := by dsimp [W]; linarith [hb.1]
  have hew : width B=W b := by nlinarith [hw.1,hw.2]
  dsimp [source]
  rw [hew]
  dsimp [W]
  ring

lemma critical_speed {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    LowerInverse.speed (z B) (source B)=1/p B := by
  have hp := p_positive (mem_outer hB)
  change Real.sqrt (q (U (source B))-(z B)^2)=1/p B
  rw [source_q hB]
  have he : S B-(z B)^2=(1/p B)^2 := by dsimp [S]; ring
  rw [he,Real.sqrt_sq_eq_abs,abs_of_pos (by positivity : 0<1/p B)]

lemma stationary {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    LowerContact.freeFirst true B (source B)=0 := by
  change 1/LowerInverse.speed (z B) (source B)-p B=0
  rw [critical_speed hB,one_div_one_div,sub_self]

lemma actual_first {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    LowerContact.outerFirst true B (source B)=first B := by
  have hp := p_positive (mem_outer hB)
  have hs := S_positive (mem_outer hB)
  change factor (U (source B))-z B*ratio (source B)/
    (q (U (source B))*LowerInverse.speed (z B) (source B))-TLabel.d1 (source B)=first B
  rw [critical_speed hB,source_q hB]
  dsimp [first,g₁,h]
  field_simp [hp.ne',hs.ne']
  ring

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerCritical
end
end
end

section
/-!
## Existence and location of the three critical-curve references

The scalar equation is solved by the intermediate value theorem on
the one complete target interval.  The chosen parameter is never
differentiated: all calculus belongs to the explicit source radical.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerCritical
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open LowerInverse LowerEnvelope

lemma q_monotone : MonotoneOn (fun b => q (U b)) (Icc 0 outerDiagonal) := by
  intro b hb B hB hle
  have hh := ShortOuterOne.SameContact.arc_antitone (outer_domain hb) (outer_domain hB) hle
  dsimp [q,NegativeTwo.Inverse.q,U]
  linarith

lemma exists_parameter {b : ℝ} (hb : b∈Icc 0 (3/5)) :
    ∃ B, B∈Icc (3/100) (3/20) ∧ S B=q (U b) := by
  have hbf := LowerGeometry.full_domain ⟨hb.1,by linarith [hb.2]⟩
  have hleft := q_monotone outer_zero_mem hbf hb.1
  have hright := q_monotone hbf
    (LowerGeometry.full_domain (by norm_num : (3/5:ℝ)∈Icc 0 (4/5))) hb.2
  have hc : ContinuousOn S (Icc (3/100) (3/20)) :=
    fun B hB => (S_hasDerivAt (mem_outer hB)).continuousAt.continuousWithinAt
  have he : q (U b)∈Icc (S (3/100)) (S (3/20)) :=
    ⟨(continuation_endpoints.1.trans_le hleft).le,(hright.trans_lt continuation_endpoints.2).le⟩
  obtain ⟨B,hB,hval⟩ := intermediate_value_Icc (by norm_num : (3/100:ℝ)≤3/20) hc he
  exact ⟨B,hB,hval⟩

def parameter (b : ℝ) (hb : b∈Icc 0 (3/5)) : ℝ := Classical.choose (exists_parameter hb)

lemma parameter_mem {b : ℝ} (hb : b∈Icc 0 (3/5)) : parameter b hb∈Icc (3/100) (3/20) :=
  (Classical.choose_spec (exists_parameter hb)).1
lemma parameter_equation {b : ℝ} (hb : b∈Icc 0 (3/5)) : S (parameter b hb)=q (U b) :=
  (Classical.choose_spec (exists_parameter hb)).2
lemma source_parameter {b : ℝ} (hb : b∈Icc 0 (3/5)) : source (parameter b hb)=b :=
  source_eq_of_S (parameter_mem hb) hb (parameter_equation hb)
lemma parameter_domain {b : ℝ} (hb : b∈Icc 0 (3/5)) : Domain (parameter b hb) :=
  ⟨parameter_mem hb,by rw [source_parameter hb]; exact hb⟩

lemma parameter_bracket {b l u : ℝ} (hb : b∈Icc 0 (3/5))
    (hl : l∈Icc (3/100) (3/20)) (hu : u∈Icc (3/100) (3/20))
    (hleft : S l<q (U b)) (hright : q (U b)<S u) :
    l<parameter b hb ∧ parameter b hb<u := by
  have hP := parameter_mem hb
  have he := parameter_equation hb
  constructor
  · by_contra hn
    have hm := S_monotone (mem_short hP) (mem_short hl) (le_of_not_gt hn)
    rw [he] at hm
    linarith
  · by_contra hn
    have hm := S_monotone (mem_short hu) (mem_short hP) (le_of_not_gt hn)
    rw [he] at hm
    linarith

def halfPoint : ℝ := parameter (1/2) (by norm_num)
def referencePoint : ℝ := parameter (99/200) (by norm_num)
def endPoint : ℝ := parameter (3/5) (by norm_num)

lemma half_domain : Domain halfPoint := parameter_domain (by norm_num)
lemma reference_domain : Domain referencePoint := parameter_domain (by norm_num)
lemma end_domain : Domain endPoint := parameter_domain (by norm_num)
lemma half_source : source halfPoint=(1/2:ℝ) := source_parameter (by norm_num)
lemma reference_source : source referencePoint=(99/200:ℝ) := source_parameter (by norm_num)
lemma end_source : source endPoint=(3/5:ℝ) := source_parameter (by norm_num)

lemma below_half_iff {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    B≤halfPoint ↔ source B≤1/2 := by
  constructor
  · intro hh
    have hm := source_monotone hB half_domain.1 hh
    rwa [half_source] at hm
  · intro hh
    by_contra hn
    have hm := source_strictMono half_domain.1 hB (lt_of_not_ge hn)
    rw [half_source] at hm
    linarith

lemma half_below_iff {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    halfPoint≤B ↔ 1/2≤ source B := by
  constructor
  · intro hh
    have hm := source_monotone half_domain.1 hB hh
    rwa [half_source] at hm
  · intro hh
    by_contra hn
    have hm := source_strictMono hB half_domain.1 (lt_of_not_ge hn)
    rw [half_source] at hm
    linarith

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerCritical
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerCritical
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

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerCritical
end
end
end
