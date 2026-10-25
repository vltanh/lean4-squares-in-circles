module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeSourcePrimary
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeUpperDiagonal

/-!
# Eight squares: bounds on the three complete lower-contact regimes

The intervals in this file are the three analytic regimes of the
minimum proof.  Every bound is transported from the actual shifted
circle; none is a cell of a coordinate cover.
-/

section
/-!
## Both original lower-secondary owners on their exact common contact domain

The contact domain `Domain` is the shifted-circle quarter disk. The two costs differ only in
which label, L or T, is assigned to its free coordinate. The original weak margins compare
directly with the inverse phase (`original_first_reduction`, `original_third_reduction`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerContact
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

def Domain (b B : ℝ) : Prop :=
  b∈Icc 0 outerDiagonal ∧ B∈Icc 0 outerDiagonal ∧ b≤arc B-1
def inner (reverse : Bool) : RoleLabel := if reverse then LLabel else TLabel
def outer (reverse : Bool) : RoleLabel := if reverse then TLabel else LLabel
def cost (reverse : Bool) (b B : ℝ) : ℝ :=
  Real.pi/2+LowerInverse.phase (b+1/2) B-(inner reverse).outer b-(outer reverse).outer B
def freeFirst (reverse : Bool) (b B : ℝ) : ℝ :=
  1/LowerInverse.speed (b+1/2) B-(inner reverse).d1 b
def outerFirst (reverse : Bool) (b B : ℝ) : ℝ :=
  LowerInverse.first (b+1/2) B-(outer reverse).d1 B
def freeSecond (reverse : Bool) (b B : ℝ) : ℝ :=
  (b+1/2)/(LowerInverse.speed (b+1/2) B)^3-(inner reverse).d2 b
def mixed (b B : ℝ) : ℝ := -ratio B/(LowerInverse.speed (b+1/2) B)^3
def outerSecond (reverse : Bool) (b B : ℝ) : ℝ :=
  LowerInverse.second (b+1/2) B-(outer reverse).d2 B
def outerThird (reverse : Bool) (b B : ℝ) : ℝ :=
  LowerInverse.third (b+1/2) B-(outer reverse).d3 B

lemma domain_bounds {b B : ℝ} (hd : Domain b B) :
    b<(83/200:ℝ) ∧ B≤bOne ∧ b+1/2∈LowerInverse.shifts := by
  have hA := NegativeTwo.primary_mem (ShortOuterOne.SameContact.arc_state hd.2.1)
  have hb : b<83/200 := by linarith [hd.2.2,hA.2,outer_endpoint_bounds.2.1]
  have hB : B≤bOne := below_bOne_of_primary_one
    (ShortOuterOne.SameContact.arc_state hd.2.1) (by linarith [hd.1.1,hd.2.2])
  exact ⟨hb,hB,⟨by linarith [hd.1.1],by linarith⟩⟩

lemma physical_speed {b B : ℝ} (hd : Domain b B) :
    W B≤LowerInverse.speed (b+1/2) B := by
  have hh := OppositeTwo.PrimaryInverse.data hd.2.1 (domain_bounds hd).2.2
  have hbase := NegativeTwo.ContactInverse.base_circle hd.2.1
  have hz : b+1/2≤U B-1 := by dsimp [U]; linarith [hd.2.2]
  have hnonneg : 0≤b+1/2 := by linarith [hd.1.1]
  have hw : 0<W B := by dsimp [W]; linarith [hd.2.1.1]
  nlinarith [hh.2.2.1,hh.2.2.2]

lemma cut_domain {b B x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10))
    (hcut : b≤lowerSecondary B x) : Domain b B := by
  have ht := positive_trig hx
  have hA := NegativeTwo.primary_mem (ShortOuterOne.SameContact.arc_state hB)
  have hcos := mul_le_mul_of_nonneg_left ht.2.1
    (show 0≤arc B-1/2 by linarith [hA.1,fine_outer_endpoint_bounds.2])
  have hsin := mul_nonneg (show 0≤B+1/2 by linarith [hB.1]) ht.2.2.1
  dsimp [lowerSecondary] at hcut
  exact ⟨hb,hB,by nlinarith⟩

lemma cost_free_hasDerivAt (reverse : Bool) {b B : ℝ}
    (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal)
    (hz : b+1/2∈LowerInverse.shifts) :
    HasDerivAt (fun t => cost reverse t B) (freeFirst reverse b B) b := by
  have hd := (LowerInverse.phase_shift_hasDerivAt hB hz).comp b
    ((hasDerivAt_id b).add_const (1/2))
  convert (((hd.const_add (Real.pi/2)).sub
    ((inner reverse).outer_hasDerivAt (outer_domain hb))).sub_const ((outer reverse).outer B))
    using 1 <;> dsimp [cost,freeFirst]
  ring

lemma cost_outer_hasDerivAt (reverse : Bool) {b B : ℝ}
    (hB : B∈Icc 0 outerDiagonal) (hz : b+1/2∈LowerInverse.shifts) :
    HasDerivAt (cost reverse b) (outerFirst reverse b B) B := by
  have hd := (((LowerInverse.phase_source_hasDerivAt hB hz).const_add (Real.pi/2)).sub_const
    ((inner reverse).outer b)).fun_sub ((outer reverse).outer_hasDerivAt (outer_domain hB))
  exact hd.congr_deriv (by simp only [outerFirst])

lemma freeFirst_free_hasDerivAt (reverse : Bool) {b B : ℝ}
    (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal)
    (hz : b+1/2∈LowerInverse.shifts) :
    HasDerivAt (fun t => freeFirst reverse t B) (freeSecond reverse b B) b := by
  have hd := ((LowerInverse.shift_second_hasDerivAt hB hz).comp b
    ((hasDerivAt_id' (x := b)).add_const (1/2))).fun_sub
      ((inner reverse).d1_hasDerivAt (outer_domain hb))
  exact hd.congr_deriv (by simp only [freeSecond]; ring)

lemma freeFirst_outer_hasDerivAt (reverse : Bool) {b B : ℝ}
    (hB : B∈Icc 0 outerDiagonal) (hz : b+1/2∈LowerInverse.shifts) :
    HasDerivAt (freeFirst reverse b) (mixed b B) B := by
  convert (LowerInverse.shift_source_hasDerivAt hB hz).sub_const ((inner reverse).d1 b)
    using 1 <;> rfl

lemma outerFirst_free_hasDerivAt (reverse : Bool) {b B : ℝ}
    (hB : B∈Icc 0 outerDiagonal) (hz : b+1/2∈LowerInverse.shifts) :
    HasDerivAt (fun t => outerFirst reverse t B) (mixed b B) b := by
  have hd := (LowerInverse.first_shift_hasDerivAt hB hz).comp b
    ((hasDerivAt_id b).add_const (1/2))
  convert hd.sub_const ((outer reverse).d1 B) using 1 <;>
    dsimp [outerFirst,mixed]
  ring

lemma outerFirst_outer_hasDerivAt (reverse : Bool) {b B : ℝ}
    (hB : B∈Icc 0 outerDiagonal) (hz : b+1/2∈LowerInverse.shifts) :
    HasDerivAt (outerFirst reverse b) (outerSecond reverse b B) B := by
  convert (LowerInverse.first_source_hasDerivAt hB hz).sub
    ((outer reverse).d1_hasDerivAt (outer_domain hB)) using 1 <;> rfl

lemma outerSecond_hasDerivAt (reverse : Bool) {b B : ℝ}
    (hB : B∈Icc 0 outerDiagonal) (hz : b+1/2∈LowerInverse.shifts) :
    HasDerivAt (outerSecond reverse b) (outerThird reverse b B) B := by
  convert (LowerInverse.second_source_hasDerivAt hB hz).sub
    ((outer reverse).d2_hasDerivAt (outer_domain hB)) using 1 <;> rfl

lemma aligned_lower (reverse : Bool) {b B : ℝ} (hd : Domain b B)
    (halign : b=arc B-1) : (44889/50000:ℝ)<cost reverse b B := by
  have hphase := LowerInverse.aligned hd.2.1 (z := b+1/2)
    (by dsimp [U]; linarith)
  have hs := ShortOuterOne.SameContact.arc_state hd.1
  have ht := ShortOuterOne.SameContact.arc_state hd.2.1
  cases reverse
  · have hh := aligned_first hs ht (by linarith)
    dsimp [cost,inner,outer,value,T,L] at *
    rw [hphase]
    linarith
  · have hh := aligned_last ht hs (by linarith)
    dsimp [cost,inner,outer,value,T,L] at *
    rw [hphase]
    linarith

theorem original_first_reduction {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) 1 (Real.pi/2-x)) :
    Domain b B ∧ cost false b B≤value b B (Real.pi/2-x) := by
  have hcut := lower_source_secondary ht hx hm
  have hd := cut_domain (NegativeTwo.source_mem hs) (NegativeTwo.source_mem ht) hx hcut
  have hf := LowerInverse.weak_phase hd.2.1 (domain_bounds hd).2.2 hx
    (by dsimp [lowerSecondary] at hcut; linarith)
  refine ⟨hd,?_⟩
  dsimp [cost,inner,outer,value,T,L]
  linarith

theorem original_third_reduction {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) 1 (Real.pi/2-x)) :
    Domain B b ∧ cost true B b≤value b B (Real.pi/2-x) := by
  have hcut := lower_target_secondary hs hx hm
  have hd := cut_domain (NegativeTwo.source_mem ht) (NegativeTwo.source_mem hs) hx hcut
  have hf := LowerInverse.weak_phase hd.2.1 (domain_bounds hd).2.2 hx
    (by dsimp [lowerSecondary] at hcut; linarith)
  refine ⟨hd,?_⟩
  dsimp [cost,inner,outer,value,T,L]
  linarith

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerContact
end
end
end

section
/-!
## Arithmetic transport for lower inverse formulas

Each enclosure carries a proof about its actual radical expression.
The operations below are used at named references or on one complete
analytic regime; there is no coordinate cover or sampled input.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerAlgebra
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open StationaryPrimitives (Interval)
open ReferenceAlgebra
open LowerInverse (q factor factorD factorDD)

def qBox {u : ℝ} (U : Interval u) : Interval (q u) :=
  (Interval.point (Q0+1)).sub ((Interval.point 2).mul U)

def factorBox {u : ℝ} (U : Interval u) (Q : Interval (q u))
    (hU : 0<U.lo) (hQ : 0<Q.lo) : Interval (factor u) :=
  ((Interval.point Q0).sub U).div (U.mul Q) (Interval.mul_lo_pos hU hQ)

def factorDBox {u : ℝ} (U : Interval u) (Q : Interval (q u))
    (hU : 0<U.lo) (hQ : 0<Q.lo) : Interval (factorD u) := by
  let N := (((Interval.point (4*Q0)).mul U).sub
    ((Interval.point 2).mul U.square)).sub (Interval.point (Q0*(Q0+1)))
  exact N.div (U.square.mul Q.square)
    (Interval.mul_lo_pos (Interval.square_lo_pos hU) (Interval.square_lo_pos hQ))

def factorDDBox {u : ℝ} (U : Interval u) (Q : Interval (q u))
    (hU : 0<U.lo) (hQ : 0<Q.lo) : Interval (factorDD u) := by
  let C := Interval.point (Q0+1)
  have hC : 0<C.lo := by norm_num [C,Interval.point,Q0]
  exact ((Interval.point (2*Q0)).div (C.mul U.cube)
    (Interval.mul_lo_pos hC (Interval.cube_lo_pos hU))).add
      ((Interval.point (8*(Q0-1))).div (C.mul Q.cube)
        (Interval.mul_lo_pos hC (Interval.cube_lo_pos hQ)))

def A1Box {y : ℝ} (R : Interval (ratio y)) (D : Interval (ratioD y))
    (DD : Interval (ratioDD y)) (Q : Interval (q (U y))) (hQ : 0<Q.lo) :
    Interval (LowerInverse.A1 y) := by
  let Z := ((((Interval.point 9).mul R).mul D).div Q.square (Interval.square_lo_pos hQ)).sub
    (((Interval.point 15).mul R.cube).div Q.cube (Interval.cube_lo_pos hQ))
  exact Z.sub (DD.div Q hQ)

def A3Box {y : ℝ} (R : Interval (ratio y)) (D : Interval (ratioD y))
    (Q : Interval (q (U y))) (hQ : 0<Q.lo) : Interval (LowerInverse.A3 y) :=
  ((((Interval.point 3).mul R).mul D).div Q.square (Interval.square_lo_pos hQ)).sub
    (((Interval.point 10).mul R.cube).div Q.cube (Interval.cube_lo_pos hQ))

def speedBox {z y : ℝ} (Z : Interval z) (Q : Interval (q (U y)))
    (s : ℝ) (hs : 0<s) (hr : 0≤(Q.sub Z.square).lo) : Interval (LowerInverse.speed z y) :=
  rootThree (Q.sub Z.square) s hs hr

def inverseFirstBox {z y : ℝ} (Z : Interval z) (X : Interval (U y))
    (R : Interval (ratio y)) (Q : Interval (q (U y)))
    (V : Interval (LowerInverse.speed z y))
    (hX : 0<X.lo) (hQ : 0<Q.lo) (hV : 0<V.lo) : Interval (LowerInverse.first z y) :=
  (factorBox X Q hX hQ).sub ((Z.mul R).div (Q.mul V) (Interval.mul_lo_pos hQ hV))

def inverseSecondBox {z y : ℝ} (Z : Interval z) (X : Interval (U y))
    (R : Interval (ratio y)) (D : Interval (ratioD y)) (Q : Interval (q (U y)))
    (V : Interval (LowerInverse.speed z y))
    (hX : 0<X.lo) (hQ : 0<Q.lo) (hV : 0<V.lo) : Interval (LowerInverse.second z y) := by
  let C := (D.sub (((Interval.point 2).mul R.square).div Q hQ)).sub
    (R.square.div V.square (Interval.square_lo_pos hV))
  let W := ((R.mul (factorDBox X Q hX hQ)).neg).sub
    ((Z.div (Q.mul V) (Interval.mul_lo_pos hQ hV)).mul C)
  refine ⟨W.lo,W.hi,?_⟩
  have h : LowerInverse.second z y=-(ratio y*factorD (U y))-
      z/(q (U y)*LowerInverse.speed z y)*
        (ratioD y-2*ratio y^2/q (U y)-ratio y^2/LowerInverse.speed z y^2) := by
    simp only [LowerInverse.second,NegativeTwo.Inverse.brace,ratioD,U]
    ring
  rw [h]
  exact W.mem

def freeFirstBox (reverse : Bool) {b B : ℝ} (Y : Interval b) (X : Interval (U b))
    (V : Interval (LowerInverse.speed (b+1/2) B)) (hX : 0<X.lo) (hV : 0<V.lo) :
    Interval (LowerContact.freeFirst reverse b B) :=
  ((Interval.point 1).div V hV).sub (ReferenceAlgebra.firstBox (LowerContact.inner reverse) Y X hX)

def outerFirstBox (reverse : Bool) {b B : ℝ}
    (Z : Interval (b+1/2)) (Y : Interval B) (X : Interval (U B))
    (V : Interval (LowerInverse.speed (b+1/2) B))
    (hX : 0<X.lo) (hQ : 0<(qBox X).lo) (hV : 0<V.lo) :
    Interval (LowerContact.outerFirst reverse b B) :=
  (inverseFirstBox Z X (ratioBox Y X hX) (qBox X) V hX hQ hV).sub
    (ReferenceAlgebra.firstBox (LowerContact.outer reverse) Y X hX)

def outerSecondBox (reverse : Bool) {b B : ℝ}
    (Z : Interval (b+1/2)) (Y : Interval B) (X : Interval (U B))
    (V : Interval (LowerInverse.speed (b+1/2) B))
    (hX : 0<X.lo) (hQ : 0<(qBox X).lo) (hV : 0<V.lo) :
    Interval (LowerContact.outerSecond reverse b B) :=
  (inverseSecondBox Z X (ratioBox Y X hX) (ratioDBox X hX) (qBox X) V hX hQ hV).sub
    (ReferenceAlgebra.secondBox (LowerContact.outer reverse) Y X hX)

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerAlgebra
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerGeometry
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open StationaryPrimitives (Interval)
open ReferenceAlgebra LowerAlgebra LowerInverse

lemma full_domain {y : ℝ} (hy : y∈Icc 0 (4/5)) : y∈Icc 0 outerDiagonal :=
  ⟨hy.1,by linarith [hy.2,fine_outer_endpoint_bounds.2]⟩

lemma shifted_range {y l h u v : ℝ} (hy : y∈Icc 0 outerDiagonal)
    (hyl : l≤y) (hyh : y≤h) (hl : 0≤l+1/2) (hu : 0≤u) (hv : 0<v)
    (hlo : u^2+(h+1/2)^2<Q0) (hhi : Q0<v^2+(l+1/2)^2) :
    u<U y ∧ U y<v := by
  have hc := UW_circle (outer_domain hy)
  have hp := U_positive (outer_domain hy)
  have hwlo : l+1/2≤W y := by dsimp [W]; linarith
  have hwhi : W y≤h+1/2 := by dsimp [W]; linarith
  have hwslo := mul_self_le_mul_self hl hwlo
  have hwshi := mul_self_le_mul_self (hl.trans hwlo) hwhi
  constructor <;> nlinarith

lemma early_U {y : ℝ} (hy : y∈Icc 0 (2/5)) :
    (881/500:ℝ)<U y ∧ U y<383/200 :=
  shifted_range (full_domain ⟨hy.1,by linarith [hy.2]⟩) hy.1 hy.2
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Q0]) (by norm_num [Q0])

lemma middle_U {y : ℝ} (hy : y∈Icc (2/5) (1/2)) :
    (1707/1000:ℝ)<U y ∧ U y<1763/1000 :=
  shifted_range (full_domain ⟨by linarith [hy.1],by linarith [hy.2]⟩) hy.1 hy.2
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Q0]) (by norm_num [Q0])

lemma late_U {b y : ℝ} (hd : LowerContact.Domain b y) (hy : 1/2≤y) :
    (3/2:ℝ)≤U y ∧ U y<427/250 := by
  have hlo : (3/2:ℝ)≤U y := by dsimp [U]; linarith [hd.1.1,hd.2.2]
  have hc := UW_circle (outer_domain hd.2.1)
  have hw : 1≤W y := by dsimp [W]; linarith
  norm_num [Q0] at hc
  exact ⟨hlo,by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤1) hw]⟩

private lemma r62_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl
private lemma r62_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r62_ratioDD_eq {y : ℝ} : ratioDD y = 3*Q0*(y+1/2)/((U y)^3*(U y)^2) := by
  dsimp [ratioDD,U]; ring
private lemma r62_ratioDDBox_lo {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDDBox Y X hX).lo = (((Interval.point (3*Q0)).mul (Y.add (Interval.point (1/2)))).div
      (X.cube.mul X.square)
      (Interval.mul_lo_pos (Interval.cube_lo_pos hX) (Interval.square_lo_pos hX))).lo :=
  r62_mpr_lo r62_ratioDD_eq (congrArg _ r62_ratioDD_eq) _
private lemma r62_ratioDDBox_hi {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDDBox Y X hX).hi = (((Interval.point (3*Q0)).mul (Y.add (Interval.point (1/2)))).div
      (X.cube.mul X.square)
      (Interval.mul_lo_pos (Interval.cube_lo_pos hX) (Interval.square_lo_pos hX))).hi :=
  r62_mpr_hi r62_ratioDD_eq (congrArg _ r62_ratioDD_eq) _

local macro "lower_bounds" : tactic => `(tactic|
  norm_num [ratioBox,ratioDBox,r62_ratioDDBox_lo,r62_ratioDDBox_hi,qBox,factorDBox,factorDDBox,
    A1Box,A3Box,Interval.point,Interval.of_bounds,Interval.add,Interval.sub,
    Interval.neg,Interval.mul,Interval.square,Interval.cube,Interval.inv,
    Interval.div,Q0])

lemma early_data {y : ℝ} (hy : y∈Icc 0 (2/5)) :
    (261/1000:ℝ)<ratio y ∧ ratio y<511/1000 ∧
    (557/1000:ℝ)<ratioD y ∧ ratioD y<179/250 ∧
    (57/250:ℝ)<ratioDD y ∧ (1357/1250:ℝ)<q (U y) ∧
      q (U y)<3479/2500 ∧ 0≤factorD (U y) := by
  let Y : Interval y := Interval.of_bounds hy
  let X : Interval (U y) := Interval.of_bounds ⟨(early_U hy).1.le,(early_U hy).2.le⟩
  have hX : 0<X.lo := by dsimp only [X]; lower_bounds
  let R := ratioBox Y X hX
  let D := ratioDBox X hX
  let DD := ratioDDBox Y X hX
  let Q := qBox X
  have hQ : 0<Q.lo := by dsimp only [Q,X]; lower_bounds
  let F := factorDBox X Q hX hQ
  have hr0 : (261/1000:ℝ)<R.lo := by dsimp only [R,X,Y]; lower_bounds
  have hr1 : R.hi<(511/1000:ℝ) := by dsimp only [R,X,Y]; lower_bounds
  have hd0 : (557/1000:ℝ)<D.lo := by dsimp only [D,X]; lower_bounds
  have hd1 : D.hi<(179/250:ℝ) := by dsimp only [D,X]; lower_bounds
  have hdd : (57/250:ℝ)<DD.lo := by dsimp only [DD,X,Y]; lower_bounds
  have hf : 0≤F.lo := by dsimp only [F,Q,X]; lower_bounds
  have hq0 : (1357/1250:ℝ)<q (U y) := by
    have hu := (early_U hy).2
    norm_num [q,NegativeTwo.Inverse.q,Q0]
    linarith
  have hq1 : q (U y)<(3479/2500:ℝ) := by
    have hu := (early_U hy).1
    norm_num [q,NegativeTwo.Inverse.q,Q0]
    linarith
  exact ⟨hr0.trans_le R.mem.1,R.mem.2.trans_lt hr1,
    hd0.trans_le D.mem.1,D.mem.2.trans_lt hd1,hdd.trans_le DD.mem.1,
    hq0,hq1,hf.trans F.mem.1⟩

lemma third_upper {z y a c e t : ℝ}
    (hx : X y≤a) (hA : A1 y≤c) (hB : A3 y≤e)
    (hr : 0≤ratio y) (hq : 0<q (U y))
    (ht : 0≤quotient z y) (htt : quotient z y≤t) (hc : 0≤c) (he : 0≤e) :
    third z y≤a+c*t+e*t^3 := by
  have ht3 := pow_le_pow_left₀ ht htt 3
  have hct := (mul_le_mul_of_nonneg_right hA ht).trans
    (mul_le_mul_of_nonneg_left htt hc)
  have het := (mul_le_mul_of_nonneg_right hB (pow_nonneg ht 3)).trans
    (mul_le_mul_of_nonneg_left ht3 he)
  have hlast : 0≤3*(ratio y)^3/(q (U y))^3*(quotient z y)^5 := by positivity
  dsimp [third]
  linarith

lemma early_third_terms {y : ℝ} (hy : y∈Icc 0 (2/5)) :
    X y<(209/200:ℝ) ∧ A1 y<633/250 ∧ A3 y<433/500 := by
  have h := early_data hy
  let R : Interval (ratio y) := Interval.of_bounds ⟨h.1.le,h.2.1.le⟩
  let D : Interval (ratioD y) := Interval.of_bounds ⟨h.2.2.1.le,h.2.2.2.1.le⟩
  let U₀ : Interval (U y) := Interval.of_bounds ⟨(early_U hy).1.le,(early_U hy).2.le⟩
  let Q : Interval (q (U y)) := Interval.of_bounds ⟨h.2.2.2.2.2.1.le,h.2.2.2.2.2.2.1.le⟩
  have hU : 0<U₀.lo := by dsimp only [U₀]; lower_bounds
  have hQ : 0<Q.lo := by dsimp only [Q]; lower_bounds
  let DD₀ := ratioDDBox (Interval.of_bounds hy) U₀ hU
  have hDD : DD₀.hi≤(1:ℝ) := by dsimp only [DD₀,U₀]; lower_bounds
  let DD : Interval (ratioDD y) :=
    Interval.of_bounds ⟨h.2.2.2.2.1.le,DD₀.mem.2.trans hDD⟩
  let XX := R.square.mul (factorDDBox U₀ Q hU hQ)
  let AA := A1Box R D DD Q hQ
  let BB := A3Box R D Q hQ
  have hx : XX.hi<(209/200:ℝ) := by dsimp only [XX,R,U₀,Q]; lower_bounds
  have hA : AA.hi<(633/250:ℝ) := by dsimp only [AA,R,D,DD,Q]; lower_bounds
  have hB : BB.hi<(433/500:ℝ) := by dsimp only [BB,R,D,Q]; lower_bounds
  have hxle : X y≤(ratio y)^2*factorDD (U y) := by
    dsimp [X]
    have hp := mul_nonneg (by linarith [h.2.2.1] : (0:ℝ)≤ratioD y) h.2.2.2.2.2.2.2
    linarith
  exact ⟨hxle.trans_lt (XX.mem.2.trans_lt hx),AA.mem.2.trans_lt hA,BB.mem.2.trans_lt hB⟩

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerGeometry
end
end
end
