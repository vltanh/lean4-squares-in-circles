module

public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.SourceThreeMinimumPolynomials
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.TargetTwoCornerReferences

/-!
# Eight squares: every original lower transverse negative-core owner

The exact small-target minimum and the large-target aligned deformation
cover the complete physical arc. The contact inequality is used only to
compare with the original source and target, including all weak ties.
-/

section
/-!
## Exact reference algebra for the negative-core minimum

Every enclosure remains attached to its actual real expression. Circle
heights and stationary roots use integer-square comparisons. Arctangent
arguments are first rounded outwards to explicit rational endpoints;
the proved alternating polynomials are evaluated only at those points.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum.References
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open OppositeThree.ReferenceAlgebra

def widen {x : ℝ} (X : Interval x) (l u : ℝ) (hl : l≤X.lo) (hu : X.hi≤u) : Interval x :=
  ⟨l,u,hl.trans X.mem.1,X.mem.2.trans hu⟩

def heightBox {B : ℝ} (hB : B∈targets) (l u : ℝ) (hl : 0≤l) (hu : 0≤u)
    (hlo : l^2+(B+1/2)^2<Q0) (hhi : Q0<u^2+(B+1/2)^2) : Interval (U B) := by
  have hh := shifted_chart_reference (outer_domain (target_domain hB)) hl hu hlo hhi
  exact Interval.of_bounds ⟨hh.1.le,hh.2.le⟩

def tBox {B : ℝ} (X : Interval (U B)) : Interval (T B) :=
  (Interval.point (Q0+1)).sub ((Interval.point 2).mul X)

def vBox {B : ℝ} (Y : Interval B) : Interval (V B) := Y.add (Interval.point (1/2))

def stationaryBox {h B : ℝ} (hh : h∈slopes) (hB : B∈targets)
    (X : Interval (U B)) (l u : ℝ) (hl : 0≤l) (hu : 0≤u)
    (hlo : l^2<h^2*(Q0+1-2*X.hi)-1)
    (hhi : h^2*(Q0+1-2*X.lo)-1<u^2) : Interval (S h B) := by
  have hs := S_positive hh hB
  have hsq := S_sq hh hB
  have hp := mul_nonneg (sq_nonneg h) (show 0≤X.hi-U B by linarith [X.mem.2])
  have hq := mul_nonneg (sq_nonneg h) (show 0≤U B-X.lo by linarith [X.mem.1])
  dsimp [T] at hsq
  exact ⟨l,u,by nlinarith,by nlinarith⟩

def arg (B : ℝ) : ℝ := (V B-P B)/(V B+P B)

lemma phase_identity {B : ℝ} (hB : B∈targets) : beta B=Real.pi/4+Real.arctan (arg B) := by
  have hv : 0≤V B := by dsimp [V]; linarith [hB.1]
  have hh := CoreAngleEndpoint.arctan_complement (P_positive hB) hv
  have hid : (P B-V B)/(P B+V B)= -arg B := by dsimp [arg]; ring
  rw [hid,Real.arctan_neg] at hh
  dsimp [beta]
  linarith

def argumentBox {B : ℝ} (Y : Interval B) (X : Interval (U B))
    (hden : 0<((vBox Y).add (X.sub (Interval.point 1))).lo) : Interval (arg B) :=
  ((vBox Y).sub (X.sub (Interval.point 1))).div
    ((vBox Y).add (X.sub (Interval.point 1))) hden

def atanLo (x : ℝ) : ℝ := if 0≤x then atanLower x else -atanUpper (-x)
def atanHi (x : ℝ) : ℝ := if 0≤x then atanUpper x else -atanLower (-x)

lemma atanLo_le (x : ℝ) : atanLo x≤Real.arctan x := by
  by_cases hx : 0≤x
  · simpa [atanLo,hx] using atanLower_le hx
  · have hh := arctan_le_atanUpper (show 0≤ -x by linarith)
    rw [Real.arctan_neg] at hh
    dsimp [atanLo]
    rw [ite_eq_right hx]
    linarith

lemma le_atanHi (x : ℝ) : Real.arctan x≤atanHi x := by
  by_cases hx : 0≤x
  · simpa [atanHi,hx] using arctan_le_atanUpper hx
  · have hh := atanLower_le (show 0≤ -x by linarith)
    rw [Real.arctan_neg] at hh
    dsimp [atanHi]
    rw [ite_eq_right hx]
    linarith

def atanBox {x : ℝ} (X : Interval x) : Interval (Real.arctan x) :=
  ⟨atanLo X.lo,atanHi X.hi,
    (atanLo_le X.lo).trans (Real.arctan_strictMono.monotone X.mem.1),
    (Real.arctan_strictMono.monotone X.mem.2).trans (le_atanHi X.hi)⟩

def betaBox {B : ℝ} (hB : B∈targets) (A : Interval (arg B)) : Interval (beta B) := by
  let H := (piBox.div (Interval.point 4) (by norm_num [Interval.point])).add (atanBox A)
  exact ⟨H.lo,H.hi,by rw [phase_identity hB]; exact H.mem⟩

def baseBox {B : ℝ} (X : Interval (U B)) : Interval (baseE (U B)) :=
  (((Interval.point 2).mul X.square).sub ((Interval.point (4*Q0)).mul X)).add
    (Interval.point (Q0*(Q0+1)))

def phaseFirstBox {B : ℝ} (X : Interval (U B)) (hX : 0<X.lo)
    (hT : 0<(tBox X).lo) : Interval (betaD B) :=
  ((Interval.point Q0).sub X).div (X.mul (tBox X)) (Interval.mul_lo_pos hX hT)

def phaseSecondBox {B : ℝ} (Y : Interval B) (X : Interval (U B)) (hX : 0<X.lo)
    (hT : 0<(tBox X).lo) : Interval (betaDD B) :=
  ((baseBox X).mul (vBox Y)).div (X.cube.mul (tBox X).square)
    (Interval.mul_lo_pos (Interval.cube_lo_pos hX) (Interval.square_lo_pos hT))

def stationaryFirstBox {h B : ℝ} (Y : Interval B) (X : Interval (U B)) (W : Interval (S h B))
    (hX : 0<X.lo) (hT : 0<(tBox X).lo) : Interval (R h B) :=
  ((ratioBox Y X hX).mul W).div (tBox X) hT

def stationarySecondBox {h B : ℝ} (Y : Interval B) (X : Interval (U B)) (W : Interval (S h B))
    (hX : 0<X.lo) (hT : 0<(tBox X).lo) (hW : 0<W.lo) : Interval (RD h B) :=
  ((((ratioDBox X hX).mul W).div (tBox X) hT).add
    (((Interval.point (h^2)).mul (ratioBox Y X hX).square).div (W.mul (tBox X))
      (Interval.mul_lo_pos hW hT))).sub
        ((((Interval.point 2).mul (ratioBox Y X hX).square).mul W).div (tBox X).square
          (Interval.square_lo_pos hT))

def valueBox {h B : ℝ} (Y : Interval B) (X : Interval (U B))
    (W : Interval (S h B)) (A : Interval (beta B)) : Interval (E h B) :=
  ((((((A.add (atanBox W)).sub W).sub (Interval.point e)).sub
    (Interval.point (epsilon h))).add (Interval.point (h/2))).sub (labelBox LLabel Y X))

def firstBox {h B : ℝ} (Y : Interval B) (X : Interval (U B)) (W : Interval (S h B))
    (hX : 0<X.lo) (hT : 0<(tBox X).lo) : Interval (E1 h B) :=
  (((phaseFirstBox X hX hT).sub (stationaryFirstBox Y X W hX hT)).sub
    (OppositeThree.ReferenceAlgebra.firstBox LLabel Y X hX))

def secondBox {h B : ℝ} (Y : Interval B) (X : Interval (U B)) (W : Interval (S h B))
    (hX : 0<X.lo) (hT : 0<(tBox X).lo) (hW : 0<W.lo) : Interval (E2 h B) :=
  (((phaseSecondBox Y X hX hT).sub (stationarySecondBox Y X W hX hT hW)).sub
    (OppositeThree.ReferenceAlgebra.secondBox LLabel Y X hX))

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum.References
end
end
end

section
/-!
## Six named references for the exact negative-core minimum

Every decimal endpoint below is an exact rational. Height and stationary
radical cages follow from their squared endpoints. Arctangent arguments
have outward rational cages before their proved alternating sums are
used. These are references for continuous derivative arguments, not a
subdivision of the target domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum.References
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open OppositeThree.ReferenceAlgebra

private lemma r61_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r61_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl
private lemma r61_coordinate_eq {y : ℝ} : ShortOuterOne.SameContact.arc y = U y-1/2 := by
  dsimp [U]; ring
private lemma r61_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r61_mpr_lo r61_coordinate_eq (congrArg _ r61_coordinate_eq) _
private lemma r61_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r61_mpr_hi r61_coordinate_eq (congrArg _ r61_coordinate_eq) _
private lemma r61_label_eq (H : RoleLabel) {y : ℝ} :
    H.outer y = H.c+H.p*(ShortOuterOne.SameContact.arc y)+H.q*y+H.r*y^2+
      H.s*(ShortOuterOne.SameContact.arc y*y) := by
  dsimp [RoleLabel.outer,RoleLabel.eval]; ring
private lemma r61_labelBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).lo = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).lo :=
  r61_mpr_lo (r61_label_eq H) (congrArg _ (r61_label_eq H)) _
private lemma r61_labelBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).hi = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).hi :=
  r61_mpr_hi (r61_label_eq H) (congrArg _ (r61_label_eq H)) _

local macro "reference_arithmetic" : tactic => `(tactic|
  norm_num [heightBox,stationaryBox,widen,argumentBox,betaBox,atanBox,atanLo,atanHi,
    valueBox,firstBox,secondBox,phaseFirstBox,phaseSecondBox,stationaryFirstBox,
    stationarySecondBox,baseBox,tBox,vBox,piBox,ratioBox,ratioDBox,
    r61_labelBox_lo,r61_labelBox_hi,r61_coordinate_lo,r61_coordinate_hi,
    OppositeThree.ReferenceAlgebra.firstBox,OppositeThree.ReferenceAlgebra.secondBox,
    epsilon,e,g,z,EdgeThreeAligned.en,EdgeThreeAligned.gn,EdgeThreeAligned.zn,
    LPrimaryZero.e,LLabel,RoleLabel.eval,Q0,atanLower,atanUpper,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.inv,Interval.div])

lemma minimum_reference : (89776733/100000000:ℝ)<E g (607/2000) ∧ |E1 g (607/2000)|<(3/500000:ℝ) := by
  have hB : (607/2000:ℝ)∈targets := by norm_num [targets]
  let Y := Interval.point (607/2000:ℝ)
  let X := heightBox hB (1808310744866600/1000000000000000) (1808310744866601/1000000000000000)
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  let W := stationaryBox first_slope hB X (508665829398/1000000000000) (508665829399/1000000000000)
    (by norm_num) (by norm_num)
    (by dsimp [X]; reference_arithmetic) (by dsimp [X]; reference_arithmetic)
  have hX : 0<X.lo := by dsimp [X]; reference_arithmetic
  have hT : 0<(tBox X).lo := by dsimp [X]; reference_arithmetic
  have hW : 0<W.lo := by dsimp [W]; reference_arithmetic
  let A₀ := argumentBox Y X (by dsimp [Y,X]; reference_arithmetic)
  let A := widen A₀ (-2984683458/1000000000000) (-2984683457/1000000000000)
    (by dsimp [A₀,Y,X]; reference_arithmetic) (by dsimp [A₀,Y,X]; reference_arithmetic)
  let V := valueBox Y X W (betaBox hB A)
  let F := firstBox Y X W hX hT
  have h0 : (89776733/100000000:ℝ)<V.lo := by dsimp [V,A,A₀,W,Y,X]; reference_arithmetic
  have h1 : -(3/500000:ℝ)<F.lo := by dsimp [F,W,Y,X]; reference_arithmetic
  have h2 : F.hi<(3/500000:ℝ) := by dsimp [F,W,Y,X]; reference_arithmetic
  exact ⟨h0.trans_le V.mem.1,abs_lt.mpr ⟨h1.trans_le F.mem.1,F.mem.2.trans_lt h2⟩⟩

lemma early_terminal : (4489/5000:ℝ)<E g (8/25) ∧ 0<E1 g (8/25) ∧ (11/50:ℝ)<E2 g (8/25) := by
  have hB : (8/25:ℝ)∈targets := by norm_num [targets]
  let Y := Interval.point (8/25:ℝ)
  let X := heightBox hB (1800888669518468/1000000000000000) (1800888669518469/1000000000000000)
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  let W := stationaryBox first_slope hB X (522613872198/1000000000000) (522613872199/1000000000000)
    (by norm_num) (by norm_num)
    (by dsimp [X]; reference_arithmetic) (by dsimp [X]; reference_arithmetic)
  have hX : 0<X.lo := by dsimp [X]; reference_arithmetic
  have hT : 0<(tBox X).lo := by dsimp [X]; reference_arithmetic
  have hW : 0<W.lo := by dsimp [W]; reference_arithmetic
  let A₀ := argumentBox Y X (by dsimp [Y,X]; reference_arithmetic)
  let A := widen A₀ (11790649685/1000000000000) (11790649686/1000000000000)
    (by dsimp [A₀,Y,X]; reference_arithmetic) (by dsimp [A₀,Y,X]; reference_arithmetic)
  let V := valueBox Y X W (betaBox hB A)
  let F := firstBox Y X W hX hT
  let D := secondBox Y X W hX hT hW
  have h0 : (4489/5000:ℝ)<V.lo := by dsimp [V,A,A₀,W,Y,X]; reference_arithmetic
  have h1 : (0:ℝ)<F.lo := by dsimp [F,W,Y,X]; reference_arithmetic
  have h2 : (11/50:ℝ)<D.lo := by dsimp [D,W,Y,X]; reference_arithmetic
  exact ⟨h0.trans_le V.mem.1,h1.trans_le F.mem.1,h2.trans_le D.mem.1⟩

lemma middle_terminal : (1797/2000:ℝ)<E g (2/5) ∧ 0<E1 g (2/5) ∧ E2 g (2/5)<0 := by
  have hB : (2/5:ℝ)∈targets := by norm_num [targets]
  let Y := Interval.point (2/5:ℝ)
  let X := heightBox hB (1762271261752855/1000000000000000) (1762271261752856/1000000000000000)
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  let W := stationaryBox first_slope hB X (589887806260/1000000000000) (589887806261/1000000000000)
    (by norm_num) (by norm_num)
    (by dsimp [X]; reference_arithmetic) (by dsimp [X]; reference_arithmetic)
  have hX : 0<X.lo := by dsimp [X]; reference_arithmetic
  have hT : 0<(tBox X).lo := by dsimp [X]; reference_arithmetic
  have hW : 0<W.lo := by dsimp [W]; reference_arithmetic
  let A₀ := argumentBox Y X (by dsimp [Y,X]; reference_arithmetic)
  let A := widen A₀ (82855753700/1000000000000) (82855753701/1000000000000)
    (by dsimp [A₀,Y,X]; reference_arithmetic) (by dsimp [A₀,Y,X]; reference_arithmetic)
  let V := valueBox Y X W (betaBox hB A)
  let F := firstBox Y X W hX hT
  let D := secondBox Y X W hX hT hW
  have h0 : (1797/2000:ℝ)<V.lo := by dsimp [V,A,A₀,W,Y,X]; reference_arithmetic
  have h1 : (0:ℝ)<F.lo := by dsimp [F,W,Y,X]; reference_arithmetic
  have h2 : D.hi<(0:ℝ) := by dsimp [D,W,Y,X]; reference_arithmetic
  exact ⟨h0.trans_le V.mem.1,h1.trans_le F.mem.1,D.mem.2.trans_lt h2⟩

lemma first_terminal : (1797/2000:ℝ)<E g (9/20) := by
  have hB : (9/20:ℝ)∈targets := by norm_num [targets]
  let Y := Interval.point (9/20:ℝ)
  let X := heightBox hB (1735828332526001/1000000000000000) (1735828332526002/1000000000000000)
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  let W := stationaryBox first_slope hB X (631834846091/1000000000000) (631834846092/1000000000000)
    (by norm_num) (by norm_num)
    (by dsimp [X]; reference_arithmetic) (by dsimp [X]; reference_arithmetic)
  have hX : 0<X.lo := by dsimp [X]; reference_arithmetic
  have hT : 0<(tBox X).lo := by dsimp [X]; reference_arithmetic
  have hW : 0<W.lo := by dsimp [W]; reference_arithmetic
  let A₀ := argumentBox Y X (by dsimp [Y,X]; reference_arithmetic)
  let A := widen A₀ (127042394140/1000000000000) (127042394141/1000000000000)
    (by dsimp [A₀,Y,X]; reference_arithmetic) (by dsimp [A₀,Y,X]; reference_arithmetic)
  let V := valueBox Y X W (betaBox hB A)
  have h0 : (1797/2000:ℝ)<V.lo := by dsimp [V,A,A₀,W,Y,X]; reference_arithmetic
  exact h0.trans_le V.mem.1

lemma second_initial : (89807/100000:ℝ)<E (39/40) (9/20) ∧ E2 (39/40) (9/20)<0 := by
  have hB : (9/20:ℝ)∈targets := by norm_num [targets]
  let Y := Interval.point (9/20:ℝ)
  let X := heightBox hB (1735828332526001/1000000000000000) (1735828332526002/1000000000000000)
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  let W := stationaryBox second_slope hB X (610449533364/1000000000000) (610449533365/1000000000000)
    (by norm_num) (by norm_num)
    (by dsimp [X]; reference_arithmetic) (by dsimp [X]; reference_arithmetic)
  have hX : 0<X.lo := by dsimp [X]; reference_arithmetic
  have hT : 0<(tBox X).lo := by dsimp [X]; reference_arithmetic
  have hW : 0<W.lo := by dsimp [W]; reference_arithmetic
  let A₀ := argumentBox Y X (by dsimp [Y,X]; reference_arithmetic)
  let A := widen A₀ (127042394140/1000000000000) (127042394141/1000000000000)
    (by dsimp [A₀,Y,X]; reference_arithmetic) (by dsimp [A₀,Y,X]; reference_arithmetic)
  let V := valueBox Y X W (betaBox hB A)
  let D := secondBox Y X W hX hT hW
  have h0 : (89807/100000:ℝ)<V.lo := by dsimp [V,A,A₀,W,Y,X]; reference_arithmetic
  have h1 : D.hi<(0:ℝ) := by dsimp [D,W,Y,X]; reference_arithmetic
  exact ⟨h0.trans_le V.mem.1,D.mem.2.trans_lt h1⟩

lemma second_terminal : (89807/100000:ℝ)<E (39/40) (27/50) := by
  have hB : (27/50:ℝ)∈targets := by norm_num [targets]
  let Y := Interval.point (27/50:ℝ)
  let X := heightBox hB (1683448840921517/1000000000000000) (1683448840921518/1000000000000000)
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  let W := stationaryBox second_slope hB X (687193670807/1000000000000) (687193670808/1000000000000)
    (by norm_num) (by norm_num)
    (by dsimp [X]; reference_arithmetic) (by dsimp [X]; reference_arithmetic)
  have hX : 0<X.lo := by dsimp [X]; reference_arithmetic
  have hT : 0<(tBox X).lo := by dsimp [X]; reference_arithmetic
  have hW : 0<W.lo := by dsimp [W]; reference_arithmetic
  let A₀ := argumentBox Y X (by dsimp [Y,X]; reference_arithmetic)
  let A := widen A₀ (206882357406/1000000000000) (206882357407/1000000000000)
    (by dsimp [A₀,Y,X]; reference_arithmetic) (by dsimp [A₀,Y,X]; reference_arithmetic)
  let V := valueBox Y X W (betaBox hB A)
  have h0 : (89807/100000:ℝ)<V.lo := by dsimp [V,A,A₀,W,Y,X]; reference_arithmetic
  exact h0.trans_le V.mem.1

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum.References
end
end
end

section
/-!
## The complete small-target negative-core minimum

One quadratic tangent controls the unique tight minimum. A concave
first derivative then gives the increasing continuation, followed by
two intervals whose costs are concave and have strictly positive
endpoint reserves. Every dividing point belongs to the proved domains.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower)

lemma early_lower {B : ℝ} (hB : B∈Icc (0:ℝ) (8/25)) : γ<E g B := by
  have hdom {y : ℝ} (hy : y∈Icc (0:ℝ) (8/25)) : y∈targets :=
    ⟨hy.1,by linarith [hy.2]⟩
  have hc (y : ℝ) (hy : y∈Icc (0:ℝ) (8/25)) : (11/50:ℝ)≤E2 g y := by
    have hm := first_second_antitone (hdom hy) (show (8/25:ℝ)∈targets by norm_num [targets]) hy.2
    linarith [References.early_terminal.2.2]
  have ht := curvature_tangent (κ := (11/50:ℝ)) (f := E g) (d := E1 g) (dd := E2 g)
    hB (show (607/2000:ℝ)∈Icc (0:ℝ) (8/25) by norm_num)
    (fun y hy => E_hasDerivAt first_slope (hdom hy))
    (fun y hy => E1_hasDerivAt first_slope (hdom hy)) hc
  have hd := abs_lt.mp References.minimum_reference.2
  have hp := mul_pos (show 0<E1 g (607/2000)+3/500000 by linarith [hd.1])
    (show 0<(3/500000:ℝ)-E1 g (607/2000) by linarith [hd.2])
  have hsq := sq_nonneg ((11/50)*(B-607/2000)+E1 g (607/2000))
  dsimp [γ,EdgeThreeAligned.threshold]
  nlinarith [References.minimum_reference.1]

lemma middle_slope {B : ℝ} (hB : B∈Icc (8/25:ℝ) (2/5)) : 0<E1 g B := by
  have hdom {y : ℝ} (hy : y∈Icc (8/25:ℝ) (2/5)) : y∈targets :=
    ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hc : ConcaveOn ℝ (Icc (8/25:ℝ) (2/5)) (E1 g) :=
    concave_of_deriv2 (fun y hy => E1_hasDerivAt first_slope (hdom hy))
      (fun y hy => E2_hasDerivAt first_slope (hdom hy))
      (fun y hy => (first_third_negative (hdom hy)).le)
  exact concave_gt_of_endpoints hc hB References.early_terminal.2.1 References.middle_terminal.2.1

lemma middle_lower {B : ℝ} (hB : B∈Icc (8/25:ℝ) (2/5)) : γ<E g B := by
  have hdom {y : ℝ} (hy : y∈Icc (8/25:ℝ) (2/5)) : y∈targets :=
    ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hm : MonotoneOn (E g) (Icc (8/25:ℝ) (2/5)) :=
    monoOn_of_hasDeriv_nonneg
      (fun y hy => (E_hasDerivAt first_slope (hdom hy)).continuousAt.continuousWithinAt)
      (fun y hy => E_hasDerivAt first_slope (hdom (Ioo_subset_Icc_self hy)))
      (fun y hy => (middle_slope (Ioo_subset_Icc_self hy)).le)
  have he := hm (show (8/25:ℝ)∈Icc (8/25:ℝ) (2/5) by norm_num) hB hB.1
  dsimp [γ,EdgeThreeAligned.threshold]
  linarith [References.early_terminal.1]

lemma first_late_lower {B : ℝ} (hB : B∈Icc (2/5:ℝ) (9/20)) : γ<E g B := by
  have hdom {y : ℝ} (hy : y∈Icc (2/5:ℝ) (9/20)) : y∈targets :=
    ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hc : ConcaveOn ℝ (Icc (2/5:ℝ) (9/20)) (E g) :=
    concave_of_deriv2 (fun y hy => E_hasDerivAt first_slope (hdom hy))
      (fun y hy => E1_hasDerivAt first_slope (hdom hy)) (fun y hy => by
        have hm := first_second_antitone (show (2/5:ℝ)∈targets by norm_num [targets]) (hdom hy) hy.1
        linarith [References.middle_terminal.2.2])
  apply concave_gt_of_endpoints hc hB
  · dsimp [γ,EdgeThreeAligned.threshold]
    linarith [References.middle_terminal.1]
  · dsimp [γ,EdgeThreeAligned.threshold]
    linarith [References.first_terminal]

theorem first_lower {B : ℝ} (hB : B∈Icc (0:ℝ) (9/20)) : γ<E g B := by
  by_cases he : B≤8/25
  · exact early_lower ⟨hB.1,he⟩
  · by_cases hm : B≤2/5
    · exact middle_lower ⟨by linarith,hm⟩
    · exact first_late_lower ⟨by linarith,hB.2⟩

theorem second_lower {B : ℝ} (hB : B∈Icc (9/20:ℝ) (27/50)) : γ<E (39/40) B := by
  have hdom {y : ℝ} (hy : y∈Icc (9/20:ℝ) (27/50)) : y∈targets :=
    ⟨by linarith [hy.1],hy.2⟩
  have hc : ConcaveOn ℝ (Icc (9/20:ℝ) (27/50)) (E (39/40)) :=
    concave_of_deriv2 (fun y hy => E_hasDerivAt second_slope (hdom hy))
      (fun y hy => E1_hasDerivAt second_slope (hdom hy)) (fun y hy => by
        have hm := second_second_antitone
          (show (9/20:ℝ)∈Icc (9/20:ℝ) (27/50) by norm_num) hy hy.1
        linarith [References.second_initial.2])
  apply concave_gt_of_endpoints hc hB
  · dsimp [γ,EdgeThreeAligned.threshold]
    linarith [References.second_initial.1]
  · dsimp [γ,EdgeThreeAligned.threshold]
    linarith [References.second_terminal]

theorem contact_lower {B φ : ℝ} (hB : B∈targets) (hφ : Lower φ)
    (hb : 0≤contact B φ) : γ<C B φ := by
  by_cases he : B≤9/20
  · exact (first_lower ⟨hB.1,he⟩).trans_le (angle_lower first_slope hB hφ hb)
  · exact (second_lower ⟨by linarith,hB.2⟩).trans_le (angle_lower second_slope hB hφ hb)

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower)

theorem transverse_original {a b A B φ : ℝ} (hs : CoreState a b)
    (ht : OuterState A B) (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤-b+A*Real.sin φ-B*Real.cos φ) :
    γ<value a b B φ := by
  have hc := original_contact hs ht hφ hsep
  have hmin : γ<C B φ := by
    by_cases he : B≤27/50
    · exact Minimum.contact_lower ⟨ht.1,he⟩ hφ hc.2.1
    · exact High.lower ht (by linarith) hφ hc.2.1
  exact hmin.trans_le hc.2.2.2.2

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource
end
end
end
