module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeSourceThreeMinimumReferencesData

/-!
# Six named references for the exact negative-core minimum

Every decimal endpoint below is an exact rational. Height and stationary
radical cages follow from their squared endpoints. Arctangent arguments
have outward rational cages before their proved alternating sums are
used. These are references for continuous derivative arguments, not a
subdivision of the target domain. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Minimum.References
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open OppositeThree.ReferenceAlgebra

local macro "reference_arithmetic" : tactic => `(tactic|
  norm_num [heightBox,stationaryBox,widen,argumentBox,betaBox,atanBox,atanLo,atanHi,
    valueBox,firstBox,secondBox,phaseFirstBox,phaseSecondBox,stationaryFirstBox,
    stationarySecondBox,baseBox,tBox,vBox,piBox,ratioBox,ratioDBox,labelBox,
    OppositeThree.ReferenceAlgebra.firstBox,OppositeThree.ReferenceAlgebra.secondBox,
    coordinate,epsilon,e,g,z,EdgeThreeAligned.en,EdgeThreeAligned.gn,EdgeThreeAligned.zn,
    LPrimaryZero.e,LLabel,RoleLabel.eval,Q0,atanLower,atanUpper,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.inv,Interval.div])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
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
  have h1 : (-3/500000:ℝ)<F.lo := by dsimp [F,W,Y,X]; reference_arithmetic
  have h2 : F.hi<(3/500000:ℝ) := by dsimp [F,W,Y,X]; reference_arithmetic
  exact ⟨h0.trans_le V.mem.1,abs_lt.mpr ⟨h1.trans_le F.mem.1,F.mem.2.trans_lt h2⟩⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
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

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Minimum.References
