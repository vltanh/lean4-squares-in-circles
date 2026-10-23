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

local macro "envelope_reference" : tactic => `(tactic|
  norm_num [zBox,pBox,ellBox,SBox,hBox,h₁Box,markerBox,slopeRatioBox,qBox,
    firstBox,secondBox,thirdBox,ratioBox,ratioDBox,ratioDDBox,coordinate,
    shifted,radicand,rootThree,rootStep,LLabel,Q0,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.inv,Interval.div])

def leftU : Interval (U (3/100)) :=
  shifted (Interval.point (3/100)) (19/10) (by norm_num) (by envelope_reference)
def rightU : Interval (U (3/20)) :=
  shifted (Interval.point (3/20)) (19/10) (by norm_num) (by envelope_reference)
def sourceEndU : Interval (U (3/5)) :=
  shifted (Interval.point (3/5)) (33/20) (by norm_num) (by envelope_reference)

lemma endpoint_label_bounds :
    p (3/100)<(1117/1000:ℝ) ∧ (911/1000:ℝ)<p (3/20) ∧
    -(191/100:ℝ)<ell (3/100) ∧ ell (3/20)< -(753/500:ℝ) ∧
    (129/40:ℝ)<LLabel.d3 (3/100) ∧ LLabel.d3 (3/20)<438/125 := by
  have hl : 0<leftU.lo := by dsimp [leftU]; envelope_reference
  have hr : 0<rightU.lo := by dsimp [rightU]; envelope_reference
  let P₀ := pBox (Interval.point (3/100)) leftU hl
  let P₁ := pBox (Interval.point (3/20)) rightU hr
  let E₀ := ellBox (Interval.point (3/100)) leftU hl
  let E₁ := ellBox (Interval.point (3/20)) rightU hr
  let T₀ := thirdBox LLabel (Interval.point (3/100)) leftU hl
  let T₁ := thirdBox LLabel (Interval.point (3/20)) rightU hr
  have hp₀ : P₀.hi<(1117/1000:ℝ) := by dsimp [P₀,leftU]; envelope_reference
  have hp₁ : (911/1000:ℝ)<P₁.lo := by dsimp [P₁,rightU]; envelope_reference
  have he₀ : -(191/100:ℝ)<E₀.lo := by dsimp [E₀,leftU]; envelope_reference
  have he₁ : E₁.hi< -(753/500:ℝ) := by dsimp [E₁,rightU]; envelope_reference
  have ht₀ : (129/40:ℝ)<T₀.lo := by dsimp [T₀,leftU]; envelope_reference
  have ht₁ : T₁.hi<(438/125:ℝ) := by dsimp [T₁,rightU]; envelope_reference
  exact ⟨P₀.mem.2.trans_lt hp₀,hp₁.trans_le P₁.mem.1,he₀.trans_le E₀.mem.1,
    E₁.mem.2.trans_lt he₁,ht₀.trans_le T₀.mem.1,T₁.mem.2.trans_lt ht₁⟩

lemma endpoint_product_bounds :
    (591/1000:ℝ)<h (3/100) ∧ h (3/100)<74/125 ∧
    (591/1000:ℝ)<h (3/20) ∧ h₁ (3/100)<21/200 ∧
    -(69/1000:ℝ)<h₁ (3/20) ∧ 0<marker (3/20) ∧ slopeRatio (3/20)<227/125 := by
  have hl : 0<leftU.lo := by dsimp [leftU]; envelope_reference
  have hr : 0<rightU.lo := by dsimp [rightU]; envelope_reference
  let P₀ := pBox (Interval.point (3/100)) leftU hl
  let P₁ := pBox (Interval.point (3/20)) rightU hr
  let E₀ := ellBox (Interval.point (3/100)) leftU hl
  let E₁ := ellBox (Interval.point (3/20)) rightU hr
  have hp : 0<P₁.lo := by dsimp [P₁,rightU]; envelope_reference
  let H₀ := hBox (Interval.point (3/100)) P₀
  let H₁ := hBox (Interval.point (3/20)) P₁
  let J₀ := h₁Box (Interval.point (3/100)) P₀ E₀
  let J₁ := h₁Box (Interval.point (3/20)) P₁ E₁
  let M := markerBox P₁ E₁
  let K := slopeRatioBox P₁ E₁ hp
  have hH₀l : (591/1000:ℝ)<H₀.lo := by dsimp [H₀,P₀,leftU]; envelope_reference
  have hH₀h : H₀.hi<(74/125:ℝ) := by dsimp [H₀,P₀,leftU]; envelope_reference
  have hH₁ : (591/1000:ℝ)<H₁.lo := by dsimp [H₁,P₁,rightU]; envelope_reference
  have hJ₀ : J₀.hi<(21/200:ℝ) := by dsimp [J₀,P₀,E₀,leftU]; envelope_reference
  have hJ₁ : -(69/1000:ℝ)<J₁.lo := by dsimp [J₁,P₁,E₁,rightU]; envelope_reference
  have hM : 0<M.lo := by dsimp [M,P₁,E₁,rightU]; envelope_reference
  have hK : K.hi<(227/125:ℝ) := by dsimp [K,P₁,E₁,rightU]; envelope_reference
  exact ⟨hH₀l.trans_le H₀.mem.1,H₀.mem.2.trans_lt hH₀h,hH₁.trans_le H₁.mem.1,
    J₀.mem.2.trans_lt hJ₀,hJ₁.trans_le J₁.mem.1,hM.trans_le M.mem.1,K.mem.2.trans_lt hK⟩

lemma continuation_endpoints :
    S (3/100)<LowerInverse.q (U 0) ∧ LowerInverse.q (U (3/5))<S (3/20) := by
  have hl : 0<leftU.lo := by dsimp [leftU]; envelope_reference
  have hr : 0<rightU.lo := by dsimp [rightU]; envelope_reference
  let P₀ := pBox (Interval.point (3/100)) leftU hl
  let P₁ := pBox (Interval.point (3/20)) rightU hr
  have hp₀ : 0<P₀.lo := by dsimp [P₀,leftU]; envelope_reference
  have hp₁ : 0<P₁.lo := by dsimp [P₁,rightU]; envelope_reference
  let S₀ := SBox (Interval.point (3/100)) P₀ hp₀
  let S₁ := SBox (Interval.point (3/20)) P₁ hp₁
  let Q₀ := qBox Aligned.zeroU
  let Q₁ := qBox sourceEndU
  have h₀ : S₀.hi<Q₀.lo := by dsimp [S₀,P₀,Q₀,leftU,Aligned.zeroU]; envelope_reference
  have h₁ : Q₁.hi<S₁.lo := by dsimp [S₁,P₁,Q₁,rightU,sourceEndU]; envelope_reference
  exact ⟨S₀.mem.2.trans_lt (h₀.trans_le Q₀.mem.1),Q₁.mem.2.trans_lt (h₁.trans_le S₁.mem.1)⟩

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerEnvelope
