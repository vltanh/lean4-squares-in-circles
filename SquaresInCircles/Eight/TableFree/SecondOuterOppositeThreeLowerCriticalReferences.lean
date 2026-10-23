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

local macro "critical_reference" : tactic => `(tactic|
  norm_num [zBox,pBox,ellBox,SBox,hBox,h₁Box,DBox,g₁Box,g₂Box,qBox,
    factorBox,factorDBox,speedBox,labelBox,firstBox,secondBox,ratioBox,ratioDBox,coordinate,
    shifted,radicand,rootThree,rootStep,LLabel,TLabel,Q0,
    LowerContact.inner,LowerContact.outer,probeSource,probeLo,probeHi,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.inv,Interval.div])

lemma half_second : (3/50:ℝ)<second halfPoint := by
  let Y := probeBox true
  let X₀ := probeU true
  have hX : 0<X₀.lo := by dsimp [X₀,probeU,probeBox]; critical_reference
  let P := pBox Y X₀ hX
  let E := ellBox Y X₀ hX
  have hP : 0<P.lo := by dsimp [P,Y,X₀,probeU,probeBox]; critical_reference
  let Q := SBox Y P hP
  let H := hBox Y P
  let J := h₁Box Y P E
  let D₀ := DBox Y P E hP
  have hQ : 0<Q.lo := by dsimp [Q,P,Y,X₀,probeU,probeBox]; critical_reference
  have hD : 0<D₀.lo := by dsimp [D₀,P,E,Y,X₀,probeU,probeBox]; critical_reference
  let G₁ := g₁Box H Q hQ
  let G₂ := g₂Box H J Q D₀ hQ hD
  let V := probeSourceU true
  have hV : 0<V.lo := by dsimp [V,probeSourceU]; critical_reference
  let Q₀ := qBox V
  have hQ₀ : 0<Q₀.lo := by dsimp [Q₀,V,probeSourceU]; critical_reference
  let R := ratioBox (Interval.point (probeSource true)) V hV
  let R₁ := ratioDBox V hV
  let F := factorDBox V Q₀ hV hQ₀
  let T := secondBox TLabel (Interval.point (probeSource true)) V hV
  let Z := ((((R.mul F).neg).add (((Interval.point 4).mul R.square).mul G₂)).
    add (((Interval.point 2).mul R₁).mul G₁)).sub T
  have hh : (3/50:ℝ)<Z.lo := by
    dsimp [Z,T,F,R,R₁,V,Q₀,G₁,G₂,H,J,D₀,Q,P,E,Y,X₀,probeU,probeBox,probeSourceU]
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
  have ht : T.hi<(208793/500000:ℝ) := by dsimp [T,probeSourceU]; critical_reference
  have hl : L₀.hi<(171201/1000000:ℝ) := by dsimp [L₀,probeBox,probeU]; critical_reference
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
      dsimp [probeSourceU]; critical_reference
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
  dsimp [cost,LowerContact.cost,LowerContact.inner,LowerContact.outer]
  rw [reference_source]
  change (89779/100000:ℝ)<Real.pi/2+LowerInverse.phase (z referencePoint) (99/200)-
    L referencePoint-T (99/200)
  norm_num [referenceAngle] at hphase
  linarith [pi_hand_enclosure.1]

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerCritical
