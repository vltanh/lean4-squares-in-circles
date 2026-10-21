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

local macro "critical_reference" : tactic => `(tactic|
  norm_num [zBox,pBox,ellBox,SBox,hBox,h₁Box,DBox,g₁Box,g₂Box,qBox,
    factorBox,factorDBox,outerFirstBox,inverseFirstBox,speedBox,
    labelBox,firstBox,secondBox,ratioBox,ratioDBox,coordinate,
    shifted,radicand,rootThree,rootStep,LLabel,TLabel,Q0,
    LowerContact.inner,LowerContact.outer,probeSource,probeLo,probeHi,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.inv,Interval.div])

def probeSourceU (late : Bool) : Interval (U (probeSource late)) :=
  shifted (Interval.point (probeSource late)) (17/10) (by norm_num)
    (by cases late <;> critical_reference)
def probeLoU (late : Bool) : Interval (U (probeLo late)) :=
  shifted (Interval.point (probeLo late)) (19/10) (by norm_num)
    (by cases late <;> critical_reference)
def probeHiU (late : Bool) : Interval (U (probeHi late)) :=
  shifted (Interval.point (probeHi late)) (19/10) (by norm_num)
    (by cases late <;> critical_reference)

lemma probe_scalar_bracket (late : Bool) :
    S (probeLo late)<LowerInverse.q (U (probeSource late)) ∧
      LowerInverse.q (U (probeSource late))<S (probeHi late) := by
  have hl : 0<(probeLoU late).lo := by cases late <;> dsimp [probeLoU] <;> critical_reference
  have hr : 0<(probeHiU late).lo := by cases late <;> dsimp [probeHiU] <;> critical_reference
  let P₀ := pBox (Interval.point (probeLo late)) (probeLoU late) hl
  let P₁ := pBox (Interval.point (probeHi late)) (probeHiU late) hr
  have hp₀ : 0<P₀.lo := by cases late <;> dsimp [P₀,probeLoU] <;> critical_reference
  have hp₁ : 0<P₁.lo := by cases late <;> dsimp [P₁,probeHiU] <;> critical_reference
  let S₀ := SBox (Interval.point (probeLo late)) P₀ hp₀
  let S₁ := SBox (Interval.point (probeHi late)) P₁ hp₁
  let Q := qBox (probeSourceU late)
  have h₀ : S₀.hi<Q.lo := by
    cases late <;> dsimp [S₀,P₀,Q,probeLoU,probeSourceU] <;> critical_reference
  have h₁ : Q.hi<S₁.lo := by
    cases late <;> dsimp [S₁,P₁,Q,probeHiU,probeSourceU] <;> critical_reference
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

lemma half_first : (1/4000:ℝ)<first halfPoint := by
  have hu : 0<(probeSourceU true).lo := by dsimp [probeSourceU]; critical_reference
  have hq : 0<(qBox (probeSourceU true)).lo := by dsimp [probeSourceU]; critical_reference
  have hv : 0<(probeSpeed true).lo := by dsimp [probeSpeed,probeBox,probeSourceU]; critical_reference
  let Z := outerFirstBox true ((probeBox true).add (Interval.point (1/2)))
    (Interval.point (probeSource true)) (probeSourceU true) (probeSpeed true) hu hq hv
  have hh : (1/4000:ℝ)<Z.lo := by
    dsimp [Z,probeSpeed,probeBox,probeSourceU]; critical_reference
  have hval := hh.trans_le Z.mem.1
  have he := actual_first half_domain.1
  rw [half_source] at he
  simpa [probePoint,probeSource,he] using hval

lemma reference_first : |first referencePoint|<(1/10000:ℝ) := by
  have hu : 0<(probeSourceU false).lo := by dsimp [probeSourceU]; critical_reference
  have hq : 0<(qBox (probeSourceU false)).lo := by dsimp [probeSourceU]; critical_reference
  have hv : 0<(probeSpeed false).lo := by dsimp [probeSpeed,probeBox,probeSourceU]; critical_reference
  let Z := outerFirstBox true ((probeBox false).add (Interval.point (1/2)))
    (Interval.point (probeSource false)) (probeSourceU false) (probeSpeed false) hu hq hv
  have hl : -(1/10000:ℝ)<Z.lo := by
    dsimp [Z,probeSpeed,probeBox,probeSourceU]; critical_reference
  have hh : Z.hi<(1/10000:ℝ) := by
    dsimp [Z,probeSpeed,probeBox,probeSourceU]; critical_reference
  have hval := abs_lt.mpr ⟨hl.trans_le Z.mem.1,Z.mem.2.trans_lt hh⟩
  have he := actual_first reference_domain.1
  rw [reference_source] at he
  simpa [probePoint,probeSource,he] using hval

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerCritical
