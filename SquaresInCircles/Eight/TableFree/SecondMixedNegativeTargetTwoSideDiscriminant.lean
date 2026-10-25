module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeTargetTwoData
public import SquaresInCircles.Eight.TableFree.SecondMixedPHeightQuadratic
public import SquaresInCircles.Eight.TableFree.SecondOuterConcaveSlope

/-!
# The exact side discriminant and its first four derivatives

The original expression is retained as a quadratic discriminant in
the core coordinate. Its two-harmonic expansion permits a single
fourth-derivative sign on the complete angle interval.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeTarget.Side
open CommonQuarter CorePairGeometry Arithmetic

abbrev p := PHeightQuadratic.p
abbrev k := PHeightQuadratic.k
def v0 : ℝ := Real.pi/2+PHeightQuadratic.c+e-γ
def contactD (x : ℝ) : ℝ := -2/5+(13/12)*Real.sin x+Real.cos x/2
def qa (x : ℝ) : ℝ := k*(Real.cos x)^2-z
def qb (x : ℝ) : ℝ := g-Real.cos x*(p+2*k*contactD x)
def qc (x : ℝ) : ℝ := v0-x+p*contactD x+k*(contactD x)^2
def A : ℝ := 12316256254413/10000000000000
def B : ℝ := -7644002660021/50000000000000
def C : ℝ := (39/100)*Real.pi-2705833101088507809/2000000000000000000
def H : ℝ := 3146949/4000000
def J : ℝ := -7083/12500
def Z : ℝ := (7083/25000)*Real.pi-3987658073098843809/2000000000000000000
def q : ℝ := 39/50
def E (x : ℝ) : ℝ := A*Real.cos x+B*Real.sin x+(C-q*x)*Real.cos (2*x)+
  H*Real.sin (2*x)+Z+J*x
def E1 (x : ℝ) : ℝ := -A*Real.sin x+B*Real.cos x+(-q+2*H)*Real.cos (2*x)-
  2*(C-q*x)*Real.sin (2*x)+J
def E2 (x : ℝ) : ℝ := -A*Real.cos x-B*Real.sin x-4*(C-q*x)*Real.cos (2*x)+
  (4*q-4*H)*Real.sin (2*x)
def E3 (x : ℝ) : ℝ := A*Real.sin x-B*Real.cos x+(12*q-8*H)*Real.cos (2*x)+
  8*(C-q*x)*Real.sin (2*x)
def E4 (x : ℝ) : ℝ := A*Real.cos x+B*Real.sin x+16*(C-q*x)*Real.cos (2*x)+
  (16*H-32*q)*Real.sin (2*x)

lemma C_bounds : -(25539083129/200000000000:ℝ)<C ∧ C< -(31923853911/250000000000:ℝ) := by
  dsimp [C]
  constructor <;> linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]

lemma Z_bounds : -(220750601187/200000000000:ℝ)<Z ∧ Z< -(551876502967/500000000000:ℝ) := by
  dsimp [Z]
  constructor <;> linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]

lemma discriminant_identity (x : ℝ) : E x=4*qa x*qc x-(qb x)^2 := by
  dsimp [E,qa,qb,qc,contactD,v0,A,B,C,H,Z,J,q,p,k,PHeightQuadratic.p,PHeightQuadratic.k,
    PHeightQuadratic.c,g,z,e,γ]
  rw [Real.cos_two_mul,Real.sin_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma E_hasDerivAt (x : ℝ) : HasDerivAt E (E1 x) x := by
  have hs := (Real.hasDerivAt_sin (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hc := (Real.hasDerivAt_cos (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  convert ((((((Real.hasDerivAt_cos x).const_mul A).add ((Real.hasDerivAt_sin x).const_mul B)).add
    ((((hasDerivAt_id x).const_mul q).const_sub C).mul hc)).add (hs.const_mul H)).add_const Z).add
      ((hasDerivAt_id x).const_mul J) using 1
  · funext y
    simp only [E,Pi.add_apply,Pi.mul_apply,Function.comp_apply,id]
  · dsimp [E1]
    ring

lemma E1_hasDerivAt (x : ℝ) : HasDerivAt E1 (E2 x) x := by
  have hs := (Real.hasDerivAt_sin (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hc := (Real.hasDerivAt_cos (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  convert (((((Real.hasDerivAt_sin x).const_mul (-A)).add ((Real.hasDerivAt_cos x).const_mul B)).add
    (hc.const_mul (-q+2*H))).sub
      (((((hasDerivAt_id x).const_mul q).const_sub C).mul hs).const_mul 2)).add_const J
    using 1
  · funext y
    simp only [E1,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Function.comp_apply,id]
    ring
  · dsimp [E2]
    ring

lemma E2_hasDerivAt (x : ℝ) : HasDerivAt E2 (E3 x) x := by
  have hs := (Real.hasDerivAt_sin (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hc := (Real.hasDerivAt_cos (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  convert ((((Real.hasDerivAt_cos x).const_mul (-A)).sub ((Real.hasDerivAt_sin x).const_mul B)).sub
    (((((hasDerivAt_id x).const_mul q).const_sub C).mul hc).const_mul 4)).add
      (hs.const_mul (4*q-4*H)) using 1
  · funext y
    simp only [E2,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Function.comp_apply,id]
    ring
  · dsimp [E3]
    ring

lemma E3_hasDerivAt (x : ℝ) : HasDerivAt E3 (E4 x) x := by
  have hs := (Real.hasDerivAt_sin (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hc := (Real.hasDerivAt_cos (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  convert ((((Real.hasDerivAt_sin x).const_mul A).sub ((Real.hasDerivAt_cos x).const_mul B)).add
    (hc.const_mul (12*q-8*H))).add
      (((((hasDerivAt_id x).const_mul q).const_sub C).mul hs).const_mul 8) using 1
  · funext y
    simp only [E3,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Function.comp_apply,id]
    ring
  · dsimp [E4]
    ring

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeTarget.Side
