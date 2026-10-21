module

public import SquaresInCircles.Eight.TableFree.SecondOuterLabelCalculus

/-!
# Rational differential identities for a fixed-circle contact

The inverse rotation uses the physical shifted primary coordinate.  Its
rational derivative and its derivative in the target coordinate are
kept exact; no label bound or contact-minimum assumption enters here.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

namespace NegativeTwo.Inverse

def q (u : ℝ) : ℝ := Q0+1-2*u
def N (u : ℝ) : ℝ := 4*Q0*u-2*u^2-Q0*(Q0+1)
def factor (u : ℝ) : ℝ := (Q0-u)/(u*q u)
def factorD (u : ℝ) : ℝ := N u/(u^2*(q u)^2)
def K (u : ℝ) : ℝ := 3*u^3-5*Q0*u+Q0*(Q0+1)
def brace (u r v : ℝ) : ℝ := Q0/u^3-2*r^2/q u-r^2/v^2

lemma q_hasDerivAt (u : ℝ) : HasDerivAt q (-2) u := by
  convert ((hasDerivAt_id u).const_mul 2).const_sub (Q0+1) using 1 <;>
    dsimp [q] <;> ring

lemma factor_hasDerivAt {u : ℝ} (hu : u≠0) (hq : q u≠0) :
    HasDerivAt factor (factorD u) u := by
  have hd := ((hasDerivAt_id u).const_sub Q0).div
    ((hasDerivAt_id u).mul (q_hasDerivAt u)) (mul_ne_zero hu hq)
  convert hd using 1
  · rfl
  · dsimp [factorD,N]
    field_simp [hu,hq]
    dsimp [q]
    ring

lemma brace_identity {u r z v : ℝ} (hu : u≠0) (hq : q u≠0)
    (hv : v≠0) (hc : u^2+r^2*u^2=Q0) (hn : z^2+v^2=q u) :
    brace u r v=K u/(u^3*q u)-r^2*z^2/(q u*v^2) := by
  dsimp [brace,K]
  field_simp [hu,hq,hv]
  dsimp [q] at *
  linear_combination (u^2*v^2)*hc+(r^2*u^3)*hn

lemma actual_q_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (1357/1250:ℝ)<q (U b) := by
  have hu := (UW_bounds hb).2.1
  norm_num [q,Q0]
  linarith

lemma factor_lower {u : ℝ} (hu : 0<u) (hq : 0<q u) :
    (4/5:ℝ)<factor u := by
  apply (lt_div_iff₀ (mul_pos hu hq)).2
  have he : Q0-u-(4/5)*u*q u=
      (8/5)*(u-7707/5000)^2+1783401/15625000 := by
    norm_num [q,Q0]
    ring
  have hh := sq_nonneg (u-7707/5000)
  nlinarith

end NegativeTwo.Inverse

namespace PJCritical

abbrev heightFactorD := NegativeTwo.Inverse.factorD

def inverseTarget (u r z v : ℝ) : ℝ :=
  -r*heightFactorD u+z/(NegativeTwo.Inverse.q u*v)*
    NegativeTwo.Inverse.brace u r v

end PJCritical

end SquaresInCircles.Eight.TableFree.SecondWord
