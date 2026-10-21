module

public import SquaresInCircles.Eight.TableFree.SecondOuterFixedReference

/-!
# Exact arithmetic at a fixed source-circle reference

These formulas enclose the value and first two derivatives of `P` from
a rational bracket for its physical circle radical.  The bracket is
always supplied by the exact circle equation at the named reference.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.SourceReference

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def valueLo (b ul uh : ℝ) : ℝ :=
  1239/50000+(18603/20000)*b+(2363/100000)*b^2-(2211/20000)*(uh-1/2)*b
def valueHi (b ul uh : ℝ) : ℝ :=
  1239/50000+(18603/20000)*b+(2363/100000)*b^2-(2211/20000)*(ul-1/2)*b
def firstLo (b ul uh : ℝ) : ℝ :=
  18603/20000+(2363/50000)*b-(2211/20000)*(uh-1/2)+
    (2211/20000)*b*((b+1/2)/uh)
def firstHi (b ul uh : ℝ) : ℝ :=
  18603/20000+(2363/50000)*b-(2211/20000)*(ul-1/2)+
    (2211/20000)*b*((b+1/2)/ul)
def secondLo (b ul uh : ℝ) : ℝ :=
  2363/50000+(2211/10000)*((b+1/2)/uh)+(2211/20000)*b*(Q0/uh^3)
def secondHi (b ul uh : ℝ) : ℝ :=
  2363/50000+(2211/10000)*((b+1/2)/ul)+(2211/20000)*b*(Q0/ul^3)

theorem source {b ul uh : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hU : U b∈Icc ul uh) (hul : 1/2<ul) :
    valueLo b ul uh≤P b ∧ P b≤valueHi b ul uh ∧
      firstLo b ul uh≤PLabel.d1 b ∧ PLabel.d1 b≤firstHi b ul uh ∧
      secondLo b ul uh≤PLabel.d2 b ∧ PLabel.d2 b≤secondHi b ul uh := by
  have hr := FixedReference.ratios hb ⟨le_rfl,le_rfl⟩ hU hb.1 hul
  have hblo := mul_le_mul_of_nonneg_right hU.1 hb.1
  have hbhi := mul_le_mul_of_nonneg_right hU.2 hb.1
  have hrlo := mul_le_mul_of_nonneg_left hr.1 hb.1
  have hrhi := mul_le_mul_of_nonneg_left hr.2.1 hb.1
  have hDlo := mul_le_mul_of_nonneg_left hr.2.2.1 hb.1
  have hDhi := mul_le_mul_of_nonneg_left hr.2.2.2 hb.1
  have hv : P b=1239/50000+(18603/20000)*b+(2363/100000)*b^2-
      (2211/20000)*(U b-1/2)*b := by
    dsimp [P,RoleLabel.outer,RoleLabel.eval,PLabel,U]
    ring
  have hd : PLabel.d1 b=18603/20000+(2363/50000)*b-
      (2211/20000)*(U b-1/2)+(2211/20000)*b*ratio b := by
    dsimp [RoleLabel.d1,PLabel,U]
    ring
  have hdd : PLabel.d2 b=2363/50000+(2211/10000)*ratio b+
      (2211/20000)*b*ratioD b := by
    dsimp [RoleLabel.d2,PLabel]
    ring
  rw [hv,hd,hdd]
  dsimp [valueLo,valueHi,firstLo,firstHi,secondLo,secondHi]
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith [hU.1,hU.2]

lemma source_third_upper {b ul upper : ℝ}
    (hb : b∈Icc 0 outerDiagonal) (hul : 0<ul) (hu : ul≤U b)
    (hupper : 0<upper)
    (hnum : 3*Q0*(2211/20000)*(Q0-(b+1/2)/2)<upper*ul^5) :
    PLabel.d3 b<upper := by
  have hp := U_positive (outer_domain hb)
  have hpow := pow_le_pow_left₀ hul.le hu 5
  have he := PLabel.third_numerator (outer_domain hb)
  have hh := mul_le_mul_of_nonneg_left hpow hupper.le
  norm_num [PLabel,W] at he
  nlinarith [pow_pos hp 5]

lemma target_third_lower {b uh lower : ℝ}
    (hb : b∈Icc 0 outerDiagonal) (hu : U b≤uh) (hlower : 0<lower)
    (hnum : lower*uh^5<3*Q0*(95769/100000)*(Q0-(b+1/2)/2)) :
    lower<TLabel.d3 b := by
  have hp := U_positive (outer_domain hb)
  have hpow := pow_le_pow_left₀ hp.le hu 5
  have he := TLabel.third_numerator (outer_domain hb)
  have hh := mul_le_mul_of_nonneg_left hpow hlower.le
  norm_num [TLabel,W] at he
  nlinarith [pow_pos hp 5]

end SquaresInCircles.Eight.TableFree.SecondWord.SourceReference
