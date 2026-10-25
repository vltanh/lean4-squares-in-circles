module

public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts

/-!
# Eight squares: exact arithmetic at a fixed source-circle reference

These formulas enclose the value and first two derivatives of `P` from
a rational bracket for its physical circle radical.  The bracket is
always supplied by the exact circle equation at the named reference.
-/

section
/-!
## Exact fixed-reference enclosures for the target label `K`

The value and its first two derivatives are enclosed from a bracket for
the actual secondary coordinate and its one physical circle radical.
Every product retains its sign; the formulas therefore apply on the
entire nonnegative outer arc.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.KReference

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio ratioD)

def valueLo (bl _bh ul uh : ℝ) : ℝ :=
  -(66/3125)*(uh-1/2)+(2909/10000)*bl+(22321/50000)*(ul-1/2)*bl
def valueHi (_bl bh ul uh : ℝ) : ℝ :=
  -(66/3125)*(ul-1/2)+(2909/10000)*bh+(22321/50000)*(uh-1/2)*bh
def firstLo (bl bh ul uh : ℝ) : ℝ :=
  2909/10000+(22321/50000)*(ul-1/2)+(66/3125)*((bl+1/2)/uh)-
    (22321/50000)*bh*((bh+1/2)/ul)
def firstHi (bl bh ul uh : ℝ) : ℝ :=
  2909/10000+(22321/50000)*(uh-1/2)+(66/3125)*((bh+1/2)/ul)-
    (22321/50000)*bl*((bl+1/2)/uh)
def secondLo (_bl bh ul uh : ℝ) : ℝ :=
  -(22321/25000)*((bh+1/2)/ul)+(66/3125)*(Q0/uh^3)-
    (22321/50000)*bh*(Q0/ul^3)
def secondHi (bl _bh ul uh : ℝ) : ℝ :=
  -(22321/25000)*((bl+1/2)/uh)+(66/3125)*(Q0/ul^3)-
    (22321/50000)*bl*(Q0/uh^3)

theorem target {b bl bh ul uh : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hbox : b∈Icc bl bh) (hU : U b∈Icc ul uh)
    (hbl : 0≤bl) (hul : 1/2<ul) :
    valueLo bl bh ul uh≤K b ∧ K b≤valueHi bl bh ul uh ∧
      firstLo bl bh ul uh≤KLabel.d1 b ∧ KLabel.d1 b≤firstHi bl bh ul uh ∧
      secondLo bl bh ul uh≤KLabel.d2 b ∧ KLabel.d2 b≤ secondHi bl bh ul uh := by
  have hr := FixedReference.ratios hb hbox hU hbl hul
  have hul0 : 0<ul := by linarith
  have huh0 : 0<uh := by linarith [hU.1,hU.2]
  have hrad : 0≤U b-1/2 := by linarith [hU.1]
  have hradhi : 0≤uh-1/2 := by linarith [hU.1,hU.2]
  have hprodlo := mul_le_mul
    (show ul-1/2≤U b-1/2 by linarith [hU.1]) hbox.1 hbl hrad
  have hprodhi := mul_le_mul
    (show U b-1/2≤uh-1/2 by linarith [hU.2]) hbox.2 hb.1 hradhi
  have hr0 : 0≤ratio b := (ShortOuterOne.SameContact.ratio_pos (outer_domain hb)).le
  have hrl0 : 0≤(bl+1/2)/uh := by positivity
  have hrh0 : 0≤(bh+1/2)/ul := by
    have hbh : 0≤bh := hb.1.trans hbox.2
    positivity
  have hbrlo := mul_le_mul hbox.1 hr.1 hrl0 hb.1
  have hbrhi := mul_le_mul hbox.2 hr.2.1 hr0 (hb.1.trans hbox.2)
  have hD0 : 0≤ratioD b := (outer_ratio_bounds hb).2.2.1.le
  have hDl0 : 0≤Q0/uh^3 := by norm_num [Q0]; positivity
  have hbDlo := mul_le_mul hbox.1 hr.2.2.1 hDl0 hb.1
  have hbDhi := mul_le_mul hbox.2 hr.2.2.2 hD0 (hb.1.trans hbox.2)
  have hv : K b= -(66/3125)*(U b-1/2)+(2909/10000)*b+
      (22321/50000)*(U b-1/2)*b := by
    dsimp [K,RoleLabel.outer,RoleLabel.eval,KLabel,U]
    ring
  have hd : KLabel.d1 b=2909/10000+(22321/50000)*(U b-1/2)+
      (66/3125)*ratio b-(22321/50000)*b*ratio b := by
    dsimp [RoleLabel.d1,KLabel,U]
    ring
  have hdd : KLabel.d2 b= -(22321/25000)*ratio b+(66/3125)*ratioD b-
      (22321/50000)*b*ratioD b := by
    dsimp [RoleLabel.d2,KLabel]
    ring
  rw [hv,hd,hdd]
  dsimp [valueLo,valueHi,firstLo,firstHi,secondLo,secondHi]
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;>
    nlinarith [hU.1,hU.2,hbox.1,hbox.2,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2]

end SquaresInCircles.Eight.SecondWord.KReference
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.SourceReference

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def valueLo (b _ul uh : ℝ) : ℝ :=
  1239/50000+(18603/20000)*b+(2363/100000)*b^2-(2211/20000)*(uh-1/2)*b
def valueHi (b ul _uh : ℝ) : ℝ :=
  1239/50000+(18603/20000)*b+(2363/100000)*b^2-(2211/20000)*(ul-1/2)*b
def firstLo (b _ul uh : ℝ) : ℝ :=
  18603/20000+(2363/50000)*b-(2211/20000)*(uh-1/2)+
    (2211/20000)*b*((b+1/2)/uh)
def firstHi (b ul _uh : ℝ) : ℝ :=
  18603/20000+(2363/50000)*b-(2211/20000)*(ul-1/2)+
    (2211/20000)*b*((b+1/2)/ul)
def secondLo (b _ul uh : ℝ) : ℝ :=
  2363/50000+(2211/10000)*((b+1/2)/uh)+(2211/20000)*b*(Q0/uh^3)
def secondHi (b ul _uh : ℝ) : ℝ :=
  2363/50000+(2211/10000)*((b+1/2)/ul)+(2211/20000)*b*(Q0/ul^3)

theorem source {b ul uh : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hU : U b∈Icc ul uh) (hul : 1/2<ul) :
    valueLo b ul uh≤P b ∧ P b≤valueHi b ul uh ∧
      firstLo b ul uh≤PLabel.d1 b ∧ PLabel.d1 b≤firstHi b ul uh ∧
      secondLo b ul uh≤PLabel.d2 b ∧ PLabel.d2 b≤ secondHi b ul uh := by
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
  have hval : PLabel.d3 b*(U b)^5=3*Q0*(2211/20000)*(Q0-(b+1/2)/2) := by
    rw [he]
    simp only [PLabel,W]
    ring
  by_contra hc
  have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hc) (pow_pos hp 5).le
  linarith

lemma target_third_lower {b uh lower : ℝ}
    (hb : b∈Icc 0 outerDiagonal) (hu : U b≤uh) (hlower : 0<lower)
    (hnum : lower*uh^5<3*Q0*(95769/100000)*(Q0-(b+1/2)/2)) :
    lower<TLabel.d3 b := by
  have hp := U_positive (outer_domain hb)
  have hpow := pow_le_pow_left₀ hp.le hu 5
  have he := TLabel.third_numerator (outer_domain hb)
  have hh := mul_le_mul_of_nonneg_left hpow hlower.le
  have hval : TLabel.d3 b*(U b)^5=3*Q0*(95769/100000)*(Q0-(b+1/2)/2) := by
    rw [he]
    simp only [TLabel,W]
    ring
  by_contra hc
  have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hc) (pow_pos hp 5).le
  linarith

end SquaresInCircles.Eight.SecondWord.SourceReference
end
end
end
