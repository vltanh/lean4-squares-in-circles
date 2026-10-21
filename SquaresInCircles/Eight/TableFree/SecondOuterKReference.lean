module

public import SquaresInCircles.Eight.TableFree.SecondOuterKBounds

/-!
# Exact fixed-reference enclosures for the target label `K`

The value and its first two derivatives are enclosed from a bracket for
the actual secondary coordinate and its one physical circle radical.
Every product retains its sign; the formulas therefore apply on the
entire nonnegative outer arc.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.KReference

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio ratioD)

def valueLo (bl bh ul uh : ℝ) : ℝ :=
  -(66/3125)*(uh-1/2)+(2909/10000)*bl+(22321/50000)*(ul-1/2)*bl
def valueHi (bl bh ul uh : ℝ) : ℝ :=
  -(66/3125)*(ul-1/2)+(2909/10000)*bh+(22321/50000)*(uh-1/2)*bh
def firstLo (bl bh ul uh : ℝ) : ℝ :=
  2909/10000+(22321/50000)*(ul-1/2)+(66/3125)*((bl+1/2)/uh)-
    (22321/50000)*bh*((bh+1/2)/ul)
def firstHi (bl bh ul uh : ℝ) : ℝ :=
  2909/10000+(22321/50000)*(uh-1/2)+(66/3125)*((bh+1/2)/ul)-
    (22321/50000)*bl*((bl+1/2)/uh)
def secondLo (bl bh ul uh : ℝ) : ℝ :=
  -(22321/25000)*((bh+1/2)/ul)+(66/3125)*(Q0/uh^3)-
    (22321/50000)*bh*(Q0/ul^3)
def secondHi (bl bh ul uh : ℝ) : ℝ :=
  -(22321/25000)*((bl+1/2)/uh)+(66/3125)*(Q0/ul^3)-
    (22321/50000)*bl*(Q0/uh^3)

theorem target {b bl bh ul uh : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hbox : b∈Icc bl bh) (hU : U b∈Icc ul uh)
    (hbl : 0≤bl) (hul : 1/2<ul) :
    valueLo bl bh ul uh≤K b ∧ K b≤valueHi bl bh ul uh ∧
      firstLo bl bh ul uh≤KLabel.d1 b ∧ KLabel.d1 b≤firstHi bl bh ul uh ∧
      secondLo bl bh ul uh≤KLabel.d2 b ∧ KLabel.d2 b≤secondHi bl bh ul uh := by
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

end SquaresInCircles.Eight.TableFree.SecondWord.KReference
