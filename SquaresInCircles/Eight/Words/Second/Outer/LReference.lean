module

public import SquaresInCircles.Eight.Words.Second.Outer.FixedReference

/-!
# Eight squares: exact references for the positive edge-three target label

These enclosures retain the signs of every coefficient of the literal
label `L`.  Their hypotheses are a coordinate bracket and a square-
proved bracket for its actual circle radical, with no verifier table.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.LReference

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio ratioD)

def valueLo (bl bh _ul uh : ℝ) : ℝ :=
  793/20000+(38551/10000)*bl-(37437/25000)*bh^2-
    (94721/50000)*(uh-1/2)*bh
def valueHi (bl bh ul _uh : ℝ) : ℝ :=
  793/20000+(38551/10000)*bh-(37437/25000)*bl^2-
    (94721/50000)*(ul-1/2)*bl
def firstLo (bl bh _ul uh : ℝ) : ℝ :=
  38551/10000-(37437/12500)*bh-(94721/50000)*(uh-1/2)+
    (94721/50000)*bl*((bl+1/2)/uh)
def firstHi (bl bh ul _uh : ℝ) : ℝ :=
  38551/10000-(37437/12500)*bl-(94721/50000)*(ul-1/2)+
    (94721/50000)*bh*((bh+1/2)/ul)
def secondLo (bl _bh _ul uh : ℝ) : ℝ :=
  -(37437/12500)+(94721/25000)*((bl+1/2)/uh)+
    (94721/50000)*bl*(Q0/uh^3)
def secondHi (_bl bh ul _uh : ℝ) : ℝ :=
  -(37437/12500)+(94721/25000)*((bh+1/2)/ul)+
    (94721/50000)*bh*(Q0/ul^3)

theorem target {b bl bh ul uh : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hbox : b∈Icc bl bh) (hU : U b∈Icc ul uh)
    (hbl : 0≤bl) (hul : 1/2<ul) :
    valueLo bl bh ul uh≤L b ∧ L b≤valueHi bl bh ul uh ∧
      firstLo bl bh ul uh≤LLabel.d1 b ∧ LLabel.d1 b≤firstHi bl bh ul uh ∧
      secondLo bl bh ul uh≤LLabel.d2 b ∧ LLabel.d2 b≤ secondHi bl bh ul uh := by
  have hr := FixedReference.ratios hb hbox hU hbl hul
  have hul0 : 0<ul := by linarith
  have huh0 : 0<uh := by linarith [hU.1,hU.2]
  have hrad : 0≤U b-1/2 := by linarith [hU.1]
  have hradhi : 0≤uh-1/2 := by linarith [hU.1,hU.2]
  have hprodlo := mul_le_mul
    (show ul-1/2≤U b-1/2 by linarith [hU.1]) hbox.1 hbl hrad
  have hprodhi := mul_le_mul
    (show U b-1/2≤uh-1/2 by linarith [hU.2]) hbox.2 hb.1 hradhi
  have hslo : bl^2≤b^2 := pow_le_pow_left₀ hbl hbox.1 2
  have hshi : b^2≤bh^2 := pow_le_pow_left₀ hb.1 hbox.2 2
  have hr0 : 0≤ratio b := (ShortOuterOne.SameContact.ratio_pos (outer_domain hb)).le
  have hrl0 : 0≤(bl+1/2)/uh := by positivity
  have hbrlo := mul_le_mul hbox.1 hr.1 hrl0 hb.1
  have hbrhi := mul_le_mul hbox.2 hr.2.1 hr0 (hb.1.trans hbox.2)
  have hD0 : 0≤ratioD b := (outer_ratio_bounds hb).2.2.1.le
  have hDl0 : 0≤Q0/uh^3 := by norm_num [Q0]; positivity
  have hbDlo := mul_le_mul hbox.1 hr.2.2.1 hDl0 hb.1
  have hbDhi := mul_le_mul hbox.2 hr.2.2.2 hD0 (hb.1.trans hbox.2)
  have hv : L b=793/20000+(38551/10000)*b-(37437/25000)*b^2-
      (94721/50000)*(U b-1/2)*b := by
    dsimp [L,RoleLabel.outer,RoleLabel.eval,LLabel,U]
    ring
  have hd : LLabel.d1 b=38551/10000-(37437/12500)*b-
      (94721/50000)*(U b-1/2)+(94721/50000)*b*ratio b := by
    dsimp [RoleLabel.d1,LLabel,U]
    ring
  have hdd : LLabel.d2 b= -(37437/12500)+(94721/25000)*ratio b+
      (94721/50000)*b*ratioD b := by
    dsimp [RoleLabel.d2,LLabel]
    ring
  rw [hv,hd,hdd]
  dsimp only [valueLo,valueHi,firstLo,firstHi,secondLo,secondHi]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · linarith only [hbox.1,hshi,hprodhi]
  · linarith only [hbox.2,hslo,hprodlo]
  · linarith only [hbox.2,hU.2,hbrlo]
  · linarith only [hbox.1,hU.1,hbrhi]
  · linarith only [hr.1,hbDlo]
  · linarith only [hr.2.1,hbDhi]

end SquaresInCircles.Eight.SecondWord.LReference
