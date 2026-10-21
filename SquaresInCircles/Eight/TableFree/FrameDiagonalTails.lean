module

public import SquaresInCircles.Eight.TableFree.FrameDiagonalGeometry

/-!
# Complete angular tails for M/H and H/H

The quarter-periodic charge is bounded by half the distance to the
quarter turn.  These estimates cover every later angle, with no upper
frame-window hypothesis.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameDiagonalTails
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport

def mhTail (middleSource i j : Bool) : ℝ :=
  if i then (if j then (if middleSource then 93/100 else 71/50) else 61/100)
  else (if j then 171/100 else (if middleSource then 71/50 else 93/100))
def hhTail (i j : Bool) : ℝ :=
  if i then (if j then Real.pi/2 else 21/20) else (if j then 15543/10000 else 127/100)

theorem quarter_charge_upper (x : ℝ) : periodicFrameCost x≤|x-Real.pi/2|/2 := by
  have hp := periodicFrameCost_pi_half (x-Real.pi/2)
  have he : x-Real.pi/2+Real.pi/2=x := by ring
  rw [he] at hp
  rw [hp]
  have hs := Real.abs_sin_le_abs (x := x-Real.pi/2)
  have hc := Real.abs_cos_le_one (x-Real.pi/2)
  dsimp [periodicFrameCost]
  linarith

theorem angular_after {x : ℝ} (hx : Real.pi/2≤x) :
    (91/100)*x+(9/100)*(Real.pi/2)≤x-(9/50)*periodicFrameCost x := by
  have hh := quarter_charge_upper x
  rw [abs_of_nonneg (sub_nonneg.mpr hx)] at hh
  linarith

theorem angular_from_before {x l : ℝ} (hl : l≤Real.pi/2) (hx : l≤x) :
    (109/100)*l-(9/100)*(Real.pi/2)≤x-(9/50)*periodicFrameCost x := by
  by_cases hxq : x≤Real.pi/2
  · have hh := quarter_charge_upper x
    rw [abs_of_nonpos (sub_nonpos.mpr hxq)] at hh
    linarith
  · have hh := angular_after (lt_of_not_ge hxq).le
    linarith

theorem high_signed_bounds (i : Bool) {b : ℝ} (hb : b∈Icc 0 b1) :
    -(160727/500000:ℝ)<sign i*H b ∧ sign i*H b<160727/500000 := by
  have hh := H_bounds hb
  cases i <;> dsimp [sign] <;> constructor <;> linarith

theorem middle_signed_bounds (i : Bool) {b : ℝ} (hb : b∈Icc b1 b2) :
    -(601/1250:ℝ)<sign i*M b ∧ sign i*M b<601/1250 := by
  have hh := M_bounds hb
  cases i <;> dsimp [sign] <;> constructor <;> linarith

theorem middle_high_late (i j : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (hx : (171/100:ℝ)≤x) :
    (4463/5000:ℝ)<cost true false i j b B x := by
  have hs := middle_signed_bounds i hb
  have ht := high_signed_bounds j hB
  have ha := angular_after (show Real.pi/2≤x by linarith [Arithmetic.pi_hand_enclosure.2])
  dsimp [cost,marker]
  linarith [Arithmetic.pi_hand_enclosure.1]

theorem high_middle_late (i j : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2) (hx : (171/100:ℝ)≤x) :
    (4463/5000:ℝ)<cost false true i j b B x := by
  have hs := high_signed_bounds i hb
  have ht := middle_signed_bounds j hB
  have ha := angular_after (show Real.pi/2≤x by linarith [Arithmetic.pi_hand_enclosure.2])
  dsimp [cost,marker]
  linarith [Arithmetic.pi_hand_enclosure.1]

theorem middle_high (i j : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (hx : mhTail true i j≤x) :
    (4463/5000:ℝ)<cost true false i j b B x := by
  have hs := M_bounds hb
  have ht := H_bounds hB
  have hch := CorePairGeometry.charge_upper x
  cases i <;> cases j
  · dsimp [mhTail,cost,marker,sign] at *
    linarith
  · exact middle_high_late false true hb hB hx
  · dsimp [mhTail,cost,marker,sign] at *
    linarith
  · dsimp [mhTail,cost,marker,sign] at *
    linarith

theorem high_middle (i j : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2) (hx : mhTail false i j≤x) :
    (4463/5000:ℝ)<cost false true i j b B x := by
  have hs := H_bounds hb
  have ht := M_bounds hB
  have hch := CorePairGeometry.charge_upper x
  cases i <;> cases j
  · dsimp [mhTail,cost,marker,sign] at *
    linarith
  · exact high_middle_late false true hb hB hx
  · dsimp [mhTail,cost,marker,sign] at *
    linarith
  · dsimp [mhTail,cost,marker,sign] at *
    linarith

theorem high_high_late (i j : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1) (hx : Real.pi/2≤x) :
    (9099/10000:ℝ)<cost false false i j b B x := by
  have hs := high_signed_bounds i hb
  have ht := high_signed_bounds j hB
  have ha := angular_after hx
  dsimp [cost,marker]
  linarith [Arithmetic.pi_hand_enclosure.1]

theorem high_high (i j : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1) (hx : hhTail i j≤x) :
    (9099/10000:ℝ)<cost false false i j b B x := by
  have hs := H_bounds hb
  have ht := H_bounds hB
  have hch := CorePairGeometry.charge_upper x
  cases i <;> cases j
  · dsimp [hhTail,cost,marker,sign] at *
    linarith
  · have hl : (15543/10000:ℝ)≤Real.pi/2 := by linarith [Arithmetic.pi_hand_enclosure.1]
    have ha := angular_from_before hl hx
    dsimp [cost,marker,sign]
    linarith [Arithmetic.pi_hand_enclosure.2]
  · dsimp [hhTail,cost,marker,sign] at *
    linarith
  · exact high_high_late true true hb hB hx

end SquaresInCircles.Eight.TableFree.FrameDiagonalTails
