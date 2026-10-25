module

public import SquaresInCircles.Eight.TableFree.FrameMidHighTargetContact
public import SquaresInCircles.Eight.TableFree.FrameMidHighSourceContact

/-!
# Both actual middle/high orders on the complete quarter strip

The source and target contact paths are applied to the original circle
points and original weak central inequality.  Both sides include the
quarter turn and the endpoints of the strip.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameMidHighQuarterStrip
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FrameMidHighContactArc

theorem middle_high {b B x : ℝ} (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (Real.pi/2-1/50) (Real.pi/2+1/50))
    (hm : 0≤central false true (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false false true b B x := by
  let e : ℝ := x-Real.pi/2
  have he : e∈strip := by dsimp [e,strip]; constructor <;> linarith [hx.1,hx.2]
  have hid : Real.pi/2+e=x := by dsimp [e]; ring
  by_cases hn : e≤0
  · have hs : e∈side true := ⟨he.1,hn⟩
    have hh := FrameMidHighTargetContact.actual_lower hb hB hs (by simpa only [hid] using hm)
    simpa only [hid] using hh
  · have hs : e∈side false := ⟨(lt_of_not_ge hn).le,he.2⟩
    have hh := FrameMidHighTargetContact.actual_lower hb hB hs (by simpa only [hid] using hm)
    simpa only [hid] using hh

theorem high_middle {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (Real.pi/2-1/50) (Real.pi/2+1/50))
    (hm : 0≤central false true (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost false true false true b B x := by
  let e : ℝ := x-Real.pi/2
  have he : e∈strip := by dsimp [e,strip]; constructor <;> linarith [hx.1,hx.2]
  have hid : Real.pi/2+e=x := by dsimp [e]; ring
  by_cases hn : e≤0
  · have hs : e∈side true := ⟨he.1,hn⟩
    have hh := FrameMidHighSourceContact.actual_lower hB hb hs (by simpa only [hid] using hm)
    simpa only [hid] using hh
  · have hs : e∈side false := ⟨(lt_of_not_ge hn).le,he.2⟩
    have hh := FrameMidHighSourceContact.actual_lower hB hb hs (by simpa only [hid] using hm)
    simpa only [hid] using hh

end SquaresInCircles.Eight.TableFree.FrameMidHighQuarterStrip
