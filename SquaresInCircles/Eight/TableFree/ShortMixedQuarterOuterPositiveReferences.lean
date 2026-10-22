module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterOuterPositiveData

/-!
# Fixed references for the positive-core primary contact

Uncompiled transcription of (14), (16), and the named axial references.
Only fixed geometric endpoints and the three displayed interior
references are enclosed. The following calculus proves the full domains.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterPositive.Reference
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open MixedQuarter.Reference
open SecondWord.OppositeThree.ReferenceAlgebra (rootThree)

def uBox {x : ℝ} (hx : 0≤x) : Interval (U x) :=
  ((Interval.point 1).add ((Interval.point c0).mul (sine hx))).add
    ((cosine hx).mul (Interval.point (1/2)))
def hBox {x : ℝ} (hx : 0≤x) : Interval (h x) :=
  ((Interval.point c0).mul (cosine hx)).sub ((sine hx).mul (Interval.point (1/2)))
def radicand {u : ℝ} (Y : Interval u) : Interval (Q0-u^2) := (Interval.point Q0).sub Y.square
def vBox {u : ℝ} (Y : Interval u) (hr : 0≤(radicand Y).lo) : Interval (V u) :=
  rootThree (radicand Y) (13/10) (by norm_num) hr
def mBox (r : Row) {u : ℝ} (Y : Interval u) (W : Interval (V u)) : Interval (M r u) :=
  ((Interval.point (ocP r)).mul (Y.sub (Interval.point (1/2)))).sub
    ((Interval.point (ocQ r)).mul (W.sub (Interval.point (1/2))))
def mdBox (r : Row) {u : ℝ} (Y : Interval u) (W : Interval (V u)) (hW : 0<W.lo) :
    Interval (Md r u) :=
  (Interval.point (ocP r)).add (((Interval.point (ocQ r)).mul Y).div W hW)
def curvatureBox (r : Row) {u : ℝ} (Y : Interval u) (W : Interval (V u)) (hW : 0<W.lo) :
    Interval (curvature r u) :=
  ((((Interval.point (ocQ r*Q0)).div W.cube (Interval.cube_lo_pos hW)).mul
    ((Interval.point J).sub ((Y.sub (Interval.point 1)).square))).sub
      ((mdBox r Y W hW).mul (Y.sub (Interval.point 1))))
def kBox (r : Row) {x : ℝ} (hx : 0≤x) (W : Interval (V (U x))) : Interval (K r x) :=
  (((halfPi.sub (Interval.point x)).add (Interval.point (ocC r))).add (mBox r (uBox hx) W))
def kdBox (r : Row) {x : ℝ} (hx : 0≤x) (W : Interval (V (U x))) (hW : 0<W.lo) : Interval (Kd r x) :=
  (Interval.point (-1)).add ((mdBox r (uBox hx) W hW).mul (hBox hx))
def eventBox (r : Row) {x : ℝ} (hx : 0≤x) (W : Interval (V (U x))) (hW : 0<W.lo) : Interval (H r x) :=
  ((mdBox r (uBox hx) W hW).mul (cosine hx)).sub (Interval.point (ocG r))

macro "positive_core_reference" : tactic => `(tactic|
  (dsimp [uBox,hBox,radicand,vBox,mBox,mdBox,curvatureBox,kBox,kdBox,eventBox,
    c0,J,cap,U,h,K,Kd,H,M,Md,Mdd,curvature,reference]; mixed_fixed))

theorem cap_height : outerAxial+1/2<U cap ∧ U cap<383/200 := by
  have hL : axial.hi+1/2<(uBox (show 0≤cap by norm_num [cap])).lo := by positive_core_reference
  have hU : (uBox (show 0≤cap by norm_num [cap])).hi<(383/200:ℝ) := by positive_core_reference
  exact ⟨lt_of_le_of_lt (add_le_add_right axial.mem.2 _) (hL.trans_le (uBox (by norm_num [cap])).mem.1),
    (uBox (by norm_num [cap])).mem.2.trans_lt hU⟩

theorem cap_trig : (903/1000:ℝ)<Real.cos cap ∧ Real.sin cap<107/250 := by
  have hC : (903/1000:ℝ)<(cosine (show 0≤cap by norm_num [cap])).lo := by positive_core_reference
  have hS : (sine (show 0≤cap by norm_num [cap])).hi<(107/250:ℝ) := by positive_core_reference
  exact ⟨hC.trans_le (cosine (by norm_num [cap])).mem.1,
    (sine (by norm_num [cap])).mem.2.trans_lt hS⟩

theorem corner_far : (1:ℝ)<(CoreAngleEndpoint.diagonal+1/2)*Real.sin (7/10)+Real.cos (7/10) := by
  let W := ((coreDiagonal.add (Interval.point (1/2))).mul (sine (by norm_num : (0:ℝ)≤7/10))).
    add (cosine (by norm_num : (0:ℝ)≤7/10))
  have hh : (1:ℝ)<W.lo := by dsimp [W]; mixed_fixed
  exact hh.trans_le W.mem.1

theorem initial_curvature (r : Row) (hr : Rows r) : (109/100:ℝ)<curvature r (3/2) := by
  let Y := Interval.point (3/2:ℝ)
  have hrad : 0≤(radicand Y).lo := by dsimp [Y]; positive_core_reference
  let W := vBox Y hrad
  have hW : 0<W.lo := by dsimp [W,Y]; positive_core_reference
  have hh : (109/100:ℝ)<(curvatureBox r Y W hW).lo := by
    fin_cases r <;> norm_num [Rows,sourcePositive,targetPositive] at hr <;>
      dsimp [W,Y] <;> positive_core_reference
  exact hh.trans_le (curvatureBox r Y W hW).mem.1

theorem initial_values (r : Row) (hr : Rows r) (hRise : Rising r) :
    (8981/10000:ℝ)<K r 0 ∧ 0<Kd r 0 := by
  have hrad : 0≤(radicand (uBox (by norm_num : (0:ℝ)≤0))).lo := by positive_core_reference
  let W := vBox (uBox (by norm_num : (0:ℝ)≤0)) hrad
  have hW : 0<W.lo := by dsimp [W]; positive_core_reference
  have hV : (8981/10000:ℝ)<(kBox r (by norm_num : (0:ℝ)≤0) W).lo := by
    fin_cases r <;> norm_num [Rows,Rising,sourcePositive,targetPositive] at hr hRise <;>
      dsimp [W] <;> positive_core_reference
  have hD : 0<(kdBox r (by norm_num : (0:ℝ)≤0) W hW).lo := by
    fin_cases r <;> norm_num [Rows,Rising,sourcePositive,targetPositive] at hr hRise <;>
      dsimp [W] <;> positive_core_reference
  exact ⟨hV.trans_le (kBox r (by norm_num) W).mem.1,hD.trans_le (kdBox r (by norm_num) W hW).mem.1⟩

theorem reference_bound (r : Row) (hr : Rows r) (hRise : ¬Rising r) :
    (449/500:ℝ)<K r (reference r)-(Kd r (reference r))^2/(109/50) := by
  have hnonneg : 0≤reference r := by
    dsimp [reference]; split_ifs <;> norm_num
  have hrad : 0≤(radicand (uBox hnonneg)).lo := by
    fin_cases r <;> norm_num [Rows,Rising,sourcePositive,targetPositive] at hr hRise <;>
      positive_core_reference
  let W := vBox (uBox hnonneg) hrad
  have hW : 0<W.lo := by
    fin_cases r <;> norm_num [Rows,Rising,sourcePositive,targetPositive] at hr hRise <;>
      dsimp [W] <;> positive_core_reference
  let L := (kBox r hnonneg W).sub
    (((kdBox r hnonneg W hW).square).mul (Interval.point (50/109)))
  have hh : (449/500:ℝ)<L.lo := by
    fin_cases r <;> norm_num [Rows,Rising,sourcePositive,targetPositive] at hr hRise <;>
      dsimp [L,W] <;> positive_core_reference
  have he := hh.trans_le L.mem.1
  simpa only [div_eq_mul_inv] using he

theorem initial_event (r : Row) (hr : Rows r) :
    (Interior r → H r 0<0) ∧ (¬Interior r → 0<H r 0) := by
  have hrad : 0≤(radicand (uBox (by norm_num : (0:ℝ)≤0))).lo := by positive_core_reference
  let W := vBox (uBox (by norm_num : (0:ℝ)≤0)) hrad
  have hW : 0<W.lo := by dsimp [W]; positive_core_reference
  constructor
  · intro hi
    have hh : (eventBox r (by norm_num : (0:ℝ)≤0) W hW).hi<0 := by
      fin_cases r <;> norm_num [Rows,Interior,sourcePositive,targetPositive] at hr hi <;>
        dsimp [W] <;> positive_core_reference
    exact (eventBox r (by norm_num) W hW).mem.2.trans_lt hh
  · intro hi
    have hh : 0<(eventBox r (by norm_num : (0:ℝ)≤0) W hW).lo := by
      fin_cases r <;> norm_num [Rows,Interior,sourcePositive,targetPositive] at hr hi <;>
        dsimp [W] <;> positive_core_reference
    exact hh.trans_le (eventBox r (by norm_num) W hW).mem.1

theorem event_at_eleven (r : Row) (hr : Rows r) (hi : Interior r) : (1/250:ℝ)<H r (11/100) := by
  have hrad : 0≤(radicand (uBox (by norm_num : (0:ℝ)≤11/100))).lo := by positive_core_reference
  let W := vBox (uBox (by norm_num : (0:ℝ)≤11/100)) hrad
  have hW : 0<W.lo := by dsimp [W]; positive_core_reference
  have hh : (1/250:ℝ)<(eventBox r (by norm_num : (0:ℝ)≤11/100) W hW).lo := by
    fin_cases r <;> norm_num [Rows,Interior,sourcePositive,targetPositive] at hr hi <;>
      dsimp [W] <;> positive_core_reference
  exact hh.trans_le (eventBox r (by norm_num) W hW).mem.1

def alignedInterior (r : Row) : ℝ := Real.pi/2+ocC r+ocG r+
  (ocG r-ocP r+ocQ r)/2-radius*Real.sqrt ((ocG r-ocP r)^2+ocQ r^2)

theorem aligned_interior (r : Row) (hr : Rows r) (hi : Interior r) :
    (89809/100000:ℝ)<alignedInterior r := by
  let Z := Interval.point ((ocG r-ocP r)^2+ocQ r^2)
  have hZ : 0≤Z.lo := by dsimp [Z,Interval.point]; positivity
  let N := rootThree Z (if r=3 then 21/10 else 3/2)
    (by split_ifs <;> norm_num) hZ
  let F := (((halfPi.add (Interval.point (ocC r))).add (Interval.point (ocG r))).add
    (Interval.point ((ocG r-ocP r+ocQ r)/2))).sub (circleRadius.mul N)
  have hh : (89809/100000:ℝ)<F.lo := by
    fin_cases r <;> norm_num [Rows,Interior,sourcePositive,targetPositive] at hr hi <;>
      dsimp [F,N,Z] <;> positive_core_reference
  exact hh.trans_le F.mem.1

theorem aligned_multiplier (r : Row) (hr : Rows r) : max (ocG r) (Md r (3/2))<57/50 := by
  let Y := Interval.point (3/2:ℝ)
  have hrad : 0≤(radicand Y).lo := by dsimp [Y]; positive_core_reference
  let W := vBox Y hrad
  have hW : 0<W.lo := by dsimp [W,Y]; positive_core_reference
  have hh : (mdBox r Y W hW).hi<(57/50:ℝ) := by
    fin_cases r <;> norm_num [Rows,sourcePositive,targetPositive] at hr <;>
      dsimp [W,Y] <;> positive_core_reference
  exact max_lt (by linarith [(coefficients r hr).2.2.2.2])
    ((mdBox r Y W hW).mem.2.trans_lt hh)

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterPositive.Reference
