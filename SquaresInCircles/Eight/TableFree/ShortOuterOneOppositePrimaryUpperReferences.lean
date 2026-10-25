module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryUpperAxialData

/-!
# Named axial reference values for the upper primary owners

Uncompiled transcription of the fixed substitutions in both hand notes.
All enclosures concern the displayed individual references 0, .09 and
.1072. They use positive squaring and the adjacent alternating Taylor
polynomials; no angle-domain subdivision is a premise.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper.Reference
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open ShortWord.MixedQuarter.Reference

def initialRoot : ℝ := Real.sqrt (Q0-9/4)
theorem initial_root_bounds :
    (129058126439213/100000000000000:ℝ)< initialRoot ∧
      initialRoot<(64529063219607/50000000000000:ℝ) := by
  have hQ : Q0-9/4=(1041/625:ℝ) := by norm_num [Q0]
  dsimp only [initialRoot]
  rw [hQ]
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

def initialRootBox : Interval initialRoot := Interval.of_bounds
  ⟨initial_root_bounds.1.le,initial_root_bounds.2.le⟩
def rhoBox : Interval rho := Interval.of_bounds ⟨rho_bounds.1.le,rho_bounds.2.le⟩
def initialLBox (r : Row) : Interval (p r+q r*(3/2)/initialRoot) :=
  (Interval.point (p r)).add ((Interval.point (q r*(3/2))).div initialRootBox
    (by norm_num [initialRootBox,Interval.of_bounds]))
def initialValueBox (r : Row) : Interval (F r 0) := by
  convert ((((halfPi.add (Interval.point (c r))).add (Interval.point (p r))).sub
    ((Interval.point (q r)).mul (initialRootBox.sub (Interval.point (1/2))))).sub ((Interval.point (P r)).mul axial)) using 1
  rw [F_formula,v_formula,K_formula]
  norm_num [initialRoot]
def initialFirstBox (r : Row) : Interval (F1 r 0) := by
  convert (Interval.point 1).sub ((initialLBox r).mul (axial.sub (Interval.point (1/2)))) using 1
  rw [F1_formula,v_formula,K_formula,h_formula]
  norm_num [initialRoot]
def initialHBox (r : Row) : Interval (H r 0) := by
  convert ((initialLBox r).add ((Interval.point (P r)).mul rhoBox)).sub (Interval.point (t r)) using 1
  rw [H_formula,v_formula,K_formula]
  norm_num [initialRoot,projection]

private theorem r86_mpr_lo {a b : ℝ} (e : a=b) (h : Interval a=Interval b) (X : Interval b) :
    (h.mpr X).lo=X.lo := by
  subst e
  rfl
private theorem r86_mpr_hi {a b : ℝ} (e : a=b) (h : Interval a=Interval b) (X : Interval b) :
    (h.mpr X).hi=X.hi := by
  subst e
  rfl
private theorem r86_initialValueBox_lo (r : Row) : (initialValueBox r).lo=
    ((((halfPi.add (Interval.point (c r))).add (Interval.point (p r))).sub
      ((Interval.point (q r)).mul (initialRootBox.sub (Interval.point (1/2))))).sub
        ((Interval.point (P r)).mul axial)).lo :=
  r86_mpr_lo (by rw [F_formula,v_formula,K_formula]; norm_num [initialRoot]) _ _
private theorem r86_initialFirstBox_lo (r : Row) : (initialFirstBox r).lo=
    ((Interval.point 1).sub ((initialLBox r).mul (axial.sub (Interval.point (1/2))))).lo :=
  r86_mpr_lo (by rw [F1_formula,v_formula,K_formula,h_formula]; norm_num [initialRoot]) _ _
private theorem r86_initialHBox_lo (r : Row) : (initialHBox r).lo=
    (((initialLBox r).add ((Interval.point (P r)).mul rhoBox)).sub (Interval.point (t r))).lo :=
  r86_mpr_lo (by rw [H_formula,v_formula,K_formula]; norm_num [initialRoot,projection]) _ _

def initialLower : Row→ℝ := ![44913/50000,17967/20000,8981/10000,8981/10000,8981/10000,92987/100000]

theorem initial_value (r : Row) : initialLower r<F r 0 := by
  have hh : initialLower r<(initialValueBox r).lo := by
    rw [r86_initialValueBox_lo]
    fin_cases r <;>
      dsimp [initialLower,initialRootBox,c,p,q,P] <;> mixed_fixed
  exact hh.trans_le (initialValueBox r).mem.1

theorem initial_first_zero : (49/250:ℝ)<F1 0 0 := by
  have hh : (49/250:ℝ)<(initialFirstBox 0).lo := by
    rw [r86_initialFirstBox_lo]
    dsimp [initialLBox,initialRootBox,p,q]
    mixed_fixed
  exact hh.trans_le (initialFirstBox 0).mem.1
theorem initial_first_one : -(1/50:ℝ)<F1 1 0 := by
  have hh : -(1/50:ℝ)<(initialFirstBox 1).lo := by
    rw [r86_initialFirstBox_lo]
    dsimp [initialLBox,initialRootBox,p,q]
    mixed_fixed
  exact hh.trans_le (initialFirstBox 1).mem.1
theorem initial_first_pair (r : Row) (hr : r=3∨r=4) : -(1/125:ℝ)<F1 r 0 := by
  have hh : -(1/125:ℝ)<(initialFirstBox r).lo := by
    rw [r86_initialFirstBox_lo]
    rcases hr with rfl | rfl <;>
      dsimp [initialLBox,initialRootBox,p,q] <;> mixed_fixed
  exact hh.trans_le (initialFirstBox r).mem.1
theorem initial_H_zero : -(27/1000:ℝ)<H 0 0 := by
  have hh : -(27/1000:ℝ)<(initialHBox 0).lo := by
    rw [r86_initialHBox_lo]
    dsimp [initialLBox,initialRootBox,rhoBox,p,q,P,t]
    mixed_fixed
  exact hh.trans_le (initialHBox 0).mem.1
theorem initial_H_one : (1/20:ℝ)<H 1 0 := by
  have hh : (1/20:ℝ)<(initialHBox 1).lo := by
    rw [r86_initialHBox_lo]
    dsimp [initialLBox,initialRootBox,rhoBox,p,q,P,t]
    mixed_fixed
  exact hh.trans_le (initialHBox 1).mem.1

def KBox (x : ℝ) (hx : 0≤x) : Interval (K x) := by
  convert ((Interval.point 1).add ((cosine hx).div (Interval.point 2)
    (by norm_num [Interval.point]))).sub
      ((axial.sub (Interval.point (1/2))).mul (sine hx)) using 1
  rw [K_formula]
def vRadicand (x : ℝ) (hx : 0≤x) : Interval (Q0-(K x)^2) :=
  (Interval.point Q0).sub ((KBox x hx).square)
def vBox (x : ℝ) (hx : 0≤x) (hr : 0≤(vRadicand x hx).lo) : Interval (v x) := by
  rw [v_formula]
  exact rootSix (vRadicand x hx) (3/2) (by norm_num) hr
def hBox (x : ℝ) (hx : 0≤x) : Interval (h x) := by
  convert ((sine hx).div (Interval.point 2) (by norm_num [Interval.point])).add
    ((axial.sub (Interval.point (1/2))).mul (cosine hx)) using 1
  rw [h_formula]
def valueBox (r : Row) (x : ℝ) (hx : 0≤x) (hr : 0≤(vRadicand x hx).lo) : Interval (F r x) := by
  convert (((((halfPi.add (Interval.point x)).add (Interval.point (c r))).add
    ((Interval.point (p r)).mul ((KBox x hx).sub (Interval.point (1/2))))).sub
      ((Interval.point (q r)).mul ((vBox x hx hr).sub (Interval.point (1/2))))).sub ((Interval.point (P r)).mul axial)) using 1
  rw [F_formula]
def firstBox (r : Row) (x : ℝ) (hx : 0≤x) (hr : 0≤(vRadicand x hx).lo)
    (hv : 0<(vBox x hx hr).lo) : Interval (F1 r x) := by
  convert (Interval.point 1).sub (((Interval.point (p r)).add
    ((Interval.point (q r)).mul ((KBox x hx).div (vBox x hx hr) hv))).mul (hBox x hx)) using 1
  rw [F1_formula]
  ring

private theorem r86_KBox_lo (x : ℝ) (hx : 0≤x) : (KBox x hx).lo=
    (((Interval.point 1).add ((cosine hx).div (Interval.point 2)
      (by norm_num [Interval.point]))).sub ((axial.sub (Interval.point (1/2))).mul (sine hx))).lo :=
  r86_mpr_lo (K_formula x) _ _
private theorem r86_KBox_hi (x : ℝ) (hx : 0≤x) : (KBox x hx).hi=
    (((Interval.point 1).add ((cosine hx).div (Interval.point 2)
      (by norm_num [Interval.point]))).sub ((axial.sub (Interval.point (1/2))).mul (sine hx))).hi :=
  r86_mpr_hi (K_formula x) _ _
private theorem r86_vBox_lo (x : ℝ) (hx : 0≤x) (hr : 0≤(vRadicand x hx).lo) :
    (vBox x hx hr).lo=(rootSix (vRadicand x hx) (3/2) (by norm_num) hr).lo :=
  r86_mpr_lo (v_formula x) _ _
private theorem r86_vBox_hi (x : ℝ) (hx : 0≤x) (hr : 0≤(vRadicand x hx).lo) :
    (vBox x hx hr).hi=(rootSix (vRadicand x hx) (3/2) (by norm_num) hr).hi :=
  r86_mpr_hi (v_formula x) _ _
private theorem r86_hBox_lo (x : ℝ) (hx : 0≤x) : (hBox x hx).lo=
    (((sine hx).div (Interval.point 2) (by norm_num [Interval.point])).add
      ((axial.sub (Interval.point (1/2))).mul (cosine hx))).lo :=
  r86_mpr_lo (h_formula x) _ _
private theorem r86_hBox_hi (x : ℝ) (hx : 0≤x) : (hBox x hx).hi=
    (((sine hx).div (Interval.point 2) (by norm_num [Interval.point])).add
      ((axial.sub (Interval.point (1/2))).mul (cosine hx))).hi :=
  r86_mpr_hi (h_formula x) _ _
private theorem r86_valueBox_lo (r : Row) (x : ℝ) (hx : 0≤x) (hr : 0≤(vRadicand x hx).lo) :
    (valueBox r x hx hr).lo=(((((halfPi.add (Interval.point x)).add (Interval.point (c r))).add
      ((Interval.point (p r)).mul ((KBox x hx).sub (Interval.point (1/2))))).sub
        ((Interval.point (q r)).mul ((vBox x hx hr).sub (Interval.point (1/2))))).sub
          ((Interval.point (P r)).mul axial)).lo :=
  r86_mpr_lo (F_formula r x) _ _
private theorem r86_firstBox_lo (r : Row) (x : ℝ) (hx : 0≤x) (hr : 0≤(vRadicand x hx).lo)
    (hv : 0<(vBox x hx hr).lo) : (firstBox r x hx hr hv).lo=
    ((Interval.point 1).sub (((Interval.point (p r)).add
      ((Interval.point (q r)).mul ((KBox x hx).div (vBox x hx hr) hv))).mul (hBox x hx))).lo :=
  r86_mpr_lo (by rw [F1_formula]; ring) _ _

theorem value_at_nine : (8997/10000:ℝ)<F 1 (9/100) := by
  have hr : 0≤(vRadicand (9/100) (by norm_num)).lo := by
    simp only [vRadicand,Interval.point,Interval.sub,Interval.square,Interval.mul,
      r86_KBox_lo,r86_KBox_hi]
    mixed_fixed
  have hh : (8997/10000:ℝ)<(valueBox 1 (9/100) (by norm_num) hr).lo := by
    rw [r86_valueBox_lo]
    simp only [Interval.point,Interval.add,Interval.sub,Interval.mul,Interval.square,
      r86_KBox_lo,r86_KBox_hi,r86_vBox_lo,r86_vBox_hi,rootSix,SecondWord.OppositeThree.ReferenceAlgebra.rootThree,
      SecondWord.OppositeThree.ReferenceAlgebra.rootStep,vRadicand,
      c,p,q,P]
    mixed_fixed
  exact hh.trans_le (valueBox 1 (9/100) (by norm_num) hr).mem.1

theorem first_at_nine : (1/20:ℝ)<F1 1 (9/100) := by
  have hr : 0≤(vRadicand (9/100) (by norm_num)).lo := by
    simp only [vRadicand,Interval.point,Interval.sub,Interval.square,Interval.mul,
      r86_KBox_lo,r86_KBox_hi]
    mixed_fixed
  have hv : 0<(vBox (9/100) (by norm_num) hr).lo := by
    simp only [Interval.point,Interval.sub,Interval.square,Interval.mul,
      r86_KBox_lo,r86_KBox_hi,r86_vBox_lo,rootSix,SecondWord.OppositeThree.ReferenceAlgebra.rootThree,
      SecondWord.OppositeThree.ReferenceAlgebra.rootStep,vRadicand]
    mixed_fixed
  have hh : (1/20:ℝ)<(firstBox 1 (9/100) (by norm_num) hr hv).lo := by
    rw [r86_firstBox_lo]
    simp only [Interval.point,Interval.add,Interval.sub,Interval.mul,Interval.square,
      Interval.div,Interval.inv,r86_KBox_lo,r86_KBox_hi,r86_vBox_lo,r86_vBox_hi,r86_hBox_lo,
      r86_hBox_hi,rootSix,SecondWord.OppositeThree.ReferenceAlgebra.rootThree,
      SecondWord.OppositeThree.ReferenceAlgebra.rootStep,vRadicand,p,q]
    mixed_fixed
  exact hh.trans_le (firstBox 1 (9/100) (by norm_num) hr hv).mem.1

theorem zero_value_at_event_lower : (1159/1250:ℝ)<F 0 (134/1250) := by
  have hr : 0≤(vRadicand (134/1250) (by norm_num)).lo := by
    simp only [vRadicand,Interval.point,Interval.sub,Interval.square,Interval.mul,
      r86_KBox_lo,r86_KBox_hi]
    mixed_fixed
  have hh : (1159/1250:ℝ)<(valueBox 0 (134/1250) (by norm_num) hr).lo := by
    rw [r86_valueBox_lo]
    simp only [Interval.point,Interval.add,Interval.sub,Interval.mul,Interval.square,
      r86_KBox_lo,r86_KBox_hi,r86_vBox_lo,r86_vBox_hi,rootSix,SecondWord.OppositeThree.ReferenceAlgebra.rootThree,
      SecondWord.OppositeThree.ReferenceAlgebra.rootStep,vRadicand,
      c,p,q,P]
    mixed_fixed
  exact hh.trans_le (valueBox 0 (134/1250) (by norm_num) hr).mem.1

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper.Reference
