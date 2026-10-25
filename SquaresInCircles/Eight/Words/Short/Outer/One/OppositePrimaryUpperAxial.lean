module

public import SquaresInCircles.Eight.Arithmetic.WholeIntervalPolynomial
public import SquaresInCircles.Eight.Owners.Stationary.TerminalWeights
public import SquaresInCircles.Eight.Stationary.System
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroLReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroAsymmetric
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroCycle
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterReferences
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryUpperAxialData
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryNegativeGeometry
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryDiagonalData

/-!
# Eight squares: the axial part of the six upper primary contacts

The exceptional row 1 is reduced to its axial boundary and to the interval beginning at `.09`
(`before_one_after_nine`); its earlier interior contacts are left to the exact
angular-stationarity argument. The other rows are `before_zero` and `before_simple`.
-/

section
/-!
## Named axial reference values for the upper primary owners

All enclosures concern the displayed individual references 0, .09 and
.1072. They use positive squaring and the adjacent alternating Taylor
polynomials; no angle-domain subdivision is a premise.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper.Reference
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

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper.Reference
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD)

theorem axial_tangent (r : Row) {e x y κ : ℝ} (he : IsEvent e)
    (hx : x∈Icc 0 e) (hy : y∈Icc 0 e) (hκ : ∀u∈Icc 0 e,κ≤F2 r u) :
    F r y+F1 r y*(x-y)+κ/2*(x-y)^2≤F r x :=
  curvature_tangent hx hy (fun _ hu => F_hasDerivAt r he hu)
    (fun _ hu => F1_hasDerivAt r he hu) hκ

theorem F_zero_linear {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    (44913/50000:ℝ)+(49/250)*x<F 0 x := by
  have ht := axial_tangent 0 he hx ⟨le_rfl,by linarith [(event_bounds he).1]⟩
    (fun u hu => (axial_curvature_zero he hu).le)
  have hF := Reference.initial_value 0
  norm_num [Reference.initialLower] at hF
  have hp := mul_le_mul_of_nonneg_right Reference.initial_first_zero.le hx.1
  nlinarith [sq_nonneg x]

theorem F_zero_increasing {e : ℝ} (he : IsEvent e) : MonotoneOn (F 0) (Icc 0 e) := by
  have hm : MonotoneOn (F1 0) (Icc 0 e) :=
    monoOn_of_hasDeriv_nonneg
      (fun x hx => (F1_hasDerivAt 0 he hx).continuousAt.continuousWithinAt)
      (fun x hx => F1_hasDerivAt 0 he (Ioo_subset_Icc_self hx))
      (fun x hx => by linarith [axial_curvature_zero he (Ioo_subset_Icc_self hx)])
  apply monoOn_of_hasDeriv_nonneg
    (fun x hx => (F_hasDerivAt 0 he hx).continuousAt.continuousWithinAt)
    (fun x hx => F_hasDerivAt 0 he (Ioo_subset_Icc_self hx))
  intro x hx
  have hh := hm ⟨le_rfl,by linarith [(event_bounds he).1]⟩ (Ioo_subset_Icc_self hx) hx.1.le
  linarith [Reference.initial_first_zero]

theorem axial_ratioD_upper {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    ratioD (contact 0 x)≤Q0/(129/100:ℝ)^3 := by
  have hv := (axial_bounds he hx).2.2.1
  have hp : 0<v x := by linarith
  have hc := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤129/100) hv.le 3
  change Q0/(v x)^3≤Q0/(129/100:ℝ)^3
  apply (div_le_iff₀ (pow_pos hp 3)).2
  norm_num [Q0] at *
  nlinarith

theorem H_zero_derivative {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    -(52/25:ℝ)<H1 0 x := by
  have hb := axial_bounds he hx
  have hg := projection_early he hx
  have hD := axial_ratioD_upper he hx
  have hL := sourceD_lower 0 (before_domain he hx).2.2
  norm_num [p,q] at hL
  have hh0 : 0≤h x := by linarith [hb.2.2.2.2.1]
  have hq0 : q 0=119909/100000 := by norm_num [q]
  have h1 := mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left hD (show 0≤q 0 by norm_num [q]))
      hb.2.2.2.2.2.1.le hh0 (mul_nonneg (by norm_num [q]) (by norm_num [Q0])))
      hg.2.1.le (by linarith [hg.1] : 0≤projection x) (by norm_num [q,Q0])
  have h2 := mul_le_mul hL hg.2.2.1.le (by norm_num)
    (by linarith : 0≤ sourceD 0 (contact 0 x))
  dsimp only [H1,sourceDD]
  rw [hq0] at h1 ⊢
  norm_num [Q0] at h1
  linarith

theorem H_zero_lower {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    -(27/1000:ℝ)-(52/25)*x<H 0 x := by
  have hh := derivative_reserve
    (fun y hy => (H_hasDerivAt 0 he hy).continuousAt.continuousWithinAt)
    (fun y hy => H_hasDerivAt 0 he (Ioo_subset_Icc_self hy))
    (fun y hy => (H_zero_derivative he (Ioo_subset_Icc_self hy)).le)
    (show (0:ℝ)∈Icc 0 e from ⟨le_rfl,by linarith [(event_bounds he).1]⟩) hx hx.1
  linarith [Reference.initial_H_zero]

theorem H_one_decreasing {e : ℝ} (he : IsEvent e) : AntitoneOn (H 1) (Icc 0 e) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun x hx => (H_hasDerivAt 1 he hx).continuousAt.continuousWithinAt)
    (fun x hx => H_hasDerivAt 1 he (Ioo_subset_Icc_self hx))
  intro x hx
  have hx' := Ioo_subset_Icc_self hx
  have hb := axial_bounds he hx'
  have hg := projection_early he hx'
  have hD := source_ratioD_lower (before_domain he hx').2.2
  have hL := axial_sourceD_upper 1 he hx'
  have hd0 := (SameContact.ratioD_pos (Same.primary_domain (before_domain he hx').2.2)).le
  have hh0 : 0≤h x := by linarith [hb.2.2.2.2.1]
  have hq1 : q 1=88074/100000 := by norm_num [q]
  have h1 := mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left hD (show 0≤q 1 by norm_num [q]))
      (show (227/250:ℝ)≤h x by linarith [hb.2.2.2.2.1]) (by norm_num)
      (mul_nonneg (by norm_num [q]) hd0))
      hg.1 (by norm_num) (mul_nonneg (mul_nonneg (by norm_num [q]) hd0) hh0)
  have h2 := mul_le_mul hL.le hg.2.2.2.le
    (by linarith [hg.2.2.1] : 0≤projectionD x) (by norm_num [p,q])
  dsimp only [H1,sourceDD]
  rw [hq1] at h1 ⊢
  norm_num [p,q,Q0] at h1 h2
  linarith

theorem event_trig {e : ℝ} (he : IsEvent e) :
    (10679/100000:ℝ)<Real.sin e ∧ Real.sin e<(21419/200000:ℝ) ∧
      (124281/125000:ℝ)<Real.cos e ∧ Real.cos e<(49713/50000:ℝ) := by
  have hsl : (10679/100000:ℝ)<(ShortOuterZero.Same.Event.eventSin he).lo := by
    dsimp [ShortOuterZero.Same.Event.eventSin]
    event_reference_arithmetic
  have hsu : (ShortOuterZero.Same.Event.eventSin he).hi<(21419/200000:ℝ) := by
    dsimp [ShortOuterZero.Same.Event.eventSin]
    event_reference_arithmetic
  have hcl : (124281/125000:ℝ)<(ShortOuterZero.Same.Event.eventCos he).lo := by
    dsimp [ShortOuterZero.Same.Event.eventCos]
    event_reference_arithmetic
  have hcu : (ShortOuterZero.Same.Event.eventCos he).hi<(49713/50000:ℝ) := by
    dsimp [ShortOuterZero.Same.Event.eventCos]
    event_reference_arithmetic
  exact ⟨hsl.trans_le (ShortOuterZero.Same.Event.eventSin he).mem.1,
    (ShortOuterZero.Same.Event.eventSin he).mem.2.trans_lt hsu,
    hcl.trans_le (ShortOuterZero.Same.Event.eventCos he).mem.1,
    (ShortOuterZero.Same.Event.eventCos he).mem.2.trans_lt hcu⟩

theorem H_one_at_event {e : ℝ} (he : IsEvent e) : -(71/1000:ℝ)<H 1 e := by
  have ht := event_trig he
  have hsin := mul_le_mul rho_bounds.1.le ht.1.le (by norm_num)
    (by linarith [rho_bounds.1] : 0≤rho)
  have he2 : contact 0 e=outerDiagonal := he.2
  have hid : H 1 e=(p 1+q 1)*projection e+P 1*rho-t 1 := by
    dsimp [H,first,sourceD,stateSpeed,SecondWord.SameZero.k]
    rw [he2,ratio_zero,ratio_diagonal]
    dsimp [projection]
    ring
  rw [hid]
  norm_num [p,q,P,t,projection]
  linarith [rho_bounds.1,ht.2.2.1]

theorem H_one_lower {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    -(71/1000:ℝ)<H 1 x :=
  (H_one_at_event he).trans_le ((H_one_decreasing he) hx
    ⟨by linarith [(event_bounds he).1],le_rfl⟩ hx.2)

theorem F_pair_lower (r : Row) (hr : r=3∨r=4) {e x : ℝ}
    (he : IsEvent e) (hx : x∈Icc 0 e) : (4489/5000:ℝ)<F r x := by
  have ht := axial_tangent r he hx ⟨le_rfl,by linarith [(event_bounds he).1]⟩
    (fun u hu => (axial_curvature_pair r hr he hu).le)
  have hF := Reference.initial_value r
  have hD := Reference.initial_first_pair r hr
  have hp := mul_le_mul_of_nonneg_right hD.le hx.1
  have hs := sq_nonneg (x/4-1/125)
  rcases hr with rfl | rfl <;> norm_num [Reference.initialLower] at hF <;> nlinarith

theorem F_one_lower {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    (4489/5000:ℝ)<F 1 x := by
  have ht := axial_tangent 1 he hx ⟨le_rfl,by linarith [(event_bounds he).1]⟩
    (fun u hu => (axial_curvature_one he hu).le)
  have hF := Reference.initial_value 1
  norm_num [Reference.initialLower] at hF
  have hp := mul_le_mul_of_nonneg_right Reference.initial_first_one.le hx.1
  nlinarith [sq_nonneg ((47/100)*x-1/50)]

theorem F_one_after_nine {e x : ℝ} (he : IsEvent e) (hx : x∈Icc (9/100) e) :
    (8997/10000:ℝ)<F 1 x := by
  have h9 : (9/100:ℝ)∈Icc 0 e := ⟨by norm_num,by linarith [(event_bounds he).1]⟩
  have ht := axial_tangent 1 he ⟨by linarith [hx.1],hx.2⟩ h9
    (fun u hu => (axial_curvature_one he hu).le)
  have hp := mul_nonneg (by linarith [Reference.first_at_nine] : (0:ℝ)≤F1 1 (9/100))
    (sub_nonneg.mpr hx.1)
  linarith [Reference.value_at_nine,sq_nonneg (x-9/100)]

theorem simple_axial_first (r : Row) (hr : r=2∨r=5) {e x : ℝ}
    (he : IsEvent e) (hx : x∈Icc 0 e) :
    (if r=2 then (1/50:ℝ) else -(1/10))<F1 r x := by
  have hb := axial_bounds he hx
  have hL := axial_sourceD_upper r he hx
  have hL0 : 0≤ sourceD r (contact 0 x) := by
    linarith [sourceD_lower r (before_domain he hx).2.2,(coefficients r).2.2.1]
  have hp := mul_le_mul hL.le hb.2.2.2.2.2.1.le
    (by linarith [hb.2.2.2.2.1] : 0≤h x) (by linarith)
  simp only [h] at hp
  dsimp only [F1,angleFirst]
  rcases hr with rfl | rfl <;> norm_num [p,q] at hp ⊢ <;> linarith

theorem F_simple_lower (r : Row) (hr : r=2∨r=5) {e x : ℝ}
    (he : IsEvent e) (hx : x∈Icc 0 e) : (449/500:ℝ)<F r x := by
  have hh := derivative_reserve
    (fun u hu => (F_hasDerivAt r he hu).continuousAt.continuousWithinAt)
    (fun u hu => F_hasDerivAt r he (Ioo_subset_Icc_self hu))
    (fun u hu => (simple_axial_first r hr he (Ioo_subset_Icc_self hu)).le)
    (show (0:ℝ)∈Icc 0 e from ⟨le_rfl,by linarith [(event_bounds he).1]⟩) hx hx.1
  have hF := Reference.initial_value r
  have hcap : x<(27/250:ℝ) := by linarith [hx.2,(event_bounds he).2.1]
  have hx0 := hx.1
  rcases hr with rfl | rfl <;> norm_num [Reference.initialLower] at hh hF <;> linarith

theorem H_simple_positive (r : Row) (hr : r=2∨r=3∨r=4∨r=5) {e x : ℝ}
    (he : IsEvent e) (hx : x∈Icc 0 e) : 0<H r x := by
  have hL := sourceD_lower r (before_domain he hx).2.2
  have hg := projection_early he hx
  have hmul := mul_le_mul hL hg.1 (by norm_num)
    (by linarith [hL,(coefficients r).2.2.1] : 0≤ sourceD r (contact 0 x))
  have hid : H r x=sourceD r (contact 0 x)*projection x+P r*rho-t r := by
    dsimp [H,first,stateSpeed,SecondWord.SameZero.k,projection]
    rw [ratio_zero]
  rw [hid]
  rcases hr with rfl | rfl | rfl | rfl <;>
    norm_num [p,q,P,t] at hmul ⊢ <;> linarith [rho_bounds.2]

def zeroAxialLower (x : ℝ) : ℝ :=
  44913/50000+(49/250)*x-(27/1000+(52/25)*x)^2/(78/25)

theorem zeroAxialLower_bound {x : ℝ} (hx : x∈Icc 0 (27/250)) : (449/500:ℝ)<zeroAxialLower x := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (27/250)) zeroAxialLower := by
    apply concave_of_deriv2
      (f':=fun y => 49/250-2*(52/25)/(78/25)*(27/1000+(52/25)*y))
      (f'':=fun _ => -2*(52/25)^2/(78/25))
    · intro y _
      have hh := (((hasDerivAt_id' y).const_mul (49/250:ℝ)).const_add (44913/50000)).fun_sub
        (((((hasDerivAt_id' y).const_mul (52/25:ℝ)).const_add (27/1000)).fun_pow 2).div_const
          (78/25))
      exact hh.congr_deriv (by norm_num; ring)
    · intro y _
      have hh := ((((hasDerivAt_id' y).const_mul (52/25:ℝ)).const_add (27/1000)).const_mul
        (2*(52/25)/(78/25):ℝ)).const_sub (49/250)
      exact hh.congr_deriv (by norm_num)
    · intro y _
      norm_num
  exact concave_gt_of_endpoints hc hx (by norm_num [zeroAxialLower]) (by norm_num [zeroAxialLower])

theorem before_zero {B e x : ℝ} (he : IsEvent e) (hd : Domain B x) (hx : x≤e) :
    (449/500:ℝ)<value 0 B x := by
  have hx' : x∈Icc 0 e := ⟨hd.2.1.1,hx⟩
  have hH : -(27/1000:ℝ)-(52/25)*x<first 0 0 x := H_zero_lower he hx'
  have hh := contact_remainder 0 (before_domain he hx') hd hd.1.1
    (by norm_num : (0:ℝ)<39/25)
    (show 0≤(27/1000:ℝ)+(52/25)*x by linarith [hd.2.1.1])
    (by linarith : -(27/1000+(52/25)*x)≤first 0 0 x)
    (fun E hE => (early_curvature_zero he (between_domain (before_domain he hx') hd hE) hx).le)
  have hF := F_zero_linear he hx'
  have hbound := zeroAxialLower_bound
    (show x∈Icc 0 (27/250) from ⟨hd.2.1.1,by linarith [hx,(event_bounds he).2.1]⟩)
  dsimp only [zeroAxialLower,F] at hF hbound
  have e : (27/1000+(52/25)*x)^2/(2*(39/25):ℝ)=(27/1000+(52/25)*x)^2/(78/25) := by norm_num
  rw [e] at hh
  linarith

theorem before_simple (r : Row) (hr : r=2∨r=3∨r=4∨r=5)
    {B e x : ℝ} (he : IsEvent e) (hd : Domain B x) (hx : x≤e) :
    (4489/5000:ℝ)<value r B x := by
  have hx' : x∈Icc 0 e := ⟨hd.2.1.1,hx⟩
  have hm := endpoint_minimum r (before_domain he hx') hd hd.1.1
    (H_simple_positive r hr he hx').le
  by_cases hpair : r=3∨r=4
  · exact (F_pair_lower r hpair he hx').trans_le hm
  · have hs : r=2∨r=5 := by rcases hr with h | h | h | h <;> tauto
    have hh := F_simple_lower r hs he hx'
    dsimp [F] at hh
    linarith

theorem before_one_after_nine {B e x : ℝ} (he : IsEvent e) (hd : Domain B x)
    (hx : x∈Icc (9/100) e) : (4489/5000:ℝ)<value 1 B x := by
  have hx' : x∈Icc 0 e := ⟨hd.2.1.1,hx.2⟩
  have hh := contact_remainder 1 (before_domain he hx') hd hd.1.1
    (by norm_num : (0:ℝ)<38/25) (by norm_num : (0:ℝ)≤71/1000)
    (H_one_lower he hx').le
    (fun E hE => (early_curvature_one he (between_domain (before_domain he hx') hd hE) hx.2).le)
  have hF := F_one_after_nine he hx
  dsimp [F] at hF
  norm_num at hh
  linarith

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper
end
end
end
