module

public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterNegativeEndpoint

/-!
# Eight squares: the named references for the twelve negative-core endpoint curves

Eight references bound H-H'^2/1.3, and the other
four curves use their initial positive derivative. Every radical is
enclosed on its actual expression by positive rational square bounds.
The whole-interval curvature was proved before these substitutions.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.Endpoint
open CommonQuarter Arithmetic StationaryPrimitives Reference

def AABox (diagonal : Bool) : Interval (AA diagonal) := by
  cases diagonal
  · exact Interval.point _
  · exact coreDiagonal.add (Interval.point (1/2))
def BBBox (diagonal : Bool) : Interval (BB diagonal) := by
  cases diagonal
  · exact Interval.point _
  · exact coreDiagonal.sub (Interval.point (1/2))
def bCBox (diagonal : Bool) : Interval (bC diagonal) := by
  cases diagonal
  · exact Interval.point _
  · exact coreDiagonal

def heightBox (diagonal : Bool) {φ : ℝ} (S : Interval (Real.sin φ)) (C : Interval (Real.cos φ)) :
    Interval (height diagonal φ) :=
  ((Interval.point 1).add ((AABox diagonal).mul C)).sub ((BBBox diagonal).mul S)
def radicandBox {u : ℝ} (U : Interval u) : Interval (Q0-u^2) :=
  (Interval.point Q0).sub U.square
def radicalBox {u : ℝ} (U : Interval u) (hU : 0≤(radicandBox U).lo) : Interval (v u) :=
  rootSix (radicandBox U) (3/2) (by norm_num) hU
def valueBox (r : Row) (diagonal : Bool) {φ : ℝ} (Phi : Interval φ)
    (U : Interval (height diagonal φ)) (V : Interval (v (height diagonal φ))) :
    Interval (H r diagonal φ) := by
  convert ((((Phi.add (Interval.point (ocC r))).add
    ((Interval.point (ocP r)).mul (U.sub (Interval.point (1/2))))).sub
      ((Interval.point (ocQ r)).mul (V.sub (Interval.point (1/2))))).add
        ((Interval.point (ocG r)).mul (bCBox diagonal))) using 1 <;>
    dsimp [H,M] <;> simp only [sub_add_cancel] <;> ring
def firstBox (r : Row) (diagonal : Bool) {φ : ℝ}
    (S : Interval (Real.sin φ)) (C : Interval (Real.cos φ))
    (U : Interval (height diagonal φ)) (V : Interval (v (height diagonal φ))) (hV : 0<V.lo) :
    Interval (Hd r diagonal φ) := by
  convert (Interval.point 1).sub
    (((Interval.point (ocP r)).add (((Interval.point (ocQ r)).mul U).div V hV)).mul
      (((AABox diagonal).mul S).add ((BBBox diagonal).mul C))) using 1 <;>
    dsimp [Hd,M1,speed] <;> simp only [sub_add_cancel]

private lemma r83_mpr_lo {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).lo=S.lo := by subst e; rfl
private lemma r83_mpr_hi {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).hi=S.hi := by subst e; rfl
private lemma r83_value_eq (r : Row) (diagonal : Bool) (φ : ℝ) :
    H r diagonal φ=φ+ocC r+ocP r*(height diagonal φ-1/2)-ocQ r*(v (height diagonal φ)-1/2)+
      ocG r*bC diagonal := by
  dsimp [H,M]; simp only [sub_add_cancel]; ring
private lemma r83_valueBox_lo (r : Row) (diagonal : Bool) {φ : ℝ} (Phi : Interval φ)
    (U : Interval (height diagonal φ)) (V : Interval (v (height diagonal φ))) :
    (valueBox r diagonal Phi U V).lo=((((Phi.add (Interval.point (ocC r))).add
      ((Interval.point (ocP r)).mul (U.sub (Interval.point (1/2))))).sub
        ((Interval.point (ocQ r)).mul (V.sub (Interval.point (1/2))))).add
          ((Interval.point (ocG r)).mul (bCBox diagonal))).lo :=
  r83_mpr_lo (r83_value_eq r diagonal φ) _ _
private lemma r83_first_eq (r : Row) (diagonal : Bool) (φ : ℝ) :
    Hd r diagonal φ=1-(ocP r+ocQ r*height diagonal φ/v (height diagonal φ))*
      (AA diagonal*Real.sin φ+BB diagonal*Real.cos φ) := by
  dsimp [Hd,M1,speed]; simp only [sub_add_cancel]
private lemma r83_firstBox_lo (r : Row) (diagonal : Bool) {φ : ℝ}
    (S : Interval (Real.sin φ)) (C : Interval (Real.cos φ))
    (U : Interval (height diagonal φ)) (V : Interval (v (height diagonal φ))) (hV : 0<V.lo) :
    (firstBox r diagonal S C U V hV).lo=((Interval.point 1).sub
      (((Interval.point (ocP r)).add (((Interval.point (ocQ r)).mul U).div V hV)).mul
        (((AABox diagonal).mul S).add ((BBBox diagonal).mul C)))).lo :=
  r83_mpr_lo (r83_first_eq r diagonal φ) _ _
private lemma r83_firstBox_hi (r : Row) (diagonal : Bool) {φ : ℝ}
    (S : Interval (Real.sin φ)) (C : Interval (Real.cos φ))
    (U : Interval (height diagonal φ)) (V : Interval (v (height diagonal φ))) (hV : 0<V.lo) :
    (firstBox r diagonal S C U V hV).hi=((Interval.point 1).sub
      (((Interval.point (ocP r)).add (((Interval.point (ocQ r)).mul U).div V hV)).mul
        (((AABox diagonal).mul S).add ((BBBox diagonal).mul C)))).hi :=
  r83_mpr_hi (r83_first_eq r diagonal φ) _ _
private lemma r83_rootStep_lo_pos {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo)
    (h : 0<X.lo) : 0<(SecondWord.OppositeThree.ReferenceAlgebra.rootStep X s hs hX).lo := by
  have hh : 0≤X.hi := hX.trans (X.mem.1.trans X.mem.2)
  dsimp [SecondWord.OppositeThree.ReferenceAlgebra.rootStep]
  positivity
private lemma r83_radicalBox_lo_pos {u : ℝ} (U : Interval u) (hU : 0≤(radicandBox U).lo)
    (h : 0<(radicandBox U).lo) : 0<(radicalBox U hU).lo := by
  unfold radicalBox rootSix SecondWord.OppositeThree.ReferenceAlgebra.rootThree
  exact r83_rootStep_lo_pos _ _ _ _ h

local macro "r83_fixed" : tactic => `(tactic|
  norm_num [r83_valueBox_lo,r83_firstBox_lo,r83_firstBox_hi,
    radicandBox,radicalBox,heightBox,AABox,BBBox,bCBox,AA,BB,bC,
    Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
    piBox,halfPi,coreDiagonal,Reference.sine,Reference.cosine,
    rootSix,SecondWord.OppositeThree.ReferenceAlgebra.rootThree,
    SecondWord.OppositeThree.ReferenceAlgebra.rootStep,HighOrderTaylor.S15,HighOrderTaylor.S13,
    HighOrderTaylor.S11,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8,
    ocC,ocP,ocQ,ocG,Q0])

def reference (r : Row) (diagonal : Bool) : ℝ :=
  if r=0 then (if diagonal then 43/40 else 117/100)
  else if r=4 then (if diagonal then 1047/1000 else 1149/1000)
  else if r=11 then (if diagonal then 481/500 else 1061/1000)
  else if r=23 then (if diagonal then 132/125 else 287/250)
  else 1
theorem reference_positive (r : Row) (diagonal : Bool) : 0≤reference r diagonal := by
  fin_cases r <;> cases diagonal <;> norm_num [reference]
theorem reference_mem (r : Row) (diagonal : Bool) : reference r diagonal∈earlyAngles := by
  fin_cases r <;> cases diagonal <;> norm_num [reference,earlyAngles,lowerAngle] <;>
    linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]
def refS (r : Row) (diagonal : Bool) : Interval (Real.sin (reference r diagonal)) :=
  sine (reference_positive r diagonal)
def refC (r : Row) (diagonal : Bool) : Interval (Real.cos (reference r diagonal)) :=
  cosine (reference_positive r diagonal)
def refU (r : Row) (diagonal : Bool) : Interval (height diagonal (reference r diagonal)) :=
  heightBox diagonal (refS r diagonal) (refC r diagonal)
private lemma r83_radicand_at (diagonal : Bool) {x : ℝ} (hx : 0≤x)
    (hv : (diagonal=true ∧ (x=43/40 ∨ x=1047/1000 ∨ x=481/500 ∨ x=132/125 ∨ x=1)) ∨
      (diagonal=false ∧ (x=117/100 ∨ x=1149/1000 ∨ x=1061/1000 ∨ x=287/250 ∨ x=1))) :
    0<(radicandBox (heightBox diagonal (Reference.sine hx) (Reference.cosine hx))).lo := by
  rcases hv with ⟨rfl,rfl|rfl|rfl|rfl|rfl⟩|⟨rfl,rfl|rfl|rfl|rfl|rfl⟩ <;> r83_fixed
private lemma r83_ref_radicand_pos (r : Row) (diagonal : Bool) :
    0<(radicandBox (refU r diagonal)).lo := by
  refine r83_radicand_at diagonal (reference_positive r diagonal) ?_
  cases diagonal <;> simp only [reference,Bool.false_eq_true,↓reduceIte] <;> split_ifs <;> norm_num
theorem ref_radicand (r : Row) (diagonal : Bool) : 0≤(radicandBox (refU r diagonal)).lo :=
  (r83_ref_radicand_pos r diagonal).le
def refV (r : Row) (diagonal : Bool) : Interval (v (height diagonal (reference r diagonal))) :=
  radicalBox (refU r diagonal) (ref_radicand r diagonal)
theorem refV_positive (r : Row) (diagonal : Bool) : 0<(refV r diagonal).lo :=
  r83_radicalBox_lo_pos _ _ (r83_ref_radicand_pos r diagonal)
def refH (r : Row) (diagonal : Bool) : Interval (H r diagonal (reference r diagonal)) :=
  valueBox r diagonal (Interval.point _) (refU r diagonal) (refV r diagonal)
def refHd (r : Row) (diagonal : Bool) : Interval (Hd r diagonal (reference r diagonal)) :=
  firstBox r diagonal (refS r diagonal) (refC r diagonal) (refU r diagonal) (refV r diagonal)
    (refV_positive r diagonal)
def refQuadratic (r : Row) (diagonal : Bool) :
    Interval (H r diagonal (reference r diagonal)-(Hd r diagonal (reference r diagonal))^2/(13/10)) :=
  (refH r diagonal).sub ((refHd r diagonal).square.div (Interval.point (13/10)) (by norm_num [Interval.point]))

private lemma r83_quad_at (r : Row) (diagonal : Bool) {x : ℝ} (hx : 0≤x)
    (hR : 0≤(radicandBox (heightBox diagonal (Reference.sine hx) (Reference.cosine hx))).lo)
    (hV : 0<(radicalBox (heightBox diagonal (Reference.sine hx) (Reference.cosine hx)) hR).lo)
    (hv : (r=0 ∧ ((diagonal=true ∧ x=43/40) ∨ (diagonal=false ∧ x=117/100))) ∨
      (r=4 ∧ ((diagonal=true ∧ x=1047/1000) ∨ (diagonal=false ∧ x=1149/1000))) ∨
      (r=11 ∧ ((diagonal=true ∧ x=481/500) ∨ (diagonal=false ∧ x=1061/1000))) ∨
      (r=23 ∧ ((diagonal=true ∧ x=132/125) ∨ (diagonal=false ∧ x=287/250)))) :
    (89809/100000:ℝ)<((valueBox r diagonal (Interval.point x)
      (heightBox diagonal (Reference.sine hx) (Reference.cosine hx)) (radicalBox _ hR)).sub
        ((firstBox r diagonal (Reference.sine hx) (Reference.cosine hx)
          (heightBox diagonal (Reference.sine hx) (Reference.cosine hx)) (radicalBox _ hR) hV).square.div
            (Interval.point (13/10)) (by norm_num [Interval.point]))).lo := by
  simp only [Interval.sub,Interval.div,Interval.square,Interval.mul,Interval.inv]
  rw [r83_valueBox_lo,r83_firstBox_lo,r83_firstBox_hi]
  rcases hv with ⟨rfl,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩|⟨rfl,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩|⟨rfl,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩|
    ⟨rfl,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ <;> r83_fixed

theorem reference_reserve (r : Row) (hr : r=0∨r=4∨r=11∨r=23) (diagonal : Bool) :
    (89809/100000:ℝ)<H r diagonal (reference r diagonal)-(Hd r diagonal (reference r diagonal))^2/(13/10) := by
  have hbound : (89809/100000:ℝ)<(refQuadratic r diagonal).lo :=
    r83_quad_at r diagonal (reference_positive r diagonal) (ref_radicand r diagonal)
      (refV_positive r diagonal)
      (by rcases hr with rfl|rfl|rfl|rfl <;> cases diagonal <;> norm_num [reference])
  exact hbound.trans_le (refQuadratic r diagonal).mem.1

def initialPhi : Interval lowerAngle := halfPi.sub (Interval.point (7/10))
def initialS : Interval (Real.sin lowerAngle) := by
  convert cosine (by norm_num : (0:ℝ)≤7/10) using 1
  exact Real.sin_pi_div_two_sub (7/10)
def initialC : Interval (Real.cos lowerAngle) := by
  convert sine (by norm_num : (0:ℝ)≤7/10) using 1
  exact Real.cos_pi_div_two_sub (7/10)
private lemma r83_initialS_lo : initialS.lo=(Reference.cosine (by norm_num : (0:ℝ)≤7/10)).lo :=
  r83_mpr_lo (Real.sin_pi_div_two_sub (7/10)) _ _
private lemma r83_initialS_hi : initialS.hi=(Reference.cosine (by norm_num : (0:ℝ)≤7/10)).hi :=
  r83_mpr_hi (Real.sin_pi_div_two_sub (7/10)) _ _
private lemma r83_initialC_lo : initialC.lo=(Reference.sine (by norm_num : (0:ℝ)≤7/10)).lo :=
  r83_mpr_lo (Real.cos_pi_div_two_sub (7/10)) _ _
private lemma r83_initialC_hi : initialC.hi=(Reference.sine (by norm_num : (0:ℝ)≤7/10)).hi :=
  r83_mpr_hi (Real.cos_pi_div_two_sub (7/10)) _ _
def initialU (diagonal : Bool) : Interval (height diagonal lowerAngle) := heightBox diagonal initialS initialC
private lemma r83_initial_radicand_pos (diagonal : Bool) : 0<(radicandBox (initialU diagonal)).lo := by
  cases diagonal <;>
    simp only [radicandBox,initialU,heightBox,Interval.sub,Interval.add,Interval.square,Interval.mul,
      r83_initialS_lo,r83_initialS_hi,r83_initialC_lo,r83_initialC_hi] <;> r83_fixed
theorem initial_radicand (diagonal : Bool) : 0≤(radicandBox (initialU diagonal)).lo :=
  (r83_initial_radicand_pos diagonal).le
def initialV (diagonal : Bool) : Interval (v (height diagonal lowerAngle)) :=
  radicalBox (initialU diagonal) (initial_radicand diagonal)
theorem initialV_positive (diagonal : Bool) : 0<(initialV diagonal).lo :=
  r83_radicalBox_lo_pos _ _ (r83_initial_radicand_pos diagonal)
def initialH (r : Row) (diagonal : Bool) : Interval (H r diagonal lowerAngle) :=
  valueBox r diagonal initialPhi (initialU diagonal) (initialV diagonal)
def initialHd (r : Row) (diagonal : Bool) : Interval (Hd r diagonal lowerAngle) :=
  firstBox r diagonal initialS initialC (initialU diagonal) (initialV diagonal) (initialV_positive diagonal)

theorem initial_reserve (r : Row) (hr : r=12∨r=19) (diagonal : Bool) :
    (89809/100000:ℝ)<H r diagonal lowerAngle ∧ 0<Hd r diagonal lowerAngle := by
  have hv : (89809/100000:ℝ)<(initialH r diagonal).lo := by
    unfold initialH
    rw [r83_valueBox_lo]
    unfold initialV initialU initialPhi
    simp only [Interval.sub,Interval.add,Interval.mul,heightBox,
      r83_initialS_lo,r83_initialS_hi,r83_initialC_lo,r83_initialC_hi]
    rcases hr with rfl|rfl <;> cases diagonal <;> r83_fixed
  have hd : 0<(initialHd r diagonal).lo := by
    unfold initialHd
    rw [r83_firstBox_lo]
    unfold initialV initialU
    simp only [Interval.sub,Interval.add,Interval.mul,Interval.div,Interval.inv,heightBox,
      r83_initialS_lo,r83_initialS_hi,r83_initialC_lo,r83_initialC_hi]
    rcases hr with rfl|rfl <;> cases diagonal <;> r83_fixed
  exact ⟨hv.trans_le (initialH r diagonal).mem.1,hd.trans_le (initialHd r diagonal).mem.1⟩

theorem lower (r : Row) (hr : Remaining r) (diagonal : Bool) {φ : ℝ}
    (hφ : φ∈earlyAngles) : (89809/100000:ℝ)<H r diagonal φ := by
  by_cases hi : r=12∨r=19
  · have h := curvature_tangent (κ:=(13/20:ℝ)) hφ early_left
      (fun t ht => H_hasDerivAt r diagonal ht)
      (fun t ht => Hd_hasDerivAt r diagonal ht)
      (fun t ht => (curvature r hr diagonal ht).le)
    have hinit := initial_reserve r hi diagonal
    have hp := mul_nonneg hinit.2.le (sub_nonneg.mpr hφ.1)
    nlinarith [sq_nonneg (φ-lowerAngle)]
  · have hrows : r=0∨r=4∨r=11∨r=23 := by
      rcases (remaining_iff r).1 hr with h|h|h|h|h|h <;> simp_all
    have href := reference_reserve r hrows diagonal
    have h := positive_of_curvature (f:=fun t => H r diagonal t-89809/100000)
      (d:=Hd r diagonal) (dd:=Hdd r diagonal) (κ:=(13/20:ℝ)) (by norm_num)
      hφ (reference_mem r diagonal)
      (fun t ht => (H_hasDerivAt r diagonal ht).sub_const (89809/100000))
      (fun t ht => Hd_hasDerivAt r diagonal ht)
      (fun t ht => (curvature r hr diagonal ht).le) (by nlinarith)
    linarith

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.Endpoint
