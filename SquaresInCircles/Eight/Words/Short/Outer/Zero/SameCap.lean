module

public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJBoundaryReferences
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositePositiveZeroGeometry
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameAxial

/-!
# Eight squares: the three final-angle target intervals

The target curvature is greater than `.33` throughout each final-angle contact interval
(`curvature`). One value-and-slope reference (`reference`, `references`) gives the minimum over
the whole interval by a single completion of the square (`lower`).
-/

section
/-!
## The six final-angle opposite-sign short-word supports

The six displayed multipliers
are evaluated only at the physical final angle .7. Positive source
coefficients use the two circle endpoints; negative source coefficients
use the written full-circle lower support. The target support is axial.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Cap
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra
open SecondWord.SameZero.PJ.Reference (sinBox cosBox dBox aBox)

abbrev radius : ℝ := Real.sqrt Q0
def weight : Row→ℝ := ![94766/100000,96135/100000,9994/10000,93/100,45181/50000,45181/50000]
def sourceBound (r : Row) : ℝ :=
  if 0≤p r then min (p r*outerAxial) ((p r+q r-weight r)*outerDiagonal)
  else -(p r+q r-weight r)/2-radius*Real.sqrt ((p r)^2+(q r-weight r)^2)
def scalar (r : Row) : ℝ := 7/10+c r+sourceBound r+weight r/2+v r*outerAxial+
  (weight r/2)*Real.cos (7/10)+weight r*(1/2-outerAxial)*Real.sin (7/10)

lemma full_circle_lower {a b X Y : ℝ} (hs : OuterState a b) :
    -(X+Y)/2-radius*Real.sqrt (X^2+Y^2)≤X*a+Y*b := by
  have hR0 := Real.sqrt_nonneg Q0
  have hR2 := Real.sq_sqrt (show 0≤Q0 by norm_num [Q0])
  have hN0 := Real.sqrt_nonneg (X^2+Y^2)
  have hN2 := Real.sq_sqrt (show 0≤X^2+Y^2 by positivity)
  have hproj : (X*(a+1/2)+Y*(b+1/2))^2≤Q0*(X^2+Y^2) := by
    have hsquare := sq_nonneg (X*(b+1/2)-Y*(a+1/2))
    have he : (X*(a+1/2)+Y*(b+1/2))^2+
        (X*(b+1/2)-Y*(a+1/2))^2=Q0*(X^2+Y^2) := by
      linear_combination (X^2+Y^2)*hs.2.2
    linarith
  have hproduct : 0≤radius*Real.sqrt (X^2+Y^2) := mul_nonneg hR0 hN0
  have hproduct2 : (radius*Real.sqrt (X^2+Y^2))^2=Q0*(X^2+Y^2) := by
    rw [mul_pow]
    exact congrArg₂ (·*·) hR2 hN2
  have hlower : -radius*Real.sqrt (X^2+Y^2)≤X*(a+1/2)+Y*(b+1/2) := by
    nlinarith
  linarith

lemma source_lower (r : Row) {a b : ℝ} (hs : OuterState a b) :
    sourceBound r≤p r*a+(q r-weight r)*b := by
  unfold sourceBound
  split_ifs with hp
  · refine WrongWordCircleSupport.outer_concave_lower hs hp (min_le_left _ _) ?_
    have hh := min_le_right (p r*outerAxial) ((p r+q r-weight r)*outerDiagonal)
    linarith
  · have e : -(p r+q r-weight r)/2=-(p r+(q r-weight r))/2 := by ring
    rw [e]
    exact full_circle_lower hs

lemma target_signs (r : Row) :
    v r-weight r*Real.sin (7/10)<0 ∧ 0<t r-weight r*Real.cos (7/10) := by
  have ht := CommonQuarter.cap_trig
  fin_cases r <;> norm_num [weight,v,t] <;>
    constructor <;> linarith [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]

lemma target_lower (r : Row) {A B : ℝ} (ht : OuterState A B) :
    (v r-weight r*Real.sin (7/10))*outerAxial≤
      (v r-weight r*Real.sin (7/10))*A+(t r-weight r*Real.cos (7/10))*B := by
  have hs := target_signs r
  apply WrongWordCircleSupport.outer_axial_lower ht hs.1.le
  have hp := mul_nonneg (show 0≤outerAxial+1/2 by linarith [outer_endpoint_bounds.1]) hs.2.le
  linarith

def intervalMin {x y : ℝ} (X : Interval x) (Y : Interval y) : Interval (min x y) :=
  Interval.of_bounds ⟨min_le_min X.mem.1 Y.mem.1,min_le_min X.mem.2 Y.mem.2⟩

def radiusBox : Interval radius := rootThree (Interval.point Q0) 2
  (by norm_num) (by norm_num [Interval.point,Q0])
def normSeed (r : Row) : ℝ := if r=3 then 1/8 else 1/4

def normBox (r : Row) : Interval (Real.sqrt ((p r)^2+(q r-weight r)^2)) :=
  rootThree (Interval.point ((p r)^2+(q r-weight r)^2)) (normSeed r)
    (by unfold normSeed; split_ifs <;> norm_num)
    (by dsimp [Interval.point]; positivity)

def sourceBox (r : Row) : Interval (sourceBound r) := by
  unfold sourceBound
  split_ifs with hp
  · exact intervalMin ((Interval.point (p r)).mul aBox)
      ((Interval.point (p r+q r-weight r)).mul dBox)
  · exact (Interval.point (-(p r+q r-weight r)/2)).sub (radiusBox.mul (normBox r))

lemma scalar_lower (r : Row) : (923/1000:ℝ)<scalar r := by
  have ht := CommonQuarter.cap_trig
  have ha := ShortOuterZero.fine_axial_bounds
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hR : radius<19788/10000 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num [Q0]
  have hR0 : 0≤radius := Real.sqrt_nonneg _
  have hS := mul_lt_mul'' (show outerAxial-1/2<176821959/125000000-1/2 by linarith [ha.2])
    ht.2.1 (by linarith [ha.1]) (by linarith [ht.1])
  have he : scalar r=7/10+c r+sourceBound r+weight r/2+v r*outerAxial+
      (weight r/2)*Real.cos (7/10)-weight r*((outerAxial-1/2)*Real.sin (7/10)) := by
    simp only [scalar]
    ring
  rw [he]
  have hr : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 := by fin_cases r <;> simp
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · have hb : sourceBound 0=0 := by norm_num [sourceBound,p,q,weight]
    rw [hb]
    norm_num [c,v,weight] at hS ⊢
    linarith [ht.2.2.1]
  · have hb : (1898/10000:ℝ)≤ sourceBound 1 := by
      norm_num [sourceBound,p,q,weight]
      constructor <;> linarith [ha.1,hd.1]
    norm_num [c,v,weight] at hb hS ⊢
    linarith [ht.2.2.1]
  · have hb : sourceBound 2=0 := by norm_num [sourceBound,p,q,weight]
    rw [hb]
    norm_num [c,v,weight] at hS ⊢
    linarith [ht.2.2.1,ha.1]
  · have hN : Real.sqrt ((p 3)^2+(q 3-weight 3)^2)<10377/100000 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num [p,q,weight]
    have hm := mul_lt_mul'' hR hN hR0 (Real.sqrt_nonneg _)
    have hb : sourceBound 3=-(p 3+q 3-weight 3)/2-radius*Real.sqrt ((p 3)^2+(q 3-weight 3)^2) := by
      simp only [sourceBound]
      rw [ite_eq_right (by norm_num [p])]
    rw [hb]
    norm_num [c,p,q,v,weight] at hm hS ⊢
    linarith [ht.2.2.1]
  · have hb : (7292/10000:ℝ)≤ sourceBound 4 := by
      norm_num [sourceBound,p,q,weight]
      constructor <;> linarith [ha.1,hd.1]
    norm_num [c,v,weight] at hb hS ⊢
    linarith [ht.2.2.1,ha.2]
  · have hN : Real.sqrt ((p 5)^2+(q 5-weight 5)^2)<2365/10000 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num [p,q,weight]
    have hm := mul_lt_mul'' hR hN hR0 (Real.sqrt_nonneg _)
    have hb : sourceBound 5=-(p 5+q 5-weight 5)/2-radius*Real.sqrt ((p 5)^2+(q 5-weight 5)^2) := by
      simp only [sourceBound]
      rw [ite_eq_right (by norm_num [p])]
    rw [hb]
    norm_num [c,p,q,v,weight] at hm hS ⊢
    linarith [ht.2.2.1,ha.1]

lemma original_projection (r : Row) {a b A B : ℝ} (hs : OuterState a b)
    (ht : OuterState A B)
    (hm : (1+Real.sin (7/10)+Real.cos (7/10))/2≤
      b+A*Real.sin (7/10)+B*Real.cos (7/10)) :
    (923/1000:ℝ)<7/10+c r+p r*a+q r*b+v r*A+t r*B := by
  have hsource := source_lower r hs
  have htarget := target_lower r ht
  have hw : 0≤weight r := by fin_cases r <;> norm_num [weight]
  have hsep := mul_le_mul_of_nonneg_left hm hw
  have hvalue := scalar_lower r
  dsimp [scalar] at hvalue
  nlinarith only [hsource,htarget,hsep,hvalue]

/-- Each whole final-angle contact uses its literal source and target labels. -/
theorem lower (r : Row) {B : ℝ} (hd : PlusDomain B (7/10)) :
    (89809/100000:ℝ)<plusCost r B (7/10) := by
  have hs := ShortOuterOne.SameContact.arc_state hd.2.2
  have ht := ShortOuterOne.SameContact.arc_state hd.1
  have he : (1+Real.sin (7/10)+Real.cos (7/10))/2=
      plus B (7/10)+arc B*Real.sin (7/10)+B*Real.cos (7/10) := by
    dsimp [plus,SecondWord.OppositeZero.plus]
    ring
  have hh := original_projection r hs ht he.le
  dsimp [plusCost,source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval]
  linarith

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Cap
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Same.Cap
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open SecondWord (U W outer_domain outer_zero_mem)
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra
open SecondWord.SameZero.PJ.Reference (sinBox cosBox)
open SecondWord.OppositeZero.Reference (rootAt rootAt_lo_positive)

def reference : Row→ℝ := ![124677/400000,28470147/100000000,0,1434277/4000000]

lemma reference_mem (r : Row) : reference r∈Icc (0:ℝ) (9/10) := by
  fin_cases r <;> norm_num [reference]

def targetU (r : Row) : Interval (U (reference r)) := rootAt (reference r) (reference_mem r)
def sourceBox (r : Row) : Interval (contact (reference r) (7/10)) :=
  let W := ((Interval.point (1/2)).add (((Interval.point (reference r)).add (Interval.point (1/2))).mul (cosBox (7/10) (by norm_num)))).sub
      (((targetU r).sub (Interval.point 1)).mul (sinBox (7/10) (by norm_num)))
  ⟨W.lo,W.hi,by
    have h : contact (reference r) (7/10)=
        1/2+(reference r+1/2)*Real.cos (7/10)-(U (reference r)-1)*Real.sin (7/10) := by
      simp only [contact,SecondWord.SameZero.b,U]; ring
    rw [h]; exact W.mem⟩

macro "cap_reference_arithmetic" : tactic => `(tactic|
  norm_num [reference,targetU,sourceBox,SecondWord.OppositeZero.Reference.rootAt,
    rootThree,rootStep,shifted,radicand,coordinate,labelBox,firstBox,ratioBox,
    source,target,c,p,q,P,t]
  <;> event_reference_arithmetic)

private lemma r90_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r90_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl
private lemma r90_mp_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).lo = S.lo := by subst e; rfl
private lemma r90_mp_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).hi = S.hi := by subst e; rfl

private lemma r90_rootAt_lo {b : ℝ} (hb : b∈Icc 0 (9/10)) : (rootAt b hb).lo =
    (rootThree (Interval.point (Q0-(b+1/2)^2)) (2-b/2) (by linarith [hb.2])
      (by norm_num [Interval.point,Q0]; nlinarith [hb.1,hb.2])).lo := by
  unfold SecondWord.OppositeZero.Reference.rootAt
  rw [r90_mpr_lo, r90_mp_lo]
  all_goals simp [U,ShortOuterOne.SameContact.arc]
private lemma r90_rootAt_hi {b : ℝ} (hb : b∈Icc 0 (9/10)) : (rootAt b hb).hi =
    (rootThree (Interval.point (Q0-(b+1/2)^2)) (2-b/2) (by linarith [hb.2])
      (by norm_num [Interval.point,Q0]; nlinarith [hb.1,hb.2])).hi := by
  unfold SecondWord.OppositeZero.Reference.rootAt
  rw [r90_mpr_hi, r90_mp_hi]
  all_goals simp [U,ShortOuterOne.SameContact.arc]

private lemma r90_U_eq {y : ℝ} : U y = Real.sqrt (Q0-(y+1/2)^2) := by
  dsimp [U,ShortOuterOne.SameContact.arc]; ring

private lemma r90_mem_of {v : ℝ} (X : Interval v) {a c : ℝ} (ha : a≤X.lo) (hc : X.hi≤c) :
    v∈Icc a c :=
  ⟨ha.trans X.mem.1,X.mem.2.trans hc⟩

private lemma r90_contact_eq (B : ℝ) : contact B (7/10) =
    1/2+(B+1/2)*Real.cos (7/10)-(U B-1)*Real.sin (7/10) := by
  simp only [contact,SecondWord.SameZero.b,U]; ring

local macro "r90_trig" : tactic => `(tactic|
  norm_num [sinBox,cosBox,Interval.of_bounds,HighOrderTaylor.S17,HighOrderTaylor.S15,
    HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C18,HighOrderTaylor.C16,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8])

local macro "r90_arith" : tactic => `(tactic|
  norm_num [rootThree,rootStep,radicand,ratioBox,Interval.of_bounds,Interval.point,
    Interval.add,Interval.sub,Interval.neg,Interval.mul,Interval.square,Interval.div,
    Interval.inv,Q0,q,p,P,t])

lemma r90_radicand_pos (r : Row) : 0<(radicand (sourceBox r)).lo := by
  fin_cases r <;>
    norm_num [radicand,sourceBox,targetU,r90_rootAt_lo,r90_rootAt_hi,reference,rootThree,
      rootStep,sinBox,cosBox,Interval.of_bounds,Interval.point,Interval.add,Interval.sub,
      Interval.mul,Interval.square,HighOrderTaylor.S17,HighOrderTaylor.S15,
      HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C18,HighOrderTaylor.C16,
      HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8,Q0]

def sourceU (r : Row) : Interval (U (contact (reference r) (7/10))) :=
  shifted (sourceBox r) (8/5) (by norm_num) (r90_radicand_pos r).le

private lemma r90_sin : Real.sin (7/10)∈Icc (644217687237691/1000000000000000:ℝ) (161054421809423/250000000000000:ℝ) :=
  r90_mem_of (sinBox (7/10) (by norm_num)) (by r90_trig) (by r90_trig)
private lemma r90_cos : Real.cos (7/10)∈Icc (95605273410561/125000000000000:ℝ) (764842187284489/1000000000000000:ℝ) :=
  r90_mem_of (cosBox (7/10) (by norm_num)) (by r90_trig) (by r90_trig)

private lemma r90_ref0 : Domain (reference 0) (7/10) ∧
    (89809/100000:ℝ)<Same.cost 0 (reference 0) (7/10) ∧
      |Same.targetFirst 0 (reference 0) (7/10)|<(1/1000000:ℝ) := by
  rw [show reference 0=(124677/400000:ℝ) from rfl]
  have hU : U (124677/400000:ℝ)∈Icc (9023241221207/5000000000000:ℝ) (3609296488483/2000000000000:ℝ) := by
    rw [r90_U_eq]
    exact r90_mem_of (rootThree (Interval.point (Q0-((124677/400000:ℝ)+1/2)^2)) (361/200:ℝ) (by norm_num)
      (by r90_arith)) (by r90_arith) (by r90_arith)
  have hb : contact (124677/400000:ℝ) (7/10)∈Icc (1506120090393/2500000000000:ℝ) (3012240180787/5000000000000:ℝ) := by
    rw [r90_contact_eq]
    exact r90_mem_of (((Interval.point (1/2)).add (((Interval.point (124677/400000:ℝ)).add
      (Interval.point (1/2))).mul (Interval.of_bounds r90_cos))).sub
        (((Interval.of_bounds hU).sub (Interval.point 1)).mul (Interval.of_bounds r90_sin)))
      (by r90_arith) (by r90_arith)
  have hw : U (contact (124677/400000:ℝ) (7/10))∈Icc (8216155316771/5000000000000:ℝ) (3286462126709/2000000000000:ℝ) := by
    rw [r90_U_eq]
    exact r90_mem_of (rootThree (radicand (Interval.of_bounds hb)) (1643/1000:ℝ) (by norm_num)
      (by r90_arith)) (by r90_arith) (by r90_arith)
  refine ⟨⟨⟨by norm_num,by linarith [outer_endpoint_bounds.2.2.1]⟩,⟨by norm_num,le_rfl⟩,
    ⟨by linarith [hb.1],by linarith [hb.2,outer_endpoint_bounds.2.2.1]⟩⟩,?_,?_⟩
  · have e1 : U (124677/400000:ℝ)=arc (124677/400000:ℝ)+1/2 := rfl
    have e2 : U (contact (124677/400000:ℝ) (7/10))=arc (contact (124677/400000:ℝ) (7/10))+1/2 := rfl
    simp only [Same.cost]
    norm_num [c,p,q,P,t]
    linarith [hU.1,hU.2,hb.1,hb.2,hw.1,hw.2]
  · let RB := ratioBox (Interval.point (124677/400000:ℝ)) (Interval.of_bounds hU) (by r90_arith)
    let Rb := ratioBox (Interval.of_bounds hb) (Interval.of_bounds hw) (by r90_arith)
    let T := ((((Interval.point (q 0)).sub ((Interval.point (p 0)).mul Rb)).mul
      ((Interval.of_bounds r90_cos).add (RB.mul (Interval.of_bounds r90_sin)))).add
        ((Interval.point (P 0)).mul RB)).sub (Interval.point (t 0))
    have hm : Same.targetFirst 0 (124677/400000:ℝ) (7/10)∈Icc T.lo T.hi := T.mem
    have h1 : -(1/1000000:ℝ)<T.lo := by dsimp only [T,RB,Rb]; r90_arith
    have h2 : T.hi<(1/1000000:ℝ) := by dsimp only [T,RB,Rb]; r90_arith
    exact abs_lt.mpr ⟨by linarith [hm.1],by linarith [hm.2]⟩

private lemma r90_ref1 : Domain (reference 1) (7/10) ∧
    (89809/100000:ℝ)<Same.cost 1 (reference 1) (7/10) ∧
      |Same.targetFirst 1 (reference 1) (7/10)|<(1/1000000:ℝ) := by
  rw [show reference 1=(28470147/100000000:ℝ) from rfl]
  have hU : U (28470147/100000000:ℝ)∈Icc (9082735825427/5000000000000:ℝ) (3633094330171/2000000000000:ℝ) := by
    rw [r90_U_eq]
    exact r90_mem_of (rootThree (Interval.point (Q0-((28470147/100000000:ℝ)+1/2)^2)) (1817/1000:ℝ) (by norm_num)
      (by r90_arith)) (by r90_arith) (by r90_arith)
  have hb : contact (28470147/100000000:ℝ) (7/10)∈Icc (2870693312341/5000000000000:ℝ) (1435346656171/2500000000000:ℝ) := by
    rw [r90_contact_eq]
    exact r90_mem_of (((Interval.point (1/2)).add (((Interval.point (28470147/100000000:ℝ)).add
      (Interval.point (1/2))).mul (Interval.of_bounds r90_cos))).sub
        (((Interval.of_bounds hU).sub (Interval.point 1)).mul (Interval.of_bounds r90_sin)))
      (by r90_arith) (by r90_arith)
  have hw : U (contact (28470147/100000000:ℝ) (7/10))∈Icc (16618742833891/10000000000000:ℝ) (8309371416947/5000000000000:ℝ) := by
    rw [r90_U_eq]
    exact r90_mem_of (rootThree (radicand (Interval.of_bounds hb)) (831/500:ℝ) (by norm_num)
      (by r90_arith)) (by r90_arith) (by r90_arith)
  refine ⟨⟨⟨by norm_num,by linarith [outer_endpoint_bounds.2.2.1]⟩,⟨by norm_num,le_rfl⟩,
    ⟨by linarith [hb.1],by linarith [hb.2,outer_endpoint_bounds.2.2.1]⟩⟩,?_,?_⟩
  · have e1 : U (28470147/100000000:ℝ)=arc (28470147/100000000:ℝ)+1/2 := rfl
    have e2 : U (contact (28470147/100000000:ℝ) (7/10))=arc (contact (28470147/100000000:ℝ) (7/10))+1/2 := rfl
    simp only [Same.cost]
    norm_num [c,p,q,P,t]
    linarith [hU.1,hU.2,hb.1,hb.2,hw.1,hw.2]
  · let RB := ratioBox (Interval.point (28470147/100000000:ℝ)) (Interval.of_bounds hU) (by r90_arith)
    let Rb := ratioBox (Interval.of_bounds hb) (Interval.of_bounds hw) (by r90_arith)
    let T := ((((Interval.point (q 1)).sub ((Interval.point (p 1)).mul Rb)).mul
      ((Interval.of_bounds r90_cos).add (RB.mul (Interval.of_bounds r90_sin)))).add
        ((Interval.point (P 1)).mul RB)).sub (Interval.point (t 1))
    have hm : Same.targetFirst 1 (28470147/100000000:ℝ) (7/10)∈Icc T.lo T.hi := T.mem
    have h1 : -(1/1000000:ℝ)<T.lo := by dsimp only [T,RB,Rb]; r90_arith
    have h2 : T.hi<(1/1000000:ℝ) := by dsimp only [T,RB,Rb]; r90_arith
    exact abs_lt.mpr ⟨by linarith [hm.1],by linarith [hm.2]⟩

private lemma r90_ref3 : Domain (reference 3) (7/10) ∧
    (89809/100000:ℝ)<Same.cost 3 (reference 3) (7/10) ∧
      |Same.targetFirst 3 (reference 3) (7/10)|<(1/1000000:ℝ) := by
  rw [show reference 3=(1434277/4000000:ℝ) from rfl]
  have hU : U (1434277/4000000:ℝ)∈Icc (8914116393331/5000000000000:ℝ) (17828232786663/10000000000000:ℝ) := by
    rw [r90_U_eq]
    exact r90_mem_of (rootThree (Interval.point (Q0-((1434277/4000000:ℝ)+1/2)^2)) (1783/1000:ℝ) (by norm_num)
      (by r90_arith)) (by r90_arith) (by r90_arith)
  have hb : contact (1434277/4000000:ℝ) (7/10)∈Icc (6523613810069/10000000000000:ℝ) (6523613810071/10000000000000:ℝ) := by
    rw [r90_contact_eq]
    exact r90_mem_of (((Interval.point (1/2)).add (((Interval.point (1434277/4000000:ℝ)).add
      (Interval.point (1/2))).mul (Interval.of_bounds r90_cos))).sub
        (((Interval.of_bounds hU).sub (Interval.point 1)).mul (Interval.of_bounds r90_sin)))
      (by r90_arith) (by r90_arith)
  have hw : U (contact (1434277/4000000:ℝ) (7/10))∈Icc (80431076823/50000000000:ℝ) (16086215364603/10000000000000:ℝ) := by
    rw [r90_U_eq]
    exact r90_mem_of (rootThree (radicand (Interval.of_bounds hb)) (1609/1000:ℝ) (by norm_num)
      (by r90_arith)) (by r90_arith) (by r90_arith)
  refine ⟨⟨⟨by norm_num,by linarith [outer_endpoint_bounds.2.2.1]⟩,⟨by norm_num,le_rfl⟩,
    ⟨by linarith [hb.1],by linarith [hb.2,outer_endpoint_bounds.2.2.1]⟩⟩,?_,?_⟩
  · have e1 : U (1434277/4000000:ℝ)=arc (1434277/4000000:ℝ)+1/2 := rfl
    have e2 : U (contact (1434277/4000000:ℝ) (7/10))=arc (contact (1434277/4000000:ℝ) (7/10))+1/2 := rfl
    simp only [Same.cost]
    norm_num [c,p,q,P,t]
    linarith [hU.1,hU.2,hb.1,hb.2,hw.1,hw.2]
  · let RB := ratioBox (Interval.point (1434277/4000000:ℝ)) (Interval.of_bounds hU) (by r90_arith)
    let Rb := ratioBox (Interval.of_bounds hb) (Interval.of_bounds hw) (by r90_arith)
    let T := ((((Interval.point (q 3)).sub ((Interval.point (p 3)).mul Rb)).mul
      ((Interval.of_bounds r90_cos).add (RB.mul (Interval.of_bounds r90_sin)))).add
        ((Interval.point (P 3)).mul RB)).sub (Interval.point (t 3))
    have hm : Same.targetFirst 3 (1434277/4000000:ℝ) (7/10)∈Icc T.lo T.hi := T.mem
    have h1 : -(1/1000000:ℝ)<T.lo := by dsimp only [T,RB,Rb]; r90_arith
    have h2 : T.hi<(1/1000000:ℝ) := by dsimp only [T,RB,Rb]; r90_arith
    exact abs_lt.mpr ⟨by linarith [hm.1],by linarith [hm.2]⟩

lemma references (r : Row) (hr : Coupled r) : Domain (reference r) (7/10) ∧
    (89809/100000:ℝ)<Same.cost r (reference r) (7/10) ∧
      |Same.targetFirst r (reference r) (7/10)|<(1/1000000:ℝ) := by
  fin_cases r
  · exact r90_ref0
  · exact r90_ref1
  · exact (hr rfl).elim
  · exact r90_ref3

lemma curvature (r : Row) (hr : Coupled r) {B : ℝ} (hd : Domain B (7/10)) :
    (33/100:ℝ)<targetSecond r B (7/10) := by
  have ha := alpha_nonneg r hr hd.2.2
  have hfirst := mul_nonneg ha (sq_nonneg (projection B (7/10)))
  have hratio := (SecondWord.outer_ratio_bounds hd.2.2).1
  have hp := mul_nonpos_of_nonpos_of_nonneg (coupled_signs r hr).1
    (by linarith [hratio] : 0≤ratio (contact B (7/10)))
  have hl : q r≤l r (contact B (7/10)) := by dsimp [l]; linarith
  have hs : (161/250:ℝ)<Real.sin (7/10) := by linarith [CommonQuarter.cap_trig.1]
  have hproduct := mul_le_mul hl hs.le (by norm_num)
    (l_positive r hd.2.2).le
  have hP := (coefficient_signs r).2.2
  have hbracket : q r*(161/250)+P r≤l r (contact B (7/10))*Real.sin (7/10)+P r := by linarith
  have hbracket0 : 0≤q r*(161/250)+P r := by
    have hq := (coefficient_signs r).1
    positivity
  have hlast := mul_le_mul hbracket (Axial.ratioD_lower hd.1).le
    (by norm_num : (0:ℝ)≤557/1000) (hbracket0.trans hbracket)
  have href : (33/100:ℝ)<(q r*(161/250)+P r)*(557/1000) := by
    fin_cases r <;> norm_num [Coupled] at hr <;> norm_num [q,P]
  dsimp [targetSecond]
  linarith

/-- The tangent at the reference point controls the whole final-angle contact interval. -/
theorem lower (r : Row) (hr : Coupled r) {B : ℝ} (hd : Domain B (7/10)) :
    (11226/12500:ℝ)<Same.cost r B (7/10) := by
  let a := reference r
  let lo := min B a
  let hi := max B a
  have href := references r hr
  have hB : B∈Icc lo hi := ⟨min_le_left _ _,le_max_left _ _⟩
  have ha : a∈Icc lo hi := ⟨min_le_right _ _,le_max_right _ _⟩
  have hdom {u : ℝ} (hu : u∈Icc lo hi) : Domain u (7/10) := by
    have hui : u∈Icc 0 outerDiagonal :=
      ⟨(le_min hd.1.1 href.1.1.1).trans hu.1,hu.2.trans (max_le hd.1.2 href.1.1.2)⟩
    have hupper : contact u (7/10)≤outerDiagonal := by
      rcases le_total B a with h | h
      · have hle : u≤a := by simpa [hi,max_eq_right h] using hu.2
        exact (SecondWord.SameZero.b_target_monotone hd.2.1 hui href.1.1 hle).trans href.1.2.2.2
      · have hle : u≤B := by simpa [hi,max_eq_left h] using hu.2
        exact (SecondWord.SameZero.b_target_monotone hd.2.1 hui hd.1 hle).trans hd.2.2.2
    exact ⟨hui,hd.2.1,⟨by linarith [SecondWord.SameZero.b_lower hui hd.2.1],hupper⟩⟩
  have hh := curvature_tangent (f := fun u => Same.cost r u (7/10))
    (d := fun u => Same.targetFirst r u (7/10))
    (dd := fun u => targetSecond r u (7/10)) (κ := (33/100:ℝ)) hB ha
    (fun u hu => cost_target_hasDerivAt r (hdom hu))
    (fun u hu => targetFirst_hasDerivAt r (hdom hu))
    (fun u hu => (curvature r hr (hdom hu)).le)
  have hs := abs_lt.mp href.2.2
  have hsq : (Same.targetFirst r a (7/10))^2<(1/1000000:ℝ)^2 := by
    dsimp [a]
    nlinarith
  nlinarith [href.2.1,
    sq_nonneg ((33/100)*(B-a)+Same.targetFirst r a (7/10))]

end SquaresInCircles.Eight.ShortOuterZero.Same.Cap
end
end
end
