module

public import SquaresInCircles.Eight.Words.Second.Outer.JBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroContact
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJDiagonalData

/-!
# Eight squares: the three P/J boundary references

Every enclosure below carries the exact trigonometric or radical expression. Only the angles
`.10726`, `.18909` (`diagonalReference`) and `.7` and the target `.34621` (`capReference`) are
evaluated; they are fixed reference points, not a subdivision of any domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.PJ.Reference
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open StationaryPrimitives (Interval)
open OppositeThree.ReferenceAlgebra

def dBox : Interval outerDiagonal := Interval.of_bounds ⟨diagonal_fine.1.le,diagonal_fine.2.le⟩
def dUBox : Interval (U outerDiagonal) := by
  rw [U,ShortOuterOne.SameContact.arc_diagonal]
  exact dBox.add (Interval.point (1/2))
def aBox : Interval outerAxial := Interval.of_bounds
  ⟨ShortOuterZero.fine_axial_bounds.1.le,ShortOuterZero.fine_axial_bounds.2.le⟩
def sinBox (x : ℝ) (hx : 0≤x) : Interval (Real.sin x) :=
  Interval.of_bounds ⟨HighOrderTaylor.S15_le_sin hx,HighOrderTaylor.sin_le_S17 hx⟩
def cosBox (x : ℝ) (hx : 0≤x) : Interval (Real.cos x) :=
  Interval.of_bounds ⟨HighOrderTaylor.C18_le_cos hx,HighOrderTaylor.cos_le_C16 hx⟩
def zeroSourceBox (x : ℝ) (hx : 0≤x) : Interval (b 0 x) := by
  have hh := ((Interval.point (1/2)).add ((Interval.point (1/2)).mul (cosBox x hx))).sub
    ((aBox.sub (Interval.point (1/2))).mul (sinBox x hx))
  simpa [b,ShortOuterOne.SameContact.arc_zero] using hh

def ZBox (x : ℝ) (hx : 0≤x) : Interval (Diagonal.Z x) :=
  (dBox.sub (Interval.point (1/2))).sub (sinBox x hx)
def YRadBox (x : ℝ) (hx : 0≤x) : Interval (Q0-(Diagonal.Z x)^2) :=
  (Interval.point Q0).sub (ZBox x hx).square
def YBox (x : ℝ) (hx : 0≤x) (hr : 0≤(YRadBox x hx).lo) : Interval (Diagonal.Y x) :=
  rootThree (YRadBox x hx) 2 (by norm_num) hr
def UBox (x : ℝ) (hx : 0≤x) (hr : 0≤(YRadBox x hx).lo) : Interval (Diagonal.horizontal x) :=
  ((YBox x hx hr).mul (cosBox x hx)).sub ((ZBox x hx).mul (sinBox x hx))
def VBox (x : ℝ) (hx : 0≤x) (hr : 0≤(YRadBox x hx).lo) : Interval (Diagonal.vertical x) :=
  ((YBox x hx hr).mul (sinBox x hx)).add ((ZBox x hx).mul (cosBox x hx))
def BBox (x : ℝ) (hx : 0≤x) (hr : 0≤(YRadBox x hx).lo) : Interval (Diagonal.height x) :=
  (VBox x hx hr).sub (Interval.point (1/2))
def speedBox (x : ℝ) (hx : 0≤x) (hr : 0≤(YRadBox x hx).lo)
    (hy : 0<(YBox x hx hr).lo) : Interval (Diagonal.speed x) :=
  (UBox x hx hr).mul ((Interval.point 1).sub ((cosBox x hx).div (YBox x hx hr) hy))

local macro "reference_arithmetic" : tactic => `(tactic|
  norm_num [dBox,dUBox,aBox,sinBox,cosBox,zeroSourceBox,ZBox,YRadBox,YBox,UBox,VBox,BBox,
    speedBox,rootThree,rootStep,shifted,radicand,coordinate,labelBox,firstBox,ratioBox,
    Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,Interval.mul,
    Interval.square,Interval.cube,Interval.div,Interval.inv,HighOrderTaylor.S17,
    HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C18,
    HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8,
    PLabel,JLabel,Q0,Diagonal.start])


private lemma r49_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r49_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl
private lemma r49_mp_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).lo = S.lo := by subst e; rfl

private lemma r49_zeroSourceBox_lo (x : ℝ) (hx : 0≤x) : (zeroSourceBox x hx).lo =
    (((Interval.point (1/2)).add ((Interval.point (1/2)).mul (cosBox x hx))).sub
      ((aBox.sub (Interval.point (1/2))).mul (sinBox x hx))).lo := by
  unfold zeroSourceBox
  rw [r49_mpr_lo, r49_mp_lo]
  · norm_num
  · simp only [b,ShortOuterOne.SameContact.arc_zero]
    norm_num

private lemma r49_dUBox_lo : dUBox.lo = (dBox.add (Interval.point (1/2))).lo := by
  unfold dUBox
  rw [r49_mpr_lo, r49_mpr_lo]
  · rw [ShortOuterOne.SameContact.arc_diagonal]
  · rfl
private lemma r49_dUBox_hi : dUBox.hi = (dBox.add (Interval.point (1/2))).hi := by
  unfold dUBox
  rw [r49_mpr_hi, r49_mpr_hi]
  · rw [ShortOuterOne.SameContact.arc_diagonal]
  · rfl

private lemma r49_shifted_eq {y : ℝ} : U y = Real.sqrt (Q0-(y+1/2)^2) := by dsimp [U,arc]; ring
private lemma r49_shifted_lo {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).lo = (rootThree (radicand Y) s hs hr).lo :=
  r49_mpr_lo r49_shifted_eq (congrArg _ r49_shifted_eq) _
private lemma r49_shifted_hi {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).hi = (rootThree (radicand Y) s hs hr).hi :=
  r49_mpr_hi r49_shifted_eq (congrArg _ r49_shifted_eq) _

private lemma r49_coordinate_eq {y : ℝ} : arc y = U y-1/2 := by dsimp [U]; ring
private lemma r49_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r49_mpr_lo r49_coordinate_eq (congrArg _ r49_coordinate_eq) _
private lemma r49_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r49_mpr_hi r49_coordinate_eq (congrArg _ r49_coordinate_eq) _

private lemma r49_label_eq (H : RoleLabel) {y : ℝ} :
    H.outer y = H.c+H.p*(arc y)+H.q*y+H.r*y^2+H.s*(arc y*y) := by
  dsimp [RoleLabel.outer,RoleLabel.eval]; ring
private lemma r49_labelBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).lo = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).lo :=
  r49_mpr_lo (r49_label_eq H) (congrArg _ (r49_label_eq H)) _
private lemma r49_labelBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).hi = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).hi :=
  r49_mpr_hi (r49_label_eq H) (congrArg _ (r49_label_eq H)) _

private lemma r49_mem_of {v : ℝ} (X : Interval v) {a c : ℝ} (ha : a≤X.lo) (hc : X.hi≤c) :
    v∈Icc a c :=
  ⟨ha.trans X.mem.1,X.mem.2.trans hc⟩

local macro "r49_arith" : tactic => `(tactic|
  norm_num [dBox,r49_dUBox_lo,r49_dUBox_hi,aBox,sinBox,cosBox,ZBox,YRadBox,YBox,UBox,VBox,
    BBox,speedBox,rootThree,rootStep,r49_shifted_lo,r49_shifted_hi,radicand,
    r49_coordinate_lo,r49_coordinate_hi,r49_labelBox_lo,r49_labelBox_hi,firstBox,ratioBox,
    Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,Interval.mul,
    Interval.square,Interval.cube,Interval.div,Interval.inv,HighOrderTaylor.S17,
    HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C18,
    HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8,
    PLabel,JLabel,Q0,Diagonal.start])

lemma zero_start : outerDiagonal<b 0 Diagonal.start := by
  have hh := (zeroSourceBox Diagonal.start (by norm_num [Diagonal.start])).mem
  have hlo : (899214066:ℝ)/1000000000 <
      (zeroSourceBox Diagonal.start (by norm_num [Diagonal.start])).lo := by
    rw [r49_zeroSourceBox_lo]
    r49_arith
  linarith [hh.1,diagonal_fine.2]

lemma zero_start_cost : (1797/2000:ℝ)<Diagonal.start+PLabel.outer outerDiagonal-JLabel.outer 0 := by
  have hP := (labelBox PLabel dBox dUBox).mem
  have hp : (7909016/10000000:ℝ)<(labelBox PLabel dBox dUBox).lo := by r49_arith
  have hJ := J_zero
  change JLabel.outer 0= -(13/50000)*outerAxial at hJ
  rw [hJ]
  norm_num [Diagonal.start] at *
  linarith [hP.1,ShortOuterZero.fine_axial_bounds.1]

lemma diagonal_endpoint_bounds :
    (33/20:ℝ)<Diagonal.horizontal (7/10) ∧
      Diagonal.horizontal Diagonal.start<383/200 ∧
      Diagonal.height (7/10)<outerDiagonal := by
  have hr0 : 0≤(YRadBox Diagonal.start (by norm_num [Diagonal.start])).lo := by reference_arithmetic
  have hr1 : 0≤(YRadBox (7/10) (by norm_num)).lo := by reference_arithmetic
  have h0 := (UBox Diagonal.start (by norm_num [Diagonal.start]) hr0).mem
  have h1 := (UBox (7/10) (by norm_num) hr1).mem
  have h2 := (BBox (7/10) (by norm_num) hr1).mem
  have h0' : (UBox Diagonal.start (by norm_num [Diagonal.start]) hr0).hi<383/200 := by reference_arithmetic
  have h1' : (33/20:ℝ)<(UBox (7/10) (by norm_num) hr1).lo := by reference_arithmetic
  have h2' : (BBox (7/10) (by norm_num) hr1).hi<899/1000 := by reference_arithmetic
  exact ⟨h1'.trans_le h1.1,h0.2.trans_lt h0',h2.2.trans_lt
    (h2'.trans fine_outer_endpoint_bounds.2)⟩

def diagonalReference : ℝ := 18909/100000

lemma diagonal_reference : Diagonal.Domain diagonalReference ∧
    (17955521/20000000:ℝ)<Diagonal.cost diagonalReference ∧
      |Diagonal.first diagonalReference|<(1/1000000:ℝ) := by
  rw [show diagonalReference=(18909/100000:ℝ) from rfl]
  have hx : (0:ℝ)≤(18909/100000:ℝ) := by norm_num
  have hr : 0≤(YRadBox (18909/100000:ℝ) hx).lo := by r49_arith
  have hY : 0<(YBox (18909/100000:ℝ) hx hr).lo := by r49_arith
  have hBm : Diagonal.height (18909/100000:ℝ)∈
      Icc (77301091014/1000000000000:ℝ) (77301091017/1000000000000) :=
    r49_mem_of (BBox (18909/100000:ℝ) hx hr) (by r49_arith) (by r49_arith)
  have hrad : 0≤(radicand (Interval.of_bounds hBm)).lo := by r49_arith
  have hTm : U (Diagonal.height (18909/100000:ℝ))∈
      Icc (1892702684075/1000000000000:ℝ) (1892702684079/1000000000000) :=
    r49_mem_of (shifted (Interval.of_bounds hBm) (19/10) (by norm_num) hrad)
      (by rw [r49_shifted_lo]; r49_arith) (by rw [r49_shifted_hi]; r49_arith)
  have hSm : Diagonal.speed (18909/100000:ℝ)∈
      Icc (947855753986/1000000000000:ℝ) (947855753989/1000000000000) :=
    r49_mem_of (speedBox (18909/100000:ℝ) hx hr hY) (by r49_arith) (by r49_arith)
  have hT : 0<(Interval.of_bounds hTm).lo := by r49_arith
  let V := ((Interval.point (18909/100000:ℝ)).add (labelBox PLabel dBox dUBox)).sub
    (labelBox JLabel (Interval.of_bounds hBm) (Interval.of_bounds hTm))
  let D := (Interval.point 1).sub
    ((firstBox JLabel (Interval.of_bounds hBm) (Interval.of_bounds hTm) hT).mul
      (Interval.of_bounds hSm))
  have hV : (17955521/20000000:ℝ)<V.lo := by dsimp only [V]; r49_arith
  have hDl : -(1/1000000:ℝ)<D.lo := by dsimp only [D]; r49_arith
  have hDu : D.hi<(1/1000000:ℝ) := by dsimp only [D]; r49_arith
  refine ⟨⟨by norm_num [Diagonal.start],by linarith [hBm.1]⟩,
    hV.trans_le V.mem.1,?_⟩
  rw [abs_lt]
  exact ⟨hDl.trans_le D.mem.1,D.mem.2.trans_lt hDu⟩

def capReference : ℝ := 34621/100000

lemma cap_reference : Domain capReference (7/10) ∧
    (22444717/25000000:ℝ)<value PLabel JLabel capReference (7/10) ∧
      |targetFirst PLabel JLabel capReference (7/10)|<(1/100000:ℝ) := by
  rw [show capReference=(34621/100000:ℝ) from rfl]
  have hrad : 0≤(radicand (Interval.point (34621/100000:ℝ))).lo := by
    norm_num [radicand,Interval.point,Interval.add,Interval.sub,Interval.square,
      Interval.mul,Q0]
  have hUm : U (34621/100000:ℝ)∈Icc (1788722626875/1000000000000:ℝ) (1788722626878/1000000000000) :=
    r49_mem_of (shifted (Interval.point (34621/100000:ℝ)) (9/5) (by norm_num) hrad)
      (by rw [r49_shifted_lo]; r49_arith) (by rw [r49_shifted_hi]; r49_arith)
  have hU : 0<(Interval.of_bounds hUm).lo := by r49_arith
  have hBm : b (34621/100000:ℝ) (7/10)∈
      Icc (639108040742/1000000000000:ℝ) (639108040745/1000000000000) :=
    r49_mem_of (((Interval.point (1/2)).add (((Interval.point (34621/100000:ℝ)).add
      (Interval.point (1/2))).mul (cosBox (7/10) (by norm_num)))).sub
        (((coordinate (Interval.of_bounds hUm)).sub (Interval.point (1/2))).mul
          (sinBox (7/10) (by norm_num)))) (by r49_arith) (by r49_arith)
  have hbr : 0≤(radicand (Interval.of_bounds hBm)).lo := by r49_arith
  have hAm : U (b (34621/100000:ℝ) (7/10))∈
      Icc (1618033643501/1000000000000:ℝ) (1618033643506/1000000000000) :=
    r49_mem_of (shifted (Interval.of_bounds hBm) (8/5) (by norm_num) hbr)
      (by rw [r49_shifted_lo]; r49_arith) (by rw [r49_shifted_hi]; r49_arith)
  have hA : 0<(Interval.of_bounds hAm).lo := by r49_arith
  let K := (cosBox (7/10) (by norm_num)).add
    ((ratioBox (Interval.point (34621/100000:ℝ)) (Interval.of_bounds hUm) hU).mul
      (sinBox (7/10) (by norm_num)))
  let V := ((Interval.point (7/10)).add
    (labelBox PLabel (Interval.of_bounds hBm) (Interval.of_bounds hAm))).sub
      (labelBox JLabel (Interval.point (34621/100000:ℝ)) (Interval.of_bounds hUm))
  let D := ((firstBox PLabel (Interval.of_bounds hBm) (Interval.of_bounds hAm) hA).mul K).sub
    (firstBox JLabel (Interval.point (34621/100000:ℝ)) (Interval.of_bounds hUm) hU)
  have hv : (22444717/25000000:ℝ)<V.lo := by dsimp only [V]; r49_arith
  have hdl : -(1/100000:ℝ)<D.lo := by dsimp only [D,K]; r49_arith
  have hdu : D.hi<(1/100000:ℝ) := by dsimp only [D,K]; r49_arith
  refine ⟨⟨Asymmetric.rational_outer_mem (by norm_num),by norm_num,
    ⟨by linarith [hBm.1],by linarith [hBm.2,fine_outer_endpoint_bounds.2]⟩⟩,
      hv.trans_le V.mem.1,?_⟩
  rw [abs_lt]
  exact ⟨hdl.trans_le D.mem.1,D.mem.2.trans_lt hdu⟩

end SquaresInCircles.Eight.SecondWord.SameZero.PJ.Reference
