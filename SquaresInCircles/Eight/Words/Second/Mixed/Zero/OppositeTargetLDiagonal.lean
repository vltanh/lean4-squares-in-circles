module

public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetReferenceAlgebra

/-!
# Eight squares: the L diagonal from its single strong-convexity reference

This follows §10.4: the first part decreases
to `.3`; the remaining interval has curvature greater than `1.1`, and
the one value-and-slope reference at `.3832` bounds its entire minimum.
-/

section
/-!
## The negative-target diagonal references in §§8–10

The only angles are the written cap `.44152`,
the initial L cut `.3`, and its single tangent reference `.3832`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.DiagonalReferences
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra Target.ReferenceAlgebra

local macro "diagonal_reference" : tactic => `(tactic|
  norm_num [coreBox,outerBox,sinBox,cosBox,diagonalBox,speedBox,HBox,H₁Box,H₂Box,
    labelBox,firstBox,secondBox,thirdBox,ratioBox,ratioDBox,ratioDDBox,
    coordinate,shifted,radicand,rootThree,rootStep,
    HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
    F,c,g,PLabel,JLabel,LLabel,Q0,cap])

def capU : Interval (U (diagonal cap)) :=
  shifted (diagonalBox cap (by norm_num [cap])) (7/5) (by norm_num) (by diagonal_reference)
def threeU : Interval (U (diagonal (3/10))) :=
  shifted (diagonalBox (3/10) (by norm_num)) (3/2) (by norm_num) (by diagonal_reference)
def minimumU : Interval (U (diagonal (479/1250))) :=
  shifted (diagonalBox (479/1250) (by norm_num)) (3/2) (by norm_num) (by diagonal_reference)

private lemma r96_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r96_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl

private lemma r96_shifted_eq {y : ℝ} : U y = Real.sqrt (Q0-(y+1/2)^2) := by
  dsimp [U,ShortOuterOne.SameContact.arc]; ring
private lemma r96_shifted_lo {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).lo = (rootThree (radicand Y) s hs hr).lo :=
  r96_mpr_lo r96_shifted_eq (congrArg _ r96_shifted_eq) _
private lemma r96_shifted_hi {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).hi = (rootThree (radicand Y) s hs hr).hi :=
  r96_mpr_hi r96_shifted_eq (congrArg _ r96_shifted_eq) _

private lemma r96_coordinate_eq {y : ℝ} : ShortOuterOne.SameContact.arc y = U y-1/2 := by
  dsimp [U]; ring
private lemma r96_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r96_mpr_lo r96_coordinate_eq (congrArg _ r96_coordinate_eq) _
private lemma r96_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r96_mpr_hi r96_coordinate_eq (congrArg _ r96_coordinate_eq) _

private lemma r96_label_eq (H : RoleLabel) {y : ℝ} :
    H.outer y = H.c+H.p*(ShortOuterOne.SameContact.arc y)+H.q*y+H.r*y^2+
      H.s*(ShortOuterOne.SameContact.arc y*y) := by
  dsimp [RoleLabel.outer,RoleLabel.eval]; ring
private lemma r96_labelBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).lo = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).lo :=
  r96_mpr_lo (r96_label_eq H) (congrArg _ (r96_label_eq H)) _
private lemma r96_labelBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).hi = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).hi :=
  r96_mpr_hi (r96_label_eq H) (congrArg _ (r96_label_eq H)) _

attribute [local simp ↓] r96_shifted_lo r96_shifted_hi r96_coordinate_lo r96_coordinate_hi
  r96_labelBox_lo r96_labelBox_hi

lemma J_cap : (9353/10000:ℝ)<H 0 cap := by
  let V := HBox 0 cap (by norm_num [cap]) capU
  have hv : (9353/10000:ℝ)<V.lo := by dsimp [V,capU]; diagonal_reference
  exact hv.trans_le V.mem.1

lemma P_cap : (79/10000:ℝ)<H₂ 1 cap ∧ H₁ 1 cap< -(11/250:ℝ) ∧
    (89779/100000:ℝ)<H 1 cap := by
  have hu : 0<capU.lo := by dsimp [capU]; diagonal_reference
  let V := HBox 1 cap (by norm_num [cap]) capU
  let D := H₁Box 1 cap (by norm_num [cap]) capU hu
  let E := H₂Box 1 cap (by norm_num [cap]) capU hu
  have hv : (89779/100000:ℝ)<V.lo := by dsimp [V,capU]; diagonal_reference
  have hd : D.hi< -(11/250:ℝ) := by dsimp [D,capU]; diagonal_reference
  have he : (79/10000:ℝ)<E.lo := by dsimp [E,capU]; diagonal_reference
  exact ⟨he.trans_le E.mem.1,D.mem.2.trans_lt hd,hv.trans_le V.mem.1⟩

lemma L_three : (4523/5000:ℝ)<H 2 (3/10) ∧
    LLabel.d1 (diagonal (3/10))<41/50 ∧
    (169/100:ℝ)<LLabel.d2 (diagonal (3/10)) ∧
    (3/4:ℝ)<diagonal (3/10) := by
  have hu : 0<threeU.lo := by dsimp [threeU]; diagonal_reference
  let Y := diagonalBox (3/10) (by norm_num)
  let V := HBox 2 (3/10) (by norm_num) threeU
  let D := firstBox LLabel Y threeU hu
  let E := secondBox LLabel Y threeU hu
  have hv : (4523/5000:ℝ)<V.lo := by dsimp [V,threeU]; diagonal_reference
  have hd : D.hi<(41/50:ℝ) := by dsimp [D,Y,threeU]; diagonal_reference
  have he : (169/100:ℝ)<E.lo := by dsimp [E,Y,threeU]; diagonal_reference
  have hy : (3/4:ℝ)<Y.lo := by dsimp [Y]; diagonal_reference
  exact ⟨hv.trans_le V.mem.1,D.mem.2.trans_lt hd,he.trans_le E.mem.1,hy.trans_le Y.mem.1⟩

lemma L_minimum : (8977797/10000000:ℝ)<H 2 (479/1250) ∧
    |H₁ 2 (479/1250)|<(1/12500:ℝ) := by
  have hu : 0 < minimumU.lo := by dsimp [minimumU]; diagonal_reference
  let V := HBox 2 (479/1250) (by norm_num) minimumU
  let D := H₁Box 2 (479/1250) (by norm_num) minimumU hu
  have hv : (8977797/10000000:ℝ)<V.lo := by dsimp [V,minimumU]; diagonal_reference
  have hl : -(1/12500:ℝ)<D.lo := by dsimp [D,minimumU]; diagonal_reference
  have hu : D.hi<(1/12500:ℝ) := by dsimp [D,minimumU]; diagonal_reference
  exact ⟨hv.trans_le V.mem.1,abs_lt.mpr ⟨hl.trans_le D.mem.1,D.mem.2.trans_lt hu⟩⟩

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.DiagonalReferences
end
end
end

section
/-!
## The named label comparisons in the written negative-target proof

These references are the left diagonal,
the half-coordinate, and `.9`.  All estimates are proved by substitution
in exact expression enclosures, including the fourth derivative in the
single logarithmic-derivative reference.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.LabelReferences
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra Target.ReferenceAlgebra

local macro "label_reference" : tactic => `(tactic|
  norm_num [coreBox,outerBox,sinBox,cosBox,diagonalBox,speedBox,HBox,H₁Box,H₂Box,
    fourthBox,firstBox,secondBox,thirdBox,
    ratioBox,ratioDBox,radicand,rootThree,rootStep,
    HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
    F,c,g,PLabel,JLabel,LLabel,Q0])

def zeroU : Interval (U (diagonal 0)) :=
  shifted (diagonalBox 0 (by norm_num)) (7/4) (by norm_num) (by label_reference)
def halfU : Interval (U (1/2)) :=
  shifted (Interval.point (1/2)) (17/10) (by norm_num) (by label_reference)
def nineU : Interval (U (9/10)) :=
  shifted (Interval.point (9/10)) (7/5) (by norm_num) (by label_reference)

private lemma r96_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r96_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl

private lemma r96_shifted_eq {y : ℝ} : U y = Real.sqrt (Q0-(y+1/2)^2) := by
  dsimp [U,ShortOuterOne.SameContact.arc]; ring
private lemma r96_shifted_lo {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).lo = (rootThree (radicand Y) s hs hr).lo :=
  r96_mpr_lo r96_shifted_eq (congrArg _ r96_shifted_eq) _
private lemma r96_shifted_hi {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).hi = (rootThree (radicand Y) s hs hr).hi :=
  r96_mpr_hi r96_shifted_eq (congrArg _ r96_shifted_eq) _

private lemma r96_coordinate_eq {y : ℝ} : ShortOuterOne.SameContact.arc y = U y-1/2 := by
  dsimp [U]; ring
private lemma r96_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r96_mpr_lo r96_coordinate_eq (congrArg _ r96_coordinate_eq) _
private lemma r96_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r96_mpr_hi r96_coordinate_eq (congrArg _ r96_coordinate_eq) _

private lemma r96_label_eq (H : RoleLabel) {y : ℝ} :
    H.outer y = H.c+H.p*(ShortOuterOne.SameContact.arc y)+H.q*y+H.r*y^2+
      H.s*(ShortOuterOne.SameContact.arc y*y) := by
  dsimp [RoleLabel.outer,RoleLabel.eval]; ring
private lemma r96_labelBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).lo = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).lo :=
  r96_mpr_lo (r96_label_eq H) (congrArg _ (r96_label_eq H)) _
private lemma r96_labelBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).hi = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).hi :=
  r96_mpr_hi (r96_label_eq H) (congrArg _ (r96_label_eq H)) _

private lemma r96_ratioDD_eq {y : ℝ} :
    ShortOuterOne.SameContact.ratioDD y = 3*Q0*(y+1/2)/((U y)^3*(U y)^2) := by
  dsimp [ShortOuterOne.SameContact.ratioDD,U]; ring
private lemma r96_ratioDDBox_lo {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDDBox Y X hX).lo = (((Interval.point (3*Q0)).mul (Y.add (Interval.point (1/2)))).div
      (X.cube.mul X.square)
      (Interval.mul_lo_pos (Interval.cube_lo_pos hX) (Interval.square_lo_pos hX))).lo :=
  r96_mpr_lo r96_ratioDD_eq (congrArg _ r96_ratioDD_eq) _
private lemma r96_ratioDDBox_hi {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDDBox Y X hX).hi = (((Interval.point (3*Q0)).mul (Y.add (Interval.point (1/2)))).div
      (X.cube.mul X.square)
      (Interval.mul_lo_pos (Interval.cube_lo_pos hX) (Interval.square_lo_pos hX))).hi :=
  r96_mpr_hi r96_ratioDD_eq (congrArg _ r96_ratioDD_eq) _

private lemma r96_ratioDDD_eq {y : ℝ} :
    ratioDDD y = 3*Q0*((U y)^2+5*(y+1/2)^2)/((U y)^3*((U y)^2*(U y)^2)) := by
  dsimp [ratioDDD,W]; ring
private lemma r96_ratioDDDBox_lo {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDDDBox Y X hX).lo = (((Interval.point (3*Q0)).mul (X.square.add ((Interval.point 5).mul
      (Y.add (Interval.point (1/2))).square))).div (X.cube.mul (X.square.mul X.square))
      (Interval.mul_lo_pos (Interval.cube_lo_pos hX)
        (Interval.mul_lo_pos (Interval.square_lo_pos hX) (Interval.square_lo_pos hX)))).lo :=
  r96_mpr_lo r96_ratioDDD_eq (congrArg _ r96_ratioDDD_eq) _
private lemma r96_ratioDDDBox_hi {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDDDBox Y X hX).hi = (((Interval.point (3*Q0)).mul (X.square.add ((Interval.point 5).mul
      (Y.add (Interval.point (1/2))).square))).div (X.cube.mul (X.square.mul X.square))
      (Interval.mul_lo_pos (Interval.cube_lo_pos hX)
        (Interval.mul_lo_pos (Interval.square_lo_pos hX) (Interval.square_lo_pos hX)))).hi :=
  r96_mpr_hi r96_ratioDDD_eq (congrArg _ r96_ratioDDD_eq) _

attribute [local simp ↓] r96_shifted_lo r96_shifted_hi r96_coordinate_lo r96_coordinate_hi
  r96_labelBox_lo r96_labelBox_hi r96_ratioDDBox_lo r96_ratioDDBox_hi
  r96_ratioDDDBox_lo r96_ratioDDDBox_hi

lemma initial : (21/25:ℝ)<PLabel.d1 (diagonal 0) ∧
    JLabel.d1 (diagonal 0)<181/200 ∧ JLabel.d2 (diagonal 0)< -(97/200:ℝ) ∧
    LLabel.d1 (diagonal 0)<41/50 ∧ (51/50:ℝ)<H 0 0 := by
  have hu : 0<zeroU.lo := by dsimp [zeroU]; label_reference
  let P₁ := firstBox PLabel (diagonalBox 0 (by norm_num)) zeroU hu
  let J₁ := firstBox JLabel (diagonalBox 0 (by norm_num)) zeroU hu
  let J₂ := secondBox JLabel (diagonalBox 0 (by norm_num)) zeroU hu
  let L₁ := firstBox LLabel (diagonalBox 0 (by norm_num)) zeroU hu
  let V := HBox 0 0 (by norm_num) zeroU
  have hP : (21/25:ℝ)<P₁.lo := by dsimp [P₁,zeroU]; label_reference
  have hJ : J₁.hi<(181/200:ℝ) := by dsimp [J₁,zeroU]; label_reference
  have hJJ : J₂.hi< -(97/200:ℝ) := by dsimp [J₂,zeroU]; label_reference
  have hL : L₁.hi<(41/50:ℝ) := by dsimp [L₁,zeroU]; label_reference
  have hV : (51/50:ℝ)<V.lo := by dsimp [V,zeroU]; label_reference
  exact ⟨hP.trans_le P₁.mem.1,J₁.mem.2.trans_lt hJ,J₂.mem.2.trans_lt hJJ,
    L₁.mem.2.trans_lt hL,hV.trans_le V.mem.1⟩

lemma P_half : (213/250:ℝ)<PLabel.d1 (1/2) ∧
    (11/50:ℝ)<PLabel.d2 (1/2) ∧ PLabel.d2 (1/2)<221/1000 ∧
    PLabel.d3 (1/2)<153/500 := by
  have hu : 0<halfU.lo := by dsimp [halfU]; label_reference
  let P₁ := firstBox PLabel (Interval.point (1/2)) halfU hu
  let P₂ := secondBox PLabel (Interval.point (1/2)) halfU hu
  let P₃ := thirdBox PLabel (Interval.point (1/2)) halfU hu
  have h1 : (213/250:ℝ)<P₁.lo := by dsimp [P₁,halfU]; label_reference
  have h2 : (11/50:ℝ)<P₂.lo := by dsimp [P₂,halfU]; label_reference
  have h3 : P₂.hi<(221/1000:ℝ) := by dsimp [P₂,halfU]; label_reference
  have h4 : P₃.hi<(153/500:ℝ) := by dsimp [P₃,halfU]; label_reference
  exact ⟨h1.trans_le P₁.mem.1,h2.trans_le P₂.mem.1,P₂.mem.2.trans_lt h3,
    P₃.mem.2.trans_lt h4⟩

lemma nine : PLabel.d3 (9/10)<781/1000 ∧
    (3/5:ℝ)<JLabel.d1 (9/10) ∧ LLabel.d1 (9/10)<233/200 := by
  have hu : 0<nineU.lo := by dsimp [nineU]; label_reference
  let P₃ := thirdBox PLabel (Interval.point (9/10)) nineU hu
  let J₁ := firstBox JLabel (Interval.point (9/10)) nineU hu
  let L₁ := firstBox LLabel (Interval.point (9/10)) nineU hu
  have hP : P₃.hi<(781/1000:ℝ) := by dsimp [P₃,nineU]; label_reference
  have hJ : (3/5:ℝ)<J₁.lo := by dsimp [J₁,nineU]; label_reference
  have hL : L₁.hi<(233/200:ℝ) := by dsimp [L₁,nineU]; label_reference
  exact ⟨P₃.mem.2.trans_lt hP,hJ.trans_le J₁.mem.1,L₁.mem.2.trans_lt hL⟩

lemma L_half : 5<LLabel.d3 (1/2) ∧ LLabel.d2 (1/2)<0 ∧
    (31/1000:ℝ)< -LLabel.d2 (1/2) ∧
    (42/25:ℝ)<(144/13)*LLabel.d1 (1/2)-LLabel.d3 (1/2) ∧
    |(288/13)*LLabel.d2 (1/2)-LLabel.d4 (1/2)|<9 := by
  have hu : 0<halfU.lo := by dsimp [halfU]; label_reference
  let L₁ := firstBox LLabel (Interval.point (1/2)) halfU hu
  let L₂ := secondBox LLabel (Interval.point (1/2)) halfU hu
  let L₃ := thirdBox LLabel (Interval.point (1/2)) halfU hu
  let L₄ := fourthBox LLabel (Interval.point (1/2)) halfU hu
  let D₀ := L₂.neg
  let D₁ := ((Interval.point (144/13)).mul L₁).sub L₃
  let D₂ := ((Interval.point (288/13)).mul L₂).sub L₄
  have h3 : (5:ℝ)<L₃.lo := by dsimp [L₃,halfU]; label_reference
  have h0 : (31/1000:ℝ)<D₀.lo := by dsimp [D₀,L₂,halfU]; label_reference
  have h1 : (42/25:ℝ)<D₁.lo := by dsimp [D₁,L₁,L₃,halfU]; label_reference
  have h2l : (-9:ℝ)<D₂.lo := by dsimp [D₂,L₂,L₄,halfU]; label_reference
  have h2u : D₂.hi<(9:ℝ) := by dsimp [D₂,L₂,L₄,halfU]; label_reference
  have hd : (31/1000:ℝ)< -LLabel.d2 (1/2) := h0.trans_le D₀.mem.1
  exact ⟨h3.trans_le L₃.mem.1,by linarith,hd,h1.trans_le D₁.mem.1,
    abs_lt.mpr ⟨h2l.trans_le D₂.mem.1,D₂.mem.2.trans_lt h2u⟩⟩

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.LabelReferences
end
end
end

section
/-!
## Whole-interval label shapes in the negative target proof

The shapes of the labels on the whole interval: the derivative bounds of J on the band
(`J_second_upper`, `J_first_bounds`), the chord of the third derivative of P (`P_third_chord`)
and the logarithmic-derivative inequality of L (`logarithmic_derivative`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.Shape
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratioD ratioDD)

def band : Set ℝ := Icc (diagonal 0) (9/10)

lemma band_domain {B : ℝ} (hB : B∈band) : B∈Labels.domain :=
  ⟨by linarith [hB.1,(diagonal_bounds (show (0:ℝ)∈angles by norm_num [angles,cap])).1],hB.2⟩

lemma diagonal_band {x : ℝ} (hx : x∈angles) : diagonal x∈band :=
  ⟨diagonal_monotone (by norm_num) (angle_subset hx) hx.1,(diagonal_bounds hx).2.le⟩

lemma J_third_negative {B : ℝ} (hB : B∈band) : JLabel.d3 B<0 := by
  have hb := (diagonal_bounds (show (0:ℝ)∈angles by norm_num [angles,cap])).1
  have hr := Labels.ratio_signs (band_domain hB)
  have hp : 0< -(13/50000:ℝ)+(17627/100000)*B := by linarith [hB.1]
  have hm := mul_pos hp hr.2.2.1
  norm_num [RoleLabel.d3,JLabel]
  nlinarith [hr.2.1]

lemma J_second_antitone : AntitoneOn JLabel.d2 band :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hB => (JLabel.d2_hasDerivAt (Labels.chart_domain (band_domain hB))).continuousAt.continuousWithinAt)
    (fun _ hB => JLabel.d2_hasDerivAt (Labels.chart_domain (band_domain (Ioo_subset_Icc_self hB))))
    (fun _ hB => (J_third_negative (Ioo_subset_Icc_self hB)).le)

lemma J_second_upper {B : ℝ} (hB : B∈band) : JLabel.d2 B< -(97/200:ℝ) := by
  have hz : diagonal 0∈band := ⟨le_rfl,(diagonal_bounds (by norm_num [angles,cap])).2.le⟩
  exact (J_second_antitone hz hB hB.1).trans_lt LabelReferences.initial.2.2.1

lemma J_first_antitone : AntitoneOn JLabel.d1 band :=
  antiOn_of_hasDeriv_nonpos
    (fun B hB => (JLabel.d1_hasDerivAt (Labels.chart_domain (band_domain hB))).continuousAt.continuousWithinAt)
    (fun B hB => JLabel.d1_hasDerivAt (Labels.chart_domain (band_domain (Ioo_subset_Icc_self hB))))
    (fun B hB => by linarith [J_second_upper (Ioo_subset_Icc_self hB)])

lemma J_first_bounds {B : ℝ} (hB : B∈band) : (3/5:ℝ)<JLabel.d1 B ∧ JLabel.d1 B<181/200 := by
  have hz : diagonal 0∈band := ⟨le_rfl,(diagonal_bounds (by norm_num [angles,cap])).2.le⟩
  have hu : (9/10:ℝ)∈band := ⟨hz.2,le_rfl⟩
  exact ⟨LabelReferences.nine.2.1.trans_le (J_first_antitone hB hu hB.2),
    (J_first_antitone hz hB hB.1).trans_lt LabelReferences.initial.2.1⟩

lemma P_third_chord {B : ℝ} (hB : B∈Icc (1/2:ℝ) (9/10)) :
    PLabel.d3 B<153/500+(297/250)*(B-1/2) := by
  have hd {t : ℝ} (ht : t∈Icc (1/2:ℝ) (9/10)) : t∈Labels.domain :=
    ⟨by linarith [ht.1],ht.2⟩
  have hc : ConcaveOn ℝ (Icc (1/2:ℝ) (9/10))
      (fun t => 153/500+(297/250)*(t-1/2)-PLabel.d3 t) :=
    concave_of_deriv2 (f' := fun t => 297/250-PLabel.d4 t) (f'' := fun t => -PLabel.d5 t)
      (fun t ht => (((((hasDerivAt_id' (x:=t)).sub_const (1/2)).const_mul (297/250)).const_add
        (153/500)).fun_sub (PLabel.d3_hasDerivAt (Labels.chart_domain (hd ht)))).congr_deriv
          (by ring))
      (fun t ht => (PLabel.d4_hasDerivAt (Labels.chart_domain (hd ht))).const_sub (297/250))
      (fun t ht => neg_nonpos.mpr (Labels.P_fifth_positive (hd ht)).le)
  have hh := concave_gt_of_endpoints (c:=0) hc hB
    (show 0<(153/500:ℝ)+(297/250)*((1/2:ℝ)-1/2)-PLabel.d3 (1/2) by
      linarith [LabelReferences.P_half.2.2.2])
    (show 0<(153/500:ℝ)+(297/250)*((9/10:ℝ)-1/2)-PLabel.d3 (9/10) by
      linarith [LabelReferences.nine.1])
  linarith

lemma L_first_positive {B : ℝ} (hB : B∈Labels.domain) : (3/5:ℝ)<LLabel.d1 B := by
  have hh := curvature_tangent (κ := (0:ℝ)) hB
    (show (1/2:ℝ)∈Labels.domain by norm_num [Labels.domain])
    (fun t ht => LLabel.d1_hasDerivAt (Labels.chart_domain ht))
    (fun t ht => LLabel.d2_hasDerivAt (Labels.chart_domain ht))
    (fun t ht => (Labels.L_third_positive ht).le)
  have hval := L_first_lower_strong
    (show (1/2:ℝ)∈Icc 0 outerDiagonal from Asymmetric.rational_outer_mem (by norm_num))
  have hs := L_half_second
  have hp : -(8/625:ℝ)≤LLabel.d2 (1/2)*(B-1/2) := by
    by_cases ht : 1/2≤B
    · have h1 := mul_le_mul_of_nonneg_right hs.1.le (sub_nonneg.mpr ht)
      have h2 := mul_le_mul_of_nonpos_left (show B-1/2≤(2/5:ℝ) by linarith [hB.2])
        (by norm_num : (-4/125:ℝ)≤0)
      nlinarith
    · have hm := mul_nonneg_of_nonpos_of_nonpos hs.2.le (by linarith : B-1/2≤0)
      linarith
  nlinarith

def lam : ℝ := 144/13
def D (B : ℝ) : ℝ := lam*(B-1/2)*LLabel.d1 B-LLabel.d2 B
def D₁ (B : ℝ) : ℝ := lam*LLabel.d1 B+lam*(B-1/2)*LLabel.d2 B-LLabel.d3 B
def D₂ (B : ℝ) : ℝ := 2*lam*LLabel.d2 B+lam*(B-1/2)*LLabel.d3 B-LLabel.d4 B
def D₃ (B : ℝ) : ℝ := 3*lam*LLabel.d3 B+lam*(B-1/2)*LLabel.d4 B-LLabel.d5 B

lemma D_hasDerivAt {B : ℝ} (hB : B∈Labels.domain) : HasDerivAt D (D₁ B) B := by
  have hb := Labels.chart_domain hB
  have h : HasDerivAt D _ B :=
    ((((hasDerivAt_id' (x:=B)).sub_const (1/2)).const_mul lam).fun_mul
      (LLabel.d1_hasDerivAt hb)).fun_sub (LLabel.d2_hasDerivAt hb)
  exact h.congr_deriv (by simp only [D₁]; ring)

lemma D₁_hasDerivAt {B : ℝ} (hB : B∈Labels.domain) : HasDerivAt D₁ (D₂ B) B := by
  have hb := Labels.chart_domain hB
  have h : HasDerivAt D₁ _ B :=
    (((LLabel.d1_hasDerivAt hb).const_mul lam).fun_add
      ((((hasDerivAt_id' (x:=B)).sub_const (1/2)).const_mul lam).fun_mul
        (LLabel.d2_hasDerivAt hb))).fun_sub (LLabel.d3_hasDerivAt hb)
  exact h.congr_deriv (by simp only [D₂]; ring)

lemma D₂_hasDerivAt {B : ℝ} (hB : B∈Labels.domain) : HasDerivAt D₂ (D₃ B) B := by
  have hb := Labels.chart_domain hB
  have h : HasDerivAt D₂ _ B :=
    (((LLabel.d2_hasDerivAt hb).const_mul (2*lam)).fun_add
      ((((hasDerivAt_id' (x:=B)).sub_const (1/2)).const_mul lam).fun_mul
        (LLabel.d3_hasDerivAt hb))).fun_sub (LLabel.d4_hasDerivAt hb)
  exact h.congr_deriv (by simp only [D₃]; ring)

lemma D_third_lower {B : ℝ} (hB : B∈Icc (1/2:ℝ) (9/10)) : 60<D₃ B := by
  have hd : B∈Labels.domain := ⟨by linarith [hB.1],hB.2⟩
  have h3 := LabelReferences.L_half.1.trans_le (Labels.L_third_monotone
    (by norm_num [Labels.domain]) hd hB.1)
  have hp := mul_nonneg (sub_nonneg.mpr hB.1) (Labels.L_fourth_positive hd).le
  have h5 := Labels.L_fifth_upper hd
  dsimp [D₃,lam]
  nlinarith

lemma D_first_lower {B : ℝ} (hB : B∈Icc (1/2:ℝ) (9/10)) : (201/200:ℝ)<D₁ B := by
  have hd {t : ℝ} (ht : t∈Icc (1/2:ℝ) (9/10)) : t∈Labels.domain :=
    ⟨by linarith [ht.1],ht.2⟩
  have hh := curvature_tangent (κ := (60:ℝ)) (t := 1/2) hB (by norm_num)
    (fun t ht => D₁_hasDerivAt (hd ht))
    (fun t ht => D₂_hasDerivAt (hd ht)) (fun t ht => (D_third_lower ht).le)
  have e1 : D₁ (1/2)=(144/13)*LLabel.d1 (1/2)-LLabel.d3 (1/2) := by
    simp only [D₁,lam]; ring
  have e2 : D₂ (1/2)=(288/13)*LLabel.d2 (1/2)-LLabel.d4 (1/2) := by
    simp only [D₂,lam]; ring
  have h1 : (42/25:ℝ)<D₁ (1/2) := by
    rw [e1]; exact LabelReferences.L_half.2.2.2.1
  have h2 : |D₂ (1/2)|<9 := by rw [e2]; exact LabelReferences.L_half.2.2.2.2
  have hp := mul_nonneg (show 0≤D₂ (1/2)+9 by linarith [(abs_lt.mp h2).1])
    (sub_nonneg.mpr hB.1)
  nlinarith [sq_nonneg (B-1/2-3/20)]

lemma logarithmic_derivative {B : ℝ} (hB : B∈Icc (1/2:ℝ) (9/10)) :
    LLabel.d2 B<(144/13)*(B-1/2)*LLabel.d1 B := by
  have hd {t : ℝ} (ht : t∈Icc (1/2:ℝ) (9/10)) : t∈Labels.domain :=
    ⟨by linarith [ht.1],ht.2⟩
  have hm : MonotoneOn D (Icc (1/2:ℝ) (9/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (D_hasDerivAt (hd ht)).continuousAt.continuousWithinAt)
      (fun t ht => D_hasDerivAt (hd (Ioo_subset_Icc_self ht)))
      (fun t ht => by linarith [D_first_lower (Ioo_subset_Icc_self ht)])
  have hz : 0<D (1/2) := by
    dsimp [D]
    linarith [LabelReferences.L_half.2.1]
  have hh := hz.trans_le (hm (by norm_num) hB hB.1)
  dsimp [D,lam] at hh
  linarith

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.Shape
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.LDiagonal
open CommonQuarter CorePairGeometry Arithmetic

lemma first_label_early {B : ℝ} (hB : B∈Icc (diagonal 0) (diagonal (3/10))) :
    LLabel.d1 B<41/50 := by
  have h0 : (0:ℝ)∈angles := by norm_num [angles,cap]
  have h3 : (3/10:ℝ)∈angles := by norm_num [angles,cap]
  have hdom {t : ℝ} (ht : t∈Icc (diagonal 0) (diagonal (3/10))) : t∈Labels.domain :=
    ⟨by linarith [ht.1,(diagonal_bounds h0).1],ht.2.trans (diagonal_domain h3).2⟩
  have hc : ConcaveOn ℝ (Icc (diagonal 0) (diagonal (3/10)))
      (fun t => (41/50:ℝ)-LLabel.d1 t) :=
    concave_of_deriv2
      (fun t ht => (LLabel.d1_hasDerivAt (Labels.chart_domain (hdom ht))).const_sub (41/50))
      (fun t ht => (LLabel.d2_hasDerivAt (Labels.chart_domain (hdom ht))).fun_neg)
      (fun t ht => neg_nonpos.mpr (Labels.L_third_positive (hdom ht)).le)
  have hh := concave_gt_of_endpoints (c:=0) hc hB
    (by linarith [LabelReferences.initial.2.2.2.1])
    (by linarith [DiagonalReferences.L_three.2.1])
  linarith

lemma first_label_upper {B : ℝ} (hB : B∈Shape.band) : LLabel.d1 B<233/200 := by
  have hc : ConcaveOn ℝ Shape.band (fun t => (233/200:ℝ)-LLabel.d1 t) :=
    concave_of_deriv2
      (fun t ht => (LLabel.d1_hasDerivAt
        (Labels.chart_domain (Shape.band_domain ht))).const_sub (233/200))
      (fun t ht => (LLabel.d2_hasDerivAt (Labels.chart_domain (Shape.band_domain ht))).fun_neg)
      (fun t ht => neg_nonpos.mpr (Labels.L_third_positive (Shape.band_domain ht)).le)
  have hh := concave_gt_of_endpoints (c:=0) hc hB
    (by linarith [LabelReferences.initial.2.2.2.1])
    (by linarith [LabelReferences.nine.2.2])
  linarith

lemma first_early_negative {x : ℝ} (hx : x∈Icc (0:ℝ) (3/10)) : H₁ 2 x<0 := by
  have ha : x∈angles := ⟨hx.1,by norm_num [cap]; linarith [hx.2]⟩
  have hb : diagonal x∈Icc (diagonal 0) (diagonal (3/10)) :=
    ⟨diagonal_monotone (by norm_num) (angle_subset ha) hx.1,
      diagonal_monotone (angle_subset ha) (by norm_num) hx.2⟩
  have hp := first_label_early hb
  have hw := speed_bounds ha
  have hm := mul_le_mul hp.le hw.2.1.le
    (speed_positive (angle_subset ha)).le (by norm_num)
  norm_num [H₁,F]
  linarith

lemma early {x : ℝ} (hx : x∈Icc (0:ℝ) (3/10)) : (17953/20000:ℝ)<H 2 x := by
  have ha {t : ℝ} (ht : t∈Icc (0:ℝ) (3/10)) : t∈angles :=
    ⟨ht.1,by norm_num [cap]; linarith [ht.2]⟩
  have hm : AntitoneOn (H 2) (Icc (0:ℝ) (3/10)) :=
    antiOn_of_hasDeriv_nonpos
      (fun t ht => (H_hasDerivAt 2 (ha ht)).continuousAt.continuousWithinAt)
      (fun t ht => H_hasDerivAt 2 (ha (Ioo_subset_Icc_self ht)))
      (fun t ht => (first_early_negative (Ioo_subset_Icc_self ht)).le)
  have hh := hm hx (by norm_num) hx.2
  linarith [DiagonalReferences.L_three.1]

lemma second_late_lower {x : ℝ} (hx : x∈Icc (3/10:ℝ) cap) : (11/10:ℝ)<H₂ 2 x := by
  have ha : x∈angles := ⟨by linarith [hx.1],hx.2⟩
  have hb := diagonal_domain ha
  have hthree : (3/10:ℝ)∈angles := by norm_num [angles,cap]
  have hm := diagonal_monotone (angle_subset hthree) (angle_subset ha) hx.1
  have h2 := DiagonalReferences.L_three.2.2.1.trans_le
    (Labels.L_second_monotone (diagonal_domain hthree) hb hm)
  have h1 := Shape.L_first_positive hb
  have h1u := first_label_upper (Shape.diagonal_band ha)
  have hw := speed_bounds ha
  have hp := mul_le_mul h2.le
    hw.2.2.1.le (by norm_num : (0:ℝ)≤24/25) (by linarith : 0≤LLabel.d2 (diagonal x))
  have hq := mul_nonneg (show 0≤LLabel.d1 (diagonal x) by linarith)
    (show 0≤(1/2-diagonal x)+2/5 by linarith [hb.2])
  norm_num [H₂,F]
  nlinarith

lemma late {x : ℝ} (hx : x∈Icc (3/10:ℝ) cap) : (17953/20000:ℝ)<H 2 x := by
  have ha {t : ℝ} (ht : t∈Icc (3/10:ℝ) cap) : t∈angles :=
    ⟨by linarith [ht.1],ht.2⟩
  have ht : (479/1250:ℝ)∈Icc (3/10:ℝ) cap := by norm_num [cap]
  have hh := curvature_tangent (κ := (11/10:ℝ)) hx ht
    (fun t ht => H_hasDerivAt 2 (ha ht))
    (fun t ht => H₁_hasDerivAt 2 (ha ht))
    (fun t ht => (second_late_lower ht).le)
  have hs := abs_lt.mp DiagonalReferences.L_minimum.2
  have hp := mul_pos (show 0<H₁ 2 (479/1250)+1/12500 by linarith [hs.1])
    (show 0<(1/12500:ℝ)-H₁ 2 (479/1250) by linarith [hs.2])
  nlinarith [DiagonalReferences.L_minimum.1,
    sq_nonneg ((11/10)*(x-479/1250)+H₁ 2 (479/1250))]

lemma lower {x : ℝ} (hx : x∈angles) : (17953/20000:ℝ)<H 2 x := by
  by_cases he : x≤3/10
  · exact early ⟨hx.1,he⟩
  · exact late ⟨by linarith,hx.2⟩

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.LDiagonal
end
end
end
