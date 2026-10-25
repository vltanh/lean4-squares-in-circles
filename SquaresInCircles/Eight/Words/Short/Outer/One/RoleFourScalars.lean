module

public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJBoundaryReferences

/-!
# Eight squares: the role-four positive-sign endpoint scalars

The derivative of the common diagonal scalar is concave and is positive
at alignment. Its minimum therefore lies at one of the two angle
endpoints. The separate .3 evaluation locates the intrinsic support
transition used in the primary owner.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.RoleFour
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open SecondWord.SameZero.PJ.Reference (sinBox cosBox)

def weight : ℝ := 71553/100000
def target : ℝ := 86884/100000
def constant : ℝ := 3846/100000
def diagonal (x : ℝ) : ℝ := Real.pi/2-x+constant-target*outerDiagonal+weight/2+
  weight*(1/2-outerDiagonal)*Real.cos x+weight*(1/2+outerDiagonal)*Real.sin x
def diagonalD (x : ℝ) : ℝ :=
  -1+weight*(outerDiagonal-1/2)*Real.sin x+weight*(outerDiagonal+1/2)*Real.cos x
def diagonalDD (x : ℝ) : ℝ :=
  weight*(outerDiagonal-1/2)*Real.cos x-weight*(outerDiagonal+1/2)*Real.sin x
def diagonalDDD (x : ℝ) : ℝ :=
  -weight*(outerDiagonal-1/2)*Real.sin x-weight*(outerDiagonal+1/2)*Real.cos x

def primaryHigh (x : ℝ) : ℝ := Real.pi/2+x+constant-target*outerDiagonal+weight/2+
  weight*(1/2-outerDiagonal)*(Real.cos x+Real.sin x)
def primaryHighD (x : ℝ) : ℝ :=
  1-weight*(outerDiagonal-1/2)*(Real.cos x-Real.sin x)
def secondaryHigh (x : ℝ) : ℝ :=
  Real.pi/2+x+constant-(weight+target)*outerDiagonal+weight/2+
    weight*Real.cos x/2+weight*(1/2-outerAxial)*Real.sin x
def secondaryHighD (x : ℝ) : ℝ :=
  1-weight*Real.sin x/2+weight*(1/2-outerAxial)*Real.cos x
def secondaryLow (x : ℝ) : ℝ :=
  Real.pi/2-x+constant-(weight+target)*outerDiagonal+weight/2+
    weight*Real.cos x/2+weight*(1/2+outerAxial)*Real.sin x
def secondaryLowD (x : ℝ) : ℝ :=
  -1-weight*Real.sin x/2+weight*(1/2+outerAxial)*Real.cos x
def secondaryLowDD (x : ℝ) : ℝ :=
  -weight*Real.cos x/2-weight*(1/2+outerAxial)*Real.sin x

lemma diagonal_hasDerivAt (x : ℝ) : HasDerivAt diagonal (diagonalD x) x := by
  convert (((((hasDerivAt_id x).neg).const_add
    (Real.pi/2+constant-target*outerDiagonal+weight/2)).add
      ((Real.hasDerivAt_cos x).const_mul (weight*(1/2-outerDiagonal)))).add
        ((Real.hasDerivAt_sin x).const_mul (weight*(1/2+outerDiagonal)))) using 1
  · funext y; simp only [diagonal,Pi.add_apply,Pi.neg_apply,id_eq]; ring
  · simp only [diagonalD]; ring

lemma diagonalD_hasDerivAt (x : ℝ) : HasDerivAt diagonalD (diagonalDD x) x := by
  convert ((((Real.hasDerivAt_sin x).const_mul (weight*(outerDiagonal-1/2))).const_add (-1)).add
    ((Real.hasDerivAt_cos x).const_mul (weight*(outerDiagonal+1/2)))) using 1
  · funext y; simp only [diagonalD,Pi.add_apply]
  · simp only [diagonalDD]; ring

lemma diagonalDD_hasDerivAt (x : ℝ) : HasDerivAt diagonalDD (diagonalDDD x) x := by
  convert (((Real.hasDerivAt_cos x).const_mul (weight*(outerDiagonal-1/2))).sub
    ((Real.hasDerivAt_sin x).const_mul (weight*(outerDiagonal+1/2)))) using 1
  · funext y; simp only [diagonalDD,Pi.sub_apply]
  · simp only [diagonalDDD]; ring

lemma diagonalD_concave : ConcaveOn ℝ (Icc 0 (7/10)) diagonalD := by
  apply concave_of_deriv2 (fun x _ => diagonalD_hasDerivAt x)
    (fun x _ => diagonalDD_hasDerivAt x)
  intro x hx
  have ht := positive_trig hx
  have hs := mul_nonneg (show 0≤weight*(outerDiagonal-1/2) by
    dsimp [weight]; linarith [outer_endpoint_bounds.2.2.1]) ht.2.2.1
  have hc := mul_nonneg (show 0≤weight*(outerDiagonal+1/2) by
    dsimp [weight]; linarith [outer_endpoint_bounds.2.2.1])
    (show 0≤Real.cos x by linarith [ht.1])
  dsimp [diagonalDDD]
  linarith

def piBox : Interval Real.pi :=
  Interval.of_bounds ⟨pi_hand_enclosure.1.le,pi_hand_enclosure.2.le⟩
def dBox : Interval outerDiagonal := Interval.of_bounds
  ⟨ShortMixedZero.fine_diagonal_bounds.1.le,ShortMixedZero.fine_diagonal_bounds.2.le⟩
def aBox : Interval outerAxial := Interval.of_bounds
  ⟨ShortOuterZero.fine_axial_bounds.1.le,ShortOuterZero.fine_axial_bounds.2.le⟩
def diagonalBox (x : ℝ) (hx : 0≤x) : Interval (diagonal x) := by
  convert ((((((piBox.mul (Interval.point (1/2))).sub (Interval.point x)).add
    (Interval.point constant)).sub ((Interval.point target).mul dBox)).add
      (Interval.point (weight/2))).add
        (((Interval.point weight).mul ((Interval.point (1/2)).sub dBox)).mul (cosBox x hx))).add
          (((Interval.point weight).mul ((Interval.point (1/2)).add dBox)).mul (sinBox x hx)) using 1
  dsimp [diagonal]
  ring
def diagonalDBox (x : ℝ) (hx : 0≤x) : Interval (diagonalD x) := by
  convert ((Interval.point (-1)).add
    (((Interval.point weight).mul (dBox.sub (Interval.point (1/2)))).mul (sinBox x hx))).add
      (((Interval.point weight).mul (dBox.add (Interval.point (1/2)))).mul (cosBox x hx)) using 1
  dsimp [diagonalD]
def secondaryLowBox (x : ℝ) (hx : 0≤x) : Interval (secondaryLow x) := by
  convert ((((((piBox.mul (Interval.point (1/2))).sub (Interval.point x)).add
    (Interval.point constant)).sub ((Interval.point (weight+target)).mul dBox)).add
      (Interval.point (weight/2))).add
        ((Interval.point (weight/2)).mul (cosBox x hx))).add
          (((Interval.point weight).mul ((Interval.point (1/2)).add aBox)).mul (sinBox x hx)) using 1
  dsimp [secondaryLow]
  ring

private lemma r87_mpr_lo {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).lo=S.lo := by subst e; rfl

private lemma r87_diagonalBox_lo (x : ℝ) (hx : 0≤x) : (diagonalBox x hx).lo=
    (((((((piBox.mul (Interval.point (1/2))).sub (Interval.point x)).add
    (Interval.point constant)).sub ((Interval.point target).mul dBox)).add
      (Interval.point (weight/2))).add
        (((Interval.point weight).mul ((Interval.point (1/2)).sub dBox)).mul (cosBox x hx))).add
          (((Interval.point weight).mul ((Interval.point (1/2)).add dBox)).mul (sinBox x hx))).lo := by
  dsimp only [diagonalBox]
  apply r87_mpr_lo
  simp only [diagonal]; ring

private lemma r87_diagonalDBox_lo (x : ℝ) (hx : 0≤x) : (diagonalDBox x hx).lo=
    (((Interval.point (-1)).add
    (((Interval.point weight).mul (dBox.sub (Interval.point (1/2)))).mul (sinBox x hx))).add
      (((Interval.point weight).mul (dBox.add (Interval.point (1/2)))).mul (cosBox x hx))).lo := by
  dsimp only [diagonalDBox]
  apply r87_mpr_lo
  simp only [diagonalD]

private lemma r87_secondaryLowBox_lo (x : ℝ) (hx : 0≤x) : (secondaryLowBox x hx).lo=
    (((((((piBox.mul (Interval.point (1/2))).sub (Interval.point x)).add
    (Interval.point constant)).sub ((Interval.point (weight+target)).mul dBox)).add
      (Interval.point (weight/2))).add
        ((Interval.point (weight/2)).mul (cosBox x hx))).add
          (((Interval.point weight).mul ((Interval.point (1/2)).add aBox)).mul (sinBox x hx))).lo := by
  dsimp only [secondaryLowBox]
  apply r87_mpr_lo
  simp only [secondaryLow]; ring

local macro "role_four_reference" : tactic => `(tactic|
  norm_num [diagonalBox,diagonalDBox,secondaryLowBox,piBox,dBox,aBox,
    SecondWord.SameZero.PJ.Reference.sinBox,SecondWord.SameZero.PJ.Reference.cosBox,
    Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,Interval.mul,
    HighOrderTaylor.S17,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C18,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    sin9,sin7,cos10,cos8,weight,target,constant])

lemma fine_cap_trig :
    (64421768723/100000000000:ℝ)<Real.sin (7/10) ∧
    Real.sin (7/10)<64421768724/100000000000 ∧
    (76484218728/100000000000:ℝ)<Real.cos (7/10) ∧
    Real.cos (7/10)<76484218729/100000000000 := by
  have hs := (sinBox (7/10) (by norm_num)).mem
  have hc := (cosBox (7/10) (by norm_num)).mem
  have hsl : (64421768723/100000000000:ℝ)<(sinBox (7/10) (by norm_num)).lo := by
    role_four_reference
  have hsu : (sinBox (7/10) (by norm_num)).hi<(64421768724/100000000000:ℝ) := by
    role_four_reference
  have hcl : (76484218728/100000000000:ℝ)<(cosBox (7/10) (by norm_num)).lo := by
    role_four_reference
  have hcu : (cosBox (7/10) (by norm_num)).hi<(76484218729/100000000000:ℝ) := by
    role_four_reference
  exact ⟨hsl.trans_le hs.1,hs.2.trans_lt hsu,hcl.trans_le hc.1,hc.2.trans_lt hcu⟩

lemma diagonal_initial : (90009/100000:ℝ)<diagonal 0 := by
  have hh : (90009/100000:ℝ)<(diagonalBox 0 (by norm_num)).lo := by
    rw [r87_diagonalBox_lo]; role_four_reference
  exact hh.trans_le (diagonalBox 0 (by norm_num)).mem.1

lemma diagonal_final : (91224/100000:ℝ)<diagonal (7/10) := by
  have hh : (91224/100000:ℝ)<(diagonalBox (7/10) (by norm_num)).lo := by
    rw [r87_diagonalBox_lo]; role_four_reference
  exact hh.trans_le (diagonalBox (7/10) (by norm_num)).mem.1

lemma diagonalD_initial : (117/100000:ℝ)<diagonalD 0 := by
  have hh : (117/100000:ℝ)<(diagonalDBox 0 (by norm_num)).lo := by
    rw [r87_diagonalDBox_lo]; role_four_reference
  exact hh.trans_le (diagonalDBox 0 (by norm_num)).mem.1

lemma diagonalD_reference : (408/10000:ℝ)<diagonalD (3/10) := by
  have hh : (408/10000:ℝ)<(diagonalDBox (3/10) (by norm_num)).lo := by
    rw [r87_diagonalDBox_lo]; role_four_reference
  exact hh.trans_le (diagonalDBox (3/10) (by norm_num)).mem.1

/-- A concave derivative positive at the left endpoint cannot become
negative and subsequently return to zero. -/
lemma minimum_of_concave_derivative {f f' : ℝ→ℝ} {l u x : ℝ}
    (hf : ∀y∈Icc l u,HasDerivAt f (f' y) y)
    (hd : ConcaveOn ℝ (Icc l u) f') (hdl : 0≤f' l) (hx : x∈Icc l u) :
    min (f l) (f u)≤f x := by
  have hl : l∈Icc l u := ⟨le_rfl,hx.1.trans hx.2⟩
  have hnonneg {a b : ℝ} (ha : a∈Icc l u) (hb : b∈Icc l a)
      (hda : 0≤f' a) : 0≤f' b := by
    exact (le_min hdl hda).trans (hd.min_le_of_mem_Icc hl ha hb)
  by_cases hdx : 0≤f' x
  · have hm : MonotoneOn f (Icc l x) := monoOn_of_hasDeriv_nonneg
      (fun y hy => (hf y ⟨hy.1,hy.2.trans hx.2⟩).continuousAt.continuousWithinAt)
      (fun y hy => hf y ⟨hy.1.le,hy.2.le.trans hx.2⟩)
      (fun y hy => hnonneg hx (Ioo_subset_Icc_self hy) hdx)
    exact (min_le_left _ _).trans (hm ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1)
  · have hm : AntitoneOn f (Icc x u) := by
      apply antiOn_of_hasDeriv_nonpos
      · intro y hy
        exact (hf y ⟨hx.1.trans hy.1,hy.2⟩).continuousAt.continuousWithinAt
      · intro y hy
        exact hf y ⟨hx.1.trans hy.1.le,hy.2.le⟩
      · intro y hy
        by_contra! hdy
        exact hdx (hnonneg ⟨hx.1.trans hy.1.le,hy.2.le⟩ ⟨hx.1,hy.1.le⟩ hdy.le)
    exact (min_le_right _ _).trans (hm ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2)

lemma diagonal_lower {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (90009/100000:ℝ)<diagonal x := by
  have hh := minimum_of_concave_derivative (fun y _ => diagonal_hasDerivAt y)
    diagonalD_concave (by linarith [diagonalD_initial]) hx
  exact (lt_min diagonal_initial (by linarith [diagonal_final])).trans_le hh

lemma diagonal_increasing : MonotoneOn diagonal (Icc 0 (3/10)) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro x hx
    exact (diagonal_hasDerivAt x).continuousAt.continuousWithinAt
  · intro x hx
    exact diagonal_hasDerivAt x
  · intro x hx
    have hh := diagonalD_concave.min_le_of_mem_Icc (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
      (show (3/10:ℝ)∈Icc 0 (7/10) by norm_num) (Ioo_subset_Icc_self hx)
    exact (le_min (by linarith [diagonalD_initial]) (by linarith [diagonalD_reference])).trans hh

lemma primaryHigh_hasDerivAt (x : ℝ) : HasDerivAt primaryHigh (primaryHighD x) x := by
  convert ((hasDerivAt_id x).const_add
    (Real.pi/2+constant-target*outerDiagonal+weight/2)).add
      (((Real.hasDerivAt_cos x).add (Real.hasDerivAt_sin x)).const_mul
        (weight*(1/2-outerDiagonal))) using 1
  · funext y; simp only [primaryHigh,Pi.add_apply,id_eq]; ring
  · simp only [primaryHighD]; ring

lemma primaryHigh_lower {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (90009/100000:ℝ)<primaryHigh x := by
  have hm : MonotoneOn primaryHigh (Icc 0 (7/10)) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro y hy
      exact (primaryHigh_hasDerivAt y).continuousAt.continuousWithinAt
    · intro y hy
      exact primaryHigh_hasDerivAt y
    · intro y hy
      have ht := positive_trig (Ioo_subset_Icc_self hy)
      have hd := outer_endpoint_bounds
      have hp := mul_le_mul_of_nonneg_left
        (show Real.cos y-Real.sin y≤1 by linarith [ht.2.1,ht.2.2.1])
        (show 0≤weight*(outerDiagonal-1/2) by dsimp [weight]; linarith [hd.2.2.1])
      dsimp [primaryHighD,weight] at *
      linarith [hd.2.2.2]
  have he : primaryHigh 0=diagonal 0 := by norm_num [primaryHigh,diagonal]
  have h0 := diagonal_initial
  rw [←he] at h0
  exact h0.trans_le (hm (by norm_num) hx hx.1)

lemma secondaryHigh_hasDerivAt (x : ℝ) : HasDerivAt secondaryHigh (secondaryHighD x) x := by
  convert (((hasDerivAt_id x).const_add
    (Real.pi/2+constant-(weight+target)*outerDiagonal+weight/2)).add
      ((Real.hasDerivAt_cos x).const_mul (weight/2))).add
        ((Real.hasDerivAt_sin x).const_mul (weight*(1/2-outerAxial))) using 1
  · funext y; simp only [secondaryHigh,Pi.add_apply,id_eq]; ring
  · simp only [secondaryHighD]; ring

lemma secondaryHigh_derivative {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (1/4:ℝ)<secondaryHighD x := by
  have ha := ShortOuterZero.fine_axial_bounds
  have htr := positive_trig hx
  have hcircle := Real.sin_sq_add_cos_sq x
  have hcoefficient : (1/4:ℝ)+(outerAxial-1/2)^2<(1043/1000:ℝ)^2 := by nlinarith
  have hnorm : (Real.sin x/2+(outerAxial-1/2)*Real.cos x)^2≤
      1/4+(outerAxial-1/2)^2 := by
    have hh := sq_nonneg ((outerAxial-1/2)*Real.sin x-Real.cos x/2)
    have he : (Real.sin x/2+(outerAxial-1/2)*Real.cos x)^2+
        ((outerAxial-1/2)*Real.sin x-Real.cos x/2)^2=1/4+(outerAxial-1/2)^2 := by
      linear_combination (1/4+(outerAxial-1/2)^2)*hcircle
    linarith
  have hproj : Real.sin x/2+(outerAxial-1/2)*Real.cos x<1043/1000 := by nlinarith
  dsimp [secondaryHighD,weight]
  nlinarith

lemma secondaryHigh_lower {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (90009/100000:ℝ)<secondaryHigh x := by
  have hm : MonotoneOn secondaryHigh (Icc 0 (7/10)) := monoOn_of_hasDeriv_nonneg
    (fun y _ => (secondaryHigh_hasDerivAt y).continuousAt.continuousWithinAt)
    (fun y _ => secondaryHigh_hasDerivAt y)
    (fun y hy => by linarith [secondaryHigh_derivative (Ioo_subset_Icc_self hy)])
  have he : secondaryHigh 0=diagonal 0 := by norm_num [secondaryHigh,diagonal]; ring
  exact (he.symm ▸ diagonal_initial).trans_le (hm (by norm_num) hx hx.1)

lemma secondaryLow_hasDerivAt (x : ℝ) : HasDerivAt secondaryLow (secondaryLowD x) x := by
  convert ((((hasDerivAt_id x).neg).const_add
    (Real.pi/2+constant-(weight+target)*outerDiagonal+weight/2)).add
      ((Real.hasDerivAt_cos x).const_mul (weight/2))).add
        ((Real.hasDerivAt_sin x).const_mul (weight*(1/2+outerAxial))) using 1
  · funext y; simp only [secondaryLow,Pi.add_apply,Pi.neg_apply,id_eq]; ring
  · simp only [secondaryLowD]; ring

lemma secondaryLowD_hasDerivAt (x : ℝ) : HasDerivAt secondaryLowD (secondaryLowDD x) x := by
  convert ((((Real.hasDerivAt_sin x).const_mul (weight/2)).neg).const_add (-1)).add
    ((Real.hasDerivAt_cos x).const_mul (weight*(1/2+outerAxial))) using 1
  · funext y; simp only [secondaryLowD,Pi.add_apply,Pi.neg_apply]; ring
  · simp only [secondaryLowDD]; ring

lemma secondaryLow_final : (9985/10000:ℝ)<secondaryLow (7/10) := by
  have hh : (9985/10000:ℝ)<(secondaryLowBox (7/10) (by norm_num)).lo := by
    rw [r87_secondaryLowBox_lo]; role_four_reference
  exact hh.trans_le (secondaryLowBox (7/10) (by norm_num)).mem.1

lemma secondaryLow_lower {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (90009/100000:ℝ)<secondaryLow x := by
  have hc : ConcaveOn ℝ (Icc 0 (7/10)) secondaryLow := concave_of_deriv2
    (fun y _ => secondaryLow_hasDerivAt y) (fun y _ => secondaryLowD_hasDerivAt y)
    (fun y hy => by
      have ht := positive_trig hy
      have hs := mul_nonneg (show 0≤weight*(1/2+outerAxial) by
        dsimp [weight]; linarith [outer_endpoint_bounds.1]) ht.2.2.1
      have hw : 0≤weight*Real.cos y :=
        mul_nonneg (by norm_num [weight]) (by linarith [ht.1])
      dsimp only [secondaryLowDD]
      linarith)
  have he : secondaryLow 0=diagonal 0 := by norm_num [secondaryLow,diagonal]; ring
  exact concave_gt_of_endpoints hc hx (he.symm ▸ diagonal_initial)
    (by linarith [secondaryLow_final])

end SquaresInCircles.Eight.ShortOuterOne.RoleFour
