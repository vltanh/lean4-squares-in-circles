module

public import SquaresInCircles.Eight.Words.Common.JumpTwo
public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds
public import SquaresInCircles.Eight.Words.Second.Outer.LBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeUpperEasy

/-!
# Eight squares: whole lower-half concavity for the wider mixed support slopes

The exact circular norm curvature bound remains sufficient when the
transverse coefficient is as large as .95 of the separator multiplier.
-/

section
/-!
## The unchanged canonical core corner in one coordinate

This chart includes the side join and the diagonal.  The derivative
formulas use its positive radical directly, so no angular reparametrizing
or strict-owner convention is required.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedCorner
open CommonQuarter CorePairGeometry Arithmetic

def domain : Set ℝ := Icc (1/2) CoreAngleEndpoint.diagonal
def z (b : ℝ) : ℝ := Real.sqrt (1/144-(b-1/2)^2)
def a (b : ℝ) : ℝ := 1/2+z b
def w (b : ℝ) : ℝ := (b-1/2)/z b

lemma radicand_positive {b : ℝ} (hb : b∈domain) : 0<(1/144:ℝ)-(b-1/2)^2 := by
  have hs := pow_le_pow_left₀ (sub_nonneg.mpr hb.1)
    (show b-1/2≤CoreAngleEndpoint.diagonal-1/2 by linarith [hb.2]) 2
  nlinarith [CoreAngleEndpoint.diagonal_sq]

lemma z_positive {b : ℝ} (hb : b∈domain) : 0<z b := Real.sqrt_pos.mpr (radicand_positive hb)
lemma z_sq {b : ℝ} (hb : b∈domain) : (z b)^2+(b-1/2)^2=(1/144:ℝ) := by
  have hh := Real.sq_sqrt (radicand_positive hb).le
  change (z b)^2=1/144-(b-1/2)^2 at hh
  linarith

lemma chart_bounds {b : ℝ} (hb : b∈domain) :
    CoreAngleEndpoint.diagonal-1/2≤z b ∧ z b≤1/12 ∧ b≤a b := by
  have hp := z_positive hb
  have hs := z_sq hb
  have hdiag := CoreAngleEndpoint.diagonal_bounds
  have hsmall := pow_le_pow_left₀ (sub_nonneg.mpr hb.1)
    (show b-1/2≤CoreAngleEndpoint.diagonal-1/2 by linarith [hb.2]) 2
  refine ⟨?_,?_,?_⟩
  · nlinarith [CoreAngleEndpoint.diagonal_sq]
  · nlinarith [sq_nonneg (b-1/2)]
  · dsimp [a]
    nlinarith [CoreAngleEndpoint.diagonal_sq]

lemma state {b : ℝ} (hb : b∈domain) : CoreState (a b) b := by
  refine Or.inr ⟨hb.1,(chart_bounds hb).2.2,?_⟩
  dsimp [a]
  nlinarith [z_sq hb]

lemma actual {A B : ℝ} (hB : 1/2≤B) (hBA : B≤A)
    (hc : (A-1/2)^2+(B-1/2)^2=(1/12:ℝ)^2) :
    B∈domain ∧ A=a B := by
  have hdom : B∈domain := ⟨hB,(CoreAngleEndpoint.corner_diagonal hB hBA hc).1⟩
  have hp := z_positive hdom
  have hs := z_sq hdom
  refine ⟨hdom,?_⟩
  dsimp [a]
  nlinarith

lemma join : a (1/2)=(7/12:ℝ) := by
  have hb : (1/2:ℝ)∈domain := ⟨le_rfl,by linarith [CoreAngleEndpoint.diagonal_bounds.1]⟩
  have hs := z_sq hb
  have hp := z_positive hb
  dsimp [a]
  nlinarith

lemma diagonal : a CoreAngleEndpoint.diagonal=CoreAngleEndpoint.diagonal := by
  have hb : CoreAngleEndpoint.diagonal∈domain :=
    ⟨by linarith [CoreAngleEndpoint.diagonal_bounds.1],le_rfl⟩
  have hs := z_sq hb
  have hp := z_positive hb
  dsimp [a]
  nlinarith [CoreAngleEndpoint.diagonal_sq,CoreAngleEndpoint.diagonal_bounds.1]

lemma w_bounds {b : ℝ} (hb : b∈domain) : 0≤w b ∧ w b≤1 := by
  have hp := z_positive hb
  have hba := (chart_bounds hb).2.2
  constructor
  · exact div_nonneg (sub_nonneg.mpr hb.1) hp.le
  · apply (div_le_one hp).2
    dsimp [a] at hba
    linarith

lemma circle_ratio {b : ℝ} (hb : b∈domain) : (1+(w b)^2)*(z b)^2=(1/144:ℝ) := by
  have hp := z_positive hb
  dsimp [w]
  field_simp [hp.ne']
  nlinarith [z_sq hb]

lemma z_hasDerivAt {b : ℝ} (hb : b∈domain) : HasDerivAt z (-w b) b := by
  have hp := z_positive hb
  have h1 : HasDerivAt (fun y : ℝ => 1/144-(y-1/2)^2) (-(2*(b-1/2))) b := by
    have h := (((hasDerivAt_id b).sub_const (1/2)).pow 2).const_sub (1/144)
    convert h using 1
    · funext y
      simp
    · simp only [id]
      norm_num
  have h2 := h1.sqrt (radicand_positive hb).ne'
  have hz : (fun y : ℝ => Real.sqrt (1/144-(y-1/2)^2))=z := rfl
  rw [hz] at h2
  convert h2 using 1
  rw [show Real.sqrt (1/144-(b-1/2)^2)=z b from rfl]
  dsimp only [w]
  field_simp

lemma a_hasDerivAt {b : ℝ} (hb : b∈domain) : HasDerivAt a (-w b) b :=
  (z_hasDerivAt hb).const_add (1/2)

lemma w_hasDerivAt {b : ℝ} (hb : b∈domain) :
    HasDerivAt w ((1+(w b)^2)/z b) b := by
  have hp := z_positive hb
  have hd := ((hasDerivAt_id b).sub_const (1/2)).div (z_hasDerivAt hb) hp.ne'
  convert hd using 1
  · rfl
  · dsimp [w]
    field_simp [hp.ne']
    ring

lemma endpoint_mass {b : ℝ} (hb : b∈domain) :
    (a b+1/2)^2+(b-1/2)^2∈Icc (112479/100000:ℝ) (169/144) := by
  have hs := z_sq hb
  have hbounds := chart_bounds hb
  have he : (a b+1/2)^2+(b-1/2)^2=1+2*z b+1/144 := by
    dsimp [a]
    nlinarith
  rw [he]
  constructor <;> linarith [hbounds.1,hbounds.2.1,CoreAngleEndpoint.diagonal_bounds.1]

end SquaresInCircles.Eight.SecondWord.MixedCorner
end
end
end

section
/-!
## Three whole-arc affine bounds for the actual L label

One tangent parabola controls the initial concave arc. A concave
derivative then reduces the remaining interval to its two endpoints.
The references are fixed rational points of the unchanged Q0 circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedLEnvelopes
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma half_references : LLabel.d1 (1/2)<(5/8:ℝ) ∧ LLabel.d2 (1/2)< -(3/100:ℝ) := by
  have h1 := LLabel.first_chart_reference (outer_domain L_half_mem)
    (l := (170751281107931/100000000000000:ℝ))
    (u := (170751281107932/100000000000000:ℝ))
    (dlo := (3/5:ℝ)) (dhi := (5/8:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  have h2 := LLabel.second_chart_reference (outer_domain L_half_mem)
    (l := (170751281107931/100000000000000:ℝ))
    (u := (170751281107932/100000000000000:ℝ))
    (dlo := (-1:ℝ)) (dhi := (-(3/100):ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  exact ⟨h1.2,h2.2⟩

lemma affine_half {r q c δ k B : ℝ} (hr : r∈Icc (0:ℝ) (1/2))
    (hvalue : L r<c) (hslope : |LLabel.d1 r-q|<δ) (_hδ : 0≤δ)
    (hgap : c-q*r+δ^2/(3/50)≤k) (hB : B∈Icc (0:ℝ) (1/2)) : L B<k+q*B := by
  have hdom {y : ℝ} (hy : y∈Icc (0:ℝ) (1/2)) : y∈Icc 0 outerDiagonal :=
    ⟨hy.1,hy.2.trans L_half_mem.2⟩
  have ht := curvature_tangent (f := fun y => q*y-L y) (d := fun y => q-LLabel.d1 y)
    (dd := fun y => -LLabel.d2 y) (κ := (3/100:ℝ)) hB hr
    (fun y hy => by simpa [L] using LLabel.affine_difference_hasDerivAt q (outer_domain (hdom hy)))
    (fun y hy => (LLabel.d1_hasDerivAt (outer_domain (hdom hy))).const_sub q)
    (fun y hy => by
      have hm := L_second_monotone (hdom hy) L_half_mem hy.2
      linarith [half_references.2])
  have hd := abs_lt.mp hslope
  have hprod := mul_pos (show 0<δ+(LLabel.d1 r-q) by linarith [hd.1])
    (show 0<δ-(LLabel.d1 r-q) by linarith [hd.2])
  have hs := sq_nonneg ((3/100)*(B-r)+(q-LLabel.d1 r))
  nlinarith

lemma affine_continue {q k t B : ℝ} (ht : t∈Icc (1/2:ℝ) outerDiagonal)
    (hhalf : ∀y∈Icc (0:ℝ) (1/2),L y<k+q*y)
    (hslope : LLabel.d1 (1/2)<q) (hend : L t<k+q*t)
    (hB : B∈Icc (0:ℝ) t) : L B<k+q*B := by
  by_cases he : B≤1/2
  · exact hhalf B ⟨hB.1,he⟩
  · have hdom {y : ℝ} (hy : y∈Icc (1/2:ℝ) t) : y∈Icc 0 outerDiagonal :=
      ⟨by linarith [hy.1],hy.2.trans ht.2⟩
    have hm := MinimumCalculus.endpoint_minimum_of_third_nonpos
      (f := fun y => q*y-L y) (d := fun y => q-LLabel.d1 y)
      (dd := fun y => -LLabel.d2 y) (ddd := fun y => -LLabel.d3 y)
      (show B∈Icc (1/2:ℝ) t from ⟨by linarith,hB.2⟩)
      (fun y hy => by simpa [L] using LLabel.affine_difference_hasDerivAt q (outer_domain (hdom hy)))
      (fun y hy => (LLabel.d1_hasDerivAt (outer_domain (hdom hy))).const_sub q)
      (fun y hy => (LLabel.d2_hasDerivAt (outer_domain (hdom hy))).neg)
      (fun y hy => neg_nonpos.mpr (L_third_positive (hdom hy)).le)
      (by linarith)
    have hl := hhalf (1/2) (by norm_num)
    have hmin : -k< min (q*(1/2)-L (1/2)) (q*t-L t) := lt_min (by linarith) (by linarith)
    linarith

lemma reference_3424 : L (214/625)<(346979939/1000000000:ℝ) ∧
    |LLabel.d1 (214/625)-(69/100)|<(7/500000:ℝ) := by
  have hb := Asymmetric.rational_outer_mem (show (214/625:ℝ)∈Icc 0 (899/1000) by norm_num)
  have hr := shifted_chart_reference (outer_domain hb)
    (l := (1790520103210/1000000000000:ℝ)) (u := (1790520103211/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hd := LLabel.first_chart_reference (outer_domain hb)
    (l := (1790520103210/1000000000000:ℝ)) (u := (1790520103211/1000000000000:ℝ))
    (dlo := (69/100:ℝ)) (dhi := (345007/500000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  constructor
  · dsimp [L,RoleLabel.outer,RoleLabel.eval,LLabel,U] at *
    nlinarith [hr.1]
  · rw [abs_lt]
    constructor <;> linarith [hd.1,hd.2]

lemma reference_794 : L (397/500)<(111/1000:ℝ)+(69/100)*(397/500) := by
  have hb := Asymmetric.rational_outer_mem (show (397/500:ℝ)∈Icc 0 (899/1000) by norm_num)
  have hr := shifted_chart_reference (outer_domain hb)
    (l := (1497051769311/1000000000000:ℝ)) (u := (1497051769312/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  dsimp [L,RoleLabel.outer,RoleLabel.eval,LLabel,U] at *
  nlinarith [hr.1]

theorem late_transverse {B : ℝ} (hB : B∈Icc (0:ℝ) (397/500)) :
    L B<(111/1000:ℝ)+(69/100)*B := by
  apply affine_continue
    (show (397/500:ℝ)∈Icc (1/2:ℝ) outerDiagonal from
      ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num : (397/500:ℝ)∈Icc 0 (899/1000))).2⟩)
    (fun y hy => affine_half (r := (214/625:ℝ)) (c := (346979939/1000000000:ℝ))
      (δ := (7/500000:ℝ)) (by norm_num) reference_3424.1 reference_3424.2
      (by norm_num) (by norm_num) hy)
    (by linarith [half_references.1]) reference_794 hB

lemma reference_42 : L (21/50)<(797087493/2000000000:ℝ) ∧
    |LLabel.d1 (21/50)-(12867969/20000000)|<(1/1000000000:ℝ) := by
  have hb := Asymmetric.rational_outer_mem (show (21/50:ℝ)∈Icc 0 (899/1000) by norm_num)
  have hr := shifted_chart_reference (outer_domain hb)
    (l := (175191323986092/100000000000000:ℝ)) (u := (175191323986093/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hd := LLabel.first_chart_reference (outer_domain hb)
    (l := (175191323986092/100000000000000:ℝ)) (u := (175191323986093/100000000000000:ℝ))
    (dlo := (643398449/1000000000:ℝ)) (dhi := (12867969/20000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  constructor
  · dsimp [L,RoleLabel.outer,RoleLabel.eval,LLabel,U] at *
    nlinarith [hr.1]
  · rw [abs_lt]
    constructor <;> linarith [hd.1,hd.2]

lemma reference_65 : L (13/20)<(128316398/1000000000:ℝ)+(12867969/20000000)*(13/20) := by
  have hb := Asymmetric.rational_outer_mem (show (13/20:ℝ)∈Icc 0 (899/1000) by norm_num)
  have hr := shifted_chart_reference (outer_domain hb)
    (l := (1610310529059/1000000000000:ℝ)) (u := (1610310529060/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  dsimp [L,RoleLabel.outer,RoleLabel.eval,LLabel,U] at *
  nlinarith [hr.1]

theorem primary {B : ℝ} (hB : B∈Icc (0:ℝ) (13/20)) :
    L B<(128316398/1000000000:ℝ)+(12867969/20000000)*B := by
  apply affine_continue
    (show (13/20:ℝ)∈Icc (1/2:ℝ) outerDiagonal from
      ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num : (13/20:ℝ)∈Icc 0 (899/1000))).2⟩)
    (fun y hy => affine_half (r := (21/50:ℝ)) (c := (797087493/2000000000:ℝ))
      (δ := (1/1000000000:ℝ)) (by norm_num) reference_42.1 reference_42.2
      (by norm_num) (by norm_num) hy)
    (by linarith [half_references.1]) reference_65 hB

end SquaresInCircles.Eight.SecondWord.MixedLEnvelopes
end
end
end

section
/-!
## Whole-half concavity of mixed transverse circle supports

The support slope may exceed the source label slope.  This freedom is
useful at an early contact: the remaining nonnegative source coordinate
pays for the stronger separator.  Both scalar supports below retain
their unsquared circular norm on a complete closed quarter half.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTransverseSupport
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig)

def lowerN (g p φ : ℝ) : ℝ := CircularNorm.norm (g^2+p^2) (-2*g*p) 0 φ
def lower (g p C φ : ℝ) : ℝ := φ+C+(g+p)/2+g*Real.sin φ-CommonQuarter.radius*lowerN g p φ
def lowerD (g p φ : ℝ) : ℝ := 1+g*Real.cos φ-
  CommonQuarter.radius*CircularNorm.d1 (g^2+p^2) (-2*g*p) 0 φ
def lowerDD (g p φ : ℝ) : ℝ := -g*Real.sin φ-
  CommonQuarter.radius*CircularNorm.d2 (g^2+p^2) (-2*g*p) 0 φ
def upperN (g p x : ℝ) : ℝ := CircularNorm.norm (g^2+p^2) 0 (2*g*p) x
def upper (g p C x : ℝ) : ℝ := Real.pi/2+x+C+(g+p)/2+
  g*(Real.sin x+Real.cos x)-CommonQuarter.radius*upperN g p x
def upperD (g p x : ℝ) : ℝ := 1+g*(Real.cos x-Real.sin x)-
  CommonQuarter.radius*CircularNorm.d1 (g^2+p^2) 0 (2*g*p) x
def upperDD (g p x : ℝ) : ℝ := -g*(Real.sin x+Real.cos x)-
  CommonQuarter.radius*CircularNorm.d2 (g^2+p^2) 0 (2*g*p) x

lemma lower_domain {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (φ : ℝ) :
    0<CircularNorm.energy (g^2+p^2) (-2*g*p) 0 φ := by
  have hdiff : 0<g-p := by linarith
  have hgap := sq_pos_of_pos hdiff
  have hh := mul_nonneg (mul_nonneg hg.le hp) (sub_nonneg.mpr (Real.cos_le_one φ))
  dsimp [CircularNorm.energy]
  nlinarith

lemma upper_domain {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (x : ℝ) :
    0<CircularNorm.energy (g^2+p^2) 0 (2*g*p) x := by
  have hdiff : 0<g-p := by linarith
  have hgap := sq_pos_of_pos hdiff
  have hh := mul_nonneg (mul_nonneg hg.le hp) (show 0≤1+Real.sin x by linarith [Real.neg_one_le_sin x])
  dsimp [CircularNorm.energy]
  nlinarith

lemma lower_sq {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (φ : ℝ) :
    (lowerN g p φ)^2=g^2+p^2-2*g*p*Real.cos φ := by
  have h := CircularNorm.norm_sq (lower_domain hg hp hpg φ).le
  simp only [lowerN]
  rw [h]
  simp only [CircularNorm.energy]
  ring

lemma upper_sq {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (x : ℝ) :
    (upperN g p x)^2=g^2+p^2+2*g*p*Real.sin x := by
  simpa [upperN,CircularNorm.energy] using CircularNorm.norm_sq (upper_domain hg hp hpg x).le

lemma lower_hasDerivAt {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (C φ : ℝ) :
    HasDerivAt (lower g p C) (lowerD g p φ) φ := by
  have h1 : HasDerivAt (fun y => y+C+(g+p)/2) 1 φ :=
    ((hasDerivAt_id' φ).add_const C).add_const ((g+p)/2)
  have h2 : HasDerivAt (fun y => g*Real.sin y) (g*Real.cos φ) φ :=
    (Real.hasDerivAt_sin φ).const_mul g
  have h3 : HasDerivAt (fun y => CommonQuarter.radius*lowerN g p y)
      (CommonQuarter.radius*CircularNorm.d1 (g^2+p^2) (-2*g*p) 0 φ) φ :=
    (CircularNorm.norm_hasDerivAt (lower_domain hg hp hpg φ)).const_mul CommonQuarter.radius
  refine ((h1.add h2).sub h3).congr_deriv ?_
  unfold lowerD
  ring

lemma lowerD_hasDerivAt {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (φ : ℝ) :
    HasDerivAt (lowerD g p) (lowerDD g p φ) φ := by
  have h1 : HasDerivAt (fun y => 1+g*Real.cos y) (g*(-Real.sin φ)) φ :=
    ((Real.hasDerivAt_cos φ).const_mul g).const_add 1
  have h2 : HasDerivAt (fun y => CommonQuarter.radius*CircularNorm.d1 (g^2+p^2) (-2*g*p) 0 y)
      (CommonQuarter.radius*CircularNorm.d2 (g^2+p^2) (-2*g*p) 0 φ) φ :=
    (CircularNorm.d1_hasDerivAt (lower_domain hg hp hpg φ)).const_mul CommonQuarter.radius
  refine (h1.sub h2).congr_deriv ?_
  simp only [lowerDD]
  ring

lemma upper_hasDerivAt {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (C x : ℝ) :
    HasDerivAt (upper g p C) (upperD g p x) x := by
  have h1 : HasDerivAt (fun y => Real.pi/2+y+C+(g+p)/2) 1 x :=
    (((hasDerivAt_id' x).const_add (Real.pi/2)).add_const C).add_const ((g+p)/2)
  have h2 : HasDerivAt (fun y => g*(Real.sin y+Real.cos y)) (g*(Real.cos x+(-Real.sin x))) x :=
    ((Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)).const_mul g
  have h3 : HasDerivAt (fun y => CommonQuarter.radius*upperN g p y)
      (CommonQuarter.radius*CircularNorm.d1 (g^2+p^2) 0 (2*g*p) x) x :=
    (CircularNorm.norm_hasDerivAt (upper_domain hg hp hpg x)).const_mul CommonQuarter.radius
  refine ((h1.add h2).sub h3).congr_deriv ?_
  simp only [upperD]
  ring

lemma upperD_hasDerivAt {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (x : ℝ) :
    HasDerivAt (upperD g p) (upperDD g p x) x := by
  have h1 : HasDerivAt (fun y => 1+g*(Real.cos y-Real.sin y)) (g*(-Real.sin x-Real.cos x)) x :=
    (((Real.hasDerivAt_cos x).sub (Real.hasDerivAt_sin x)).const_mul g).const_add 1
  have h2 : HasDerivAt (fun y => CommonQuarter.radius*CircularNorm.d1 (g^2+p^2) 0 (2*g*p) y)
      (CommonQuarter.radius*CircularNorm.d2 (g^2+p^2) 0 (2*g*p) x) x :=
    (CircularNorm.d1_hasDerivAt (upper_domain hg hp hpg x)).const_mul CommonQuarter.radius
  refine (h1.sub h2).congr_deriv ?_
  simp only [upperDD]
  ring

lemma lower_curvature {g p φ : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g)
    (hφ : Lower φ) : lowerDD g p φ<0 := by
  have ht := lower_trig hφ
  have hn := lower_sq hg hp hpg φ
  have hNpos : 0<lowerN g p φ := CircularNorm.norm_pos (lower_domain hg hp hpg φ)
  have hp2 := pow_le_pow_left₀ hp hpg 2
  have hcos := mul_nonneg (mul_nonneg hg.le hp) ht.2.2.1
  have hN : lowerN g p φ<(13/10)*g := by nlinarith
  have hc := CircularNorm.curvature_lower (lower_domain hg hp hpg φ)
    (show (-2*g*p)^2+(0:ℝ)^2≤(g^2+p^2)^2 by nlinarith [sq_nonneg (g^2-p^2)])
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hcurv := mul_le_mul_of_nonneg_left hc hR.le
  have hRN := (mul_lt_mul_of_pos_left hN hR).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 (by positivity : 0<(13/10)*g))
  have hgs := mul_le_mul_of_nonneg_left ht.1.le hg.le
  change CommonQuarter.radius*(-lowerN g p φ/4)≤CommonQuarter.radius*CircularNorm.d2 (g^2+p^2) (-2*g*p) 0 φ at hcurv
  dsimp [lowerDD]
  nlinarith

lemma upper_curvature {g p x : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g)
    (hx : x∈Icc (0:ℝ) (7/10)) : upperDD g p x<0 := by
  have ht := positive_trig hx
  have hn := upper_sq hg hp hpg x
  have hNpos : 0<upperN g p x := CircularNorm.norm_pos (upper_domain hg hp hpg x)
  have hsin := mul_le_mul_of_nonneg_left (Real.sin_le_one x) (mul_nonneg hg.le hp)
  have hN : upperN g p x≤g+p := by nlinarith
  have hc := CircularNorm.curvature_lower (upper_domain hg hp hpg x)
    (show (0:ℝ)^2+(2*g*p)^2≤(g^2+p^2)^2 by nlinarith [sq_nonneg (g^2-p^2)])
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hcurv := mul_le_mul_of_nonneg_left hc hR.le
  have hRN := (mul_le_mul_of_nonneg_left (hN.trans (by linarith : g+p≤(9/5)*g)) hR.le).trans_lt
    (mul_lt_mul_of_pos_right radius_bounds.2 (by positivity : 0<(9/5)*g))
  have hgs := mul_le_mul_of_nonneg_left ht.2.2.2.2.2 hg.le
  change CommonQuarter.radius*(-upperN g p x/4)≤CommonQuarter.radius*CircularNorm.d2 (g^2+p^2) 0 (2*g*p) x at hcurv
  dsimp [upperDD]
  nlinarith

theorem lower_concave {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (C : ℝ) :
    ConcaveOn ℝ (Icc lowerAngle (Real.pi/2)) (lower g p C) :=
  concave_of_deriv2 (fun x _ => lower_hasDerivAt hg hp hpg C x)
    (fun x _ => lowerD_hasDerivAt hg hp hpg x)
    (fun _ hx => (lower_curvature hg hp hpg hx).le)

theorem upper_concave {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(4/5)*g) (C : ℝ) :
    ConcaveOn ℝ (Icc (0:ℝ) (7/10)) (upper g p C) :=
  concave_of_deriv2 (fun x _ => upper_hasDerivAt hg hp hpg C x)
    (fun x _ => upperD_hasDerivAt hg hp hpg x)
    (fun _ hx => (upper_curvature hg hp hpg hx).le)

end SquaresInCircles.Eight.SecondWord.MixedTransverseSupport
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTransverseSupport
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig)

lemma lower_domain_wide {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(19/20)*g) (φ : ℝ) :
    0<CircularNorm.energy (g^2+p^2) (-2*g*p) 0 φ := by
  have hdiff : 0<g-p := by linarith
  have hgap := sq_pos_of_pos hdiff
  have hh := mul_nonneg (mul_nonneg hg.le hp) (sub_nonneg.mpr (Real.cos_le_one φ))
  dsimp [CircularNorm.energy]
  nlinarith

lemma lower_sq_wide {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(19/20)*g) (φ : ℝ) :
    (lowerN g p φ)^2=g^2+p^2-2*g*p*Real.cos φ := by
  have h := CircularNorm.norm_sq (lower_domain_wide hg hp hpg φ).le
  simp only [lowerN]
  rw [h]
  simp only [CircularNorm.energy]
  ring

lemma lower_hasDerivAt_wide {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(19/20)*g) (C φ : ℝ) :
    HasDerivAt (lower g p C) (lowerD g p φ) φ := by
  have h1 : HasDerivAt (fun y => y+C+(g+p)/2) 1 φ :=
    ((hasDerivAt_id' φ).add_const C).add_const ((g+p)/2)
  have h2 : HasDerivAt (fun y => g*Real.sin y) (g*Real.cos φ) φ :=
    (Real.hasDerivAt_sin φ).const_mul g
  have h3 : HasDerivAt (fun y => CommonQuarter.radius*lowerN g p y)
      (CommonQuarter.radius*CircularNorm.d1 (g^2+p^2) (-2*g*p) 0 φ) φ :=
    (CircularNorm.norm_hasDerivAt (lower_domain_wide hg hp hpg φ)).const_mul CommonQuarter.radius
  refine ((h1.add h2).sub h3).congr_deriv ?_
  unfold lowerD
  ring

lemma lowerD_hasDerivAt_wide {g p : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(19/20)*g) (φ : ℝ) :
    HasDerivAt (lowerD g p) (lowerDD g p φ) φ := by
  have h1 : HasDerivAt (fun y => 1+g*Real.cos y) (g*(-Real.sin φ)) φ :=
    ((Real.hasDerivAt_cos φ).const_mul g).const_add 1
  have h2 : HasDerivAt (fun y => CommonQuarter.radius*CircularNorm.d1 (g^2+p^2) (-2*g*p) 0 y)
      (CommonQuarter.radius*CircularNorm.d2 (g^2+p^2) (-2*g*p) 0 φ) φ :=
    (CircularNorm.d1_hasDerivAt (lower_domain_wide hg hp hpg φ)).const_mul CommonQuarter.radius
  refine (h1.sub h2).congr_deriv ?_
  unfold lowerDD
  ring

lemma lower_curvature_wide {g p φ : ℝ} (hg : 0<g) (hp : 0≤p) (hpg : p≤(19/20)*g)
    (hφ : Lower φ) : lowerDD g p φ<0 := by
  have ht := lower_trig hφ
  have hn := lower_sq_wide hg hp hpg φ
  have hNpos : 0<lowerN g p φ := CircularNorm.norm_pos (lower_domain_wide hg hp hpg φ)
  have hp2 := pow_le_pow_left₀ hp hpg 2
  have hcos := mul_nonneg (mul_nonneg hg.le hp) ht.2.2.1
  have hN : lowerN g p φ<(7/5)*g := by nlinarith
  have hc := CircularNorm.curvature_lower (lower_domain_wide hg hp hpg φ)
    (show (-2*g*p)^2+(0:ℝ)^2≤(g^2+p^2)^2 by nlinarith [sq_nonneg (g^2-p^2)])
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hcurv := mul_le_mul_of_nonneg_left hc hR.le
  have hRN := (mul_lt_mul_of_pos_left hN hR).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 (by positivity : 0<(7/5)*g))
  have hgs := mul_le_mul_of_nonneg_left ht.1.le hg.le
  change CommonQuarter.radius*(-lowerN g p φ/4)≤CommonQuarter.radius*CircularNorm.d2 (g^2+p^2) (-2*g*p) 0 φ at hcurv
  dsimp [lowerDD]
  nlinarith

end SquaresInCircles.Eight.SecondWord.MixedTransverseSupport
end
end
end
