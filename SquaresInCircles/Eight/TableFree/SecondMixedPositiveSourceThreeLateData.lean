module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveSourceThreePrimaryData
public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveSourceThreeEarlyReferences

/-!
# One affine dividing curve for every late transverse angle

The line is determined by the proved affine L envelope and the exact
required cost. It remains inside the original target circle domain.
The source coordinate and the target derivative are differentiated
along this whole curve. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource.Late
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open PositiveThree (Lower lowerAngle lower_trig)

def angles : Set ℝ := Icc (13/10) (Real.pi/2)
def v : ℝ := 100/69
def cut (φ : ℝ) : ℝ := (φ-51157/50000)/(69/100)
def f (φ : ℝ) : ℝ := source (cut φ) φ
def f1 (φ : ℝ) : ℝ :=
  (v*ratio (cut φ)-W (cut φ))*Real.sin φ+(1-U (cut φ)+v)*Real.cos φ
def f2 (φ : ℝ) : ℝ :=
  (v^2*ratioD (cut φ)-1+U (cut φ)-2*v)*Real.sin φ+
    (2*v*ratio (cut φ)-W (cut φ))*Real.cos φ
def f3 (φ : ℝ) : ℝ :=
  (v^3*ratioDD (cut φ)-3*v*ratio (cut φ)+W (cut φ))*Real.sin φ+
    (3*v^2*ratioD (cut φ)-1+U (cut φ)-3*v)*Real.cos φ
def D (φ : ℝ) : ℝ := FB (cut φ) φ
def D1 (φ : ℝ) : ℝ := g*(v*ratioD (cut φ)*Real.sin φ+ratio (cut φ)*Real.cos φ-Real.sin φ)-
  v*LLabel.d2 (cut φ)
def D2 (φ : ℝ) : ℝ :=
  g*((v^2*ratioDD (cut φ)-ratio (cut φ))*Real.sin φ+
    2*v*ratioD (cut φ)*Real.cos φ-Real.cos φ)-v^2*LLabel.d3 (cut φ)

lemma lower_mem {φ : ℝ} (hφ : φ∈angles) : Lower φ :=
  ⟨by dsimp [lowerAngle]; linarith [hφ.1,pi_hand_enclosure.2],hφ.2⟩

lemma cut_bounds {φ : ℝ} (hφ : φ∈angles) :
    (2/5:ℝ)<cut φ ∧ cut φ<(397/500:ℝ) := by
  dsimp [cut]
  constructor <;> linarith [hφ.1,hφ.2,pi_hand_enclosure.2]

lemma cut_domain {φ : ℝ} (hφ : φ∈angles) : cut φ∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem ⟨by linarith [(cut_bounds hφ).1],by linarith [(cut_bounds hφ).2]⟩

lemma trig {φ : ℝ} (hφ : φ∈angles) :
    0<Real.sin φ ∧ Real.sin φ≤1 ∧ 0≤Real.cos φ ∧ Real.cos φ≤67/250 := by
  have ht := lower_trig (lower_mem hφ)
  have hi : Lower (13/10:ℝ) := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],
    by linarith [pi_hand_enclosure.1]⟩
  have hm := PositiveThree.lower_cos_antitone hi (lower_mem hφ) hφ.1
  have hc := HighOrderTaylor.cos_le_C12 (x := (13/10:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.C12,cos10,cos8] at hc
  exact ⟨by linarith [ht.1],ht.2.1,ht.2.2.1,by linarith⟩

lemma shifted_bounds {φ : ℝ} (hφ : φ∈angles) :
    (1497/1000:ℝ)<U (cut φ) ∧ U (cut φ)<(1763/1000:ℝ) ∧
    (357/500:ℝ)<ratioD (cut φ) := by
  have hc := UW_circle (outer_domain (cut_domain hφ))
  have hp := U_positive (outer_domain (cut_domain hφ))
  have hb := cut_bounds hφ
  have hw : (9/10:ℝ)<W (cut φ) ∧ W (cut φ)<647/500 := by dsimp [W]; constructor <;> linarith
  have hwL := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤9/10) hw.1.le 2
  have hwU := pow_le_pow_left₀ (by linarith [hw.1] : 0≤W (cut φ)) hw.2.le 2
  have hlo : (1497/1000:ℝ)<U (cut φ) := by norm_num [Q0] at hc; nlinarith
  have hhi : U (cut φ)<(1763/1000:ℝ) := by norm_num [Q0] at hc; nlinarith
  have h3 := pow_le_pow_left₀ hp.le hhi.le 3
  have hrd : (357/500:ℝ)<ratioD (cut φ) := by
    change (357/500:ℝ)<Q0/(U (cut φ))^3
    apply (lt_div_iff₀ (pow_pos hp 3)).2
    norm_num [Q0]
    nlinarith
  exact ⟨hlo,hhi,hrd⟩

lemma cut_hasDerivAt (φ : ℝ) : HasDerivAt cut v φ := by
  convert ((hasDerivAt_id φ).sub_const (51157/50000)).div_const (69/100) using 1 <;>
    dsimp [cut,v] <;> ring

lemma U_hasDerivAt {φ : ℝ} (hφ : φ∈angles) :
    HasDerivAt (fun θ => U (cut θ)) (-v*ratio (cut φ)) φ := by
  convert (((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain (cut_domain hφ))).add_const
    (1/2)).comp φ (cut_hasDerivAt φ)) using 1 <;> dsimp [U] <;> ring

lemma W_hasDerivAt (φ : ℝ) : HasDerivAt (fun θ => W (cut θ)) v φ :=
  (cut_hasDerivAt φ).add_const (1/2)

lemma ratio_hasDerivAt {φ : ℝ} (hφ : φ∈angles) :
    HasDerivAt (fun θ => ratio (cut θ)) (v*ratioD (cut φ)) φ := by
  convert (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain (cut_domain hφ))).comp φ
    (cut_hasDerivAt φ) using 1 <;> ring

lemma ratioD_hasDerivAt {φ : ℝ} (hφ : φ∈angles) :
    HasDerivAt (fun θ => ratioD (cut θ)) (v*ratioDD (cut φ)) φ := by
  convert (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain (cut_domain hφ))).comp φ
    (cut_hasDerivAt φ) using 1 <;> ring

lemma f_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt f (f1 φ) φ := by
  have hd := ((((U_hasDerivAt hφ).const_sub 1).mul (Real.hasDerivAt_sin φ)).add
    ((W_hasDerivAt φ).mul (Real.hasDerivAt_cos φ))).add_const (1/2)
  convert hd using 1 <;> dsimp [f,source,f1,U,W] <;> ring

lemma f1_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt f1 (f2 φ) φ := by
  convert ((((ratio_hasDerivAt hφ).const_mul v).sub (W_hasDerivAt φ)).mul
    (Real.hasDerivAt_sin φ)).add
      (((U_hasDerivAt hφ).const_sub (1+v)).mul (Real.hasDerivAt_cos φ)) using 1 <;>
    dsimp [f1,f2] <;> ring

lemma f2_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt f2 (f3 φ) φ := by
  convert (((((ratioD_hasDerivAt hφ).const_mul (v^2)).add (U_hasDerivAt hφ)).sub_const (1+2*v)).mul
    (Real.hasDerivAt_sin φ)).add
      ((((ratio_hasDerivAt hφ).const_mul (2*v)).sub (W_hasDerivAt φ)).mul (Real.hasDerivAt_cos φ)) using 1 <;>
    dsimp [f2,f3] <;> ring

lemma D_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt D (D1 φ) φ := by
  convert (((((ratio_hasDerivAt hφ).mul (Real.hasDerivAt_sin φ)).add
    (Real.hasDerivAt_cos φ)).const_mul g).sub
      ((LLabel.d1_hasDerivAt (outer_domain (cut_domain hφ))).comp φ (cut_hasDerivAt φ))) using 1 <;>
    dsimp [D,FB,D1] <;> ring

lemma D1_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt D1 (D2 φ) φ := by
  convert (((((((ratioD_hasDerivAt hφ).const_mul v).mul (Real.hasDerivAt_sin φ)).add
    ((ratio_hasDerivAt hφ).mul (Real.hasDerivAt_cos φ))).sub (Real.hasDerivAt_sin φ)).const_mul g).sub
      (((LLabel.d2_hasDerivAt (outer_domain (cut_domain hφ))).comp φ (cut_hasDerivAt φ)).const_mul v)) using 1 <;>
    dsimp [D1,D2] <;> ring

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource.Late
