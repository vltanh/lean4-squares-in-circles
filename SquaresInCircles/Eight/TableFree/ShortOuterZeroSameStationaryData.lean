module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroSameData

/-!
# The exact coupled stationary coordinate of a favorable zero contact

Uncompiled transcription of equations (13)--(15) in the written proof.
At an angular stationary point, the original circle identity determines
the target height from the unchanged source coordinate. The second
angular derivative and the target derivative are then literal functions
of that same coordinate, not independent relaxed variables.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Same.Stationary
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open SecondWord (U W outer_domain outer_zero_mem UW_circle U_positive)

def z (b : ℝ) : ℝ := b-1/2
def mass (r : Row) (b : ℝ) : ℝ := (z b)^2+1/(l r b)^2
def height (r : Row) (b : ℝ) : ℝ := (Q0+1-mass r b)/2
def G (r : Row) (b : ℝ) : ℝ := z b-alpha r b/(l r b)^3
def GD (r : Row) (b : ℝ) : ℝ :=
  1-3*(-p r)*Q0*(q r*W b+p r*U b)/((U b)^5*(l r b)^4)
def targetRatio (u : ℝ) : ℝ := Real.sqrt (Q0-u^2)/u
def f (u : ℝ) : ℝ := (Q0-u)/(u*(Q0+1-2*u))
def stationaryTarget (r : Row) (b : ℝ) : ℝ :=
  f (height r b)+targetRatio (height r b)*(P r+z b*l r b/mass r b)-t r

def sourceDomain : Set ℝ := Icc (293/1000) outerDiagonal

lemma source_outer {b : ℝ} (hb : b∈sourceDomain) : b∈Icc 0 outerDiagonal :=
  ⟨by linarith [hb.1],hb.2⟩

lemma mass_positive (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : 0< mass r b := by
  have hl := l_positive r hb
  dsimp [mass]
  positivity

lemma mass_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (mass r) (2*G r b) b := by
  have hl := l_positive r hb
  have hd := (((hasDerivAt_id b).sub_const (1/2)).pow 2).add
    ((hasDerivAt_const b (1:ℝ)).div ((l_hasDerivAt r hb).pow 2)
      (pow_ne_zero 2 hl.ne'))
  convert hd using 1
  · rfl
  · dsimp [G,z]
    field_simp [hl.ne']
    ring

lemma height_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (height r) (-G r b) b := by
  exact (((mass_hasDerivAt r hb).const_sub (Q0+1)).div_const 2).congr_deriv (by ring)

lemma G_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (G r) (GD r b) b := by
  have hl := l_positive r hb
  have hu := U_positive (outer_domain hb)
  have hc := UW_circle (outer_domain hb)
  have hd := ((hasDerivAt_id b).sub_const (1/2)).sub
    ((alpha_hasDerivAt r hb).div ((l_hasDerivAt r hb).pow 3) (pow_ne_zero 3 hl.ne'))
  refine hd.congr_deriv ?_
  have hD : ratioD b=Q0/(U b)^3 := rfl
  have hDD : ratioDD b=3*Q0*(W b)/(U b)^5 := rfl
  have hR : ratio b=W b/U b := rfl
  have hL : l r b*U b=q r*U b-p r*W b := by
    simp only [l,hR]
    field_simp
  simp only [Pi.pow_apply,GD,alpha,hD,hDD,show (3:ℕ)-1=2 from rfl,Nat.cast_ofNat]
  rw [←hc]
  field_simp
  linear_combination (3*p r*(U b^2+W b^2)*W b)*hL

lemma angular_speed {B x : ℝ} (r : Row) (hd : Domain B x)
    (hstat : angleFirst r B x=0) : speed B x=1/l r (contact B x) := by
  have hl := l_positive r hd.2.2
  dsimp [angleFirst] at hstat
  apply (eq_div_iff hl.ne').2
  nlinarith

lemma actual_height {B x : ℝ} (r : Row) (hd : Domain B x)
    (hstat : angleFirst r B x=0) : height r (contact B x)=U B := by
  have hsp : SecondWord.SameZero.v B x=1/l r (SecondWord.SameZero.b B x) :=
    angular_speed r hd hstat
  have hn := SecondWord.SameZero.norm_identity hd.1 x
  rw [hsp,div_pow,one_pow] at hn
  simp only [height,mass,z,SecondWord.NegativeTwo.Inverse.q] at hn ⊢
  linarith

lemma actual_ratio {B x : ℝ} (r : Row) (hd : Domain B x)
    (hstat : angleFirst r B x=0) : targetRatio (height r (contact B x))=ratio B := by
  rw [actual_height r hd hstat]
  have hc := UW_circle (outer_domain hd.1)
  have hw : 0≤W B := by dsimp [W]; linarith [hd.1.1]
  have he : Q0-(U B)^2=(W B)^2 := by linarith
  rw [targetRatio,he,Real.sqrt_sq hw]
  rfl

lemma actual_second {B x : ℝ} (r : Row) (hd : Domain B x)
    (hstat : angleFirst r B x=0) :
    angleSecond r B x= -l r (contact B x)*G r (contact B x) := by
  have hl := l_positive r hd.2.2
  rw [angleSecond,angular_speed r hd hstat]
  dsimp [G,z]
  field_simp [hl.ne']
  ring

lemma actual_target {B x : ℝ} (r : Row) (hd : Domain B x)
    (hstat : angleFirst r B x=0) : targetFirst r B x=stationaryTarget r (contact B x) := by
  have hl := l_positive r hd.2.2
  have hu := U_positive (outer_domain hd.1)
  have hq : 0<SecondWord.NegativeTwo.Inverse.q (U B) := by
    linarith [SecondWord.NegativeTwo.Inverse.actual_q_positive hd.1]
  have hsp : SecondWord.SameZero.v B x=1/l r (SecondWord.SameZero.b B x) :=
    angular_speed r hd hstat
  have hmass : mass r (contact B x)=SecondWord.NegativeTwo.Inverse.q (U B) := by
    have hn := SecondWord.SameZero.norm_identity hd.1 x
    rw [hsp,div_pow,one_pow] at hn
    simp only [mass,z]
    linarith
  have hproj := SecondWord.SameZero.projection_identity hd.1 hd.2.1
  rw [hsp] at hproj
  have e1 : SecondWord.SameZero.k B x/(1/l r (SecondWord.SameZero.b B x))=
      SecondWord.SameZero.k B x*l r (SecondWord.SameZero.b B x) := by
    field_simp
  have e2 : W B*(SecondWord.SameZero.b B x-1/2)/
      (U B*SecondWord.NegativeTwo.Inverse.q (U B)*(1/l r (SecondWord.SameZero.b B x)))=
      W B*(SecondWord.SameZero.b B x-1/2)*l r (SecondWord.SameZero.b B x)/
        (U B*SecondWord.NegativeTwo.Inverse.q (U B)) := by
    field_simp
  rw [e1,e2] at hproj
  rw [stationaryTarget,actual_ratio r hd hstat,actual_height r hd hstat,hmass]
  have hf : f (U B)=SecondWord.NegativeTwo.Inverse.factor (U B) := rfl
  rw [hf]
  simp only [targetFirst,z]
  rw [show ratio B=W B/U B from rfl]
  linear_combination hproj

lemma f_hasDerivAt {u : ℝ} (hu : u≠0) (hq : Q0+1-2*u≠0) :
    HasDerivAt f
      ((4*Q0*u-2*u^2-Q0*(Q0+1))/(u^2*(Q0+1-2*u)^2)) u := by
  have hd := ((hasDerivAt_id' u).const_sub Q0).div
    ((hasDerivAt_id' u).mul (((hasDerivAt_id' u).const_mul 2).const_sub (Q0+1)))
    (mul_ne_zero hu hq)
  refine hd.congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero hu hq))
    (mul_ne_zero (pow_ne_zero 2 hu) (pow_ne_zero 2 hq))]
  ring

lemma f_monotone : MonotoneOn f (Icc (1747/1000:ℝ) (951/500)) := by
  have hpos {u : ℝ} (hu : u∈Icc (1747/1000:ℝ) (951/500)) :
      0<u ∧ 0<Q0+1-2*u := by
    norm_num [Q0]
    constructor <;> linarith [hu.1,hu.2]
  apply monoOn_of_hasDeriv_nonneg
    (fun u hu => (f_hasDerivAt (hpos hu).1.ne' (hpos hu).2.ne').continuousAt.continuousWithinAt)
    (fun u hu => f_hasDerivAt (hpos (Ioo_subset_Icc_self hu)).1.ne'
      (hpos (Ioo_subset_Icc_self hu)).2.ne')
  intro u hu
  have hp := mul_nonneg (show 0≤u-1747/1000 by linarith [hu.1])
    (show 0≤4*Q0-2*(u+1747/1000) by norm_num [Q0]; linarith [hu.2])
  have hn : 0≤4*Q0*u-2*u^2-Q0*(Q0+1) := by
    norm_num [Q0] at hp ⊢
    nlinarith
  exact div_nonneg hn (mul_nonneg (sq_nonneg _) (sq_nonneg _))

lemma row_zero_target_negative {b : ℝ} (hb : b∈sourceDomain) (hG : G 0 b≤0) :
    stationaryTarget 0 b<0 := by
  have hbhalf : b≤1/2 := by norm_num [G,z,alpha,p] at hG; exact hG
  have hH : height 0 b∈Icc (1747/1000:ℝ) (38021/20000) := by
    norm_num [height,mass,z,l,p,q,Q0]
    constructor <;> nlinarith [hb.1,hbhalf]
  have hu0 : 0<height 0 b := by linarith [hH.1]
  have hr : 0≤targetRatio (height 0 b) := div_nonneg (Real.sqrt_nonneg _) hu0.le
  have hl := l_positive (0:Row) (source_outer hb)
  have hz : z b≤0 := by dsimp [z]; linarith
  have hbracket : P 0+z b*l 0 b/mass 0 b≤0 := by
    norm_num [P]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hz hl.le)
      (mass_positive (0:Row) (source_outer hb)).le
  have hprod := mul_nonpos_of_nonneg_of_nonpos hr hbracket
  have hmono := f_monotone ⟨hH.1,by linarith [hH.2]⟩ (by norm_num) hH.2
  have href : f (38021/20000)-t 0< -(47/1000:ℝ) := by norm_num [f,t,Q0]
  dsimp [stationaryTarget]
  linarith

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Same.Stationary
