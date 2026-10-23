module

public import SquaresInCircles.Eight.TableFree.ShortMixedZeroSmallNegative

/-!
# The exact diagonal-contact curve of the last mixed negative family

The contact is continued through the single endpoint `.44152`; its
radical stays positive even where that continuation is slightly beyond
the physical outer diagonal. The original cost comparison will use only
the original feasible states. All three derivatives are proved from the
circle equation on this whole interval. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.ShortMixedZero.SmallContact

open CommonQuarter CorePairGeometry Arithmetic

def e : ℝ := 9133/100000
def b (x : ℝ) : ℝ := 1/2+(1/2+CoreAngleEndpoint.diagonal)*Real.sin x+
  (1/2-CoreAngleEndpoint.diagonal)*Real.cos x
def bd (x : ℝ) : ℝ := (1/2+CoreAngleEndpoint.diagonal)*Real.cos x+
  (CoreAngleEndpoint.diagonal-1/2)*Real.sin x
def bdd (x : ℝ) : ℝ := 1/2-b x
def Y (z : ℝ) : ℝ := Real.sqrt (Q0-(z+1/2)^2)
def radial (z : ℝ) : ℝ := -e*(Y z-1/2)+(88074/100000)*z
def fd (z : ℝ) : ℝ := 88074/100000+e*(z+1/2)/Y z
def fdd (z : ℝ) : ℝ := e*Q0/(Y z)^3
def fddd (z : ℝ) : ℝ := 3*e*Q0*(z+1/2)/(Y z)^5

def H (x : ℝ) : ℝ := -x+28271/100000+radial (b x)+
  (62095/100000)*CoreAngleEndpoint.diagonal
def Hd (x : ℝ) : ℝ := -1+fd (b x)*bd x
def Hdd (x : ℝ) : ℝ := fdd (b x)*(bd x)^2+fd (b x)*bdd x
def Hddd (x : ℝ) : ℝ :=
  bd x*(fddd (b x)*(bd x)^2+3*fdd (b x)*bdd x-fd (b x))

lemma b_hasDerivAt (x : ℝ) : HasDerivAt b (bd x) x := by
  convert (((Real.hasDerivAt_sin x).const_mul (1/2+CoreAngleEndpoint.diagonal)).const_add (1/2)).add
    ((Real.hasDerivAt_cos x).const_mul (1/2-CoreAngleEndpoint.diagonal)) using 1 <;>
    dsimp [b,bd] <;> ring

lemma bd_hasDerivAt (x : ℝ) : HasDerivAt bd (bdd x) x := by
  convert ((Real.hasDerivAt_cos x).const_mul (1/2+CoreAngleEndpoint.diagonal)).add
    ((Real.hasDerivAt_sin x).const_mul (CoreAngleEndpoint.diagonal-1/2)) using 1 <;>
    dsimp [bd,bdd,b] <;> ring

lemma bdd_hasDerivAt (x : ℝ) : HasDerivAt bdd (-bd x) x := by
  simpa [bdd] using (b_hasDerivAt x).const_sub (1/2)

lemma bd_lower {x : ℝ} (hx : x∈Icc 0 smallCap) : (19/20:ℝ)<bd x := by
  have hcap : smallCap≤7/10 := by norm_num [smallCap]
  have ht := positive_trig ⟨hx.1,hx.2.trans hcap⟩
  have hc := cos_lower_two hx.1
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hcos : (9/10:ℝ)<Real.cos x := by norm_num [smallCap] at hx2; nlinarith
  have hd := CoreAngleEndpoint.diagonal_bounds
  have hsin := mul_nonneg (show 0≤CoreAngleEndpoint.diagonal-1/2 by linarith [hd.1]) ht.2.2.1
  have hprimary := mul_lt_mul_of_pos_left hcos
    (show 0<1/2+CoreAngleEndpoint.diagonal by linarith [hd.1])
  dsimp [bd]
  nlinarith [hd.1]

lemma bd_square_upper (x : ℝ) : (bd x)^2<(53/50:ℝ)^2+(59/1000)^2 := by
  have hid : (bd x)^2+
      ((1/2+CoreAngleEndpoint.diagonal)*Real.sin x-
        (CoreAngleEndpoint.diagonal-1/2)*Real.cos x)^2=
      (1/2+CoreAngleEndpoint.diagonal)^2+(CoreAngleEndpoint.diagonal-1/2)^2 := by
    dsimp [bd]
    linear_combination ((1/2+CoreAngleEndpoint.diagonal)^2+
      (CoreAngleEndpoint.diagonal-1/2)^2)*(Real.sin_sq_add_cos_sq x)
  have hs := sq_nonneg ((1/2+CoreAngleEndpoint.diagonal)*Real.sin x-
    (CoreAngleEndpoint.diagonal-1/2)*Real.cos x)
  have hd := CoreAngleEndpoint.diagonal_bounds
  nlinarith [hd.1,hd.2]

lemma b_monotone : MonotoneOn b (Icc 0 smallCap) :=
  monoOn_of_hasDeriv_nonneg (fun x _ => (b_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x _ => b_hasDerivAt x) (fun x hx => by linarith [bd_lower (Ioo_subset_Icc_self hx)])

lemma endpoint_trig : Real.sin smallCap<(85463/200000:ℝ) ∧
    (904103/1000000:ℝ)<Real.cos smallCap := by
  have hs := sin_upper_five (x := smallCap) (by norm_num [smallCap])
  have hc := cos_lower_six (x := smallCap) (by norm_num [smallCap])
  norm_num [smallCap] at hs hc
  exact ⟨by linarith,by linarith⟩

lemma endpoint_b : (449609/500000:ℝ)<b smallCap ∧ b smallCap<8993/10000 := by
  have hd := CoreAngleEndpoint.diagonal_bounds
  have ht := smallCap_point_trig
  have hu := endpoint_trig
  have hsl := mul_le_mul_of_nonneg_left ht.1.le
    (show 0≤1/2+CoreAngleEndpoint.diagonal by linarith [hd.1])
  have hsu := mul_le_mul_of_nonneg_left hu.1.le
    (show 0≤1/2+CoreAngleEndpoint.diagonal by linarith [hd.1])
  have hcl := mul_le_mul_of_nonpos_left ht.2.le
    (show 1/2-CoreAngleEndpoint.diagonal≤0 by linarith [hd.1])
  have hcu := mul_le_mul_of_nonpos_left hu.2.le
    (show 1/2-CoreAngleEndpoint.diagonal≤0 by linarith [hd.1])
  dsimp [b]
  constructor <;> nlinarith [hd.1,hd.2]

lemma b_bounds {x : ℝ} (hx : x∈Icc 0 smallCap) :
    (11/25:ℝ)<b x ∧ b x<8993/10000 := by
  have hlo := b_monotone (by norm_num [smallCap]) hx hx.1
  have hhi := b_monotone hx (by norm_num [smallCap]) hx.2
  have hd := CoreAngleEndpoint.diagonal_bounds
  simp only [b,Real.sin_zero,Real.cos_zero,mul_zero,mul_one,add_zero] at hlo
  exact ⟨by linarith [hd.2],hhi.trans_lt endpoint_b.2⟩

lemma bdd_upper {x : ℝ} (hx : x∈Icc 0 smallCap) : bdd x<(59/1000:ℝ) := by
  have hlo := b_monotone (by norm_num [smallCap]) hx hx.1
  have hd := CoreAngleEndpoint.diagonal_bounds
  simp only [b,Real.sin_zero,Real.cos_zero,mul_zero,mul_one,add_zero] at hlo
  dsimp [bdd]
  linarith [hd.2]

lemma radicand_pos {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) :
    0<Q0-(z+1/2)^2 := by
  have hs := pow_le_pow_left₀ (show 0≤z+1/2 by linarith [hz.1])
    (show z+1/2≤13993/10000 by linarith [hz.2]) 2
  norm_num [Q0]
  nlinarith

lemma Y_pos {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) : 0<Y z :=
  Real.sqrt_pos.mpr (radicand_pos hz)

lemma Y_sq {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) :
    (Y z)^2+(z+1/2)^2=Q0 := by
  have hh := Real.sq_sqrt (radicand_pos hz).le
  dsimp [Y]
  linarith

lemma Y_lower {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) : (1399/1000:ℝ)<Y z := by
  have hs := Y_sq hz
  have hp := Y_pos hz
  have hz2 := pow_le_pow_left₀ (show 0≤z+1/2 by linarith [hz.1])
    (show z+1/2≤13993/10000 by linarith [hz.2]) 2
  norm_num [Q0] at hs
  nlinarith

lemma Y_hasDerivAt {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) :
    HasDerivAt Y (-(z+1/2)/Y z) z := by
  have hh := ((hasDerivAt_const z Q0).sub
    (((hasDerivAt_id z).add_const (1/2)).pow 2)).sqrt (radicand_pos hz).ne'
  convert hh using 1 <;> dsimp [Y] <;> ring

lemma radial_hasDerivAt {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) :
    HasDerivAt radial (fd z) z := by
  convert (((Y_hasDerivAt hz).sub_const (1/2)).const_mul (-e)).add
    ((hasDerivAt_id z).const_mul (88074/100000:ℝ)) using 1 <;>
    dsimp [radial,fd] <;> ring

lemma fd_hasDerivAt {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) :
    HasDerivAt fd (fdd z) z := by
  have hn := (Y_pos hz).ne'
  have hh := ((((hasDerivAt_id z).add_const (1/2)).const_mul e).div
    (Y_hasDerivAt hz) hn).const_add (88074/100000:ℝ)
  convert hh using 1
  · rfl
  · dsimp [fd,fdd,e]
    field_simp [hn]
    nlinarith only [Y_sq hz]

lemma fdd_hasDerivAt {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) :
    HasDerivAt fdd (fddd z) z := by
  have hn := (Y_pos hz).ne'
  have hh := (hasDerivAt_const z (e*Q0)).div
    ((Y_hasDerivAt hz).pow 3) (pow_ne_zero 3 hn)
  convert hh using 1
  · rfl
  · dsimp [fdd,fddd]
    field_simp [hn]
    ring

lemma curve_domain {x : ℝ} (hx : x∈Icc 0 smallCap) : b x∈Icc (11/25) (8993/10000) :=
  ⟨(b_bounds hx).1.le,(b_bounds hx).2.le⟩

lemma H_hasDerivAt {x : ℝ} (hx : x∈Icc 0 smallCap) : HasDerivAt H (Hd x) x := by
  have hf := (radial_hasDerivAt (curve_domain hx)).comp x (b_hasDerivAt x)
  convert ((((hasDerivAt_id x).neg).add_const (28271/100000:ℝ)).add hf).add_const
    ((62095/100000)*CoreAngleEndpoint.diagonal) using 1 <;> dsimp [H,Hd] <;> ring

lemma Hd_hasDerivAt {x : ℝ} (hx : x∈Icc 0 smallCap) : HasDerivAt Hd (Hdd x) x := by
  have hf := (fd_hasDerivAt (curve_domain hx)).comp x (b_hasDerivAt x)
  convert (hf.mul (bd_hasDerivAt x)).const_add (-1) using 1 <;> dsimp [Hd,Hdd] <;> ring

lemma Hdd_hasDerivAt {x : ℝ} (hx : x∈Icc 0 smallCap) : HasDerivAt Hdd (Hddd x) x := by
  have hf₂ := (fdd_hasDerivAt (curve_domain hx)).comp x (b_hasDerivAt x)
  have hf₁ := (fd_hasDerivAt (curve_domain hx)).comp x (b_hasDerivAt x)
  convert (hf₂.mul ((bd_hasDerivAt x).pow 2)).add (hf₁.mul (bdd_hasDerivAt x)) using 1 <;>
    dsimp [Hdd,Hddd] <;> ring

lemma radial_derivative_bounds {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) :
    (22/25:ℝ)<fd z ∧ 0<fdd z ∧ fdd z<27/200 ∧
      0<fddd z ∧ fddd z<289/1000 := by
  have hy := Y_lower hz
  have hyp := Y_pos hz
  have hy3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hy.le 3
  have hy5 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hy.le 5
  have he : 0<e := by norm_num [e]
  have hz0 : 0<z+1/2 := by linarith [hz.1]
  refine ⟨?_,?_,?_,?_,?_⟩
  · have hh := div_pos (mul_pos he hz0) hyp
    dsimp [fd]
    linarith
  · exact div_pos (mul_pos he (by norm_num [Q0])) (pow_pos hyp 3)
  · rw [fdd,div_lt_iff₀ (pow_pos hyp 3)]
    norm_num [e,Q0] at hy3 ⊢
    nlinarith
  · exact div_pos (by dsimp [e,Q0]; positivity) (pow_pos hyp 5)
  · rw [fddd,div_lt_iff₀ (pow_pos hyp 5)]
    norm_num [e,Q0] at hy5 ⊢
    nlinarith [hz.2]

/-- The entire contact's third derivative is strictly below `-1/2`.
The estimate comes from geometric radical bounds, not a derivative
envelope supplied to the theorem. -/
lemma Hddd_negative {x : ℝ} (hx : x∈Icc 0 smallCap) : Hddd x<-(1/2:ℝ) := by
  have hb := bd_lower hx
  have hb2 := bd_square_upper x
  have hbdd := bdd_upper hx
  have hf := radial_derivative_bounds (curve_domain hx)
  have hfirst := mul_le_mul_of_nonneg_left hb2.le hf.2.2.2.1.le
  have hfirst' := mul_lt_mul_of_pos_right hf.2.2.2.2
    (by norm_num : (0:ℝ)<(53/50)^2+(59/1000)^2)
  have hsecond := mul_lt_mul_of_pos_left hbdd hf.2.1
  have hsecond' := mul_lt_mul_of_pos_right hf.2.2.1 (by norm_num : (0:ℝ)<59/1000)
  have hbracket : fddd (b x)*(bd x)^2+3*fdd (b x)*bdd x-fd (b x)<-(53/100:ℝ) := by
    nlinarith [hf.1]
  have hprod := mul_lt_mul_of_pos_left hbracket (by linarith : 0<bd x)
  dsimp [Hddd]
  nlinarith

end SquaresInCircles.Eight.TableFree.ShortMixedZero.SmallContact
