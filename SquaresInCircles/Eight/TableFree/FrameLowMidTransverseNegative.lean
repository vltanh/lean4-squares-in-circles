module

public import SquaresInCircles.Eight.TableFree.FrameLowMidTransverseNorm

/-!
# The full negative low-to-middle transverse support

A single tangent majorant has no interior minimum in the first
quadrant.  The original radical support is increasing on the complete
second-quadrant continuation.  The final result keeps the original
negative source and its weak separating-axis equality.
Uncompiled source draft of HAND_FOUR_TYPE_SCALAR_REPLACEMENTS §5.2.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowMidTransverseNegative
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus
open FrameLowMidTransverseNorm

def r : ℝ := 1978787508/1000000000
def lam : ℝ := 49/50
def aa : ℝ := r*lam*p/(14/5)-(lam-9/100)
def bb : ℝ := -(9/100)+r*lam*q/(14/5)
def kk : ℝ := K lam (-(1/25000))-r*(7/5+(5/28)*(p^2+q^2+lam^2))
def E (x : ℝ) : ℝ := x+kk+bb*Real.cos x-aa*Real.sin x
def reflected (z : ℝ) : ℝ := Real.pi/2-z+kk+bb*Real.sin z-aa*Real.cos z
def reflectedD (z : ℝ) : ℝ := -1+bb*Real.cos z+aa*Real.sin z
def reflectedDD (z : ℝ) : ℝ := -bb*Real.sin z+aa*Real.cos z

theorem coefficient_bounds : 0<aa ∧ (1:ℝ)<bb := by
  norm_num [aa,bb,r,lam,p,q]

theorem tangent_support {x : ℝ} (hx : x∈Icc 1 (Real.pi/2)) :
    E x≤F lam (-(1/25000)) false x := by
  have hlam : lam∈Icc (0:ℝ) 1 := by constructor <;> norm_num [lam]
  have hn := N_positive hlam x
  have hmajor := tangent_majorant (n := N lam x) (show (0:ℝ)<14/5 by norm_num)
  have hR : R≤r := by simpa [r] using radius_precise.2.le
  have hr : 0≤r := by norm_num [r]
  have hh := mul_le_mul hR hmajor hn.le hr
  rw [N_square hlam x] at hh
  dsimp [energy] at hh
  dsimp [E,aa,bb,kk,F,cosCoefficient]
  ring_nf at hh ⊢
  linarith

theorem reflected_identity (x : ℝ) : reflected (Real.pi/2-x)=E x := by
  dsimp [reflected,E]
  rw [Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub]
  ring

theorem reflected_deriv (z : ℝ) : HasDerivAt reflected (reflectedD z) z := by
  unfold reflected
  convert ((((hasDerivAt_id' z).const_sub (Real.pi/2)).add_const kk).fun_add
    ((Real.hasDerivAt_sin z).const_mul bb)).fun_sub
      ((Real.hasDerivAt_cos z).const_mul aa) using 1
  simp only [reflectedD]
  ring

theorem reflectedD_deriv (z : ℝ) : HasDerivAt reflectedD (reflectedDD z) z := by
  unfold reflectedD
  convert (((Real.hasDerivAt_cos z).const_mul bb).const_add (-1)).fun_add
    ((Real.hasDerivAt_sin z).const_mul aa) using 1
  simp only [reflectedDD]
  ring

theorem reflectedDD_deriv (z : ℝ) :
    HasDerivAt reflectedDD (-bb*Real.cos z-aa*Real.sin z) z := by
  unfold reflectedDD
  convert ((Real.hasDerivAt_sin z).const_mul (-bb)).fun_add
    ((Real.hasDerivAt_cos z).const_mul aa) using 1
  ring

theorem reflectedD_concave :
    ConcaveOn ℝ (Icc 0 (Real.pi/2-1)) reflectedD := by
  apply concave_of_deriv2 (fun z _ => reflectedD_deriv z) (fun z _ => reflectedDD_deriv z)
  intro z hz
  have ht := FrameLowPair.quadrant (show z∈Icc 0 (Real.pi/2) from ⟨hz.1,by linarith [hz.2]⟩)
  have h1 := mul_nonneg (by linarith [coefficient_bounds.2] : 0≤bb) ht.2.2.1
  have h2 := mul_nonneg coefficient_bounds.1.le ht.1
  linarith

theorem E_endpoints : (9053/10000:ℝ)<E 1 ∧ (9109/10000:ℝ)<E (Real.pi/2) := by
  constructor
  · have hs := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤1 by norm_num)
    have hc := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤1 by norm_num)
    norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
      Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs hc
    norm_num [E,aa,bb,kk,FrameLowMidTransverseNorm.K,r,lam,p,q,cM]
    linarith
  · have hpi := Arithmetic.pi_hand_enclosure.1
    norm_num [E,aa,bb,kk,FrameLowMidTransverseNorm.K,r,lam,p,q,cM]
    linarith

theorem first_lower {x : ℝ} (hx : x∈Icc 1 (Real.pi/2)) :
    (1801/2000:ℝ)<F lam (-(1/25000)) false x := by
  have hz : Real.pi/2-x∈Icc 0 (Real.pi/2-1) := ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hd0 : 0≤reflectedD 0 := by simp [reflectedD]; linarith [coefficient_bounds.2]
  have hh := endpoint_minimum_of_concave_derivative hz
    (fun z _ => reflected_deriv z) reflectedD_concave hd0
  have h0 : reflected 0=E (Real.pi/2) := by simp [reflected,E]
  have h1 : reflected (Real.pi/2-1)=E 1 := reflected_identity 1
  rw [h0,h1,reflected_identity] at hh
  have hm : (1801/2000:ℝ)< min (E (Real.pi/2)) (E 1) := by
    apply lt_min <;> linarith [E_endpoints.1,E_endpoints.2]
  exact (hm.trans_le hh).trans_le (tangent_support hx)

theorem second_trig {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100)) :
    (99/100:ℝ)<Real.sin x ∧ -(7/50:ℝ)<Real.cos x ∧ Real.cos x≤0 := by
  have hsE := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤171/100 by norm_num)
  have hcE := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤171/100 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hsE hcE
  have hs := sin_endpoint_lower (by positivity : 0≤Real.pi/2)
    (by linarith [FrameLowPair.pi_lower] : (171/100:ℝ)≤Real.pi) hx
    (by norm_num : (99/100:ℝ)<Real.sin (Real.pi/2)) (by linarith)
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx.1,Real.pi_pos] : 0≤x)
    (by linarith [FrameLowPair.pi_lower] : (171/100:ℝ)≤Real.pi) hx.2
  have hsign := second_signs (show x∈Icc (Real.pi/2) Real.pi from
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩)
  exact ⟨hs,by linarith,hsign.2⟩

theorem second_norm_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100)) :
    (29/10:ℝ)<N lam x := by
  have hn := N_positive (show lam∈Icc (0:ℝ) 1 by constructor <;> norm_num [lam]) x
  have hs := N_square (show lam∈Icc (0:ℝ) 1 by constructor <;> norm_num [lam]) x
  have ht := second_trig hx
  dsimp [energy,lam,p,q] at hs hn ⊢
  nlinarith [ht.1,ht.2.2]

theorem second_norm_slope {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100)) :
    Nd lam x<27/50 := by
  have hn := second_norm_lower hx
  have ht := second_trig hx
  dsimp [Nd]
  apply (div_lt_iff₀ (by linarith : 0<N lam x)).2
  have hs := Real.sin_le_one x
  dsimp [lam,p,q] at hn ⊢
  linarith

theorem second_slope_positive {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100)) :
    0<Fd lam true x := by
  have ht := second_trig hx
  have hn := second_norm_slope hx
  have hprod := mul_lt_mul_of_pos_left hn R_pos
  have hR := mul_le_mul_of_nonneg_right
    (show R≤99/50 by linarith [radius_precise.2]) (show (0:ℝ)≤27/50 by norm_num)
  dsimp [Fd,cosCoefficient,lam] at hprod ⊢
  linarith

theorem second_monotone : MonotoneOn (F lam (-(1/25000)) true)
    (Icc (Real.pi/2) (171/100)) := by
  have hlam : lam∈Icc (0:ℝ) 1 := by constructor <;> norm_num [lam]
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (F_deriv hlam (-(1/25000)) true x).continuousAt.continuousWithinAt
  · exact fun x _ => F_deriv hlam (-(1/25000)) true x
  · exact fun x hx => (second_slope_positive (Ioo_subset_Icc_self hx)).le

theorem second_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100)) :
    (1801/2000:ℝ)<F lam (-(1/25000)) true x := by
  have hfirst := first_lower (show Real.pi/2∈Icc (1:ℝ) (Real.pi/2) from
    ⟨by linarith [FrameLowPair.pi_lower],le_rfl⟩)
  have he : F lam (-(1/25000)) false (Real.pi/2)=F lam (-(1/25000)) true (Real.pi/2) := by
    simp [F,cosCoefficient]
  rw [he] at hfirst
  exact hfirst.trans_le (second_monotone ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1)

theorem weak_separator {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (1:ℝ) (171/100))
    (hm : 0≤FrameLowMidGeometry.secondary false true b B x) :
    (1801/2000:ℝ)<FrameLowMidGeometry.lowMidCost false true b B x := by
  have hlam : lam∈Icc (0:ℝ) 1 := by constructor <;> norm_num [lam]
  have hs : -(1/25000:ℝ)≤ sign false*(L b-lam*b) := by
    simpa [sign,lam] using low_negative_source hb
  by_cases hq : x≤Real.pi/2
  · have hdom : x∈Icc 1 (Real.pi/2) := ⟨hx.1,hq⟩
    exact (first_lower hdom).trans_le (circle_support false hlam hb hB hs false
      (show x∈Icc 0 (Real.pi/2) from ⟨by linarith [hx.1],hq⟩) hm)
  · have hdom : x∈Icc (Real.pi/2) (171/100) := ⟨(lt_of_not_ge hq).le,hx.2⟩
    exact (second_lower hdom).trans_le (circle_support false hlam hb hB hs true
      (show x∈Icc (Real.pi/2) Real.pi from ⟨hdom.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩) hm)

end SquaresInCircles.Eight.TableFree.FrameLowMidTransverseNegative
