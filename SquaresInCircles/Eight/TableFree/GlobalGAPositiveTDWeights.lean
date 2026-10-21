module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDConcentration
public import SquaresInCircles.Eight.TableFree.HighOrderTaylor

/-!
# Explicit continuous weights for the positive TD2 stress

Uncompiled source.  These are the two formulas in the complete scalar
companion.  The second formula changes expression only where its two
coefficients meet.  All bounds concern complete intervals and the actual
trigonometric tilted coefficient.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD.Explicit
open Candidate Secondary

abbrev split : ℝ := 1/6
abbrev clamp : ℝ := 37/80
abbrev cap : ℝ := 653/800

def lowK (z : ℝ) : ℝ := 84/125-(z-83/500)/5+(5/2)*(z-83/500)^2
def lowL (z : ℝ) : ℝ := 101/100-(5/2)*(z-83/500)+6*(z-83/500)^2+48*(z-83/500)^3
def lowC (z : ℝ) : ℝ := 1043/1000-(21/5)*(z-83/500)+8*(z-83/500)^2

inductive Upper where | varying | clamped
  deriving DecidableEq, Fintype

def left : Upper→ℚ | .varying => 1/6 | .clamped => 37/80
def right : Upper→ℚ | .varying => 37/80 | .clamped => 7/10
def upperK : Upper→ℝ→ℝ
  | .varying,z => 117/200+z/2
  | .clamped,_ => cap
def upperC : Upper→ℝ→ℝ
  | .varying,z => 57/50-(7/10)*z
  | .clamped,_ => cap

theorem low_derivatives (z : ℝ) :
    HasDerivAt lowK (-1/5+5*(z-83/500)) z ∧
    HasDerivAt lowL (-5/2+12*(z-83/500)+144*(z-83/500)^2) z ∧
    HasDerivAt lowC (-21/5+16*(z-83/500)) z := by
  have hk : Differentiable ℝ lowK := by dsimp [lowK]; fun_prop
  have hl : Differentiable ℝ lowL := by dsimp [lowL]; fun_prop
  have hc : Differentiable ℝ lowC := by dsimp [lowC]; fun_prop
  refine ⟨?_,?_,?_⟩
  · convert (hk z).hasDerivAt using 1
    simp (disch := fun_prop) [lowK]
    ring
  · convert (hl z).hasDerivAt using 1
    simp (disch := fun_prop) [lowL]
    ring
  · convert (hc z).hasDerivAt using 1
    simp (disch := fun_prop) [lowC]
    ring

theorem low_derivatives_negative {z : ℝ} (hz : z∈Icc 0 split) :
    -1/5+5*(z-83/500)<0 ∧
      -5/2+12*(z-83/500)+144*(z-83/500)^2<0 ∧
      -21/5+16*(z-83/500)<0 := by
  have ht : -(83/500:ℝ)≤z-83/500 ∧ z-83/500≤1/1500 := by
    dsimp [split] at hz
    constructor <;> linarith [hz.1,hz.2]
  have hchord := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤(z-83/500)+83/500 by linarith [ht.1])
    (show (z-83/500)-1/1500≤0 by linarith [ht.2])
  exact ⟨by linarith [ht.2],by nlinarith [ht.1],by linarith [ht.2]⟩

theorem low_antitone :
    AntitoneOn lowK (Icc 0 split) ∧ AntitoneOn lowL (Icc 0 split) ∧
      AntitoneOn lowC (Icc 0 split) := by
  refine ⟨?_,?_,?_⟩
  · exact antiOn_of_hasDeriv_nonpos (by dsimp [lowK]; fun_prop)
      (fun z _ => (low_derivatives z).1)
      (fun z hz => (low_derivatives_negative (Ioo_subset_Icc_self hz)).1.le)
  · exact antiOn_of_hasDeriv_nonpos (by dsimp [lowL]; fun_prop)
      (fun z _ => (low_derivatives z).2.1)
      (fun z hz => (low_derivatives_negative (Ioo_subset_Icc_self hz)).2.1.le)
  · exact antiOn_of_hasDeriv_nonpos (by dsimp [lowC]; fun_prop)
      (fun z _ => (low_derivatives z).2.2)
      (fun z hz => (low_derivatives_negative (Ioo_subset_Icc_self hz)).2.2.le)

theorem low_ranges {z : ℝ} (hz : z∈Icc 0 split) :
    2/3<lowK z ∧ lowK z<31/40 ∧ 1<lowL z ∧ lowL z≤lowC z ∧
      lowC z<2 ∧ lowL z<2*lowK z := by
  have hzero : (0:ℝ)∈Icc 0 split := by norm_num [split]
  have hend : split∈Icc 0 split := by norm_num [split]
  have hklo := low_antitone.1 hz hend hz.2
  have hkhi := low_antitone.1 hzero hz hz.1
  have hllo := low_antitone.2.1 hz hend hz.2
  have hchi := low_antitone.2.2 hzero hz hz.1
  have hrK : (2/3:ℝ)<lowK split ∧ lowK 0<31/40 := by
    norm_num [lowK,split]
  have hrL : (1:ℝ)<lowL split := by norm_num [lowL,split]
  have hrC : lowC 0<(2:ℝ) := by norm_num [lowC]
  have ht : z-83/500≤1/1500 := by dsimp [split] at hz; linarith [hz.2]
  have ht3 := mul_le_mul_of_nonneg_left ht (sq_nonneg (z-83/500))
  have hlc : lowL z≤lowC z := by
    dsimp [lowL,lowC]
    nlinarith [sq_nonneg (z-83/500)]
  have hz3 := mul_nonneg (sq_nonneg z)
    (show 0≤1/6-z by simpa only [split] using sub_nonneg.mpr hz.2)
  have htwice : lowL z<2*lowK z := by
    have hid : 2*lowK z-lowL z=
        177410208/1000000000-(1536064/1000000)*z+
          (22904/1000)*z^2-48*z^3 := by dsimp [lowK,lowL]; ring
    have hsquare := sq_nonneg (z-(1536064/1000000)/(2*(14904/1000)))
    apply sub_pos.mp
    rw [hid]
    nlinarith
  exact ⟨hrK.1.trans_le hklo,hkhi.trans_lt hrK.2,
    hrL.trans_le hllo,hlc,hchi.trans_lt hrC,htwice⟩

theorem factor_upper (z : ℝ) : Real.cos z+eta*Real.sin z<1043/1000 := by
  by_contra! hh
  have hu := Real.sin_sq_add_cos_sq z
  have hs := sq_nonneg (Real.sin z-eta*Real.cos z)
  have hm := mul_nonneg (sub_nonneg.mpr hh)
    (show 0≤Real.cos z+eta*Real.sin z+1043/1000 by linarith)
  dsimp [eta] at *
  nlinarith

theorem factor_lower {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (19/20:ℝ)<Real.cos z+eta*Real.sin z := by
  have hc : ConcaveOn ℝ (Icc 0 frameCap) (harmonic 1 eta) :=
    harmonic_concave (fun t ht => by
      have hh := transport_trig ht
      dsimp [eta]
      linarith [hh.1,hh.2.2.1])
  have hleft : (19/20:ℝ)<harmonic 1 eta 0 := by norm_num [harmonic]
  have hright : (19/20:ℝ)<harmonic 1 eta frameCap := by
    have hs := sin_lower_seven (show 0≤frameCap by norm_num [frameCap])
    have hcos := cos_lower_six (show 0≤frameCap by norm_num [frameCap])
    norm_num [harmonic,eta,frameCap] at hs hcos ⊢
    linarith
  simpa [harmonic] using concave_gt_of_endpoints hc hz hleft hright

theorem low_factor {z : ℝ} (hz : z∈Icc 0 split) :
    1≤Real.cos z+eta*Real.sin z ∧ Real.cos z+eta*Real.sin z≤1+eta*z := by
  have hz2 := mul_nonneg hz.1 (show 0≤1/6-z by simpa only [split] using sub_nonneg.mpr hz.2)
  have hzsq : z^2≤(1/6:ℝ)^2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hz3 := mul_le_mul_of_nonneg_right hzsq hz.1
  have hs := Real.sin_ge_sub_cube hz.1
  have hc := Real.one_sub_sq_div_two_le_cos (x:=z)
  have hsHi := Real.sin_le hz.1
  have hcHi := Real.cos_le_one z
  dsimp [eta]
  constructor <;> nlinarith

theorem low_tilted {z : ℝ} (hz : z∈Icc 0 split) :
    lowL z≤tilted (lowC z) z ∧ tilted (lowC z) z<(3/2)*lowL z := by
  have hr := low_ranges hz
  have hc : 0≤lowC z := by linarith [hr.2.2.1,hr.2.2.2.1]
  have hlo := mul_le_mul_of_nonneg_left (low_factor hz).1 hc
  have hhi := mul_le_mul_of_nonneg_left (low_factor hz).2 hc
  have hid : (3/2)*lowL z-lowC z*(1+eta*z)=
      95506688/1000000000+(5495626136/1000000000)*z-
        (32847192/1000000)*z^2+(69656/1000)*z^3 := by
    dsimp [lowL,lowC,eta]
    ring
  have hz2 := mul_nonneg hz.1 (show 0≤1/6-z by simpa only [split] using sub_nonneg.mpr hz.2)
  have hz3 := pow_nonneg hz.1 3
  have hmargin : (955/10000:ℝ)<(3/2)*lowL z-lowC z*(1+eta*z) := by
    rw [hid]
    nlinarith
  dsimp [tilted] at ⊢
  exact ⟨by linarith [hr.2.2.2.1],by linarith⟩

theorem low_domain {z : ℝ} (hz : z∈Icc 0 split) :
    lowK z∈Icc (1/2:ℝ) (17/20) ∧ lowL z∈Icc (lowK z) (2*lowK z) ∧
      lowC z∈Icc (lowK z) 2 ∧
      (lowL z≤2*tilted (lowC z) z ∧ tilted (lowC z) z≤2*lowL z) := by
  have hr := low_ranges hz
  have hm := low_tilted hz
  refine ⟨⟨by linarith [hr.1],by linarith [hr.2.1]⟩,
    ⟨by linarith [hr.2.1,hr.2.2.1],hr.2.2.2.2.2.le⟩,
    ⟨by linarith [hr.2.1,hr.2.2.1,hr.2.2.2.1],hr.2.2.2.2.1.le⟩,?_,?_⟩ <;>
    linarith [hm.1,hm.2,hr.2.2.1]

theorem upper_ranges (a : Upper) {z : ℝ}
    (hz : z∈Icc (left a:ℝ) (right a:ℝ)) :
    z∈Icc 0 frameCap ∧ 2/3<upperK a z ∧ upperK a z≤cap ∧
      upperK a z≤upperC a z ∧ cap≤upperC a z ∧ upperC a z<128/125 := by
  cases a <;> norm_num [left,right,upperK,upperC,cap,frameCap] at hz ⊢ <;>
    constructor <;> try constructor <;> try constructor <;> try constructor <;>
    try constructor <;> linarith [hz.1,hz.2]

theorem upper_tilted (a : Upper) {z : ℝ}
    (hz : z∈Icc (left a:ℝ) (right a:ℝ)) :
    2/3<tilted (upperC a z) z ∧ tilted (upperC a z) z<6/5 ∧
      upperK a z*tilted (upperC a z) z<1 := by
  have hr := upper_ranges a hz
  have hc : 0<upperC a z := by linarith [hr.2.2.2.2.1]
  have hlo := mul_lt_mul_of_pos_left (factor_lower hr.1) hc
  have hhi := mul_lt_mul_of_pos_left (factor_upper z) hc
  have hk : 0<upperK a z := by linarith [hr.2.1]
  have hm : 0<tilted (upperC a z) z := tilted_pos hc hr.1
  have hproduct := mul_le_mul_of_nonneg_right hr.2.2.1 hm.le
  dsimp [tilted,cap] at hlo hhi hproduct ⊢
  exact ⟨by linarith [hr.2.2.2.2.1],by linarith [hr.2.2.2.2.2],
    by nlinarith [hr.2.2.2.2.2]⟩

theorem upper_domain (a : Upper) {z : ℝ}
    (hz : z∈Icc (left a:ℝ) (right a:ℝ)) :
    upperK a z∈Icc (1/2:ℝ) (17/20) ∧ (1:ℝ)∈Icc (upperK a z) (2*upperK a z) ∧
      upperC a z∈Icc (upperK a z) 2 ∧
      (1≤2*tilted (upperC a z) z ∧ tilted (upperC a z) z≤2) := by
  have hr := upper_ranges a hz
  have hm := upper_tilted a hz
  dsimp [cap] at hr
  exact ⟨⟨by linarith [hr.2.1],by linarith [hr.2.2.1]⟩,
    ⟨by linarith [hr.2.2.1],by linarith [hr.2.1]⟩,
    ⟨hr.2.2.2.1,by linarith [hr.2.2.2.2.2]⟩,
    by linarith [hm.1],by linarith [hm.2.1]⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD.Explicit
