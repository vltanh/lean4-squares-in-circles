module

public import SquaresInCircles.Eight.TableFree.FrameHighLowAxialCalculus

/-!
# Rational reference bounds for both exact axial costs

All auxiliary constants are displayed rational Taylor expressions.
The primary-coordinate ceilings are derived by squaring them against
the circle equation; no numerical root or endpoint value is assumed.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowAxialReferences
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameHighLowAxialGeometry FrameHighLowAxialCalculus

def ref (normal : Bool) : ℝ := if normal then 23/200 else 11/100
def sl (normal : Bool) : ℝ := HighOrderTaylor.S11 (ref normal)
def su (normal : Bool) : ℝ := Arithmetic.sin9 (ref normal)
def cl (normal : Bool) : ℝ := Arithmetic.cos10 (ref normal)
def cu (normal : Bool) : ℝ := Arithmetic.cos8 (ref normal)
def zl (normal : Bool) : ℝ :=
  1/2+cl normal/2-(1414575672/1000000000-1/2)*su normal
def zu (normal : Bool) : ℝ :=
  1/2+cu normal/2-(1414575670/1000000000-1/2)*sl normal
def floor (normal : Bool) : ℝ := if normal then 22087/25000 else 4417/5000
def base (normal : Bool) : ℝ :=
  ref normal-(9/100)*(su normal+cu normal-1)+(314159/100000)/4+
    if normal then (FrameHighArc.u-FrameHighArc.v)*(179842813/200000000)+FrameHighArc.v*zl normal
    else -(FrameHighArc.u-FrameHighArc.v)*(449607033/500000000)+FrameHighArc.u*zl normal
def cap (normal : Bool) : ℝ :=
  (base normal-floor normal)/(if normal then FrameHighArc.u else FrameHighArc.v)

theorem ref_domain (normal : Bool) : ref normal∈domain := by
  cases normal <;> constructor <;> norm_num [ref,domain]

theorem taylor_bounds (normal : Bool) :
    sl normal≤Real.sin (ref normal) ∧ Real.sin (ref normal)≤ su normal ∧
      cl normal≤Real.cos (ref normal) ∧ Real.cos (ref normal)≤cu normal := by
  have hx : 0≤ref normal := (ref_domain normal).1
  exact ⟨HighOrderTaylor.S11_le_sin hx,Arithmetic.sin_le_sin9 hx,
    Arithmetic.cos10_le_cos hx,Arithmetic.cos_le_cos8 hx⟩

theorem positive_constants (normal : Bool) :
    0<sl normal ∧ 0<su normal ∧ 0<cl normal ∧ 0<cu normal ∧
      0<zl normal ∧ 0<cap normal+1/2 := by
  cases normal <;> norm_num [sl,su,cl,cu,zl,cap,base,floor,ref,
    FrameHighArc.u,FrameHighArc.v,HighOrderTaylor.S11,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]

theorem height_bounds (normal : Bool) : zl normal≤Z (ref normal) ∧ Z (ref normal)≤zu normal := by
  have ht := taylor_bounds normal
  have hc := positive_constants normal
  have hs0 : 0≤Real.sin (ref normal) := hc.1.le.trans ht.1
  have hprodU := mul_le_mul
    (show a0-1/2≤1414575672/1000000000-1/2 by linarith [a0_precise.2]) ht.2.1
    hs0 (by norm_num : (0:ℝ)≤1414575672/1000000000-1/2)
  have hprodL := mul_le_mul
    (show (1414575670/1000000000-1/2:ℝ)≤a0-1/2 by linarith [a0_precise.1]) ht.1
    hc.1.le (by linarith [a0_precise.1] : 0≤a0-1/2)
  dsimp [zl,zu,Z]
  constructor <;> nlinarith

theorem cap_circle_reserve (normal : Bool) :
    Q0<(cap normal+1/2)^2+(zl normal+1/2)^2 := by
  cases normal <;> norm_num [cap,base,floor,zl,sl,su,cl,cu,ref,Q0,
    FrameHighArc.u,FrameHighArc.v,HighOrderTaylor.S11,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]

theorem primary_upper (normal : Bool) : A (Z (ref normal))<cap normal := by
  have hz := height_bounds normal
  have hc := extended_circle (Z_extended (ref_domain normal))
  have hp := positive_constants normal
  have hzsq := pow_le_pow_left₀ (by linarith [hp.2.2.2.2.1] : 0≤zl normal+1/2)
    (show zl normal+1/2≤Z (ref normal)+1/2 by linarith [hz.1]) 2
  by_contra! hbad
  have hAsq := pow_le_pow_left₀ hp.2.2.2.2.2.le
    (show cap normal+1/2≤A (Z (ref normal))+1/2 by linarith) 2
  nlinarith [cap_circle_reserve normal]

theorem normal_value : (22087/25000:ℝ)<normalF (23/200) := by
  have ht := taylor_bounds true
  have hz := height_bounds true
  have hA := primary_upper true
  have he : FrameHighArc.u*cap true=base true-floor true := by
    dsimp [cap]
    field_simp
    norm_num [FrameHighArc.u]
  dsimp [normalF,H,k,FrameHighArc.u,FrameHighArc.v]
  dsimp [base,floor,ref] at he ht hz hA
  norm_num [FrameHighArc.u,FrameHighArc.v] at he
  nlinarith [Arithmetic.pi_hand_enclosure.1,diagonal_precise.1]

theorem upper_value : (4417/5000:ℝ)<upperF (11/100) := by
  have ht := taylor_bounds false
  have hz := height_bounds false
  have hA := primary_upper false
  have he : FrameHighArc.v*cap false=base false-floor false := by
    dsimp [cap]
    field_simp
    norm_num [FrameHighArc.v]
  dsimp [upperF,G,FrameHighArc.u,FrameHighArc.v]
  dsimp [base,floor,ref] at he ht hz hA
  norm_num [FrameHighArc.u,FrameHighArc.v] at he
  nlinarith [Arithmetic.pi_hand_enclosure.1,diagonal_precise.2]

theorem normal_trig : (5737/50000:ℝ)<Real.sin (23/200) ∧
    Real.sin (23/200)<459/4000 ∧ (99339/100000:ℝ)<Real.cos (23/200) ∧
      Real.cos (23/200)<4967/5000 := by
  have ht := taylor_bounds true
  norm_num [sl,su,cl,cu,ref,HighOrderTaylor.S11,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at ht
  refine ⟨?_,?_,?_,?_⟩ <;> linarith [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]

theorem normal_height : (8917/10000:ℝ)<Z (23/200) ∧ Z (23/200)<4459/5000 := by
  have hz := height_bounds true
  have hl : (8917/10000:ℝ)<zl true := by
    norm_num [zl,sl,su,cl,cu,ref,HighOrderTaylor.S11,
      Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]
  have hu : zu true<(4459/5000:ℝ) := by
    norm_num [zu,sl,su,cl,cu,ref,HighOrderTaylor.S11,
      Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]
  exact ⟨by simpa [ref] using hl.trans_le hz.1,by simpa [ref] using hz.2.trans_lt hu⟩

theorem normal_primary_shift : (281/200:ℝ)<A (Z (23/200))+1/2 ∧
    A (Z (23/200))+1/2<176/125 := by
  have hx : (23/200:ℝ)∈domain := by constructor <;> norm_num [domain]
  have hc := extended_circle (Z_extended hx)
  have hp := extended_shift_pos (Z_extended hx)
  have hz := normal_height
  have hzl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤13917/10000)
    (show (13917/10000:ℝ)≤Z (23/200)+1/2 by linarith) 2
  have hzu := pow_le_pow_left₀ (show 0≤Z (23/200)+1/2 by linarith)
    (show Z (23/200)+1/2≤6959/5000 by linarith) 2
  norm_num [Q0] at hc
  constructor
  · by_contra! hbad
    have hh := pow_le_pow_left₀ hp.le hbad 2
    nlinarith
  · by_contra! hbad
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤176/125) hbad 2
    nlinarith

theorem normal_marker : (1907/2000:ℝ)<Hd (Z (23/200)) ∧ Hd (Z (23/200))<9553/10000 := by
  have hz := normal_height
  have ha := normal_primary_shift
  have hp : 0<A (Z (23/200))+1/2 := by linarith [ha.1]
  have hrL : (247/250:ℝ)<slope (Z (23/200)) := by
    apply (lt_div_iff₀ hp).2
    linarith [hz.1,ha.2]
  have hrU : slope (Z (23/200))<991/1000 := by
    apply (div_lt_iff₀ hp).2
    linarith [hz.2,ha.1]
  dsimp [Hd,FrameHighArc.u,FrameHighArc.v]
  constructor <;> linarith

theorem normal_P : (193/200:ℝ)<P (23/200) ∧ P (23/200)<967/1000 := by
  have ht := normal_trig
  have hlo := mul_le_mul
    (show (914575670/1000000000:ℝ)≤a0-1/2 by linarith [a0_precise.1]) ht.2.2.1.le
    (by norm_num : (0:ℝ)≤99339/100000) (by linarith [a0_precise.1] : 0≤a0-1/2)
  have hhi := mul_le_mul
    (show a0-1/2≤914575672/1000000000 by linarith [a0_precise.2]) ht.2.2.2.le
    (by linarith [ht.2.2.1] : 0≤Real.cos (23/200)) (by norm_num : (0:ℝ)≤914575672/1000000000)
  dsimp [P]
  constructor <;> nlinarith

theorem normal_derivative : |normalD (23/200)|<3/1000 := by
  have ht := normal_trig
  have hd := normal_marker
  have hp := normal_P
  have hlo := mul_le_mul hd.1.le hp.1.le (by norm_num : (0:ℝ)≤193/200)
    (by linarith [hd.1] : 0≤Hd (Z (23/200)))
  have hhi := mul_le_mul hd.2.le hp.2.le (by linarith [hp.1] : 0≤P (23/200))
    (by norm_num : (0:ℝ)≤9553/10000)
  rw [abs_lt]
  dsimp [normalD]
  constructor <;> nlinarith

theorem upper_derivative : upperD (11/100)<0 := by
  have hx : (11/100:ℝ)∈upperDomain := by constructor <;> norm_num [upperDomain]
  have hz := upper_chart hx
  have hp : 0<A (Z (11/100))+1/2 := by linarith [hz.2.2.1]
  have hr : (199/200:ℝ)<slope (Z (11/100)) := by
    apply (lt_div_iff₀ hp).2
    linarith [endpoint_heights.1,hz.2.2.2]
  have hG : (479/500:ℝ)<Gd (Z (11/100)) := by
    dsimp [Gd,FrameHighArc.u,FrameHighArc.v]
    linarith
  have ht := FrameHighLowDiagonalCurve.final_trig
  have hAc := mul_le_mul
    (show (914575670/1000000000:ℝ)≤a0-1/2 by linarith [a0_precise.1]) ht.2.2.1.le
    (by norm_num : (0:ℝ)≤99395609/100000000) (by linarith [a0_precise.1] : 0≤a0-1/2)
  have hP : (963/1000:ℝ)<P (11/100) := by dsimp [P]; nlinarith [ht.1]
  have hprod := mul_le_mul hG.le hP.le (by norm_num : (0:ℝ)≤963/1000)
    (by linarith : 0≤Gd (Z (11/100)))
  dsimp [upperD]
  nlinarith [ht.2.1,ht.2.2.1]

end SquaresInCircles.Eight.TableFree.FrameHighLowAxialReferences
