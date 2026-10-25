module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeEarlyMinorant
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeSourceSlope

/-!
# Eight squares: positive original derivative at the moving source `0.35` cut

The exact quotient curvature is bounded above by four positive
terms.  The negative target-label term dominates their sum on the
whole early arc, giving a strictly concave derivative.  Its two
actual endpoint values therefore prove positivity everywhere.
-/

section
/-!
## Exact endpoint references for a fixed-source circle rotation

At a named angle, Taylor brackets for sine and cosine first bracket
the one actual circle radical by squaring.  The displayed arithmetic
then brackets the rotation and its first two velocities.  This lemma
does not assert a bound on a grid or on a family of boxes.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.SourceReference

open CommonQuarter CorePairGeometry Arithmetic SourceCurve

lemma quotient_interval {n d nl nh dl dh : ℝ}
    (hn : n∈Icc nl nh) (hd : d∈Icc dl dh) (hnl : 0≤nl) (hdl : 0<dl) :
    n/d∈Icc (nl/dh) (nh/dl) := by
  have hdp : 0<d := hdl.trans_le hd.1
  have hdh : 0<dh := hdp.trans_le hd.2
  have hnp : 0≤n := hnl.trans hn.1
  have hnh : 0≤nh := hnp.trans hn.2
  constructor
  · apply (div_le_div_iff₀ hdh hdp).2
    exact mul_le_mul hn.1 hd.2 hdp.le hnp
  · apply (div_le_div_iff₀ hdp hdl).2
    exact mul_le_mul hn.2 hd.1 hdl.le hnh

def uLo (k sl cl yl : ℝ) : ℝ := (k+sl)*sl+yl*cl
def uHi (k sh ch yh : ℝ) : ℝ := (k+sh)*sh+yh*ch
def wLo (k sl sh ch yl : ℝ) : ℝ := yl*sl-(k+sh)*ch
def wHi (k sl sh cl yh : ℝ) : ℝ := yh*sh-(k+sl)*cl
def fLo (ch yl : ℝ) : ℝ := 1-ch/yl
def fHi (cl yh : ℝ) : ℝ := 1-cl/yh
def nLo (k sl sh : ℝ) : ℝ := sl*(Q0-1-k^2)-k*(1+sh^2)
def nHi (k sl sh : ℝ) : ℝ := sh*(Q0-1-k^2)-k*(1+sl^2)
def fpLo (k sl sh yh : ℝ) : ℝ := nLo k sl sh/yh^3
def fpHi (k sl sh yl : ℝ) : ℝ := nHi k sl sh/yl^3

lemma radical {k φ sl sh yl yh : ℝ} (h : Domain k φ)
    (hs : Real.sin φ∈Icc sl sh) (hzl : 0≤k+sl)
    (hyl : 0≤yl) (hyh : 0≤yh)
    (hlo : yl^2+(k+sh)^2<Q0) (hhi : Q0<yh^2+(k+sl)^2) :
    yl<y k φ ∧ y k φ<yh := by
  have hz : z k φ∈Icc (k+sl) (k+sh) := by
    dsimp [z]
    exact ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hz0 := hzl.trans hz.1
  have hzl2 := pow_le_pow_left₀ hzl hz.1 2
  have hzh2 := pow_le_pow_left₀ hz0 hz.2 2
  have hy := y_data h
  constructor <;> nlinarith

theorem curve {k φ sl sh cl ch yl yh : ℝ}
    (h : Domain k φ) (hk : 0≤k)
    (hs : Real.sin φ∈Icc sl sh) (hc : Real.cos φ∈Icc cl ch)
    (hsl : 0≤ sl) (hcl : 0≤cl) (hyl : 0<yl) (hyh : 0≤yh)
    (hlo : yl^2+(k+sh)^2<Q0) (hhi : Q0<yh^2+(k+sl)^2)
    (hn : 0≤nLo k sl sh) :
    y k φ∈Icc yl yh ∧
      u k φ∈Icc (uLo k sl cl yl) (uHi k sh ch yh) ∧
      w k φ∈Icc (wLo k sl sh ch yl) (wHi k sl sh cl yh) ∧
      SecondWord.PositiveThree.SourceCurve.f k φ∈Icc (fLo ch yl) (fHi cl yh) ∧
      fp k φ∈Icc (fpLo k sl sh yh) (fpHi k sl sh yl) := by
  have hy' := radical h hs (by linarith) hyl.le hyh hlo hhi
  have hy : y k φ∈Icc yl yh := ⟨hy'.1.le,hy'.2.le⟩
  have hz : z k φ∈Icc (k+sl) (k+sh) := by
    dsimp [z]
    exact ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hzlo : 0≤k+sl := by linarith
  have hz0 := hzlo.trans hz.1
  have hzhi := hz0.trans hz.2
  have hs0 := hsl.trans hs.1
  have hsh := hs0.trans hs.2
  have hc0 := hcl.trans hc.1
  have hch := hc0.trans hc.2
  have hy0 := hyl.le.trans hy.1
  have hu1 := mul_le_mul hz.1 hs.1 hsl hz0
  have hu2 := mul_le_mul hz.2 hs.2 hs0 hzhi
  have hu3 := mul_le_mul hy.1 hc.1 hcl hy0
  have hu4 := mul_le_mul hy.2 hc.2 hc0 hyh
  have hw1 := mul_le_mul hy.1 hs.1 hsl hy0
  have hw2 := mul_le_mul hy.2 hs.2 hs0 hyh
  have hw3 := mul_le_mul hz.1 hc.1 hcl hz0
  have hw4 := mul_le_mul hz.2 hc.2 hc0 hzhi
  have hf := quotient_interval hc hy hcl hyl
  have hk2 : k^2≤(1/4:ℝ) := by nlinarith [h.1.2]
  have hq : 0≤Q0-1-k^2 := by norm_num [Q0]; linarith
  have hs2lo := pow_le_pow_left₀ hsl hs.1 2
  have hs2hi := pow_le_pow_left₀ hs0 hs.2 2
  have hn1 := mul_le_mul_of_nonneg_right hs.1 hq
  have hn2 := mul_le_mul_of_nonneg_right hs.2 hq
  have hn3 := mul_le_mul_of_nonneg_left hs2lo hk
  have hn4 := mul_le_mul_of_nonneg_left hs2hi hk
  have hnum : Real.sin φ*(Q0-1-k^2)-k*(1+(Real.sin φ)^2)∈
      Icc (nLo k sl sh) (nHi k sl sh) := by
    dsimp [nLo,nHi]
    constructor <;> nlinarith
  have hden : (y k φ)^3∈Icc (yl^3) (yh^3) :=
    ⟨pow_le_pow_left₀ hyl.le hy.1 3,pow_le_pow_left₀ hy0 hy.2 3⟩
  have hfp := quotient_interval hnum hden hn (pow_pos hyl 3)
  refine ⟨hy,?_,?_,?_,?_⟩
  · dsimp [u,uLo,uHi]
    constructor <;> linarith
  · dsimp [w,wLo,wHi]
    constructor <;> linarith
  · dsimp [SecondWord.PositiveThree.SourceCurve.f,fLo,fHi]
    constructor <;> linarith [hf.1,hf.2]
  · exact hfp

end SquaresInCircles.Eight.SecondWord.PositiveThree.SourceReference
end
end
end

section
/-!
## The two actual endpoints of the source `0.35` contact

The first endpoint is the original lower angle `pi/2-0.7`; its
trigonometric references are therefore those of `0.7`.  The other
endpoint is `1.3`.  All coordinate cages below follow by squaring the
same circle radical.  Both original contact derivatives are positive.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.EarlyCut

open CommonQuarter CorePairGeometry Arithmetic SourceCurve

def parameter : ℝ := 3/20
def Domain (φ : ℝ) : Prop := φ∈Icc lowerAngle (13/10)

lemma parameter_mem : parameter∈Icc (-2/5:ℝ) (1/2) := by norm_num [parameter]
lemma parameter_nonnegative : parameter∈Icc (0:ℝ) (1/2) := by norm_num [parameter]
lemma domain {φ : ℝ} (hφ : Domain φ) : SourceCurve.Domain parameter φ :=
  ⟨parameter_mem,Early.early_lower hφ⟩
lemma left_mem : Domain lowerAngle := ⟨le_rfl,Early.end_mem.1⟩
lemma right_mem : Domain (13/10) := Early.end_mem

lemma left_trig :
    Real.sin lowerAngle∈Icc (76484218/10^8:ℝ) (76484219/10^8) ∧
      Real.cos lowerAngle∈Icc (64421768/10^8:ℝ) (64421769/10^8) := by
  have ht := PointProducts.trig (show (0:ℝ)≤7/10 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  simp only [lowerAngle,Real.sin_sub,Real.cos_sub,Real.sin_pi_div_two,
    Real.cos_pi_div_two,one_mul,zero_mul,sub_zero,zero_add]
  exact ⟨⟨by linarith [ht.2.1],by linarith [ht.2.2]⟩,
    ⟨by linarith [ht.1.1],by linarith [ht.1.2]⟩⟩

lemma right_trig :
    Real.sin (13/10)∈Icc (96355818/10^8:ℝ) (96355863/10^8) ∧
      Real.cos (13/10)∈Icc (26749878/10^8:ℝ) (26749883/10^8) := by
  have ht := PointProducts.trig (show (0:ℝ)≤13/10 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  exact ⟨⟨by linarith [ht.1.1],by linarith [ht.1.2]⟩,
    ⟨by linarith [ht.2.1],by linarith [ht.2.2]⟩⟩

lemma left_curve :
    y parameter lowerAngle∈Icc (175461213/10^8:ℝ) (175461215/10^8) ∧
      u parameter lowerAngle∈Icc (18300620/10^7:ℝ) (18300622/10^7) ∧
      w parameter lowerAngle∈Icc (7526438/10^7:ℝ) (7526440/10^7) ∧
      SecondWord.PositiveThree.SourceCurve.f parameter lowerAngle∈Icc (6328/10000:ℝ) (6329/10000) ∧
      fp parameter lowerAngle∈Icc (3656/10000:ℝ) (3657/10000) := by
  have hh := SourceReference.curve (domain left_mem) parameter_nonnegative.1
    left_trig.1 left_trig.2
    (yl := (175461213/10^8:ℝ)) (yh := (175461215/10^8:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [parameter,Q0]) (by norm_num [parameter,Q0])
    (by norm_num [SourceReference.nLo,parameter,Q0])
  norm_num [SourceReference.uLo,SourceReference.uHi,SourceReference.wLo,
    SourceReference.wHi,SourceReference.fLo,SourceReference.fHi,
    SourceReference.fpLo,SourceReference.fpHi,SourceReference.nLo,
    SourceReference.nHi,parameter,Q0] at hh
  rw [show parameter=(3/20:ℝ) from rfl]
  exact ⟨⟨by linarith [hh.1.1],by linarith [hh.1.2]⟩,
    ⟨by linarith [hh.2.1.1],by linarith [hh.2.1.2]⟩,
    ⟨by linarith [hh.2.2.1.1],by linarith [hh.2.2.1.2]⟩,
    ⟨by linarith [hh.2.2.2.1.1],by linarith [hh.2.2.2.1.2]⟩,
    ⟨by linarith [hh.2.2.2.2.1],by linarith [hh.2.2.2.2.2]⟩⟩

lemma right_curve :
    y parameter (13/10)∈Icc (163572221/10^8:ℝ) (163572253/10^8) ∧
      u parameter (13/10)∈Icc (15105317/10^7:ℝ) (15105330/10^7) ∧
      w parameter (13/10)∈Icc (12782378/10^7:ℝ) (12782392/10^7) ∧
      SecondWord.PositiveThree.SourceCurve.f parameter (13/10)∈Icc (8364/10000:ℝ) (8365/10000) ∧
      fp parameter (13/10)∈Icc (5708/10000:ℝ) (5709/10000) := by
  have hh := SourceReference.curve (domain right_mem) parameter_nonnegative.1
    right_trig.1 right_trig.2
    (yl := (163572221/10^8:ℝ)) (yh := (163572253/10^8:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [parameter,Q0]) (by norm_num [parameter,Q0])
    (by norm_num [SourceReference.nLo,parameter,Q0])
  norm_num [SourceReference.uLo,SourceReference.uHi,SourceReference.wLo,
    SourceReference.wHi,SourceReference.fLo,SourceReference.fHi,
    SourceReference.fpLo,SourceReference.fpHi,SourceReference.nLo,
    SourceReference.nHi,parameter,Q0] at hh
  rw [show parameter=(3/20:ℝ) from rfl]
  exact ⟨⟨by linarith [hh.1.1],by linarith [hh.1.2]⟩,
    ⟨by linarith [hh.2.1.1],by linarith [hh.2.1.2]⟩,
    ⟨by linarith [hh.2.2.1.1],by linarith [hh.2.2.1.2]⟩,
    ⟨by linarith [hh.2.2.2.1.1],by linarith [hh.2.2.2.1.2]⟩,
    ⟨by linarith [hh.2.2.2.2.1],by linarith [hh.2.2.2.2.2]⟩⟩

lemma left_target : target parameter lowerAngle∈Icc 0 outerDiagonal := by
  have hw := left_curve.2.2.1
  dsimp [target]
  constructor <;> linarith [hw.1,hw.2,fine_outer_endpoint_bounds.2]

lemma right_target : target parameter (13/10)∈Icc 0 outerDiagonal := by
  have hw := right_curve.2.2.1
  dsimp [target]
  constructor <;> linarith [hw.1,hw.2,fine_outer_endpoint_bounds.2]

lemma source_first : (219/250:ℝ)<VLabel.d1 (7/20) ∧ VLabel.d1 (7/20)<877/1000 := by
  apply VLabel.first_chart_reference (outer_domain V_short_mem)
    (l := (17869247326/10^10:ℝ)) (u := (17869247327/10^10:ℝ)) <;>
    norm_num [VLabel,Q0,W]

lemma left_slope : 0<slope (VLabel.d1 (7/20)) parameter lowerAngle := by
  have hh := left_curve
  have hB : target parameter lowerAngle∈Icc (2526438/10^7:ℝ) (2526440/10^7) := by
    dsimp [target]
    constructor <;> linarith [hh.2.2.1.1,hh.2.2.1.2]
  have hU : U (target parameter lowerAngle)∈Icc
      (18300620/10^7:ℝ) (18300622/10^7) := by
    rw [target_U (domain left_mem) left_target]
    exact hh.2.1
  have hL := LReference.target left_target hB hU (by norm_num) (by norm_num)
  have hq := SourceReference.quotient_interval hh.1 hh.2.1 (by norm_num) (by norm_num)
  have hprod := mul_le_mul source_first.1.le hq.1
    (by norm_num : (0:ℝ)≤(175461213/10^8)/(18300622/10^7))
    (by linarith [source_first.1] : 0≤VLabel.d1 (7/20))
  have hLhi := hL.2.2.2.1
  norm_num [LReference.firstHi,Q0] at hLhi hprod
  dsimp only [SourceCurve.slope,quotient]
  linarith

lemma right_slope : 0<slope (VLabel.d1 (7/20)) parameter (13/10) := by
  have hh := right_curve
  have hB : target parameter (13/10)∈Icc (7782378/10^7:ℝ) (7782392/10^7) := by
    dsimp [target]
    constructor <;> linarith [hh.2.2.1.1,hh.2.2.1.2]
  have hU : U (target parameter (13/10))∈Icc
      (15105317/10^7:ℝ) (15105330/10^7) := by
    rw [target_U (domain right_mem) right_target]
    exact hh.2.1
  have hL := LReference.target right_target hB hU (by norm_num) (by norm_num)
  have hq := SourceReference.quotient_interval hh.1 hh.2.1 (by norm_num) (by norm_num)
  have hprod := mul_le_mul source_first.1.le hq.1
    (by norm_num : (0:ℝ)≤(163572221/10^8)/(15105330/10^7))
    (by linarith [source_first.1] : 0≤VLabel.d1 (7/20))
  have hLhi := hL.2.2.2.1
  norm_num [LReference.firstHi,Q0] at hLhi hprod
  dsimp only [SourceCurve.slope,quotient]
  linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree.EarlyCut
end
end
end

section
/-!
## Whole-arc geometry of the source `0.35` contact

Monotonicity transfers the two actual endpoint references to the
entire angle interval.  The target-label curvature bounds come from
its monotone second and third derivatives at the two ends of the
resulting target arc.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.EarlyCut

open CommonQuarter CorePairGeometry Arithmetic SourceCurve

lemma geometry {φ : ℝ} (hφ : Domain φ) :
    u parameter φ∈Icc (151/100:ℝ) (1831/1000) ∧
      w parameter φ∈Icc (94/125:ℝ) (1279/1000) ∧
      y parameter φ∈Icc (327/200:ℝ) (351/200) ∧
      SecondWord.PositiveThree.SourceCurve.f parameter φ∈Icc (79/125:ℝ) (837/1000) ∧
      fp parameter φ∈Icc (73/200:ℝ) (571/1000) := by
  have hp := (domain hφ).2
  have hl := (domain left_mem).2
  have hr := (domain right_mem).2
  have hul := u_antitone parameter_mem hp hr hφ.2
  have huh := u_antitone parameter_mem hl hp hφ.1
  have hyl := y_antitone parameter_mem hp hr hφ.2
  have hyh := y_antitone parameter_mem hl hp hφ.1
  have hwl := target_monotone parameter_mem hl hp hφ.1
  have hwh := target_monotone parameter_mem hp hr hφ.2
  dsimp [target] at hwl hwh
  have hfl := f_monotone parameter_mem hl hp hφ.1
  have hfh := f_monotone parameter_mem hp hr hφ.2
  have hfpl := fp_monotone parameter_nonnegative hl hp hφ.1
  have hfph := fp_monotone parameter_nonnegative hp hr hφ.2
  have hleft := left_curve
  have hright := right_curve
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    linarith [hleft.1.1,hleft.1.2,hleft.2.1.1,hleft.2.1.2,
      hleft.2.2.1.1,hleft.2.2.1.2,hleft.2.2.2.1.1,hleft.2.2.2.1.2,
      hleft.2.2.2.2.1,hleft.2.2.2.2.2,
      hright.1.1,hright.1.2,hright.2.1.1,hright.2.1.2,
      hright.2.2.1.1,hright.2.2.1.2,hright.2.2.2.1.1,hright.2.2.2.1.2,
      hright.2.2.2.2.1,hright.2.2.2.2.2]

lemma target_bounds {φ : ℝ} (hφ : Domain φ) :
    target parameter φ∈Icc (63/250:ℝ) (779/1000) := by
  have hw := (geometry hφ).2.1
  dsimp [target]
  constructor <;> linarith [hw.1,hw.2]

lemma target_mem {φ : ℝ} (hφ : Domain φ) : target parameter φ∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem
    ⟨by linarith [(target_bounds hφ).1],by linarith [(target_bounds hφ).2]⟩

lemma velocities {φ : ℝ} (hφ : Domain φ) :
    (151/100:ℝ)*(79/125)≤bp parameter φ ∧
      bpp parameter φ∈Icc (-(69/200:ℝ)) (373/500) := by
  have hh := geometry hφ
  have hu := hh.1
  have hw := hh.2.1
  have hf := hh.2.2.2.1
  have hfp := hh.2.2.2.2
  have hu0 : 0≤u parameter φ := by linarith [hu.1]
  have hw0 : 0≤w parameter φ := by linarith [hw.1]
  have hf0 : 0≤SecondWord.PositiveThree.SourceCurve.f parameter φ := by linarith [hf.1]
  have hfp0 : 0≤fp parameter φ := by linarith [hfp.1]
  have hflow := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤79/125) hf.1 2
  have hfhigh := pow_le_pow_left₀ hf0 hf.2 2
  have htermlo := mul_le_mul hw.1 hflow
    (by norm_num : (0:ℝ)≤(79/125)^2) hw0
  have htermhi := mul_le_mul hw.2 hfhigh (sq_nonneg _) (by norm_num : (0:ℝ)≤1279/1000)
  have hupLo := mul_le_mul hu.1 hfp.1 (by norm_num : (0:ℝ)≤73/200) hu0
  have hupHi := mul_le_mul hu.2 hfp.2 hfp0 (by norm_num : (0:ℝ)≤1831/1000)
  have hbp := mul_le_mul hu.1 hf.1 (by norm_num : (0:ℝ)≤79/125) hu0
  dsimp [bp,bpp]
  exact ⟨hbp,⟨by nlinarith,by nlinarith⟩⟩

lemma target_left_mem : (63/250:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)
lemma target_right_mem : (779/1000:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma target_left_curvature :
    (-(567/500:ℝ))<LLabel.d2 (63/250) ∧ (383/100:ℝ)<LLabel.d3 (63/250) := by
  have hU := shifted_chart_reference (outer_domain target_left_mem)
    (l := (18303267467/10^10:ℝ)) (u := (18303267468/10^10:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0,W]) (by norm_num [Q0,W])
  have hL := LReference.target target_left_mem
    (show (63/250:ℝ)∈Icc (63/250) (63/250) from ⟨le_rfl,le_rfl⟩)
    ⟨hU.1.le,hU.2.le⟩ (by norm_num) (by norm_num)
  have hLlo := hL.2.2.2.2.1
  norm_num [LReference.secondLo,Q0] at hLlo
  have he := LLabel.third_numerator (outer_domain target_left_mem)
  have hp := pow_pos (U_positive (outer_domain target_left_mem)) 5
  have hpower := pow_le_pow_left₀ (U_positive (outer_domain target_left_mem)).le hU.2.le 5
  have hcomp := mul_le_mul_of_nonneg_left hpower (by norm_num : (0:ℝ)≤383/100)
  rw [show LLabel.s=-189442/100000 from rfl,show LLabel.p=0 from rfl] at he
  norm_num [W,Q0] at he hcomp
  constructor
  · linarith
  · nlinarith

lemma target_right_curvature : LLabel.d2 (779/1000)<(19/10:ℝ) := by
  have hU := shifted_chart_reference (outer_domain target_right_mem)
    (l := (15098870818/10^10:ℝ)) (u := (15098870819/10^10:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0,W]) (by norm_num [Q0,W])
  have hL := LReference.target target_right_mem
    (show (779/1000:ℝ)∈Icc (779/1000) (779/1000) from ⟨le_rfl,le_rfl⟩)
    ⟨hU.1.le,hU.2.le⟩ (by norm_num) (by norm_num)
  have hLhi := hL.2.2.2.2.2
  norm_num [LReference.secondHi,Q0] at hLhi
  linarith

lemma label_curvature {φ : ℝ} (hφ : Domain φ) :
    LLabel.d2 (target parameter φ)∈Icc (-(567/500:ℝ)) (19/10) ∧
      (383/100:ℝ)<LLabel.d3 (target parameter φ) := by
  have hb := target_bounds hφ
  have ht := target_mem hφ
  have hlow := L_second_monotone target_left_mem ht hb.1
  have hhigh := L_second_monotone ht target_right_mem hb.2
  have hthird := L_third_monotone target_left_mem ht hb.1
  exact ⟨⟨by linarith [target_left_curvature.1],
    by linarith [target_right_curvature]⟩,
    target_left_curvature.2.trans_le hthird⟩

lemma sine_upper {φ : ℝ} (hφ : Domain φ) : Real.sin φ≤(241/250:ℝ) := by
  have hm := lower_sin_monotone (domain hφ).2 (domain right_mem).2 hφ.2
  linarith [right_trig.1.2]

lemma z_upper {φ : ℝ} (hφ : Domain φ) : z parameter φ≤(557/500:ℝ) := by
  dsimp [z,parameter]
  linarith [sine_upper hφ]

end SquaresInCircles.Eight.SecondWord.PositiveThree.EarlyCut
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.EarlyCut

open CommonQuarter CorePairGeometry Arithmetic SourceCurve

private lemma div_upper {n d nh dl : ℝ} (hn : n≤nh) (hd : dl≤d)
    (hnh : 0≤nh) (hdl : 0<dl) : n/d≤nh/dl := by
  have hdp := hdl.trans_le hd
  exact (div_le_div_iff₀ hdp hdl).2 (mul_le_mul hn hd hdl.le hnh)

lemma quotient_curvature {φ : ℝ} (hφ : Domain φ) :
    quotientSecond parameter φ<(149/50:ℝ) := by
  have hh := geometry hφ
  have hu := hh.1
  have hw := hh.2.1
  have hy := hh.2.2.1
  have hf := hh.2.2.2.1
  have hfp := hh.2.2.2.2
  have hu0 : 0≤u parameter φ := by linarith [hu.1]
  have hw0 : 0≤w parameter φ := by linarith [hw.1]
  have hy0 : 0≤y parameter φ := by linarith [hy.1]
  have hf0 : 0≤SecondWord.PositiveThree.SourceCurve.f parameter φ := by linarith [hf.1]
  have hfp0 : 0≤fp parameter φ := by linarith [hfp.1]
  have hs0 : 0≤Real.sin φ := by linarith [(lower_trig (domain hφ).2).1]
  have hf2 := pow_le_pow_left₀ hf0 hf.2 2
  have hw2 := pow_le_pow_left₀ hw0 hw.2 2
  have hu2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤151/100) hu.1 2
  have hu3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤151/100) hu.1 3
  have hn1 := mul_le_mul (z_upper hφ) (sine_upper hφ) hs0
    (by norm_num : (0:ℝ)≤557/500)
  have hd1 := mul_le_mul hy.1 hu.1 (by norm_num : (0:ℝ)≤151/100) hy0
  have ht1 := div_upper hn1 hd1 (by norm_num) (by norm_num)
  have hn2 := mul_le_mul hy.2 hf2 (sq_nonneg _) (by norm_num : (0:ℝ)≤351/200)
  have ht2 := div_upper hn2 hu.1 (by norm_num) (by norm_num)
  have hyw := mul_le_mul hy.2 hw.2 hw0 (by norm_num : (0:ℝ)≤351/200)
  have hn3 := mul_le_mul hyw hfp.2 hfp0
    (by norm_num : (0:ℝ)≤(351/200)*(1279/1000))
  have ht3 := div_upper hn3 hu2 (by norm_num) (by norm_num)
  have hyw2 := mul_le_mul (mul_le_mul_of_nonneg_left hy.2 (by norm_num : (0:ℝ)≤2))
    hw2 (sq_nonneg _) (by norm_num : (0:ℝ)≤2*(351/200))
  have hn4 := mul_le_mul hyw2 hf2 (sq_nonneg _)
    (by norm_num : (0:ℝ)≤2*(351/200)*(1279/1000)^2)
  have ht4 := div_upper hn4 hu3 (by norm_num) (by norm_num)
  have hsum := quotientSecond_le (domain hφ)
  dsimp [quotientUpper] at hsum
  norm_num at ht1 ht2 ht3 ht4
  linarith

lemma slope_curvature {φ : ℝ} (hφ : Domain φ) :
    slopeSecond (VLabel.d1 (7/20)) parameter φ< -(27/1000:ℝ) := by
  have hquot := quotient_curvature hφ
  have hg0 : 0≤VLabel.d1 (7/20) := by linarith [source_first.1]
  have hq1 := mul_le_mul_of_nonneg_left hquot.le hg0
  have hq2 := mul_lt_mul_of_pos_right source_first.2
    (by norm_num : (0:ℝ)<149/50)
  have hvel := velocities hφ
  have hlabel := label_curvature hφ
  have hbp2 := pow_le_pow_left₀
    (by norm_num : (0:ℝ)≤(151/100)*(79/125)) hvel.1 2
  have hlabel0 : 0≤LLabel.d3 (target parameter φ) := by linarith [hlabel.2]
  have hthird := mul_le_mul hlabel.2.le hbp2
    (by norm_num : (0:ℝ)≤((151/100)*(79/125))^2) hlabel0
  have hlast := opposite_product_upper hlabel.1 hvel.2
  dsimp [slopeSecond]
  nlinarith

lemma slope_concave : ConcaveOn ℝ (Icc lowerAngle (13/10))
    (slope (VLabel.d1 (7/20)) parameter) :=
  concave_of_deriv2
    (fun φ hφ => slope_hasDerivAt _ (domain hφ) (target_mem hφ))
    (fun φ hφ => slopeFirst_hasDerivAt _ (domain hφ) (target_mem hφ))
    (fun φ hφ => by linarith [slope_curvature hφ])

theorem slope_positive {φ : ℝ} (hφ : Domain φ) :
    0<slope (VLabel.d1 (7/20)) parameter φ := by
  have hh := slope_concave.min_le_of_mem_Icc left_mem right_mem hφ
  exact (lt_min left_slope right_slope).trans_le hh

theorem original_derivative {φ : ℝ} (hφ : Domain φ) :
    0<FirstContact.first (target parameter φ) φ := by
  have he := original_slope (domain hφ) (target_mem hφ)
  have hk : (1/2:ℝ)-parameter=7/20 := by norm_num [parameter]
  rw [hk] at he
  rw [he]
  exact slope_positive hφ

end SquaresInCircles.Eight.SecondWord.PositiveThree.EarlyCut
end
end
end
