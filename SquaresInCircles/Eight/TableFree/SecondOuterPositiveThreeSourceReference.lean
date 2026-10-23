module

public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeSourceSlope
public import SquaresInCircles.Eight.TableFree.SecondOuterPointProducts

/-!
# Exact endpoint references for a fixed-source circle rotation

At a named angle, Taylor brackets for sine and cosine first bracket
the one actual circle radical by squaring.  The displayed arithmetic
then brackets the rotation and its first two velocities.  This lemma
does not assert a bound on a grid or on a family of boxes.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree.SourceReference

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
    (hsl : 0≤sl) (hcl : 0≤cl) (hyl : 0<yl) (hyh : 0≤yh)
    (hlo : yl^2+(k+sh)^2<Q0) (hhi : Q0<yh^2+(k+sl)^2)
    (hn : 0≤nLo k sl sh) :
    y k φ∈Icc yl yh ∧
      u k φ∈Icc (uLo k sl cl yl) (uHi k sh ch yh) ∧
      w k φ∈Icc (wLo k sl sh ch yl) (wHi k sl sh cl yh) ∧
      f k φ∈Icc (fLo ch yl) (fHi cl yh) ∧
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
  · dsimp [f,fLo,fHi]
    constructor <;> linarith [hf.1,hf.2]
  · exact hfp

end SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree.SourceReference
