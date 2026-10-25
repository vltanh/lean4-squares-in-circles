module

public import SquaresInCircles.Eight.TableFree.FrameMidHighVaryingCalculus
public import SquaresInCircles.Eight.TableFree.StationaryIntervalAlgebra
public import SquaresInCircles.Eight.TableFree.HighOrderTaylor
public import SquaresInCircles.Eight.TableFree.SecondOuterReferenceTrig

/-!
# Fixed references for the two complete varying supports

The norm bounds are positive square comparisons at the four geometric
endpoints and the single tangent reference `14/25`.  Ordered-field
interval operations substitute the actual circle endpoint, radius,
Taylor bounds and π enclosure into the actual value and derivatives.
There is no interval subdivision, sampled sign, or root-location input.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameMidHighVaryingReferences
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameMidHighVaryingCalculus
open StationaryPrimitives (Interval)

def aBox : Interval a2 := Interval.of_bounds ⟨a2_precise.1.le,a2_precise.2.le⟩
def rBox : Interval R := Interval.of_bounds ⟨R_precise.1.le,R_precise.2.le⟩
def piBox : Interval Real.pi := Interval.of_bounds
  ⟨Arithmetic.pi_hand_enclosure.1.le,Arithmetic.pi_hand_enclosure.2.le⟩
def bBox : Interval b2 := by
  convert (Interval.point (3/5:ℝ)).mul aBox using 1
  exact b2_eq
def xBox : Interval X := ((Interval.point 1).add aBox).sub bBox
def yBox : Interval Y := ((Interval.point 1).sub aBox).sub bBox

def markerBox : Interval M2 := by
  let h := (((piBox.div (Interval.point 4) (by norm_num [Interval.point])).add (Interval.point (85723/40000))).sub ((Interval.point k).mul aBox)).add ((Interval.point q).mul bBox)
  convert h using 1
  simp only [M2,M,A_b2,cM]

def sinBox {x : ℝ} (hx : 0≤x) : Interval (Real.sin x) :=
  Interval.of_bounds ⟨HighOrderTaylor.S11_le_sin hx,Arithmetic.sin_le_sin9 hx⟩
def cosBox {x : ℝ} (hx : 0≤x) : Interval (Real.cos x) :=
  Interval.of_bounds ⟨Arithmetic.cos10_le_cos hx,SecondWord.ReferenceTrig.cos_le_cos12 hx⟩

structure SupportIntervals (i : Bool) (x : ℝ) where
  value : Interval (F i x)
  first : Interval (Fd i x)
  second : Interval (Fdd i x)

def supportIntervals (i : Bool) {x : ℝ} (hx : 0≤x)
    (Z : Interval (N i x)) (hZ : 0<Z.lo) : SupportIntervals i x := by
  let l := Interval.point (lam i x)
  let m' := Interval.point (m i)
  let s := sinBox hx
  let c := cosBox hx
  let small := Interval.point (9/100:ℝ)
  let two := Interval.point (2:ℝ)
  let n1 := (Interval.point (T i x)).div Z hZ
  let n2 := (Interval.point (Delta i)).div Z.cube (Interval.cube_lo_pos hZ)
  refine ⟨?_,?_,?_⟩
  · exact (((((((Interval.point x).add small).add markerBox).add (two.mul l)).sub ((Interval.point (sign i*u)).mul rBox)).add (((l.mul xBox).sub small).mul c)).add (((l.mul yBox).sub small).mul s)).sub (rBox.mul Z)
  · convert ((((Interval.point 1).sub (two.mul m')).add ((((l.mul yBox).sub small).sub (m'.mul xBox)).mul c)).add ((((l.mul xBox).neg.add small).sub (m'.mul yBox)).mul s)).sub (rBox.mul n1) using 1
    dsimp only [Fd,N1]; ring
  · convert (((((l.mul xBox).neg.add small).sub ((two.mul m').mul yBox)).mul c).add ((((l.mul yBox).neg.add small).add ((two.mul m').mul xBox)).mul s)).sub (rBox.mul n2) using 1
    dsimp only [Fdd,N2]; ring

theorem norm_reference {i : Bool} {x l h : ℝ} (hl : 0<l)
    (hlh : l<h)
    (hl2 : l^2<(lam i x-sign i*u)^2+(lam i x-v)^2)
    (hh2 : (lam i x-sign i*u)^2+(lam i x-v)^2<h^2) :
    N i x∈Icc l h := by
  have hn := N_pos i x
  have hs := N_sq i x
  constructor <;> nlinarith

def positiveLeftNorm : Interval (N true (1/10)) := Interval.of_bounds
  (norm_reference (l := (54881673/100000000:ℝ)) (h := (27440839/50000000:ℝ))
    (by norm_num) (by norm_num)
    (by norm_num [lam,origin,m,sign,u,v]) (by norm_num [lam,origin,m,sign,u,v]))
def positiveRightNorm : Interval (N true (21/50)) := Interval.of_bounds
  (norm_reference (l := (40288043/100000000:ℝ)) (h := (5036006/12500000:ℝ))
    (by norm_num) (by norm_num)
    (by norm_num [lam,origin,m,sign,u,v]) (by norm_num [lam,origin,m,sign,u,v]))
def negativeLeftNorm : Interval (N false (2/5)) := Interval.of_bounds
  (norm_reference (l := (58345669/100000000:ℝ)) (h := (29172837/50000000:ℝ))
    (by norm_num) (by norm_num)
    (by norm_num [lam,origin,m,sign,u,v]) (by norm_num [lam,origin,m,sign,u,v]))
def negativeRightNorm : Interval (N false (3/5)) := Interval.of_bounds
  (norm_reference (l := (51371303/100000000:ℝ)) (h := (12842827/25000000:ℝ))
    (by norm_num) (by norm_num)
    (by norm_num [lam,origin,m,sign,u,v]) (by norm_num [lam,origin,m,sign,u,v]))
def negativeTangentNorm : Interval (N false (14/25)) := Interval.of_bounds
  (norm_reference (l := (52678261/100000000:ℝ)) (h := (26339133/50000000:ℝ))
    (by norm_num) (by norm_num)
    (by norm_num [lam,origin,m,sign,u,v]) (by norm_num [lam,origin,m,sign,u,v]))

def positiveLeft := supportIntervals true (show (0:ℝ)≤1/10 by norm_num)
  positiveLeftNorm (by norm_num [positiveLeftNorm,Interval.of_bounds])
def positiveRight := supportIntervals true (show (0:ℝ)≤21/50 by norm_num)
  positiveRightNorm (by norm_num [positiveRightNorm,Interval.of_bounds])
def negativeLeft := supportIntervals false (show (0:ℝ)≤2/5 by norm_num)
  negativeLeftNorm (by norm_num [negativeLeftNorm,Interval.of_bounds])
def negativeRight := supportIntervals false (show (0:ℝ)≤3/5 by norm_num)
  negativeRightNorm (by norm_num [negativeRightNorm,Interval.of_bounds])
def negativeTangent := supportIntervals false (show (0:ℝ)≤14/25 by norm_num)
  negativeTangentNorm (by norm_num [negativeTangentNorm,Interval.of_bounds])

private lemma r40_prod {x y xl xh yl yh : ℝ} (hx : x ∈ Icc xl xh) (hy : y ∈ Icc yl yh)
    (h0 : 0 ≤ xl) (h1 : 0 ≤ yl) : xl*yl ≤ x*y ∧ x*y ≤ xh*yh :=
  ⟨mul_le_mul hx.1 hy.1 h1 (h0.trans hx.1),
    mul_le_mul hx.2 hy.2 (h1.trans hy.1) (h0.trans (hx.1.trans hx.2))⟩

private lemma r40_ratio {r n t rl rh nl nh : ℝ} (hr : r ∈ Icc rl rh) (hn : n ∈ Icc nl nh)
    (hr0 : 0 ≤ rl) (hn0 : 0 < nl) (ht : 0 ≤ t) :
    rl*(t/nh) ≤ r*(t/n) ∧ r*(t/n) ≤ rh*(t/nl) := by
  have hN0 : 0 < n := hn0.trans_le hn.1
  have h1 : t/nh ≤ t/n := div_le_div_of_nonneg_left ht hN0 hn.2
  have h2 : t/n ≤ t/nl := div_le_div_of_nonneg_left ht hn0 hn.1
  exact ⟨mul_le_mul hr.1 h1 (div_nonneg ht (hN0.le.trans hn.2)) (hr0.trans hr.1),
    mul_le_mul hr.2 h2 (div_nonneg ht hN0.le) (hr0.trans (hr.1.trans hr.2))⟩

private lemma r40_cube {n nl nh : ℝ} (hn : n ∈ Icc nl nh) (h0 : 0 ≤ nl) :
    n^3 ∈ Icc (nl^3) (nh^3) :=
  ⟨pow_le_pow_left₀ h0 hn.1 3,pow_le_pow_left₀ (h0.trans hn.1) hn.2 3⟩

/-- The Taylor enclosures of `sin x`, `cos x` and of their products with `a2`. -/
private lemma r40_trig {x : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ HighOrderTaylor.S11 x)
    (hc : 0 ≤ Arithmetic.cos10 x) :
    HighOrderTaylor.S11 x ≤ Real.sin x ∧ Real.sin x ≤ Arithmetic.sin9 x ∧
    Arithmetic.cos10 x ≤ Real.cos x ∧ Real.cos x ≤ SecondWord.ReferenceTrig.cos12 x ∧
    (32468681/20000000)*HighOrderTaylor.S11 x ≤ a2*Real.sin x ∧
    a2*Real.sin x ≤ (162343407/100000000)*Arithmetic.sin9 x ∧
    (32468681/20000000)*Arithmetic.cos10 x ≤ a2*Real.cos x ∧
    a2*Real.cos x ≤ (162343407/100000000)*SecondWord.ReferenceTrig.cos12 x := by
  have hs1 := HighOrderTaylor.S11_le_sin hx
  have hs2 := Arithmetic.sin_le_sin9 hx
  have hc1 := Arithmetic.cos10_le_cos hx
  have hc2 := SecondWord.ReferenceTrig.cos_le_cos12 hx
  have ha : a2 ∈ Icc (32468681/20000000) (162343407/100000000) :=
    ⟨a2_precise.1.le,a2_precise.2.le⟩
  have h1 := r40_prod ha ⟨hs1,hs2⟩ (by norm_num) hs
  have h2 := r40_prod ha ⟨hc1,hc2⟩ (by norm_num) hc
  exact ⟨hs1,hs2,hc1,hc2,h1.1,h1.2,h2.1,h2.2⟩

theorem positive_endpoint_curvature :
    (4/25:ℝ)<Fdd true (1/10) ∧ (4/25:ℝ)<Fdd true (21/50) := by
  constructor
  · have hN : N true (1/10) ∈ Icc (54881673/100000000:ℝ) (27440839/50000000) := positiveLeftNorm.mem
    have ht := r40_trig (show (0:ℝ) ≤ 1/10 by norm_num) (by norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7])
      (by norm_num [Arithmetic.cos10,Arithmetic.cos8])
    norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
    obtain ⟨hs1,hs2,hc1,hc2,has1,has2,hac1,hac2⟩ := ht
    have hr := r40_ratio ⟨R_precise.1.le,R_precise.2.le⟩ (r40_cube hN (by norm_num))
      (by norm_num) (by norm_num) (Delta_pos true).le
    have hD : Delta true=38197966249/1562500000000 := by
      norm_num [Delta,m,sign,FrameDiagonalLabels.u,FrameDiagonalLabels.v]
    rw [hD] at hr
    obtain ⟨-,hr2⟩ := hr
    simp only [Fdd,N2,hD,X,Y,lam,origin,m,b2_eq,↓reduceIte]
    linarith
  · have hN : N true (21/50) ∈ Icc (40288043/100000000:ℝ) (5036006/12500000) := positiveRightNorm.mem
    have ht := r40_trig (show (0:ℝ) ≤ 21/50 by norm_num) (by norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7])
      (by norm_num [Arithmetic.cos10,Arithmetic.cos8])
    norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
    obtain ⟨hs1,hs2,hc1,hc2,has1,has2,hac1,hac2⟩ := ht
    have hr := r40_ratio ⟨R_precise.1.le,R_precise.2.le⟩ (r40_cube hN (by norm_num))
      (by norm_num) (by norm_num) (Delta_pos true).le
    have hD : Delta true=38197966249/1562500000000 := by
      norm_num [Delta,m,sign,FrameDiagonalLabels.u,FrameDiagonalLabels.v]
    rw [hD] at hr
    obtain ⟨-,hr2⟩ := hr
    simp only [Fdd,N2,hD,X,Y,lam,origin,m,b2_eq,↓reduceIte]
    linarith

theorem positive_final_slope : Fd true (21/50)< -(2/25:ℝ) := by
  have hN : N true (21/50) ∈ Icc (40288043/100000000:ℝ) (5036006/12500000) := positiveRightNorm.mem
  have ht := r40_trig (show (0:ℝ) ≤ 21/50 by norm_num) (by norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7])
    (by norm_num [Arithmetic.cos10,Arithmetic.cos8])
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  obtain ⟨hs1,hs2,hc1,hc2,has1,has2,hac1,hac2⟩ := ht
  have hT : T true (21/50)=-(12954/78125) := by
    norm_num [T,lam,origin,m,sign,FrameDiagonalLabels.u,FrameDiagonalLabels.v]
  obtain ⟨hr1,hr2⟩ := r40_ratio ⟨R_precise.1.le,R_precise.2.le⟩ hN (by norm_num) (by norm_num)
    (show (0:ℝ) ≤ 12954/78125 by norm_num)
  have e : R*N1 true (21/50)=-(R*(12954/78125/N true (21/50))) := by
    simp only [N1,hT]; ring
  simp only [Fd]
  rw [e]
  simp only [X,Y,lam,origin,m,b2_eq,↓reduceIte]
  linarith

theorem positive_final_value : (899/1000:ℝ)<F true (21/50) := by
  have hN : N true (21/50) ∈ Icc (40288043/100000000:ℝ) (5036006/12500000) := positiveRightNorm.mem
  have ht := r40_trig (show (0:ℝ) ≤ 21/50 by norm_num) (by norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7])
    (by norm_num [Arithmetic.cos10,Arithmetic.cos8])
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  obtain ⟨hs1,hs2,hc1,hc2,has1,has2,hac1,hac2⟩ := ht
  obtain ⟨hRN1,hRN2⟩ := r40_prod ⟨R_precise.1.le,R_precise.2.le⟩ hN (by norm_num) (by norm_num)
  have hR := R_precise
  have ha := a2_precise
  have hpi := Arithmetic.pi_hand_enclosure
  simp only [F,FrameDiagonalLabels.M2,FrameDiagonalLabels.M,FrameDiagonalArc.A_b2]
  simp only [FrameDiagonalLabels.cM,FrameDiagonalLabels.k,FrameDiagonalLabels.q,
    FrameDiagonalLabels.u,X,Y,lam,origin,m,sign,b2_eq,↓reduceIte]
  linarith

theorem negative_endpoint_curvature :
    (3/5:ℝ)<Fdd false (2/5) ∧ (3/5:ℝ)<Fdd false (3/5) := by
  constructor
  · have hN : N false (2/5) ∈ Icc (58345669/100000000:ℝ) (29172837/50000000) := negativeLeftNorm.mem
    have ht := r40_trig (show (0:ℝ) ≤ 2/5 by norm_num) (by norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7])
      (by norm_num [Arithmetic.cos10,Arithmetic.cos8])
    norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
    obtain ⟨hs1,hs2,hc1,hc2,has1,has2,hac1,hac2⟩ := ht
    have hr := r40_ratio ⟨R_precise.1.le,R_precise.2.le⟩ (r40_cube hN (by norm_num))
      (by norm_num) (by norm_num) (Delta_pos false).le
    have hD : Delta false=105480099729/2441406250000 := by
      norm_num [Delta,m,sign,FrameDiagonalLabels.u,FrameDiagonalLabels.v]
    rw [hD] at hr
    obtain ⟨-,hr2⟩ := hr
    simp only [Fdd,N2,hD,X,Y,lam,origin,m,b2_eq,Bool.false_eq_true,↓reduceIte]
    linarith
  · have hN : N false (3/5) ∈ Icc (51371303/100000000:ℝ) (12842827/25000000) := negativeRightNorm.mem
    have ht := r40_trig (show (0:ℝ) ≤ 3/5 by norm_num) (by norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7])
      (by norm_num [Arithmetic.cos10,Arithmetic.cos8])
    norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
    obtain ⟨hs1,hs2,hc1,hc2,has1,has2,hac1,hac2⟩ := ht
    have hr := r40_ratio ⟨R_precise.1.le,R_precise.2.le⟩ (r40_cube hN (by norm_num))
      (by norm_num) (by norm_num) (Delta_pos false).le
    have hD : Delta false=105480099729/2441406250000 := by
      norm_num [Delta,m,sign,FrameDiagonalLabels.u,FrameDiagonalLabels.v]
    rw [hD] at hr
    obtain ⟨-,hr2⟩ := hr
    simp only [Fdd,N2,hD,X,Y,lam,origin,m,b2_eq,Bool.false_eq_true,↓reduceIte]
    linarith

theorem negative_tangent_value : (89273/100000:ℝ)<F false (14/25) := by
  have hN : N false (14/25) ∈ Icc (52678261/100000000:ℝ) (26339133/50000000) := negativeTangentNorm.mem
  have ht := r40_trig (show (0:ℝ) ≤ 14/25 by norm_num) (by norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7])
    (by norm_num [Arithmetic.cos10,Arithmetic.cos8])
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  obtain ⟨hs1,hs2,hc1,hc2,has1,has2,hac1,hac2⟩ := ht
  obtain ⟨hRN1,hRN2⟩ := r40_prod ⟨R_precise.1.le,R_precise.2.le⟩ hN (by norm_num) (by norm_num)
  have hR := R_precise
  have ha := a2_precise
  have hpi := Arithmetic.pi_hand_enclosure
  simp only [F,FrameDiagonalLabels.M2,FrameDiagonalLabels.M,FrameDiagonalArc.A_b2]
  simp only [FrameDiagonalLabels.cM,FrameDiagonalLabels.k,FrameDiagonalLabels.q,
    FrameDiagonalLabels.u,X,Y,lam,origin,m,sign,b2_eq,Bool.false_eq_true,↓reduceIte]
  linarith

theorem negative_tangent_slope : |Fd false (14/25)|<(7/5000:ℝ) := by
  have hN : N false (14/25) ∈ Icc (52678261/100000000:ℝ) (26339133/50000000) := negativeTangentNorm.mem
  have ht := r40_trig (show (0:ℝ) ≤ 14/25 by norm_num) (by norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7])
    (by norm_num [Arithmetic.cos10,Arithmetic.cos8])
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  obtain ⟨hs1,hs2,hc1,hc2,has1,has2,hac1,hac2⟩ := ht
  have hT : T false (14/25)=-(17531461/100000000) := by
    norm_num [T,lam,origin,m,sign,FrameDiagonalLabels.u,FrameDiagonalLabels.v]
  obtain ⟨hr1,hr2⟩ := r40_ratio ⟨R_precise.1.le,R_precise.2.le⟩ hN (by norm_num) (by norm_num)
    (show (0:ℝ) ≤ 17531461/100000000 by norm_num)
  have e : R*N1 false (14/25)=-(R*(17531461/100000000/N false (14/25))) := by
    simp only [N1,hT]; ring
  simp only [Fd]
  rw [e]
  simp only [X,Y,lam,origin,m,b2_eq,Bool.false_eq_true,↓reduceIte]
  rw [abs_lt]
  constructor <;> linarith

end SquaresInCircles.Eight.TableFree.FrameMidHighVaryingReferences
