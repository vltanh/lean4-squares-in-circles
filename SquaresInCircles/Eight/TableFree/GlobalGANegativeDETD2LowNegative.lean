module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2LowPositive
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2LowNegativeComparison
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2SecantCoordinate

/-!
# The low negative-DE pure-negative alternative

Uncompiled transcription of Section 6, equations (31)--(32), of the
negative-DE TD2 angle companion. The short-angle G comparison and the
whole-angle B chord reduce the pure-negative alternative to H. The
remaining scalar is concave in the prescribed coordinate x = tan s;
the original A/TD split and every coefficient remain fixed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowNegative
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeSlope OrdinaryNegativeEnvelope PairNormCalculus OrdinaryCurvatureBounds
open NegativeAPositiveTD (Curvature SecantCoordinate)

theorem H_endpoint_constants :
    shapeC0q R (757/1000)<72/125 ∧ Curvature.shapeD0q (757/1000)<239/200 := by
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  constructor
  · unfold shapeC0q
    apply quotient_lt_of_square (pow_pos (shape_pos _) 3) (by norm_num)
    rw [show ((shape (757/1000:ℝ))^3)^2=((shape (757/1000:ℝ))^2)^3 by ring,shape_sq]
    norm_num [mul_pow,hR2,qCap]
  · unfold Curvature.shapeD0q
    apply quotient_lt_of_square (shape_pos _) (by norm_num)
    norm_num [mul_pow,shape_sq,hR2,qCap]

theorem H_constants {k : ℝ} (hk : k∈Icc (2/3:ℝ) (757/1000)) :
    curvatureZero R k 1<72/125 ∧ Curvature.slopeZero k 1<239/200 := by
  have hk0 : 0<k := by linarith [hk.1]
  have hk1 : k≤1 := by linarith [hk.2]
  obtain ⟨_,_,hC,_⟩ := curvature_constants_normalize (R:=R) hk0 (by norm_num : (0:ℝ)<1)
  obtain ⟨_,hD⟩ := Curvature.constants_normalize hk0 (by norm_num : (0:ℝ)<1)
  have hCbound := (Curvature.shapeC0q_monotone ⟨hk0.le,hk1⟩
    (by norm_num : (757/1000:ℝ)∈Icc 0 1) hk.2).trans_lt H_endpoint_constants.1
  have hDbound := (Curvature.shapeD0q_monotone ⟨hk0.le,hk1⟩
    (by norm_num : (757/1000:ℝ)∈Icc 0 1) hk.2).trans_lt H_endpoint_constants.2
  simp only [div_one,one_mul] at hC hD
  exact ⟨by rw [hC]; exact hCbound,by rw [hD]; exact hDbound⟩

theorem H_slope {k t : ℝ} (hk : k∈Icc (2/3:ℝ) (757/1000))
    (ht : t∈Icc 0 frameCap) : Vd R k 1 t<239/200 := by
  have hk0 : 0<k := by linarith [hk.1]
  have hh := Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le hk0
    (by linarith [hk.2] : k≤1) (by linarith [hk.1] : 1≤2*k)
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap) ht ht.1
  have he : Vd R k 1 0=Curvature.slopeZero k 1 := by
    simp [Vd,mixedNDerivative,Curvature.slopeZero,normD1]
  rw [he] at hh
  exact hh.trans_lt (H_constants hk).2

theorem H_tangent {k t : ℝ} (hk : k∈Icc (2/3:ℝ) (757/1000))
    (ht : t∈Icc 0 frameCap) : V R k 1 t≤(239/200)*t := by
  have hh := V_tangent_zero (by linarith [hk.1] : 0<k)
    (by linarith [hk.2] : k≤1) (by linarith [hk.1] : 1≤2*k) ht
  have hd := H_slope hk (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
  exact hh.trans (mul_le_mul_of_nonneg_right hd.le ht.1)

theorem B_dominates_H {θ z t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) :
    V R (Explicit.k .low θ) 1 t≤Explicit.V .low θ z 2 t := by
  have hr := Explicit.low_ranges hθ
  have hm := Explicit.low_tilted hθ hz
  have hlm := hr.2.2.2.2.2.2.1.trans hm.1
  have hp := LowRanges.pairs hθ hz 2
  have hh := H_tangent ⟨hr.1.le,hr.2.1.le⟩ ht
  have hb := V_chord_lower hp.1 hp.2.1 hp.2.2.1 ht
  have hlower : 1≤Explicit.p .low θ z 2 := by
    simpa [Explicit.p,min_eq_left hlm] using hr.2.2.1.le
  have hmul := mul_le_mul_of_nonneg_right hlower ht.1
  change _≤Explicit.V .low θ z 2 t at hb
  nlinarith

theorem pure_comparison {θ z t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 θ) (i : Fin 3) :
    V R (Explicit.k .low θ) 1 t≤Explicit.V .low θ z i t := by
  have hr := Explicit.low_ranges hθ
  have htf : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap]; linarith [ht.2,hθ.2]⟩
  fin_cases i
  · simp [Explicit.V,Explicit.p,Explicit.q]
  · have hh := NegativeAPositiveTD.LowNegativeComparison.larger_coefficient
      (by linarith [hr.1] : 0<Explicit.k .low θ)
      (by linarith [hr.2.1] : Explicit.k .low θ≤1)
      hr.2.2.1.le hr.2.2.2.2.2.2.2.le
      (show t∈Icc 0 (1/5:ℝ) from ⟨ht.1,by linarith [ht.2,hθ.2]⟩)
    simpa [Explicit.V,Explicit.p,Explicit.q] using hh
  · exact B_dominates_H hθ hz htf

theorem tangent_cut {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    Real.tan θ<169/1000 := by
  have hframe : θ∈Icc 0 frameCap := ⟨hθ.1,by norm_num [frameCap]; linarith [hθ.2]⟩
  have hL : (1/6:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hm := SecantCoordinate.tan_monotone hframe hL hθ.2
  have hc := cos_lower_two (show (0:ℝ)≤1/6 by norm_num)
  have hs := sin_upper_five (show (0:ℝ)≤1/6 by norm_num)
  have he : Real.tan (1/6:ℝ)<169/1000 := by
    rw [Real.tan_eq_sin_div_cos]
    exact (div_lt_iff₀ (NegativeESecant.cos_pos hL)).2 (by norm_num at hc hs; linarith)
  exact hm.trans_lt he

def scalar (B k θ x : ℝ) : ℝ :=
  B+(13/12)*x-(diagonal-1/2)*(SecantCoordinate.radical 1 x-1)+
    V R k 1 (θ-Real.arctan x)
def first (k θ x : ℝ) : ℝ :=
  13/12-(diagonal-1/2)*x/SecantCoordinate.radical 1 x-
    Vd R k 1 (θ-Real.arctan x)/(1+x^2)
def second (k θ x : ℝ) : ℝ :=
  -(diagonal-1/2)/(SecantCoordinate.radical 1 x)^3+
    SecantCoordinate.negativeSecond k 1 θ x

theorem scalar_hasDerivAt {B k θ x : ℝ} (hk : 0<k)
    (hd : θ-Real.arctan x∈Icc 0 frameCap) :
    HasDerivAt (scalar B k θ) (first k θ x) x := by
  have hb := ((hasDerivAt_id x).const_mul (13/12:ℝ)).const_add B
  have hw := ((SecantCoordinate.radical_hasDerivAt (A:=1) (x:=x) (by norm_num)).sub_const 1).
    const_mul (diagonal-1/2)
  have hv := (V_hasDerivAt hk (by norm_num : (0:ℝ)<1) hd).comp x
    ((Real.hasDerivAt_arctan x).const_sub θ)
  convert (hb.sub hw).add hv using 1 <;> dsimp [scalar,first] <;> ring

theorem first_hasDerivAt {k θ x : ℝ} (hk : 0<k)
    (hd : θ-Real.arctan x∈Icc 0 frameCap) :
    HasDerivAt (first k θ) (second k θ x) x := by
  have hbase := (SecantCoordinate.radicalFirst_hasDerivAt (A:=1) (x:=x) (by norm_num)).
    const_mul (diagonal-1/2)
  have hv := SecantCoordinate.pureFirst_hasDerivAt (l:=0) (r:=0) hk (by norm_num : (0:ℝ)<1) hd
  simp only [SecantCoordinate.pureFirst,SecantCoordinate.pureSecond,zero_mul,zero_sub,zero_add] at hv
  convert (hbase.const_sub (13/12:ℝ)).add hv using 1 <;>
    dsimp [first,second] <;> ring

theorem second_negative {k θ x : ℝ} (hk : k∈Icc (2/3:ℝ) (757/1000))
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hx : x∈Icc 0 (Real.tan θ)) : second k θ x<0 := by
  have hk0 : 0<k := by linarith [hk.1]
  have hframe : θ∈Icc 0 frameCap := ⟨hθ.1,by norm_num [frameCap]; linarith [hθ.2]⟩
  have hs := SecantCoordinate.arctan_interval hframe hx
  have hd : θ-Real.arctan x∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hs.1,hframe.2]⟩
  have hdL : θ-Real.arctan x≤1/6 := by linarith [hθ.2,hs.1]
  have hcos := cos_lower_two hd.1
  have hd2 := pow_le_pow_left₀ hd.1 hdL 2
  have hcurv := curvature_negative_upper (Real.sqrt_nonneg qCap) hk0
    (by norm_num : (0:ℝ)<1)
    (show -(θ-Real.arctan x)∈Icc (-frameCap) 0 from ⟨by linarith [hd.2],by linarith [hd.1]⟩)
  have hC := (H_constants hk).1
  have hV := H_slope hk hd
  have hproduct := mul_le_mul_of_nonneg_left hV.le hx.1
  have hxU : x<169/1000 := hx.2.trans_lt (tangent_cut hθ)
  have hnum : curvature R k 1 (-(θ-Real.arctan x))-Real.cos (θ-Real.arctan x)+
      2*x*Vd R k 1 (θ-Real.arctan x)<0 := by nlinarith
  have hnegative : SecantCoordinate.negativeSecond k 1 θ x<0 := by
    unfold SecantCoordinate.negativeSecond
    simp only [one_mul]
    exact div_neg_of_neg_of_pos hnum (by positivity)
  have hdiag : 0≤(diagonal-1/2)/(SecantCoordinate.radical 1 x)^3 := by
    exact div_nonneg (by linarith [diagonal_bounds.1])
      (pow_nonneg (Real.sqrt_nonneg _) 3)
  dsimp [second]
  linarith

theorem scalar_concave {B k θ : ℝ} (hk : k∈Icc (2/3:ℝ) (757/1000))
    (hθ : θ∈Icc (0:ℝ) (1/6)) : ConcaveOn ℝ (Icc 0 (Real.tan θ)) (scalar B k θ) := by
  have hk0 : 0<k := by linarith [hk.1]
  have hframe : θ∈Icc 0 frameCap := ⟨hθ.1,by norm_num [frameCap]; linarith [hθ.2]⟩
  have hd (x : ℝ) (hx : x∈Icc 0 (Real.tan θ)) : θ-Real.arctan x∈Icc 0 frameCap := by
    have hs := SecantCoordinate.arctan_interval hframe hx
    exact ⟨by linarith [hs.2],by linarith [hs.1,hframe.2]⟩
  exact concave_of_deriv2 (fun x hx => scalar_hasDerivAt hk0 (hd x hx))
    (fun x hx => first_hasDerivAt hk0 (hd x hx))
    (fun x hx => (second_negative hk hθ hx).le)

/-- The endpoint principle is exported before the A/TD split is changed. -/
theorem original_endpoint_lower {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (hs : s∈Icc 0 (a+z)) :
    min (Explicit.baseline .low a z 0+V R (Explicit.k .low (a+z)) 1 (a+z))
      (Explicit.baseline .low a z (a+z))≤
    Explicit.baseline .low a z s+V R (Explicit.k .low (a+z)) 1 (a+z-s) := by
  have hframe : a+z∈Icc 0 frameCap := ⟨hθ.1,by norm_num [frameCap]; linarith [hθ.2]⟩
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans hframe.2⟩
  have hr := Explicit.low_ranges hθ
  have hx : Real.tan s∈Icc 0 (Real.tan (a+z)) :=
    ⟨SecantCoordinate.tan_nonnegative hsf,SecantCoordinate.tan_monotone hsf hframe hs.2⟩
  have hid {t : ℝ} (ht : t∈Icc 0 (a+z)) :
      scalar (Explicit.baseline .low a z 0) (Explicit.k .low (a+z)) (a+z) (Real.tan t)=
        Explicit.baseline .low a z t+V R (Explicit.k .low (a+z)) 1 (a+z-t) := by
    have htf : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hframe.2⟩
    have hc := NegativeESecant.cos_pos htf
    have hrad : SecantCoordinate.radical 1 (Real.tan t)=LowD.sec t := by
      rw [Real.tan_eq_sin_div_cos]
      have hroot := SecantCoordinate.radical_square (A:=1) (x:=Real.sin t/Real.cos t) (by norm_num)
      have hpos := SecantCoordinate.radical_positive (A:=1) (x:=Real.sin t/Real.cos t) (by norm_num)
      have hsquare : (LowD.sec t)^2=1+(Real.sin t/Real.cos t)^2 := by
        dsimp [LowD.sec,NegativeELargeA.secant]
        field_simp [hc.ne']
        nlinarith [Real.sin_sq_add_cos_sq t]
      have hsec : 0<LowD.sec t := div_pos (by norm_num) hc
      nlinarith
    rw [scalar,SecantCoordinate.arctan_tan htf,hrad,LowD.diagonal_baseline hθ ht]
    rw [LowD.diagonalCorrection,NegativeESecant.gain_secant _ htf]
    dsimp [LowD.sec,NegativeELargeA.secant,NegativeESecant.K]
    ring
  have hz : (0:ℝ)∈Icc 0 (Real.tan (a+z)) := ⟨le_rfl,SecantCoordinate.tan_nonnegative hframe⟩
  have he : Real.tan (a+z)∈Icc 0 (Real.tan (a+z)) := ⟨hz.2,le_rfl⟩
  have hh := (scalar_concave (B:=Explicit.baseline .low a z 0) ⟨hr.1.le,hr.2.1.le⟩ hθ).
    min_le_of_mem_Icc hz he hx
  have hzero := hid (t:=0) ⟨le_rfl,hθ.1⟩
  have hlast := hid (t:=a+z) ⟨hθ.1,le_rfl⟩
  simp only [Real.tan_zero,sub_zero] at hzero
  simp only [sub_self,V_zero,add_zero] at hlast
  rw [hzero,hlast,hid hs] at hh
  exact hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowNegative
