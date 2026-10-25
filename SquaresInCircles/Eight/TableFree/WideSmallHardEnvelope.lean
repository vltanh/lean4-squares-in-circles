module

public import SquaresInCircles.Eight.TableFree.SmallHardEnvelope

/-!
# A sharper continuous hard envelope down to the .28 tangent threshold

Uncompiled source draft.  Three rational quadratic majorants give a
single polynomial comparison on the complete tangent interval [.28,.5].
The opposite contact has no angular excess when its transverse corner
exceeds the charge; the remaining intrinsic branch has a uniform
completed-square excess.  The resulting actual middle budget is below
.4175, without implicit optimizers or a numerical acceptance premise.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.WideSmallHardEnvelope
open EndpointRotationPenalty

def angleUpper (d : ℝ) : ℝ := 3893/12500-(18/25)*d+d^2/5
def leftRadiusUpper (d : ℝ) : ℝ := 89701/50000-(93/200)*d-(67/200)*d^2
def rightRadiusUpper (d : ℝ) : ℝ := 3199/2000+(729/1000)*d-(39/100)*d^2

theorem majorant_bounds {d : ℝ} (hd : d∈Icc (-(11/200 : ℝ)) (33/200)) :
    angleUpper d∈Icc (19/100 : ℝ) (353/1000) ∧
      1<leftRadiusUpper d ∧ 0<rightRadiusUpper d := by
  have habs : |d|≤33/200 := abs_le.mpr ⟨by linarith [hd.1],hd.2⟩
  have hd2 : d^2≤(33/200 : ℝ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg d) habs 2
  have hchord : d^2≤(11/100)*d+363/40000 := by
    nlinarith [mul_nonneg (show 0≤d+11/200 by linarith [hd.1])
      (show 0≤33/200-d by linarith [hd.2])]
  dsimp [angleUpper,leftRadiusUpper,rightRadiusUpper]
  exact ⟨⟨by nlinarith [hd.2,sq_nonneg d],by nlinarith [hd.1]⟩,
    by nlinarith [hd.2],by nlinarith [hd.1]⟩

theorem left_square_reserve {d : ℝ} (hd : -(11/200 : ℝ)≤d) :
    qCap<(leftRadiusUpper d)^2+(167/200+d)^2 := by
  let x := d+11/200
  have hx : 0≤x := by dsimp [x]; linarith
  have hcoef : 0<219884361/80000000000-(28109813/800000000)*x+
      (573721/2000000)*x^2 := by
    nlinarith [sq_nonneg (x-9/140),sq_nonneg x]
  have hid : (leftRadiusUpper d)^2+(167/200+d)^2-qCap=
      2504114409/64000000000000+x*
        (219884361/80000000000-(28109813/800000000)*x+
          (573721/2000000)*x^2)+(4489/40000)*x^4 := by
    dsimp [leftRadiusUpper,qCap,x]
    ring
  have hp : 0<2504114409/64000000000000+x*
      (219884361/80000000000-(28109813/800000000)*x+
        (573721/2000000)*x^2)+(4489/40000)*x^4 := by positivity
  linarith

theorem right_square_reserve {d : ℝ} (hd : d≤33/200) :
    qCap<(rightRadiusUpper d)^2+(233/200-d)^2 := by
  have hcoef : 19/100≤283831/1000000-(28431/50000)*d+(1521/10000)*d^2 := by
    nlinarith [sq_nonneg d]
  have hprod := mul_le_mul_of_nonneg_right hcoef (sq_nonneg d)
  have hid : (rightRadiusUpper d)^2+(233/200-d)^2-qCap=
      101/4000000+(2071/1000000)*d+
        (283831/1000000-(28431/50000)*d+(1521/10000)*d^2)*d^2 := by
    dsimp [rightRadiusUpper,qCap]
    ring
  rw [←sub_pos]
  rw [hid]
  nlinarith [sq_nonneg (d+2071/380000)]

theorem angle_taylor_reserve {d : ℝ} (hd : d∈Icc (-(11/200 : ℝ)) (33/200)) :
    (leftRadiusUpper d-1)*
        (1-(angleUpper d)^2/2+(angleUpper d)^4/24)-
      (167/200+d)*(angleUpper d-(angleUpper d)^3/6)<1/2 := by
  obtain ⟨c,hcdef⟩ : ∃ c : ℝ,c=213602950719462301/117187500000000000000 := ⟨_,rfl⟩
  obtain ⟨K,hKdef⟩ : ∃ K : ℝ,K=2826945227271970329/39062500000000000000+
      (708646698993441/19531250000000000)*d+
      (10316357513921/2929687500000000)*d^2+
      (166726669477/15625000000000)*d^3+
      (35200013789/9375000000000)*d^4-
      (34103849/9375000000)*d^5+(1720519/1250000000)*d^6-
      (1453/5000000)*d^7+(67/3000000)*d^8 := ⟨_,rfl⟩
  have habs : |d|≤33/200 := abs_le.mpr ⟨by linarith only [hd.1],hd.2⟩
  have hp (n : ℕ) : |d^n|≤(33/200 : ℝ)^n := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg d) habs n
  have h3 := (abs_le.mp (hp 3)).1
  have h5 := (abs_le.mp (hp 5)).2
  have h7 := (abs_le.mp (hp 7)).2
  have hK : 3/50≤K := by
    rw [hKdef]
    linarith only [hd.1,sq_nonneg d,sq_nonneg (d^2),sq_nonneg (d^3),sq_nonneg (d^4),h3,h5,h7]
  have hlinear : -(1/500)*|d|≤c*d := by
    have hm := mul_le_mul_of_nonneg_left (neg_abs_le d) (show 0≤c by rw [hcdef]; norm_num)
    have hc := mul_le_mul_of_nonneg_right (show c≤1/500 by rw [hcdef]; norm_num) (abs_nonneg d)
    linarith only [hm,hc]
  have hquad := mul_le_mul_of_nonneg_right hK (sq_nonneg d)
  have hid : 1/2-((leftRadiusUpper d-1)*
        (1-(angleUpper d)^2/2+(angleUpper d)^4/24)-
      (167/200+d)*(angleUpper d-(angleUpper d)^3/6))=
      735951208656548699/29296875000000000000000+c*d+K*d^2 := by
    rw [hcdef,hKdef]
    dsimp [leftRadiusUpper,angleUpper]
    ring
  have hsquare : |d|^2=d^2 := sq_abs d
  have hpositive : 0<735951208656548699/29296875000000000000000+c*d+K*d^2 := by
    linarith only [sq_nonneg (|d|-1/60),hlinear,hquad,hsquare]
  linarith only [hid,hpositive]

theorem hard_angle_upper {a b z : ℝ}
    (hb : b∈Icc (7/25 : ℝ) (1/2)) (ha : 1/2<a)
    (hc : (a+1/2)^2+(b+1/2)^2≤qCap)
    (hz : z∈Icc 0 frameCap)
    (hf : 1/2≤(a-1/2)*Real.cos z-(b+1/2)*Real.sin z) :
    z<angleUpper (b-67/200) := by
  let d := b-67/200
  have hd : d∈Icc (-(11/200 : ℝ)) (33/200) := by
    dsimp [d]; constructor <;> linarith [hb.1,hb.2]
  have hy : b+1/2=167/200+d := by dsimp [d]; ring
  have hm := majorant_bounds hd
  have hz' : angleUpper d∈Icc 0 frameCap := by
    dsimp [frameCap]
    exact ⟨by linarith [hm.1.1],by linarith [hm.1.2]⟩
  have har : a+1/2<leftRadiusUpper d := by
    have hs := left_square_reserve hd.1
    rw [←hy] at hs
    nlinarith [hm.2.1]
  by_contra! hbad
  have hcos := CorrelatedSameBlock.cos_anti hz' hz hbad
  have hsin := CorrelatedSameBlock.sin_mono hz' hz hbad
  have hpc := mul_le_mul_of_nonneg_left hcos (by linarith : 0≤a-1/2)
  have hys := mul_le_mul_of_nonneg_left hsin (by linarith [hb.1] : 0≤b+1/2)
  have hcap := mul_le_mul_of_nonneg_right (show a-1/2≤leftRadiusUpper d-1 by linarith)
    (show 0≤Real.cos (angleUpper d) by linarith [(transport_trig hz').1])
  have hct := mul_le_mul_of_nonneg_left (cos_upper_four hz'.1)
    (show 0≤leftRadiusUpper d-1 by linarith [hm.2.1])
  have hst := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hz'.1)
    (show 0≤167/200+d by linarith [hd.1])
  have hpoly := angle_taylor_reserve hd
  rw [hy] at hf hys
  linarith

theorem opposite_quadratic {P Y v : ℝ}
    (hP : P∈Icc (557/1000 : ℝ) (177/250))
    (hY : Y∈Icc (1 : ℝ) (61/50))
    (hv : v∈Icc 0 frameCap)
    (hf : 1/2≤P*Real.cos v-Y*Real.sin v) :
    P*Real.cos v-Y*Real.sin v≤P-Y*v-v^2/5 := by
  have htr := transport_trig hv
  have hpc1 := mul_le_mul_of_nonneg_left (Real.cos_le_one v)
    (show 0≤P by linarith [hP.1])
  have hys1 := mul_le_mul_of_nonneg_right hY.1 htr.2.2.1
  have hsv : Real.sin v≤26/125 := by nlinarith [hP.2]
  have hv21 : v<21/100 := by
    by_contra! hvlong
    have hsm := CorrelatedSameBlock.sin_mono
      (show (21/100 : ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hv hvlong
    have hsl := Real.sin_ge_sub_cube (show (0:ℝ)≤21/100 by norm_num)
    norm_num at hsl
    linarith
  have hv3 : v^3≤(21/100 : ℝ)*v^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hv21.le (sq_nonneg v)]
  have hv4 : v^4≤(21/100 : ℝ)^2*v^2 := by
    nlinarith [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv.1 hv21.le 2) (sq_nonneg v)]
  have hct := mul_le_mul_of_nonneg_left (cos_upper_four hv.1)
    (show 0≤P by linarith [hP.1])
  have hst := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hv.1)
    (show 0≤Y by linarith [hY.1])
  have hp2 := mul_le_mul_of_nonneg_right hP.1 (sq_nonneg v)
  have hp4 := mul_le_mul_of_nonneg_right hP.2 (pow_nonneg hv.1 4)
  have hy3 := mul_le_mul_of_nonneg_right hY.2 (pow_nonneg hv.1 3)
  nlinarith

/-- The sharper complete interval bound used by both crossed small
normal and wrong-sign endpoint comparisons. -/
theorem actual_middle_bound {aA aB b t z v : ℝ}
    (hb : b∈Icc (7/25 : ℝ) (1/2)) (haA : 1/2<aA)
    (hA : (aA+1/2)^2+(b+1/2)^2≤qCap)
    (hB : (aB+1/2)^2+(3/2-b)^2≤qCap)
    (hz : z∈Icc 0 frameCap) (hv : v∈Icc 0 frameCap) (ht : 0≤t)
    (hGA : 1/2≤(aA-1/2)*Real.cos z-(b+1/2)*Real.sin z)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(3/2-b)*Real.sin v) :
    t+charge*(z+v)<167/400 := by
  obtain ⟨d,hd_def⟩ : ∃ d : ℝ,d=b-67/200 := ⟨_,rfl⟩
  obtain ⟨Y,hY_def⟩ : ∃ Y : ℝ,Y=3/2-b := ⟨_,rfl⟩
  obtain ⟨R,hR_def⟩ : ∃ R : ℝ,R=Real.sqrt (qCap-Y^2) := ⟨_,rfl⟩
  have hd : d∈Icc (-(11/200 : ℝ)) (33/200) := by
    rw [hd_def]; constructor <;> linarith only [hb.1,hb.2]
  have hY : Y∈Icc (1 : ℝ) (61/50) := by
    rw [hY_def]; constructor <;> linarith only [hb.1,hb.2]
  have hY2 := pow_le_pow_left₀ (show 0≤Y by linarith only [hY.1]) hY.2 2
  have hYsq : (1:ℝ)≤Y^2 := one_le_pow₀ hY.1
  have hrad : 0≤qCap-Y^2 := by
    simp only [qCap]
    linarith only [hY2]
  have hR0 : 0≤R := by rw [hR_def]; exact Real.sqrt_nonneg _
  have hR2 : R^2=qCap-Y^2 := by rw [hR_def]; exact Real.sq_sqrt hrad
  have hR : R∈Icc (1557/1000 : ℝ) (427/250) := by
    rw [hR_def]
    constructor
    · rw [Real.le_sqrt (by norm_num) hrad]
      simp only [qCap]
      linarith only [hY2]
    · rw [Real.sqrt_le_left (by norm_num)]
      simp only [qCap]
      linarith only [hYsq]
  have hBcap : aB-1/2≤R-1 := by
    rw [← hY_def] at hB
    have h1 : |aB+1/2|≤R := by
      rw [hR_def]
      exact Real.abs_le_sqrt (by linarith only [hB])
    linarith only [le_abs_self (aB+1/2),h1]
  have hmul := mul_le_mul_of_nonneg_right hBcap
    (show 0≤Real.cos v by linarith only [(transport_trig hv).1])
  have hBT' : t+1/2≤(R-1)*Real.cos v-Y*Real.sin v := by
    rw [← hY_def] at hBT
    linarith only [hBT,hmul]
  have hquad := opposite_quadratic
    (show R-1∈Icc (557/1000 : ℝ) (177/250) by constructor <;> linarith only [hR.1,hR.2])
    hY hv (by linarith only [hBT',ht])
  have hzmax := hard_angle_upper hb haA hA hz hGA
  rw [← hd_def] at hzmax
  have hRmax : R<rightRadiusUpper d := by
    have hs := right_square_reserve hd.2
    have hy : Y=233/200-d := by rw [hY_def,hd_def]; ring
    rw [←hy] at hs
    have hpos := (majorant_bounds hd).2.2
    apply lt_of_pow_lt_pow_left₀ 2 hpos.le
    linarith only [hs,hR2]
  have hid : charge*angleUpper d+rightRadiusUpper d-3/2=
      40895/98000-(279/49000)*d-(911/4900)*d^2 := by
    dsimp [charge,angleUpper,rightRadiusUpper]
    ring
  have hzcharge := mul_lt_mul_of_pos_left hzmax (by norm_num [charge] : 0<charge)
  by_cases hYp : charge≤Y
  · have hpv := mul_le_mul_of_nonneg_right hYp hv.1
    have hcombined : charge*angleUpper d+rightRadiusUpper d-3/2<167/400 := by
      rw [hid]
      linarith only [sq_nonneg (d+279/18220)]
    linarith only [sq_nonneg v,hpv,hBT',hquad,hRmax,hcombined,hzcharge]
  · have hexcess : (R-1)*Real.cos v-Y*Real.sin v+charge*v≤R-1+5/9604 := by
      have hyv := mul_le_mul_of_nonneg_right hY.1 hv.1
      simp only [charge]
      linarith only [sq_nonneg (v-5/98),hquad,hyv]
    have hdlarge : 7/50≤d := by
      have h := lt_of_not_ge hYp
      simp only [charge] at h
      rw [hd_def]
      linarith only [h,hY_def]
    have hcombined : charge*angleUpper d+rightRadiusUpper d-3/2+5/9604<167/400 := by
      rw [hid]
      linarith only [sq_nonneg d,hdlarge]
    linarith only [hBT',hexcess,hRmax,hcombined,hzcharge]

end SquaresInCircles.Eight.TableFree.WideSmallHardEnvelope
