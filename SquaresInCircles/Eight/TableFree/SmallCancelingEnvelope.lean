module

public import SquaresInCircles.Eight.TableFree.SignedOppositeHardEnvelope
public import SquaresInCircles.Eight.TableFree.WideSmallHardEnvelope

/-!
# A direct two-middle envelope for the small canceling branch

Uncompiled source draft.  Two explicit quadratic radius majorants and
one affine reference angle bound the entire first angular envelope.
The second envelope uses its actual hard contact and a completed square.
Every polynomial comparison holds on the full transverse interval;
there is no maximizer, numerical minimum, or angular mesh premise.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SmallCancelingEnvelope
open EndpointRotationPenalty

def leftRadius (x : ℝ) : ℝ :=
  89107/50000-(48257/100000)*x-(169/500)*x^2
def rightRadius (x : ℝ) : ℝ :=
  161741/100000+(70483/100000)*x-(393/1000)*x^2
def referenceAngle (x : ℝ) : ℝ := 477/2000-(38/25)*x
def referenceU (x : ℝ) : ℝ :=
  (leftRadius x-1)*Real.sin (referenceAngle x)+(43/50+x)*Real.cos (referenceAngle x)
def referenceV (x : ℝ) : ℝ :=
  (leftRadius x-1)*Real.cos (referenceAngle x)-(43/50+x)*Real.sin (referenceAngle x)
def lowerU (x : ℝ) : ℝ :=
  (leftRadius x-1)*(referenceAngle x-(referenceAngle x)^3/6)+
    (43/50+x)*(1-(referenceAngle x)^2/2)
def upperU (x : ℝ) : ℝ :=
  (leftRadius x-1)*referenceAngle x+
    (43/50+x)*(1-(referenceAngle x)^2/2+(referenceAngle x)^4/24)
def lowerV (x : ℝ) : ℝ :=
  (leftRadius x-1)*(1-(referenceAngle x)^2/2)-(43/50+x)*referenceAngle x
def upperValue (x : ℝ) : ℝ :=
  (leftRadius x-1)*(1-(referenceAngle x)^2/2+(referenceAngle x)^4/24)-
    (43/50+x)*(referenceAngle x-(referenceAngle x)^3/6)+
    charge*referenceAngle x+4*(1/250)^2

theorem interval_bounds {x : ℝ} (hx : x∈Icc (-(1/40 : ℝ)) (7/50)) :
    leftRadius x∈Icc (17/10 : ℝ) (9/5) ∧
      (3/2 : ℝ)≤rightRadius x ∧ referenceAngle x∈Icc 0 frameCap := by
  have ha : |x|≤7/50 := abs_le.mpr ⟨by linarith [hx.1],hx.2⟩
  have h2 : x^2≤49/2500 := by
    have hh := pow_le_pow_left₀ (abs_nonneg x) ha 2
    rw [sq_abs] at hh
    linarith
  dsimp [leftRadius,rightRadius,referenceAngle,frameCap]
  constructor
  · constructor <;> nlinarith [hx.1,hx.2,sq_nonneg x]
  · constructor
    · nlinarith [hx.1]
    · constructor <;> linarith [hx.1,hx.2]

theorem radius_reserves {x : ℝ} (hx : x∈Icc (-(1/40 : ℝ)) (7/50)) :
    qCap<(leftRadius x)^2+(43/50+x)^2 ∧
      qCap<(rightRadius x)^2+(57/50-x)^2 := by
  have hA : 19/1000≤281471649/10000000000+(8155433/25000000)*x+
      (28561/250000)*x^2 := by nlinarith [hx.1,sq_nonneg x]
  have hB : 147/1000≤2255010689/10000000000-(27699819/50000000)*x+
      (154449/1000000)*x^2 := by nlinarith [hx.2,sq_nonneg x]
  have hA2 := mul_le_mul_of_nonneg_right hA (sq_nonneg x)
  have hB2 := mul_le_mul_of_nonneg_right hB (sq_nonneg x)
  have hAid : (leftRadius x)^2+(43/50+x)^2-qCap=
      57449/2500000000-(36499/2500000000)*x+
        (281471649/10000000000+(8155433/25000000)*x+
          (28561/250000)*x^2)*x^2 := by dsimp [leftRadius,qCap]; ring
  have hBid : (rightRadius x)^2+(57/50-x)^2-qCap=
      151081/10000000000-(9097/5000000000)*x+
        (2255010689/10000000000-(27699819/50000000)*x+
          (154449/1000000)*x^2)*x^2 := by dsimp [rightRadius,qCap]; ring
  constructor <;> nlinarith [hx.2,sq_nonneg x]

theorem reference_polynomials {x : ℝ} (hx : x∈Icc (-(1/40 : ℝ)) (7/50)) :
    charge-1/250≤lowerU x ∧ upperU x≤charge+1/250 ∧ 53/100≤lowerV x := by
  have ha : |x|≤7/50 := abs_le.mpr ⟨by linarith [hx.1],hx.2⟩
  have hp (n : ℕ) : |x^n|≤(7/50 : ℝ)^n := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) ha n
  have h2 : x^2≤49/2500 := by
    have hh := hp 2
    simp only [abs_pow,sq_abs] at hh
    linarith
  have h3 := abs_le.mp (hp 3)
  have hsec : x^2≤(23/200)*x+7/2000 := by
    nlinarith [mul_nonneg (show 0≤x+1/40 by linarith [hx.1])
      (show 0≤7/50-x by linarith [hx.2])]
  let KL := -(8545902570753/40000000000000 : ℝ)-(48981718097/750000000000)*x-
    (887459657/4687500000)*x^2-(1159171/5859375)*x^3
  let KU := (46760035791/1000000000000 : ℝ)-(9107949611/12500000000)*x+
    (6056497/117187500)*x^2+(260642/1171875)*x^3
  let KV := (2262873917/20000000000 : ℝ)+(27183319/62500000)*x+
    (61009/156250)*x^2
  have hKL : -(23/100 : ℝ)≤KL := by dsimp [KL]; nlinarith [hx.2,h3.2]
  have hKU : KU≤7/100 := by dsimp [KU]; nlinarith [hx.1,h3.2]
  have hKV : 1/10≤KV := by dsimp [KV]; nlinarith [hx.1,sq_nonneg x]
  have hLid : lowerU x-charge=
      -(3748053713973/39200000000000000 : ℝ)+
        (22854024591767/1600000000000000)*x+KL*x^2 := by
    dsimp [lowerU,leftRadius,referenceAngle,charge,KL]; ring
  have hUid : upperU x-charge=
      (560968063462329/313600000000000000 : ℝ)-
        (15001935170233/640000000000000)*x+KU*x^2 := by
    dsimp [upperU,leftRadius,referenceAngle,charge,KU]; ring
  have hVid : lowerV x-53/100=
      (9914023397/400000000000 : ℝ)+
        (706716981193/800000000000)*x+KV*x^2 := by
    dsimp [lowerV,leftRadius,referenceAngle,KV]; ring
  have hL2 := mul_le_mul_of_nonneg_right hKL (sq_nonneg x)
  have hU2 := mul_le_mul_of_nonneg_right hKU (sq_nonneg x)
  have hV2 := mul_le_mul_of_nonneg_right hKV (sq_nonneg x)
  refine ⟨?_,?_,?_⟩
  · linarith [hL2,h2,hx.1,hx.2]
  · linarith [hU2,h2,hx.1,hx.2]
  · linarith [hV2,sq_nonneg x,hx.1,hx.2]

theorem budget_polynomial {x : ℝ} (hx : x∈Icc (-(1/40 : ℝ)) (7/50)) :
    upperValue x+rightRadius x-1+(9/320)*x^2<709/500 := by
  have ha : |x|≤7/50 := abs_le.mpr ⟨by linarith [hx.1],hx.2⟩
  have hp (n : ℕ) : |x^n|≤(7/50 : ℝ)^n := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) ha n
  have h2 : x^2≤49/2500 := by
    have hh := hp 2
    simp only [abs_pow,sq_abs] at hh
    linarith
  have h3 := (abs_le.mp (hp 3)).1
  let K := -(9826702308776527/320000000000000000 : ℝ)+
    (124820306249837/1500000000000000)*x+
    (663272806273/18750000000000)*x^2-
    (1762138831/29296875000)*x^3-(22024249/292968750)*x^4
  have hK : K≤ -(1/100 : ℝ) := by
    dsimp [K]
    nlinarith [hx.2,sq_nonneg (x^2)]
  have hK2 := mul_le_mul_of_nonneg_right hK (sq_nonneg x)
  have hid : upperValue x+rightRadius x-1+(9/320)*x^2=
      (444583309738999565121/313600000000000000000 : ℝ)-
        (291326780388325931/627200000000000000000)*x+K*x^2 := by
    dsimp [upperValue,leftRadius,rightRadius,referenceAngle,charge,K]
    ring
  nlinarith [hx.1,sq_nonneg x]

theorem left_envelope {x z : ℝ} (hx : x∈Icc (-(1/40 : ℝ)) (7/50))
    (hz : z∈Icc 0 frameCap) :
    (leftRadius x-1)*Real.cos z-(43/50+x)*Real.sin z+charge*z≤upperValue x := by
  obtain ⟨hR,hB,hu⟩ := interval_bounds hx
  have hP : 0≤leftRadius x-1 := by linarith [hR.1]
  have hY : 0≤43/50+x := by linarith [hx.1]
  have hL : lowerU x≤referenceU x := by
    have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hu.1) hP
    have hc := mul_le_mul_of_nonneg_left
      (Real.one_sub_sq_div_two_le_cos (x := referenceAngle x)) hY
    dsimp [lowerU,referenceU]
    linarith
  have hU : referenceU x≤upperU x := by
    have hs := mul_le_mul_of_nonneg_left (Real.sin_le hu.1) hP
    have hc := mul_le_mul_of_nonneg_left (cos_upper_four hu.1) hY
    dsimp [upperU,referenceU]
    linarith
  have hV : lowerV x≤referenceV x := by
    have hc := mul_le_mul_of_nonneg_left
      (Real.one_sub_sq_div_two_le_cos (x := referenceAngle x)) hP
    have hs := mul_le_mul_of_nonneg_left (Real.sin_le hu.1) hY
    dsimp [lowerV,referenceV]
    linarith
  obtain ⟨hLp,hUp,hVp⟩ := reference_polynomials hx
  have hη : |charge-referenceU x|≤1/250 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hUi : referenceU x∈Icc 0 (11/10 : ℝ) := by
    dsimp [charge] at hLp hUp
    constructor <;> linarith
  have hd : z-referenceAngle x∈Icc (-frameCap) frameCap := by
    constructor <;> linarith [hz.1,hz.2,hu.1,hu.2]
  have hrot := SignedOppositeHardEnvelope.rotation_upper hUi
    (Or.inl (show (2/5 : ℝ)≤referenceV x by linarith)) hd hη
  have hid := SignedOppositeHardEnvelope.rotation_identity (leftRadius x-1)
    (43/50+x) (referenceAngle x) (z-referenceAngle x)
  rw [show referenceAngle x+(z-referenceAngle x)=z by ring] at hid
  change (leftRadius x-1)*Real.cos z-(43/50+x)*Real.sin z=
    referenceV x*Real.cos (z-referenceAngle x)-
      referenceU x*Real.sin (z-referenceAngle x) at hid
  have hvalue : referenceV x+charge*referenceAngle x+4*(1/250)^2≤upperValue x := by
    have hc := mul_le_mul_of_nonneg_left (cos_upper_four hu.1) hP
    have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hu.1) hY
    dsimp [referenceV,upperValue]
    linarith
  nlinarith

theorem right_envelope {x a t v : ℝ} (hx : x∈Icc (-(1/40 : ℝ)) (7/50))
    (ha : 0≤a) (ht : 0≤t) (hv : v∈Icc 0 frameCap)
    (hc : (a+1/2)^2+(57/50-x)^2≤qCap)
    (hf : t+1/2≤(a-1/2)*Real.cos v-(57/50-x)*Real.sin v) :
    t+charge*v≤rightRadius x-3/2+(9/320)*x^2 := by
  let R := Real.sqrt (qCap-(57/50-x)^2)
  have hy : 57/50-x∈Icc (1 : ℝ) (233/200) := by
    constructor <;> linarith [hx.1,hx.2]
  have hy2 := pow_le_pow_left₀ (by linarith [hy.1]) hy.2 2
  have hrad : 0≤qCap-(57/50-x)^2 := by dsimp [qCap]; nlinarith
  have hR0 : 0≤R := Real.sqrt_nonneg _
  have hR2 : R^2=qCap-(57/50-x)^2 := Real.sq_sqrt hrad
  have hy1 : 1≤(57/50-x)^2 := by nlinarith [hy.1]
  have hR : R∈Icc (1557/1000 : ℝ) (427/250) := by
    constructor
    · exact (Real.le_sqrt (by norm_num) hrad).2 (by dsimp [qCap]; linarith)
    · exact (Real.sqrt_le_left (by norm_num)).2 (by dsimp [qCap]; linarith)
  have haR : a+1/2≤R := (Real.le_sqrt (by linarith) hrad).2 (by linarith)
  have hcos : 0≤Real.cos v := by linarith [(transport_trig hv).1]
  have hcap := mul_le_mul_of_nonneg_right (show a-1/2≤R-1 by linarith) hcos
  have hhard : 1/2≤(R-1)*Real.cos v-(57/50-x)*Real.sin v := by linarith
  have hquad := WideSmallHardEnvelope.opposite_quadratic
    (show R-1∈Icc (557/1000 : ℝ) (177/250) by constructor <;> linarith [hR.1,hR.2])
    (show 57/50-x∈Icc (1 : ℝ) (61/50) by constructor <;> linarith [hy.1,hy.2])
    hv hhard
  have hRbar : R≤rightRadius x := by
    have hh := (radius_reserves hx).2
    have hb := (interval_bounds hx).2.1
    exact (Real.sqrt_le_left (by linarith)).2 (by linarith)
  by_cases hk : charge≤57/50-x
  · have hm := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hk) hv.1
    linarith [sq_nonneg v,sq_nonneg x]
  · have hx0 : 0≤x := by dsimp [charge] at hk; linarith
    have hk0 : 0≤charge-(57/50-x) := by linarith
    have hk1 : charge-(57/50-x)≤(3/20)*x := by
      dsimp [charge]
      linarith [hx.2]
    have hk2 := pow_le_pow_left₀ hk0 hk1 2
    have hs := sq_nonneg (v-(5/2)*(charge-(57/50-x)))
    linarith

/-- Both actual normal hard contacts at the original q are bounded by
the complete explicit two-angle envelope. -/
theorem actual_middle_bound {aA aB Y g t z v : ℝ}
    (hY : Y∈Icc (167/200 : ℝ) 1) (haA : 0≤aA) (haB : 0≤aB)
    (hA : (aA+1/2)^2+Y^2≤qCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hz : z∈Icc 0 frameCap) (hv : v∈Icc 0 frameCap) (ht : 0≤t)
    (hGA : g+1/2≤(aA-1/2)*Real.cos z-Y*Real.sin z)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v) :
    g+t+charge*(z+v)<209/500 := by
  let x := Y-43/50
  have hx : x∈Icc (-(1/40 : ℝ)) (7/50) := by
    dsimp [x]
    constructor <;> linarith [hY.1,hY.2]
  have hYeq : Y=43/50+x := by dsimp [x]; ring
  have hBeq : 2-Y=57/50-x := by dsimp [x]; ring
  have hRa := (interval_bounds hx).1.1
  have hs := (radius_reserves hx).1
  rw [←hYeq] at hs
  have haR : aA+1/2≤leftRadius x := by
    generalize qCap=Q at hs hA
    nlinarith
  have hcos : 0≤Real.cos z := by linarith [(transport_trig hz).1]
  have hcap := mul_le_mul_of_nonneg_right (show aA-1/2≤leftRadius x-1 by linarith) hcos
  have hleft := left_envelope hx hz
  rw [←hYeq] at hleft
  have hright := right_envelope hx haB ht hv
    (by simpa [←hBeq] using hB) (by simpa [←hBeq] using hBT)
  have hsum := budget_polynomial hx
  nlinarith

end SquaresInCircles.Eight.TableFree.SmallCancelingEnvelope
