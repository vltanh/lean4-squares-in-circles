module

public import SquaresInCircles.Eight.Frames.Signed.OppositeHardSigns
public import SquaresInCircles.Eight.Owners.Small.PositiveReflection
public import SquaresInCircles.Eight.Owners.Wide.SmallWrongSign
public import SquaresInCircles.Eight.Words.Crossed.LargeGeometry
public import SquaresInCircles.Eight.Words.Crossed.GACycle
public import SquaresInCircles.Eight.Words.Crossed.SmallGeometry
public import SquaresInCircles.Eight.Words.Crossed.ClampBudget

/-!
# Eight squares: the small crossed HG2 branch of a hard input

The opposite normal sign follows from its larger tangent. The two middle circles and the hard axes
capture the full angle (`HardOuterGeometry.crossed_HG2_small_full_angle`), and the composite on the
original circle builds the new HG0 and GA0 data (`HardOuterGeometry.crossed_HG2_small_data`). The
small HG0 capture of that descendant gives the small common crossing at the radius `q`:
`47/98 < A.y` and `θ_A - θ_H < 1/100` (`HardInput.crossed_HG2_small_output`).
-/

section
/-!
## A direct two-middle envelope for the small canceling branch

Two explicit quadratic radius majorants and
one affine reference angle bound the entire first angular envelope.
The second envelope uses its actual hard contact and a completed square.
Every polynomial comparison holds on the full transverse interval;
there is no maximizer, numerical minimum, or angular mesh premise.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SmallCancelingEnvelope
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

end SquaresInCircles.Eight.SmallCancelingEnvelope
end
end
end

section
/-!
## The small crossed HG2 composite at H and A

The envelope of the two middles and the positive HG2 projection force the full HG angle below
`1/5` (`full_error_short`). On this interval the circle of H gives `U_H < 0.8`
(`rotated_support_upper`), while the rotation of A gives `U_A ≥ 0.835` (`U_lower`), so
feasible-contact continuation gives the whole path of decreasing angle with a strict reserve
(`alignment_reserve`, `actual_cap`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SmallCancelingScalar
open PositiveSmallScalar CrossedCancelingScalar EndpointRotationPenalty EndpointBudgetScalars

theorem full_error_short {H : SignedPoint} {aA aB Y g t r z v : ℝ}
    (hHs : H.Sorted) (hHc : H.AvoidsCore) (hHq : H.Contained qCap)
    (hHy : 0≤H.y) (hY : Y∈Icc (167/200 : ℝ) 1)
    (haA : 0≤aA) (haB : 0≤aB)
    (hA : (aA+1/2)^2+Y^2≤qCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (_hr : 0≤r) (hz : z∈Icc 0 frameCap) (hv : v∈Icc 0 frameCap)
    (hspan : z+r≤frameCap) (ht : 0≤t)
    (hHG : 1/2≤g+S H (z+r))
    (hGA : g+1/2≤(aA-1/2)*Real.cos z-Y*Real.sin z)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v)
    (hbudget : H.y-t+charge*(r-v)<1-S0) : z+r<1/5 := by
  have hmiddle := SmallCancelingEnvelope.actual_middle_bound hY haA haB hA hB hz hv ht hGA hBT
  have hH := SignedPoint.coordinate_bounds hHs hHc hHq le_rfl
  by_contra! hlong
  have hh : z+r∈Icc (39/200 : ℝ) (11/10) := by
    dsimp [frameCap] at hspan
    constructor <;> linarith
  have hreserve := CrossedZeroReserve.strict
    (show H.a-1/2≤183/200 by linarith [hH.2.1]) hh
  have hcos := mul_nonneg hHy (sub_nonneg.mpr (Real.cos_le_one (z+r)))
  have hS0 := SignedOppositeHardEnvelope.budget_reserve
  dsimp [S] at hHG
  nlinarith

theorem rotated_support_upper {H : SignedPoint} {h : ℝ}
    (hHy : 0≤H.y) (hHq : H.Contained qCap)
    (hh : h∈Icc 0 (1/5 : ℝ)) (hS : 103/500≤S H h) : U_H H h<4/5 := by
  have hi : h∈Icc 0 frameCap := ⟨hh.1,by dsimp [frameCap]; linarith [hh.2]⟩
  have ht := transport_trig hi
  have h2 := pow_le_pow_left₀ hh.1 hh.2 2
  have hs := Real.sin_le hh.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := h)
  obtain ⟨m,hm_def⟩ : ∃ m, m=Real.cos h+Real.sin h := ⟨_,rfl⟩
  obtain ⟨n,hn_def⟩ : ∃ n, n=Real.cos h-Real.sin h := ⟨_,rfl⟩
  have hm : 1 ≤ m := by
    have hp := mul_nonneg (show 0≤Real.cos h by linarith [ht.1]) ht.2.2.1
    have hm0 : 0 ≤ m := by rw [hm_def]; linarith [ht.1,ht.2.2.1]
    have hsq : m^2=1+2*(Real.cos h*Real.sin h) := by
      rw [hm_def]
      linear_combination Real.sin_sq_add_cos_sq h
    nlinarith
  have hn : 39/50≤n := by rw [hn_def]; linarith [hh.2]
  have hid : (S H h+m)^2+(U_H H h+n)^2=H.circle := by
    rw [hm_def,hn_def]
    dsimp [S,U_H,SignedPoint.circle]
    rw [abs_of_nonneg hHy]
    linear_combination (((H.a+1/2)^2+(H.y+1/2)^2)*Real.sin_sq_add_cos_sq h)
  by_contra! hbad
  have hs2 := pow_le_pow_left₀ (show (0:ℝ)≤603/500 by norm_num)
    (show 603/500≤S H h+m by linarith) 2
  have hu2 := pow_le_pow_left₀ (show (0:ℝ)≤79/50 by norm_num)
    (show 79/50≤U_H H h+n by linarith) 2
  have hq : H.circle≤9789/2500 := hHq
  linarith

theorem U_lower {q P Y z : ℝ} (C : PositiveSmallScalar.CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hV : 1/2≤V P Y z) : Y≤U P Y z := by
  have ht := transport_trig hz
  have hP : 0≤P := by linarith [C.P_mem.1]
  have hY : 0≤Y := by linarith [C.Y_mem.1]
  have hU : 0≤U P Y z := by
    dsimp [U]
    exact add_nonneg (mul_nonneg hP ht.2.2.1)
      (mul_nonneg hY (by linarith [ht.1]))
  have hv := PositiveSmallScalar.V_upper C hz
  have hv2 := pow_le_pow_left₀ (show 0≤V P Y z by linarith) hv 2
  nlinarith [PositiveSmallScalar.rotation_identity P Y z]

theorem alignment_reserve {q P Y r z : ℝ} {H : SignedPoint}
    (C : PositiveSmallScalar.CapData q P Y)
    (hHy : 0≤H.y) (hHq : H.Contained q)
    (hr : 0≤r) (hz : 0≤z) (hspan : z+r≤1/5)
    (hV : 1/2≤V P Y z) (hpair : 1≤composite H P Y r z) :
    ∀x∈Icc 0 z, 1≤composite H P Y r x ∧
      (7/200)*(z-x)≤composite H P Y r x-composite H P Y r z := by
  apply feasible_left_reserve hz (by norm_num : (0:ℝ)<7/200)
  · exact (continuous_iff_continuousAt.2 fun x =>
      (composite_hasDerivAt H P Y r x).continuousAt).continuousOn
  · intro x _
    exact composite_hasDerivAt H P Y r x
  · intro x hx hfeasible
    have hxi : x∈Icc 0 frameCap := ⟨hx.1,by dsimp [frameCap]; linarith [hx.2]⟩
    have hzi : z∈Icc 0 frameCap := ⟨hz,by dsimp [frameCap]; linarith⟩
    have hhi : x+r∈Icc 0 (1/5 : ℝ) := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have hxV : 1/2≤V P Y x :=
      hV.trans (PositiveSmallScalar.V_antitone C hxi hzi hx.2)
    have hxU := U_lower C hxi hxV
    have hxupper := (PositiveSmallScalar.V_upper C hxi).trans C.P_mem.2
    have hxS : 103/500≤S H (x+r) := by dsimp [composite] at hfeasible; linarith
    have hhU := rotated_support_upper hHy (hHq.trans C.ceiling) hhi hxS
    dsimp [compositeD]
    linarith [C.Y_mem.1]
  · exact hpair

theorem actual_cap {q z : ℝ} {G A : SignedPoint}
    (hq : q≤qCap) (hAs : A.Sorted) (hAc : A.AvoidsCore)
    (hAq : A.Contained q) (hAy : A.y∈Icc (67/200 : ℝ) (1/2))
    (hGy : G.y≤0) (hz : z∈Icc 0 frameCap)
    (hGA : quarterFeasible G A (-z) 0) :
    PositiveSmallScalar.CapData q (A.a-1/2) (A.y+1/2) ∧
      1/2≤V (A.a-1/2) (A.y+1/2) z := by
  have ha := SignedPoint.primary_gt_half hAs hAc
  have hcontact := SignedOppositeHardEnvelope.negative_hard_contact hz hGA
  have ht := transport_trig hz
  have hp := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤A.a-1/2 by linarith)
  have hy := mul_nonneg (show 0≤A.y+1/2 by linarith [hAy.1]) ht.2.2.1
  have ha1 : 1≤A.a := by linarith
  have hcircle : (A.a-1/2+1)^2+(A.y+1/2)^2≤q := by
    have h : A.circle≤q := hAq
    simp only [SignedPoint.circle,abs_of_nonneg (show 0≤A.y by linarith [hAy.1])] at h
    have he : A.a-1/2+1=A.a+1/2 := by ring
    rw [he]
    exact h
  have hupper : A.a-1/2≤397/500 := by
    have hc := hcircle.trans hq
    dsimp [qCap] at hc
    nlinarith [hAy.1]
  refine ⟨⟨⟨by linarith,hupper⟩,⟨by linarith [hAy.1],by linarith [hAy.2]⟩,
    hcircle,hq⟩,?_⟩
  dsimp [V]
  linarith

/-- The tangent `g` of the endpoint is below the tangent of H; only the captured full angle and the
canceling projection enter. -/
theorem tangent_order {H : SignedPoint} {r g : ℝ}
    (_hHy : 0≤H.y) (hHa : H.a≤283/200)
    (hr : r∈Icc 0 (1/5 : ℝ)) (hg : g∈Icc (0:ℝ) (147/500))
    (hHG : 1/2≤g+S H r) : g<H.y := by
  have hi : r∈Icc 0 frameCap := ⟨hr.1,by dsimp [frameCap]; linarith [hr.2]⟩
  have ht := transport_trig hi
  have hsin := Real.sin_le hr.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x := r)
  have h2 := pow_le_pow_left₀ hr.1 hr.2 2
  have hc98 : 49/50≤Real.cos r := by linarith
  by_contra! hbad
  have hprimary := mul_le_mul_of_nonneg_right
    (show H.a-1/2≤183/200 by linarith) ht.2.2.1
  have hminor := mul_le_mul_of_nonneg_right
    (show H.y-1/2≤g-1/2 by linarith) (show 0≤Real.cos r by linarith [ht.1])
  have hgcos := mul_le_mul_of_nonpos_left hc98
    (show g-1/2≤0 by linarith [hg.2])
  dsimp [S] at hHG
  linarith [hr.2,hg.2]

end SquaresInCircles.Eight.SmallCancelingScalar
end
end
end

section
/-!
## An actual small crossed HG2-to-HG0 output at the source q

The complete composite reserve determines the
new G tangent at the original A frame.  Its actual q-circle point has
strict HG0 slack.  Positive G motion leaves strict aligned GA slack,
which is spent on the original A primary.  Original A deficits and all
other anchor data survive; no artificial circle lift is counted as loss.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SmallCancelingConstruction
open PositiveSmallScalar CrossedCancelingScalar EndpointRotationPenalty

theorem actual_output {q r z : ℝ} {H G A : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hHs : H.Sorted) (hAs : A.Sorted)
    (hHc : H.AvoidsCore) (hAc : A.AvoidsCore)
    (hHq : H.Contained q) (hAq : A.Contained q)
    (hHy : 0≤H.y) (hAy : A.y∈Icc (67/200 : ℝ) (1/2)) (hGy : G.y≤0)
    (hr : r∈Ioc 0 frameCap) (hz : z∈Icc 0 frameCap) (hspan : z+r<1/5)
    (hHG : zeroFeasible H G (z+r) 2) (hGA : quarterFeasible G A (-z) 0) :
    Nonempty (CrossedGAData q H G A r z) := by
  obtain ⟨C,hV⟩ := SmallCancelingScalar.actual_cap hq hAs hAc hAq hAy hGy hz hGA
  have hfull : z+r≤frameCap := by dsimp [frameCap]; linarith only [hspan]
  have hpair := original_pair hr.1.le hz.1 hfull hHG hGA
  have hreserve := SmallCancelingScalar.alignment_reserve C hHy hHq hr.1.le hz.1
    hspan.le hV hpair 0 ⟨le_rfl,hz.1⟩
  have hcomp0 : composite H (A.a-1/2) (A.y+1/2) r 0=A.a-1/2+S H r := by
    simp only [composite,V,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero,zero_add]
  have hzero : 1≤A.a-1/2+S H r := hcomp0 ▸ hreserve.1
  obtain ⟨g,hg_def⟩ : ∃ g, g=max 0 (1/2-S H r) := ⟨_,rfl⟩
  have hg0 : 0≤g := by rw [hg_def]; exact le_max_left _ _
  have hga : g+1≤A.a := by
    have hh : g≤A.a-1 := by
      rw [hg_def]
      exact max_le (by linarith only [C.P_mem.1]) (by linarith only [hzero])
    linarith only [hh]
  have hg : g∈Icc (0:ℝ) (147/500) := ⟨hg0,by linarith only [hga,C.P_mem.2]⟩
  have hhg : 1/2≤g+S H r := by
    have hh := le_max_right 0 (1/2-S H r)
    rw [← hg_def] at hh
    linarith only [hh]
  have hHbounds := SignedPoint.coordinate_bounds hHs hHc hHq hq
  have horder : g<H.y := SmallCancelingScalar.tangent_order hHy hHbounds.2.1.le
    ⟨hr.1.le,by linarith only [hspan,hz.1]⟩ hg hhg
  have hdiag : |-g|≤diagonalCoordinate q := by
    rw [abs_neg,abs_of_nonneg hg0]
    linarith only [hg.2,(uniform_circle_reserves hqL hq).1]
  obtain ⟨hGs,hGq,hGc⟩ := SignedPoint.outerAt_spec hqL hdiag
  obtain ⟨G',hG'⟩ : ∃ G', G'=SignedPoint.outerAt q (-g) := ⟨_,rfl⟩
  rw [← hG'] at hGs hGq hGc
  have hGyEq : G'.y= -g := by rw [hG']; rfl
  have hGcircle : (G'.a+1/2)^2+(g+1/2)^2=q := by
    have h : G'.circle=q := hGq
    simp only [SignedPoint.circle,hGyEq,abs_neg,abs_of_nonneg hg0] at h
    exact h
  have hHcircle : (H.a+1/2)^2+(H.y+1/2)^2≤q := by
    have h : H.circle≤q := hHq
    simp only [SignedPoint.circle,abs_of_nonneg hHy] at h
    exact h
  have hminor := pow_lt_pow_left₀ (show g+1/2<H.y+1/2 by linarith only [horder])
    (show 0≤g+1/2 by linarith only [hg0]) (by decide : (2:ℕ)≠0)
  have hprimary : H.a<G'.a := by
    by_contra! hle
    have h2 := pow_le_pow_left₀ (show 0≤G'.a+1/2 by linarith only [hGs.1])
      (show G'.a+1/2≤H.a+1/2 by linarith only [hle]) 2
    linarith only [h2,hHcircle,hGcircle,hminor]
  have hsin : 0<Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr.1
    (by have := hr.2; dsimp [frameCap] at this; linarith only [this,Real.pi_gt_three])
  have hpositive := mul_pos (sub_pos.mpr hprimary) hsin
  have hnonneg := mul_nonneg (sub_nonneg.mpr horder.le)
    (sub_nonneg.mpr (Real.cos_le_one r))
  have hHGzero : zeroFeasible H G' r 0 := by
    rw [zeroFeasible,edgeWidth_positive_formula ⟨hr.1.le,hr.2⟩]
    simp only [zeroProjection,Matrix.cons_val_zero,hGyEq]
    dsimp [S] at hhg
    linarith only [hhg,hpositive,hnonneg]
  have hstrictGA : 0<z → g+1<A.a := by
    intro hzpos
    have ht := transport_trig hz
    have hsinz : 0<Real.sin z := Real.sin_pos_of_pos_of_lt_pi hzpos
      (by have := hz.2; dsimp [frameCap] at this; linarith only [this,Real.pi_gt_three])
    have hp := mul_le_mul_of_nonneg_left ht.2.1
      (show 0≤A.a-1/2 by linarith only [C.P_mem.1])
    have hys := mul_pos (show 0<A.y+1/2 by linarith only [hAy.1]) hsinz
    have ha1 : 1<A.a := by dsimp [V] at hV; linarith only [hV,hp,hys]
    have hf0 : 1<A.a-1/2+S H r := by
      have hh := hreserve.2
      rw [hcomp0,sub_zero] at hh
      linarith only [hh,hpair,hzpos]
    by_cases hs : 0≤1/2-S H r
    · rw [hg_def,max_eq_right hs]
      linarith only [hf0]
    · have heq : g=0 := by rw [hg_def]; exact max_eq_left (le_of_not_ge hs)
      rw [heq]
      linarith only [ha1]
  have hAout : ∃ A' : SignedPoint, A'.Sorted ∧ A'.AvoidsCore ∧
      A'.Contained q ∧ A'.y=A.y ∧ g+1≤A'.a ∧
      (0<z → A'.circle<q) ∧ (A.circle<q → A'.circle<q) := by
    by_cases hz0 : z=0
    · exact ⟨A,hAs,hAc,hAq,rfl,hga,by intro h; linarith only [h,hz0],fun h => h⟩
    · have hzpos : 0<z := lt_of_le_of_ne hz.1 (Ne.symm hz0)
      have hstrict := hstrictGA hzpos
      obtain ⟨A',hA'⟩ : ∃ A' : SignedPoint, A'=⟨(A.a+g+1)/2,A.y⟩ := ⟨_,rfl⟩
      have hA'a : A'.a=(A.a+g+1)/2 := by rw [hA']
      have hA'y : A'.y=A.y := by rw [hA']
      have ha' : g+1<A'.a ∧ A'.a<A.a := by rw [hA'a]; constructor <;> linarith only [hstrict]
      have hAs' : A'.Sorted := by
        refine ⟨by linarith only [ha'.1,hg0],?_⟩
        rw [hA'y,abs_of_nonneg (show 0≤A.y by linarith only [hAy.1])]
        linarith only [ha'.1,hAy.2,hg0]
      have hAc' : A'.AvoidsCore := by
        dsimp [SignedPoint.AvoidsCore,SignedPoint.coreDistance]
        rw [max_eq_left (by linarith only [ha'.1,hg0] : 0≤A'.a-1/2)]
        have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/12)
          (show 1/12≤A'.a-1/2 by linarith only [ha'.1,hg0]) 2
        linarith only [h2,sq_nonneg (max (|A'.y|-1/2) 0)]
      have hsq := pow_lt_pow_left₀ (show A'.a+1/2<A.a+1/2 by linarith only [ha'.2])
        (show 0≤A'.a+1/2 by linarith only [ha'.1,hg0]) (by decide : (2:ℕ)≠0)
      have hloss : A'.circle<A.circle := by
        simp only [SignedPoint.circle,hA'y]
        linarith only [hsq]
      have hstrictq : A'.circle<q := hloss.trans_le hAq
      exact ⟨A',hAs',hAc',hstrictq.le,hA'y,ha'.1.le,fun _ => hstrictq,
        fun h => hloss.trans h⟩
  obtain ⟨A',hAs',hAc',hAq',hAy',hga',hstrict',hloss'⟩ := hAout
  exact ⟨{
    pointG := G'
    pointA := A'
    G_sorted := hGs
    G_avoids := hGc
    G_contained := hGq.le
    G_nonpos := by rw [hGyEq]; linarith only [hg0]
    A_sorted := hAs'
    A_avoids := hAc'
    A_contained := hAq'
    A_tangent := hAy'
    HG_zero := hHGzero
    GA_hard := by
      simpa [quarterFeasible,quarterProjection,hGyEq] using
        (show (1:ℝ)≤ -g+A'.a by linarith only [hga'])
    A_strict := hstrict'
    A_loss := hloss' }⟩

end SquaresInCircles.Eight.SmallCancelingConstruction
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCycle
open Candidate EndpointRotationPenalty EndpointBudgetScalars

theorem HardOuterGeometry.crossed_HG2_small_full_angle {q : ℝ}
    (I : HardOuterGeometry q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hHG : I.cycle.Feasible H 2) : I.cycle.theta G-I.cycle.theta H<1/5 := by
  let r := I.cycle.theta A-I.cycle.theta H
  let z := I.cycle.theta G-I.cycle.theta A
  let v := I.cycle.theta A-I.cycle.theta T
  let Y := (I.cycle.point A).y+1/2
  have hr : 0≤r := (sub_pos.mpr hHA).le
  have hz : z∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hAG,(le_abs_self z).trans (I.necessary.spread G A)⟩
  have hv : v∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hTA,(le_abs_self v).trans (I.necessary.spread A T)⟩
  have hspan : z+r≤frameCap := by
    have hh := (le_abs_self (I.cycle.theta G-I.cycle.theta H)).trans (I.necessary.spread G H)
    dsimp [z,r]
    linarith
  have hhi : z+r∈Icc 0 frameCap := ⟨by linarith [hz.1],hspan⟩
  have hY : Y∈Icc (167/200 : ℝ) 1 := by
    dsimp [Y]
    constructor <;> linarith [hsmall.1,hsmall.2]
  have hTy := I.large_middle_T_positive hq hAB hnorm hTA hAG
    (by linarith [hsmall.2])
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-z) 0 := by
    simpa [z,Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,neg_sub]
      using I.GA_hard
  have hGA' := SignedOppositeHardEnvelope.negative_hard_contact hz hGA
  have hBT : quarterFeasible (I.cycle.point B) (I.cycle.point T) (-v) 2 := by
    rw [show -v=I.cycle.theta T-I.cycle.theta B by dsimp [v]; rw [←hAB]; ring]
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg] using I.BT_hard
  have hBTref : quarterFeasible (I.cycle.point T).reflect (I.cycle.point B).reflect (-v) 0 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect _ _ (-v) 2).2 hBT
  have hBT' := SignedOppositeHardEnvelope.negative_hard_contact hv hBTref
  simp only [SignedPoint.reflect,neg_neg] at hBT'
  have hyB : -(I.cycle.point B).y+1/2=2-Y := by dsimp [Y]; linarith
  rw [hyB] at hBT'
  have hAcircle : ((I.cycle.point A).a+1/2)^2+Y^2≤qCap := by
    simpa [Y,SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg I.anchors_normal.A_nonneg]
      using (I.necessary.contained A).trans hq
  have hBcircle : ((I.cycle.point B).a+1/2)^2+(2-Y)^2≤qCap := by
    have hb := (I.necessary.contained B).trans hq
    dsimp [SignedPoint.Contained,SignedPoint.circle] at hb
    rw [abs_of_nonpos I.anchors_normal.B_nonpos,hyB] at hb
    exact hb
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) (z+r) 2 := by
    convert hHG using 1
    simp [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg,z,r]
  have hHGscalar : 1/2≤ -(I.cycle.point G).y+
      CrossedCancelingScalar.S (I.cycle.point H) (z+r) := by
    rw [zeroFeasible,edgeWidth_positive_formula hhi] at hHG'
    simp [zeroProjection] at hHG'
    dsimp [CrossedCancelingScalar.S]
    linarith
  have hTD := (signed_outer_charges hq I.necessary I.anchors_normal I.witnesses I.zero_signs).2
  have hep := I.endpoint_bound hq
  have hbudget : (I.cycle.point H).y-(I.cycle.point T).y+EndpointRotationPenalty.charge*(r-v)<1-S0 := by
    dsimp [r,v,epsilon] at *
    linarith
  have hh := SmallCancelingScalar.full_error_short
    (I.necessary.sorted H) (I.necessary.core H) ((I.necessary.contained H).trans hq)
    I.anchors_normal.H_nonneg hY (I.necessary.sorted A).1.le (I.necessary.sorted B).1.le
    hAcircle hBcircle hr hz hv hspan hTy.le hHGscalar hGA' hBT' hbudget
  dsimp [z,r] at hh
  linarith

theorem HardOuterGeometry.crossed_HG2_small_data {q : ℝ}
    (I : HardOuterGeometry q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hGy : (I.cycle.point G).y≤0) (hHG : I.cycle.Feasible H 2) :
    Nonempty (CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) := by
  let r := I.cycle.theta A-I.cycle.theta H
  let z := I.cycle.theta G-I.cycle.theta A
  have hr : r∈Ioc 0 frameCap :=
    ⟨sub_pos.mpr hHA,(le_abs_self r).trans (I.necessary.spread A H)⟩
  have hz : z∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hAG,(le_abs_self z).trans (I.necessary.spread G A)⟩
  have hfull := I.crossed_HG2_small_full_angle hq hAB hnorm hTA hAG hHA hsmall hHG
  have hspan : z+r<1/5 := by dsimp [z,r]; linarith
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) (z+r) 2 := by
    convert hHG using 1
    simp [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg,z,r]
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-z) 0 := by
    simpa [z,Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,neg_sub]
      using I.GA_hard
  exact SmallCancelingConstruction.actual_output hqL hq
    (I.necessary.sorted H) (I.necessary.sorted A) (I.necessary.core H) (I.necessary.core A)
    (I.necessary.contained H) (I.necessary.contained A) I.anchors_normal.H_nonneg
    hsmall hGy hr hz hspan hHG' hGA

theorem HardOuterGeometry.crossed_HG2_small_output {q : ℝ}
    (I : HardOuterGeometry q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hGy : (I.cycle.point G).y≤0) (hHG : I.cycle.Feasible H 2) :
    47/98<(I.cycle.point A).y ∧ I.cycle.theta A-I.cycle.theta H<1/100 ∧
      Nonempty (CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
        (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) := by
  obtain ⟨O⟩ := I.crossed_HG2_small_data hqL hq hAB hnorm hTA hAG hHA hsmall hGy hHG
  let J := I.fromCrossedGAData hAB O
  have hAB' : J.cycle.theta A=J.cycle.theta B := hAB
  have hsum' : (J.cycle.point A).y-(J.cycle.point B).y=1 := by
    change O.pointA.y-(I.cycle.point B).y=1
    rw [O.A_tangent]
    exact hnorm
  have hsmall' : (J.cycle.point A).y∈Icc (67/200 : ℝ) (1/2) := by
    change O.pointA.y∈Icc (67/200 : ℝ) (1/2)
    rw [O.A_tangent]
    exact hsmall
  have hHG' : J.cycle.Feasible H 0 := by
    simpa [J,HardOuterGeometry.fromCrossedGAData,crossedGACycle,Feasible,slack,edge,word,
      delta,next,H,G,A,zeroFeasible,sub_nonneg] using O.HG_zero
  have hcap := J.crossed_HG0_small_reserve hqL hq hAB' hsum' hTA le_rfl hHA
    hsmall' O.G_nonpos hHG'
  refine ⟨?_,hcap.2.1,⟨O⟩⟩
  have hA := hcap.1
  change 47/98<O.pointA.y at hA
  simpa only [O.A_tangent] using hA

theorem HardInput.crossed_HG2_small_output {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hHG : I.cycle.Feasible H 2) :
    47/98<(I.cycle.point A).y ∧ I.cycle.theta A-I.cycle.theta H<1/100 ∧
      Nonempty (CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
        (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) := by
  have hG := I.small_middle_G_negative hqL hq hAB hnorm
    ⟨by linarith [hsmall.1],hsmall.2⟩ hTA hAG
  exact I.outerGeometry.crossed_HG2_small_output hqL hq hAB hnorm hTA hAG hHA hsmall hG.le hHG

end SquaresInCircles.Eight.SignedCycle
end
end
end
