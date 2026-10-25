module

public import SquaresInCircles.Eight.TableFree.SignedOppositeHardBounds

/-!
# Whole-interval reserves for the free signed opposite angle

Uncompiled source draft.  The comparison angle varies affinely with the
actual middle tangent.  Its transverse residual is bounded explicitly,
and a single completed square pays for every possible opposite angle.
The formulas below are exact Taylor polynomials, not sampled extrema.
Their combined upper budget is below 83/200 on both full tangent ranges.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SignedOppositeHardEnvelope
open EndpointRotationPenalty

def lowerU (x : ℝ) : ℝ :=
  (rightRadius x-1)*(referenceAngle x-(referenceAngle x)^3/6)+
    rightY x*(1-(referenceAngle x)^2/2)

def upperU (x : ℝ) : ℝ :=
  (rightRadius x-1)*(referenceAngle x-(referenceAngle x)^3/6+
    (referenceAngle x)^5/120)+
    rightY x*(1-(referenceAngle x)^2/2+(referenceAngle x)^4/24)

def lowerV (x : ℝ) : ℝ :=
  (rightRadius x-1)*(1-(referenceAngle x)^2/2)-rightY x*referenceAngle x

def upperValue (x η : ℝ) : ℝ :=
  (rightRadius x-1)*(1-(referenceAngle x)^2/2+(referenceAngle x)^4/24)-
    rightY x*(referenceAngle x-(referenceAngle x)^3/6)+
    charge*referenceAngle x+4*η^2

def objectiveLow (d : ℝ) : ℝ :=
  charge*leftAngle d+upperValue (-d) (lowTolerance d)-1/2

def objectiveHigh (d : ℝ) : ℝ :=
  upperValue d (highTolerance d)-1/2-(43/50)*d

theorem low_U_lower {d : ℝ} (hd : d∈Icc 0 lowLength) :
    charge-lowTolerance d≤lowerU (-d) := by
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  have h3 := pow_le_pow_left₀ hd.1 hd.2 3
  have h4 := pow_le_pow_left₀ hd.1 hd.2 4
  have hcoef : 0≤7074577/62500000-(102461243/500000000)*d-
      (64127809/1200000000)*d^2-(87451/1250000)*d^3-
      (2174743/12000000)*d^4 := by
    dsimp [lowLength] at hd h2 h3 h4
    nlinarith [hd.2]
  have hid : lowerU (-d)-charge+lowTolerance d=
      1537681/3828125000+d*(7074577/62500000-
        (102461243/500000000)*d-(64127809/1200000000)*d^2-
        (87451/1250000)*d^3-(2174743/12000000)*d^4) := by
    dsimp [lowerU,rightRadius,rightY,referenceAngle,charge,lowTolerance]
    ring
  have hp : 0≤1537681/3828125000+d*(7074577/62500000-
      (102461243/500000000)*d-(64127809/1200000000)*d^2-
      (87451/1250000)*d^3-(2174743/12000000)*d^4) := by
    linarith [mul_nonneg hd.1 hcoef]
  linarith

theorem low_U_upper {d : ℝ} (hd : d∈Icc 0 lowLength) :
    upperU (-d)≤charge+lowTolerance d := by
  have h4 := pow_le_pow_left₀ hd.1 hd.2 4
  have hcoef : 0≤145861629877/750000000000-
      (2089928023/96000000000)*d^4 := by
    dsimp [lowLength] at h4
    nlinarith
  have hquad : 0≤22123053791/11962890625000-
      (2373256837/195312500000)*d+(180164586367/1562500000000)*d^2 := by
    nlinarith [sq_nonneg (d-13/220),sq_nonneg d,hd.1]
  have hid : charge+lowTolerance d-upperU (-d)=
      (22123053791/11962890625000-(2373256837/195312500000)*d+
        (180164586367/1562500000000)*d^2)+
      d^3*(145861629877/750000000000-(2089928023/96000000000)*d^4)+
      (188270083717/2400000000000)*d^4+
      (17508975057/640000000000)*d^5+(10158731/2000000000)*d^6 := by
    dsimp [upperU,rightRadius,rightY,referenceAngle,charge,lowTolerance]
    ring
  have hp : 0≤(22123053791/11962890625000-(2373256837/195312500000)*d+
      (180164586367/1562500000000)*d^2)+
      d^3*(145861629877/750000000000-(2089928023/96000000000)*d^4)+
      (188270083717/2400000000000)*d^4+
      (17508975057/640000000000)*d^5+(10158731/2000000000)*d^6 := by
    linarith [mul_nonneg (pow_nonneg hd.1 3) hcoef,pow_nonneg hd.1 4,pow_nonneg hd.1 5,
      pow_nonneg hd.1 6]
  linarith

theorem low_V_lower {d : ℝ} (hd : d∈Icc 0 lowLength) :
    2/5≤lowerV (-d) := by
  have hcoef : 0≤2275681/2500000-(239937/20000000)*d := by
    dsimp [lowLength] at hd
    linarith [hd.2]
  have hid : lowerV (-d)-2/5=28961/3125000+
      d*(2275681/2500000-(239937/20000000)*d)+
      (3813/15625)*d^3+(70153/200000)*d^4 := by
    dsimp [lowerV,rightRadius,rightY,referenceAngle]
    ring
  have hp : 0≤28961/3125000+d*(2275681/2500000-(239937/20000000)*d)+
      (3813/15625)*d^3+(70153/200000)*d^4 := by
    linarith [mul_nonneg hd.1 hcoef,pow_nonneg hd.1 3,pow_nonneg hd.1 4]
  linarith

theorem high_U_lower {d : ℝ} (hd : d∈Icc 0 highLength) :
    charge-highTolerance d≤lowerU d := by
  have h3 := pow_le_pow_left₀ hd.1 hd.2 3
  have hcoef : 0≤1675423/62500000-(102461243/500000000)*d-
      (87451/1250000)*d^3 := by
    dsimp [highLength] at hd h3
    nlinarith [hd.2]
  have hid : lowerU d-charge+highTolerance d=
      1537681/3828125000+d*(1675423/62500000-
        (102461243/500000000)*d-(87451/1250000)*d^3)+
      (64127809/1200000000)*d^3+(2174743/12000000)*d^5 := by
    dsimp [lowerU,rightRadius,rightY,referenceAngle,charge,highTolerance]
    ring
  have hp : 0≤1537681/3828125000+d*(1675423/62500000-
      (102461243/500000000)*d-(87451/1250000)*d^3)+
      (64127809/1200000000)*d^3+(2174743/12000000)*d^5 := by
    linarith [mul_nonneg hd.1 hcoef,pow_nonneg hd.1 3,pow_nonneg hd.1 5]
  linarith

theorem high_U_upper {d : ℝ} (hd : d∈Icc 0 highLength) :
    upperU d≤charge+highTolerance d := by
  have hcoef2 : 0≤180164586367/1562500000000-
      (145861629877/750000000000)*d := by
    dsimp [highLength] at hd
    linarith [hd.2]
  have hcoef4 : 0≤188270083717/2400000000000-
      (17508975057/640000000000)*d := by
    dsimp [highLength] at hd
    linarith [hd.2]
  have hid : charge+highTolerance d-upperU d=
      22123053791/11962890625000+(29717006837/195312500000)*d+
      d^2*(180164586367/1562500000000-(145861629877/750000000000)*d)+
      d^4*(188270083717/2400000000000-(17508975057/640000000000)*d)+
      (10158731/2000000000)*d^6+(2089928023/96000000000)*d^7 := by
    dsimp [upperU,rightRadius,rightY,referenceAngle,charge,highTolerance]
    ring
  have hp : 0≤22123053791/11962890625000+(29717006837/195312500000)*d+
      d^2*(180164586367/1562500000000-(145861629877/750000000000)*d)+
      d^4*(188270083717/2400000000000-(17508975057/640000000000)*d)+
      (10158731/2000000000)*d^6+(2089928023/96000000000)*d^7 := by
    linarith [mul_nonneg (pow_nonneg hd.1 2) hcoef2,mul_nonneg (pow_nonneg hd.1 4) hcoef4,
      hd.1,pow_nonneg hd.1 6,pow_nonneg hd.1 7]
  linarith

theorem high_V_lower {d : ℝ} (hd : d∈Icc 0 highLength) :
    3/10≤lowerV d := by
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  have h3 := pow_le_pow_left₀ hd.1 hd.2 3
  have hbase : 0≤341461/3125000-(2275681/2500000)*d-
      (239937/20000000)*d^2-(3813/15625)*d^3 := by
    dsimp [highLength] at hd h2 h3
    nlinarith [hd.2]
  have hid : lowerV d-3/10=
      341461/3125000-(2275681/2500000)*d-
        (239937/20000000)*d^2-(3813/15625)*d^3+(70153/200000)*d^4 := by
    dsimp [lowerV,rightRadius,rightY,referenceAngle]
    ring
  nlinarith [pow_nonneg hd.1 4]

/-- The full low-range budget decreases below its rational left-end
upper value after its positive tail is collected into one coefficient. -/
theorem objectiveLow_lt {d : ℝ} (hd : d∈Icc 0 lowLength) :
    objectiveLow d<83/200 := by
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  have h3 := pow_le_pow_left₀ hd.1 hd.2 3
  have h4 := pow_nonneg hd.1 4
  have h5 := pow_nonneg hd.1 5
  have hcoef : -1795899747/15312500000+
      (4405933259/12500000000)*d+(2492993371/30000000000)*d^2+
      (253068779/32000000000)*d^3-(268119/50000000)*d^4-
      (67417033/960000000)*d^5≤0 := by
    dsimp [lowLength] at hd h2 h3
    nlinarith [hd.2]
  have hm := mul_nonpos_of_nonneg_of_nonpos hd.1 hcoef
  have hid : objectiveLow d=39623908607/95703125000+
      d*(-1795899747/15312500000+
        (4405933259/12500000000)*d+(2492993371/30000000000)*d^2+
        (253068779/32000000000)*d^3-(268119/50000000)*d^4-
        (67417033/960000000)*d^5) := by
    dsimp [objectiveLow,upperValue,leftAngle,rightRadius,rightY,
      referenceAngle,lowTolerance,charge]
    ring
  have hconstant : (39623908607/95703125000 : ℝ)<83/200 := by norm_num
  linarith

/-- The same explicit pivot works throughout the large tangent range;
the left circle contributes its genuine tangent-line upper bound. -/
theorem objectiveHigh_lt {d : ℝ} (hd : d∈Icc 0 highLength) :
    objectiveHigh d<83/200 := by
  have h3 := pow_le_pow_left₀ hd.1 hd.2 3
  have h4 := pow_le_pow_left₀ hd.1 hd.2 4
  have h2 := pow_nonneg hd.1 2
  have h5 := pow_nonneg hd.1 5
  have hcoef : -822925253/15312500000+
      (4825933259/12500000000)*d-(2492993371/30000000000)*d^2+
      (253068779/32000000000)*d^3+(268119/50000000)*d^4-
      (67417033/960000000)*d^5≤0 := by
    dsimp [highLength] at hd h3 h4
    nlinarith [hd.2]
  have hm := mul_nonpos_of_nonneg_of_nonpos hd.1 hcoef
  have hid : objectiveHigh d=39623908607/95703125000+
      d*(-822925253/15312500000+
        (4825933259/12500000000)*d-(2492993371/30000000000)*d^2+
        (253068779/32000000000)*d^3+(268119/50000000)*d^4-
        (67417033/960000000)*d^5) := by
    dsimp [objectiveHigh,upperValue,rightRadius,rightY,referenceAngle,highTolerance,charge]
    ring
  have hconstant : (39623908607/95703125000 : ℝ)<83/200 := by norm_num
  linarith

end SquaresInCircles.Eight.TableFree.SignedOppositeHardEnvelope
