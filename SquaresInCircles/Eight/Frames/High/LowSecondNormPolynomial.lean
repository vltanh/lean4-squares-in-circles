module

public import SquaresInCircles.Eight.Frames.Diagonal.Tails
public import SquaresInCircles.Eight.Frames.High.Arc
public import SquaresInCircles.Eight.Frames.Low.HighParallelCalculus
public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds

/-!
# Eight squares: the second quartic norm majorant by positive quadratic expressions

One exact Taylor polynomial is bounded on each sign of the centered
coordinate.  The positive half reduces to two completed squares; the
negative half uses one endpoint power bound.  Neither half is split
into subintervals or supplied with coefficient arrays.
-/

section
/-!
## The high/high forms with a fixed target

For a high/high pair with the multiplier `l`, the source is bounded by its value at the axial end
or by the support of the whole circle (`sourceValue`, with `circle` false or true), and the target
by its value at one of the two ends of the high arc (`endA`, `endB`); the support of the pair is
then the function `F circle i j cut l x` of the angle (`support_formula`), with its first three
derivatives (`F_deriv`, `Fd_deriv`, `Fdd_deriv`). When `Cc ≥ 0`, `Ss ≤ 0` and the slope at the
right end is negative, the minimum of `F` on an interval is at an end (`endpoint_minimum`); when
the amplitude satisfies `Cc² + Ss² < 1`, `F` is monotone (`amplitude_monotone`), as for the
multiplier `17/50` (`small_multiplier_amplitude`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighHighFixedCalculus
open FramePair FramePairCalculus FrameDiagonalArc FrameDiagonalLabels

def gamma : ℝ := 9099/10000
def endA (cut : Bool) : ℝ := if cut then a1 else FrameDiagonalArc.a0
def endB (cut : Bool) : ℝ := if cut then b1 else 0
def sourceU (i : Bool) (l : ℝ) : ℝ := sign i*u-l
def sourceV (i : Bool) (l : ℝ) : ℝ := sign i*(v-l)
def sourceBase (circle i : Bool) (l : ℝ) : ℝ :=
  if circle then -sourceU i l else sourceU i l*FrameDiagonalArc.a0
def sourceEnergy (circle i : Bool) (l : ℝ) : ℝ :=
  if circle then (sourceU i l)^2+(sourceV i l)^2 else 0
def sourceNorm (circle i : Bool) (l : ℝ) : ℝ := Real.sqrt (sourceEnergy circle i l)
def sourceValue (circle i : Bool) (l : ℝ) : ℝ := sourceBase circle i l-R*sourceNorm circle i l
def constantBase (circle i j cut : Bool) (l : ℝ) : ℝ :=
  9/100+l-sign i*u*FrameDiagonalArc.a0-sign j*H (endB cut)+sourceBase circle i l
def Cc (j cut : Bool) (l : ℝ) : ℝ := l*(1+endA cut+sign j*endB cut)-9/100
def Ss (j cut : Bool) (l : ℝ) : ℝ := l*(1-endA cut+sign j*endB cut)-9/100
def F (circle i j cut : Bool) (l x : ℝ) : ℝ :=
  x+constantBase circle i j cut l+Cc j cut l*Real.cos x+Ss j cut l*Real.sin x-
    R*sourceNorm circle i l
def Fd (j cut : Bool) (l x : ℝ) : ℝ :=
  1-Cc j cut l*Real.sin x+Ss j cut l*Real.cos x
def Fdd (j cut : Bool) (l x : ℝ) : ℝ :=
  -Cc j cut l*Real.cos x-Ss j cut l*Real.sin x
def Fddd (j cut : Bool) (l x : ℝ) : ℝ :=
  Cc j cut l*Real.sin x-Ss j cut l*Real.cos x

theorem endpoint_circle (cut : Bool) : (endA cut+1)^2+(endB cut)^2=2*Q0 := by
  cases cut
  · simp only [endA,endB,Bool.false_eq_true,↓reduceIte,FrameDiagonalArc.a0]
    rw [← R_sq]
    ring
  · exact first_circle

theorem endpoint_A (cut : Bool) : A (endB cut)=endA cut := by
  cases cut <;> simp [endA,endB]

theorem sourceNorm_nonneg (circle i : Bool) (l : ℝ) : 0≤ sourceNorm circle i l :=
  Real.sqrt_nonneg _
theorem sourceNorm_sq (circle i : Bool) (l : ℝ) :
    (sourceNorm circle i l)^2=sourceEnergy circle i l := by
  apply Real.sq_sqrt
  cases circle <;> dsimp [sourceEnergy] <;> positivity

theorem sourceValue_eq (circle i : Bool) (l : ℝ) :
    sourceValue circle i l=
      if circle then FrameDiagonalSupport.sourceCircle false i l
      else FrameDiagonalSupport.source false i l 0 := by
  cases circle <;> simp [sourceValue,sourceBase,sourceNorm,sourceEnergy,sourceU,sourceV,
    FrameDiagonalSupport.sourceCircle,FrameDiagonalSupport.source,
    FrameDiagonalSupport.sourceU,FrameDiagonalSupport.sourceV,
    primary,transverse,linear,A_zero]

theorem support_formula (circle i j cut : Bool) (l : ℝ) {x : ℝ}
    (hx : x∈Icc 0 (Real.pi/2)) :
    FrameDiagonalSupport.base false false i j l x+sourceValue circle i l+
      FrameDiagonalSupport.target false j l x (endB cut)=F circle i j cut l x := by
  rw [FrameDiagonalSupport.fixed_target_first false false i j l (endB cut)
    (sourceValue circle i l) hx,endpoint_A]
  dsimp [F,constantBase,Cc,Ss,sourceValue,constant,marker]
  ring

theorem F_deriv (circle i j cut : Bool) (l x : ℝ) :
    HasDerivAt (F circle i j cut l) (Fd j cut l x) x := by
  have h := ((((hasDerivAt_id x).add_const (constantBase circle i j cut l)).add
    ((Real.hasDerivAt_cos x).const_mul (Cc j cut l))).add
    ((Real.hasDerivAt_sin x).const_mul (Ss j cut l))).sub_const
    (R*sourceNorm circle i l)
  convert h using 1
  · funext y
    simp only [F,id,Pi.add_apply]
  · dsimp only [Fd]
    ring

theorem Fd_deriv (j cut : Bool) (l x : ℝ) : HasDerivAt (Fd j cut l) (Fdd j cut l x) x := by
  have h := (((Real.hasDerivAt_sin x).const_mul (-Cc j cut l)).const_add 1).add
    ((Real.hasDerivAt_cos x).const_mul (Ss j cut l))
  convert h using 1
  · funext y
    simp only [Fd,Pi.add_apply]
    ring
  · dsimp only [Fdd]
    ring

theorem Fdd_deriv (j cut : Bool) (l x : ℝ) : HasDerivAt (Fdd j cut l) (Fddd j cut l x) x := by
  have h := ((Real.hasDerivAt_cos x).const_mul (-Cc j cut l)).sub
    ((Real.hasDerivAt_sin x).const_mul (Ss j cut l))
  convert h using 1
  · funext y
    simp only [Fdd,Pi.sub_apply]
  · dsimp only [Fddd]
    ring

theorem endpoint_minimum (circle i j cut : Bool) {l a b x : ℝ}
    (ha : 0≤a) (hb : b≤Real.pi/2) (hx : x∈Icc a b)
    (hC : 0≤Cc j cut l) (hS : Ss j cut l≤0) (hd : Fd j cut l b<0) :
    min (F circle i j cut l a) (F circle i j cut l b)≤F circle i j cut l x := by
  apply SecondWord.MinimumCalculus.endpoint_minimum hx
    (fun t _ => F_deriv circle i j cut l t)
    (fun t _ => Fd_deriv j cut l t) (fun t _ => Fdd_deriv j cut l t) _ hd
  intro t ht
  have hq := FrameLowPair.quadrant ⟨ha.trans ht.1,ht.2.trans hb⟩
  have h1 := mul_nonneg hC hq.1
  have h2 := mul_nonpos_of_nonpos_of_nonneg hS hq.2.2.1
  dsimp [Fddd]
  linarith

theorem amplitude_monotone (circle i j cut : Bool) {l : ℝ}
    (hamp : (Cc j cut l)^2+(Ss j cut l)^2<1) : Monotone (F circle i j cut l) := by
  apply monotone_of_hasDerivAt_nonneg (fun x => F_deriv circle i j cut l x)
  intro x
  have hh : Cc j cut l*Real.sin x+(-Ss j cut l)*Real.cos x<1 := by
    apply FrameCoreArc.projection_lt (by norm_num : (0:ℝ)<1)
    simpa only [neg_sq,one_pow] using hamp
  dsimp [Fd]
  linarith

theorem small_multiplier_amplitude (cut : Bool) :
    (Cc false cut (17/50))^2+(Ss false cut (17/50))^2<1 := by
  have hc := endpoint_circle cut
  have ha0 := a0_precise
  have ha1 := a1_precise
  cases cut
  · dsimp [Cc,Ss,endA,endB,sign] at *
    norm_num [Q0] at hc
    nlinarith
  · dsimp [Cc,Ss,endA,endB,sign] at *
    rw [b1_eq] at *
    norm_num [Q0] at hc
    nlinarith

end SquaresInCircles.Eight.FrameHighHighFixedCalculus
end
end
end

section
/-!
## The first quartic norm majorant on the whole high/low interval

The squared difference decreases on `[-.11,.58]`.  Its derivative
sign follows from coefficient grouping and a completed square, and
its final endpoint is positive.  These are identities and inequalities
for one polynomial on one complete interval, not sampled values.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowFirstNormPolynomial
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus

def domain : Set ℝ := Icc (-(11/100:ℝ)) (29/50)
def lam (x : ℝ) : ℝ := 495453/500000-(7/25)*x
def U1 (w : ℝ) : ℝ :=
  12336/15625-(48483/250000)*w+(25833/1000000)*w^2+
    (6347/1000000)*w^3+(71/62500)*w^4
def U1d (w : ℝ) : ℝ :=
  -(48483/250000)+2*(25833/1000000)*w+
    3*(6347/1000000)*w^2+4*(71/62500)*w^3
def X1 (w : ℝ) : ℝ := FrameHighArc.u^2+(lam (19/100+w)-FrameHighArc.v)^2
def A (w : ℝ) : ℝ := (U1 w)^2-X1 w
def Ad (w : ℝ) : ℝ := 2*U1 w*U1d w+(14/25)*(lam (19/100+w)-FrameHighArc.v)

theorem lam_bounds {x : ℝ} (hx : x∈Icc (2/25:ℝ) (77/100)) :
    (9/100:ℝ)<lam x ∧ lam x<1 := by dsimp [lam]; constructor <;> linarith [hx.1,hx.2]

theorem U1_deriv (w : ℝ) : HasDerivAt U1 (U1d w) w := by
  have h := ((((hasDerivAt_const w (12336/15625:ℝ)).sub ((hasDerivAt_id' w).const_mul (48483/250000))).add
    ((hasDerivAt_pow 2 w).const_mul (25833/1000000))).add
      ((hasDerivAt_pow 3 w).const_mul (6347/1000000))).add
        ((hasDerivAt_pow 4 w).const_mul (71/62500))
  refine h.congr_deriv ?_
  rw [U1d]
  ring

theorem A_deriv (w : ℝ) : HasDerivAt A (Ad w) w := by
  have hl : HasDerivAt (fun z => lam (19/100+z)-FrameHighArc.v) (-(7/25:ℝ)) w :=
    (((hasDerivAt_const w (495453/500000:ℝ)).sub
      (((hasDerivAt_id' w).const_add (19/100)).const_mul (7/25))).sub_const
        FrameHighArc.v).congr_deriv (by ring)
  have h := ((U1_deriv w).pow 2).sub ((hl.pow 2).const_add (FrameHighArc.u^2))
  refine h.congr_deriv ?_
  rw [Ad]
  ring

theorem negative_derivative_remainder {y : ℝ} (hy : 0≤y) :
    Ad (-y)< -(97/100000000:ℝ)+(341/50000000)*y^2+
      (169/62500000)*y^3+(101/1000000)*y^6 := by
  have h2 := pow_nonneg hy 2
  have h3 := pow_nonneg hy 3
  have h4 := pow_nonneg hy 4
  have h5 := pow_nonneg hy 5
  have h6 := pow_nonneg hy 6
  have h7 := pow_nonneg hy 7
  simp only [Ad,U1,U1d,lam,FrameHighArc.v]
  linarith

theorem positive_derivative_remainder {w : ℝ} (hw : 0≤w) :
    Ad w< -(97/100000000:ℝ)+(269/1000000000)*w+(341/50000000)*w^2+
      w^4*(-563/1000000+(297/500000)*w+(101/1000000)*w^2+(13/1250000)*w^3) := by
  have h2 := pow_nonneg hw 2
  have h3 := pow_nonneg hw 3
  have h4 := pow_nonneg hw 4
  have h5 := pow_nonneg hw 5
  have h6 := pow_nonneg hw 6
  have h7 := pow_nonneg hw 7
  simp only [Ad,U1,U1d,lam,FrameHighArc.v]
  linarith

theorem derivative_negative {w : ℝ} (hw : w∈domain) : Ad w<0 := by
  by_cases hneg : w≤0
  · have hy : -w∈Icc (0:ℝ) (11/100) := ⟨by linarith,by linarith [hw.1]⟩
    have hr := negative_derivative_remainder hy.1
    simp only [neg_neg] at hr
    have h2 := pow_le_pow_left₀ hy.1 hy.2 2
    have h3 := pow_le_pow_left₀ hy.1 hy.2 3
    have h6 := pow_le_pow_left₀ hy.1 hy.2 6
    nlinarith
  · have hp : 0≤w := le_of_not_ge hneg
    have hr := positive_derivative_remainder hp
    have h2 := pow_le_pow_left₀ hp hw.2 2
    have h3 := pow_le_pow_left₀ hp hw.2 3
    have hb : -563/1000000+(297/500000)*w+(101/1000000)*w^2+
        (13/1250000)*w^3≤-(9/50000:ℝ) := by linarith [hw.2]
    have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg hp 4)
    have hlin := mul_le_mul_of_nonneg_left hw.2 (by norm_num : (0:ℝ)≤269/1000000000)
    nlinarith [sq_nonneg ((9/25000:ℝ)*w^2-341/50000000)]

theorem A_antitone : AntitoneOn A domain := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun w _ => (A_deriv w).continuousAt.continuousWithinAt
  · exact fun w _ => A_deriv w
  · exact fun w hw => (derivative_negative (Ioo_subset_Icc_self hw)).le

theorem final_reserve : (33/12500000:ℝ)<A (29/50) := by
  norm_num [A,U1,X1,lam,FrameHighArc.u,FrameHighArc.v]

theorem squared_reserve {w : ℝ} (hw : w∈domain) : (33/12500000:ℝ)<A w :=
  final_reserve.trans_le (A_antitone hw ⟨by norm_num,le_rfl⟩ hw.2)

theorem U1_positive {w : ℝ} (hw : w∈domain) : (67/100:ℝ)<U1 w := by
  by_cases hneg : w≤0
  · have hy : -w∈Icc (0:ℝ) (11/100) := ⟨by linarith,by linarith [hw.1]⟩
    have h3 := pow_le_pow_left₀ hy.1 hy.2 3
    have h4 := pow_nonneg hy.1 4
    have h2 := sq_nonneg w
    dsimp [U1]
    nlinarith
  · have hp : 0≤w := le_of_not_ge hneg
    have h2 := sq_nonneg w
    have h3 := pow_nonneg hp 3
    have h4 := pow_nonneg hp 4
    dsimp [U1]
    nlinarith [hw.2]

end SquaresInCircles.Eight.FrameHighLowFirstNormPolynomial
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowSecondNormPolynomial
open FrameHighLowFirstNormPolynomial FrameCircleArc

def U2 (w : ℝ) : ℝ := 302419/500000+(11993/12500)*w-(6409/31250)*w^2-
  (3817/62500)*w^3+(2247/50000)*w^4
def X2 (w : ℝ) : ℝ := FrameLowArc.u^2+FrameLowArc.v^2+(lam (19/100+w))^2+
  2*lam (19/100+w)*(FrameLowArc.u*Arithmetic.sin9 (19/100+w)-
    FrameLowArc.v*Arithmetic.cos8 (19/100+w))
def B (w : ℝ) : ℝ := (U2 w)^2-X2 w-9/100000000
def negativeLower (y : ℝ) : ℝ :=
  3/2500000-(89/20000000)*y-(113/20000000)*y^2+
    y^3*(1067/1000000-(39349/500000)*y^2)-(181/12500)*y^6
def positiveLower (w : ℝ) : ℝ :=
  3/2500000+(111/25000000)*w-(113/20000000)*w^2-(267/250000)*w^3+
    (63/100000)*w^4+(7869/100000)*w^5-(181/12500)*w^6-
      (4493/1000000)*w^7-(323/20000000)*w^9

theorem negative_remainder {y : ℝ} (hy : 0≤y) : negativeLower y<B (-y) := by
  have h2 := pow_nonneg hy 2
  have h3 := pow_nonneg hy 3
  have h4 := pow_nonneg hy 4
  have h5 := pow_nonneg hy 5
  have h6 := pow_nonneg hy 6
  have h7 := pow_nonneg hy 7
  have h8 := pow_nonneg hy 8
  have h9 := pow_nonneg hy 9
  have h10 := pow_nonneg hy 10
  simp only [negativeLower,B,U2,X2,lam,FrameLowArc.u,FrameLowArc.v,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos8]
  linarith

theorem positive_remainder {w : ℝ} (hw : 0≤w) : positiveLower w<B w := by
  have h2 := pow_nonneg hw 2
  have h3 := pow_nonneg hw 3
  have h4 := pow_nonneg hw 4
  have h5 := pow_nonneg hw 5
  have h6 := pow_nonneg hw 6
  have h7 := pow_nonneg hw 7
  have h8 := pow_nonneg hw 8
  have h9 := pow_nonneg hw 9
  have h10 := pow_nonneg hw 10
  simp only [positiveLower,B,U2,X2,lam,FrameLowArc.u,FrameLowArc.v,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos8]
  linarith

theorem negative_lower_positive {y : ℝ} (hy : y∈Icc (0:ℝ) (11/100)) :
    (61/100000000:ℝ)<negativeLower y := by
  have h2 := pow_le_pow_left₀ hy.1 hy.2 2
  have h6 := pow_le_pow_left₀ hy.1 hy.2 6
  have hb : 0≤1067/1000000-(39349/500000)*y^2 := by linarith
  have hm := mul_nonneg (pow_nonneg hy.1 3) hb
  dsimp [negativeLower]
  nlinarith [hy.2]

theorem positive_tail {w : ℝ} (hw : w∈Icc (0:ℝ) (29/50)) :
    (137/2000:ℝ)<7869/100000-(181/12500)*w-
      (4493/1000000)*w^2-(323/20000000)*w^4 := by
  have h2 := pow_le_pow_left₀ hw.1 hw.2 2
  have h4 := pow_le_pow_left₀ hw.1 hw.2 4
  linarith [hw.2]

theorem first_quadratic (t : ℝ) :
    (59/50000000:ℝ)<3/2500000-(113/20000000)*t+(63/100000)*t^2 := by
  nlinarith [sq_nonneg ((63/50000:ℝ)*t-113/20000000)]

theorem second_quadratic (t : ℝ) :
    (27/100000000:ℝ)<111/25000000-(267/250000)*t+(137/2000)*t^2 := by
  nlinarith [sq_nonneg ((137/1000:ℝ)*t-267/250000)]

theorem positive_lower_positive {w : ℝ} (hw : w∈Icc (0:ℝ) (29/50)) :
    (59/50000000:ℝ)<positiveLower w := by
  have ht := mul_le_mul_of_nonneg_left (positive_tail hw).le (pow_nonneg hw.1 5)
  have hq0 := first_quadratic (w^2)
  have hq1 := mul_nonneg hw.1 (by linarith [second_quadratic (w^2)] :
    0≤111/25000000-(267/250000)*(w^2)+(137/2000)*(w^2)^2)
  dsimp [positiveLower]
  nlinarith only [ht,hq0,hq1]

theorem squared_reserve {w : ℝ} (hw : w∈domain) : 0<B w := by
  by_cases hneg : w≤0
  · have hy : -w∈Icc (0:ℝ) (11/100) := ⟨by linarith,by linarith [hw.1]⟩
    have hh := (negative_lower_positive hy).trans (negative_remainder hy.1)
    simp only [neg_neg] at hh
    linarith
  · have hp : w∈Icc (0:ℝ) (29/50) := ⟨le_of_not_ge hneg,hw.2⟩
    have hh := (positive_lower_positive hp).trans (positive_remainder hp.1)
    linarith

theorem U2_positive {w : ℝ} (hw : w∈domain) : (49/100:ℝ)<U2 w := by
  by_cases hneg : w≤0
  · have hy : -w∈Icc (0:ℝ) (11/100) := ⟨by linarith,by linarith [hw.1]⟩
    have h2 := pow_le_pow_left₀ hy.1 hy.2 2
    have h3 := pow_nonneg hy.1 3
    have h4 := pow_nonneg hy.1 4
    dsimp [U2]
    nlinarith
  · have hp : 0≤w := le_of_not_ge hneg
    have h2 := pow_le_pow_left₀ hp hw.2 2
    have hb : 0≤11993/12500-(6409/31250)*w-(3817/62500)*w^2 := by
      linarith [hw.2]
    have hm := mul_nonneg hp hb
    have h4 := pow_nonneg hp 4
    dsimp [U2]
    nlinarith

end SquaresInCircles.Eight.FrameHighLowSecondNormPolynomial
end
end
end
