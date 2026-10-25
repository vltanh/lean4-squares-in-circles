module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2Polynomial
public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveWeights
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# Whole-domain ranges of the negative-DE weight families

Uncompiled transcription of Section 4.  The high l/c lower bounds keep
the single completed cubic at t=24/25.  The low tilted ratio and the two
high ratios are the displayed whole-interval coefficient sums.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD
open Candidate Secondary PositiveAngularEnvelope

namespace Certificate
open Polynomial WholeIntervalPolynomial ChebyshevLeadingBounds
open PositiveTD.Certificate (L h etaQ)

def lowTiltGap : ℚ[X] := C (69/50)*l .low-c .low*(1+C etaQ*X)
def highRatioGap (upper : Bool) : ℚ[X] :=
  if upper then C (1017/1000)*l .high-c .high else c .high-C (9/10)*l .high

/-! ### Kernel certificates

Each polynomial is represented by a scaled integer coefficient list
(`WholeIntervalPolynomial.Certificate`) built to mirror its definition. -/

open WholeIntervalPolynomial.Certificate in
private theorem r75_repC (n : ℤ) (d : ℕ) {q : ℚ} (hd : d≠0) (h : q=n/d) :
    (⟨[n],d⟩ : Scaled).Rep (C q) := by
  unfold Scaled.Rep
  have hd' : (d:ℚ)≠0 := by exact_mod_cast hd
  simp only [toPoly,mul_zero,add_zero,← map_mul]
  congr 1
  rw [h]
  field_simp

/-- A positive integer fraction. -/
private theorem r75_pos_frac {N : ℤ} {D : ℚ} (hD : 0<D) (h : 0<N) : (0:ℚ)<N/D :=
  div_pos (by exact_mod_cast h) hD

/-- A rational number below an integer fraction, from an integer inequality. -/
private theorem r75_lt_frac {r : ℚ} {a N : ℤ} {b : ℕ} {D : ℚ} (hr : r=a/b) (hb : 0<b) (hD : 0<D)
    (hDn : ∃ n : ℕ,(n:ℚ)=D ∧ a*n<N*b) : r<(N:ℚ)/D := by
  obtain ⟨n,hn,h⟩ := hDn
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  rw [hr,div_lt_div_iff₀ hb' hD,← hn]
  exact_mod_cast h

open WholeIntervalPolynomial.Certificate in
private def r75_dS : Scaled := Scaled.var.sub ⟨[1],6⟩

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_d : r75_dS.Rep (X-C L) :=
  Scaled.rep_var.sub (r75_repC 1 6 (by norm_num) (by norm_num))

open WholeIntervalPolynomial.Certificate in
private def r75_tS : Scaled := (⟨[15],8⟩ : Scaled).mul r75_dS

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_t : r75_tS.Rep t :=
  (r75_repC 15 8 (by norm_num) (by norm_num)).mul r75_rep_d

open WholeIntervalPolynomial.Certificate in
private def r75_lLowS : Scaled :=
  ((⟨[10073],10000⟩ : Scaled).sub ((⟨[17],10⟩ : Scaled).mul r75_dS)).add
    ((⟨[11],5⟩ : Scaled).mul (r75_dS.pow 2))

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_lLow : r75_lLowS.Rep (l .low) :=
  ((r75_repC 10073 10000 (by norm_num) (by norm_num)).sub
    ((r75_repC 17 10 (by norm_num) (by norm_num)).mul r75_rep_d)).add
    ((r75_repC 11 5 (by norm_num) (by norm_num)).mul (r75_rep_d.pow 2))

open WholeIntervalPolynomial.Certificate in
private def r75_cLowS : Scaled :=
  ((⟨[10389],10000⟩ : Scaled).sub ((⟨[69],20⟩ : Scaled).mul r75_dS)).add
    ((⟨[9],1⟩ : Scaled).mul (r75_dS.pow 2))

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_cLow : r75_cLowS.Rep (c .low) :=
  ((r75_repC 10389 10000 (by norm_num) (by norm_num)).sub
    ((r75_repC 69 20 (by norm_num) (by norm_num)).mul r75_rep_d)).add
    ((r75_repC 9 1 (by norm_num) (by norm_num)).mul (r75_rep_d.pow 2))

open WholeIntervalPolynomial.Certificate in
private def r75_lHighS : Scaled :=
  (((⟨[1005069],1000000⟩ : Scaled).sub ((⟨[146411],1000000⟩ : Scaled).mul r75_tS)).sub
    ((⟨[157739],1000000⟩ : Scaled).mul (r75_tS.pow 2))).add
    ((⟨[162815],1000000⟩ : Scaled).mul (r75_tS.pow 3))

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_lHigh : r75_lHighS.Rep (l .high) :=
  (((r75_repC 1005069 1000000 (by norm_num) (by norm_num)).sub
    ((r75_repC 146411 1000000 (by norm_num) (by norm_num)).mul r75_rep_t)).sub
    ((r75_repC 157739 1000000 (by norm_num) (by norm_num)).mul (r75_rep_t.pow 2))).add
    ((r75_repC 162815 1000000 (by norm_num) (by norm_num)).mul (r75_rep_t.pow 3))

open WholeIntervalPolynomial.Certificate in
private def r75_cHighS : Scaled :=
  (((⟨[1021248],1000000⟩ : Scaled).sub ((⟨[168873],1000000⟩ : Scaled).mul r75_tS)).sub
    ((⟨[165381],1000000⟩ : Scaled).mul (r75_tS.pow 2))).add
    ((⟨[175944],1000000⟩ : Scaled).mul (r75_tS.pow 3))

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_cHigh : r75_cHighS.Rep (c .high) :=
  (((r75_repC 1021248 1000000 (by norm_num) (by norm_num)).sub
    ((r75_repC 168873 1000000 (by norm_num) (by norm_num)).mul r75_rep_t)).sub
    ((r75_repC 165381 1000000 (by norm_num) (by norm_num)).mul (r75_rep_t.pow 2))).add
    ((r75_repC 175944 1000000 (by norm_num) (by norm_num)).mul (r75_rep_t.pow 3))

open WholeIntervalPolynomial.Certificate in
private def r75_tiltS : Scaled :=
  ((⟨[69],50⟩ : Scaled).mul r75_lLowS).sub
    (r75_cLowS.mul ((Scaled.ofNat 1).add ((⟨[293],1000⟩ : Scaled).mul Scaled.var)))

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_tilt :
    (r75_tiltS.center 1 12 1 1).Rep (centered 0 L lowTiltGap) :=
  (((r75_repC 69 50 (by norm_num) (by norm_num)).mul r75_rep_lLow).sub
    (r75_rep_cLow.mul (Scaled.rep_one.add ((r75_repC 293 1000 (by norm_num) (by norm_num)).mul
      Scaled.rep_var)))).centered 1 12 1 1 (by norm_num) (by norm_num) (by norm_num)

open WholeIntervalPolynomial.Certificate in
private def r75_ratioS : Bool→Scaled
  | true => ((⟨[1017],1000⟩ : Scaled).mul r75_lHighS).sub r75_cHighS
  | false => r75_cHighS.sub ((⟨[9],10⟩ : Scaled).mul r75_lHighS)

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_ratio (upper : Bool) :
    ((r75_ratioS upper).center 1 30 13 8).Rep (centered L h (highRatioGap upper)) := by
  cases upper
  · exact (r75_rep_cHigh.sub ((r75_repC 9 10 (by norm_num) (by norm_num)).mul
      r75_rep_lHigh)).centered 1 30 13 8 (by norm_num) (by norm_num) (by norm_num)
  · exact (((r75_repC 1017 1000 (by norm_num) (by norm_num)).mul r75_rep_lHigh).sub
      r75_rep_cHigh).centered 1 30 13 8 (by norm_num) (by norm_num) (by norm_num)

theorem low_tilt_certificate :
    centered 0 L lowTiltGap=expansion 3 (centered 0 L lowTiltGap) ∧
    lowerOn 3 0 L lowTiltGap=(11909/16000000:ℚ) := by
  open WholeIntervalPolynomial.Certificate in
  have hall : (r75_tiltS.center 1 12 1 1).s≠0 ∧ (r75_tiltS.center 1 12 1 1).l.length≤3+1 ∧
      lowerZ 3 (fun j => (chebList (r75_tiltS.center 1 12 1 1).l).getD j 0)*16000000*2=
        11909*((r75_tiltS.center 1 12 1 1).s*2^(r75_tiltS.center 1 12 1 1).l.length) := by
    decide +kernel
  refine ⟨r75_rep_tilt.eq_expansion hall.1 hall.2.1,?_⟩
  rw [WholeIntervalPolynomial.Certificate.lowerOn_eq_of_rep r75_rep_tilt hall.1 hall.2.1]
  have hs : ((r75_tiltS.center 1 12 1 1).s:ℚ)≠0 := by exact_mod_cast hall.1
  rw [div_eq_div_iff (by positivity) (by norm_num)]
  have h := congrArg (fun z : ℤ => (z:ℚ)) hall.2.2
  push_cast at h
  linarith

theorem high_ratio_certificate (upper : Bool) :
    centered L h (highRatioGap upper)=expansion 3 (centered L h (highRatioGap upper)) ∧
    (if upper then 2596/10000000 else 0)<lowerOn 3 L h (highRatioGap upper) := by
  open WholeIntervalPolynomial.Certificate in
  have hall : ∀ u : Bool,((r75_ratioS u).center 1 30 13 8).s≠0 ∧
      ((r75_ratioS u).center 1 30 13 8).l.length≤3+1 ∧
      (if u then 2596 else 0)*((((r75_ratioS u).center 1 30 13 8).s:ℤ)*
        2^((r75_ratioS u).center 1 30 13 8).l.length)<
        lowerZ 3 (fun j => (chebList ((r75_ratioS u).center 1 30 13 8).l).getD j 0)*10000000*2 := by
    decide +kernel
  refine ⟨(r75_rep_ratio upper).eq_expansion (hall upper).1 (hall upper).2.1,?_⟩
  rw [WholeIntervalPolynomial.Certificate.lowerOn_eq_of_rep (r75_rep_ratio upper) (hall upper).1
    (hall upper).2.1,lt_div_iff₀ (WholeIntervalPolynomial.Certificate.scale_pos (hall upper).1)]
  have h' := (Int.cast_lt (R:=ℚ)).mpr (hall upper).2.2
  cases upper <;> simp only [Bool.false_eq_true,↓reduceIte] at h' ⊢ <;> push_cast at h' <;>
    linarith

def highLC (atC : Bool) : ℚ[X] :=
  if atC then C (1021248/1000000)-C (168873/1000000)*X-
    C (165381/1000000)*X^2+C (175944/1000000)*X^3
  else C (1005069/1000000)-C (146411/1000000)*X-
    C (157739/1000000)*X^2+C (162815/1000000)*X^3
def highLCReverse (atC : Bool) : ℚ[X] := (highLC atC).comp (C (24/25)-X)
def highLCCoeff (atC : Bool) (j : ℕ) : ℚ := (highLCReverse atC).coeff j
def highLCQuadratic (atC : Bool) : ℚ := highLCCoeff atC 2+(24/25)*highLCCoeff atC 3
def highLCLower : Bool → ℚ | false => 863/1000 | true => 862/1000

open WholeIntervalPolynomial.Certificate in
private def r75_lcS : Bool→Scaled
  | true => ((((⟨[1021248],1000000⟩ : Scaled).sub ((⟨[168873],1000000⟩ : Scaled).mul
      Scaled.var)).sub ((⟨[165381],1000000⟩ : Scaled).mul (Scaled.var.pow 2))).add
      ((⟨[175944],1000000⟩ : Scaled).mul (Scaled.var.pow 3))).center 1 25 24 (-25)
  | false => ((((⟨[1005069],1000000⟩ : Scaled).sub ((⟨[146411],1000000⟩ : Scaled).mul
      Scaled.var)).sub ((⟨[157739],1000000⟩ : Scaled).mul (Scaled.var.pow 2))).add
      ((⟨[162815],1000000⟩ : Scaled).mul (Scaled.var.pow 3))).center 1 25 24 (-25)

private theorem r75_reverse_eq (p : ℚ[X]) :
    p.comp (C (24/25)-X)=centered (49/25) (-1/25) p := by
  rw [centered,affine]
  congr 1
  rw [show ((49/25:ℚ)+-1/25)/2=24/25 by norm_num,show ((-1/25:ℚ)-49/25)/2=-1 by norm_num,
    map_neg,map_one]
  ring

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_lc (atC : Bool) : (r75_lcS atC).Rep (highLCReverse atC) := by
  rw [highLCReverse,r75_reverse_eq]
  cases atC
  · exact ((((r75_repC 1005069 1000000 (by norm_num) (by norm_num)).sub
      ((r75_repC 146411 1000000 (by norm_num) (by norm_num)).mul Scaled.rep_var)).sub
      ((r75_repC 157739 1000000 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 2))).add
      ((r75_repC 162815 1000000 (by norm_num) (by norm_num)).mul
        (Scaled.rep_var.pow 3))).centered 1 25 24 (-25) (by norm_num) (by norm_num) (by norm_num)
  · exact ((((r75_repC 1021248 1000000 (by norm_num) (by norm_num)).sub
      ((r75_repC 168873 1000000 (by norm_num) (by norm_num)).mul Scaled.rep_var)).sub
      ((r75_repC 165381 1000000 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 2))).add
      ((r75_repC 175944 1000000 (by norm_num) (by norm_num)).mul
        (Scaled.rep_var.pow 3))).centered 1 25 24 (-25) (by norm_num) (by norm_num) (by norm_num)

open WholeIntervalPolynomial.Certificate in
private theorem r75_coeff_val {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) (j : ℕ)
    {q : ℚ} (n : ℤ) (d : ℕ) (hq : q=n/d) (hd : d≠0) (h : c.l.getD j 0*d=n*c.s) :
    p.coeff j=q := by
  rw [hc.coeff hs j,hq,div_eq_div_iff (by exact_mod_cast hs) (by exact_mod_cast hd)]
  exact_mod_cast h

theorem high_lc_identity (atC : Bool) : highLCReverse atC=
    C (highLCCoeff atC 0)+C (highLCCoeff atC 1)*X+
      C (highLCCoeff atC 2)*X^2+C (highLCCoeff atC 3)*X^3 := by
  have hs : (r75_lcS atC).s≠0 := by cases atC <;> decide +kernel
  have h := (highLCReverse atC).as_sum_range_C_mul_X_pow' (n:=4)
    (lt_of_le_of_lt ((r75_rep_lc atC).natDegree_le hs) (by cases atC <;> decide +kernel))
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,
    pow_one] at h
  exact h

theorem high_lc_certificate (atC : Bool) :
    highLCCoeff atC 3<0 ∧ 0<highLCQuadratic atC ∧
    highLCLower atC<highLCCoeff atC 0-
      (highLCCoeff atC 1)^2/(4*highLCQuadratic atC) := by
  cases atC
  · have hs : (r75_lcS false).s≠0 := by decide +kernel
    have h0 := r75_coeff_val (r75_rep_lc false) hs 0 (q:=2697470217/3125000000) 2697470217 3125000000 (by norm_num)
      (by norm_num) (by decide +kernel)
    have h1 := r75_coeff_val (r75_rep_lc false) hs 1 (q:=(-110129)/125000000) (-110129) 125000000 (by norm_num)
      (by norm_num) (by decide +kernel)
    have h2 := r75_coeff_val (r75_rep_lc false) hs 2 (q:=1555841/5000000) 1555841 5000000 (by norm_num)
      (by norm_num) (by decide +kernel)
    have h3 := r75_coeff_val (r75_rep_lc false) hs 3 (q:=(-32563)/200000) (-32563) 200000 (by norm_num)
      (by norm_num) (by decide +kernel)
    simp only [highLCQuadratic,highLCCoeff,highLCLower,h0,h1,h2,h3]
    norm_num
  · have hs : (r75_lcS true).s≠0 := by decide +kernel
    have h0 := r75_coeff_val (r75_rep_lc true) hs 0 (q:=1684333557/1953125000) 1684333557 1953125000 (by norm_num)
      (by norm_num) (by decide +kernel)
    have h1 := r75_coeff_val (r75_rep_lc true) hs 1 (q:=(-28407)/625000000) (-28407) 625000000 (by norm_num)
      (by norm_num) (by decide +kernel)
    have h2 := r75_coeff_val (r75_rep_lc true) hs 2 (q:=8533443/25000000) 8533443 25000000 (by norm_num)
      (by norm_num) (by decide +kernel)
    have h3 := r75_coeff_val (r75_rep_lc true) hs 3 (q:=(-21993)/125000) (-21993) 125000 (by norm_num)
      (by norm_num) (by decide +kernel)
    simp only [highLCQuadratic,highLCCoeff,highLCLower,h0,h1,h2,h3]
    norm_num

theorem high_lc_lower (atC : Bool) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    (highLCLower atC:ℝ)<aeval u (highLC atC) := by
  obtain ⟨w,hw_def⟩ : ∃ w : ℝ,w=24/25-u := ⟨_,rfl⟩
  have hw : w≤24/25 := by rw [hw_def]; linarith [hu.1]
  have hcube : w^3≤(24/25)*w^2 := by nlinarith [mul_nonneg (sq_nonneg w) (sub_nonneg.mpr hw)]
  have hc : (highLCCoeff atC 3:ℝ)<0 := by exact_mod_cast (high_lc_certificate atC).1
  have hq : (0:ℝ)<(highLCQuadratic atC:ℝ) := by exact_mod_cast (high_lc_certificate atC).2.1
  have hcub := mul_le_mul_of_nonpos_left hcube hc.le
  have hmin := quadratic_min (a:=(highLCCoeff atC 0:ℝ))
    (b:=(highLCCoeff atC 1:ℝ)) (x:=w) hq
  have hr : (highLCLower atC:ℝ)<(highLCCoeff atC 0:ℝ)-
      (highLCCoeff atC 1:ℝ)^2/(4*(highLCQuadratic atC:ℝ)) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr (high_lc_certificate atC).2.2
    push_cast at hh
    exact hh
  have he := congrArg (fun p : ℚ[X] => aeval w p) (high_lc_identity atC)
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at he
  have hv : aeval w (highLCReverse atC)=aeval u (highLC atC) := by
    rw [highLCReverse,aeval_comp]
    simp only [map_sub,aeval_C,aeval_X,eq_ratCast,hw_def]
    push_cast
    ring_nf
  rw [hv] at he
  simp only [highLCQuadratic] at hmin hr
  push_cast at hmin hr
  linarith

end Certificate

namespace Explicit

theorem low_ranges {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    (2/3:ℝ)<k .low θ ∧ k .low θ<757/1000 ∧
      1<l .low θ ∧ l .low θ<1352/1000 ∧
      (10389/10000:ℝ)≤c .low θ ∧ c .low θ<1864/1000 ∧
      l .low θ≤c .low θ ∧ l .low θ<2*k .low θ := by
  let x : ℝ := 1/6-θ
  have hx : x∈Icc (0:ℝ) (1/6) := ⟨by dsimp [x]; linarith [hθ.2],by dsimp [x]; linarith [hθ.1]⟩
  have hx2 : x^2≤x/6 := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hk : k .low θ=6708/10000-(3/20)*x+4*x^2 := by dsimp [k,L,x]; ring
  have hl : l .low θ=10073/10000+(17/10)*x+(11/5)*x^2 := by dsimp [l,L,x]; ring
  have hc : c .low θ=10389/10000+(69/20)*x+9*x^2 := by dsimp [c,L,x]; ring
  have hratio : 2*k .low θ-l .low θ=72935/450000+θ/15+(29/5)*θ^2 := by
    dsimp [k,l,L]
    ring
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · nlinarith [sq_nonneg (x-3/160)]
  · nlinarith [hx.1,hx.2]
  · nlinarith [hx.1,sq_nonneg x]
  · nlinarith [hx.1,hx.2]
  · nlinarith [hx.1,sq_nonneg x]
  · nlinarith [hx.1,hx.2]
  · nlinarith [hx.1,sq_nonneg x]
  · nlinarith [hθ.1,sq_nonneg θ]

theorem high_parameter {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) : t θ∈Icc (0:ℝ) 1 := by
  dsimp [t,L]
  exact ⟨by linarith [hθ.1],by linarith [hθ.2]⟩

theorem high_ranges {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    (670158/1000000:ℝ)≤k .high θ ∧ k .high θ≤800408/1000000 ∧
      (863/1000:ℝ)<l .high θ ∧ l .high θ≤1005069/1000000 ∧
      (862/1000:ℝ)<c .high θ ∧ c .high θ≤1021248/1000000 ∧
      l .high θ<(3/2)*k .high θ ∧ c .high θ≤1073/1000-(3/10)*θ := by
  have ht := high_parameter hθ
  have hpow (n : ℕ) : 0≤(t θ)^n ∧ (t θ)^n≤1 :=
    ⟨pow_nonneg ht.1 n,by simpa using pow_le_pow_left₀ ht.1 ht.2 n⟩
  have h2 : (t θ)^2≤t θ := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have h3 : (t θ)^3≤(t θ)^2 := by nlinarith [mul_nonneg (sq_nonneg (t θ)) (sub_nonneg.mpr ht.2)]
  have hl := Certificate.high_lc_lower false ht
  have hc := Certificate.high_lc_lower true ht
  simp only [Certificate.highLCLower,Certificate.highLC,Bool.false_eq_true,↓reduceIte,map_add,
    map_sub,map_mul,map_pow,Polynomial.aeval_C,Polynomial.aeval_X,eq_ratCast] at hl hc
  push_cast at hl hc
  have hratio : (3/2)*k .high θ-l .high θ=
      168/1000000+(316988/1000000)*t θ+(167498/1000000)*(t θ)^2-
        (149276/1000000)*(t θ)^3+(15/10000)*(t θ)^4 := by dsimp [k,l]; ring
  have hcorrelation : 1073/1000-(3/10)*θ-c .high θ=
      (1752/1000000)*(1-t θ)+(62/1000000)*t θ+
        t θ*(1-t θ)*(10563/1000000+(175944/1000000)*t θ) := by
    dsimp [c,t,L]
    ring
  have hlast := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
    (show 0≤10563/1000000+(175944/1000000)*t θ by linarith [ht.1])
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [k]; nlinarith [(hpow 1).1,(hpow 2).1,(hpow 3).1,(hpow 4).1]
  · dsimp [k]; nlinarith [(hpow 1).2,(hpow 2).2,(hpow 3).2,(hpow 4).2]
  · dsimp [l]; linarith
  · dsimp [l]; nlinarith [ht.1]
  · dsimp [c]; linarith
  · dsimp [c]; nlinarith [ht.1]
  · nlinarith [ht.1,(hpow 2).1,(hpow 4).1]
  · nlinarith [ht.1,ht.2]

theorem low_tilted {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) :
    c .low θ≤ m .low θ z ∧ m .low θ z<(69/50)*l .low θ := by
  have hr := low_ranges hθ
  have hc : 0<c .low θ := by linarith [hr.2.2.2.2.1]
  have hz' : z∈Icc 0 PositiveTD.Explicit.split := ⟨hz.1,hz.2.trans hθ.2⟩
  have hf := PositiveTD.Explicit.low_factor hz'
  have hlow := mul_le_mul_of_nonneg_left hf.1 hc.le
  have hupper := mul_le_mul_of_nonneg_left
    (show Real.cos z+eta*Real.sin z≤1+eta*θ by
      have he : PositiveTD.eta=eta := rfl
      rw [he] at hf
      dsimp [eta] at *
      linarith [hz.2,hf.2]) hc.le
  have hcert := (WholeIntervalPolynomial.interval_bounds
    (by norm_num [PositiveTD.Certificate.L] : (0:ℚ)<PositiveTD.Certificate.L)
    Certificate.low_tilt_certificate.1
    (show θ∈Icc ((0:ℚ):ℝ) ((PositiveTD.Certificate.L:ℚ):ℝ) by
      norm_num [PositiveTD.Certificate.L]; exact hθ)).1
  rw [Certificate.low_tilt_certificate.2] at hcert
  simp only [Certificate.lowTiltGap,map_sub,map_mul,map_add,map_one,Polynomial.aeval_C,
    Polynomial.aeval_X,eq_ratCast,Certificate.l_eval,Certificate.c_eval] at hcert
  push_cast [PositiveTD.Certificate.etaQ] at hcert
  refine ⟨by simpa [m,eta,PositiveTD.eta] using hlow,?_⟩
  dsimp [m,eta]
  dsimp [eta] at hupper
  nlinarith

theorem high_ratios {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    (9/10)*l .high θ<c .high θ ∧ c .high θ<(1017/1000)*l .high θ := by
  have hfalse := Certificate.high_ratio_certificate false
  have htrue := Certificate.high_ratio_certificate true
  have hθ' : θ∈Icc ((PositiveTD.Certificate.L:ℚ):ℝ) ((PositiveTD.Certificate.h:ℚ):ℝ) := by
    norm_num [PositiveTD.Certificate.L,PositiveTD.Certificate.h]; exact hθ
  have hL := WholeIntervalPolynomial.positive_on_interval
    (by norm_num [PositiveTD.Certificate.L,PositiveTD.Certificate.h] :
      PositiveTD.Certificate.L<PositiveTD.Certificate.h) hfalse.1 hfalse.2 hθ'
  have hU := WholeIntervalPolynomial.positive_on_interval
    (by norm_num [PositiveTD.Certificate.L,PositiveTD.Certificate.h] :
      PositiveTD.Certificate.L<PositiveTD.Certificate.h) htrue.1 htrue.2 hθ'
  simp only [Certificate.highRatioGap,Bool.false_eq_true,↓reduceIte,map_sub,map_mul,
    Polynomial.aeval_C,eq_ratCast,Certificate.l_eval,Certificate.c_eval] at hL hU
  push_cast at hL hU
  exact ⟨by linarith,by linarith⟩

theorem high_tilted {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) :
    k .high θ< m .high θ z ∧ m .high θ z<(1061/1000)*l .high θ ∧
      m .high θ z<(1066/1000:ℝ) ∧ (2/3)*l .high θ< m .high θ z := by
  have hr := high_ranges hθ
  have hrat := high_ratios hθ
  have hc : 0<c .high θ := by linarith [hr.2.2.2.2.1]
  have hl : 0<l .high θ := by linarith [hr.2.2.1]
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by norm_num [frameCap]; linarith [hz.2,hθ.2]⟩
  have hlow₀ := mul_lt_mul_of_pos_left (PositiveTD.Explicit.factor_lower hz') hc
  have hupper := mul_lt_mul_of_pos_left (PositiveTD.Explicit.factor_upper z) hc
  have hlow : (19/20)*c .high θ< m .high θ z := by
    simpa [m,eta,PositiveTD.eta,mul_comm] using hlow₀
  change m .high θ z<c .high θ*(1043/1000) at hupper
  refine ⟨?_,?_,?_,?_⟩ <;>
    nlinarith [hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,
      hr.2.2.2.2.2.1,hrat.1,hrat.2]

theorem family_positive (f : Family) {θ z : ℝ}
    (hθ : θ∈Icc (left f) (right f)) (hz : z∈Icc 0 θ) :
    0<k f θ ∧ 0<l f θ ∧ 0<c f θ ∧ 0< m f θ z := by
  cases f
  · have hr := low_ranges hθ
    have hm := low_tilted hθ hz
    exact ⟨by linarith [hr.1],by linarith [hr.2.2.1],
      by linarith [hr.2.2.2.2.1],by linarith [hr.2.2.2.2.1,hm.1]⟩
  · have hr := high_ranges hθ
    have hm := high_tilted hθ hz
    exact ⟨by linarith [hr.1],by linarith [hr.2.2.1],
      by linarith [hr.2.2.2.2.1],by linarith [hr.1,hm.1]⟩

theorem high_pairs {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (i : Fin 3) : 0<p .high θ z i ∧ p .high θ z i≤q .high θ z i ∧
      (2/3)*q .high θ z i<p .high θ z i ∧
      (863/1000:ℝ)<q .high θ z i ∧ q .high θ z i<(1066/1000:ℝ) := by
  have hr := high_ranges hθ
  have hm := high_tilted hθ hz
  have hk : 0<k .high θ := by linarith [hr.1]
  have hl : 0<l .high θ := by linarith [hr.2.2.1]
  have hm0 : 0< m .high θ z := hk.trans hm.1
  have hkl : k .high θ<l .high θ := by linarith [hr.2.1,hr.2.2.1]
  fin_cases i
  · show 0<k .high θ ∧ k .high θ≤1 ∧ (2/3)*1<k .high θ ∧ (863/1000:ℝ)<1 ∧ (1:ℝ)<1066/1000
    exact ⟨hk,by linarith [hr.2.1],by linarith [hr.1],by norm_num,by norm_num⟩
  · show 0<k .high θ ∧ k .high θ≤l .high θ ∧ (2/3)*l .high θ<k .high θ ∧
      (863/1000:ℝ)<l .high θ ∧ l .high θ<1066/1000
    exact ⟨hk,hkl.le,by linarith [hr.2.2.2.2.2.2.1],hr.2.2.1,
      by linarith [hr.2.2.2.1]⟩
  · show 0 < min (l .high θ) (m .high θ z) ∧
      min (l .high θ) (m .high θ z) ≤ max (l .high θ) (m .high θ z) ∧
      (2/3)*max (l .high θ) (m .high θ z) < min (l .high θ) (m .high θ z) ∧
      (863/1000:ℝ) < max (l .high θ) (m .high θ z) ∧
      max (l .high θ) (m .high θ z) < 1066/1000
    refine ⟨lt_min hl hm0,min_le_max,?_,?_,?_⟩
    · rcases le_total (l .high θ) (m .high θ z) with hh | hh
      · rw [min_eq_left hh,max_eq_right hh]
        nlinarith [hm.2.1]
      · rw [min_eq_right hh,max_eq_left hh]
        exact hm.2.2.2
    · exact hr.2.2.1.trans_le (le_max_left _ _)
    · exact max_lt (by linarith [hr.2.2.2.1]) hm.2.2.1

theorem high_q_ratio {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (i j : Fin 3) : q .high θ z i<(29/25)*q .high θ z j := by
  have hi := high_pairs hθ hz i
  have hj := high_pairs hθ hz j
  have hr := high_ranges hθ
  have hm := high_tilted hθ hz
  have hq (n : Fin 3) : q .high θ z n=1 ∨ q .high θ z n=l .high θ ∨
      q .high θ z n=max (l .high θ) (m .high θ z) := by
    fin_cases n
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  by_cases hl : 1≤l .high θ
  · have hj1 : 1≤q .high θ z j := by
      rcases hq j with h|h|h <;> rw [h]
      · exact hl
      · exact hl.trans (le_max_left _ _)
    nlinarith [hi.2.2.2.2]
  · by_cases hm1 : m .high θ z≤1
    · have hi1 : q .high θ z i≤1 := by
        rcases hq i with h|h|h <;> rw [h]
        · exact (lt_of_not_ge hl).le
        · exact max_le (lt_of_not_ge hl).le hm1
      nlinarith [hj.2.2.2.1]
    · have hiM : q .high θ z i≤ m .high θ z := by
        rcases hq i with h|h|h <;> rw [h]
        · exact (lt_of_not_ge hm1).le
        · linarith [lt_of_not_ge hl,lt_of_not_ge hm1]
        · exact max_le (by linarith [lt_of_not_ge hl,lt_of_not_ge hm1]) le_rfl
      have hjL : l .high θ≤q .high θ z j := by
        rcases hq j with h|h|h <;> rw [h]
        · exact (lt_of_not_ge hl).le
        · exact le_max_left _ _
      nlinarith [hm.2.1,hr.2.2.1]

/-- The late interval used by the shared secant-coordinate shape proof.
The cubic upper estimate for l and the affine c/theta correlation are
kept before taking the maximum in the original B pair. -/
theorem high_late_q_le_one {θ z : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (hlate : (11/20:ℝ)≤θ) (i : Fin 3) : q .high θ z i≤1 := by
  have ht := high_parameter hθ
  have htlate : (23/32:ℝ)≤t θ := by dsimp [t,L]; linarith
  have h2 : (t θ)^2≤t θ := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have h3 : (t θ)^3≤(t θ)^2 := by
    nlinarith [mul_nonneg (sq_nonneg (t θ)) (sub_nonneg.mpr ht.2)]
  have hl : l .high θ≤1005069/1000000-(141335/1000000)*t θ := by
    dsimp [l]
    nlinarith
  have hl1 : l .high θ≤1 := by linarith
  have hr := high_ranges hθ
  have hc : c .high θ≤227/250 := by linarith [hr.2.2.2.2.2.2.2]
  have hcpos : 0<c .high θ := by linarith [hr.2.2.2.2.1]
  have hm := mul_lt_mul_of_pos_left (PositiveTD.Explicit.factor_upper z) hcpos
  have hm1 : m .high θ z≤1 := by
    change c .high θ*(Real.cos z+PositiveTD.eta*Real.sin z)<
      c .high θ*(1043/1000) at hm
    dsimp [m,eta,PositiveTD.eta]
    dsimp [PositiveTD.eta] at hm
    nlinarith
  fin_cases i <;> simp only [q,Matrix.cons_val_succ,Matrix.cons_val_zero]
  · exact le_rfl
  · exact hl1
  · exact max_le hl1 hm1

end Explicit
end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD
