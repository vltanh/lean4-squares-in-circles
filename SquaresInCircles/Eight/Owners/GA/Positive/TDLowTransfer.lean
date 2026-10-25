module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Owners.DirectedPowerBounds
public import SquaresInCircles.Eight.Owners.GA.Positive.TDPolynomialData
public import SquaresInCircles.Eight.Owners.GA.Positive.TDScalarBounds
public import SquaresInCircles.Eight.Owners.GA.TD2LowEnvelope

/-!
# Eight squares: the four low TD2 scalar inequalities at the explicit weights

The original trigonometric force norms are bounded
by the exact polynomials, and the four whole-interval reserves are
transferred through positive auxiliary masses.  The D support is its
actual sorted-circle formula throughout this coefficient interval.
-/

section
/-!
## Four whole-interval polynomial reserves on the low TD2 interval

The tight first numerator retains its positive cubic
at the right endpoint; the mixed numerator retains a quadratic at the
midpoint.  The two separated numerators use respectively one centered
coefficient sum and their exact secant quotient.  All rational reductions
are written as kernel proof terms and have not been executed.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.PositiveTD.Certificate
open Polynomial PowerTailBounds

def lowMass : Fin 3→ℚ[X] := ![lowRH,lowRG,lowRB]
def lowMassReserve : Fin 3→ℚ := ![109/100,29/25,71/50]
def lowMassCentered (i : Fin 3) : ℚ[X] := DirectedPowerBounds.shift (1/12) (lowMass i)
def lowReversed : ℚ[X] := DirectedPowerBounds.reverse L lowP
def lowMixedCentered : ℚ[X] := DirectedPowerBounds.shift (1/12) lowPM
def lowSHCentered : ℚ[X] := DirectedPowerBounds.shift (1/12) lowPSH
def lowQuotientCentered : ℚ[X] := DirectedPowerBounds.shift (1/12) lowChordQuotient


/-! ### Kernel certificates

Each polynomial is represented by a scaled integer coefficient list
(`WholeIntervalPolynomial.Certificate`) built to mirror its definition; the
reserves are integer inequalities checked by the kernel. -/

open WholeIntervalPolynomial.Certificate in
private theorem r44_repC (n : ℤ) (d : ℕ) {q : ℚ} (hd : d≠0) (h : q=n/d) :
    (⟨[n],d⟩ : Scaled).Rep (C q) := by
  unfold Scaled.Rep
  have hd' : (d:ℚ)≠0 := by exact_mod_cast hd
  simp only [toPoly,mul_zero,add_zero,← map_mul]
  congr 1
  rw [h]
  field_simp

private theorem r44_ch : ch=3964941898733393/5184000000000000 := by
  norm_num [ch,C10,C4,h]

private theorem r44_Ch : Ch=52337233065258114343/68428800000000000000 := by
  norm_num [Ch,C12,C10,C4,h]

private theorem r44_sh : sh=367358693969535751/570240000000000000 := by
  norm_num [sh,S11,S9,S5,h]

private theorem r44_shift_eq (a : ℚ) (p : ℚ[X]) :
    DirectedPowerBounds.shift a p=WholeIntervalPolynomial.centered (a-1) (a+1) p := by
  rw [DirectedPowerBounds.shift,WholeIntervalPolynomial.centered,WholeIntervalPolynomial.affine,
    show (a-1+(a+1))/2=a by ring,show (a+1-(a-1))/2=1 by ring,map_one,one_mul]

private theorem r44_reverse_eq (a : ℚ) (p : ℚ[X]) :
    DirectedPowerBounds.reverse a p=WholeIntervalPolynomial.centered (a+1) (a-1) p := by
  rw [DirectedPowerBounds.reverse,WholeIntervalPolynomial.centered,
    WholeIntervalPolynomial.affine,show (a+1+(a-1))/2=a by ring,
    show (a-1-(a+1))/2=-1 by ring,map_neg,map_one,neg_one_mul,sub_eq_add_neg]

private theorem r44_eval_eq_coeff (a b : ℚ) (p : ℚ[X]) :
    p.eval ((a+b)/2)=(WholeIntervalPolynomial.centered a b p).coeff 0 := by
  rw [coeff_zero_eq_eval_zero,WholeIntervalPolynomial.centered,eval_comp,
    WholeIntervalPolynomial.affine]
  simp

/-- A polynomial of degree below `k+n` is its first `k` monomials plus its tail. -/
private theorem r44_split {p : ℚ[X]} (k n : ℕ) (hp : p.natDegree<k+n) :
    p=(∑ i ∈ Finset.range k,C (p.coeff i)*X^i)+tail p k n := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' hp]
  rw [Finset.sum_range_add,tail,Fin.sum_univ_eq_sum_range (fun j => C (p.coeff (j+k))*X^(j+k)) n]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [add_comm k j]

private theorem r44_coeff_sub_norm {c : WholeIntervalPolynomial.Certificate.Scaled} {p : ℚ[X]}
    (hc : c.Rep p) (hs : c.s≠0) (j0 k n m : ℕ) (hm : 0 < m) {r : ℚ} (hr : r*m=1) :
    p.coeff j0-PowerTailBounds.norm p k n r=
      ((c.l.getD j0 0*(m:ℤ)^n-∑ j : Fin n,|c.l.getD (j.val+k) 0| *(m:ℤ)^(n-1-j.val) : ℤ):ℚ)/
        ((c.s*m^n:ℕ):ℚ) := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hm' : (0:ℚ) < m := by exact_mod_cast hm
  have hr' : r=1/m := by field_simp; linarith
  unfold PowerTailBounds.norm
  simp only [hc.coeff hs]
  push_cast
  rw [sub_div,Finset.sum_div]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj := j.isLt
    have hpow : (m:ℚ)^n=m^(n-1-j.val)*m^(j.val+1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [abs_div,abs_of_pos hs',hr',hpow,div_pow,one_pow]
    field_simp

private theorem r44_coeff_sub_negnorm {c : WholeIntervalPolynomial.Certificate.Scaled}
    {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) (j0 k n m : ℕ) (hm : 0 < m) {r : ℚ} (hr : r*m=1) :
    p.coeff j0-DirectedPowerBounds.negativeNorm p k n r=
      ((c.l.getD j0 0*(m:ℤ)^n-
        ∑ j : Fin n,max (-c.l.getD (j.val+k) 0) 0*(m:ℤ)^(n-1-j.val) : ℤ):ℚ)/
        ((c.s*m^n:ℕ):ℚ) := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hm' : (0:ℚ) < m := by exact_mod_cast hm
  have hr' : r=1/m := by field_simp; linarith
  unfold DirectedPowerBounds.negativeNorm
  simp only [hc.coeff hs]
  push_cast
  rw [sub_div,Finset.sum_div]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj := j.isLt
    have hpow : (m:ℚ)^n=m^(n-1-j.val)*m^(j.val+1) := by
      rw [← pow_add]
      congr 1
      omega
    have key : max (-(((c.l.getD (j.val+k) 0:ℤ):ℚ)/c.s)) 0=
        max (-((c.l.getD (j.val+k) 0:ℤ):ℚ)) 0/c.s := by
      rw [← max_div_div_right hs'.le,zero_div,neg_div]
    rw [key,hr',hpow,div_pow,one_pow]
    field_simp

/-- A rational number below an integer fraction, from an integer inequality. -/
private theorem r44_lt_frac {r : ℚ} {a N : ℤ} {b D : ℕ} (hr : r=a/b) (hb : 0<b) (hD : 0<D)
    (h : a*D<N*b) : r<(N:ℚ)/(D:ℚ) := by
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  have hD' : (0:ℚ)<D := by exact_mod_cast hD
  rw [hr,div_lt_div_iff₀ hb' hD']
  exact_mod_cast h

open WholeIntervalPolynomial.Certificate in
private def r44_S5S : Scaled :=
  (Scaled.var.sub ((⟨[1],6⟩ : Scaled).mul (Scaled.var.pow 3))).add ((⟨[1],120⟩ : Scaled).mul
    (Scaled.var.pow 5))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_S5 : r44_S5S.Rep S5 :=
  (Scaled.rep_var.sub ((r44_repC 1 6 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow
    3))).add ((r44_repC 1 120 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 5))

open WholeIntervalPolynomial.Certificate in
private def r44_S9S : Scaled :=
  (r44_S5S.sub ((⟨[1],5040⟩ : Scaled).mul (Scaled.var.pow 7))).add ((⟨[1],362880⟩ : Scaled).mul
    (Scaled.var.pow 9))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_S9 : r44_S9S.Rep S9 :=
  (r44_rep_S5.sub ((r44_repC 1 5040 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow
    7))).add ((r44_repC 1 362880 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 9))

open WholeIntervalPolynomial.Certificate in
private def r44_S11S : Scaled :=
  r44_S9S.sub ((⟨[1],39916800⟩ : Scaled).mul (Scaled.var.pow 11))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_S11 : r44_S11S.Rep S11 :=
  r44_rep_S9.sub ((r44_repC 1 39916800 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 11))

open WholeIntervalPolynomial.Certificate in
private def r44_C4S : Scaled :=
  ((Scaled.ofNat 1).sub ((⟨[1],2⟩ : Scaled).mul (Scaled.var.pow 2))).add ((⟨[1],24⟩ :
    Scaled).mul (Scaled.var.pow 4))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_C4 : r44_C4S.Rep C4 :=
  (Scaled.rep_one.sub ((r44_repC 1 2 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow
    2))).add ((r44_repC 1 24 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 4))

open WholeIntervalPolynomial.Certificate in
private def r44_C10S : Scaled :=
  ((r44_C4S.sub ((⟨[1],720⟩ : Scaled).mul (Scaled.var.pow 6))).add ((⟨[1],40320⟩ : Scaled).mul
    (Scaled.var.pow 8))).sub ((⟨[1],3628800⟩ : Scaled).mul (Scaled.var.pow 10))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_C10 : r44_C10S.Rep C10 :=
  ((r44_rep_C4.sub ((r44_repC 1 720 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow
    6))).add ((r44_repC 1 40320 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 8))).sub
    ((r44_repC 1 3628800 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 10))

open WholeIntervalPolynomial.Certificate in
private def r44_C12S : Scaled :=
  r44_C10S.add ((⟨[1],479001600⟩ : Scaled).mul (Scaled.var.pow 12))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_C12 : r44_C12S.Rep C12 :=
  r44_rep_C10.add ((r44_repC 1 479001600 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow
    12))

open WholeIntervalPolynomial.Certificate in
private def r44_lKS : Scaled :=
  ((⟨[84],125⟩ : Scaled).sub ((⟨[1],5⟩ : Scaled).mul (Scaled.var.sub (⟨[83],500⟩ :
    Scaled)))).add ((⟨[5],2⟩ : Scaled).mul ((Scaled.var.sub (⟨[83],500⟩ : Scaled)).pow 2))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_lK : r44_lKS.Rep lowK :=
  ((r44_repC 84 125 (by norm_num) (by norm_num)).sub ((r44_repC 1 5 (by norm_num) (by
    norm_num)).mul (Scaled.rep_var.sub (r44_repC 83 500 (by norm_num) (by norm_num))))).add
    ((r44_repC 5 2 (by norm_num) (by norm_num)).mul ((Scaled.rep_var.sub (r44_repC 83 500 (by
    norm_num) (by norm_num))).pow 2))

open WholeIntervalPolynomial.Certificate in
private def r44_lLS : Scaled :=
  (((⟨[101],100⟩ : Scaled).sub ((⟨[5],2⟩ : Scaled).mul (Scaled.var.sub (⟨[83],500⟩ :
    Scaled)))).add ((⟨[6],1⟩ : Scaled).mul ((Scaled.var.sub (⟨[83],500⟩ : Scaled)).pow 2))).add
    ((⟨[48],1⟩ : Scaled).mul ((Scaled.var.sub (⟨[83],500⟩ : Scaled)).pow 3))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_lL : r44_lLS.Rep lowL :=
  (((r44_repC 101 100 (by norm_num) (by norm_num)).sub ((r44_repC 5 2 (by norm_num) (by
    norm_num)).mul (Scaled.rep_var.sub (r44_repC 83 500 (by norm_num) (by norm_num))))).add
    ((r44_repC 6 1 (by norm_num) (by norm_num)).mul ((Scaled.rep_var.sub (r44_repC 83 500 (by
    norm_num) (by norm_num))).pow 2))).add ((r44_repC 48 1 (by norm_num) (by norm_num)).mul
    ((Scaled.rep_var.sub (r44_repC 83 500 (by norm_num) (by norm_num))).pow 3))

open WholeIntervalPolynomial.Certificate in
private def r44_lCS : Scaled :=
  ((⟨[1043],1000⟩ : Scaled).sub ((⟨[21],5⟩ : Scaled).mul (Scaled.var.sub (⟨[83],500⟩ :
    Scaled)))).add ((⟨[8],1⟩ : Scaled).mul ((Scaled.var.sub (⟨[83],500⟩ : Scaled)).pow 2))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_lC : r44_lCS.Rep lowC :=
  ((r44_repC 1043 1000 (by norm_num) (by norm_num)).sub ((r44_repC 21 5 (by norm_num) (by
    norm_num)).mul (Scaled.rep_var.sub (r44_repC 83 500 (by norm_num) (by norm_num))))).add
    ((r44_repC 8 1 (by norm_num) (by norm_num)).mul ((Scaled.rep_var.sub (r44_repC 83 500 (by
    norm_num) (by norm_num))).pow 2))

open WholeIntervalPolynomial.Certificate in
private def r44_mMS : Scaled :=
  r44_lCS.mul (r44_C10S.add ((⟨[293],1000⟩ : Scaled).mul r44_S11S))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_mM : r44_mMS.Rep (mMinus lowC) :=
  r44_rep_lC.mul (r44_rep_C10.add ((r44_repC 293 1000 (by norm_num) (by norm_num [etaQ])).mul
    r44_rep_S11))

open WholeIntervalPolynomial.Certificate in
private def r44_mPS : Scaled :=
  r44_lCS.mul (r44_C12S.add ((⟨[293],1000⟩ : Scaled).mul r44_S9S))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_mP : r44_mPS.Rep (mPlus lowC) :=
  r44_rep_lC.mul (r44_rep_C12.add ((r44_repC 293 1000 (by norm_num) (by norm_num [etaQ])).mul
    r44_rep_S9))

open WholeIntervalPolynomial.Certificate in
private def r44_AS : Scaled :=
  ((((((((⟨[2],1⟩ : Scaled).mul r44_lKS).add ((⟨[3],1⟩ : Scaled).mul r44_lLS)).add ((⟨[3],2⟩ :
    Scaled).mul r44_mMS)).add (⟨[3],2⟩ : Scaled)).add r44_C10S).add ((r44_lCS.mul (⟨[1],2⟩ :
    Scaled)).mul (((Scaled.ofNat 1).add r44_C10S).add r44_S11S))).sub (((Scaled.ofNat 1).add
    r44_lCS).mul (⟨[899214066],1000000000⟩ : Scaled))).sub ((r44_lCS.mul
    (⟨[1415477291],1000000000⟩ : Scaled)).mul r44_S9S)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_A : r44_AS.Rep lowA :=
  ((((((((r44_repC 2 1 (by norm_num) (by norm_num)).mul r44_rep_lK).add ((r44_repC 3 1 (by
    norm_num) (by norm_num)).mul r44_rep_lL)).add ((r44_repC 3 2 (by norm_num) (by
    norm_num)).mul r44_rep_mM)).add (r44_repC 3 2 (by norm_num) (by norm_num))).add
    r44_rep_C10).add ((r44_rep_lC.mul (r44_repC 1 2 (by norm_num) (by norm_num))).mul
    ((Scaled.rep_one.add r44_rep_C10).add r44_rep_S11))).sub ((Scaled.rep_one.add
    r44_rep_lC).mul (r44_repC 899214066 1000000000 (by norm_num) (by norm_num [cbar])))).sub
    ((r44_rep_lC.mul (r44_repC 1415477291 1000000000 (by norm_num) (by norm_num
    [sigmabar]))).mul r44_rep_S9)

open WholeIntervalPolynomial.Certificate in
private def r44_PHS : Scaled :=
  ((Scaled.ofNat 1).add (r44_lKS.pow 2)).sub (((⟨[2],1⟩ : Scaled).mul r44_lKS).mul r44_S11S)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_PH : r44_PHS.Rep lowPH :=
  (Scaled.rep_one.add (r44_rep_lK.pow 2)).sub (((r44_repC 2 1 (by norm_num) (by norm_num)).mul
    r44_rep_lK).mul r44_rep_S11)

open WholeIntervalPolynomial.Certificate in
private def r44_PGS : Scaled :=
  (r44_lKS.pow 2).add (r44_lLS.pow 2)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_PG : r44_PGS.Rep lowPG :=
  (r44_rep_lK.pow 2).add (r44_rep_lL.pow 2)

open WholeIntervalPolynomial.Certificate in
private def r44_PBS : Scaled :=
  (r44_mPS.pow 2).add (r44_lLS.pow 2)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_PB : r44_PBS.Rep lowPB :=
  (r44_rep_mP.pow 2).add (r44_rep_lL.pow 2)

open WholeIntervalPolynomial.Certificate in
private def r44_RHS : Scaled :=
  ((⟨[89],100⟩ : Scaled).mul ((Scaled.ofNat 1).sub ((⟨[1],2⟩ : Scaled).mul (Scaled.var.pow
    2)))).add ((⟨[57],125⟩ : Scaled).mul ((r44_lKS.sub Scaled.var).add ((⟨[1],6⟩ : Scaled).mul
    (Scaled.var.pow 3))))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_RH : r44_RHS.Rep lowRH :=
  ((r44_repC 89 100 (by norm_num) (by norm_num)).mul (Scaled.rep_one.sub ((r44_repC 1 2 (by
    norm_num) (by norm_num)).mul (Scaled.rep_var.pow 2)))).add ((r44_repC 57 125 (by norm_num)
    (by norm_num)).mul ((r44_rep_lK.sub Scaled.rep_var).add ((r44_repC 1 6 (by norm_num) (by
    norm_num)).mul (Scaled.rep_var.pow 3))))

open WholeIntervalPolynomial.Certificate in
private def r44_RGS : Scaled :=
  ((⟨[11],20⟩ : Scaled).mul r44_lKS).add ((⟨[167],200⟩ : Scaled).mul r44_lLS)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_RG : r44_RGS.Rep lowRG :=
  ((r44_repC 11 20 (by norm_num) (by norm_num)).mul r44_rep_lK).add ((r44_repC 167 200 (by
    norm_num) (by norm_num)).mul r44_rep_lL)

open WholeIntervalPolynomial.Certificate in
private def r44_RBS : Scaled :=
  (((⟨[729],1000⟩ : Scaled).mul r44_lCS).mul (((Scaled.ofNat 1).add ((⟨[293],1000⟩ : Scaled).mul
    Scaled.var)).sub ((⟨[1],2⟩ : Scaled).mul (Scaled.var.pow 2)))).add ((⟨[1369],2000⟩ :
    Scaled).mul r44_lLS)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_RB : r44_RBS.Rep lowRB :=
  (((r44_repC 729 1000 (by norm_num) (by norm_num)).mul r44_rep_lC).mul ((Scaled.rep_one.add
    ((r44_repC 293 1000 (by norm_num) (by norm_num [etaQ])).mul Scaled.rep_var)).sub ((r44_repC
    1 2 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 2)))).add ((r44_repC 1369 2000 (by
    norm_num) (by norm_num)).mul r44_rep_lL)

open WholeIntervalPolynomial.Certificate in
private def r44_DenS : Scaled :=
  (((⟨[2],1⟩ : Scaled).mul r44_RHS).mul r44_RGS).mul r44_RBS

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_Den : r44_DenS.Rep lowDen :=
  (((r44_repC 2 1 (by norm_num) (by norm_num)).mul r44_rep_RH).mul r44_rep_RG).mul r44_rep_RB

open WholeIntervalPolynomial.Certificate in
private def r44_PS : Scaled :=
  (((((⟨[2],1⟩ : Scaled).mul r44_AS).mul r44_RHS).mul r44_RGS).mul r44_RBS).sub
    ((⟨[1978787508],1000000000⟩ : Scaled).mul (((((r44_PHS.add (r44_RHS.pow 2)).mul r44_RGS).mul
    r44_RBS).add (((r44_PGS.add (r44_RGS.pow 2)).mul r44_RHS).mul r44_RBS)).add (((r44_PBS.add
    (r44_RBS.pow 2)).mul r44_RHS).mul r44_RGS)))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_P : r44_PS.Rep lowP :=
  (((((r44_repC 2 1 (by norm_num) (by norm_num)).mul r44_rep_A).mul r44_rep_RH).mul
    r44_rep_RG).mul r44_rep_RB).sub ((r44_repC 1978787508 1000000000 (by norm_num) (by norm_num
    [Rbar])).mul (((((r44_rep_PH.add (r44_rep_RH.pow 2)).mul r44_rep_RG).mul r44_rep_RB).add
    (((r44_rep_PG.add (r44_rep_RG.pow 2)).mul r44_rep_RH).mul r44_rep_RB)).add (((r44_rep_PB.add
    (r44_rep_RB.pow 2)).mul r44_rep_RH).mul r44_rep_RG)))

open WholeIntervalPolynomial.Certificate in
private def r44_JS : Scaled :=
  (r44_lKS.mul ((((⟨[803502302830208981],570240000000000000⟩ : Scaled).mul r44_C10S).sub
    ((⟨[8254189788913824223],68428800000000000000⟩ : Scaled).mul r44_S9S)).sub (Scaled.ofNat
    1))).add (r44_lLS.mul ((⟨[3964941898733393],5184000000000000⟩ : Scaled).sub r44_C12S))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_J : r44_JS.Rep lowJ :=
  (r44_rep_lK.mul ((((r44_repC 803502302830208981 570240000000000000 (by norm_num) (by norm_num
    [r44_ch,r44_sh])).mul r44_rep_C10).sub ((r44_repC 8254189788913824223 68428800000000000000
    (by norm_num) (by norm_num [r44_Ch,r44_sh])).mul r44_rep_S9)).sub Scaled.rep_one)).add
    (r44_rep_lL.mul ((r44_repC 3964941898733393 5184000000000000 (by norm_num) (by norm_num
    [r44_ch])).sub r44_rep_C12))

open WholeIntervalPolynomial.Certificate in
private def r44_PMS : Scaled :=
  r44_PS.add (r44_DenS.mul r44_JS)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_PM : r44_PMS.Rep lowPM :=
  r44_rep_P.add (r44_rep_Den.mul r44_rep_J)

open WholeIntervalPolynomial.Certificate in
private def r44_AsS : Scaled :=
  ((((((((⟨[2],1⟩ : Scaled).mul r44_lKS).add ((⟨[3],1⟩ : Scaled).mul r44_lLS)).add ((⟨[3],2⟩ :
    Scaled).mul r44_mMS)).add (⟨[5],2⟩ : Scaled)).add ((r44_lCS.mul (⟨[1],2⟩ : Scaled)).mul
    (((Scaled.ofNat 1).add r44_C10S).add r44_S11S))).sub (((Scaled.ofNat 1).add r44_lCS).mul
    (⟨[899214066],1000000000⟩ : Scaled))).sub ((r44_lCS.mul (⟨[1415477291],1000000000⟩ :
    Scaled)).mul r44_S9S)).sub (((⟨[109],200⟩ : Scaled).mul r44_mPS).mul ((⟨[7],10⟩ :
    Scaled).sub Scaled.var))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_As : r44_AsS.Rep lowAstar :=
  ((((((((r44_repC 2 1 (by norm_num) (by norm_num)).mul r44_rep_lK).add ((r44_repC 3 1 (by
    norm_num) (by norm_num)).mul r44_rep_lL)).add ((r44_repC 3 2 (by norm_num) (by
    norm_num)).mul r44_rep_mM)).add (r44_repC 5 2 (by norm_num) (by norm_num))).add
    ((r44_rep_lC.mul (r44_repC 1 2 (by norm_num) (by norm_num))).mul ((Scaled.rep_one.add
    r44_rep_C10).add r44_rep_S11))).sub ((Scaled.rep_one.add r44_rep_lC).mul (r44_repC 899214066
    1000000000 (by norm_num) (by norm_num [cbar])))).sub ((r44_rep_lC.mul (r44_repC 1415477291
    1000000000 (by norm_num) (by norm_num [sigmabar]))).mul r44_rep_S9)).sub (((r44_repC 109 200
    (by norm_num) (by norm_num)).mul r44_rep_mP).mul ((r44_repC 7 10 (by norm_num) (by norm_num
    [h])).sub Scaled.rep_var))

open WholeIntervalPolynomial.Certificate in
private def r44_PHhS : Scaled :=
  ((Scaled.ofNat 1).add (r44_lKS.pow 2)).sub ((⟨[367358693969535751],285120000000000000⟩ :
    Scaled).mul r44_lKS)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_PHh : r44_PHhS.Rep lowPHh :=
  (Scaled.rep_one.add (r44_rep_lK.pow 2)).sub ((r44_repC 367358693969535751 285120000000000000
    (by norm_num) (by norm_num [r44_sh])).mul r44_rep_lK)

open WholeIntervalPolynomial.Certificate in
private def r44_PSHS : Scaled :=
  (((((⟨[2],1⟩ : Scaled).mul (r44_AsS.add (⟨[-1219058101266607],5184000000000000⟩ :
    Scaled))).mul (⟨[77],100⟩ : Scaled)).mul r44_RGS).mul r44_RBS).sub
    ((⟨[1978787508],1000000000⟩ : Scaled).mul (((((r44_PHhS.add ((⟨[77],100⟩ : Scaled).pow
    2)).mul r44_RGS).mul r44_RBS).add (((r44_PGS.add (r44_RGS.pow 2)).mul (⟨[77],100⟩ :
    Scaled)).mul r44_RBS)).add (((r44_PBS.add (r44_RBS.pow 2)).mul (⟨[77],100⟩ : Scaled)).mul
    r44_RGS)))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_PSH : r44_PSHS.Rep lowPSH :=
  (((((r44_repC 2 1 (by norm_num) (by norm_num)).mul (r44_rep_As.add (r44_repC
    (-1219058101266607) 5184000000000000 (by norm_num) (by norm_num [r44_ch])))).mul (r44_repC
    77 100 (by norm_num) (by norm_num))).mul r44_rep_RG).mul r44_rep_RB).sub ((r44_repC
    1978787508 1000000000 (by norm_num) (by norm_num [Rbar])).mul (((((r44_rep_PHh.add
    ((r44_repC 77 100 (by norm_num) (by norm_num)).pow 2)).mul r44_rep_RG).mul r44_rep_RB).add
    (((r44_rep_PG.add (r44_rep_RG.pow 2)).mul (r44_repC 77 100 (by norm_num) (by norm_num))).mul
    r44_rep_RB)).add (((r44_rep_PB.add (r44_rep_RB.pow 2)).mul (r44_repC 77 100 (by norm_num)
    (by norm_num))).mul r44_rep_RG)))

open WholeIntervalPolynomial.Certificate in
private def r44_PH0S : Scaled :=
  (Scaled.ofNat 1).add (r44_lKS.pow 2)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_PH0 : r44_PH0S.Rep lowPH0 :=
  Scaled.rep_one.add (r44_rep_lK.pow 2)

open WholeIntervalPolynomial.Certificate in
private def r44_PGhS : Scaled :=
  ((r44_lKS.pow 2).add (r44_lLS.pow 2)).sub (((⟨[367358693969535751],285120000000000000⟩ :
    Scaled).mul r44_lKS).mul r44_lLS)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_PGh : r44_PGhS.Rep lowPGh :=
  ((r44_rep_lK.pow 2).add (r44_rep_lL.pow 2)).sub (((r44_repC 367358693969535751
    285120000000000000 (by norm_num) (by norm_num [r44_sh])).mul r44_rep_lK).mul r44_rep_lL)

open WholeIntervalPolynomial.Certificate in
private def r44_RHzS : Scaled :=
  (⟨[41],50⟩ : Scaled).add ((⟨[143],250⟩ : Scaled).mul r44_lKS)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_RHz : r44_RHzS.Rep lowRHzero :=
  (r44_repC 41 50 (by norm_num) (by norm_num)).add ((r44_repC 143 250 (by norm_num) (by
    norm_num)).mul r44_rep_lK)

open WholeIntervalPolynomial.Certificate in
private def r44_RGcS : Scaled :=
  (⟨[153],200⟩ : Scaled).mul r44_lLS

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_RGc : r44_RGcS.Rep lowRGcap :=
  (r44_repC 153 200 (by norm_num) (by norm_num)).mul r44_rep_lL

open WholeIntervalPolynomial.Certificate in
private def r44_PSGS : Scaled :=
  (((((⟨[2],1⟩ : Scaled).mul (r44_AsS.add (r44_lLS.mul (⟨[-1219058101266607],5184000000000000⟩ :
    Scaled)))).mul r44_RHzS).mul r44_RGcS).mul r44_RBS).sub ((⟨[1978787508],1000000000⟩ :
    Scaled).mul (((((r44_PH0S.add (r44_RHzS.pow 2)).mul r44_RGcS).mul r44_RBS).add
    (((r44_PGhS.add (r44_RGcS.pow 2)).mul r44_RHzS).mul r44_RBS)).add (((r44_PBS.add
    (r44_RBS.pow 2)).mul r44_RHzS).mul r44_RGcS)))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_PSG : r44_PSGS.Rep lowPSG :=
  (((((r44_repC 2 1 (by norm_num) (by norm_num)).mul (r44_rep_As.add (r44_rep_lL.mul (r44_repC
    (-1219058101266607) 5184000000000000 (by norm_num) (by norm_num [r44_ch]))))).mul
    r44_rep_RHz).mul r44_rep_RGc).mul r44_rep_RB).sub ((r44_repC 1978787508 1000000000 (by
    norm_num) (by norm_num [Rbar])).mul (((((r44_rep_PH0.add (r44_rep_RHz.pow 2)).mul
    r44_rep_RGc).mul r44_rep_RB).add (((r44_rep_PGh.add (r44_rep_RGc.pow 2)).mul
    r44_rep_RHz).mul r44_rep_RB)).add (((r44_rep_PB.add (r44_rep_RB.pow 2)).mul r44_rep_RHz).mul
    r44_rep_RGc)))

open WholeIntervalPolynomial.Certificate in
private def r44_massS : Fin 3 → Scaled := ![r44_RHS,r44_RGS,r44_RBS]

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_mass (i : Fin 3) :
    ((r44_massS i).center 1 12 1 12).Rep (lowMassCentered i) := by
  rw [lowMassCentered,r44_shift_eq]
  fin_cases i
  · exact r44_rep_RH.centered 1 12 1 12 (by norm_num) (by norm_num) (by norm_num)
  · exact r44_rep_RG.centered 1 12 1 12 (by norm_num) (by norm_num) (by norm_num)
  · exact r44_rep_RB.centered 1 12 1 12 (by norm_num) (by norm_num) (by norm_num)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_rev : (r44_PS.center 1 6 1 (-6)).Rep lowReversed := by
  rw [lowReversed,r44_reverse_eq]
  exact r44_rep_P.centered 1 6 1 (-6) (by norm_num) (by norm_num [L]) (by norm_num [L])

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_mix : (r44_PMS.center 1 12 1 12).Rep lowMixedCentered := by
  rw [lowMixedCentered,r44_shift_eq]
  exact r44_rep_PM.centered 1 12 1 12 (by norm_num) (by norm_num) (by norm_num)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_SHc : (r44_PSHS.center 1 12 1 12).Rep lowSHCentered := by
  rw [lowSHCentered,r44_shift_eq]
  exact r44_rep_PSH.centered 1 12 1 12 (by norm_num) (by norm_num) (by norm_num)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_PSGrev :
    (r44_PSGS.center 1 6 1 (-6)).Rep (WholeIntervalPolynomial.centered (L+1) (L-1) lowPSG) :=
  r44_rep_PSG.centered 1 6 1 (-6) (by norm_num) (by norm_num [L]) (by norm_num [L])

private theorem r44_evalL_eq :
    lowPSG.eval L=(WholeIntervalPolynomial.centered (L+1) (L-1) lowPSG).coeff 0 := by
  rw [← r44_eval_eq_coeff]
  congr 1
  ring

/-! The quotient of the chord remainder: a candidate coefficient list from
synthetic division, verified by multiplying back. -/

/-- Synthetic division by `X-1/6` with every quotient coefficient scaled by `D`. -/
private def r44_synthAux (D : ℤ) : ℤ → List ℤ → List ℤ
  | _,[] => []
  | u,g :: rest => (D*g+u/6) :: r44_synthAux D (D*g+u/6) rest

/-- The negated quotient of `toPoly G` by `X-1/6`, scaled by `6^(deg-1)`. -/
private def r44_quotL (G : List ℤ) : List ℤ :=
  match G.reverse with
  | [] => []
  | gn :: rest =>
    (((6:ℤ)^(G.length-2)*gn) ::
      r44_synthAux ((6:ℤ)^(G.length-2)) ((6:ℤ)^(G.length-2)*gn) rest.dropLast).reverse.map
        (fun x => -x)

open WholeIntervalPolynomial.Certificate in
private theorem r44_toPoly_zero : ∀ l : List ℤ,l.all (fun x => x==0)=true → toPoly l=0
  | [],_ => by simp [toPoly]
  | a :: l,h => by
    simp only [List.all_cons,Bool.and_eq_true,beq_iff_eq] at h
    simp [toPoly,h.1,r44_toPoly_zero l h.2]

open WholeIntervalPolynomial.Certificate in
private theorem r44_eq_of_rep {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q)
    (hsa : a.s≠0) (hsb : b.s≠0) (h : (a.sub b).l.all (fun x => x==0)=true) : p=q := by
  have hr := ha.sub hb
  unfold Scaled.Rep at hr
  rw [r44_toPoly_zero _ h] at hr
  have hs : ((a.sub b).s:ℚ)≠0 := by
    simp only [Scaled.sub,Nat.cast_mul]
    exact mul_ne_zero (by exact_mod_cast hsa) (by exact_mod_cast hsb)
  have h0 := hr.symm
  rw [mul_eq_zero,C_eq_zero] at h0
  exact sub_eq_zero.mp (h0.resolve_left hs)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_self (c : Scaled) (hs : c.s≠0) :
    c.Rep (C (1/(c.s:ℚ))*toPoly c.l) := by
  unfold Scaled.Rep
  have hs' : (c.s:ℚ)≠0 := by exact_mod_cast hs
  rw [← mul_assoc,← map_mul,mul_one_div_cancel hs',map_one,one_mul]

open WholeIntervalPolynomial.Certificate in
private def r44_e0S : Scaled := ⟨[r44_PSGS.l.getD 0 0],r44_PSGS.s⟩

open WholeIntervalPolynomial.Certificate in
private def r44_eLS : Scaled :=
  ⟨[(r44_PSGS.center 1 6 1 (-6)).l.getD 0 0],(r44_PSGS.center 1 6 1 (-6)).s⟩

open WholeIntervalPolynomial.Certificate in
private def r44_chordS : Scaled :=
  (((Scaled.ofNat 1).sub ((⟨[6],1⟩ : Scaled).mul Scaled.var)).mul r44_e0S).add
    (((⟨[6],1⟩ : Scaled).mul Scaled.var).mul r44_eLS)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_chord : r44_chordS.Rep lowChord := by
  have hs0 : r44_PSGS.s≠0 := by decide +kernel
  have hsL : (r44_PSGS.center 1 6 1 (-6)).s≠0 := by decide +kernel
  have h0 : r44_e0S.Rep (C (lowPSG.eval 0)) :=
    r44_repC _ _ hs0 (by rw [← coeff_zero_eq_eval_zero]; exact r44_rep_PSG.coeff hs0 0)
  have hL : r44_eLS.Rep (C (lowPSG.eval L)) :=
    r44_repC _ _ hsL (by rw [r44_evalL_eq]; exact r44_rep_PSGrev.coeff hsL 0)
  exact ((Scaled.rep_one.sub ((r44_repC 6 1 (by norm_num) (by norm_num [L])).mul
    Scaled.rep_var)).mul h0).add
    (((r44_repC 6 1 (by norm_num) (by norm_num [L])).mul Scaled.rep_var).mul hL)

open WholeIntervalPolynomial.Certificate in
private def r44_fS : Scaled := r44_PSGS.sub r44_chordS

open WholeIntervalPolynomial.Certificate in
private def r44_QS : Scaled :=
  ⟨r44_quotL r44_fS.l.tail,r44_fS.s*6^(r44_fS.l.tail.length-2)⟩

open WholeIntervalPolynomial.Certificate in
private def r44_prodS : Scaled :=
  (Scaled.var.mul ((⟨[1],6⟩ : Scaled).sub Scaled.var)).mul r44_QS

theorem low_mass_identity (i : Fin 3) :
    lowMassCentered i=C ((lowMassCentered i).coeff 0)+tail (lowMassCentered i) 1 4 := by
  have hs : ((r44_massS i).center 1 12 1 12).s≠0 := by fin_cases i <;> decide +kernel
  have hl : ((r44_massS i).center 1 12 1 12).l.length-1<1+4 := by
    fin_cases i <;> decide +kernel
  have h := r44_split 1 4 (lt_of_le_of_lt ((r44_rep_mass i).natDegree_le hs) hl)
  rw [Finset.sum_range_one,pow_zero,mul_one] at h
  exact h

theorem low_mass_reserve (i : Fin 3) :
    lowMassReserve i<(lowMassCentered i).coeff 0-
      PowerTailBounds.norm (lowMassCentered i) 1 4 (1/12) := by
  have hs : ((r44_massS i).center 1 12 1 12).s≠0 := by fin_cases i <;> decide +kernel
  rw [r44_coeff_sub_norm (r44_rep_mass i) hs 0 1 4 12 (by norm_num) (by norm_num)]
  fin_cases i
  · exact r44_lt_frac (a:=109) (b:=100) (by change (109/100:ℚ)=_; norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
  · exact r44_lt_frac (a:=29) (b:=25) (by change (29/25:ℚ)=_; norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
  · exact r44_lt_frac (a:=71) (b:=50) (by change (71/50:ℚ)=_; norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)

theorem low_mass_lower (i : Fin 3) {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    (lowMassReserve i:ℝ)<aeval z (lowMass i) := by
  have hx : |z-1/12|≤(1/12:ℝ) := abs_le.mpr
    ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hb := DirectedPowerBounds.constant_lower (low_mass_identity i)
    (show |z-1/12|≤((1/12:ℚ):ℝ) by norm_num; exact hx)
  have hr : (lowMassReserve i:ℝ)<((lowMassCentered i).coeff 0:ℝ)-
      (PowerTailBounds.norm (lowMassCentered i) 1 4 (1/12):ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr (low_mass_reserve i)
    push_cast at hh
    exact hh
  have he : aeval (z-1/12) (lowMassCentered i)=aeval z (lowMass i) := by
    simp [lowMassCentered]
  rw [he] at hb
  exact hr.trans_le hb

theorem low_masses_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowRH ∧ 0<aeval z lowRG ∧ 0<aeval z lowRB := by
  have h0 := low_mass_lower 0 hz
  have h1 := low_mass_lower 1 hz
  have h2 := low_mass_lower 2 hz
  norm_num [lowMass,lowMassReserve] at h0 h1 h2
  exact ⟨by linarith,by linarith,by linarith⟩

theorem low_reversed_identity :
    lowReversed=C (lowReversed.coeff 0)+C (lowReversed.coeff 1)*X+
      C (lowReversed.coeff 2)*X^2+C (lowReversed.coeff 3)*X^3+
        tail lowReversed 4 31 := by
  have h := r44_split 4 31 (lt_of_le_of_lt (r44_rep_rev.natDegree_le (by decide +kernel))
    (by decide +kernel))
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,
    pow_one] at h
  exact h

theorem low_reversed_reserve :
    (199/100000:ℚ)<lowReversed.coeff 0 ∧
      (43/2500:ℚ)<lowReversed.coeff 1 ∧
      (277/50:ℚ)<lowReversed.coeff 2 ∧
      (297/100:ℚ)<lowReversed.coeff 3-
        DirectedPowerBounds.negativeNorm lowReversed 4 31 L := by
  have hs : (r44_PS.center 1 6 1 (-6)).s≠0 := by decide +kernel
  have hD : 0<(r44_PS.center 1 6 1 (-6)).s := Nat.pos_of_ne_zero hs
  have hD' : 0<(r44_PS.center 1 6 1 (-6)).s*6^31 := Nat.mul_pos hD (by positivity)
  -- one kernel evaluation of the reversed polynomial for the four reserves
  obtain ⟨h0,h1,h2,h3⟩ :
      (199:ℤ)*((r44_PS.center 1 6 1 (-6)).s:ℤ)<
        (r44_PS.center 1 6 1 (-6)).l.getD 0 0*((100000:ℕ):ℤ) ∧
      (43:ℤ)*((r44_PS.center 1 6 1 (-6)).s:ℤ)<(r44_PS.center 1 6 1 (-6)).l.getD 1 0*((2500:ℕ):ℤ) ∧
      (277:ℤ)*((r44_PS.center 1 6 1 (-6)).s:ℤ)<(r44_PS.center 1 6 1 (-6)).l.getD 2 0*((50:ℕ):ℤ) ∧
      (297:ℤ)*(((r44_PS.center 1 6 1 (-6)).s*6^31 : ℕ):ℤ)<
        ((r44_PS.center 1 6 1 (-6)).l.getD 3 0*((6:ℕ):ℤ)^31-
          ∑ j : Fin 31,max (-(r44_PS.center 1 6 1 (-6)).l.getD (j.val+4) 0) 0*
            ((6:ℕ):ℤ)^(31-1-j.val))*((100:ℕ):ℤ) := by
    decide +kernel
  refine ⟨?_,?_,?_,?_⟩
  · rw [r44_rep_rev.coeff hs 0]
    exact r44_lt_frac (a:=199) (b:=100000) (by norm_num) (by norm_num) hD h0
  · rw [r44_rep_rev.coeff hs 1]
    exact r44_lt_frac (a:=43) (b:=2500) (by norm_num) (by norm_num) hD h1
  · rw [r44_rep_rev.coeff hs 2]
    exact r44_lt_frac (a:=277) (b:=50) (by norm_num) (by norm_num) hD h2
  · rw [r44_coeff_sub_negnorm r44_rep_rev hs 3 4 31 6 (by norm_num) (by norm_num [L])]
    exact r44_lt_frac (a:=297) (b:=100) (by norm_num) (by norm_num) hD' h3

theorem lowP_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowP := by
  let x : ℝ := 1/6-z
  have hx : x∈Set.Icc 0 (L:ℝ) := by
    norm_num [x,L]
    exact ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hb := DirectedPowerBounds.cubic_lower low_reversed_identity hx
  have h0 : (0:ℝ)<(lowReversed.coeff 0:ℝ) := by
    exact_mod_cast lt_trans (by norm_num : (0:ℚ)<199/100000) low_reversed_reserve.1
  have h1 : (0:ℝ)≤(lowReversed.coeff 1:ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : (0:ℚ)<43/2500) low_reversed_reserve.2.1).le
  have h2 : (0:ℝ)≤(lowReversed.coeff 2:ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : (0:ℚ)<277/50) low_reversed_reserve.2.2.1).le
  have h3 : (0:ℝ)≤(lowReversed.coeff 3:ℝ)-
      (DirectedPowerBounds.negativeNorm lowReversed 4 31 L:ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : (0:ℚ)<297/100) low_reversed_reserve.2.2.2).le
  have he : aeval x lowReversed=aeval z lowP := by
    simp [lowReversed,x,L]
  rw [he] at hb
  have h1x := mul_nonneg h1 hx.1
  have h2x := mul_nonneg h2 (sq_nonneg x)
  have h3x := mul_nonneg h3 (pow_nonneg hx.1 3)
  linarith

theorem low_mixed_identity :
    lowMixedCentered=C (lowMixedCentered.coeff 0)+C (lowMixedCentered.coeff 1)*X+
      C (lowMixedCentered.coeff 2)*X^2+tail lowMixedCentered 3 32 := by
  have h := r44_split 3 32 (lt_of_le_of_lt (r44_rep_mix.natDegree_le (by decide +kernel))
    (by decide +kernel))
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,
    pow_one] at h
  exact h

theorem low_mixed_reserve :
    (23/625:ℚ)<lowMixedCentered.coeff 0 ∧
      |lowMixedCentered.coeff 1|<19/40 ∧
      (187/25:ℚ)<lowMixedCentered.coeff 2-
        PowerTailBounds.norm lowMixedCentered 3 32 (1/12) := by
  have hs : (r44_PMS.center 1 12 1 12).s≠0 := by decide +kernel
  have hs' : (0:ℚ)<(r44_PMS.center 1 12 1 12).s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hD : 0<(r44_PMS.center 1 12 1 12).s := Nat.pos_of_ne_zero hs
  have hD' : 0<(r44_PMS.center 1 12 1 12).s*12^32 := Nat.mul_pos hD (by positivity)
  -- one kernel evaluation of the mixed polynomial for the three reserves
  obtain ⟨h0,h,h2⟩ :
      (23:ℤ)*((r44_PMS.center 1 12 1 12).s:ℤ)<(r44_PMS.center 1 12 1 12).l.getD 0 0*((625:ℕ):ℤ) ∧
      |(r44_PMS.center 1 12 1 12).l.getD 1 0| *40<19*(r44_PMS.center 1 12 1 12).s ∧
      (187:ℤ)*(((r44_PMS.center 1 12 1 12).s*12^32 : ℕ):ℤ)<
        ((r44_PMS.center 1 12 1 12).l.getD 2 0*((12:ℕ):ℤ)^32-
          ∑ j : Fin 32,|(r44_PMS.center 1 12 1 12).l.getD (j.val+3) 0| *
            ((12:ℕ):ℤ)^(32-1-j.val))*((25:ℕ):ℤ) := by
    decide +kernel
  refine ⟨?_,?_,?_⟩
  · rw [r44_rep_mix.coeff hs 0]
    exact r44_lt_frac (a:=23) (b:=625) (by norm_num) (by norm_num) hD h0
  · rw [r44_rep_mix.coeff hs 1,abs_div,abs_of_pos hs',div_lt_iff₀ hs']
    have h' : ((|(r44_PMS.center 1 12 1 12).l.getD 1 0| *40:ℤ):ℚ)<
        ((19*(r44_PMS.center 1 12 1 12).s:ℤ):ℚ) := by exact_mod_cast h
    push_cast at h'
    linarith
  · rw [r44_coeff_sub_norm r44_rep_mix hs 2 3 32 12 (by norm_num) (by norm_num)]
    exact r44_lt_frac (a:=187) (b:=25) (by norm_num) (by norm_num) hD' h2

theorem lowPM_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowPM := by
  let x : ℝ := z-1/12
  have hx : |x|≤(1/12:ℝ) := abs_le.mpr
    ⟨by dsimp [x]; linarith [hz.1],by dsimp [x]; linarith [hz.2]⟩
  have hb := PowerTailBounds.quadratic_lower low_mixed_identity (by norm_num)
    (show |x|≤((1/12:ℚ):ℝ) by norm_num; exact hx)
  have h0 : (23/625:ℝ)<(lowMixedCentered.coeff 0:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr low_mixed_reserve.1
    push_cast at hh
    exact hh
  have h1 : |(lowMixedCentered.coeff 1:ℝ)|<19/40 := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr low_mixed_reserve.2.1
    push_cast at hh
    exact hh
  have h2 : (187/25:ℝ)<(lowMixedCentered.coeff 2:ℝ)-
      (PowerTailBounds.norm lowMixedCentered 3 32 (1/12):ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr low_mixed_reserve.2.2
    push_cast at hh
    exact hh
  have hlinear : -(19/40)*|x|≤(lowMixedCentered.coeff 1:ℝ)*x := by
    have hh := mul_le_mul_of_nonneg_right h1.le (abs_nonneg x)
    rw [← abs_mul] at hh
    have hh' := (abs_le.mp hh).1
    linarith
  have hquad := mul_le_mul_of_nonneg_right h2.le (sq_nonneg x)
  have he : aeval x lowMixedCentered=aeval z lowPM := by simp [lowMixedCentered,x]
  rw [he] at hb
  nlinarith [sq_nonneg (|x|-(19/40)/(2*(187/25))),sq_abs x]

theorem low_SH_identity :
    lowSHCentered=C (lowSHCentered.coeff 0)+tail lowSHCentered 1 34 := by
  have h := r44_split 1 34 (lt_of_le_of_lt (r44_rep_SHc.natDegree_le (by decide +kernel))
    (by decide +kernel))
  rw [Finset.sum_range_one,pow_zero,mul_one] at h
  exact h

theorem low_SH_reserve : (9/50:ℚ)<lowSHCentered.coeff 0-
    PowerTailBounds.norm lowSHCentered 1 34 (1/12) := by
  rw [r44_coeff_sub_norm r44_rep_SHc (by decide +kernel) 0 1 34 12 (by norm_num) (by norm_num)]
  exact r44_lt_frac (a:=9) (b:=50) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem lowPSH_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowPSH := by
  have hx : |z-1/12|≤(1/12:ℝ) := abs_le.mpr
    ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hb := DirectedPowerBounds.constant_lower low_SH_identity
    (show |z-1/12|≤((1/12:ℚ):ℝ) by norm_num; exact hx)
  have hr : (9/50:ℝ)<(lowSHCentered.coeff 0:ℝ)-
      (PowerTailBounds.norm lowSHCentered 1 34 (1/12):ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr low_SH_reserve
    push_cast at hh
    exact hh
  have he : aeval (z-1/12) lowSHCentered=aeval z lowPSH := by simp [lowSHCentered]
  rw [he] at hb
  linarith

theorem low_chord_identity : lowPSG=lowChord+X*(C L-X)*lowChordQuotient := by
  have hL : (L:ℚ)≠0 := by norm_num [L]
  have hc0 : lowChord.eval 0=lowPSG.eval 0 := by simp [lowChord]
  have hcL : lowChord.eval L=lowPSG.eval L := by
    simp only [lowChord,eval_add,eval_mul,eval_sub,eval_one,eval_C,eval_X]
    field_simp
    ring
  obtain ⟨f,hf⟩ : ∃ f,f=lowPSG-lowChord := ⟨_,rfl⟩
  have h0 : f.coeff 0=0 := by
    rw [coeff_zero_eq_eval_zero,hf,eval_sub,hc0,sub_self]
  have hfX : f=f.divX*X := by
    have h := divX_mul_X_add f
    rw [h0,map_zero,add_zero] at h
    exact h.symm
  have hroot : f.divX.IsRoot L := by
    have hfL : f.eval L=0 := by rw [hf,eval_sub,hcL,sub_self]
    rw [hfX,eval_mul,eval_X] at hfL
    exact (mul_eq_zero.mp hfL).resolve_right hL
  have hq := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hQ : lowChordQuotient=-(f.divX/ₘ(X-C L)) := by rw [lowChordQuotient,hf]
  have hfeq : lowPSG=lowChord+f := by rw [hf]; ring
  rw [hQ,hfeq]
  congr 1
  calc f=f.divX*X := hfX
    _=(X-C L)*(f.divX/ₘ(X-C L))*X := by rw [hq]
    _=X*(C L-X)*-(f.divX/ₘ(X-C L)) := by ring

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_Q : r44_QS.Rep lowChordQuotient := by
  have hsQ : r44_QS.s≠0 := by decide +kernel
  have hP := r44_rep_self r44_QS hsQ
  have hprod : r44_prodS.Rep (X*(C L-X)*(C (1/(r44_QS.s:ℚ))*toPoly r44_QS.l)) :=
    (Scaled.rep_var.mul ((r44_repC 1 6 (by norm_num) (by norm_num [L])).sub Scaled.rep_var)).mul hP
  have hf : r44_fS.Rep (lowPSG-lowChord) := r44_rep_PSG.sub r44_rep_chord
  have heq := r44_eq_of_rep hf hprod (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hid : lowPSG-lowChord=X*(C L-X)*lowChordQuotient := by
    rw [low_chord_identity]
    ring
  have hne : (X*(C L-X):ℚ[X])≠0 := by
    apply mul_ne_zero X_ne_zero
    intro h0
    have h1 := congrArg (fun p : ℚ[X] => p.coeff 1) h0
    simp at h1
  have hQ : lowChordQuotient=C (1/(r44_QS.s:ℚ))*toPoly r44_QS.l :=
    mul_left_cancel₀ hne (hid.symm.trans heq)
  rw [hQ]
  exact hP

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_Qc : (r44_QS.center 1 12 1 12).Rep lowQuotientCentered := by
  rw [lowQuotientCentered,r44_shift_eq]
  exact r44_rep_Q.centered 1 12 1 12 (by norm_num) (by norm_num) (by norm_num)

theorem low_quotient_identity :
    lowQuotientCentered=C (lowQuotientCentered.coeff 0)+tail lowQuotientCentered 1 34 := by
  have h := r44_split 1 34 (lt_of_le_of_lt (r44_rep_Qc.natDegree_le (by decide +kernel))
    (by decide +kernel))
  rw [Finset.sum_range_one,pow_zero,mul_one] at h
  exact h

theorem low_chord_reserves :
    (451/10000:ℚ)<lowPSG.eval 0 ∧ (3963/10000:ℚ)<lowPSG.eval L ∧
      (44/5:ℚ)<lowQuotientCentered.coeff 0-
        PowerTailBounds.norm lowQuotientCentered 1 34 (1/12) := by
  have hs0 : r44_PSGS.s≠0 := by decide +kernel
  have hsL : (r44_PSGS.center 1 6 1 (-6)).s≠0 := by decide +kernel
  have hsQ : (r44_QS.center 1 12 1 12).s≠0 := by decide +kernel
  -- one kernel evaluation of the separated numerator for the three reserves
  obtain ⟨h0,h1,h2⟩ :
      (451:ℤ)*(r44_PSGS.s:ℤ)<r44_PSGS.l.getD 0 0*((10000:ℕ):ℤ) ∧
      (3963:ℤ)*((r44_PSGS.center 1 6 1 (-6)).s:ℤ)<
        (r44_PSGS.center 1 6 1 (-6)).l.getD 0 0*((10000:ℕ):ℤ) ∧
      (44:ℤ)*(((r44_QS.center 1 12 1 12).s*12^34 : ℕ):ℤ)<
        ((r44_QS.center 1 12 1 12).l.getD 0 0*((12:ℕ):ℤ)^34-
          ∑ j : Fin 34,|(r44_QS.center 1 12 1 12).l.getD (j.val+1) 0| *
            ((12:ℕ):ℤ)^(34-1-j.val))*((5:ℕ):ℤ) := by
    decide +kernel
  refine ⟨?_,?_,?_⟩
  · rw [← coeff_zero_eq_eval_zero,r44_rep_PSG.coeff hs0 0]
    exact r44_lt_frac (a:=451) (b:=10000) (by norm_num) (by norm_num) (Nat.pos_of_ne_zero hs0) h0
  · rw [r44_evalL_eq,r44_rep_PSGrev.coeff hsL 0]
    exact r44_lt_frac (a:=3963) (b:=10000) (by norm_num) (by norm_num) (Nat.pos_of_ne_zero hsL)
      h1
  · rw [r44_coeff_sub_norm r44_rep_Qc hsQ 0 1 34 12 (by norm_num) (by norm_num)]
    exact r44_lt_frac (a:=44) (b:=5) (by norm_num) (by norm_num)
      (Nat.mul_pos (Nat.pos_of_ne_zero hsQ) (by positivity)) h2

theorem lowPSG_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowPSG := by
  have hx : |z-1/12|≤(1/12:ℝ) := abs_le.mpr
    ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hb := DirectedPowerBounds.constant_lower low_quotient_identity
    (show |z-1/12|≤((1/12:ℚ):ℝ) by norm_num; exact hx)
  have hr : (44/5:ℝ)<(lowQuotientCentered.coeff 0:ℝ)-
      (PowerTailBounds.norm lowQuotientCentered 1 34 (1/12):ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr low_chord_reserves.2.2
    push_cast at hh
    exact hh
  have he : aeval (z-1/12) lowQuotientCentered=aeval z lowChordQuotient := by
    simp [lowQuotientCentered]
  rw [he] at hb
  have hQ : 0≤aeval z lowChordQuotient := by linarith
  obtain ⟨e0,he0⟩ : ∃ e,e=lowPSG.eval 0 := ⟨_,rfl⟩
  obtain ⟨eL,heL⟩ : ∃ e,e=lowPSG.eval L := ⟨_,rfl⟩
  have hzero : (451/10000:ℝ)≤(e0:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr low_chord_reserves.1
    rw [← he0] at hh
    push_cast at hh
    exact hh.le
  have hend : (451/10000:ℝ)≤(eL:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr low_chord_reserves.2.1
    rw [← heL] at hh
    push_cast at hh
    linarith
  have hfirst := mul_le_mul_of_nonneg_left hzero
    (show 0≤1-6*z by linarith [hz.2])
  have hlast := mul_le_mul_of_nonneg_left hend (show 0≤6*z by linarith [hz.1])
  have h6 : ((1/L:ℚ):ℝ)=6 := by norm_num [L]
  have hchord : aeval z lowChord=(1-6*z)*(e0:ℝ)+6*z*(eL:ℝ) := by
    simp only [lowChord,map_add,map_sub,map_mul,map_one,aeval_C,aeval_X,eq_ratCast,← he0,
      ← heL,h6]
  have hprod := mul_nonneg (mul_nonneg hz.1 (show 0≤1/6-z by linarith [hz.2])) hQ
  have hid := congrArg (fun f : ℚ[X] => aeval z f) low_chord_identity
  simp only [map_add,map_mul,map_sub,aeval_X,aeval_C,eq_ratCast] at hid
  rw [show ((L:ℚ):ℝ)=1/6 by norm_num [L]] at hid
  linarith

end SquaresInCircles.Eight.GlobalGA.PositiveTD.Certificate
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PositiveTD.Certificate
open Polynomial Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

@[simp] theorem ch_cast : (ch:ℝ)=aeval frameCap C10 := by
  norm_num [ch,h,C10,C4,frameCap]
@[simp] theorem Ch_cast : (Ch:ℝ)=aeval frameCap C12 := by
  norm_num [Ch,h,C12,C10,C4,frameCap]
@[simp] theorem sh_cast : (sh:ℝ)=aeval frameCap S11 := by
  norm_num [sh,h,S11,S9,S5,frameCap]

theorem low_frame_domain {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) : z∈Icc 0 frameCap :=
  ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩

theorem low_nonradical_lower {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) :
    aeval z lowA≤lowNonradical (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z+
      Real.cos z-1 ∧
    aeval z lowAstar≤lowNonradical (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z-
      (109/200)*tilted (Explicit.lowC z) z*(frameCap-z) := by
  have hz' := low_frame_domain hz
  obtain ⟨hklo,hkhi,hllo,hlc,hchi,hlk⟩ := Explicit.low_ranges hz
  have hc : 0<Explicit.lowC z := by linarith
  have ht := taylor_bounds hz'
  have hm := tilted_polynomial_bounds (c:=lowC) hz' (by simpa using hc)
  simp only [lowC_eval] at hm
  have hD := mul_le_mul_of_nonneg_left diagonal_le_cbar
    (show 0≤1+Explicit.lowC z by linarith)
  have hs := sigma_sine_upper hz' hc.le
  have hW0 := mul_le_mul_of_nonneg_left
    (add_le_add ht.2.2.2.2.1 ht.2.1) hc.le
  have hW : Explicit.lowC z/2*(1+aeval z C10+aeval z S11)≤
      Explicit.lowC z*edgeWidth z := by
    rw [edgeWidth_positive_formula hz']
    nlinarith only [hW0]
  have hsep := mul_le_mul_of_nonneg_right hm.2.2 (sub_nonneg.mpr hz'.2)
  rw [show (cbar:ℝ)=449607033/500000000 by norm_num [cbar]] at hD
  rw [show (sigmabar:ℝ)=1415477291/1000000000 by norm_num [sigmabar]] at hs
  constructor
  · norm_num only [lowA,map_add,map_sub,map_mul,map_one,aeval_C,eq_ratCast,lowK_eval,lowL_eval,lowC_eval]
    dsimp [lowNonradical]
    nlinarith only [hm.2.1,ht.2.2.2.2.1,hD,hs,hW]
  · norm_num only [lowAstar,map_add,map_sub,map_mul,map_one,aeval_C,eq_ratCast,aeval_X,
      lowK_eval,lowL_eval,lowC_eval,h]
    dsimp [lowNonradical,frameCap] at hsep ⊢
    nlinarith only [hm.2.1,hD,hs,hW,hsep]

theorem low_norm_bounds {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) :
    (pairNorm (Explicit.lowK z) 1 (-z))^2≤aeval z lowPH ∧
    (pairNorm (Explicit.lowK z) (Explicit.lowL z) 0)^2≤aeval z lowPG ∧
    (pairNorm (Explicit.lowL z) (tilted (Explicit.lowC z) z) 0)^2≤aeval z lowPB ∧
    (pairNorm (Explicit.lowK z) 1 (-frameCap))^2≤aeval z lowPHh ∧
    (pairNorm (Explicit.lowK z) 1 0)^2≤aeval z lowPH0 ∧
    (pairNorm (Explicit.lowK z) (Explicit.lowL z) (-frameCap))^2≤aeval z lowPGh := by
  have hz' := low_frame_domain hz
  obtain ⟨hklo,hkhi,hllo,hlc,hchi,hlk⟩ := Explicit.low_ranges hz
  have hk : 0<Explicit.lowK z := by linarith
  have hl : 0<Explicit.lowL z := by linarith
  have hc : 0<Explicit.lowC z := by linarith
  have hm := tilted_polynomial_bounds (c:=lowC) hz' (by simpa using hc)
  simp only [lowC_eval] at hm
  have hm0 : 0<tilted (Explicit.lowC z) z := tilted_pos hc hz'
  have hm2 : (tilted (Explicit.lowC z) z)^2≤(aeval z (mPlus lowC))^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm.2.2)
      (show 0≤aeval z (mPlus lowC)+tilted (Explicit.lowC z) z by linarith [hm.2.2])]
  have hzcap : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hs := (taylor_bounds hz').2.1
  have hscap := (taylor_bounds hzcap).2.1
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have hh := negative_norm_sq_le (q:=1) hk (by norm_num) hz' hs
    norm_num only [lowPH,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,eq_ratCast,lowK_eval]
    nlinarith only [hh]
  · rw [zero_norm_sq]
    simp [lowPG]
  · rw [zero_norm_sq]
    simp only [lowPB,map_add,map_pow,lowL_eval]
    linarith
  · have hh := negative_norm_sq_le (q:=1) hk (by norm_num) hzcap hscap
    norm_num only [lowPHh,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,eq_ratCast,
      lowK_eval,Rat.cast_mul,sh_cast]
    nlinarith only [hh]
  · rw [zero_norm_sq]
    simp [lowPH0,add_comm]
  · have hh := negative_norm_sq_le hk hl hzcap hscap
    norm_num only [lowPGh,map_add,map_sub,map_mul,map_pow,aeval_C,eq_ratCast,
      lowK_eval,lowL_eval,Rat.cast_mul,sh_cast]
    nlinarith only [hh]

theorem low_J_lower {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) :
    aeval z lowJ≤Explicit.lowK z*(PositiveAngularEnvelope.phi (frameCap-z)-1)+
      Explicit.lowL z*(Real.cos frameCap-Real.cos z) := by
  have hz' := low_frame_domain hz
  obtain ⟨hklo,hkhi,hllo,hlc,hchi,hlk⟩ := Explicit.low_ranges hz
  have ht := taylor_bounds hz'
  have htcap := taylor_bounds (show frameCap∈Icc 0 frameCap by
    exact ⟨by norm_num [frameCap],le_rfl⟩)
  have hs : 0≤Real.sin z := (transport_trig hz').2.2.1
  have hc : 0≤Real.cos z := by linarith [(transport_trig hz').1]
  have hsum : (ch:ℝ)+(sh:ℝ)≤Real.cos frameCap+Real.sin frameCap := by
    rw [ch_cast,sh_cast]
    linarith [htcap.2.1,htcap.2.2.2.2.1]
  have hsum0 : 0≤Real.cos frameCap+Real.sin frameCap := by
    have tt := transport_trig (show frameCap∈Icc 0 frameCap by
      exact ⟨by norm_num [frameCap],le_rfl⟩)
    linarith [tt.1,tt.2.2.1]
  have hprod := mul_le_mul hsum ht.2.2.2.2.1
    (show 0≤aeval z C10 by linarith [ht.2.2.2.1]) hsum0
  have hdiff : Real.cos frameCap-Real.sin frameCap≤(Ch:ℝ)-(sh:ℝ) := by
    rw [Ch_cast,sh_cast]
    linarith [htcap.2.1,htcap.2.2.2.2.2]
  have hdiff0 : 0≤(Ch:ℝ)-(sh:ℝ) := by
    have tt := transport_trig (show frameCap∈Icc 0 frameCap by
      exact ⟨by norm_num [frameCap],le_rfl⟩)
    linarith [tt.2.2.2.2]
  have hprod' := mul_le_mul hdiff ht.2.2.1 hs hdiff0
  have hphi : PositiveAngularEnvelope.phi (frameCap-z)=
      (Real.cos frameCap+Real.sin frameCap)*Real.cos z-
        (Real.cos frameCap-Real.sin frameCap)*Real.sin z := by
    simp only [PositiveAngularEnvelope.phi,Real.cos_sub,Real.sin_sub]
    ring
  have hphiLower : ((ch:ℝ)+(sh:ℝ))*aeval z C10-
      ((Ch:ℝ)-(sh:ℝ))*aeval z S9≤PositiveAngularEnvelope.phi (frameCap-z) := by
    rw [hphi]
    linarith
  have hkprod := mul_le_mul_of_nonneg_left (sub_le_sub_right hphiLower 1)
    (show 0≤Explicit.lowK z by linarith)
  have hcos : (ch:ℝ)-aeval z C12≤Real.cos frameCap-Real.cos z := by
    rw [ch_cast]
    linarith [htcap.2.2.2.2.1,ht.2.2.2.2.2]
  have hlprod := mul_le_mul_of_nonneg_left hcos
    (show 0≤Explicit.lowL z by linarith)
  norm_num only [lowJ,map_add,map_sub,map_mul,map_one,aeval_C,eq_ratCast,lowK_eval,lowL_eval,
    Rat.cast_add,Rat.cast_sub]
  linarith only [hkprod,hlprod]

theorem lowPM_num3 :
    lowPM=num3 (lowA+lowJ) lowPH lowPG lowPB lowRH lowRG lowRB := by
  dsimp [lowPM,lowP,lowDen,num3]
  ring

theorem low_H_positive {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) :
    0<baseline (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z+
      V R (Explicit.lowK z) 1 z := by
  have hr := low_masses_positive hz
  have hn := low_norm_bounds hz
  have h := num3_transfer hr.1 hr.2.1 hr.2.2
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.2.1 hn.2.2.1 (low_nonradical_lower hz).1 (lowP_positive hz)
  have hc : 1≤Explicit.lowC z := by
    have hh := Explicit.low_ranges hz
    linarith [hh.2.2.1,hh.2.2.2.1]
  rw [low_H_identity hc]
  exact h

theorem low_M_positive {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) :
    0<baseline (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z+
      V R (Explicit.lowK z) 1 z+Explicit.lowK z*(PositiveAngularEnvelope.phi (frameCap-z)-1)+
        Explicit.lowL z*(Real.cos frameCap-Real.cos z) := by
  have hr := low_masses_positive hz
  have hn := low_norm_bounds hz
  have hA : aeval z (lowA+lowJ)≤
      lowNonradical (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z+
        Real.cos z-1+(Explicit.lowK z*(PositiveAngularEnvelope.phi (frameCap-z)-1)+
          Explicit.lowL z*(Real.cos frameCap-Real.cos z)) := by
    simpa only [map_add] using add_le_add (low_nonradical_lower hz).1 (low_J_lower hz)
  have hp : 0<aeval z (num3 (lowA+lowJ) lowPH lowPG lowPB lowRH lowRG lowRB) := by
    rw [← lowPM_num3]
    exact lowPM_positive hz
  have h := num3_transfer hr.1 hr.2.1 hr.2.2
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.2.1 hn.2.2.1 hA hp
  have hc : 1≤Explicit.lowC z := by
    have hh := Explicit.low_ranges hz
    linarith [hh.2.2.1,hh.2.2.2.1]
  rw [low_H_identity hc]
  linarith only [h]

theorem low_SH_positive {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) :
    0<baseline (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z-
      (109/200)*tilted (Explicit.lowC z) z*(frameCap-z)+V R (Explicit.lowK z) 1 frameCap := by
  have hr := low_masses_positive hz
  have hn := low_norm_bounds hz
  have htcap := taylor_bounds (show frameCap∈Icc 0 frameCap by
    exact ⟨by norm_num [frameCap],le_rfl⟩)
  have hA : aeval z (lowAstar+C (ch-1))≤
      lowNonradical (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z-
        (109/200)*tilted (Explicit.lowC z) z*(frameCap-z)+Real.cos frameCap-1 := by
    have hh := (low_nonradical_lower hz).2
    norm_num only [map_add,aeval_C,eq_ratCast,Rat.cast_sub,Rat.cast_one,ch_cast]
    linarith [htcap.2.2.2.2.1]
  have h := num3_transfer (show 0<aeval z (C (77/100):ℚ[X]) by norm_num)
    hr.2.1 hr.2.2 (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.2.2.2.1 hn.2.1 hn.2.2.1 hA (lowPSH_positive hz)
  have hc : 1≤Explicit.lowC z := by
    have hh := Explicit.low_ranges hz
    linarith [hh.2.2.1,hh.2.2.2.1]
  have he := low_H_identity (k:=Explicit.lowK z) (l:=Explicit.lowL z)
    (c:=Explicit.lowC z) (z:=z) (t:=frameCap) hc
  linarith only [h,he]

theorem low_SG_positive {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) :
    0<baseline (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z-
      (109/200)*tilted (Explicit.lowC z) z*(frameCap-z)+
        V R (Explicit.lowK z) (Explicit.lowL z) frameCap := by
  have hr := low_masses_positive hz
  have hn := low_norm_bounds hz
  obtain ⟨hklo,hkhi,hllo,hlc,hchi,hlk⟩ := Explicit.low_ranges hz
  have hr0 : 0<aeval z lowRHzero := by
    norm_num only [lowRHzero,map_add,map_mul,aeval_C,eq_ratCast,lowK_eval]
    linarith
  have hr1 : 0<aeval z lowRGcap := by
    norm_num only [lowRGcap,map_mul,aeval_C,eq_ratCast,lowL_eval]
    linarith
  have htcap := taylor_bounds (show frameCap∈Icc 0 frameCap by
    exact ⟨by norm_num [frameCap],le_rfl⟩)
  have hcos : (ch:ℝ)-1≤Real.cos frameCap-1 := by
    rw [ch_cast]
    linarith [htcap.2.2.2.2.1]
  have hp := mul_le_mul_of_nonneg_left hcos (show 0≤Explicit.lowL z by linarith)
  have hA : aeval z (lowAstar+lowL*C (ch-1))≤
      lowNonradical (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z-
        (109/200)*tilted (Explicit.lowC z) z*(frameCap-z)+
          Explicit.lowL z*(Real.cos frameCap-1) := by
    have hh := (low_nonradical_lower hz).2
    norm_num only [map_add,map_mul,aeval_C,eq_ratCast,Rat.cast_sub,Rat.cast_one,lowL_eval]
    linarith only [hh,hp]
  have h := num3_transfer hr0 hr1 hr.2.2
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.2.2.2.2.1 hn.2.2.2.2.2 hn.2.2.1 hA (lowPSG_positive hz)
  have he := low_G_identity (k:=Explicit.lowK z) (l:=Explicit.lowL z)
    (c:=Explicit.lowC z) (z:=z) (t:=frameCap) (by linarith : 1≤Explicit.lowC z)
  linarith only [h,he]

/-- Concrete positivity for every intrinsic alternative on the whole
low interval, with no residual scalar premise. -/
theorem low_endpoint_positive {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) (i j : Fin 4) :
    0<baseline (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z+
      endpoint (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z i j := by
  obtain ⟨hklo,hkhi,hllo,hlc,hchi,hlk⟩ := Explicit.low_ranges hz
  have hm := Explicit.low_tilted hz
  exact low_scalars_positive ⟨hklo.le,by linarith⟩ ⟨hllo.le,hlk.le⟩
    ⟨hm.1,hm.2.le⟩ hz (low_H_positive hz) (low_M_positive hz)
    (low_SH_positive hz) (low_SG_positive hz) i j

end SquaresInCircles.Eight.GlobalGA.PositiveTD.Certificate
end
end
end
