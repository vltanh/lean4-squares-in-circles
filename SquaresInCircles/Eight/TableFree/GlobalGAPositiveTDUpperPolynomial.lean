module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDLowPolynomial
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# Whole-interval polynomial reserves for the upper TD2 family

Uncompiled source.  The coefficient formulas change only at their common
clamp.  The tight H numerator on the first interval retains its positive
quadratic; the other three numerators use one centered coefficient sum.
All identities and reserves below concern the explicitly defined
polynomials on their entire natural coefficient interval.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD.Certificate
open Polynomial PowerTailBounds Explicit

def upperMid (a : Upper) : ℚ := (left a+right a)/2
def upperRadius (a : Upper) : ℚ := (right a-left a)/2
def upperMass (a : Upper) : Fin 5→ℚ[X] :=
  ![upperRk a,upperRm a,upperRc a,upperRHminus a,upperRBminus a]
def upperMassCentered (a : Upper) (i : Fin 5) : ℚ[X] :=
  DirectedPowerBounds.shift (upperMid a) (upperMass a i)
def upperHShifted : ℚ[X] := DirectedPowerBounds.shift L (upperPH .varying)
def upperBCentered (a : Upper) : ℚ[X] :=
  DirectedPowerBounds.shift (upperMid a) (upperPB a)
def upperHClampedCentered : ℚ[X] :=
  DirectedPowerBounds.shift (upperMid .clamped) (upperPH .clamped)

/-! ### Kernel certificates

Each polynomial is represented as a scaled integer coefficient list
(`WholeIntervalPolynomial.Certificate`), mirroring its definition; the
shift to the interval midpoint is the composition `centered`.  The
coefficient sums `norm` and `negativeNorm` are compared in integers. -/

section r45Certificates
open WholeIntervalPolynomial.Certificate

private theorem r45_eq_tail {p : ℚ[X]} {n : ℕ} (hp : p.natDegree≤n) :
    p=C (p.coeff 0)+tail p 1 n := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hp)]
  rw [Finset.sum_range_succ',tail,
    Fin.sum_univ_eq_sum_range (fun j => C (p.coeff (j+1))*X^(j+1)) n]
  simp only [pow_zero,mul_one]
  ring

private theorem r45_eq_quad_tail {p : ℚ[X]} {n : ℕ} (hp : p.natDegree≤n+2) :
    p=C (p.coeff 0)+C (p.coeff 1)*X+C (p.coeff 2)*X^2+tail p 3 n := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (show p.natDegree<n+3 by omega)]
  rw [tail,Fin.sum_univ_eq_sum_range (fun j => C (p.coeff (j+3))*X^(j+3)) n,
    Finset.sum_range_succ',Finset.sum_range_succ',Finset.sum_range_succ']
  simp only [add_assoc,Nat.reduceAdd,zero_add,pow_zero,mul_one,pow_one]
  ring

private theorem r45_shift_centered (m : ℚ) (p : ℚ[X]) :
    DirectedPowerBounds.shift m p=WholeIntervalPolynomial.centered (m-1) (m+1) p := by
  unfold DirectedPowerBounds.shift WholeIntervalPolynomial.centered WholeIntervalPolynomial.affine
  congr 1
  rw [show (m-1+(m+1))/2=m by ring,show (m+1-(m-1))/2=1 by ring,map_one,one_mul]

private def r45_normZ (l : List ℤ) (start n rn rd : ℕ) : ℤ :=
  ∑ j : Fin n,|l.getD (j.val+start) 0| * (rn:ℤ)^(j.val+1)*(rd:ℤ)^(n-(j.val+1))

private def r45_negNormZ (l : List ℤ) (start n rn rd : ℕ) : ℤ :=
  ∑ j : Fin n,max (-(l.getD (j.val+start) 0)) 0*(rn:ℤ)^(j.val+1)*(rd:ℤ)^(n-(j.val+1))

private theorem r45_pow_split (rd : ℚ) {n : ℕ} (j : Fin n) :
    rd^n=rd^(j.val+1)*rd^(n-(j.val+1)) := by
  rw [← pow_add]
  congr 1
  have := j.isLt
  omega

private theorem r45_norm_eq {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0)
    (start n rn rd : ℕ) (hrd : rd≠0) :
    PowerTailBounds.norm p start n ((rn:ℚ)/rd)=
      (r45_normZ c.l start n rn rd:ℚ)/(c.s*(rd:ℚ)^n) := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hrd' : (0:ℚ)<rd := by exact_mod_cast Nat.pos_of_ne_zero hrd
  unfold PowerTailBounds.norm r45_normZ
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hc.coeff hs,abs_div,abs_of_pos hs',div_pow,r45_pow_split (rd:ℚ) j]
  field_simp

private theorem r45_negNorm_eq {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0)
    (start n rn rd : ℕ) (hrd : rd≠0) :
    DirectedPowerBounds.negativeNorm p start n ((rn:ℚ)/rd)=
      (r45_negNormZ c.l start n rn rd:ℚ)/(c.s*(rd:ℚ)^n) := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hrd' : (0:ℚ)<rd := by exact_mod_cast Nat.pos_of_ne_zero hrd
  have key (x : ℚ) : max (-(x/c.s)) 0=max (-x) 0/c.s := by
    rcases le_total x 0 with h | h
    · rw [max_eq_left (by rw [neg_nonneg]; exact div_nonpos_of_nonpos_of_nonneg h hs'.le),
        max_eq_left (by linarith)]
      ring
    · rw [max_eq_right (by rw [neg_nonpos]; exact div_nonneg h hs'.le),
        max_eq_right (by linarith),zero_div]
  unfold DirectedPowerBounds.negativeNorm r45_negNormZ
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hc.coeff hs,key,div_pow,r45_pow_split (rd:ℚ) j]
  field_simp

private theorem r45_reserve {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0)
    {n rn rd Rn Rd : ℕ} {r R : ℚ} (hr : r=(rn:ℚ)/rd) (hR : R=(Rn:ℚ)/Rd)
    (hrd : rd≠0) (hRd : Rd≠0)
    (hz : (Rn:ℤ)*c.s*(rd:ℤ)^n<(c.l.getD 0 0*(rd:ℤ)^n-r45_normZ c.l 1 n rn rd)*Rd) :
    R<p.coeff 0-PowerTailBounds.norm p 1 n r := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hrd' : (0:ℚ)<rd := by exact_mod_cast Nat.pos_of_ne_zero hrd
  have hRd' : (0:ℚ)<Rd := by exact_mod_cast Nat.pos_of_ne_zero hRd
  have hz' : (((Rn:ℤ)*c.s*(rd:ℤ)^n:ℤ):ℚ)<
      (((c.l.getD 0 0*(rd:ℤ)^n-r45_normZ c.l 1 n rn rd)*Rd:ℤ):ℚ) := by exact_mod_cast hz
  push_cast at hz'
  rw [hr,hR,hc.coeff hs,r45_norm_eq hc hs 1 n rn rd hrd]
  have he : (c.l.getD 0 0:ℚ)/c.s-(r45_normZ c.l 1 n rn rd:ℚ)/(c.s*(rd:ℚ)^n)=
      ((c.l.getD 0 0:ℚ)*(rd:ℚ)^n-r45_normZ c.l 1 n rn rd)/(c.s*(rd:ℚ)^n) := by
    field_simp
  rw [he,div_lt_div_iff₀ hRd' (by positivity)]
  linarith

private theorem r45_coeff_gt {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) (k : ℕ)
    {Rn Rd : ℕ} {R : ℚ} (hR : R=(Rn:ℚ)/Rd) (hRd : Rd≠0)
    (hz : (Rn:ℤ)*c.s<c.l.getD k 0*Rd) : R<p.coeff k := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hRd' : (0:ℚ)<Rd := by exact_mod_cast Nat.pos_of_ne_zero hRd
  have hz' : (((Rn:ℤ)*c.s:ℤ):ℚ)<((c.l.getD k 0*Rd:ℤ):ℚ) := by exact_mod_cast hz
  push_cast at hz'
  rw [hR,hc.coeff hs,div_lt_div_iff₀ hRd' hs']
  linarith

private theorem r45_quad_reserve {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0)
    {n rn rd Rn Rd : ℕ} {r R : ℚ} (hr : r=(rn:ℚ)/rd) (hR : R=(Rn:ℚ)/Rd)
    (hrd : rd≠0) (hRd : Rd≠0)
    (hz : (Rn:ℤ)*c.s*(rd:ℤ)^n<(c.l.getD 2 0*(rd:ℤ)^n-r45_negNormZ c.l 3 n rn rd)*Rd) :
    R<p.coeff 2-DirectedPowerBounds.negativeNorm p 3 n r := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hrd' : (0:ℚ)<rd := by exact_mod_cast Nat.pos_of_ne_zero hrd
  have hRd' : (0:ℚ)<Rd := by exact_mod_cast Nat.pos_of_ne_zero hRd
  have hz' : (((Rn:ℤ)*c.s*(rd:ℤ)^n:ℤ):ℚ)<
      (((c.l.getD 2 0*(rd:ℤ)^n-r45_negNormZ c.l 3 n rn rd)*Rd:ℤ):ℚ) := by exact_mod_cast hz
  push_cast at hz'
  rw [hr,hR,hc.coeff hs,r45_negNorm_eq hc hs 3 n rn rd hrd]
  have he : (c.l.getD 2 0:ℚ)/c.s-(r45_negNormZ c.l 3 n rn rd:ℚ)/(c.s*(rd:ℚ)^n)=
      ((c.l.getD 2 0:ℚ)*(rd:ℚ)^n-r45_negNormZ c.l 3 n rn rd)/(c.s*(rd:ℚ)^n) := by
    field_simp
  rw [he,div_lt_div_iff₀ hRd' (by positivity)]
  linarith

/-! Builders mirroring the definitions of the polynomials. -/

private def r45_S5S : Scaled :=
  (Scaled.var.sub ((Scaled.const (1/6)).mul (Scaled.var.pow 3))).add
    ((Scaled.const (1/120)).mul (Scaled.var.pow 5))

private theorem r45_rep_S5 : r45_S5S.Rep S5 :=
  (Scaled.rep_var.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 5))

private def r45_S9S : Scaled :=
  (r45_S5S.sub ((Scaled.const (1/5040)).mul (Scaled.var.pow 7))).add
    ((Scaled.const (1/362880)).mul (Scaled.var.pow 9))

private theorem r45_rep_S9 : r45_S9S.Rep S9 :=
  (r45_rep_S5.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 7))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 9))

private def r45_S11S : Scaled :=
  r45_S9S.sub ((Scaled.const (1/39916800)).mul (Scaled.var.pow 11))

private theorem r45_rep_S11 : r45_S11S.Rep S11 :=
  r45_rep_S9.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 11))

private def r45_C4S : Scaled :=
  ((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (1/24)).mul (Scaled.var.pow 4))

private theorem r45_rep_C4 : r45_C4S.Rep C4 :=
  (Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4))

private def r45_C10S : Scaled :=
  ((r45_C4S.sub ((Scaled.const (1/720)).mul (Scaled.var.pow 6))).add
    ((Scaled.const (1/40320)).mul (Scaled.var.pow 8))).sub
    ((Scaled.const (1/3628800)).mul (Scaled.var.pow 10))

private theorem r45_rep_C10 : r45_C10S.Rep C10 :=
  ((r45_rep_C4.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 6))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 8))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 10))

private def r45_C12S : Scaled :=
  r45_C10S.add ((Scaled.const (1/479001600)).mul (Scaled.var.pow 12))

private theorem r45_rep_C12 : r45_C12S.Rep C12 :=
  r45_rep_C10.add ((Scaled.rep_const _).mul (Scaled.rep_var.pow 12))

private def r45_KS : Upper→Scaled
  | .varying => (Scaled.const (117/200)).add ((Scaled.const (1/2)).mul Scaled.var)
  | .clamped => Scaled.const (653/800)

private theorem r45_rep_K : ∀ a : Upper,(r45_KS a).Rep (upperK a)
  | .varying => (Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)
  | .clamped => Scaled.rep_const _

private def r45_CS : Upper→Scaled
  | .varying => (Scaled.const (57/50)).sub ((Scaled.const (7/10)).mul Scaled.var)
  | .clamped => Scaled.const (653/800)

private theorem r45_rep_C : ∀ a : Upper,(r45_CS a).Rep (upperC a)
  | .varying => (Scaled.rep_const _).sub ((Scaled.rep_const _).mul Scaled.rep_var)
  | .clamped => Scaled.rep_const _

private def r45_mMinusS (c : Scaled) : Scaled :=
  c.mul (r45_C10S.add ((Scaled.const etaQ).mul r45_S11S))

private theorem r45_rep_mMinus {c : Scaled} {q : ℚ[X]} (hc : c.Rep q) :
    (r45_mMinusS c).Rep (mMinus q) :=
  hc.mul (r45_rep_C10.add ((Scaled.rep_const _).mul r45_rep_S11))

private def r45_mPlusS (c : Scaled) : Scaled :=
  c.mul (r45_C12S.add ((Scaled.const etaQ).mul r45_S9S))

private theorem r45_rep_mPlus {c : Scaled} {q : ℚ[X]} (hc : c.Rep q) :
    (r45_mPlusS c).Rep (mPlus q) :=
  hc.mul (r45_rep_C12.add ((Scaled.rep_const _).mul r45_rep_S9))

private def r45_MtS (a : Upper) : Scaled :=
  (r45_CS a).mul (r45_C4S.add ((Scaled.const etaQ).mul r45_S5S))

private theorem r45_rep_Mt (a : Upper) : (r45_MtS a).Rep (upperMtilde a) :=
  (r45_rep_C a).mul (r45_rep_C4.add ((Scaled.rep_const _).mul r45_rep_S5))

private def r45_AS (a : Upper) : Scaled :=
  ((((((((Scaled.const 2).mul (r45_KS a)).add (Scaled.const 5)).add r45_C10S).add
    ((Scaled.const (3/2)).mul (r45_mMinusS (r45_CS a)))).add
    ((Scaled.const (1/2)).mul (r45_CS a))).add
    (((Scaled.const (1/2)).mul (r45_CS a)).mul (((Scaled.ofNat 1).add r45_C10S).add r45_S11S))).sub
    (((r45_CS a).mul (Scaled.const sigmabar)).mul r45_S9S))

private theorem r45_rep_A (a : Upper) : (r45_AS a).Rep (upperA a) :=
  ((((((((Scaled.rep_const _).mul (r45_rep_K a)).add (Scaled.rep_const _)).add r45_rep_C10).add
    ((Scaled.rep_const _).mul (r45_rep_mMinus (r45_rep_C a)))).add
    ((Scaled.rep_const _).mul (r45_rep_C a))).add
    (((Scaled.rep_const _).mul (r45_rep_C a)).mul ((Scaled.rep_one.add r45_rep_C10).add
      r45_rep_S11))).sub
    (((r45_rep_C a).mul (Scaled.rep_const _)).mul r45_rep_S9))

private def r45_num4S (A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled) : Scaled :=
  (((((((Scaled.const 2).mul A).mul r0).mul r1).mul r2).mul r3).sub
    ((Scaled.const Rbar).mul
      ((((((((P0.add (r0.pow 2)).mul r1).mul r2).mul r3)).add
        ((((P1.add (r1.pow 2)).mul r0).mul r2).mul r3)).add
        ((((P2.add (r2.pow 2)).mul r0).mul r1).mul r3)).add
        ((((P3.add (r3.pow 2)).mul r0).mul r1).mul r2))))

private theorem r45_rep_num4 {A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled}
    {a p0 p1 p2 p3 s0 s1 s2 s3 : ℚ[X]} (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1)
    (h2 : P2.Rep p2) (h3 : P3.Rep p3) (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2)
    (g3 : r3.Rep s3) :
    (r45_num4S A P0 P1 P2 P3 r0 r1 r2 r3).Rep (num4 a p0 p1 p2 p3 s0 s1 s2 s3) :=
  (((((((Scaled.rep_const _).mul hA).mul g0).mul g1).mul g2).mul g3).sub
    ((Scaled.rep_const _).mul
      ((((((((h0.add (g0.pow 2)).mul g1).mul g2).mul g3)).add
        ((((h1.add (g1.pow 2)).mul g0).mul g2).mul g3)).add
        ((((h2.add (g2.pow 2)).mul g0).mul g1).mul g3)).add
        ((((h3.add (g3.pow 2)).mul g0).mul g1).mul g2))))

private def r45_PkS (a : Upper) : Scaled := (Scaled.ofNat 1).add ((r45_KS a).pow 2)
private theorem r45_rep_Pk (a : Upper) : (r45_PkS a).Rep (upperPk a) :=
  Scaled.rep_one.add ((r45_rep_K a).pow 2)

private def r45_PmS (a : Upper) : Scaled := (Scaled.ofNat 1).add ((r45_mPlusS (r45_CS a)).pow 2)
private theorem r45_rep_Pm (a : Upper) : (r45_PmS a).Rep (upperPm a) :=
  Scaled.rep_one.add ((r45_rep_mPlus (r45_rep_C a)).pow 2)

private def r45_PcS (a : Upper) : Scaled := (Scaled.ofNat 1).add ((r45_CS a).pow 2)
private theorem r45_rep_Pc (a : Upper) : (r45_PcS a).Rep (upperPc a) :=
  Scaled.rep_one.add ((r45_rep_C a).pow 2)

private def r45_PHmS (a : Upper) : Scaled :=
  ((Scaled.ofNat 1).add ((r45_KS a).pow 2)).sub (((Scaled.const 2).mul (r45_KS a)).mul r45_S11S)
private theorem r45_rep_PHm (a : Upper) : (r45_PHmS a).Rep (upperPHminus a) :=
  (Scaled.rep_one.add ((r45_rep_K a).pow 2)).sub
    (((Scaled.rep_const _).mul (r45_rep_K a)).mul r45_rep_S11)

private def r45_PBmS (a : Upper) : Scaled :=
  ((Scaled.ofNat 1).add ((r45_mPlusS (r45_CS a)).pow 2)).sub
    (((Scaled.const 2).mul (r45_mMinusS (r45_CS a))).mul r45_S11S)
private theorem r45_rep_PBm (a : Upper) : (r45_PBmS a).Rep (upperPBminus a) :=
  (Scaled.rep_one.add ((r45_rep_mPlus (r45_rep_C a)).pow 2)).sub
    (((Scaled.rep_const _).mul (r45_rep_mMinus (r45_rep_C a))).mul r45_rep_S11)

private def r45_RkS (a : Upper) : Scaled :=
  (Scaled.const (81/100)).add ((Scaled.const (293/500)).mul (r45_KS a))
private theorem r45_rep_Rk (a : Upper) : (r45_RkS a).Rep (upperRk a) :=
  (Scaled.rep_const _).add ((Scaled.rep_const _).mul (r45_rep_K a))

private def r45_RmS (a : Upper) : Scaled :=
  (Scaled.const (143/200)).add ((Scaled.const (699/1000)).mul (r45_MtS a))
private theorem r45_rep_Rm (a : Upper) : (r45_RmS a).Rep (upperRm a) :=
  (Scaled.rep_const _).add ((Scaled.rep_const _).mul (r45_rep_Mt a))

private def r45_RcS (a : Upper) : Scaled :=
  (Scaled.const (18/25)).add ((Scaled.const (347/500)).mul (r45_CS a))
private theorem r45_rep_Rc (a : Upper) : (r45_RcS a).Rep (upperRc a) :=
  (Scaled.rep_const _).add ((Scaled.rep_const _).mul (r45_rep_C a))

private def r45_RHmS (a : Upper) : Scaled :=
  ((Scaled.const (9/10)).mul r45_C4S).add ((Scaled.const (87/200)).mul ((r45_KS a).sub r45_S5S))
private theorem r45_rep_RHm (a : Upper) : (r45_RHmS a).Rep (upperRHminus a) :=
  ((Scaled.rep_const _).mul r45_rep_C4).add
    ((Scaled.rep_const _).mul ((r45_rep_K a).sub r45_rep_S5))

private def r45_RBmS (a : Upper) : Scaled :=
  ((Scaled.const (9/10)).mul r45_C4S).add ((Scaled.const (87/200)).mul ((r45_MtS a).sub r45_S5S))
private theorem r45_rep_RBm (a : Upper) : (r45_RBmS a).Rep (upperRBminus a) :=
  ((Scaled.rep_const _).mul r45_rep_C4).add
    ((Scaled.rep_const _).mul ((r45_rep_Mt a).sub r45_rep_S5))

private def r45_PHS (a : Upper) : Scaled :=
  r45_num4S (r45_AS a) (r45_PkS a) (r45_PmS a) (r45_PHmS a) (r45_PcS a)
    (r45_RkS a) (r45_RmS a) (r45_RHmS a) (r45_RcS a)
private theorem r45_rep_PH (a : Upper) : (r45_PHS a).Rep (upperPH a) :=
  r45_rep_num4 (r45_rep_A a) (r45_rep_Pk a) (r45_rep_Pm a) (r45_rep_PHm a) (r45_rep_Pc a)
    (r45_rep_Rk a) (r45_rep_Rm a) (r45_rep_RHm a) (r45_rep_Rc a)

private def r45_PBS (a : Upper) : Scaled :=
  r45_num4S (r45_AS a) (r45_PkS a) (r45_PkS a) (r45_PBmS a) (r45_PcS a)
    (r45_RkS a) (r45_RkS a) (r45_RBmS a) (r45_RcS a)
private theorem r45_rep_PB (a : Upper) : (r45_PBS a).Rep (upperPB a) :=
  r45_rep_num4 (r45_rep_A a) (r45_rep_Pk a) (r45_rep_Pk a) (r45_rep_PBm a) (r45_rep_Pc a)
    (r45_rep_Rk a) (r45_rep_Rk a) (r45_rep_RBm a) (r45_rep_Rc a)

private def r45_massS (a : Upper) : Fin 5→Scaled :=
  ![r45_RkS a,r45_RmS a,r45_RcS a,r45_RHmS a,r45_RBmS a]

private theorem r45_rep_mass (a : Upper) (i : Fin 5) : (r45_massS a i).Rep (upperMass a i) := by
  fin_cases i
  · exact r45_rep_Rk a
  · exact r45_rep_Rm a
  · exact r45_rep_Rc a
  · exact r45_rep_RHm a
  · exact r45_rep_RBm a

private def r45_center (c : Scaled) : Upper→Scaled
  | .varying => c.center 1 480 151 480
  | .clamped => c.center 1 160 93 160

private theorem r45_rep_shift {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (a : Upper) :
    (r45_center c a).Rep (DirectedPowerBounds.shift (upperMid a) p) := by
  rw [r45_shift_centered]
  cases a
  · exact hc.centered 1 480 151 480 (by norm_num) (by norm_num [upperMid,left,right])
      (by norm_num [upperMid,left,right])
  · exact hc.centered 1 160 93 160 (by norm_num) (by norm_num [upperMid,left,right])
      (by norm_num [upperMid,left,right])

private theorem r45_rep_HShifted :
    ((r45_PHS .varying).center 1 6 1 6).Rep upperHShifted := by
  rw [upperHShifted,r45_shift_centered]
  exact (r45_rep_PH .varying).centered 1 6 1 6 (by norm_num) (by norm_num [L]) (by norm_num [L])

end r45Certificates

theorem upper_centered_domain (a : Upper) {z : ℝ}
    (hz : z∈Set.Icc (left a:ℝ) (right a:ℝ)) :
    |z-(upperMid a:ℝ)|≤(upperRadius a:ℝ) := by
  rw [abs_le]
  norm_num [upperMid,upperRadius]
  constructor <;> linarith [hz.1,hz.2]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem upper_mass_identity (a : Upper) (i : Fin 5) :
    upperMassCentered a i=C ((upperMassCentered a i).coeff 0)+
      tail (upperMassCentered a i) 1 6 := by
  have hc := r45_rep_shift (r45_rep_mass a i) a
  have hs : (r45_center (r45_massS a i) a).s≠0 := by
    cases a <;> fin_cases i <;> decide +kernel
  have hl : (r45_center (r45_massS a i) a).l.length≤7 := by
    cases a <;> fin_cases i <;> decide +kernel
  exact r45_eq_tail ((hc.natDegree_le hs).trans (by omega))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem upper_mass_reserve (a : Upper) (i : Fin 5) :
    (17/25:ℚ)<(upperMassCentered a i).coeff 0-
      PowerTailBounds.norm (upperMassCentered a i) 1 6 (upperRadius a) := by
  have hc := r45_rep_shift (r45_rep_mass a i) a
  have hs : (r45_center (r45_massS a i) a).s≠0 := by
    cases a <;> fin_cases i <;> decide +kernel
  cases a
  · exact r45_reserve (rn:=71) (rd:=480) (Rn:=17) (Rd:=25) hc hs
      (by norm_num [upperRadius,left,right]) (by norm_num) (by norm_num) (by norm_num)
      (by fin_cases i <;> decide +kernel)
  · exact r45_reserve (rn:=19) (rd:=160) (Rn:=17) (Rd:=25) hc hs
      (by norm_num [upperRadius,left,right]) (by norm_num) (by norm_num) (by norm_num)
      (by fin_cases i <;> decide +kernel)

theorem upper_mass_lower (a : Upper) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc (left a:ℝ) (right a:ℝ)) :
    (17/25:ℝ)<aeval z (upperMass a i) := by
  have hb := DirectedPowerBounds.constant_lower (upper_mass_identity a i)
    (upper_centered_domain a hz)
  have hr : (((17/25:ℚ)):ℝ)<(((upperMassCentered a i).coeff 0-
      PowerTailBounds.norm (upperMassCentered a i) 1 6 (upperRadius a):ℚ):ℝ) :=
    Rat.cast_lt.mpr (upper_mass_reserve a i)
  push_cast at hr
  have he : aeval (z-(upperMid a:ℝ)) (upperMassCentered a i)=
      aeval z (upperMass a i) := by simp [upperMassCentered]
  rw [he] at hb
  exact hr.trans_le hb

theorem upper_masses_positive (a : Upper) {z : ℝ}
    (hz : z∈Set.Icc (left a:ℝ) (right a:ℝ)) :
    0<aeval z (upperRk a) ∧ 0<aeval z (upperRm a) ∧
      0<aeval z (upperRc a) ∧ 0<aeval z (upperRHminus a) ∧
      0<aeval z (upperRBminus a) := by
  have h0 := upper_mass_lower a 0 hz
  have h1 := upper_mass_lower a 1 hz
  have h2 := upper_mass_lower a 2 hz
  have h3 := upper_mass_lower a 3 hz
  have h4 := upper_mass_lower a 4 hz
  norm_num [upperMass] at h0 h1 h2 h3 h4
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem upper_H_shifted_identity :
    upperHShifted=C (upperHShifted.coeff 0)+C (upperHShifted.coeff 1)*X+
      C (upperHShifted.coeff 2)*X^2+tail upperHShifted 3 31 := by
  have hc := r45_rep_HShifted
  exact r45_eq_quad_tail ((hc.natDegree_le (by decide +kernel)).trans (by decide +kernel))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem upper_H_shifted_reserve :
    (77/50000:ℚ)<upperHShifted.coeff 0 ∧
      (109/1000:ℚ)<upperHShifted.coeff 1 ∧
      (77/100:ℚ)<upperHShifted.coeff 2-
        DirectedPowerBounds.negativeNorm upperHShifted 3 31 (71/240) := by
  have hc := r45_rep_HShifted
  have hs : ((r45_PHS .varying).center 1 6 1 6).s≠0 := by decide +kernel
  exact ⟨r45_coeff_gt hc hs 0 (Rn:=77) (Rd:=50000) (by norm_num) (by norm_num)
      (by decide +kernel),
    r45_coeff_gt hc hs 1 (Rn:=109) (Rd:=1000) (by norm_num) (by norm_num) (by decide +kernel),
    r45_quad_reserve hc hs (rn:=71) (rd:=240) (Rn:=77) (Rd:=100) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel)⟩

theorem upperPH_varying_positive {z : ℝ}
    (hz : z∈Set.Icc (left .varying:ℝ) (right .varying:ℝ)) :
    0<aeval z (upperPH .varying) := by
  have hx : z-1/6∈Set.Icc 0 ((71/240:ℚ):ℝ) := by
    norm_num [left,right] at hz ⊢
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hb := DirectedPowerBounds.quadratic_lower upper_H_shifted_identity hx
  have h0 : (0:ℝ)<(upperHShifted.coeff 0:ℝ) := by
    exact_mod_cast lt_trans (by norm_num : (0:ℚ)<77/50000) upper_H_shifted_reserve.1
  have h1 : (0:ℝ)≤(upperHShifted.coeff 1:ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : (0:ℚ)<109/1000)
      upper_H_shifted_reserve.2.1).le
  have h2 : (0:ℝ)≤(upperHShifted.coeff 2:ℝ)-
      (DirectedPowerBounds.negativeNorm upperHShifted 3 31 (71/240):ℝ) := by
    have hh := (lt_trans (by norm_num : (0:ℚ)<77/100) upper_H_shifted_reserve.2.2).le
    have hc := Rat.cast_le (K:=ℝ) |>.mpr hh
    push_cast at hc
    exact hc
  have he : aeval (z-1/6) upperHShifted=aeval z (upperPH .varying) := by
    simp [upperHShifted,L]
  rw [he] at hb
  have hl := mul_nonneg h1 hx.1
  have hq := mul_nonneg h2 (sq_nonneg (z-1/6))
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem upper_B_centered_identity (a : Upper) :
    upperBCentered a=C ((upperBCentered a).coeff 0)+tail (upperBCentered a) 1 29 := by
  have hc := r45_rep_shift (r45_rep_PB a) a
  have hs : (r45_center (r45_PBS a) a).s≠0 := by cases a <;> decide +kernel
  have hl : (r45_center (r45_PBS a) a).l.length≤30 := by cases a <;> decide +kernel
  exact r45_eq_tail ((hc.natDegree_le hs).trans (by omega))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem upper_B_centered_reserve (a : Upper) :
    (3/100:ℚ)<(upperBCentered a).coeff 0-
      PowerTailBounds.norm (upperBCentered a) 1 29 (upperRadius a) := by
  have hc := r45_rep_shift (r45_rep_PB a) a
  have hs : (r45_center (r45_PBS a) a).s≠0 := by cases a <;> decide +kernel
  cases a
  · exact r45_reserve (rn:=71) (rd:=480) (Rn:=3) (Rd:=100) hc hs
      (by norm_num [upperRadius,left,right]) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel)
  · exact r45_reserve (rn:=19) (rd:=160) (Rn:=3) (Rd:=100) hc hs
      (by norm_num [upperRadius,left,right]) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel)

theorem upperPB_positive (a : Upper) {z : ℝ}
    (hz : z∈Set.Icc (left a:ℝ) (right a:ℝ)) :
    0<aeval z (upperPB a) := by
  have hb := DirectedPowerBounds.constant_lower (upper_B_centered_identity a)
    (upper_centered_domain a hz)
  have hr : (((3/100:ℚ)):ℝ)<(((upperBCentered a).coeff 0-
      PowerTailBounds.norm (upperBCentered a) 1 29 (upperRadius a):ℚ):ℝ) :=
    Rat.cast_lt.mpr (upper_B_centered_reserve a)
  push_cast at hr
  have he : aeval (z-(upperMid a:ℝ)) (upperBCentered a)=aeval z (upperPB a) := by
    simp [upperBCentered]
  rw [he] at hb
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem upper_H_clamped_identity :
    upperHClampedCentered=C (upperHClampedCentered.coeff 0)+
      tail upperHClampedCentered 1 29 := by
  have hc := r45_rep_shift (r45_rep_PH .clamped) .clamped
  have hs : (r45_center (r45_PHS .clamped) .clamped).s≠0 := by decide +kernel
  have hl : (r45_center (r45_PHS .clamped) .clamped).l.length≤30 := by decide +kernel
  exact r45_eq_tail ((hc.natDegree_le hs).trans (by omega))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem upper_H_clamped_reserve :
    (1/10:ℚ)<upperHClampedCentered.coeff 0-
      PowerTailBounds.norm upperHClampedCentered 1 29 (upperRadius .clamped) := by
  have hc := r45_rep_shift (r45_rep_PH .clamped) .clamped
  have hs : (r45_center (r45_PHS .clamped) .clamped).s≠0 := by decide +kernel
  exact r45_reserve (rn:=19) (rd:=160) (Rn:=1) (Rd:=10) hc hs
    (by norm_num [upperRadius,left,right]) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

theorem upperPH_clamped_positive {z : ℝ}
    (hz : z∈Set.Icc (left .clamped:ℝ) (right .clamped:ℝ)) :
    0<aeval z (upperPH .clamped) := by
  have hb := DirectedPowerBounds.constant_lower upper_H_clamped_identity
    (upper_centered_domain .clamped hz)
  have hr : (((1/10:ℚ)):ℝ)<((upperHClampedCentered.coeff 0-
      PowerTailBounds.norm upperHClampedCentered 1 29 (upperRadius .clamped):ℚ):ℝ) :=
    Rat.cast_lt.mpr upper_H_clamped_reserve
  push_cast at hr
  have he : aeval (z-(upperMid .clamped:ℝ)) upperHClampedCentered=
      aeval z (upperPH .clamped) := by simp [upperHClampedCentered]
  rw [he] at hb
  linarith

theorem upperPH_positive (a : Upper) {z : ℝ}
    (hz : z∈Set.Icc (left a:ℝ) (right a:ℝ)) :
    0<aeval z (upperPH a) := by
  cases a
  · exact upperPH_varying_positive hz
  · exact upperPH_clamped_positive hz

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD.Certificate
