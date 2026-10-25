module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2PolynomialData
public import SquaresInCircles.Eight.Arithmetic.KroneckerPolynomials

/-!
# Eight squares: whole-interval positivity of the fourteen negative-A / TD2 numerators

The two tight low numerators keep their
displayed leading terms, the mixed numerator keeps its Chebyshev
quadratic, and the three endpoint quotients keep their positive constant.
Every remaining bound is the stated whole-interval coefficient sum.
The rational identities are proof terms, not executed certificates.

The kernel evaluates integer coefficient lists that mirror the polynomials.  Sums are divided
by the gcd of the list and its scale, which keeps the integers short; long products and the
affine changes of variable are one integer product or evaluation read back in a power-of-two
base by masks and shifts (`KroneckerPolynomials`).  Each bound is one kernel evaluation of
integer inequalities.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
open Polynomial WholeIntervalPolynomial ChebyshevLeadingBounds
open PositiveTD.Certificate (h)
open WholeIntervalPolynomial.Certificate (Scaled lowerOn_eq_of_rep toPoly chebList lowerZ scale_pos)
open PositiveTD.Certificate (S5 S9 S11 C4 C10 C12 num3 num4 etaQ Rbar cbar sigmabar)

/-! ### The numerators as scaled integer coefficient lists

Each polynomial of the companion is mirrored by a `Scaled` list built with the same
operations, and `Scaled.Rep` proves that the list represents it.  The kernel evaluates
only these integer lists. -/

private def r42S5 : Scaled :=
  (Scaled.var.subN ((Scaled.const (1/6)).mul (Scaled.mono 3))).addN
    ((Scaled.const (1/120)).mul (Scaled.mono 5))
private theorem r42S5_rep : r42S5.Rep S5 :=
  (Scaled.rep_var.subN ((Scaled.rep_const _).mul (Scaled.rep_mono 3))).addN
    ((Scaled.rep_const _).mul (Scaled.rep_mono 5))
private def r42S9 : Scaled :=
  (r42S5.subN ((Scaled.const (1/5040)).mul (Scaled.mono 7))).addN
    ((Scaled.const (1/362880)).mul (Scaled.mono 9))
private theorem r42S9_rep : r42S9.Rep S9 :=
  (r42S5_rep.subN ((Scaled.rep_const _).mul (Scaled.rep_mono 7))).addN
    ((Scaled.rep_const _).mul (Scaled.rep_mono 9))
private def r42S11 : Scaled := r42S9.subN ((Scaled.const (1/39916800)).mul (Scaled.mono 11))
private theorem r42S11_rep : r42S11.Rep S11 :=
  r42S9_rep.subN ((Scaled.rep_const _).mul (Scaled.rep_mono 11))
private def r42C4 : Scaled :=
  ((Scaled.ofNat 1).subN ((Scaled.const (1/2)).mul (Scaled.mono 2))).addN
    ((Scaled.const (1/24)).mul (Scaled.mono 4))
private theorem r42C4_rep : r42C4.Rep C4 :=
  (Scaled.rep_one.subN ((Scaled.rep_const _).mul (Scaled.rep_mono 2))).addN
    ((Scaled.rep_const _).mul (Scaled.rep_mono 4))
private def r42C10 : Scaled :=
  ((r42C4.subN ((Scaled.const (1/720)).mul (Scaled.mono 6))).addN
    ((Scaled.const (1/40320)).mul (Scaled.mono 8))).subN
    ((Scaled.const (1/3628800)).mul (Scaled.mono 10))
private theorem r42C10_rep : r42C10.Rep C10 :=
  ((r42C4_rep.subN ((Scaled.rep_const _).mul (Scaled.rep_mono 6))).addN
    ((Scaled.rep_const _).mul (Scaled.rep_mono 8))).subN
    ((Scaled.rep_const _).mul (Scaled.rep_mono 10))
private def r42C12 : Scaled := r42C10.addN ((Scaled.const (1/479001600)).mul (Scaled.mono 12))
private theorem r42C12_rep : r42C12.Rep C12 :=
  r42C10_rep.addN ((Scaled.rep_const _).mul (Scaled.rep_mono 12))

private theorem r42num3_rep {A P0 P1 P2 r0 r1 r2 : Scaled} {a p0 p1 p2 s0 s1 s2 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) :
    (Scaled.num3 Rbar A P0 P1 P2 r0 r1 r2).Rep (num3 a p0 p1 p2 s0 s1 s2) :=
  hA.num3 Rbar h0 h1 h2 g0 g1 g2
private theorem r42num4_rep {A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled}
    {a p0 p1 p2 p3 s0 s1 s2 s3 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2) (h3 : P3.Rep p3)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) (g3 : r3.Rep s3) :
    (Scaled.num4 Rbar A P0 P1 P2 P3 r0 r1 r2 r3).Rep (num4 a p0 p1 p2 p3 s0 s1 s2 s3) :=
  hA.num4 Rbar h0 h1 h2 h3 g0 g1 g2 g3

private def r42t : Family → Scaled
  | .low => (Scaled.const split).subN Scaled.var
  | .high => Scaled.var.subN (Scaled.const split)
private theorem r42t_rep : ∀ f, (r42t f).Rep (t f)
  | .low => (Scaled.rep_const _).subN Scaled.rep_var
  | .high => Scaled.rep_var.subN (Scaled.rep_const _)

private def r42k : Family → Scaled
  | .low => (((Scaled.const (169/250)).subN ((Scaled.const (1/5)).mul (r42t .low))).addN
      ((Scaled.const (19/5)).mul ((r42t .low).pow 2))).subN
      ((Scaled.const 5).mul ((r42t .low).pow 3))
  | .high => (((Scaled.const (169/250)).addN ((Scaled.const (1/5)).mul (r42t .high))).addN
      ((Scaled.const (9/10)).mul ((r42t .high).pow 2))).subN
      ((Scaled.const (13/10)).mul ((r42t .high).pow 3))
private theorem r42k_rep : ∀ f, (r42k f).Rep (k f)
  | .low => (((Scaled.rep_const _).subN ((Scaled.rep_const _).mul (r42t_rep .low))).addN
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 2))).subN
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 3))
  | .high => (((Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r42t_rep .high))).addN
      ((Scaled.rep_const _).mul ((r42t_rep .high).pow 2))).subN
      ((Scaled.rep_const _).mul ((r42t_rep .high).pow 3))

private def r42l : Family → Scaled
  | .low => ((((Scaled.const (41/40)).subN ((Scaled.const (1/4)).mul (r42t .low))).addN
      ((Scaled.const (29/2)).mul ((r42t .low).pow 2))).addN
      ((Scaled.const (55/4)).mul ((r42t .low).pow 3))).subN
      ((Scaled.const 200).mul ((r42t .low).pow 4))
  | .high => ((Scaled.const (41/40)).addN ((Scaled.const (11/50)).mul (r42t .high))).subN
      ((Scaled.const (3/10)).mul ((r42t .high).pow 2))
private theorem r42l_rep : ∀ f, (r42l f).Rep (l f)
  | .low => ((((Scaled.rep_const _).subN ((Scaled.rep_const _).mul (r42t_rep .low))).addN
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 2))).addN
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 3))).subN
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 4))
  | .high => ((Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r42t_rep .high))).subN
      ((Scaled.rep_const _).mul ((r42t_rep .high).pow 2))

private def r42c : Family → Scaled
  | .low => ((Scaled.ofNat 1).addN ((Scaled.const (11/10)).mul (r42t .low))).addN
      ((Scaled.const 17).mul ((r42t .low).pow 2))
  | .high => ((Scaled.ofNat 1).subN ((Scaled.const (7/10)).mul (r42t .high))).addN
      ((Scaled.const (22/25)).mul ((r42t .high).pow 2))
private theorem r42c_rep : ∀ f, (r42c f).Rep (c f)
  | .low => (Scaled.rep_one.addN ((Scaled.rep_const _).mul (r42t_rep .low))).addN
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 2))
  | .high => (Scaled.rep_one.subN ((Scaled.rep_const _).mul (r42t_rep .high))).addN
      ((Scaled.rep_const _).mul ((r42t_rep .high).pow 2))

private def r42mLo (f : Family) : Scaled := (r42c f).mul (r42C10.addN ((Scaled.const etaQ).mul r42S11))
private theorem r42mLo_rep (f : Family) : (r42mLo f).Rep (mLo f) :=
  (r42c_rep f).mul (r42C10_rep.addN ((Scaled.rep_const _).mul r42S11_rep))
private def r42mHi (f : Family) : Scaled := (r42c f).mul (r42C12.addN ((Scaled.const etaQ).mul r42S9))
private theorem r42mHi_rep (f : Family) : (r42mHi f).Rep (mHi f) :=
  (r42c_rep f).mul (r42C12_rep.addN ((Scaled.rep_const _).mul r42S9_rep))
private def r42mu (f : Family) : Scaled := (r42c f).mul (r42C4.addN ((Scaled.const etaQ).mul r42S5))
private theorem r42mu_rep (f : Family) : (r42mu f).Rep (mu f) :=
  (r42c_rep f).mul (r42C4_rep.addN ((Scaled.rep_const _).mul r42S5_rep))
private def r42widthLo : Scaled := (Scaled.const (1/2)).mul (((Scaled.ofNat 1).addN r42C10).addN r42S11)
private theorem r42widthLo_rep : r42widthLo.Rep widthLo :=
  (Scaled.rep_const _).mul ((Scaled.rep_one.addN r42C10_rep).addN r42S11_rep)

private def r42elemBase (f : Family) : Scaled :=
  ((((((Scaled.const 2).mul (r42k f)).addN ((Scaled.const 3).mul (r42l f))).addN
    ((Scaled.const (3/2)).mul (r42mLo f))).addN ((r42c f).mul r42widthLo)).addN
    (Scaled.const (5/2))).subN (((r42c f).mul (Scaled.const sigmabar)).mul r42S9)
private theorem r42elemBase_rep (f : Family) : (r42elemBase f).Rep
    (C 2*k f+C 3*l f+C (3/2)*mLo f+c f*widthLo+C (5/2)-c f*C sigmabar*S9) :=
  ((((((Scaled.rep_const _).mul (r42k_rep f)).addN ((Scaled.rep_const _).mul (r42l_rep f))).addN
    ((Scaled.rep_const _).mul (r42mLo_rep f))).addN ((r42c_rep f).mul r42widthLo_rep)).addN
    (Scaled.rep_const _)).subN (((r42c_rep f).mul (Scaled.rep_const _)).mul r42S9_rep)
private def r42elem : Family → Scaled
  | .low => (r42elemBase .low).addN (((Scaled.ofNat 1).addN (r42c .low)).neg.mul (Scaled.const cbar))
  | .high => (r42elemBase .high).addN ((Scaled.const (1/2)).mul ((Scaled.ofNat 1).addN (r42c .high)))
private theorem r42elem_rep : ∀ f, (r42elem f).Rep (elementary f)
  | .low => by
    rw [elementary,ite_eq_left_of_eq_true _ _ (eq_self _)]
    exact (r42elemBase_rep .low).addN ((Scaled.rep_one.addN (r42c_rep .low)).neg.mul (Scaled.rep_const _))
  | .high => by
    rw [elementary,ite_eq_right_of_eq_false _ _ (by decide)]
    exact (r42elemBase_rep .high).addN ((Scaled.rep_const _).mul (Scaled.rep_one.addN (r42c_rep .high)))

private def r42PH (f : Family) : Scaled := (Scaled.ofNat 1).addN ((r42k f).pow 2)
private theorem r42PH_rep (f : Family) : (r42PH f).Rep (PH f) := Scaled.rep_one.addN ((r42k_rep f).pow 2)
private def r42PG (f : Family) : Scaled := ((r42k f).pow 2).addN ((r42l f).pow 2)
private theorem r42PG_rep (f : Family) : (r42PG f).Rep (PG f) := ((r42k_rep f).pow 2).addN ((r42l_rep f).pow 2)
private def r42PB (f : Family) : Scaled := (r42mHi f).ksq.addN ((r42l f).pow 2)
private theorem r42PB_rep (f : Family) : (r42PB f).Rep (PB f) := (r42mHi_rep f).ksq.addN ((r42l_rep f).pow 2)
private def r42PD (f : Family) : Scaled := (Scaled.ofNat 1).addN ((r42c f).pow 2)
private theorem r42PD_rep (f : Family) : (r42PD f).Rep (PD f) := Scaled.rep_one.addN ((r42c_rep f).pow 2)
private def r42RH (f : Family) : Scaled := (Scaled.const (83/100)).addN ((Scaled.const (279/500)).mul (r42k f))
private theorem r42RH_rep (f : Family) : (r42RH f).Rep (RH f) :=
  (Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r42k_rep f))
private def r42RG (f : Family) : Scaled :=
  ((Scaled.const (11/20)).mul (r42k f)).addN ((Scaled.const (167/200)).mul (r42l f))
private theorem r42RG_rep (f : Family) : (r42RG f).Rep (RG f) :=
  ((Scaled.rep_const _).mul (r42k_rep f)).addN ((Scaled.rep_const _).mul (r42l_rep f))
private def r42RB (f : Family) : Scaled :=
  ((Scaled.const (29/40)).mul (r42mu f)).addN ((Scaled.const (689/1000)).mul (r42l f))
private theorem r42RB_rep (f : Family) : (r42RB f).Rep (RB f) :=
  ((Scaled.rep_const _).mul (r42mu_rep f)).addN ((Scaled.rep_const _).mul (r42l_rep f))
private def r42RD (f : Family) : Scaled := (Scaled.const (7071/10000)).mul ((Scaled.ofNat 1).addN (r42c f))
private theorem r42RD_rep (f : Family) : (r42RD f).Rep (RD f) :=
  (Scaled.rep_const _).mul (Scaled.rep_one.addN (r42c_rep f))

private def r42AZ (f : Family) : Scaled :=
  ((r42C10.kmul ((r42elem f).subN (r42l f))).addN (r42l f)).addN
    (((Scaled.const (13/12)).mul (r42l f)).mul r42S11)
private theorem r42AZ_rep (f : Family) : (r42AZ f).Rep (AZ f) :=
  ((r42C10_rep.kmul ((r42elem_rep f).subN (r42l_rep f))).addN (r42l_rep f)).addN
    (((Scaled.rep_const _).mul (r42l_rep f)).mul r42S11_rep)

private def r42PHminus (f : Family) : Scaled :=
  (r42PH f).subN (((Scaled.const 2).mul (r42k f)).mul r42S11)
private theorem r42PHminus_rep (f : Family) : (r42PHminus f).Rep (PHminus f) :=
  (r42PH_rep f).subN (((Scaled.rep_const _).mul (r42k_rep f)).mul r42S11_rep)
private def r42PGminus (f : Family) : Scaled :=
  (r42PG f).subN ((((Scaled.const 2).mul (r42k f)).mul (r42l f)).mul r42S11)
private theorem r42PGminus_rep (f : Family) : (r42PGminus f).Rep (PGminus f) :=
  (r42PG_rep f).subN ((((Scaled.rep_const _).mul (r42k_rep f)).mul (r42l_rep f)).mul r42S11_rep)
private def r42PBminus (f : Family) : Scaled :=
  (r42PB f).subN ((((Scaled.const 2).mul (r42l f)).mul (r42mLo f)).kmul r42S11)
private theorem r42PBminus_rep (f : Family) : (r42PBminus f).Rep (PBminus f) :=
  (r42PB_rep f).subN ((((Scaled.rep_const _).mul (r42l_rep f)).mul (r42mLo_rep f)).kmul r42S11_rep)
private def r42RHminus (f : Family) : Scaled :=
  ((Scaled.const (179/200)).mul r42C4).addN ((Scaled.const (223/500)).mul ((r42k f).subN r42S5))
private theorem r42RHminus_rep (f : Family) : (r42RHminus f).Rep (RHminus f) :=
  ((Scaled.rep_const _).mul r42C4_rep).addN ((Scaled.rep_const _).mul ((r42k_rep f).subN r42S5_rep))
private def r42RGminus (f : Family) : Scaled :=
  (((Scaled.const (9/10)).mul (r42l f)).mul r42C4).addN
    ((Scaled.const (109/250)).mul ((r42k f).subN ((r42l f).mul r42S5)))
private theorem r42RGminus_rep (f : Family) : (r42RGminus f).Rep (RGminus f) :=
  (((Scaled.rep_const _).mul (r42l_rep f)).mul r42C4_rep).addN
    ((Scaled.rep_const _).mul ((r42k_rep f).subN ((r42l_rep f).mul r42S5_rep)))
private def r42RBminus (f : Family) : Scaled :=
  (((Scaled.const (94/125)).mul (r42l f)).mul r42C4).addN
    ((Scaled.const (33/50)).mul ((r42mu f).subN ((r42l f).mul r42S5)))
private theorem r42RBminus_rep (f : Family) : (r42RBminus f).Rep (RBminus f) :=
  (((Scaled.rep_const _).mul (r42l_rep f)).mul r42C4_rep).addN
    ((Scaled.rep_const _).mul ((r42mu_rep f).subN ((r42l_rep f).mul r42S5_rep)))
private def r42qStar (f : Family) : Scaled :=
  (r42l f).addN ((Scaled.const (3/100)).mul ((Scaled.const h).subN Scaled.var))
private theorem r42qStar_rep (f : Family) : (r42qStar f).Rep (qStar f) :=
  (r42l_rep f).addN ((Scaled.rep_const _).mul ((Scaled.rep_const _).subN Scaled.rep_var))

/-! Constants given by evaluating a represented polynomial at a rational point. -/

private theorem r42_rep_eval {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s : ℤ)
    {a : ℚ} (hden : den≠0) (ha : a=num*s/den) : (S.kcenter num den s 0).Rep (C (p.eval a)) := by
  have hc := hp.kcentered num den s 0 (a:=a) (b:=a) hden (by rw [← ha]; ring) (by simp)
  have he : WholeIntervalPolynomial.centered a a p=C (p.eval a) := by
    rw [WholeIntervalPolynomial.centered,affine,sub_self,zero_div,map_zero,zero_mul,add_zero,
      add_self_div_two,comp_C]
  rwa [he] at hc
private theorem r42_rep_Cadd {S T : Scaled} {a b : ℚ} (hS : S.Rep (C a)) (hT : T.Rep (C b)) :
    (S.addN T).Rep (C (a+b)) := by rw [map_add]; exact hS.addN hT
private theorem r42_rep_Csub {S T : Scaled} {a b : ℚ} (hS : S.Rep (C a)) (hT : T.Rep (C b)) :
    (S.subN T).Rep (C (a-b)) := by rw [map_sub]; exact hS.subN hT
private theorem r42_rep_Cmul {S T : Scaled} {a b : ℚ} (hS : S.Rep (C a)) (hT : T.Rep (C b)) :
    (S.mul T).Rep (C (a*b)) := by rw [map_mul]; exact hS.mul hT
private theorem r42_rep_Cpow {S : Scaled} {a : ℚ} (hS : S.Rep (C a)) (n : ℕ) :
    (S.pow n).Rep (C (a^n)) := by rw [map_pow]; exact hS.pow n

/-- A represented constant, cut down to its constant entry. -/
private def r42head (S : Scaled) : Scaled := ⟨[S.l.getD 0 0],S.s⟩
private theorem r42head_rep {S : Scaled} {c : ℚ} (hS : S.Rep (C c)) : (r42head S).Rep (C c) := by
  unfold Scaled.Rep at *
  have h0 := congrArg (fun q => q.coeff 0) hS
  simp only [Certificate.coeff_toPoly,coeff_C_mul,coeff_C_zero] at h0
  simp only [r42head,Certificate.toPoly,mul_zero,add_zero,h0,map_mul]

private def r42ch : Scaled := r42head (r42C10.kcenter 7 10 1 0)
private theorem r42ch_rep : r42ch.Rep (C PositiveTD.Certificate.ch) :=
  r42head_rep <| r42_rep_eval r42C10_rep 7 10 1 (by norm_num) (by norm_num [h])
private def r42Ch : Scaled := r42head (r42C12.kcenter 7 10 1 0)
private theorem r42Ch_rep : r42Ch.Rep (C PositiveTD.Certificate.Ch) :=
  r42head_rep <| r42_rep_eval r42C12_rep 7 10 1 (by norm_num) (by norm_num [h])
private def r42sh : Scaled := r42head (r42S11.kcenter 7 10 1 0)
private theorem r42sh_rep : r42sh.Rep (C PositiveTD.Certificate.sh) :=
  r42head_rep <| r42_rep_eval r42S11_rep 7 10 1 (by norm_num) (by norm_num [h])

/-! The fourteen numerators. -/

private def r42NH : Family → Scaled
  | .low => Scaled.num3 Rbar (((r42elem .low).addN r42C10).subN (Scaled.ofNat 1))
      (r42PG .low) (r42PB .low) (r42PHminus .low) (r42RG .low) (r42RB .low) (r42RHminus .low)
  | .high => Scaled.num4 Rbar (((r42elem .high).addN r42C10).subN (Scaled.ofNat 1))
      (r42PG .high) (r42PB .high) (r42PHminus .high) (r42PD .high)
      (r42RG .high) (r42RB .high) (r42RHminus .high) (r42RD .high)
private theorem r42NH_rep : ∀ f, (r42NH f).Rep (NH f)
  | .low => by
    rw [NH,ite_eq_left_of_eq_true _ _ (eq_self _)]
    exact r42num3_rep (((r42elem_rep .low).addN r42C10_rep).subN Scaled.rep_one)
      (r42PG_rep .low) (r42PB_rep .low) (r42PHminus_rep .low) (r42RG_rep .low) (r42RB_rep .low)
      (r42RHminus_rep .low)
  | .high => by
    rw [NH,ite_eq_right_of_eq_false _ _ (by decide)]
    exact r42num4_rep (((r42elem_rep .high).addN r42C10_rep).subN Scaled.rep_one)
      (r42PG_rep .high) (r42PB_rep .high) (r42PHminus_rep .high) (r42PD_rep .high)
      (r42RG_rep .high) (r42RB_rep .high) (r42RHminus_rep .high) (r42RD_rep .high)

private def r42NG : Scaled :=
  Scaled.num4 Rbar ((r42elem .high).addN ((r42l .high).mul (r42C10.subN (Scaled.ofNat 1))))
    (r42PH .high) (r42PB .high) (r42PGminus .high) (r42PD .high)
    (r42RH .high) (r42RB .high) (r42RGminus .high) (r42RD .high)
private theorem r42NG_rep : r42NG.Rep NG :=
  r42num4_rep ((r42elem_rep .high).addN ((r42l_rep .high).mul (r42C10_rep.subN Scaled.rep_one)))
    (r42PH_rep .high) (r42PB_rep .high) (r42PGminus_rep .high) (r42PD_rep .high)
    (r42RH_rep .high) (r42RB_rep .high) (r42RGminus_rep .high) (r42RD_rep .high)

private def r42NB : Scaled :=
  Scaled.num4 Rbar ((r42elem .high).addN ((r42qStar .high).mul (r42C10.subN (Scaled.ofNat 1))))
    (r42PH .high) (r42PG .high) (r42PBminus .high) (r42PD .high)
    (r42RH .high) (r42RG .high) (r42RBminus .high) (r42RD .high)
private theorem r42NB_rep : r42NB.Rep NB :=
  r42num4_rep ((r42elem_rep .high).addN ((r42qStar_rep .high).mul (r42C10_rep.subN Scaled.rep_one)))
    (r42PH_rep .high) (r42PG_rep .high) (r42PBminus_rep .high) (r42PD_rep .high)
    (r42RH_rep .high) (r42RG_rep .high) (r42RBminus_rep .high) (r42RD_rep .high)

private def r42GAP0 (f : Family) : Scaled := r42C12.ksq.kmul (r42PH f)
private def r42GAP1 (f : Family) : Scaled := ((r42l f).pow 2).addN (((r42k f).pow 2).kmul r42C12.ksq)
private def r42GAP2 (f : Family) : Scaled := r42C12.ksq.kmul (r42PB f)
private def r42GAP3 (f : Family) : Scaled := r42C12.ksq.kmul (r42PD f)
private def r42GAR0 (f : Family) : Scaled := r42C4.mul (r42RH f)
private def r42GAR1 (f : Family) : Scaled :=
  ((Scaled.const (21/25)).mul (r42l f)).addN (((Scaled.const (543/1000)).mul (r42k f)).mul r42C4)
private def r42GAR2 (f : Family) : Scaled := r42C4.mul (r42RB f)
private def r42GAR3 (f : Family) : Scaled := r42C4.mul (r42RD f)
private theorem r42GAP0_rep (f : Family) : (r42GAP0 f).Rep (equalGAP f 0) :=
  r42C12_rep.ksq.kmul (r42PH_rep f)
private theorem r42GAP1_rep (f : Family) : (r42GAP1 f).Rep (equalGAP f 1) :=
  ((r42l_rep f).pow 2).addN (((r42k_rep f).pow 2).kmul r42C12_rep.ksq)
private theorem r42GAP2_rep (f : Family) : (r42GAP2 f).Rep (equalGAP f 2) :=
  r42C12_rep.ksq.kmul (r42PB_rep f)
private theorem r42GAP3_rep (f : Family) : (r42GAP3 f).Rep (equalGAP f 3) :=
  r42C12_rep.ksq.kmul (r42PD_rep f)
private theorem r42GAR0_rep (f : Family) : (r42GAR0 f).Rep (equalGAR f 0) := r42C4_rep.mul (r42RH_rep f)
private theorem r42GAR1_rep (f : Family) : (r42GAR1 f).Rep (equalGAR f 1) :=
  ((Scaled.rep_const _).mul (r42l_rep f)).addN (((Scaled.rep_const _).mul (r42k_rep f)).mul r42C4_rep)
private theorem r42GAR2_rep (f : Family) : (r42GAR2 f).Rep (equalGAR f 2) := r42C4_rep.mul (r42RB_rep f)
private theorem r42GAR3_rep (f : Family) : (r42GAR3 f).Rep (equalGAR f 3) := r42C4_rep.mul (r42RD_rep f)

private def r42NZ : Family → Scaled
  | .low => Scaled.num3 Rbar (r42AZ .low) (r42GAP0 .low) (r42GAP1 .low) (r42GAP2 .low)
      (r42GAR0 .low) (r42GAR1 .low) (r42GAR2 .low)
  | .high => Scaled.num4 Rbar (r42AZ .high) (r42GAP0 .high) (r42GAP1 .high) (r42GAP2 .high) (r42GAP3 .high)
      (r42GAR0 .high) (r42GAR1 .high) (r42GAR2 .high) (r42GAR3 .high)
private theorem r42NZ_rep : ∀ f, (r42NZ f).Rep (NZ f)
  | .low => by
    rw [NZ,ite_eq_left_of_eq_true _ _ (eq_self _)]
    exact r42num3_rep (r42AZ_rep .low) (r42GAP0_rep .low) (r42GAP1_rep .low) (r42GAP2_rep .low)
      (r42GAR0_rep .low) (r42GAR1_rep .low) (r42GAR2_rep .low)
  | .high => by
    rw [NZ,ite_eq_right_of_eq_false _ _ (by decide)]
    exact r42num4_rep (r42AZ_rep .high) (r42GAP0_rep .high) (r42GAP1_rep .high)
      (r42GAP2_rep .high) (r42GAP3_rep .high)
      (r42GAR0_rep .high) (r42GAR1_rep .high) (r42GAR2_rep .high) (r42GAR3_rep .high)

private def r42NZA : Scaled :=
  Scaled.num4 Rbar (r42AZ .high) (r42GAP0 .high) (r42C12.ksq.kmul (r42PG .high))
    (((r42l .high).pow 2).addN ((r42mHi .high).ksq.kmul r42C12.ksq)) (r42GAP3 .high)
    (r42GAR0 .high) (r42C4.mul (r42RG .high))
    (((Scaled.const (4/5)).mul (r42l .high)).addN (((Scaled.const (3/5)).mul (r42mu .high)).mul r42C4))
    (r42GAR3 .high)
private theorem r42NZA_rep : r42NZA.Rep NZA :=
  r42num4_rep (r42AZ_rep .high) (r42GAP0_rep .high) (r42C12_rep.ksq.kmul (r42PG_rep .high))
    (((r42l_rep .high).pow 2).addN ((r42mHi_rep .high).ksq.kmul r42C12_rep.ksq))
    (r42GAP3_rep .high) (r42GAR0_rep .high) (r42C4_rep.mul (r42RG_rep .high))
    (((Scaled.rep_const _).mul (r42l_rep .high)).addN
      (((Scaled.rep_const _).mul (r42mu_rep .high)).mul r42C4_rep))
    (r42GAR3_rep .high)

private def r42phiLo : Scaled :=
  ((r42ch.addN r42sh).mul r42C10).subN ((r42Ch.subN r42sh).mul r42S9)
private theorem r42phiLo_rep : r42phiLo.Rep phiLo :=
  ((r42_rep_Cadd r42ch_rep r42sh_rep).mul r42C10_rep).subN ((r42_rep_Csub r42Ch_rep r42sh_rep).mul r42S9_rep)
private def r42chm1 : Scaled := r42ch.subN (Scaled.const 1)
private theorem r42chm1_rep : r42chm1.Rep (C (PositiveTD.Certificate.ch-1)) :=
  r42_rep_Csub r42ch_rep (Scaled.rep_const 1)

private def r42NM : Scaled :=
  Scaled.num3 Rbar (((r42elem .low).addN ((r42k .low).mul (r42phiLo.subN (Scaled.ofNat 1)))).addN
      ((r42l .low).mul r42chm1))
    (r42PH .low) (r42PB .low) (r42PGminus .low) (r42RH .low) (r42RB .low) (r42RGminus .low)
private theorem r42NM_rep : r42NM.Rep NM :=
  r42num3_rep (((r42elem_rep .low).addN ((r42k_rep .low).mul (r42phiLo_rep.subN Scaled.rep_one))).addN
      ((r42l_rep .low).mul r42chm1_rep))
    (r42PH_rep .low) (r42PB_rep .low) (r42PGminus_rep .low) (r42RH_rep .low) (r42RB_rep .low)
    (r42RGminus_rep .low)

private def r42lowStar : Scaled :=
  (r42elem .low).subN (((Scaled.const (109/200)).mul ((r42mHi .low).addN
    ((Scaled.const (2/5)).mul Scaled.var))).mul ((Scaled.const h).subN Scaled.var))
private theorem r42lowStar_rep : r42lowStar.Rep lowStar :=
  (r42elem_rep .low).subN (((Scaled.rep_const _).mul ((r42mHi_rep .low).addN
    ((Scaled.rep_const _).mul Scaled.rep_var))).mul ((Scaled.rep_const _).subN Scaled.rep_var))
private def r42twosh : Scaled := (Scaled.const 2).mul r42sh
private theorem r42twosh_rep : r42twosh.Rep (C (2*PositiveTD.Certificate.sh)) :=
  r42_rep_Cmul (Scaled.rep_const 2) r42sh_rep
private def r42NSH : Scaled :=
  Scaled.num3 Rbar (r42lowStar.addN r42chm1) (r42PG .low) (r42PB .low)
    ((r42PH .low).subN (r42twosh.mul (r42k .low))) (r42RG .low) (r42RB .low)
    (Scaled.const (77/100))
private theorem r42NSH_rep : r42NSH.Rep NSH :=
  r42num3_rep (r42lowStar_rep.addN r42chm1_rep) (r42PG_rep .low) (r42PB_rep .low)
    ((r42PH_rep .low).subN (r42twosh_rep.mul (r42k_rep .low))) (r42RG_rep .low) (r42RB_rep .low)
    (Scaled.rep_const _)
private def r42NSG : Scaled :=
  Scaled.num3 Rbar (r42lowStar.addN ((r42l .low).mul r42chm1)) (r42PH .low) (r42PB .low)
    ((r42PG .low).subN ((r42twosh.mul (r42k .low)).mul (r42l .low))) (r42RH .low) (r42RB .low)
    ((Scaled.const (77/100)).mul (r42l .low))
private theorem r42NSG_rep : r42NSG.Rep NSG :=
  r42num3_rep (r42lowStar_rep.addN ((r42l_rep .low).mul r42chm1_rep)) (r42PH_rep .low) (r42PB_rep .low)
    ((r42PG_rep .low).subN ((r42twosh_rep.mul (r42k_rep .low)).mul (r42l_rep .low)))
    (r42RH_rep .low) (r42RB_rep .low) ((Scaled.rep_const _).mul (r42l_rep .low))

/-! The four angle cuts. -/

private def r42ang (e : Cut) (S : Scaled) : Scaled :=
  r42head (if cutAtG e then S.kcenter 1 4 1 0 else S.kcenter 19 50 1 0)
private theorem r42ang_rep (e : Cut) {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) :
    (r42ang e S).Rep (C (p.eval (cutAngle e))) := by
  apply r42head_rep
  rcases hb : cutAtG e with _|_ <;> simp only [cutAngle,hb,Bool.false_eq_true,↓reduceIte]
  · exact r42_rep_eval hp 19 50 1 (by norm_num) (by norm_num)
  · exact r42_rep_eval hp 1 4 1 (by norm_num) (by norm_num)

private def r42gl (e : Cut) : Scaled := r42ang e r42C10
private def r42gh (e : Cut) : Scaled := r42ang e r42C12
private def r42tl (e : Cut) : Scaled := r42ang e r42S11
private def r42th (e : Cut) : Scaled := r42ang e r42S9
private def r42ga (e : Cut) : Scaled := r42ang e r42C4
private def r42ta (e : Cut) : Scaled := r42ang e r42S5
private theorem r42gl_rep (e : Cut) : (r42gl e).Rep (C (gammaLo e)) := r42ang_rep e r42C10_rep
private theorem r42gh_rep (e : Cut) : (r42gh e).Rep (C (gammaHi e)) := r42ang_rep e r42C12_rep
private theorem r42tl_rep (e : Cut) : (r42tl e).Rep (C (tauLo e)) := r42ang_rep e r42S11_rep
private theorem r42th_rep (e : Cut) : (r42th e).Rep (C (tauHi e)) := r42ang_rep e r42S9_rep
private theorem r42ga_rep (e : Cut) : (r42ga e).Rep (C (gammaApprox e)) := r42ang_rep e r42C4_rep
private theorem r42ta_rep (e : Cut) : (r42ta e).Rep (C (tauApprox e)) := r42ang_rep e r42S5_rep

private def r42cosLo (e : Cut) : Scaled := ((r42gl e).mul r42C10).addN ((r42tl e).mul r42S11)
private theorem r42cosLo_rep (e : Cut) : (r42cosLo e).Rep (thetaCosLo e) :=
  ((r42gl_rep e).mul r42C10_rep).addN ((r42tl_rep e).mul r42S11_rep)
private def r42sinLo (e : Cut) : Scaled := ((r42gl e).mul r42S11).subN ((r42th e).mul r42C12)
private theorem r42sinLo_rep (e : Cut) : (r42sinLo e).Rep (thetaSinLo e) :=
  ((r42gl_rep e).mul r42S11_rep).subN ((r42th_rep e).mul r42C12_rep)
private def r42cosAp (e : Cut) : Scaled := ((r42ga e).mul r42C4).addN ((r42ta e).mul r42S5)
private theorem r42cosAp_rep (e : Cut) : (r42cosAp e).Rep (thetaCosApprox e) :=
  ((r42ga_rep e).mul r42C4_rep).addN ((r42ta_rep e).mul r42S5_rep)
private def r42sinAp (e : Cut) : Scaled := ((r42ga e).mul r42S5).subN ((r42ta e).mul r42C4)
private theorem r42sinAp_rep (e : Cut) : (r42sinAp e).Rep (thetaSinApprox e) :=
  ((r42ga_rep e).mul r42S5_rep).subN ((r42ta_rep e).mul r42C4_rep)
private def r42theta (e : Cut) : Scaled := Scaled.var.subN (Scaled.const (cutAngle e))
private theorem r42theta_rep (e : Cut) : (r42theta e).Rep (theta e) :=
  Scaled.rep_var.subN (Scaled.rep_const _)

private def r42cutA (e : Cut) : Scaled :=
  ((((r42gl e).mul ((r42elem .high).subN (r42l .high))).addN (r42l .high)).addN
    (((Scaled.const (13/12)).mul (r42tl e)).mul (r42l .high))).addN
    (((r42gh e).mul (if cutRole e=0 then Scaled.ofNat 1 else r42l .high)).mul
      ((r42cosLo e).subN (Scaled.ofNat 1)))
private theorem r42cutA_rep (e : Cut) : (r42cutA e).Rep (cutA e) := by
  unfold r42cutA cutA
  by_cases hr : cutRole e=0
  · simp only [hr,↓reduceIte]
    exact ((((r42gl_rep e).mul ((r42elem_rep .high).subN (r42l_rep .high))).addN (r42l_rep .high)).addN
      ((r42_rep_Cmul (Scaled.rep_const _) (r42tl_rep e)).mul (r42l_rep .high))).addN
      (((r42gh_rep e).mul Scaled.rep_one).mul ((r42cosLo_rep e).subN Scaled.rep_one))
  · simp only [hr,↓reduceIte]
    exact ((((r42gl_rep e).mul ((r42elem_rep .high).subN (r42l_rep .high))).addN (r42l_rep .high)).addN
      ((r42_rep_Cmul (Scaled.rep_const _) (r42tl_rep e)).mul (r42l_rep .high))).addN
      (((r42gh_rep e).mul (r42l_rep .high)).mul ((r42cosLo_rep e).subN Scaled.rep_one))

private def r42gh2 (e : Cut) : Scaled := (r42gh e).pow 2
private theorem r42gh2_rep (e : Cut) : (r42gh2 e).Rep (C (gammaHi e)^2) := (r42gh_rep e).pow 2
private def r42gl2 (e : Cut) : Scaled := (Scaled.const 2).mul ((r42gl e).pow 2)
private theorem r42gl2_rep (e : Cut) : (r42gl2 e).Rep (C (2*gammaLo e^2)) :=
  r42_rep_Cmul (Scaled.rep_const 2) (r42_rep_Cpow (r42gl_rep e) 2)

-- the P and R entries
private def r42cP0 (e : Cut) : Scaled := (r42gh2 e).mul (r42PH .high)
private theorem r42cP0_rep (e : Cut) : (r42cP0 e).Rep (C (gammaHi e)^2*PH .high) :=
  (r42gh2_rep e).mul (r42PH_rep .high)
private def r42cP0u (e : Cut) : Scaled :=
  ((r42gh2 e).mul (r42PH .high)).subN (((r42gl2 e).mul (r42k .high)).mul (r42sinLo e))
private theorem r42cP0u_rep (e : Cut) : (r42cP0u e).Rep
    (C (gammaHi e)^2*PH .high-C (2*gammaLo e^2)*k .high*thetaSinLo e) :=
  ((r42gh2_rep e).mul (r42PH_rep .high)).subN (((r42gl2_rep e).mul (r42k_rep .high)).mul (r42sinLo_rep e))
private def r42cP1g (e : Cut) : Scaled := ((r42l .high).pow 2).addN ((r42gh2 e).mul ((r42k .high).pow 2))
private theorem r42cP1g_rep (e : Cut) : (r42cP1g e).Rep ((l .high)^2+C (gammaHi e)^2*(k .high)^2) :=
  ((r42l_rep .high).pow 2).addN ((r42gh2_rep e).mul ((r42k_rep .high).pow 2))
private def r42cP1a (e : Cut) : Scaled := (r42gh2 e).mul (r42PG .high)
private theorem r42cP1a_rep (e : Cut) : (r42cP1a e).Rep (C (gammaHi e)^2*PG .high) :=
  (r42gh2_rep e).mul (r42PG_rep .high)
private def r42cP1u (e : Cut) : Scaled :=
  ((r42gh2 e).mul (r42PG .high)).subN ((((r42gl2 e).mul (r42k .high)).mul (r42l .high)).mul (r42sinLo e))
private theorem r42cP1u_rep (e : Cut) : (r42cP1u e).Rep
    (C (gammaHi e)^2*PG .high-C (2*gammaLo e^2)*k .high*l .high*thetaSinLo e) :=
  ((r42gh2_rep e).mul (r42PG_rep .high)).subN
    ((((r42gl2_rep e).mul (r42k_rep .high)).mul (r42l_rep .high)).mul (r42sinLo_rep e))
private def r42cP2g (e : Cut) : Scaled := (r42gh2 e).mul (r42PB .high)
private theorem r42cP2g_rep (e : Cut) : (r42cP2g e).Rep (C (gammaHi e)^2*PB .high) :=
  (r42gh2_rep e).mul (r42PB_rep .high)
private def r42cP2a (e : Cut) : Scaled := ((r42l .high).pow 2).addN ((r42gh2 e).mul (r42mHi .high).ksq)
private theorem r42cP2a_rep (e : Cut) : (r42cP2a e).Rep ((l .high)^2+C (gammaHi e)^2*(mHi .high)^2) :=
  ((r42l_rep .high).pow 2).addN ((r42gh2_rep e).mul (r42mHi_rep .high).ksq)
private def r42cP2u (e : Cut) : Scaled :=
  ((r42gh2 e).mul (r42PB .high)).subN ((((r42gl2 e).mul (r42l .high)).mul (r42mLo .high)).mul (r42sinLo e))
private theorem r42cP2u_rep (e : Cut) : (r42cP2u e).Rep
    (C (gammaHi e)^2*PB .high-C (2*gammaLo e^2)*l .high*mLo .high*thetaSinLo e) :=
  ((r42gh2_rep e).mul (r42PB_rep .high)).subN
    ((((r42gl2_rep e).mul (r42l_rep .high)).mul (r42mLo_rep .high)).mul (r42sinLo_rep e))
private def r42cP3 (e : Cut) : Scaled := (r42gh2 e).mul (r42PD .high)
private theorem r42cP3_rep (e : Cut) : (r42cP3 e).Rep (C (gammaHi e)^2*PD .high) :=
  (r42gh2_rep e).mul (r42PD_rep .high)

private def r42cR0 (e : Cut) : Scaled := (r42ga e).mul (r42RH .high)
private theorem r42cR0_rep (e : Cut) : (r42cR0 e).Rep (C (gammaApprox e)*RH .high) :=
  (r42ga_rep e).mul (r42RH_rep .high)
private def r42cR0u (e : Cut) : Scaled :=
  (r42ga e).mul (((Scaled.const (87/100)).mul (r42cosAp e)).addN
    ((Scaled.const (493/1000)).mul ((r42k .high).subN (r42sinAp e))))
private theorem r42cR0u_rep (e : Cut) : (r42cR0u e).Rep (C (gammaApprox e)*
    (C (87/100)*thetaCosApprox e+C (493/1000)*(k .high-thetaSinApprox e))) :=
  (r42ga_rep e).mul (((Scaled.rep_const _).mul (r42cosAp_rep e)).addN
    ((Scaled.rep_const _).mul ((r42k_rep .high).subN (r42sinAp_rep e))))
private def r42cR1g (e : Cut) : Scaled :=
  ((Scaled.const (21/25)).mul (r42l .high)).addN
    (((Scaled.const (543/1000)).mul (r42ga e)).mul (r42k .high))
private theorem r42cR1g_rep (e : Cut) : (r42cR1g e).Rep
    (C (21/25)*l .high+C (543/1000*gammaApprox e)*k .high) :=
  ((Scaled.rep_const _).mul (r42l_rep .high)).addN
    ((r42_rep_Cmul (Scaled.rep_const _) (r42ga_rep e)).mul (r42k_rep .high))
private def r42cR1a (e : Cut) : Scaled := (r42ga e).mul (r42RG .high)
private theorem r42cR1a_rep (e : Cut) : (r42cR1a e).Rep (C (gammaApprox e)*RG .high) :=
  (r42ga_rep e).mul (r42RG_rep .high)
private def r42cR1u (e : Cut) : Scaled :=
  (r42ga e).mul ((((Scaled.const (9/10)).mul (r42l .high)).mul (r42cosAp e)).addN
    ((Scaled.const (109/250)).mul ((r42k .high).subN ((r42l .high).mul (r42sinAp e)))))
private theorem r42cR1u_rep (e : Cut) : (r42cR1u e).Rep (C (gammaApprox e)*
    (C (9/10)*l .high*thetaCosApprox e+C (109/250)*(k .high-l .high*thetaSinApprox e))) :=
  (r42ga_rep e).mul ((((Scaled.rep_const _).mul (r42l_rep .high)).mul (r42cosAp_rep e)).addN
    ((Scaled.rep_const _).mul ((r42k_rep .high).subN ((r42l_rep .high).mul (r42sinAp_rep e)))))
private def r42cR2g (e : Cut) : Scaled := (r42ga e).mul (r42RB .high)
private theorem r42cR2g_rep (e : Cut) : (r42cR2g e).Rep (C (gammaApprox e)*RB .high) :=
  (r42ga_rep e).mul (r42RB_rep .high)
private def r42cR2a (e : Cut) : Scaled :=
  ((Scaled.const (4/5)).mul (r42l .high)).addN (((Scaled.const (3/5)).mul (r42ga e)).mul (r42mu .high))
private theorem r42cR2a_rep (e : Cut) : (r42cR2a e).Rep
    (C (4/5)*l .high+C (3/5*gammaApprox e)*mu .high) :=
  ((Scaled.rep_const _).mul (r42l_rep .high)).addN
    ((r42_rep_Cmul (Scaled.rep_const _) (r42ga_rep e)).mul (r42mu_rep .high))
private def r42cR2u (e : Cut) : Scaled :=
  (r42ga e).mul (((((Scaled.const (357/500)).addN ((Scaled.const (11/20)).mul (r42theta e))).mul
      (r42l .high)).mul (r42cosAp e)).addN
    (((Scaled.const (7/10)).subN ((Scaled.const (41/50)).mul (r42theta e))).mul
      ((r42mu .high).subN ((r42l .high).mul (r42sinAp e)))))
private theorem r42cR2u_rep (e : Cut) : (r42cR2u e).Rep (C (gammaApprox e)*
    ((C (357/500)+C (11/20)*theta e)*l .high*thetaCosApprox e+
      (C (7/10)-C (41/50)*theta e)*(mu .high-l .high*thetaSinApprox e))) :=
  (r42ga_rep e).mul (((((Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r42theta_rep e))).mul
      (r42l_rep .high)).mul (r42cosAp_rep e)).addN
    (((Scaled.rep_const _).subN ((Scaled.rep_const _).mul (r42theta_rep e))).mul
      ((r42mu_rep .high).subN ((r42l_rep .high).mul (r42sinAp_rep e)))))
private def r42cR3 (e : Cut) : Scaled := (r42ga e).mul (r42RD .high)
private theorem r42cR3_rep (e : Cut) : (r42cR3 e).Rep (C (gammaApprox e)*RD .high) :=
  (r42ga_rep e).mul (r42RD_rep .high)

private def r42cutN : Cut → Scaled
  | .gaH => Scaled.num4 Rbar (r42cutA .gaH) (r42cP0u .gaH) (r42cP1g .gaH) (r42cP2g .gaH) (r42cP3 .gaH)
      (r42cR0u .gaH) (r42cR1g .gaH) (r42cR2g .gaH) (r42cR3 .gaH)
  | .gaB => Scaled.num4 Rbar (r42cutA .gaB) (r42cP0 .gaB) (r42cP1g .gaB) (r42cP2u .gaB) (r42cP3 .gaB)
      (r42cR0 .gaB) (r42cR1g .gaB) (r42cR2u .gaB) (r42cR3 .gaB)
  | .abG => Scaled.num4 Rbar (r42cutA .abG) (r42cP0 .abG) (r42cP1u .abG) (r42cP2a .abG) (r42cP3 .abG)
      (r42cR0 .abG) (r42cR1u .abG) (r42cR2a .abG) (r42cR3 .abG)
  | .abH => Scaled.num4 Rbar (r42cutA .abH) (r42cP0u .abH) (r42cP1a .abH) (r42cP2a .abH) (r42cP3 .abH)
      (r42cR0u .abH) (r42cR1a .abH) (r42cR2a .abH) (r42cR3 .abH)
private theorem r42cutN_rep : ∀ e, (r42cutN e).Rep (cutN e)
  | .gaH => r42num4_rep (r42cutA_rep .gaH) (r42cP0u_rep .gaH) (r42cP1g_rep .gaH) (r42cP2g_rep .gaH)
      (r42cP3_rep .gaH) (r42cR0u_rep .gaH) (r42cR1g_rep .gaH) (r42cR2g_rep .gaH) (r42cR3_rep .gaH)
  | .gaB => r42num4_rep (r42cutA_rep .gaB) (r42cP0_rep .gaB) (r42cP1g_rep .gaB) (r42cP2u_rep .gaB)
      (r42cP3_rep .gaB) (r42cR0_rep .gaB) (r42cR1g_rep .gaB) (r42cR2u_rep .gaB) (r42cR3_rep .gaB)
  | .abG => r42num4_rep (r42cutA_rep .abG) (r42cP0_rep .abG) (r42cP1u_rep .abG) (r42cP2a_rep .abG)
      (r42cP3_rep .abG) (r42cR0_rep .abG) (r42cR1u_rep .abG) (r42cR2a_rep .abG) (r42cR3_rep .abG)
  | .abH => r42num4_rep (r42cutA_rep .abH) (r42cP0u_rep .abH) (r42cP1a_rep .abH) (r42cP2a_rep .abH)
      (r42cP3_rep .abH) (r42cR0u_rep .abH) (r42cR1a_rep .abH) (r42cR2a_rep .abH) (r42cR3_rep .abH)

/-! Composition with affine maps. -/

private theorem r42_comp_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s t : ℤ)
    {a b : ℚ} (hden : den≠0) (hab : (a+b)/2=num*s/den) (hba : (b-a)/2=num*t/den)
    {q : ℚ[X]} (hq : C ((a+b)/2)+C ((b-a)/2)*X=q) :
    (S.kcenter num den s t).Rep (p.comp q) := by
  have hc := hp.kcentered num den s t hden hab hba
  rwa [WholeIntervalPolynomial.centered,affine,hq] at hc

private theorem r42_flip_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) :
    (S.kcenter 1 5 1 (-5)).Rep (p.comp (C split-X)) :=
  r42_comp_rep hp 1 5 1 (-5) (a:=6/5) (b:=-4/5) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show ((6/5:ℚ)+-4/5)/2=split by norm_num [split],
      show ((-4/5:ℚ)-6/5)/2=-1 by norm_num,map_neg,map_one]; ring)

private theorem r42_shift_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s t : ℤ)
    {a : ℚ} (hden : den≠0) (ha : a=num*s/den) (h1 : (1:ℚ)=num*t/den) :
    (S.kcenter num den s t).Rep (p.comp (X+C a)) :=
  r42_comp_rep hp num den s t (a:=a-1) (b:=a+1) hden (by rw [← ha]; ring) (by rw [← h1]; ring)
    (by rw [show (a-1+(a+1))/2=a by ring,show (a+1-(a-1))/2=1 by ring,map_one,one_mul,add_comm])

private theorem r42_quot_eq (p : ℚ[X]) (a : ℚ) :
    (p-C (p.eval a)) /ₘ (X-C a)=(divX (p.comp (X+C a))).comp (X-C a) := by
  have h0 : (p.comp (X+C a)).coeff 0=p.eval a := by
    rw [coeff_zero_eq_eval_zero,eval_comp]; simp
  have h1 := X_mul_divX_add (p.comp (X+C a))
  have h2 : (p.comp (X+C a)).comp (X-C a)=p := by
    rw [comp_assoc]; simp
  have key : p-C (p.eval a)=(X-C a)*(divX (p.comp (X+C a))).comp (X-C a) := by
    have h3 := congrArg (fun q => q.comp (X-C a)) h1
    simp only [add_comp,mul_comp,X_comp,C_comp,h2,h0] at h3
    linear_combination (-1:ℚ[X])*h3
  rw [key,mul_divByMonic_cancel_left _ (monic_X_sub_C a)]

private theorem r42_quot_identity (p : ℚ[X]) (a : ℚ) :
    p=C (p.eval a)+(X-C a)*((p-C (p.eval a)) /ₘ (X-C a)) := by
  have hr : IsRoot (p-C (p.eval a)) a := by simp [IsRoot]
  rw [mul_divByMonic_eq_iff_isRoot.mpr hr]; ring

private theorem r42_centered_shift (r : ℚ[X]) (a b : ℚ) :
    centered a b (r.comp (X-C a))=centered 0 (b-a) r := by
  unfold WholeIntervalPolynomial.centered affine
  rw [comp_assoc]
  congr 1
  rw [sub_comp,X_comp,C_comp,show (0+(b-a))/2=(a+b)/2-a by ring,
    show (b-a-0)/2=(b-a)/2 by ring,map_sub]
  ring

/-! The low tails. -/

private def r42HFlip : Scaled := (r42NH .low).kcenter 1 5 1 (-5)
private theorem r42HFlip_rep : r42HFlip.Rep lowHFlip := r42_flip_rep (r42NH_rep .low)
private def r42HTail : Scaled := (r42HFlip.divX.divX.divX).kcenter 1 10 1 1
private theorem r42HTail_rep : r42HTail.Rep (centered 0 split lowHTail) :=
  r42HFlip_rep.divX.divX.divX.kcentered 1 10 1 1 (by norm_num) (by norm_num [split]) (by norm_num [split])
private def r42ZFlip : Scaled := (r42NZ .low).kcenter 1 5 1 (-5)
private theorem r42ZFlip_rep : r42ZFlip.Rep lowZFlip := r42_flip_rep (r42NZ_rep .low)
private def r42ZTail : Scaled := (r42ZFlip.divX.divX).kcenter 1 10 1 1
private theorem r42ZTail_rep : r42ZTail.Rep (centered 0 split lowZTail) :=
  r42ZFlip_rep.divX.divX.kcentered 1 10 1 1 (by norm_num) (by norm_num [split]) (by norm_num [split])



private lemma r42_icc {a b : ℚ} {a' b' z : ℝ} (ha : (a:ℝ)=a') (hb : (b:ℝ)=b')
    (hz : z∈Set.Icc a' b') : z∈Set.Icc (a:ℝ) (b:ℝ) := by
  rw [ha,hb]; exact hz

private lemma r42_flip {u z : ℝ} (hu : u=1/5-z) (p : ℚ[X]) :
    aeval u (p.comp (C split-X))=aeval z p := by
  rw [aeval_comp]
  congr 1
  simp only [map_sub,aeval_C,aeval_X,eq_ratCast,split,hu]
  push_cast
  ring_nf

private lemma r42_cast_lt {a b : ℚ} (h : a<b) : (a:ℝ)<(b:ℝ) := Rat.cast_lt.mpr h

/-! ### Integer checks

Each statement below is one kernel evaluation of a few integer conditions on the lists. -/

/-- `ρ` is below the `i`-th coefficient of the polynomial represented by `S`, in integers. -/
private abbrev r42CoeffOK (S : Scaled) (ρ : ℚ) (i : ℕ) : Prop :=
  S.s≠0 ∧ ρ.num*S.s<ρ.den*S.l.getD i 0

/-- The list of `c` fits degree `D`, and `ρ` is below the coefficient-norm bound, in integers. -/
private abbrev r42BoundOK (c : Scaled) (D : ℕ) (ρ : ℚ) : Prop :=
  c.s≠0 ∧ c.l.length≤D+1 ∧
    ρ.num*(c.s*2^c.l.length)<2*ρ.den*lowerZ D (fun j => (chebList c.l).getD j 0)

/-- `0 < b 2` and `ρ` below `quadraticReserve b count` for the degree-`D` Chebyshev coefficients
`b` of the polynomial represented by `c`, in integers. -/
private abbrev r42QuadOK (c : Scaled) (D count : ℕ) (ρ : ℚ) : Prop :=
  c.s≠0 ∧ c.l.length≤D+1 ∧ 0<(chebList c.l).getD 2 0 ∧
    ρ.num*(8*(chebList c.l).getD 2 0*(c.s*2^c.l.length))<
      2*ρ.den*(8*(chebList c.l).getD 2 0*((chebList c.l).getD 0 0-(chebList c.l).getD 2 0-
        ∑ j : Fin count,|(chebList c.l).getD (j.val+3) 0|)-(chebList c.l).getD 1 0^2)

private theorem r42_coeff_lt {S : Scaled} {p : ℚ[X]} (hS : S.Rep p) {ρ : ℚ} {i : ℕ}
    (h : r42CoeffOK S ρ i) : ρ<p.coeff i := by
  obtain ⟨hs,hlt⟩ := h
  have hs' : (0:ℚ)<S.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd : (0:ℚ)<ρ.den := by exact_mod_cast ρ.den_pos
  have hc : ((ρ.num*S.s:ℤ):ℚ)<((ρ.den*S.l.getD i 0:ℤ):ℚ) := by exact_mod_cast hlt
  push_cast at hc
  rw [hS.coeff hs,lt_div_iff₀ hs',← Rat.num_div_den ρ,div_mul_eq_mul_div,div_lt_iff₀ hd]
  linarith

private theorem r42_bound {c : Scaled} {a b : ℚ} {p : ℚ[X]} (hc : c.Rep (centered a b p))
    {D : ℕ} {ρ : ℚ} (h : r42BoundOK c D ρ) :
    centered a b p=expansion D (centered a b p) ∧ ρ<lowerOn D a b p := by
  obtain ⟨hs,hl,hlt⟩ := h
  refine ⟨hc.eq_expansion hs hl,?_⟩
  have hd : (0:ℚ)<ρ.den := by exact_mod_cast ρ.den_pos
  have hc' : ((ρ.num*(c.s*2^c.l.length):ℤ):ℚ)<
      ((2*ρ.den*lowerZ D (fun j => (chebList c.l).getD j 0):ℤ):ℚ) := by exact_mod_cast hlt
  push_cast at hc'
  rw [lowerOn_eq_of_rep hc hs hl,lt_div_iff₀ (scale_pos hs),← Rat.num_div_den ρ,
    div_mul_eq_mul_div,div_lt_iff₀ hd]
  linarith

private theorem r42_quad {c : Scaled} {a b : ℚ} {p : ℚ[X]} (hc : c.Rep (centered a b p))
    {D count : ℕ} {ρ : ℚ} (h : r42QuadOK c D count ρ) :
    centered a b p=expansion D (centered a b p) ∧ 0<coefficient D (centered a b p) 2 ∧
      ρ<quadraticReserve (coefficient D (centered a b p)) count := by
  obtain ⟨hs,hl,h2,hlt⟩ := h
  refine ⟨hc.eq_expansion hs hl,?_⟩
  rw [Certificate.coefficient_centered_eq hc hs hl]
  have hK := scale_pos hs
  have hd : (0:ℚ)<ρ.den := by exact_mod_cast ρ.den_pos
  have hB2 : (0:ℚ)<((chebList c.l).getD 2 0:ℤ) := by exact_mod_cast h2
  have e2 : (c.s:ℚ)*2^c.l.length=2*(c.s*2^c.l.length/2) := by ring
  generalize (c.s:ℚ)*2^c.l.length/2=K at hK e2
  have htail : tailNorm (fun j => ((chebList c.l).getD j 0:ℚ)/K) 3 count=
      ((∑ j : Fin count,|(chebList c.l).getD (j.val+3) 0|:ℤ):ℚ)/K := by
    unfold tailNorm
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [abs_div,abs_of_pos hK]
  refine ⟨div_pos hB2 hK,?_⟩
  unfold quadraticReserve
  rw [htail]
  beta_reduce
  push_cast
  have hc' := (Int.cast_lt (R:=ℚ)).2 hlt
  push_cast at hc'
  rw [e2] at hc'
  generalize ((chebList c.l).getD 0 0:ℚ)=B0 at hc' ⊢
  generalize ((chebList c.l).getD 1 0:ℚ)=B1 at hc' ⊢
  generalize ((chebList c.l).getD 2 0:ℚ)=B2 at hc' hB2 ⊢
  generalize (∑ j : Fin count,(|(chebList c.l).getD (j.val+3) 0|:ℚ))=T at hc' ⊢
  have key : B0/K-B2/K-(B1/K)^2/(8*(B2/K))-T/K=(8*B2*(B0-B2-T)-B1^2)/(8*B2*K) := by
    field_simp
    ring
  rw [key,lt_div_iff₀ (by positivity),← Rat.num_div_den ρ,div_mul_eq_mul_div,div_lt_iff₀ hd]
  linarith

theorem low_H_identity : lowHFlip=C (lowHFlip.coeff 0)+C (lowHFlip.coeff 1)*X+
    C (lowHFlip.coeff 2)*X^2+X^3*lowHTail := by
  have e1 := X_mul_divX_add lowHFlip
  have e2 := X_mul_divX_add lowHFlip.divX
  have e3 := X_mul_divX_add lowHFlip.divX.divX
  norm_num only [coeff_divX] at e2 e3
  rw [lowHTail]
  linear_combination (-1:ℚ[X])*e1+(-X)*e2+(-X^2)*e3

private theorem r42_low_H_check : r42CoeffOK r42HFlip (161/100000) 0 ∧
    r42CoeffOK r42HFlip (-173/5000) 1 ∧ r42CoeffOK r42HFlip (-191/500) 2 ∧
    r42BoundOK r42HTail 34 (158/5) := by
  decide +kernel

theorem low_H_coefficients :
    (161/100000:ℚ)<lowHFlip.coeff 0 ∧
    (-173/5000:ℚ)<lowHFlip.coeff 1 ∧
    (-191/500:ℚ)<lowHFlip.coeff 2 :=
  ⟨r42_coeff_lt r42HFlip_rep r42_low_H_check.1,r42_coeff_lt r42HFlip_rep r42_low_H_check.2.1,
    r42_coeff_lt r42HFlip_rep r42_low_H_check.2.2.1⟩

theorem low_H_tail_expansion : centered 0 split lowHTail=
    expansion 34 (centered 0 split lowHTail) :=
  (r42_bound r42HTail_rep r42_low_H_check.2.2.2).1

theorem low_H_tail_reserve : (158/5:ℚ)<lowerOn 34 0 split lowHTail :=
  (r42_bound r42HTail_rep r42_low_H_check.2.2.2).2

theorem low_H_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/5:ℝ)) :
    (97/100000:ℝ)<aeval z (NH .low) := by
  obtain ⟨u,hu_def⟩ : ∃ u : ℝ,u=1/5-z := ⟨_,rfl⟩
  have hu : u∈Set.Icc ((0:ℚ):ℝ) ((split:ℚ):ℝ) :=
    r42_icc (a':=0) (b':=1/5) (by norm_num) (by norm_num [split])
      ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hu0 : 0≤u := by linarith [hz.2]
  have ht := positive_on_interval (by norm_num [split] : (0:ℚ)<split)
    low_H_tail_expansion low_H_tail_reserve hu
  have h0 : (161/100000:ℝ)<(lowHFlip.coeff 0:ℝ) := by
    have hc := r42_cast_lt low_H_coefficients.1
    push_cast at hc
    exact hc
  have h1 : (-173/5000:ℝ)<(lowHFlip.coeff 1:ℝ) := by
    have hc := r42_cast_lt low_H_coefficients.2.1
    push_cast at hc
    exact hc
  have h2 : (-191/500:ℝ)<(lowHFlip.coeff 2:ℝ) := by
    have hc := r42_cast_lt low_H_coefficients.2.2
    push_cast at hc
    exact hc
  have he := congrArg (fun p : ℚ[X] => aeval u p) low_H_identity
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at he
  have hrefl : aeval u lowHFlip=aeval z (NH .low) := r42_flip hu_def _
  rw [hrefl] at he
  have hlinear := mul_le_mul_of_nonneg_right h1.le hu0
  have hquadratic := mul_le_mul_of_nonneg_right h2.le (sq_nonneg u)
  have hcubic := mul_le_mul_of_nonneg_left ht.le (pow_nonneg hu0 3)
  have hretained := mul_nonneg hu0 (sq_nonneg (u-1/50))
  have hcomplete := sq_nonneg (u-(1181/25000)/(2*(441/500)))
  norm_num at ht hcubic
  linarith

theorem low_Z_identity : lowZFlip=C (lowZFlip.coeff 0)+C (lowZFlip.coeff 1)*X+
    X^2*lowZTail := by
  have e1 := X_mul_divX_add lowZFlip
  have e2 := X_mul_divX_add lowZFlip.divX
  norm_num only [coeff_divX] at e2
  rw [lowZTail]
  linear_combination (-1:ℚ[X])*e1+(-X)*e2

private theorem r42_low_Z_check : r42CoeffOK r42ZFlip (753/500000) 0 ∧
    r42CoeffOK r42ZFlip (-987/10000) 1 ∧ r42BoundOK r42ZTail 64 (77/10) := by
  decide +kernel

theorem low_Z_coefficients :
    (753/500000:ℚ)<lowZFlip.coeff 0 ∧
    (-987/10000:ℚ)<lowZFlip.coeff 1 :=
  ⟨r42_coeff_lt r42ZFlip_rep r42_low_Z_check.1,r42_coeff_lt r42ZFlip_rep r42_low_Z_check.2.1⟩

theorem low_Z_tail_expansion : centered 0 split lowZTail=
    expansion 64 (centered 0 split lowZTail) :=
  (r42_bound r42ZTail_rep r42_low_Z_check.2.2).1

theorem low_Z_tail_reserve : (77/10:ℚ)<lowerOn 64 0 split lowZTail :=
  (r42_bound r42ZTail_rep r42_low_Z_check.2.2).2

theorem low_Z_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/5:ℝ)) :
    (59/50000:ℝ)<aeval z (NZ .low) := by
  obtain ⟨u,hu_def⟩ : ∃ u : ℝ,u=1/5-z := ⟨_,rfl⟩
  have hu : u∈Set.Icc ((0:ℚ):ℝ) ((split:ℚ):ℝ) :=
    r42_icc (a':=0) (b':=1/5) (by norm_num) (by norm_num [split])
      ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hu0 : 0≤u := by linarith [hz.2]
  have ht := positive_on_interval (by norm_num [split] : (0:ℚ)<split)
    low_Z_tail_expansion low_Z_tail_reserve hu
  have h0 : (753/500000:ℝ)<(lowZFlip.coeff 0:ℝ) := by
    have hc := r42_cast_lt low_Z_coefficients.1
    push_cast at hc
    exact hc
  have h1 : (-987/10000:ℝ)<(lowZFlip.coeff 1:ℝ) := by
    have hc := r42_cast_lt low_Z_coefficients.2
    push_cast at hc
    exact hc
  have he := congrArg (fun p : ℚ[X] => aeval u p) low_Z_identity
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at he
  have hrefl : aeval u lowZFlip=aeval z (NZ .low) := r42_flip hu_def _
  rw [hrefl] at he
  have hlinear := mul_le_mul_of_nonneg_right h1.le hu0
  have hquadratic := mul_le_mul_of_nonneg_left ht.le (sq_nonneg u)
  have hcomplete := sq_nonneg (u-(987/10000)/(2*(77/10)))
  norm_num at ht hquadratic
  linarith

def mixedCoefficient : ℕ→ℚ := coefficient 40 (centered 0 split NM)

private def r42NMc : Scaled := r42NM.kcenter 1 10 1 1
private theorem r42NMc_rep : r42NMc.Rep (centered 0 split NM) :=
  r42NM_rep.kcentered 1 10 1 1 (by norm_num) (by norm_num [split]) (by norm_num [split])
private theorem r42_mixed_check : r42QuadOK r42NMc 40 38 (153/5000) := by decide +kernel

/-- The Chebyshev quadratic part of a series. -/
private theorem r42_series_quad (c : ℕ → ℚ) (n : ℕ) :
    series (n+2) c=C (c 0-c 2)+C (c 1)*X+C (2*c 2)*X^2+tail c 3 n := by
  rw [series,tail,Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,Nat.cast_zero,
    zero_add]
  have hrest : ∀ j : Fin n,C (c (j.val+1+1+1))*
      Polynomial.Chebyshev.T ℚ ((j.val:ℤ)+1+1+1)=
      C (c (j.val+3))*Polynomial.Chebyshev.T ℚ ((j.val:ℤ)+3) := fun j => by
    ring_nf
  simp only [hrest,Polynomial.Chebyshev.T_one,show (1:ℕ)+1=2 from rfl,show (1:ℤ)+1=2 by norm_num,
    Polynomial.Chebyshev.T_two,map_sub,map_mul,map_ofNat]
  ring

theorem low_mixed_identity : centered 0 split NM=
    C (mixedCoefficient 0-mixedCoefficient 2)+C (mixedCoefficient 1)*X+
      C (2*mixedCoefficient 2)*X^2+tail mixedCoefficient 3 38 := by
  rw [(r42_quad r42NMc_rep r42_mixed_check).1,expansion,← mixedCoefficient.eq_1]
  exact r42_series_quad mixedCoefficient 38

theorem low_mixed_reserve : 0< mixedCoefficient 2 ∧
    (153/5000:ℚ)<quadraticReserve mixedCoefficient 38 := by
  rw [mixedCoefficient]
  exact (r42_quad r42NMc_rep r42_mixed_check).2

theorem low_M_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/5:ℝ)) :
    (153/5000:ℝ)<aeval z NM := by
  have hb := quadratic_on_interval (by norm_num [split] : (0:ℚ)<split)
    low_mixed_identity low_mixed_reserve.1
    (r42_icc (by norm_num) (by norm_num [split]) hz)
  have hr : (153/5000:ℝ)<(quadraticReserve mixedCoefficient 38:ℝ) := by
    have hc := r42_cast_lt low_mixed_reserve.2
    push_cast at hc
    exact hc
  exact hr.trans_le hb

/-- The eight direct coefficient-norm certificates in the companion. -/
inductive Direct where
  | lowSH | lowSG | highB | highZ | highZA | cutGAB | cutABG | cutABH
  deriving DecidableEq

instance : Fintype Direct where
  elems := {.lowSH, .lowSG, .highB, .highZ, .highZA, .cutGAB, .cutABG, .cutABH}
  complete x := by cases x <;> decide
def directPolynomial : Direct→ℚ[X]
  | .lowSH => NSH | .lowSG => NSG | .highB => NB | .highZ => NZ .high
  | .highZA => NZA | .cutGAB => cutN .gaB | .cutABG => cutN .abG | .cutABH => cutN .abH
def directDegree : Direct→ℕ
  | .lowSH => 32 | .lowSG => 35 | .highB => 36 | .highZ => 72
  | .highZA => 72 | .cutGAB => 36 | .cutABG => 40 | .cutABH => 38
def directLeft : Direct→ℚ
  | .lowSH => 0 | .lowSG => 0 | .highB => split | .highZ => split
  | .highZA => split | .cutGAB => 1/4 | .cutABG => 19/50 | .cutABH => 19/50
def directRight : Direct→ℚ | .lowSH => split | .lowSG => split | _ => h
def directReserve : Direct→ℚ
  | .lowSH => 231/1250 | .lowSG => 157/5000 | .highB => 1/200
  | .highZ => 91/50000 | .highZA => 51/12500 | .cutGAB => 21/3125
  | .cutABG => 107/2000 | .cutABH => 111/2000

/-! Per-case certificates of the direct coefficient norms. -/

private def r42c_lowSH : Scaled := r42NSH.kcenter 1 10 1 1
private theorem r42c_lowSH_rep : r42c_lowSH.Rep (centered 0 split NSH) :=
  r42NSH_rep.kcentered 1 10 1 1 (by norm_num) (by norm_num [split]) (by norm_num [split])
private theorem r42_lowSH_check : r42BoundOK r42c_lowSH 32 (231/1250) := by decide +kernel

private def r42c_lowSG : Scaled := r42NSG.kcenter 1 10 1 1
private theorem r42c_lowSG_rep : r42c_lowSG.Rep (centered 0 split NSG) :=
  r42NSG_rep.kcentered 1 10 1 1 (by norm_num) (by norm_num [split]) (by norm_num [split])
private theorem r42_lowSG_check : r42BoundOK r42c_lowSG 35 (157/5000) := by decide +kernel

private def r42c_highB : Scaled := r42NB.kcenter 1 20 9 5
private theorem r42c_highB_rep : r42c_highB.Rep (centered split h NB) :=
  r42NB_rep.kcentered 1 20 9 5 (by norm_num) (by norm_num [split,h]) (by norm_num [split,h])
private theorem r42_highB_check : r42BoundOK r42c_highB 36 (1/200) := by decide +kernel

private def r42c_highZ : Scaled := (r42NZ .high).kcenter 1 20 9 5
private theorem r42c_highZ_rep : r42c_highZ.Rep (centered split h (NZ .high)) :=
  (r42NZ_rep .high).kcentered 1 20 9 5 (by norm_num) (by norm_num [split,h]) (by norm_num [split,h])
private theorem r42_highZ_check : r42BoundOK r42c_highZ 72 (91/50000) := by decide +kernel

private def r42c_highZA : Scaled := r42NZA.kcenter 1 20 9 5
private theorem r42c_highZA_rep : r42c_highZA.Rep (centered split h NZA) :=
  r42NZA_rep.kcentered 1 20 9 5 (by norm_num) (by norm_num [split,h]) (by norm_num [split,h])
private theorem r42_highZA_check : r42BoundOK r42c_highZA 72 (51/12500) := by decide +kernel

private def r42c_cutGAB : Scaled := (r42cutN .gaB).kcenter 1 40 19 9
private theorem r42c_cutGAB_rep : r42c_cutGAB.Rep (centered (1/4) h (cutN .gaB)) :=
  (r42cutN_rep .gaB).kcentered 1 40 19 9 (by norm_num) (by norm_num [h]) (by norm_num [h])
private theorem r42_cutGAB_check : r42BoundOK r42c_cutGAB 36 (21/3125) := by decide +kernel

private def r42c_cutABG : Scaled := (r42cutN .abG).kcenter 1 50 27 8
private theorem r42c_cutABG_rep : r42c_cutABG.Rep (centered (19/50) h (cutN .abG)) :=
  (r42cutN_rep .abG).kcentered 1 50 27 8 (by norm_num) (by norm_num [h]) (by norm_num [h])
private theorem r42_cutABG_check : r42BoundOK r42c_cutABG 40 (107/2000) := by decide +kernel

private def r42c_cutABH : Scaled := (r42cutN .abH).kcenter 1 50 27 8
private theorem r42c_cutABH_rep : r42c_cutABH.Rep (centered (19/50) h (cutN .abH)) :=
  (r42cutN_rep .abH).kcentered 1 50 27 8 (by norm_num) (by norm_num [h]) (by norm_num [h])
private theorem r42_cutABH_check : r42BoundOK r42c_cutABH 38 (111/2000) := by decide +kernel

theorem direct_expansion (e : Direct) :
    centered (directLeft e) (directRight e) (directPolynomial e)=
      expansion (directDegree e)
        (centered (directLeft e) (directRight e) (directPolynomial e)) := by
  cases e
  exacts [(r42_bound r42c_lowSH_rep r42_lowSH_check).1,
    (r42_bound r42c_lowSG_rep r42_lowSG_check).1,
    (r42_bound r42c_highB_rep r42_highB_check).1,
    (r42_bound r42c_highZ_rep r42_highZ_check).1,
    (r42_bound r42c_highZA_rep r42_highZA_check).1,
    (r42_bound r42c_cutGAB_rep r42_cutGAB_check).1,
    (r42_bound r42c_cutABG_rep r42_cutABG_check).1,
    (r42_bound r42c_cutABH_rep r42_cutABH_check).1]

theorem direct_reserve (e : Direct) : directReserve e<
    lowerOn (directDegree e) (directLeft e) (directRight e) (directPolynomial e) := by
  cases e
  exacts [(r42_bound r42c_lowSH_rep r42_lowSH_check).2,
    (r42_bound r42c_lowSG_rep r42_lowSG_check).2,
    (r42_bound r42c_highB_rep r42_highB_check).2,
    (r42_bound r42c_highZ_rep r42_highZ_check).2,
    (r42_bound r42c_highZA_rep r42_highZA_check).2,
    (r42_bound r42c_cutGAB_rep r42_cutGAB_check).2,
    (r42_bound r42c_cutABG_rep r42_cutABG_check).2,
    (r42_bound r42c_cutABH_rep r42_cutABH_check).2]

theorem direct_positive (e : Direct) {z : ℝ}
    (hz : z∈Set.Icc (directLeft e:ℝ) (directRight e:ℝ)) :
    (directReserve e:ℝ)<aeval z (directPolynomial e) := by
  apply positive_on_interval _ (direct_expansion e) (direct_reserve e) hz
  cases e <;> norm_num [directLeft,directRight,split,h]

/-- The three positive secant quotients. -/
inductive Quotient where | highH | highG | cutGAH
  deriving DecidableEq

instance : Fintype Quotient where
  elems := {.highH, .highG, .cutGAH}
  complete x := by cases x <;> decide
def quotientPolynomial : Quotient→ℚ[X]
  | .highH => highHQuotient | .highG => highGQuotient | .cutGAH => cutHQuotient
def quotientNumerator : Quotient→ℚ[X]
  | .highH => NH .high | .highG => NG | .cutGAH => cutN .gaH
def quotientLeft : Quotient→ℚ | .highH => split | .highG => split | .cutGAH => 1/4
def quotientDegree : Quotient→ℕ | .highH => 37 | .highG => 39 | .cutGAH => 37
def quotientReserve : Quotient→ℚ | .highH => 53/2500 | .highG => 457/5000 | .cutGAH => 453/1000
def quotientEndpoint : Quotient→ℚ | .highH => 57/25000 | .highG => 173/20000 | .cutGAH => 33/5000

/-! Per-case certificates of the secant quotients. -/

private def r42s_highH : Scaled := (r42NH .high).kcenter 1 5 1 5
private theorem r42s_highH_rep : r42s_highH.Rep ((NH .high).comp (X+C split)) :=
  r42_shift_rep (r42NH_rep .high) 1 5 1 5 (by norm_num) (by norm_num [split]) (by norm_num)
private def r42q_highH : Scaled := r42s_highH.divX.kcenter 1 4 1 1
private theorem r42q_highH_rep :
    r42q_highH.Rep (centered 0 (h-split) (divX ((NH .high).comp (X+C split)))) :=
  r42s_highH_rep.divX.kcentered 1 4 1 1 (by norm_num) (by norm_num [split,h]) (by norm_num [split,h])
private theorem r42_highH_check :
    r42BoundOK r42q_highH 37 (53/2500) ∧ r42CoeffOK r42s_highH (57/25000) 0 := by
  decide +kernel
private theorem r42_highH_expansion :
    centered split h highHQuotient=expansion 37 (centered split h highHQuotient) := by
  rw [highHQuotient,r42_quot_eq,r42_centered_shift]
  exact (r42_bound r42q_highH_rep r42_highH_check.1).1
private theorem r42_highH_reserve : (53/2500:ℚ)<lowerOn 37 split h highHQuotient := by
  rw [lowerOn,highHQuotient,r42_quot_eq,r42_centered_shift,← lowerOn]
  exact (r42_bound r42q_highH_rep r42_highH_check.1).2
private theorem r42_highH_endpoint : (57/25000:ℚ)<(NH .high).eval split := by
  have he : (NH .high).eval split=((NH .high).comp (X+C split)).coeff 0 := by
    rw [coeff_zero_eq_eval_zero,eval_comp]; simp
  rw [he]
  exact r42_coeff_lt r42s_highH_rep r42_highH_check.2

private def r42s_highG : Scaled := r42NG.kcenter 1 5 1 5
private theorem r42s_highG_rep : r42s_highG.Rep (NG.comp (X+C split)) :=
  r42_shift_rep r42NG_rep 1 5 1 5 (by norm_num) (by norm_num [split]) (by norm_num)
private def r42q_highG : Scaled := r42s_highG.divX.kcenter 1 4 1 1
private theorem r42q_highG_rep :
    r42q_highG.Rep (centered 0 (h-split) (divX (NG.comp (X+C split)))) :=
  r42s_highG_rep.divX.kcentered 1 4 1 1 (by norm_num) (by norm_num [split,h]) (by norm_num [split,h])
private theorem r42_highG_check :
    r42BoundOK r42q_highG 39 (457/5000) ∧ r42CoeffOK r42s_highG (173/20000) 0 := by
  decide +kernel
private theorem r42_highG_expansion :
    centered split h highGQuotient=expansion 39 (centered split h highGQuotient) := by
  rw [highGQuotient,r42_quot_eq,r42_centered_shift]
  exact (r42_bound r42q_highG_rep r42_highG_check.1).1
private theorem r42_highG_reserve : (457/5000:ℚ)<lowerOn 39 split h highGQuotient := by
  rw [lowerOn,highGQuotient,r42_quot_eq,r42_centered_shift,← lowerOn]
  exact (r42_bound r42q_highG_rep r42_highG_check.1).2
private theorem r42_highG_endpoint : (173/20000:ℚ)<NG.eval split := by
  have he : NG.eval split=(NG.comp (X+C split)).coeff 0 := by
    rw [coeff_zero_eq_eval_zero,eval_comp]; simp
  rw [he]
  exact r42_coeff_lt r42s_highG_rep r42_highG_check.2

private def r42s_cutGAH : Scaled := (r42cutN .gaH).kcenter 1 4 1 4
private theorem r42s_cutGAH_rep : r42s_cutGAH.Rep ((cutN .gaH).comp (X+C (1/4))) :=
  r42_shift_rep (r42cutN_rep .gaH) 1 4 1 4 (by norm_num) (by norm_num) (by norm_num)
private def r42q_cutGAH : Scaled := r42s_cutGAH.divX.kcenter 9 40 1 1
private theorem r42q_cutGAH_rep :
    r42q_cutGAH.Rep (centered 0 (h-(1/4)) (divX ((cutN .gaH).comp (X+C (1/4))))) :=
  r42s_cutGAH_rep.divX.kcentered 9 40 1 1 (by norm_num) (by norm_num [h]) (by norm_num [h])
private theorem r42_cutGAH_check :
    r42BoundOK r42q_cutGAH 37 (453/1000) ∧ r42CoeffOK r42s_cutGAH (33/5000) 0 := by
  decide +kernel
private theorem r42_cutGAH_expansion :
    centered (1/4) h cutHQuotient=expansion 37 (centered (1/4) h cutHQuotient) := by
  rw [cutHQuotient,r42_quot_eq,r42_centered_shift]
  exact (r42_bound r42q_cutGAH_rep r42_cutGAH_check.1).1
private theorem r42_cutGAH_reserve : (453/1000:ℚ)<lowerOn 37 (1/4) h cutHQuotient := by
  rw [lowerOn,cutHQuotient,r42_quot_eq,r42_centered_shift,← lowerOn]
  exact (r42_bound r42q_cutGAH_rep r42_cutGAH_check.1).2
private theorem r42_cutGAH_endpoint : (33/5000:ℚ)<(cutN .gaH).eval (1/4) := by
  have he : (cutN .gaH).eval (1/4)=((cutN .gaH).comp (X+C (1/4))).coeff 0 := by
    rw [coeff_zero_eq_eval_zero,eval_comp]; simp
  rw [he]
  exact r42_coeff_lt r42s_cutGAH_rep r42_cutGAH_check.2

theorem quotient_identity (e : Quotient) :
    quotientNumerator e=C ((quotientNumerator e).eval (quotientLeft e))+
      (X-C (quotientLeft e))*quotientPolynomial e := by
  cases e <;> exact r42_quot_identity _ _

theorem quotient_expansion (e : Quotient) :
    centered (quotientLeft e) h (quotientPolynomial e)=
      expansion (quotientDegree e) (centered (quotientLeft e) h (quotientPolynomial e)) := by
  cases e
  exacts [r42_highH_expansion,r42_highG_expansion,r42_cutGAH_expansion]

theorem quotient_reserve (e : Quotient) :
    quotientReserve e<lowerOn (quotientDegree e) (quotientLeft e) h (quotientPolynomial e) ∧
    quotientEndpoint e<(quotientNumerator e).eval (quotientLeft e) := by
  cases e
  exacts [⟨r42_highH_reserve,r42_highH_endpoint⟩,⟨r42_highG_reserve,r42_highG_endpoint⟩,
    ⟨r42_cutGAH_reserve,r42_cutGAH_endpoint⟩]

theorem quotient_positive (e : Quotient) {z : ℝ}
    (hz : z∈Set.Icc (quotientLeft e:ℝ) (h:ℝ)) :
    (quotientEndpoint e:ℝ)<aeval z (quotientNumerator e) := by
  have ht := positive_on_interval
    (by cases e <;> norm_num [quotientLeft,split,h] : quotientLeft e<h)
    (quotient_expansion e) (quotient_reserve e).1 hz
  have hp : 0≤aeval z (quotientPolynomial e) := by
    have hr : (0:ℝ)<(quotientReserve e:ℝ) := by
      cases e <;> norm_num [quotientReserve]
    exact (hr.trans ht).le
  have he := congrArg (fun p : ℚ[X] => aeval z p) (quotient_identity e)
  simp only [map_add,map_mul,map_sub,aeval_C,aeval_X,eq_ratCast] at he
  have hleft := r42_cast_lt (quotient_reserve e).2
  have hterm := mul_nonneg (sub_nonneg.mpr hz.1) hp
  linarith

theorem low_numerators_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/5:ℝ)) :
    0<aeval z (NH .low) ∧ 0<aeval z (NZ .low) ∧ 0<aeval z NM ∧
      0<aeval z NSH ∧ 0<aeval z NSG := by
  have hH := low_H_positive hz
  have hZ := low_Z_positive hz
  have hM := low_M_positive hz
  have hSH := direct_positive .lowSH
    (r42_icc (by norm_num [directLeft]) (by norm_num [directRight,split]) hz)
  have hSG := direct_positive .lowSG
    (r42_icc (by norm_num [directLeft]) (by norm_num [directRight,split]) hz)
  norm_num [directReserve,directPolynomial] at hSH hSG
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem high_numerators_positive {z : ℝ} (hz : z∈Set.Icc (1/5:ℝ) (7/10:ℝ)) :
    0<aeval z (NH .high) ∧ 0<aeval z NG ∧ 0<aeval z NB ∧
      0<aeval z (NZ .high) ∧ 0<aeval z NZA := by
  have hq (e : Quotient) (he : quotientLeft e=split) :
      z∈Set.Icc (quotientLeft e:ℝ) (h:ℝ) :=
    r42_icc (by rw [he]; norm_num [split]) (by norm_num [h]) hz
  have hd (e : Direct) (hl : directLeft e=split) (hr : directRight e=h) :
      z∈Set.Icc (directLeft e:ℝ) (directRight e:ℝ) :=
    r42_icc (by rw [hl]; norm_num [split]) (by rw [hr]; norm_num [h]) hz
  have hH := quotient_positive .highH (hq .highH rfl)
  have hG := quotient_positive .highG (hq .highG rfl)
  have hB := direct_positive .highB (hd .highB rfl rfl)
  have hZ := direct_positive .highZ (hd .highZ rfl rfl)
  have hZA := direct_positive .highZA (hd .highZA rfl rfl)
  norm_num [quotientEndpoint,quotientNumerator] at hH hG
  norm_num [directReserve,directPolynomial] at hB hZ hZA
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem cut_numerator_positive (e : Cut) {z : ℝ}
    (hz : z∈Set.Icc (cutAngle e:ℝ) (h:ℝ)) : 0<aeval z (cutN e) := by
  cases e
  · have hh := quotient_positive .cutGAH hz
    norm_num [quotientEndpoint,quotientNumerator] at hh
    linarith
  · have hh := direct_positive .cutGAB hz
    norm_num [directReserve,directPolynomial] at hh
    linarith
  · have hh := direct_positive .cutABG hz
    norm_num [directReserve,directPolynomial] at hh
    linarith
  · have hh := direct_positive .cutABH hz
    norm_num [directReserve,directPolynomial] at hh
    linarith

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
