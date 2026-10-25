module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2PolynomialData
public import SquaresInCircles.Eight.Arithmetic.KroneckerPolynomials

/-!
# Eight squares: whole-interval positivity for the negative-EH / TD2 endpoints

The two low T endpoints keep their centered quadratic (`small_quadratic_certificate`); all other
numerators use the aggregate of their coefficients. Every mass is positive on its whole native
interval (`small_mass_positive`, `far_mass_positive`). These are finite polynomial identities,
not a grid of angle evaluations.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Certificate
open WholeIntervalPolynomial ChebyshevLeadingBounds
open PositiveTD.Certificate (L h)

theorem small_interval (r : SmallCase) : smallLeft r<smallRight r := by
  cases r <;> norm_num [smallLeft,smallRight,v,L,h]
theorem far_interval (r : FarCase) : farLeft r<farRight r := by
  cases r <;> norm_num [farLeft,farRight,v,u,h]

section r78
open WholeIntervalPolynomial.Certificate (Scaled lowerOn_eq_of_rep lowerZ chebList toPoly)
open PositiveTD.Certificate (etaQ Rbar sigmabar cbar S5 S9 S11 C4 C10 C12 num3 num4)

private theorem r78num3_rep {A P0 P1 P2 r0 r1 r2 : Scaled} {a p0 p1 p2 s0 s1 s2 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) :
    (Scaled.num3 Rbar A P0 P1 P2 r0 r1 r2).Rep (num3 a p0 p1 p2 s0 s1 s2) :=
  hA.num3 Rbar h0 h1 h2 g0 g1 g2
private theorem r78num4_rep {A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled}
    {a p0 p1 p2 p3 s0 s1 s2 s3 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2) (h3 : P3.Rep p3)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) (g3 : r3.Rep s3) :
    (Scaled.num4 Rbar A P0 P1 P2 P3 r0 r1 r2 r3).Rep (num4 a p0 p1 p2 p3 s0 s1 s2 s3) :=
  hA.num4 Rbar h0 h1 h2 h3 g0 g1 g2 g3

/-! ### The numerators and masses as scaled integer coefficient lists

Each polynomial of the endpoint data is mirrored by a `Scaled` list built with the same
operations, and `Scaled.Rep` proves that the list represents it. The kernel evaluates
only these integer lists: sums are reduced by their gcd (`addN`, `subN`), and the numerators,
the long products and the changes of variable go through Kronecker substitution in a
power-of-two base (`Scaled.num3`, `num4`, `kmul`, `ksq`, `kcenter` of `KroneckerPolynomials`). -/

private def r78Z : Scaled := ⟨[],1⟩
private theorem r78Z_rep : r78Z.Rep 0 := Scaled.rep_zero
private def r78one : Scaled := Scaled.ofNat 1
private theorem r78one_rep : r78one.Rep 1 := Scaled.rep_one

private def r78S5 : Scaled :=
  (Scaled.var.subN ((Scaled.const (1/6)).mul (Scaled.mono 3))).addN
    ((Scaled.const (1/120)).mul (Scaled.mono 5))
private theorem r78S5_rep : r78S5.Rep S5 :=
  (Scaled.rep_var.subN ((Scaled.rep_const _).mul (Scaled.rep_mono 3))).addN
    ((Scaled.rep_const _).mul (Scaled.rep_mono 5))
private def r78S9 : Scaled :=
  (r78S5.subN ((Scaled.const (1/5040)).mul (Scaled.mono 7))).addN
    ((Scaled.const (1/362880)).mul (Scaled.mono 9))
private theorem r78S9_rep : r78S9.Rep S9 :=
  (r78S5_rep.subN ((Scaled.rep_const _).mul (Scaled.rep_mono 7))).addN
    ((Scaled.rep_const _).mul (Scaled.rep_mono 9))
private def r78S11 : Scaled := r78S9.subN ((Scaled.const (1/39916800)).mul (Scaled.mono 11))
private theorem r78S11_rep : r78S11.Rep S11 :=
  r78S9_rep.subN ((Scaled.rep_const _).mul (Scaled.rep_mono 11))
private def r78C4 : Scaled :=
  (r78one.subN ((Scaled.const (1/2)).mul (Scaled.mono 2))).addN
    ((Scaled.const (1/24)).mul (Scaled.mono 4))
private theorem r78C4_rep : r78C4.Rep C4 :=
  (r78one_rep.subN ((Scaled.rep_const _).mul (Scaled.rep_mono 2))).addN
    ((Scaled.rep_const _).mul (Scaled.rep_mono 4))
private def r78C10 : Scaled :=
  ((r78C4.subN ((Scaled.const (1/720)).mul (Scaled.mono 6))).addN
    ((Scaled.const (1/40320)).mul (Scaled.mono 8))).subN
    ((Scaled.const (1/3628800)).mul (Scaled.mono 10))
private theorem r78C10_rep : r78C10.Rep C10 :=
  ((r78C4_rep.subN ((Scaled.rep_const _).mul (Scaled.rep_mono 6))).addN
    ((Scaled.rep_const _).mul (Scaled.rep_mono 8))).subN
    ((Scaled.rep_const _).mul (Scaled.rep_mono 10))
private def r78C12 : Scaled := r78C10.addN ((Scaled.const (1/479001600)).mul (Scaled.mono 12))
private theorem r78C12_rep : r78C12.Rep C12 :=
  r78C10_rep.addN ((Scaled.rep_const _).mul (Scaled.rep_mono 12))
private def r78C2 : Scaled := r78one.subN ((Scaled.const (1/2)).mul (Scaled.mono 2))
private theorem r78C2_rep : r78C2.Rep C2 :=
  r78one_rep.subN ((Scaled.rep_const _).mul (Scaled.rep_mono 2))
private def r78S3 : Scaled := Scaled.var.subN ((Scaled.const (1/6)).mul (Scaled.mono 3))
private theorem r78S3_rep : r78S3.Rep S3 :=
  Scaled.rep_var.subN ((Scaled.rep_const _).mul (Scaled.rep_mono 3))

/-! Composition with affine maps and evaluation at rational points. -/

private theorem r78_comp_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s t : ℤ)
    {a b : ℚ} (hden : den≠0) (hab : (a+b)/2=num*s/den) (hba : (b-a)/2=num*t/den)
    {q : ℚ[X]} (hq : C ((a+b)/2)+C ((b-a)/2)*X=q) :
    (S.kcenter num den s t).Rep (p.comp q) := by
  have hc := hp.kcentered num den s t hden hab hba
  rwa [WholeIntervalPolynomial.centered,affine,hq] at hc

private theorem r78_rep_eval {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s : ℤ)
    {a : ℚ} (hden : den≠0) (ha : a=num*s/den) : (S.kcenter num den s 0).Rep (C (p.eval a)) := by
  have hc := hp.kcentered num den s 0 (a:=a) (b:=a) hden (by rw [← ha]; ring) (by simp)
  have he : WholeIntervalPolynomial.centered a a p=C (p.eval a) := by
    rw [WholeIntervalPolynomial.centered,affine,sub_self,zero_div,map_zero,zero_mul,add_zero,
      add_self_div_two,comp_C]
  rwa [he] at hc

/-- A represented constant, cut down to its constant entry. -/
private def r78head (S : Scaled) : Scaled := ⟨[S.l.getD 0 0],S.s⟩
private theorem r78head_rep {S : Scaled} {c : ℚ} (hS : S.Rep (C c)) : (r78head S).Rep (C c) := by
  unfold Scaled.Rep at *
  have h0 := congrArg (fun q => q.coeff 0) hS
  simp only [WholeIntervalPolynomial.Certificate.coeff_toPoly,coeff_C_mul,coeff_C_zero] at h0
  simp only [r78head,WholeIntervalPolynomial.Certificate.toPoly,mul_zero,add_zero,h0,map_mul]

/-- Composition with `X-C (1/10)`. -/
private def r78dv (S : Scaled) : Scaled := S.kcenter 1 10 (-1) 10
private theorem r78dv_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) :
    (r78dv S).Rep (p.comp (X-C v)) :=
  r78_comp_rep hp 1 10 (-1) 10 (a:=-11/10) (b:=9/10) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show ((-11/10:ℚ)+9/10)/2=-v by norm_num [v],
      show ((9/10:ℚ)-(-11/10))/2=1 by norm_num,map_neg,map_one]; ring)
/-- Composition with `X-C (1/4)`. -/
private def r78du (S : Scaled) : Scaled := S.kcenter 1 4 (-1) 4
private theorem r78du_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) :
    (r78du S).Rep (p.comp (X-C u)) :=
  r78_comp_rep hp 1 4 (-1) 4 (a:=-5/4) (b:=3/4) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show ((-5/4:ℚ)+3/4)/2=-u by norm_num [u],
      show ((3/4:ℚ)-(-5/4))/2=1 by norm_num,map_neg,map_one]; ring)
/-- Composition with `C (1/10)-X`. -/
private def r78dr (S : Scaled) : Scaled := S.kcenter 1 10 1 (-10)
private theorem r78dr_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) :
    (r78dr S).Rep (p.comp (C v-X)) :=
  r78_comp_rep hp 1 10 1 (-10) (a:=11/10) (b:=-9/10) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show ((11/10:ℚ)+-9/10)/2=v by norm_num [v],
      show ((-9/10:ℚ)-11/10)/2=-1 by norm_num,map_neg,map_one]; ring)

/-! The negative-DE families. -/

private def r78DL : Scaled := Scaled.var.subN (Scaled.const L)
private theorem r78DL_rep : r78DL.Rep (X-C L) := Scaled.rep_var.subN (Scaled.rep_const _)
private def r78t : Scaled := (Scaled.const (15/8)).mul r78DL
private theorem r78t_rep : r78t.Rep NegativeDEPositiveTD.Certificate.t :=
  (Scaled.rep_const _).mul r78DL_rep

private def r78k : Family → Scaled
  | .low => ((Scaled.const (6708/10000)).addN ((Scaled.const (3/20)).mul r78DL)).addN
      ((Scaled.const 4).mul (r78DL.pow 2))
  | .high => ((((Scaled.const (670158/1000000)).addN ((Scaled.const (113718/1000000)).mul r78t)).addN
      ((Scaled.const (6506/1000000)).mul (r78t.pow 2))).addN
      ((Scaled.const (9026/1000000)).mul (r78t.pow 3))).addN
      ((Scaled.const (1/1000)).mul (r78t.pow 4))
private theorem r78k_rep : ∀ f, (r78k f).Rep (NegativeDEPositiveTD.Certificate.k f)
  | .low => ((Scaled.rep_const _).addN ((Scaled.rep_const _).mul r78DL_rep)).addN
      ((Scaled.rep_const _).mul (r78DL_rep.pow 2))
  | .high => ((((Scaled.rep_const _).addN ((Scaled.rep_const _).mul r78t_rep)).addN
      ((Scaled.rep_const _).mul (r78t_rep.pow 2))).addN
      ((Scaled.rep_const _).mul (r78t_rep.pow 3))).addN
      ((Scaled.rep_const _).mul (r78t_rep.pow 4))
private def r78l : Family → Scaled
  | .low => ((Scaled.const (10073/10000)).subN ((Scaled.const (17/10)).mul r78DL)).addN
      ((Scaled.const (11/5)).mul (r78DL.pow 2))
  | .high => (((Scaled.const (1005069/1000000)).subN ((Scaled.const (146411/1000000)).mul r78t)).subN
      ((Scaled.const (157739/1000000)).mul (r78t.pow 2))).addN
      ((Scaled.const (162815/1000000)).mul (r78t.pow 3))
private theorem r78l_rep : ∀ f, (r78l f).Rep (NegativeDEPositiveTD.Certificate.l f)
  | .low => ((Scaled.rep_const _).subN ((Scaled.rep_const _).mul r78DL_rep)).addN
      ((Scaled.rep_const _).mul (r78DL_rep.pow 2))
  | .high => (((Scaled.rep_const _).subN ((Scaled.rep_const _).mul r78t_rep)).subN
      ((Scaled.rep_const _).mul (r78t_rep.pow 2))).addN
      ((Scaled.rep_const _).mul (r78t_rep.pow 3))
private def r78c : Family → Scaled
  | .low => ((Scaled.const (10389/10000)).subN ((Scaled.const (69/20)).mul r78DL)).addN
      ((Scaled.const 9).mul (r78DL.pow 2))
  | .high => (((Scaled.const (1021248/1000000)).subN ((Scaled.const (168873/1000000)).mul r78t)).subN
      ((Scaled.const (165381/1000000)).mul (r78t.pow 2))).addN
      ((Scaled.const (175944/1000000)).mul (r78t.pow 3))
private theorem r78c_rep : ∀ f, (r78c f).Rep (NegativeDEPositiveTD.Certificate.c f)
  | .low => ((Scaled.rep_const _).subN ((Scaled.rep_const _).mul r78DL_rep)).addN
      ((Scaled.rep_const _).mul (r78DL_rep.pow 2))
  | .high => (((Scaled.rep_const _).subN ((Scaled.rep_const _).mul r78t_rep)).subN
      ((Scaled.rep_const _).mul (r78t_rep.pow 2))).addN
      ((Scaled.rep_const _).mul (r78t_rep.pow 3))

private def r78J0 : Scaled :=
  ((Scaled.const (1/2)).mul (r78C10.subN r78one)).addN
    ((Scaled.const (1/2-NegativeDEPositiveTD.Certificate.abar)).mul r78S9)
private theorem r78J0_rep : r78J0.Rep J0 :=
  ((Scaled.rep_const _).mul (r78C10_rep.subN r78one_rep)).addN ((Scaled.rep_const _).mul r78S9_rep)
private def r78J1 : Scaled := r78J0.subN ((Scaled.const (151/500)).mul (r78DL.pow 6))
private theorem r78J1_rep : r78J1.Rep J1 :=
  r78J0_rep.subN ((Scaled.rep_const _).mul (r78DL_rep.pow 6))

private def r78mLo : Family → Split → Scaled
  | f,.atT => (r78c f).mul (r78C10.addN ((Scaled.const etaQ).mul r78S11))
  | f,.atA => r78c f
private theorem r78mLo_rep : ∀ f e,
    (r78mLo f e).Rep (NegativeDEPositiveTD.Certificate.mLo f e)
  | f,.atT => (r78c_rep f).mul (r78C10_rep.addN ((Scaled.rep_const _).mul r78S11_rep))
  | f,.atA => r78c_rep f
private def r78mHi : Family → Split → Scaled
  | f,.atT => (r78c f).mul (r78C12.addN ((Scaled.const etaQ).mul r78S9))
  | f,.atA => r78c f
private theorem r78mHi_rep : ∀ f e,
    (r78mHi f e).Rep (NegativeDEPositiveTD.Certificate.mHi f e)
  | f,.atT => (r78c_rep f).mul (r78C12_rep.addN ((Scaled.rep_const _).mul r78S9_rep))
  | f,.atA => r78c_rep f
private def r78mu : Family → Split → Scaled
  | .low,.atT => (r78c .low).mul (r78C2.addN ((Scaled.const etaQ).mul Scaled.var))
  | .high,.atT => (r78c .high).mul (r78C4.addN ((Scaled.const etaQ).mul r78S5))
  | .low,.atA => r78c .low
  | .high,.atA => r78c .high
private theorem r78mu_rep : ∀ f e,
    (r78mu f e).Rep (NegativeDEPositiveTD.Certificate.mu f e)
  | .low,.atT => (r78c_rep .low).mul (r78C2_rep.addN ((Scaled.rep_const _).mul Scaled.rep_var))
  | .high,.atT => (r78c_rep .high).mul (r78C4_rep.addN ((Scaled.rep_const _).mul r78S5_rep))
  | .low,.atA => r78c_rep .low
  | .high,.atA => r78c_rep .high

private def r78lowE : Split → Scaled
  | .atT => (((((Scaled.const 2).mul (r78k .low)).addN ((Scaled.const 3).mul (r78l .low))).addN
      ((Scaled.const (3/2)).mul (r78mLo .low .atT))).addN (Scaled.const (5/2))).addN
      (((Scaled.const (1/2)).mul (r78c .low)).mul ((r78one.addN r78C10).addN r78S11)) |>.subN
      (((r78c .low).mul (Scaled.const sigmabar)).mul r78S9)
  | .atA => (((((Scaled.const 2).mul (r78k .low)).addN ((Scaled.const 3).mul (r78l .low))).addN
      ((Scaled.const (5/2)).mul (r78c .low))).addN (Scaled.const (5/2))).addN
      ((r78l .low).mul r78J0)
private theorem r78lowE_rep : ∀ e, (r78lowE e).Rep (NegativeDEPositiveTD.Certificate.lowE e)
  | .atT => (((((Scaled.rep_const _).mul (r78k_rep .low)).addN
      ((Scaled.rep_const _).mul (r78l_rep .low))).addN
      ((Scaled.rep_const _).mul (r78mLo_rep .low .atT))).addN (Scaled.rep_const _)).addN
      (((Scaled.rep_const _).mul (r78c_rep .low)).mul ((r78one_rep.addN r78C10_rep).addN r78S11_rep))
      |>.subN (((r78c_rep .low).mul (Scaled.rep_const _)).mul r78S9_rep)
  | .atA => (((((Scaled.rep_const _).mul (r78k_rep .low)).addN
      ((Scaled.rep_const _).mul (r78l_rep .low))).addN
      ((Scaled.rep_const _).mul (r78c_rep .low))).addN (Scaled.rep_const _)).addN
      ((r78l_rep .low).mul r78J0_rep)
private def r78lowB (e : Split) : Scaled :=
  (r78lowE e).subN ((Scaled.const cbar).mul (r78one.addN (r78c .low)))
private theorem r78lowB_rep (e : Split) : (r78lowB e).Rep (NegativeDEPositiveTD.Certificate.lowB e) :=
  (r78lowE_rep e).subN ((Scaled.rep_const _).mul (r78one_rep.addN (r78c_rep .low)))
private def r78highB : Split → Scaled
  | .atT => ((((((Scaled.const 2).mul (r78k .high)).addN ((Scaled.const 3).mul (r78l .high))).addN
      ((Scaled.const (3/2)).mul (r78mLo .high .atT))).addN
      ((Scaled.const (1/2)).mul (r78c .high))).addN (Scaled.const 3)).addN
      (((Scaled.const (1/2)).mul (r78c .high)).mul ((r78one.addN r78C10).addN r78S11)) |>.subN
      (((r78c .high).mul (Scaled.const sigmabar)).mul r78S9)
  | .atA => ((((Scaled.const 2).mul (r78k .high)).addN ((Scaled.const 3).mul (r78l .high))).addN
      ((Scaled.const 3).mul (r78c .high))).addN (Scaled.const 3) |>.addN ((r78l .high).mul r78J1)
private theorem r78highB_rep : ∀ e, (r78highB e).Rep (NegativeDEPositiveTD.Certificate.highB e)
  | .atT => ((((((Scaled.rep_const _).mul (r78k_rep .high)).addN
      ((Scaled.rep_const _).mul (r78l_rep .high))).addN
      ((Scaled.rep_const _).mul (r78mLo_rep .high .atT))).addN
      ((Scaled.rep_const _).mul (r78c_rep .high))).addN (Scaled.rep_const _)).addN
      (((Scaled.rep_const _).mul (r78c_rep .high)).mul ((r78one_rep.addN r78C10_rep).addN r78S11_rep))
      |>.subN (((r78c_rep .high).mul (Scaled.rep_const _)).mul r78S9_rep)
  | .atA => ((((Scaled.rep_const _).mul (r78k_rep .high)).addN
      ((Scaled.rep_const _).mul (r78l_rep .high))).addN
      ((Scaled.rep_const _).mul (r78c_rep .high))).addN (Scaled.rep_const _)
      |>.addN ((r78l_rep .high).mul r78J1_rep)

private def r78PH (f : Family) : Scaled := r78one.addN ((r78k f).pow 2)
private theorem r78PH_rep (f : Family) : (r78PH f).Rep (NegativeDEPositiveTD.Certificate.PH f) :=
  r78one_rep.addN ((r78k_rep f).pow 2)
private def r78PG (f : Family) : Scaled := ((r78k f).pow 2).addN ((r78l f).pow 2)
private theorem r78PG_rep (f : Family) : (r78PG f).Rep (NegativeDEPositiveTD.Certificate.PG f) :=
  ((r78k_rep f).pow 2).addN ((r78l_rep f).pow 2)
private def r78PB (f : Family) (e : Split) : Scaled := ((r78mHi f e).ksq).addN ((r78l f).pow 2)
private theorem r78PB_rep (f : Family) (e : Split) :
    (r78PB f e).Rep (NegativeDEPositiveTD.Certificate.PB f e) :=
  ((r78mHi_rep f e).ksq).addN ((r78l_rep f).pow 2)
private def r78PD (f : Family) : Scaled := r78one.addN ((r78c f).pow 2)
private theorem r78PD_rep (f : Family) : (r78PD f).Rep (NegativeDEPositiveTD.Certificate.PD f) :=
  r78one_rep.addN ((r78c_rep f).pow 2)
private def r78RH : Family → Scaled
  | .low => (Scaled.const (41/50)).addN ((Scaled.const (143/250)).mul (r78k .low))
  | .high => (Scaled.const (4/5)).addN ((Scaled.const (3/5)).mul (r78k .high))
private theorem r78RH_rep : ∀ f, (r78RH f).Rep (NegativeDEPositiveTD.Certificate.RH f)
  | .low => (Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r78k_rep .low))
  | .high => (Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r78k_rep .high))
private def r78RG : Family → Scaled
  | .low => ((Scaled.const (11/20)).mul (r78k .low)).addN ((Scaled.const (167/200)).mul (r78l .low))
  | .high => ((Scaled.const (31/50)).mul (r78k .high)).addN
      ((Scaled.const (3923/5000)).mul (r78l .high))
private theorem r78RG_rep : ∀ f, (r78RG f).Rep (NegativeDEPositiveTD.Certificate.RG f)
  | .low => ((Scaled.rep_const _).mul (r78k_rep .low)).addN ((Scaled.rep_const _).mul (r78l_rep .low))
  | .high => ((Scaled.rep_const _).mul (r78k_rep .high)).addN
      ((Scaled.rep_const _).mul (r78l_rep .high))
private def r78RB (f : Family) (e : Split) : Scaled :=
  if f=.low then ((Scaled.const (729/1000)).mul (r78mu f e)).addN
    ((Scaled.const (1369/2000)).mul (r78l f))
  else (Scaled.const (7071/10000)).mul ((r78l f).addN (r78mu f e))
private theorem r78RB_rep (f : Family) (e : Split) :
    (r78RB f e).Rep (NegativeDEPositiveTD.Certificate.RB f e) :=
  Scaled.Rep.ite (((Scaled.rep_const _).mul (r78mu_rep f e)).addN
    ((Scaled.rep_const _).mul (r78l_rep f)))
    ((Scaled.rep_const _).mul ((r78l_rep f).addN (r78mu_rep f e)))
private def r78RD : Scaled := (Scaled.const (18/25)).addN ((Scaled.const (347/500)).mul (r78c .high))
private theorem r78RD_rep : r78RD.Rep NegativeDEPositiveTD.Certificate.RD :=
  (Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r78c_rep .high))
private def r78qStar : Scaled :=
  (r78l .high).addN ((Scaled.const (3/20)).mul ((Scaled.const h).subN Scaled.var))
private theorem r78qStar_rep : r78qStar.Rep NegativeDEPositiveTD.Certificate.qStar :=
  (r78l_rep .high).addN ((Scaled.rep_const _).mul ((Scaled.rep_const _).subN Scaled.rep_var))

/-! The EH gain. -/

private def r78gPoly : Scaled :=
  ((Scaled.const K).mul r78S11).addN ((Scaled.const beta).mul (r78C10.subN r78one))
private theorem r78gPoly_rep : r78gPoly.Rep gPoly :=
  ((Scaled.rep_const _).mul r78S11_rep).addN ((Scaled.rep_const _).mul (r78C10_rep.subN r78one_rep))
private def r78GPoly : Scaled := ((Scaled.const p).mul r78gPoly).subN (Scaled.const (11/50000))
private theorem r78GPoly_rep : r78GPoly.Rep GPoly :=
  ((Scaled.rep_const _).mul r78gPoly_rep).subN (Scaled.rep_const _)
private theorem r78_gStar_eval (s : ℚ) : gPoly.eval s=gStar s := by
  simp [gPoly,gStar]
private theorem r78_GStar_eval (s : ℚ) : GPoly.eval s=GStar s := by
  simp [GPoly,GStar,r78_gStar_eval]
private def r78gStarV : Scaled := r78head (r78gPoly.kcenter 1 10 1 0)
private theorem r78gStarV_rep : r78gStarV.Rep (C (gStar v)) := by
  have h := r78head_rep (r78_rep_eval r78gPoly_rep 1 10 1 (a:=v) (by norm_num) (by norm_num [v]))
  rwa [r78_gStar_eval] at h
private def r78GStarV : Scaled := r78head (r78GPoly.kcenter 1 10 1 0)
private theorem r78GStarV_rep : r78GStarV.Rep (C (GStar v)) := by
  have h := r78head_rep (r78_rep_eval r78GPoly_rep 1 10 1 (a:=v) (by norm_num) (by norm_num [v]))
  rwa [r78_GStar_eval] at h
private def r78GStarU : Scaled := r78head (r78GPoly.kcenter 1 4 1 0)
private theorem r78GStarU_rep : r78GStarU.Rep (C (GStar u)) := by
  have h := r78head_rep (r78_rep_eval r78GPoly_rep 1 4 1 (a:=u) (by norm_num) (by norm_num [u]))
  rwa [r78_GStar_eval] at h

/-! The small-error numerators. -/

private def r78smallP (r : SmallCase) (e : Split) : Fin 4 → Scaled :=
  let f := smallFamily r
  ![(r78PH f).subN (if r=.lowH ∨ r=.highH then
        ((Scaled.const 2).mul (r78k f)).mul (r78dv r78S11) else r78Z),
    (r78PG f).subN (if r=.highG then
        (((Scaled.const 2).mul (r78k f)).mul (r78l f)).mul (r78dv r78S11) else r78Z),
    (r78PB f e).subN (if r=.highB then
        (((Scaled.const 2).mul (r78l f)).mul (r78mLo f e)).kmul (r78dv r78S11) else r78Z),
    if f=.low then r78Z else r78PD f]
private theorem r78smallP_rep (r : SmallCase) (e : Split) (i : Fin 4) :
    (r78smallP r e i).Rep (smallP r e i) := by
  fin_cases i
  · exact (r78PH_rep _).subN (Scaled.Rep.ite
      (((Scaled.rep_const _).mul (r78k_rep _)).mul (r78dv_rep r78S11_rep)) r78Z_rep)
  · exact (r78PG_rep _).subN (Scaled.Rep.ite
      ((((Scaled.rep_const _).mul (r78k_rep _)).mul (r78l_rep _)).mul (r78dv_rep r78S11_rep)) r78Z_rep)
  · exact (r78PB_rep _ _).subN (Scaled.Rep.ite
      ((((Scaled.rep_const _).mul (r78l_rep _)).mul (r78mLo_rep _ _)).kmul (r78dv_rep r78S11_rep))
      r78Z_rep)
  · exact Scaled.Rep.ite r78Z_rep (r78PD_rep _)

private def r78smallMass (r : SmallCase) (e : Split) : Fin 4 → Scaled :=
  let f := smallFamily r
  ![if r=.lowH then ((Scaled.const (89/100)).mul (r78dv r78C2)).addN
        ((Scaled.const (57/125)).mul ((r78k f).subN (r78dv r78S3)))
      else if r=.highH then ((Scaled.const (93/100)).mul (r78dv r78C4)).addN
        ((Scaled.const (919/2500)).mul ((r78k f).subN (r78dv r78S5)))
      else r78RH f,
    if r=.highG then (((Scaled.const (93/100)).mul (r78l f)).mul (r78dv r78C4)).addN
        ((Scaled.const (919/2500)).mul ((r78k f).subN ((r78l f).mul (r78dv r78S5))))
      else r78RG f,
    if r=.highB then (((Scaled.const (83/100)).mul (r78l f)).mul (r78dv r78C4)).addN
        ((Scaled.const (14/25)).mul ((r78mu f e).subN ((r78l f).mul (r78dv r78S5))))
      else r78RB f e,
    if f=.low then r78one else r78RD]
private theorem r78smallMass_rep (r : SmallCase) (e : Split) (i : Fin 4) :
    (r78smallMass r e i).Rep (smallMass r e i) := by
  fin_cases i
  · exact Scaled.Rep.ite (((Scaled.rep_const _).mul (r78dv_rep r78C2_rep)).addN
        ((Scaled.rep_const _).mul ((r78k_rep _).subN (r78dv_rep r78S3_rep))))
      (Scaled.Rep.ite (((Scaled.rep_const _).mul (r78dv_rep r78C4_rep)).addN
        ((Scaled.rep_const _).mul ((r78k_rep _).subN (r78dv_rep r78S5_rep)))) (r78RH_rep _))
  · exact Scaled.Rep.ite ((((Scaled.rep_const _).mul (r78l_rep _)).mul (r78dv_rep r78C4_rep)).addN
        ((Scaled.rep_const _).mul ((r78k_rep _).subN ((r78l_rep _).mul (r78dv_rep r78S5_rep)))))
      (r78RG_rep _)
  · exact Scaled.Rep.ite ((((Scaled.rep_const _).mul (r78l_rep _)).mul (r78dv_rep r78C4_rep)).addN
        ((Scaled.rep_const _).mul ((r78mu_rep _ _).subN ((r78l_rep _).mul (r78dv_rep r78S5_rep)))))
      (r78RB_rep _ _)
  · exact Scaled.Rep.ite r78one_rep r78RD_rep

private def r78smallB (r : SmallCase) (e : Split) : Scaled :=
  if smallFamily r=.low then r78lowB e else r78highB e
private theorem r78smallB_rep (r : SmallCase) (e : Split) : (r78smallB r e).Rep
    (if smallFamily r=.low then NegativeDEPositiveTD.Certificate.lowB e
      else NegativeDEPositiveTD.Certificate.highB e) :=
  Scaled.Rep.ite (r78lowB_rep e) (r78highB_rep e)
private def r78smallNonrad : SmallCase → Split → Scaled
  | .lowZero,e => (r78smallB .lowZero e).addN r78gPoly
  | .lowH,e => (((r78smallB .lowH e).addN r78gStarV).addN (r78dv r78C10)).subN r78one
  | .highH,e => (((r78smallB .highH e).addN r78gStarV).addN (r78dv r78C10)).subN r78one
  | .highG,e => ((r78smallB .highG e).addN r78gStarV).addN
      ((r78l .high).mul ((r78dv r78C10).subN r78one))
  | .highB,e => ((r78smallB .highB e).addN r78gStarV).addN
      (r78qStar.mul ((r78dv r78C10).subN r78one))
private theorem r78smallNonrad_rep : ∀ r e, (r78smallNonrad r e).Rep (smallNonradical r e)
  | .lowZero,e => (r78smallB_rep .lowZero e).addN r78gPoly_rep
  | .lowH,e => (((r78smallB_rep .lowH e).addN r78gStarV_rep).addN (r78dv_rep r78C10_rep)).subN r78one_rep
  | .highH,e => (((r78smallB_rep .highH e).addN r78gStarV_rep).addN (r78dv_rep r78C10_rep)).subN r78one_rep
  | .highG,e => ((r78smallB_rep .highG e).addN r78gStarV_rep).addN
      ((r78l_rep .high).mul ((r78dv_rep r78C10_rep).subN r78one_rep))
  | .highB,e => ((r78smallB_rep .highB e).addN r78gStarV_rep).addN
      (r78qStar_rep.mul ((r78dv_rep r78C10_rep).subN r78one_rep))

private def r78smallNum (r : SmallCase) (e : Split) : Scaled :=
  if smallFamily r=.low then
    Scaled.num3 Rbar (r78smallNonrad r e) (r78smallP r e 0) (r78smallP r e 1) (r78smallP r e 2)
      (r78smallMass r e 0) (r78smallMass r e 1) (r78smallMass r e 2)
  else Scaled.num4 Rbar (r78smallNonrad r e) (r78smallP r e 0) (r78smallP r e 1) (r78smallP r e 2)
      (r78smallP r e 3) (r78smallMass r e 0) (r78smallMass r e 1) (r78smallMass r e 2)
      (r78smallMass r e 3)
private theorem r78smallNum_rep (r : SmallCase) (e : Split) :
    (r78smallNum r e).Rep (smallNumerator r e) :=
  Scaled.Rep.ite
    (r78num3_rep (r78smallNonrad_rep r e) (r78smallP_rep r e 0) (r78smallP_rep r e 1)
      (r78smallP_rep r e 2) (r78smallMass_rep r e 0) (r78smallMass_rep r e 1) (r78smallMass_rep r e 2))
    (r78num4_rep (r78smallNonrad_rep r e) (r78smallP_rep r e 0) (r78smallP_rep r e 1)
      (r78smallP_rep r e 2) (r78smallP_rep r e 3) (r78smallMass_rep r e 0) (r78smallMass_rep r e 1)
      (r78smallMass_rep r e 2) (r78smallMass_rep r e 3))

/-! The remaining-error numerators. -/

private def r78farK : Family → Scaled
  | .low => Scaled.const (121/200)
  | .high => (Scaled.const (101/200)).addN ((Scaled.const (2/5)).mul Scaled.var)
private theorem r78farK_rep : ∀ f, (r78farK f).Rep (farK f)
  | .low => Scaled.rep_const _
  | .high => (Scaled.rep_const _).addN ((Scaled.rep_const _).mul Scaled.rep_var)
private def r78farL : Family → Scaled
  | .low => r78one.subN ((Scaled.const (9/25)).mul Scaled.var)
  | .high => (Scaled.const (381/400)).subN ((Scaled.const (17/100)).mul Scaled.var)
private theorem r78farL_rep : ∀ f, (r78farL f).Rep (farL f)
  | .low => r78one_rep.subN ((Scaled.rep_const _).mul Scaled.rep_var)
  | .high => (Scaled.rep_const _).subN ((Scaled.rep_const _).mul Scaled.rep_var)
private def r78farC : Family → Scaled
  | .low => (Scaled.const (111/100)).subN ((Scaled.const (77/100)).mul Scaled.var)
  | .high => (Scaled.const (1929/2000)).subN ((Scaled.const (47/250)).mul Scaled.var)
private theorem r78farC_rep : ∀ f, (r78farC f).Rep (farC f)
  | .low => (Scaled.rep_const _).subN ((Scaled.rep_const _).mul Scaled.rep_var)
  | .high => (Scaled.rep_const _).subN ((Scaled.rep_const _).mul Scaled.rep_var)
private def r78farMLo (f : Family) : Split → Scaled
  | .atT => (r78farC f).mul (r78C10.addN ((Scaled.const etaQ).mul r78S11))
  | .atA => r78farC f
private theorem r78farMLo_rep (f : Family) : ∀ e, (r78farMLo f e).Rep (farMLo f e)
  | .atT => (r78farC_rep f).mul (r78C10_rep.addN ((Scaled.rep_const _).mul r78S11_rep))
  | .atA => r78farC_rep f
private def r78farMHi (f : Family) : Split → Scaled
  | .atT => (r78farC f).mul (r78C12.addN ((Scaled.const etaQ).mul r78S9))
  | .atA => r78farC f
private theorem r78farMHi_rep (f : Family) : ∀ e, (r78farMHi f e).Rep (farMHi f e)
  | .atT => (r78farC_rep f).mul (r78C12_rep.addN ((Scaled.rep_const _).mul r78S9_rep))
  | .atA => r78farC_rep f
private def r78farMu (f : Family) : Split → Scaled
  | .atT => (r78farC f).mul (r78C4.addN ((Scaled.const etaQ).mul r78S5))
  | .atA => r78farC f
private theorem r78farMu_rep (f : Family) : ∀ e, (r78farMu f e).Rep (farMu f e)
  | .atT => (r78farC_rep f).mul (r78C4_rep.addN ((Scaled.rep_const _).mul r78S5_rep))
  | .atA => r78farC_rep f
private def r78farB (f : Family) : Split → Scaled
  | .atT => ((((((Scaled.const 2).mul (r78farK f)).addN ((Scaled.const 3).mul (r78farL f))).addN
      ((Scaled.const (3/2)).mul (r78farMLo f .atT))).addN
      ((Scaled.const (1/2)).mul (r78farC f))).addN (Scaled.const 3)).addN
      (((Scaled.const (1/2)).mul (r78farC f)).mul ((r78one.addN r78C10).addN r78S11)) |>.subN
      (((r78farC f).mul (Scaled.const sigmabar)).mul r78S9)
  | .atA => ((((Scaled.const 2).mul (r78farK f)).addN ((Scaled.const 3).mul (r78farL f))).addN
      ((Scaled.const 3).mul (r78farC f))).addN (Scaled.const 3) |>.addN
      ((r78farL f).mul (if f=.low then r78J0 else r78J1))
private theorem r78farB_rep (f : Family) : ∀ e, (r78farB f e).Rep (farB f e)
  | .atT => ((((((Scaled.rep_const _).mul (r78farK_rep f)).addN
      ((Scaled.rep_const _).mul (r78farL_rep f))).addN
      ((Scaled.rep_const _).mul (r78farMLo_rep f .atT))).addN
      ((Scaled.rep_const _).mul (r78farC_rep f))).addN (Scaled.rep_const _)).addN
      (((Scaled.rep_const _).mul (r78farC_rep f)).mul ((r78one_rep.addN r78C10_rep).addN r78S11_rep))
      |>.subN (((r78farC_rep f).mul (Scaled.rep_const _)).mul r78S9_rep)
  | .atA => ((((Scaled.rep_const _).mul (r78farK_rep f)).addN
      ((Scaled.rep_const _).mul (r78farL_rep f))).addN
      ((Scaled.rep_const _).mul (r78farC_rep f))).addN (Scaled.rep_const _)
      |>.addN ((r78farL_rep f).mul (Scaled.Rep.ite r78J0_rep r78J1_rep))
private def r78farPH (f : Family) : Scaled := r78one.addN ((r78farK f).pow 2)
private theorem r78farPH_rep (f : Family) : (r78farPH f).Rep (farPH f) :=
  r78one_rep.addN ((r78farK_rep f).pow 2)
private def r78farPG (f : Family) : Scaled := ((r78farK f).pow 2).addN ((r78farL f).pow 2)
private theorem r78farPG_rep (f : Family) : (r78farPG f).Rep (farPG f) :=
  ((r78farK_rep f).pow 2).addN ((r78farL_rep f).pow 2)
private def r78farPB (f : Family) (e : Split) : Scaled := ((r78farMHi f e).ksq).addN ((r78farL f).pow 2)
private theorem r78farPB_rep (f : Family) (e : Split) : (r78farPB f e).Rep (farPB f e) :=
  ((r78farMHi_rep f e).ksq).addN ((r78farL_rep f).pow 2)
private def r78farPD (f : Family) : Scaled := r78one.addN ((r78farC f).pow 2)
private theorem r78farPD_rep (f : Family) : (r78farPD f).Rep (farPD f) :=
  r78one_rep.addN ((r78farC_rep f).pow 2)
private def r78farRH (f : Family) : Scaled :=
  (Scaled.const (4/5)).addN ((Scaled.const (3/5)).mul (r78farK f))
private theorem r78farRH_rep (f : Family) : (r78farRH f).Rep (farRH f) :=
  (Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r78farK_rep f))
private def r78farRG (f : Family) : Scaled :=
  ((Scaled.const (31/50)).mul (r78farK f)).addN ((Scaled.const (3923/5000)).mul (r78farL f))
private theorem r78farRG_rep (f : Family) : (r78farRG f).Rep (farRG f) :=
  ((Scaled.rep_const _).mul (r78farK_rep f)).addN ((Scaled.rep_const _).mul (r78farL_rep f))
private def r78farRB (f : Family) (e : Split) : Scaled :=
  (Scaled.const (7071/10000)).mul ((r78farL f).addN (r78farMu f e))
private theorem r78farRB_rep (f : Family) (e : Split) : (r78farRB f e).Rep (farRB f e) :=
  (Scaled.rep_const _).mul ((r78farL_rep f).addN (r78farMu_rep f e))
private def r78farRD (f : Family) : Scaled :=
  (Scaled.const (18/25)).addN ((Scaled.const (347/500)).mul (r78farC f))
private theorem r78farRD_rep (f : Family) : (r78farRD f).Rep (farRD f) :=
  (Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r78farC_rep f))
private def r78farQStar : Scaled :=
  (r78farL .high).addN ((Scaled.const (3/20)).mul ((Scaled.const h).subN Scaled.var))
private theorem r78farQStar_rep : r78farQStar.Rep farQStar :=
  (r78farL_rep .high).addN ((Scaled.rep_const _).mul ((Scaled.rep_const _).subN Scaled.rep_var))

/-- Composition with the EH shift of each far case. -/
private def r78dfar (r : FarCase) (S : Scaled) : Scaled :=
  if r=.lowUH ∨ r=.lowUB then r78dr S
  else if r=.highHu ∨ r=.highGu ∨ r=.highBu then r78du S else r78dv S
private theorem r78dfar_rep (r : FarCase) {S : Scaled} {q : ℚ[X]} (hS : S.Rep q) :
    (r78dfar r S).Rep (q.comp (farDelta r)) := by
  cases r
  · exact r78dr_rep hS
  · exact r78dr_rep hS
  · exact r78dv_rep hS
  · exact r78dv_rep hS
  · exact r78dv_rep hS
  · exact r78dv_rep hS
  · exact r78dv_rep hS
  · exact r78dv_rep hS
  · exact r78du_rep hS
  · exact r78du_rep hS
  · exact r78du_rep hS
private def r78farDelta (r : FarCase) : Scaled :=
  if r=.lowUH ∨ r=.lowUB then (Scaled.const v).subN Scaled.var
  else Scaled.var.subN (Scaled.const (farS r))
private theorem r78farDelta_rep (r : FarCase) : (r78farDelta r).Rep (farDelta r) :=
  Scaled.Rep.ite ((Scaled.rep_const _).subN Scaled.rep_var) (Scaled.rep_var.subN (Scaled.rep_const _))
private def r78GStarS (r : FarCase) : Scaled :=
  if r=.highHu ∨ r=.highGu ∨ r=.highBu then r78GStarU else r78GStarV
private theorem r78GStarS_rep (r : FarCase) : (r78GStarS r).Rep (C (GStar (farS r))) := by
  cases r
  iterate 8 exact r78GStarV_rep
  iterate 3 exact r78GStarU_rep

private def r78farP (r : FarCase) (e : Split) : Fin 4 → Scaled :=
  let f := farFamily r
  ![if r=.lowUH then (r78farPH f).addN (((Scaled.const 2).mul (r78farK f)).mul (r78dfar r r78S9))
      else (r78farPH f).subN (if farNegativeH r then
        ((Scaled.const 2).mul (r78farK f)).mul (r78dfar r r78S11) else r78Z),
    (r78farPG f).subN (if farNegativeG r then
      (((Scaled.const 2).mul (r78farK f)).mul (r78farL f)).mul (r78dfar r r78S11) else r78Z),
    if r=.lowUB then (r78farPB f e).addN
        ((((Scaled.const 2).mul (r78farL f)).mul (r78farMHi f e)).kmul (r78dfar r r78S9))
      else (r78farPB f e).subN (if farNegativeB r then
        (((Scaled.const 2).mul (r78farL f)).mul (r78farMLo f e)).kmul (r78dfar r r78S11) else r78Z),
    r78farPD f]
private theorem r78farP_rep (r : FarCase) (e : Split) (i : Fin 4) :
    (r78farP r e i).Rep (farP r e i) := by
  fin_cases i
  · exact Scaled.Rep.ite ((r78farPH_rep _).addN
        (((Scaled.rep_const _).mul (r78farK_rep _)).mul (r78dfar_rep r r78S9_rep)))
      ((r78farPH_rep _).subN (Scaled.Rep.ite
        (((Scaled.rep_const _).mul (r78farK_rep _)).mul (r78dfar_rep r r78S11_rep)) r78Z_rep))
  · exact (r78farPG_rep _).subN (Scaled.Rep.ite
      ((((Scaled.rep_const _).mul (r78farK_rep _)).mul (r78farL_rep _)).mul
        (r78dfar_rep r r78S11_rep)) r78Z_rep)
  · exact Scaled.Rep.ite ((r78farPB_rep _ _).addN
        ((((Scaled.rep_const _).mul (r78farL_rep _)).mul (r78farMHi_rep _ _)).kmul
          (r78dfar_rep r r78S9_rep)))
      ((r78farPB_rep _ _).subN (Scaled.Rep.ite
        ((((Scaled.rep_const _).mul (r78farL_rep _)).mul (r78farMLo_rep _ _)).kmul
          (r78dfar_rep r r78S11_rep)) r78Z_rep))
  · exact r78farPD_rep _

private def r78farMass (r : FarCase) (e : Split) : Fin 4 → Scaled :=
  let f := farFamily r
  ![if r=.lowUH then ((Scaled.const (209/250)).mul (r78dfar r r78C2)).addN
        ((Scaled.const (137/250)).mul ((r78farK f).addN (r78dfar r r78S3)))
      else if r=.lowVH then ((Scaled.const (89/100)).mul (r78dfar r r78C2)).addN
        ((Scaled.const (57/125)).mul ((r78farK f).subN (r78dfar r r78S3)))
      else if farNegativeH r then ((Scaled.const (47/50)).mul (r78dfar r r78C4)).addN
        ((Scaled.const (853/2500)).mul ((r78farK f).subN (r78dfar r r78S5)))
      else r78farRH f,
    if r=.lowVG then (((Scaled.const (89/100)).mul (r78farL f)).mul (r78dfar r r78C2)).addN
        ((Scaled.const (57/125)).mul ((r78farK f).subN ((r78farL f).mul (r78dfar r r78S3))))
      else if farNegativeG r then
        (((Scaled.const (179/200)).mul (r78farL f)).mul (r78dfar r r78C4)).addN
        ((Scaled.const (223/500)).mul ((r78farK f).subN ((r78farL f).mul (r78dfar r r78S5))))
      else r78farRG f,
    if r=.lowUB then (((Scaled.const (16/25)).mul (r78farL f)).mul (r78dfar r r78C2)).addN
        ((Scaled.const (96/125)).mul ((r78farMu f e).addN ((r78farL f).mul (r78dfar r r78S3))))
      else if farNegativeB r then
        (((Scaled.const (41/50)).mul (r78farL f)).mul (r78dfar r r78C4)).addN
        ((Scaled.const (143/250)).mul ((r78farMu f e).subN ((r78farL f).mul (r78dfar r r78S5))))
      else r78farRB f e,
    r78farRD f]
private theorem r78farMass_rep (r : FarCase) (e : Split) (i : Fin 4) :
    (r78farMass r e i).Rep (farMass r e i) := by
  fin_cases i
  · exact Scaled.Rep.ite (((Scaled.rep_const _).mul (r78dfar_rep r r78C2_rep)).addN
        ((Scaled.rep_const _).mul ((r78farK_rep _).addN (r78dfar_rep r r78S3_rep))))
      (Scaled.Rep.ite (((Scaled.rep_const _).mul (r78dfar_rep r r78C2_rep)).addN
        ((Scaled.rep_const _).mul ((r78farK_rep _).subN (r78dfar_rep r r78S3_rep))))
      (Scaled.Rep.ite (((Scaled.rep_const _).mul (r78dfar_rep r r78C4_rep)).addN
        ((Scaled.rep_const _).mul ((r78farK_rep _).subN (r78dfar_rep r r78S5_rep))))
        (r78farRH_rep _)))
  · exact Scaled.Rep.ite ((((Scaled.rep_const _).mul (r78farL_rep _)).mul (r78dfar_rep r r78C2_rep)).addN
        ((Scaled.rep_const _).mul ((r78farK_rep _).subN ((r78farL_rep _).mul (r78dfar_rep r r78S3_rep)))))
      (Scaled.Rep.ite ((((Scaled.rep_const _).mul (r78farL_rep _)).mul (r78dfar_rep r r78C4_rep)).addN
        ((Scaled.rep_const _).mul ((r78farK_rep _).subN ((r78farL_rep _).mul (r78dfar_rep r r78S5_rep)))))
        (r78farRG_rep _))
  · exact Scaled.Rep.ite ((((Scaled.rep_const _).mul (r78farL_rep _)).mul (r78dfar_rep r r78C2_rep)).addN
        ((Scaled.rep_const _).mul ((r78farMu_rep _ _).addN ((r78farL_rep _).mul (r78dfar_rep r r78S3_rep)))))
      (Scaled.Rep.ite ((((Scaled.rep_const _).mul (r78farL_rep _)).mul (r78dfar_rep r r78C4_rep)).addN
        ((Scaled.rep_const _).mul ((r78farMu_rep _ _).subN ((r78farL_rep _).mul (r78dfar_rep r r78S5_rep)))))
        (r78farRB_rep _ _))
  · exact r78farRD_rep _

private def r78farNonrad (r : FarCase) (e : Split) : Scaled :=
  let f := farFamily r
  if r=.lowZero then (r78farB f e).addN r78GPoly
  else ((r78farB f e).addN (r78GStarS r)).addN
    (if r=.lowUH then ((r78farK f).mul (((r78dfar r r78C10).addN (r78dfar r r78S11)).subN r78one)).subN
        ((Scaled.const epsilon).mul (r78farDelta r))
     else if r=.lowUB then
        ((r78farL f).mul (((r78dfar r r78C10).addN (r78dfar r r78S11)).subN r78one)).subN
        ((Scaled.const epsilon).mul (r78farDelta r))
     else (if farNegativeG r then r78farL f else if farNegativeB r then r78farQStar else r78one).mul
       ((r78dfar r r78C10).subN r78one))
private theorem r78farNonrad_rep (r : FarCase) (e : Split) :
    (r78farNonrad r e).Rep (farNonradical r e) :=
  Scaled.Rep.ite ((r78farB_rep _ e).addN r78GPoly_rep)
    (((r78farB_rep _ e).addN (r78GStarS_rep r)).addN
      (Scaled.Rep.ite (((r78farK_rep _).mul
          (((r78dfar_rep r r78C10_rep).addN (r78dfar_rep r r78S11_rep)).subN r78one_rep)).subN
          ((Scaled.rep_const _).mul (r78farDelta_rep r)))
        (Scaled.Rep.ite (((r78farL_rep _).mul
          (((r78dfar_rep r r78C10_rep).addN (r78dfar_rep r r78S11_rep)).subN r78one_rep)).subN
          ((Scaled.rep_const _).mul (r78farDelta_rep r)))
          ((Scaled.Rep.ite (r78farL_rep _) (Scaled.Rep.ite r78farQStar_rep r78one_rep)).mul
            ((r78dfar_rep r r78C10_rep).subN r78one_rep)))))

private def r78farNum (r : FarCase) (e : Split) : Scaled :=
  Scaled.num4 Rbar (r78farNonrad r e) (r78farP r e 0) (r78farP r e 1) (r78farP r e 2) (r78farP r e 3)
    (r78farMass r e 0) (r78farMass r e 1) (r78farMass r e 2) (r78farMass r e 3)
private theorem r78farNum_rep (r : FarCase) (e : Split) :
    (r78farNum r e).Rep (farNumerator r e) :=
  r78num4_rep (r78farNonrad_rep r e) (r78farP_rep r e 0) (r78farP_rep r e 1) (r78farP_rep r e 2)
    (r78farP_rep r e 3) (r78farMass_rep r e 0) (r78farMass_rep r e 1) (r78farMass_rep r e 2)
    (r78farMass_rep r e 3)

/-! Integer forms of the two reserve comparisons. -/

private theorem r78_lt {c : Scaled} {Z : ℤ} {ρ : ℚ} (n : ℤ) (d : ℕ) (hρ : ρ=n/d) (hd : 0<d)
    (hs : c.s≠0) (h : n*((c.s*2^c.l.length:ℕ):ℤ)<2*d*Z) :
    ρ<(Z:ℚ)/(c.s*2^c.l.length/2) := by
  have hS : (0:ℚ)<c.s*2^c.l.length/2 := WholeIntervalPolynomial.Certificate.scale_pos hs
  rw [hρ,div_lt_div_iff₀ (by exact_mod_cast hd) hS]
  have h' : ((n*((c.s*2^c.l.length:ℕ):ℤ):ℤ):ℚ)<((2*d*Z:ℤ):ℚ) := by exact_mod_cast h
  push_cast at h'
  linarith


private theorem r78_quad_core {B : ℕ → ℤ} {K : ℚ} {M : ℕ} {ρ : ℚ} (cnt : ℕ) (n : ℤ) (d : ℕ)
    (hK : K=M/2) (hM : 0<M) (hρ : ρ=n/d) (hd : 0<d) (h2 : 0<B 2)
    (h : 4*B 2*n*M<d*(8*B 2*(B 0-B 2-∑ j : Fin cnt,|B (j.val+3)|)-(B 1)^2)) :
    0<(fun j => (B j:ℚ)/K) 2 ∧ ρ<quadraticReserve (fun j => (B j:ℚ)/K) cnt := by
  have hM' : (0:ℚ)<M := by exact_mod_cast hM
  have hK0 : 0<K := by rw [hK]; linarith
  have hB2 : (0:ℚ)<B 2 := by exact_mod_cast h2
  refine ⟨div_pos hB2 hK0,?_⟩
  obtain ⟨T,hT⟩ : ∃T : ℚ,T=∑ j : Fin cnt,|(B (j.val+3):ℚ)| := ⟨_,rfl⟩
  have hsum : tailNorm (fun j => (B j:ℚ)/K) 3 cnt=T/K := by
    rw [tailNorm,hT,Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [abs_div,abs_of_pos hK0]
  unfold quadraticReserve
  rw [hsum]
  have e : (B 0:ℚ)/K-B 2/K-(B 1/K)^2/(8*(B 2/K))-T/K=
      (8*B 2*(B 0-B 2-T)-(B 1)^2)/(8*B 2*K) := by
    field_simp
    ring
  show ρ<(B 0:ℚ)/K-B 2/K-(B 1/K)^2/(8*(B 2/K))-T/K
  rw [e,hρ,div_lt_div_iff₀ (by exact_mod_cast hd) (by positivity)]
  have h' : ((4*B 2*n*M:ℤ):ℚ)<((d*(8*B 2*(B 0-B 2-∑ j : Fin cnt,|B (j.val+3)|)-(B 1)^2):ℤ):ℚ) := by
    exact_mod_cast h
  push_cast at h'
  rw [← hT] at h'
  rw [hK]
  linarith

private theorem r78_series_quad (c : ℕ → ℚ) (n : ℕ) :
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

/-- The Chebyshev quadratic part of an expansion, with its coefficients named `c`. -/
private theorem r78_quad_id {p : ℚ[X]} {D : ℕ} {c : ℕ → ℚ} (hc : coefficient D p=c) (hD : 2≤D)
    (hp : p=expansion D p) : p=C (c 0-c 2)+C (c 1)*X+C (2*c 2)*X^2+tail c 3 (D-2) := by
  obtain ⟨n,rfl⟩ : ∃ n,D=n+2 := ⟨D-2,by omega⟩
  rw [show n+2-2=n by omega,← hc]
  conv_lhs => rw [hp]
  exact r78_series_quad _ n

private theorem r78_I0 : (0+v:ℚ)/2=((1:ℕ):ℚ)*((1:ℤ):ℚ)/((20:ℕ):ℚ) ∧
    (v-0:ℚ)/2=((1:ℕ):ℚ)*((1:ℤ):ℚ)/((20:ℕ):ℚ) := by
  norm_num [v,u,L,h]

private theorem r78_I1 : (v+L:ℚ)/2=((1:ℕ):ℚ)*((4:ℤ):ℚ)/((30:ℕ):ℚ) ∧
    (L-v:ℚ)/2=((1:ℕ):ℚ)*((1:ℤ):ℚ)/((30:ℕ):ℚ) := by
  norm_num [v,u,L,h]

private theorem r78_I2 : (L+h:ℚ)/2=((1:ℕ):ℚ)*((13:ℤ):ℚ)/((30:ℕ):ℚ) ∧
    (h-L:ℚ)/2=((1:ℕ):ℚ)*((8:ℤ):ℚ)/((30:ℕ):ℚ) := by
  norm_num [v,u,L,h]

private theorem r78_I3 : (v+u:ℚ)/2=((1:ℕ):ℚ)*((7:ℤ):ℚ)/((40:ℕ):ℚ) ∧
    (u-v:ℚ)/2=((1:ℕ):ℚ)*((3:ℤ):ℚ)/((40:ℕ):ℚ) := by
  norm_num [v,u,L,h]

private theorem r78_I4 : (u+h:ℚ)/2=((1:ℕ):ℚ)*((19:ℤ):ℚ)/((40:ℕ):ℚ) ∧
    (h-u:ℚ)/2=((1:ℕ):ℚ)*((9:ℤ):ℚ)/((40:ℕ):ℚ) := by
  norm_num [v,u,L,h]

private theorem r78_ρ35 : (3/5:ℚ)=((3:ℤ):ℚ)/((5:ℕ):ℚ) := by norm_num

/-- One whole-interval certificate from its kernel-checked integer facts. -/
private theorem r78_cert {S : Scaled} {a b ρ : ℚ} {p : ℚ[X]} {D : ℕ} (num den : ℕ) (s t : ℤ)
    (hS : S.Rep p) (hden : den≠0) (hab : (a+b)/2=num*s/den ∧ (b-a)/2=num*t/den)
    (n : ℤ) (d : ℕ) (hρ : ρ=n/d) (hd : 0<d)
    (hk : (S.kcenter num den s t).s≠0 ∧ (S.kcenter num den s t).l.length≤D+1 ∧
      n*(((S.kcenter num den s t).s*2^(S.kcenter num den s t).l.length:ℕ):ℤ)<
        2*d*lowerZ D (fun j => (chebList (S.kcenter num den s t).l).getD j 0)) :
    centered a b p=expansion D (centered a b p) ∧ ρ<lowerOn D a b p := by
  have hc := hS.kcentered num den s t hden hab.1 hab.2
  exact ⟨hc.eq_expansion hk.1 hk.2.1,
    by rw [lowerOn_eq_of_rep hc hk.1 hk.2.1]; exact r78_lt n d hρ hd hk.1 hk.2.2⟩

/-! The kernel facts. The cases on one interval share their polynomials, so each interval is
one kernel evaluation, and the fact of each case is a projection of it. -/

set_option Elab.async false in
set_option maxRecDepth 1000000 in
private theorem r78g_S_lowZero :
    (((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).l.length ≤ smallDegree .lowZero .atA+1 ∧
    (8991:ℤ)*((((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).s*2^((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((100000:ℕ):ℤ)*lowerZ (smallDegree .lowZero .atA)
      (fun j => (chebList ((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l.length≤32+1 ∧ 0<(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 2 0 ∧
    4*(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 2 0*(183947:ℤ)*((((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).s*2^((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<
      ((10000000:ℕ):ℤ)*(8*(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 2 0*((chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 0 0-(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 2 0-
        ∑ j : Fin 30,|(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD (j.val+3) 0|)-((chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 1 0)^2)) := by
  decide +kernel

private theorem r78kSD_lowZero_atA : ((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).l.length ≤ smallDegree .lowZero .atA+1 ∧
    (8991:ℤ)*((((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).s*2^((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((100000:ℕ):ℤ)*lowerZ (smallDegree .lowZero .atA)
      (fun j => (chebList ((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.1

private theorem r78kSM_lowZero_atT_0 : ((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.2.1

private theorem r78kSM_lowZero_atT_1 : ((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.2.2.1

private theorem r78kSM_lowZero_atT_2 : ((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.2.2.2.1

private theorem r78kSM_lowZero_atT_3 : ((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.2.2.2.2.1

private theorem r78kSM_lowZero_atA_0 : ((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.2.2.2.2.2.1

private theorem r78kSM_lowZero_atA_1 : ((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.2.2.2.2.2.2.1

private theorem r78kSM_lowZero_atA_2 : ((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.2.2.2.2.2.2.2.1

private theorem r78kSM_lowZero_atA_3 : ((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.2.2.2.2.2.2.2.2.1

private theorem r78kSQ_lowZero : ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l.length≤32+1 ∧ 0<(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 2 0 ∧
    4*(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 2 0*(183947:ℤ)*((((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).s*2^((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<
      ((10000000:ℕ):ℤ)*(8*(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 2 0*((chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 0 0-(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 2 0-
        ∑ j : Fin 30,|(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD (j.val+3) 0|)-((chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 1 0)^2) := r78g_S_lowZero.2.2.2.2.2.2.2.2.2


set_option Elab.async false in
set_option maxRecDepth 1000000 in
private theorem r78g_S_lowH :
    (((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).l.length ≤ smallDegree .lowH .atA+1 ∧
    (94417:ℤ)*((((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).s*2^((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .lowH .atA)
      (fun j => (chebList ((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l.length≤33+1 ∧ 0<(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 2 0 ∧
    4*(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 2 0*(27740:ℤ)*((((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).s*2^((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<
      ((10000000:ℕ):ℤ)*(8*(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 2 0*((chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 0 0-(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 2 0-
        ∑ j : Fin 31,|(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD (j.val+3) 0|)-((chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 1 0)^2)) := by
  decide +kernel

private theorem r78kSD_lowH_atA : ((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).l.length ≤ smallDegree .lowH .atA+1 ∧
    (94417:ℤ)*((((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).s*2^((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .lowH .atA)
      (fun j => (chebList ((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.1

private theorem r78kSM_lowH_atT_0 : ((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.2.1

private theorem r78kSM_lowH_atT_1 : ((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.2.2.1

private theorem r78kSM_lowH_atT_2 : ((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.2.2.2.1

private theorem r78kSM_lowH_atT_3 : ((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.2.2.2.2.1

private theorem r78kSM_lowH_atA_0 : ((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.2.2.2.2.2.1

private theorem r78kSM_lowH_atA_1 : ((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.2.2.2.2.2.2.1

private theorem r78kSM_lowH_atA_2 : ((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.2.2.2.2.2.2.2.1

private theorem r78kSM_lowH_atA_3 : ((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.2.2.2.2.2.2.2.2.1

private theorem r78kSQ_lowH : ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l.length≤33+1 ∧ 0<(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 2 0 ∧
    4*(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 2 0*(27740:ℤ)*((((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).s*2^((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<
      ((10000000:ℕ):ℤ)*(8*(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 2 0*((chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 0 0-(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 2 0-
        ∑ j : Fin 31,|(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD (j.val+3) 0|)-((chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 1 0)^2) := r78g_S_lowH.2.2.2.2.2.2.2.2.2


set_option Elab.async false in
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 1000000 in
private theorem r78g_S_high :
    (((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highH .atT+1 ∧
    (8161:ℤ)*((((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highH .atT)
      (fun j => (chebList ((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highH .atA+1 ∧
    (7429:ℤ)*((((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highH .atA)
      (fun j => (chebList ((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highG .atT+1 ∧
    (49256:ℤ)*((((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highG .atT)
      (fun j => (chebList ((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highG .atA+1 ∧
    (45860:ℤ)*((((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highG .atA)
      (fun j => (chebList ((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highB .atT+1 ∧
    (344132:ℤ)*((((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highB .atT)
      (fun j => (chebList ((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highB .atA+1 ∧
    (923872:ℤ)*((((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highB .atA)
      (fun j => (chebList ((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).l).getD j 0)) := by
  decide +kernel

private theorem r78kSD_highH_atT : ((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highH .atT+1 ∧
    (8161:ℤ)*((((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highH .atT)
      (fun j => (chebList ((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.1

private theorem r78kSD_highH_atA : ((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highH .atA+1 ∧
    (7429:ℤ)*((((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highH .atA)
      (fun j => (chebList ((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.1

private theorem r78kSD_highG_atT : ((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highG .atT+1 ∧
    (49256:ℤ)*((((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highG .atT)
      (fun j => (chebList ((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.1

private theorem r78kSD_highG_atA : ((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highG .atA+1 ∧
    (45860:ℤ)*((((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highG .atA)
      (fun j => (chebList ((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.1

private theorem r78kSD_highB_atT : ((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highB .atT+1 ∧
    (344132:ℤ)*((((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highB .atT)
      (fun j => (chebList ((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.1

private theorem r78kSD_highB_atA : ((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highB .atA+1 ∧
    (923872:ℤ)*((((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highB .atA)
      (fun j => (chebList ((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.1

private theorem r78kSM_highH_atT_0 : ((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.1

private theorem r78kSM_highH_atT_1 : ((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.1

private theorem r78kSM_highH_atT_2 : ((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highH_atT_3 : ((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highH_atA_0 : ((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highH_atA_1 : ((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highH_atA_2 : ((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highH_atA_3 : ((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highG_atT_0 : ((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highG_atT_1 : ((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highG_atT_2 : ((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highG_atT_3 : ((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highG_atA_0 : ((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highG_atA_1 : ((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highG_atA_2 : ((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highG_atA_3 : ((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highB_atT_0 : ((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highB_atT_1 : ((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highB_atT_2 : ((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highB_atT_3 : ((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highB_atA_0 : ((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highB_atA_1 : ((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highB_atA_2 : ((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highB_atA_3 : ((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2


set_option Elab.async false in
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 1000000 in
private theorem r78g_F_lowU :
    (((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).l.length ≤ farDegree .lowUH .atT+1 ∧
    (98274:ℤ)*((((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).s*2^((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowUH .atT)
      (fun j => (chebList ((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).l.length ≤ farDegree .lowUH .atA+1 ∧
    (441112:ℤ)*((((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).s*2^((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowUH .atA)
      (fun j => (chebList ((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).l.length ≤ farDegree .lowUB .atT+1 ∧
    (145059:ℤ)*((((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).s*2^((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowUB .atT)
      (fun j => (chebList ((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).l.length ≤ farDegree .lowUB .atA+1 ∧
    (508864:ℤ)*((((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).s*2^((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowUB .atA)
      (fun j => (chebList ((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).l).getD j 0)) := by
  decide +kernel

private theorem r78kFD_lowUH_atT : ((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).l.length ≤ farDegree .lowUH .atT+1 ∧
    (98274:ℤ)*((((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).s*2^((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowUH .atT)
      (fun j => (chebList ((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.1

private theorem r78kFD_lowUH_atA : ((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).l.length ≤ farDegree .lowUH .atA+1 ∧
    (441112:ℤ)*((((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).s*2^((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowUH .atA)
      (fun j => (chebList ((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.1

private theorem r78kFD_lowUB_atT : ((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).l.length ≤ farDegree .lowUB .atT+1 ∧
    (145059:ℤ)*((((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).s*2^((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowUB .atT)
      (fun j => (chebList ((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.1

private theorem r78kFD_lowUB_atA : ((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).l.length ≤ farDegree .lowUB .atA+1 ∧
    (508864:ℤ)*((((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).s*2^((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowUB .atA)
      (fun j => (chebList ((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.1

private theorem r78kFM_lowUH_atT_0 : ((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.1

private theorem r78kFM_lowUH_atT_1 : ((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.1

private theorem r78kFM_lowUH_atT_2 : ((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.1

private theorem r78kFM_lowUH_atT_3 : ((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUH_atA_0 : ((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUH_atA_1 : ((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUH_atA_2 : ((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUH_atA_3 : ((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUB_atT_0 : ((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUB_atT_1 : ((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUB_atT_2 : ((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUB_atT_3 : ((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUB_atA_0 : ((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUB_atA_1 : ((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUB_atA_2 : ((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUB_atA_3 : ((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2


set_option Elab.async false in
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 1000000 in
private theorem r78g_F_lowV :
    (((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowVH .atT+1 ∧
    (246572:ℤ)*((((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowVH .atT)
      (fun j => (chebList ((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowVH .atA+1 ∧
    (293761:ℤ)*((((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowVH .atA)
      (fun j => (chebList ((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowVG .atT+1 ∧
    (220630:ℤ)*((((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowVG .atT)
      (fun j => (chebList ((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowVG .atA+1 ∧
    (165940:ℤ)*((((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowVG .atA)
      (fun j => (chebList ((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowZero .atT+1 ∧
    (201415:ℤ)*((((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowZero .atT)
      (fun j => (chebList ((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowZero .atA+1 ∧
    (145527:ℤ)*((((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowZero .atA)
      (fun j => (chebList ((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).l).getD j 0)) := by
  decide +kernel

private theorem r78kFD_lowVH_atT : ((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowVH .atT+1 ∧
    (246572:ℤ)*((((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowVH .atT)
      (fun j => (chebList ((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.1

private theorem r78kFD_lowVH_atA : ((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowVH .atA+1 ∧
    (293761:ℤ)*((((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowVH .atA)
      (fun j => (chebList ((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.1

private theorem r78kFD_lowVG_atT : ((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowVG .atT+1 ∧
    (220630:ℤ)*((((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowVG .atT)
      (fun j => (chebList ((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.1

private theorem r78kFD_lowVG_atA : ((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowVG .atA+1 ∧
    (165940:ℤ)*((((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowVG .atA)
      (fun j => (chebList ((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.1

private theorem r78kFD_lowZero_atT : ((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowZero .atT+1 ∧
    (201415:ℤ)*((((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowZero .atT)
      (fun j => (chebList ((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.1

private theorem r78kFD_lowZero_atA : ((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowZero .atA+1 ∧
    (145527:ℤ)*((((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowZero .atA)
      (fun j => (chebList ((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.1

private theorem r78kFM_lowVH_atT_0 : ((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.1

private theorem r78kFM_lowVH_atT_1 : ((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVH_atT_2 : ((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVH_atT_3 : ((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVH_atA_0 : ((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVH_atA_1 : ((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVH_atA_2 : ((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVH_atA_3 : ((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVG_atT_0 : ((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVG_atT_1 : ((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVG_atT_2 : ((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVG_atT_3 : ((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVG_atA_0 : ((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVG_atA_1 : ((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVG_atA_2 : ((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVG_atA_3 : ((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowZero_atT_0 : ((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowZero_atT_1 : ((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowZero_atT_2 : ((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowZero_atT_3 : ((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowZero_atA_0 : ((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowZero_atA_1 : ((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowZero_atA_2 : ((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowZero_atA_3 : ((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2


set_option Elab.async false in
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 1000000 in
private theorem r78g_F_highV :
    (((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highHv .atT+1 ∧
    (302465:ℤ)*((((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highHv .atT)
      (fun j => (chebList ((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highHv .atA+1 ∧
    (255999:ℤ)*((((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highHv .atA)
      (fun j => (chebList ((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highGv .atT+1 ∧
    (223385:ℤ)*((((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highGv .atT)
      (fun j => (chebList ((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highGv .atA+1 ∧
    (155563:ℤ)*((((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highGv .atA)
      (fun j => (chebList ((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highBv .atT+1 ∧
    (474660:ℤ)*((((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highBv .atT)
      (fun j => (chebList ((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highBv .atA+1 ∧
    (1028199:ℤ)*((((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highBv .atA)
      (fun j => (chebList ((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).l).getD j 0)) := by
  decide +kernel

private theorem r78kFD_highHv_atT : ((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highHv .atT+1 ∧
    (302465:ℤ)*((((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highHv .atT)
      (fun j => (chebList ((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.1

private theorem r78kFD_highHv_atA : ((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highHv .atA+1 ∧
    (255999:ℤ)*((((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highHv .atA)
      (fun j => (chebList ((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.1

private theorem r78kFD_highGv_atT : ((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highGv .atT+1 ∧
    (223385:ℤ)*((((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highGv .atT)
      (fun j => (chebList ((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.1

private theorem r78kFD_highGv_atA : ((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highGv .atA+1 ∧
    (155563:ℤ)*((((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highGv .atA)
      (fun j => (chebList ((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.1

private theorem r78kFD_highBv_atT : ((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highBv .atT+1 ∧
    (474660:ℤ)*((((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highBv .atT)
      (fun j => (chebList ((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.1

private theorem r78kFD_highBv_atA : ((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highBv .atA+1 ∧
    (1028199:ℤ)*((((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highBv .atA)
      (fun j => (chebList ((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.1

private theorem r78kFM_highHv_atT_0 : ((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.1

private theorem r78kFM_highHv_atT_1 : ((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.1

private theorem r78kFM_highHv_atT_2 : ((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHv_atT_3 : ((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHv_atA_0 : ((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHv_atA_1 : ((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHv_atA_2 : ((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHv_atA_3 : ((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGv_atT_0 : ((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGv_atT_1 : ((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGv_atT_2 : ((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGv_atT_3 : ((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGv_atA_0 : ((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGv_atA_1 : ((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGv_atA_2 : ((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGv_atA_3 : ((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBv_atT_0 : ((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBv_atT_1 : ((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBv_atT_2 : ((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBv_atT_3 : ((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBv_atA_0 : ((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBv_atA_1 : ((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBv_atA_2 : ((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBv_atA_3 : ((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2


set_option Elab.async false in
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 1000000 in
private theorem r78g_F_highU :
    (((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highHu .atT+1 ∧
    (147124:ℤ)*((((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highHu .atT)
      (fun j => (chebList ((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highHu .atA+1 ∧
    (104322:ℤ)*((((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highHu .atA)
      (fun j => (chebList ((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highGu .atT+1 ∧
    (198910:ℤ)*((((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highGu .atT)
      (fun j => (chebList ((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highGu .atA+1 ∧
    (132153:ℤ)*((((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highGu .atA)
      (fun j => (chebList ((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highBu .atT+1 ∧
    (166633:ℤ)*((((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highBu .atT)
      (fun j => (chebList ((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highBu .atA+1 ∧
    (132561:ℤ)*((((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highBu .atA)
      (fun j => (chebList ((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).l.length≤6+1 ∧
    (629:ℤ)*((((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).s*2^((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((1000000:ℕ):ℤ)*lowerZ 6
      (fun j => (chebList ((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).l).getD j 0)) := by
  decide +kernel

private theorem r78kFD_highHu_atT : ((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highHu .atT+1 ∧
    (147124:ℤ)*((((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highHu .atT)
      (fun j => (chebList ((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.1

private theorem r78kFD_highHu_atA : ((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highHu .atA+1 ∧
    (104322:ℤ)*((((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highHu .atA)
      (fun j => (chebList ((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.1

private theorem r78kFD_highGu_atT : ((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highGu .atT+1 ∧
    (198910:ℤ)*((((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highGu .atT)
      (fun j => (chebList ((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.1

private theorem r78kFD_highGu_atA : ((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highGu .atA+1 ∧
    (132153:ℤ)*((((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highGu .atA)
      (fun j => (chebList ((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.1

private theorem r78kFD_highBu_atT : ((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highBu .atT+1 ∧
    (166633:ℤ)*((((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highBu .atT)
      (fun j => (chebList ((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.1

private theorem r78kFD_highBu_atA : ((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highBu .atA+1 ∧
    (132561:ℤ)*((((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highBu .atA)
      (fun j => (chebList ((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.1

private theorem r78kFM_highHu_atT_0 : ((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.1

private theorem r78kFM_highHu_atT_1 : ((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.1

private theorem r78kFM_highHu_atT_2 : ((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHu_atT_3 : ((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHu_atA_0 : ((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHu_atA_1 : ((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHu_atA_2 : ((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHu_atA_3 : ((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGu_atT_0 : ((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGu_atT_1 : ((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGu_atT_2 : ((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGu_atT_3 : ((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGu_atA_0 : ((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGu_atA_1 : ((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGu_atA_2 : ((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGu_atA_3 : ((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBu_atT_0 : ((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBu_atT_1 : ((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBu_atT_2 : ((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBu_atT_3 : ((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBu_atA_0 : ((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBu_atA_1 : ((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBu_atA_2 : ((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBu_atA_3 : ((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kQS : ((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).l.length≤6+1 ∧
    (629:ℤ)*((((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).s*2^((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((1000000:ℕ):ℤ)*lowerZ 6
      (fun j => (chebList ((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2


end r78

theorem small_direct_certificate (r : SmallCase) (e : Split) (hr : smallQuadratic r e=false) :
    centered (smallLeft r) (smallRight r) (smallNumerator r e)=
      expansion (smallDegree r e) (centered (smallLeft r) (smallRight r) (smallNumerator r e)) ∧
    smallReserve r e<lowerOn (smallDegree r e) (smallLeft r) (smallRight r) (smallNumerator r e) := by
  cases r <;> cases e
  · exact absurd hr (by decide)
  · exact r78_cert 1 20 (1) (1) (r78smallNum_rep .lowZero .atA) (by decide) r78_I0 8991 100000 (by norm_num [smallReserve]) (by decide) r78kSD_lowZero_atA
  · exact absurd hr (by decide)
  · exact r78_cert 1 30 (4) (1) (r78smallNum_rep .lowH .atA) (by decide) r78_I1 94417 10000000 (by norm_num [smallReserve]) (by decide) r78kSD_lowH_atA
  · exact r78_cert 1 30 (13) (8) (r78smallNum_rep .highH .atT) (by decide) r78_I2 8161 10000000 (by norm_num [smallReserve]) (by decide) r78kSD_highH_atT
  · exact r78_cert 1 30 (13) (8) (r78smallNum_rep .highH .atA) (by decide) r78_I2 7429 10000000 (by norm_num [smallReserve]) (by decide) r78kSD_highH_atA
  · exact r78_cert 1 30 (13) (8) (r78smallNum_rep .highG .atT) (by decide) r78_I2 49256 10000000 (by norm_num [smallReserve]) (by decide) r78kSD_highG_atT
  · exact r78_cert 1 30 (13) (8) (r78smallNum_rep .highG .atA) (by decide) r78_I2 45860 10000000 (by norm_num [smallReserve]) (by decide) r78kSD_highG_atA
  · exact r78_cert 1 30 (13) (8) (r78smallNum_rep .highB .atT) (by decide) r78_I2 344132 10000000 (by norm_num [smallReserve]) (by decide) r78kSD_highB_atT
  · exact r78_cert 1 30 (13) (8) (r78smallNum_rep .highB .atA) (by decide) r78_I2 923872 10000000 (by norm_num [smallReserve]) (by decide) r78kSD_highB_atA

def smallCoefficients (r : SmallCase) (e : Split) : ℕ→ℚ :=
  coefficient (smallDegree r e) (centered (smallLeft r) (smallRight r) (smallNumerator r e))

theorem small_quadratic_certificate (r : SmallCase) (e : Split) (hr : smallQuadratic r e=true) :
    centered (smallLeft r) (smallRight r) (smallNumerator r e)=
      C (smallCoefficients r e 0-smallCoefficients r e 2)+C (smallCoefficients r e 1)*X+
      C (2*smallCoefficients r e 2)*X^2+tail (smallCoefficients r e) 3 (smallDegree r e-2) ∧
    0<smallCoefficients r e 2 ∧
    smallReserve r e<quadraticReserve (smallCoefficients r e) (smallDegree r e-2) := by
  cases r <;> cases e
  · obtain ⟨hs,hl,h2,hq⟩ := r78kSQ_lowZero
    have hc := (r78smallNum_rep .lowZero .atT).kcentered 1 20 (1) (1)
      (a:=smallLeft .lowZero) (b:=smallRight .lowZero) (by decide) r78_I0.1 r78_I0.2
    have hcoef := WholeIntervalPolynomial.Certificate.coefficient_centered_eq hc hs hl
    refine ⟨r78_quad_id (smallCoefficients.eq_1 _ _).symm (by decide) ?_,?_⟩
    · rw [show smallDegree .lowZero .atT=32 from rfl]
      exact hc.eq_expansion hs hl
    · rw [smallCoefficients,show smallDegree .lowZero .atT=32 from rfl,hcoef,
        show (32:ℕ)-2=30 from rfl]
      have hK : (((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).s:ℚ)*2^((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l.length/2=((((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).s*2^((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l.length:ℕ):ℚ)/2 := by
        push_cast; ring
      exact r78_quad_core (B:=fun j => (WholeIntervalPolynomial.Certificate.chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD j 0)
        (K:=(((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).s:ℚ)*2^((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l.length/2) (M:=((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).s*2^((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l.length) (ρ:=smallReserve .lowZero .atT)
        30 183947 10000000 hK (Nat.mul_pos (Nat.pos_of_ne_zero hs) (by positivity))
        (by norm_num [smallReserve]) (by decide) h2 hq
  · exact absurd hr (by decide)
  · obtain ⟨hs,hl,h2,hq⟩ := r78kSQ_lowH
    have hc := (r78smallNum_rep .lowH .atT).kcentered 1 30 (4) (1)
      (a:=smallLeft .lowH) (b:=smallRight .lowH) (by decide) r78_I1.1 r78_I1.2
    have hcoef := WholeIntervalPolynomial.Certificate.coefficient_centered_eq hc hs hl
    refine ⟨r78_quad_id (smallCoefficients.eq_1 _ _).symm (by decide) ?_,?_⟩
    · rw [show smallDegree .lowH .atT=33 from rfl]
      exact hc.eq_expansion hs hl
    · rw [smallCoefficients,show smallDegree .lowH .atT=33 from rfl,hcoef,
        show (33:ℕ)-2=31 from rfl]
      have hK : (((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).s:ℚ)*2^((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l.length/2=((((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).s*2^((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l.length:ℕ):ℚ)/2 := by
        push_cast; ring
      exact r78_quad_core (B:=fun j => (WholeIntervalPolynomial.Certificate.chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD j 0)
        (K:=(((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).s:ℚ)*2^((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l.length/2) (M:=((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).s*2^((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l.length) (ρ:=smallReserve .lowH .atT)
        31 27740 10000000 hK (Nat.mul_pos (Nat.pos_of_ne_zero hs) (by positivity))
        (by norm_num [smallReserve]) (by decide) h2 hq
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)

theorem small_numerator_positive (r : SmallCase) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) : 0<aeval θ (smallNumerator r e) := by
  have hreserve : (0:ℝ)<(smallReserve r e:ℝ) := by
    cases r <;> cases e <;> norm_num [smallReserve]
  cases hr : smallQuadratic r e
  · have hc := small_direct_certificate r e hr
    exact hreserve.trans (positive_on_interval (small_interval r) hc.1 hc.2 hθ)
  · have hc := small_quadratic_certificate r e hr
    have hh := quadratic_on_interval (small_interval r) hc.1 hc.2.1 hθ
    have hq : (smallReserve r e:ℝ)<
        (quadraticReserve (smallCoefficients r e) (smallDegree r e-2):ℝ) := by
      exact_mod_cast hc.2.2
    exact (hreserve.trans hq).trans_le hh

theorem small_mass_certificate (r : SmallCase) (e : Split) (i : Fin 4) :
    centered (smallLeft r) (smallRight r) (smallMass r e i)=
      expansion 12 (centered (smallLeft r) (smallRight r) (smallMass r e i)) ∧
    (3/5:ℚ)<lowerOn 12 (smallLeft r) (smallRight r) (smallMass r e i) := by
  cases r <;> cases e <;> fin_cases i
  · exact r78_cert 1 20 (1) (1) (r78smallMass_rep .lowZero .atT 0) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kSM_lowZero_atT_0
  · exact r78_cert 1 20 (1) (1) (r78smallMass_rep .lowZero .atT 1) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kSM_lowZero_atT_1
  · exact r78_cert 1 20 (1) (1) (r78smallMass_rep .lowZero .atT 2) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kSM_lowZero_atT_2
  · exact r78_cert 1 20 (1) (1) (r78smallMass_rep .lowZero .atT 3) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kSM_lowZero_atT_3
  · exact r78_cert 1 20 (1) (1) (r78smallMass_rep .lowZero .atA 0) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kSM_lowZero_atA_0
  · exact r78_cert 1 20 (1) (1) (r78smallMass_rep .lowZero .atA 1) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kSM_lowZero_atA_1
  · exact r78_cert 1 20 (1) (1) (r78smallMass_rep .lowZero .atA 2) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kSM_lowZero_atA_2
  · exact r78_cert 1 20 (1) (1) (r78smallMass_rep .lowZero .atA 3) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kSM_lowZero_atA_3
  · exact r78_cert 1 30 (4) (1) (r78smallMass_rep .lowH .atT 0) (by decide) r78_I1 3 5 r78_ρ35 (by decide) r78kSM_lowH_atT_0
  · exact r78_cert 1 30 (4) (1) (r78smallMass_rep .lowH .atT 1) (by decide) r78_I1 3 5 r78_ρ35 (by decide) r78kSM_lowH_atT_1
  · exact r78_cert 1 30 (4) (1) (r78smallMass_rep .lowH .atT 2) (by decide) r78_I1 3 5 r78_ρ35 (by decide) r78kSM_lowH_atT_2
  · exact r78_cert 1 30 (4) (1) (r78smallMass_rep .lowH .atT 3) (by decide) r78_I1 3 5 r78_ρ35 (by decide) r78kSM_lowH_atT_3
  · exact r78_cert 1 30 (4) (1) (r78smallMass_rep .lowH .atA 0) (by decide) r78_I1 3 5 r78_ρ35 (by decide) r78kSM_lowH_atA_0
  · exact r78_cert 1 30 (4) (1) (r78smallMass_rep .lowH .atA 1) (by decide) r78_I1 3 5 r78_ρ35 (by decide) r78kSM_lowH_atA_1
  · exact r78_cert 1 30 (4) (1) (r78smallMass_rep .lowH .atA 2) (by decide) r78_I1 3 5 r78_ρ35 (by decide) r78kSM_lowH_atA_2
  · exact r78_cert 1 30 (4) (1) (r78smallMass_rep .lowH .atA 3) (by decide) r78_I1 3 5 r78_ρ35 (by decide) r78kSM_lowH_atA_3
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highH .atT 0) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highH_atT_0
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highH .atT 1) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highH_atT_1
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highH .atT 2) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highH_atT_2
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highH .atT 3) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highH_atT_3
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highH .atA 0) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highH_atA_0
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highH .atA 1) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highH_atA_1
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highH .atA 2) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highH_atA_2
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highH .atA 3) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highH_atA_3
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highG .atT 0) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highG_atT_0
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highG .atT 1) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highG_atT_1
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highG .atT 2) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highG_atT_2
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highG .atT 3) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highG_atT_3
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highG .atA 0) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highG_atA_0
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highG .atA 1) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highG_atA_1
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highG .atA 2) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highG_atA_2
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highG .atA 3) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highG_atA_3
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highB .atT 0) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highB_atT_0
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highB .atT 1) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highB_atT_1
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highB .atT 2) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highB_atT_2
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highB .atT 3) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highB_atT_3
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highB .atA 0) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highB_atA_0
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highB .atA 1) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highB_atA_1
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highB .atA 2) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highB_atA_2
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highB .atA 3) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highB_atA_3

theorem small_mass_positive (r : SmallCase) (e : Split) (i : Fin 4) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) : 0<aeval θ (smallMass r e i) := by
  have hc := small_mass_certificate r e i
  have hh := positive_on_interval (small_interval r) hc.1 hc.2 hθ
  norm_num at hh
  linarith

theorem far_certificate (r : FarCase) (e : Split) :
    centered (farLeft r) (farRight r) (farNumerator r e)=
      expansion (farDegree r e) (centered (farLeft r) (farRight r) (farNumerator r e)) ∧
    farReserve r e<lowerOn (farDegree r e) (farLeft r) (farRight r) (farNumerator r e) := by
  cases r <;> cases e
  · exact r78_cert 1 20 (1) (1) (r78farNum_rep .lowUH .atT) (by decide) r78_I0 98274 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowUH_atT
  · exact r78_cert 1 20 (1) (1) (r78farNum_rep .lowUH .atA) (by decide) r78_I0 441112 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowUH_atA
  · exact r78_cert 1 20 (1) (1) (r78farNum_rep .lowUB .atT) (by decide) r78_I0 145059 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowUB_atT
  · exact r78_cert 1 20 (1) (1) (r78farNum_rep .lowUB .atA) (by decide) r78_I0 508864 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowUB_atA
  · exact r78_cert 1 40 (7) (3) (r78farNum_rep .lowVH .atT) (by decide) r78_I3 246572 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowVH_atT
  · exact r78_cert 1 40 (7) (3) (r78farNum_rep .lowVH .atA) (by decide) r78_I3 293761 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowVH_atA
  · exact r78_cert 1 40 (7) (3) (r78farNum_rep .lowVG .atT) (by decide) r78_I3 220630 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowVG_atT
  · exact r78_cert 1 40 (7) (3) (r78farNum_rep .lowVG .atA) (by decide) r78_I3 165940 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowVG_atA
  · exact r78_cert 1 40 (7) (3) (r78farNum_rep .lowZero .atT) (by decide) r78_I3 201415 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowZero_atT
  · exact r78_cert 1 40 (7) (3) (r78farNum_rep .lowZero .atA) (by decide) r78_I3 145527 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowZero_atA
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highHv .atT) (by decide) r78_I4 302465 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highHv_atT
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highHv .atA) (by decide) r78_I4 255999 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highHv_atA
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highGv .atT) (by decide) r78_I4 223385 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highGv_atT
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highGv .atA) (by decide) r78_I4 155563 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highGv_atA
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highBv .atT) (by decide) r78_I4 474660 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highBv_atT
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highBv .atA) (by decide) r78_I4 1028199 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highBv_atA
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highHu .atT) (by decide) r78_I4 147124 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highHu_atT
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highHu .atA) (by decide) r78_I4 104322 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highHu_atA
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highGu .atT) (by decide) r78_I4 198910 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highGu_atT
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highGu .atA) (by decide) r78_I4 132153 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highGu_atA
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highBu .atT) (by decide) r78_I4 166633 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highBu_atT
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highBu .atA) (by decide) r78_I4 132561 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highBu_atA

theorem far_numerator_positive (r : FarCase) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (farLeft r:ℝ) (farRight r:ℝ)) : 0<aeval θ (farNumerator r e) := by
  have hc := far_certificate r e
  have hh := positive_on_interval (far_interval r) hc.1 hc.2 hθ
  have hr : (0:ℝ)<(farReserve r e:ℝ) := by cases r <;> cases e <;> norm_num [farReserve]
  exact hr.trans hh

theorem far_mass_certificate (r : FarCase) (e : Split) (i : Fin 4) :
    centered (farLeft r) (farRight r) (farMass r e i)=
      expansion 12 (centered (farLeft r) (farRight r) (farMass r e i)) ∧
    (3/5:ℚ)<lowerOn 12 (farLeft r) (farRight r) (farMass r e i) := by
  cases r <;> cases e <;> fin_cases i
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUH .atT 0) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUH_atT_0
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUH .atT 1) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUH_atT_1
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUH .atT 2) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUH_atT_2
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUH .atT 3) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUH_atT_3
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUH .atA 0) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUH_atA_0
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUH .atA 1) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUH_atA_1
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUH .atA 2) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUH_atA_2
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUH .atA 3) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUH_atA_3
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUB .atT 0) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUB_atT_0
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUB .atT 1) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUB_atT_1
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUB .atT 2) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUB_atT_2
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUB .atT 3) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUB_atT_3
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUB .atA 0) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUB_atA_0
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUB .atA 1) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUB_atA_1
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUB .atA 2) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUB_atA_2
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUB .atA 3) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUB_atA_3
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVH .atT 0) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVH_atT_0
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVH .atT 1) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVH_atT_1
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVH .atT 2) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVH_atT_2
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVH .atT 3) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVH_atT_3
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVH .atA 0) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVH_atA_0
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVH .atA 1) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVH_atA_1
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVH .atA 2) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVH_atA_2
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVH .atA 3) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVH_atA_3
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVG .atT 0) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVG_atT_0
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVG .atT 1) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVG_atT_1
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVG .atT 2) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVG_atT_2
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVG .atT 3) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVG_atT_3
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVG .atA 0) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVG_atA_0
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVG .atA 1) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVG_atA_1
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVG .atA 2) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVG_atA_2
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVG .atA 3) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVG_atA_3
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowZero .atT 0) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowZero_atT_0
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowZero .atT 1) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowZero_atT_1
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowZero .atT 2) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowZero_atT_2
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowZero .atT 3) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowZero_atT_3
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowZero .atA 0) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowZero_atA_0
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowZero .atA 1) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowZero_atA_1
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowZero .atA 2) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowZero_atA_2
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowZero .atA 3) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowZero_atA_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHv .atT 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHv_atT_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHv .atT 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHv_atT_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHv .atT 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHv_atT_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHv .atT 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHv_atT_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHv .atA 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHv_atA_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHv .atA 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHv_atA_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHv .atA 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHv_atA_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHv .atA 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHv_atA_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGv .atT 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGv_atT_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGv .atT 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGv_atT_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGv .atT 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGv_atT_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGv .atT 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGv_atT_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGv .atA 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGv_atA_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGv .atA 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGv_atA_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGv .atA 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGv_atA_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGv .atA 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGv_atA_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBv .atT 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBv_atT_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBv .atT 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBv_atT_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBv .atT 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBv_atT_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBv .atT 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBv_atT_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBv .atA 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBv_atA_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBv .atA 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBv_atA_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBv .atA 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBv_atA_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBv .atA 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBv_atA_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHu .atT 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHu_atT_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHu .atT 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHu_atT_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHu .atT 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHu_atT_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHu .atT 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHu_atT_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHu .atA 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHu_atA_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHu .atA 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHu_atA_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHu .atA 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHu_atA_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHu .atA 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHu_atA_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGu .atT 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGu_atT_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGu .atT 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGu_atT_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGu .atT 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGu_atT_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGu .atT 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGu_atT_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGu .atA 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGu_atA_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGu .atA 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGu_atA_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGu .atA 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGu_atA_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGu .atA 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGu_atA_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBu .atT 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBu_atT_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBu .atT 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBu_atT_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBu .atT 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBu_atT_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBu .atT 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBu_atT_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBu .atA 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBu_atA_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBu .atA 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBu_atA_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBu .atA 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBu_atA_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBu .atA 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBu_atA_3

theorem far_mass_positive (r : FarCase) (e : Split) (i : Fin 4) {θ : ℝ}
    (hθ : θ∈Icc (farLeft r:ℝ) (farRight r:ℝ)) : 0<aeval θ (farMass r e i) := by
  have hc := far_mass_certificate r e i
  have hh := positive_on_interval (far_interval r) hc.1 hc.2 hθ
  norm_num at hh
  linarith

theorem far_qstar_T_certificate :
    centered u h (farQStar-farMu .high .atT)=
      expansion 6 (centered u h (farQStar-farMu .high .atT)) ∧
    (629/1000000:ℚ)<lowerOn 6 u h (farQStar-farMu .high .atT) := by
  exact r78_cert 1 40 (19) (9) ((r78farQStar_rep.sub (r78farMu_rep .high .atT))) (by decide) r78_I4 629 1000000 (by norm_num) (by decide) r78kQS

theorem far_qstar_T_positive {θ : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10)) :
    0<aeval θ (farQStar-farMu .high .atT) := by
  have hh := positive_on_interval (by norm_num [u,h] : u<h)
    far_qstar_T_certificate.1 far_qstar_T_certificate.2
    (show θ∈Icc (u:ℝ) (h:ℝ) by norm_num [u,h]; exact hθ)
  rw [map_sub]
  norm_num at hh
  linarith

theorem far_qstar_A_positive {θ : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10)) :
    0<aeval θ (farQStar-farC .high) := by
  norm_num [farQStar,farL,farC,h]
  linarith [hθ.2]

theorem small_domain (r : SmallCase) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) :
    θ∈Icc (Explicit.left .small (smallFamily r)) (Explicit.right .small (smallFamily r)) := by
  cases r <;>
    norm_num [smallLeft,smallRight,smallFamily,Explicit.left,Explicit.right,Explicit.L,L,h,v,
      Eight.frameCap] at hθ ⊢ <;> constructor <;> linarith [hθ.1,hθ.2]

theorem far_domain (r : FarCase) {θ : ℝ}
    (hθ : θ∈Icc (farLeft r:ℝ) (farRight r:ℝ)) :
    θ∈Icc (Explicit.left .far (farFamily r)) (Explicit.right .far (farFamily r)) := by
  cases r <;>
    norm_num [farLeft,farRight,farFamily,Explicit.left,Explicit.right,Explicit.u,h,v,u,
      Eight.frameCap] at hθ ⊢ <;> constructor <;> linarith [hθ.1,hθ.2]

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Certificate
