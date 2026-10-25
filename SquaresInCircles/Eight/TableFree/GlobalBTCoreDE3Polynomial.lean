module

public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3Data
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# Whole-interval certificates for the core-E DE3 scalars

The small-DE prefix uses one centered quadratic reserve.  The
saturated aligned prefix uses one centered coefficient norm on its
entire interval.  All certificates are fixed rational identities.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3

open Polynomial PowerTailBounds FrameCircleArc

/-! ### Kernel certificates (integer lists of `PolynomialCertificates`) -/

open WholeIntervalPolynomial.Certificate (Scaled) in
private theorem r56_shift_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s t : ℤ)
    {m : ℚ} (hden : den≠0) (hm : m=num*s/den) (h1 : (1:ℚ)=num*t/den) :
    (S.center num den s t).Rep (DirectedPowerBounds.shift m p) := by
  have hc := hp.centered num den s t (a:=m-1) (b:=m+1) hden (by rw [← hm]; ring)
    (by rw [← h1]; ring)
  rwa [WholeIntervalPolynomial.centered,WholeIntervalPolynomial.affine,
    show (m-1+(m+1))/2=m by ring,show (m+1-(m-1))/2=1 by ring,map_one,one_mul] at hc

/-- The integer numerator of `PowerTailBounds.norm` at the radius `num/den`. -/
private def r56_normZ (l : List ℤ) (start count num den : ℕ) : ℤ :=
  ∑ j : Fin count,|l.getD (j.val+start) 0| * (num:ℤ)^(j.val+1)*(den:ℤ)^(count-(j.val+1))

open WholeIntervalPolynomial.Certificate (Scaled) in
private theorem r56_coeff_sub_norm {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (hs : S.s≠0)
    (k start count num den : ℕ) (hden : den≠0) :
    p.coeff k-PowerTailBounds.norm p start count ((num:ℚ)/den)=
      ((S.l.getD k 0*(den:ℤ)^count-r56_normZ S.l start count num den:ℤ):ℚ)/
        ((S.s:ℚ)*(den:ℚ)^count) := by
  have hs' : (0:ℚ)<S.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd : (0:ℚ)<den := by exact_mod_cast Nat.pos_of_ne_zero hden
  have hn : PowerTailBounds.norm p start count ((num:ℚ)/den)=
      (r56_normZ S.l start count num den:ℚ)/((S.s:ℚ)*(den:ℚ)^count) := by
    simp only [PowerTailBounds.norm,hp.coeff hs,r56_normZ]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj : j.val+1≤count := j.isLt
    rw [abs_div,abs_of_pos hs',div_pow,
      show (den:ℚ)^count=(den:ℚ)^(j.val+1)*(den:ℚ)^(count-(j.val+1)) by
        rw [← pow_add,Nat.add_sub_cancel' hj]]
    field_simp
  rw [hn,hp.coeff hs]
  push_cast
  field_simp

open WholeIntervalPolynomial.Certificate (Scaled) in
private theorem r56_reserve_pos {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (hs : S.s≠0)
    (k start count num den : ℕ) (hden : den≠0)
    (h : 0<S.l.getD k 0*(den:ℤ)^count-r56_normZ S.l start count num den) :
    0<p.coeff k-PowerTailBounds.norm p start count ((num:ℚ)/den) := by
  rw [r56_coeff_sub_norm hp hs k start count num den hden]
  have hs' : (0:ℚ)<S.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd : (0:ℚ)<den := by exact_mod_cast Nat.pos_of_ne_zero hden
  exact div_pos (by exact_mod_cast h) (by positivity)

open WholeIntervalPolynomial.Certificate (Scaled) in
private theorem r56_discriminant {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (hs : S.s≠0)
    (start count num den : ℕ) (hden : den≠0)
    (h : S.l.getD 1 0^2*(den:ℤ)^count<
      4*S.l.getD 0 0*(S.l.getD 2 0*(den:ℤ)^count-r56_normZ S.l start count num den)) :
    (p.coeff 1)^2<4*(p.coeff 0)*(p.coeff 2-PowerTailBounds.norm p start count ((num:ℚ)/den)) := by
  rw [r56_coeff_sub_norm hp hs 2 start count num den hden,hp.coeff hs,hp.coeff hs]
  have hs' : (0:ℚ)<S.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd : (0:ℚ)<(den:ℚ)^count := by
    have : (0:ℚ)<den := by exact_mod_cast Nat.pos_of_ne_zero hden
    positivity
  have hq : ((S.l.getD 1 0:ℚ))^2*(den:ℚ)^count<
      4*(S.l.getD 0 0:ℚ)*(((S.l.getD 2 0*(den:ℤ)^count-r56_normZ S.l start count num den:ℤ)):ℚ) := by
    exact_mod_cast h
  have e1 : ((S.l.getD 1 0:ℚ)/S.s)^2=
      ((S.l.getD 1 0:ℚ))^2*(den:ℚ)^count/((S.s:ℚ)^2*(den:ℚ)^count) := by
    field_simp
  have e2 : 4*((S.l.getD 0 0:ℚ)/S.s)*
      (((S.l.getD 2 0*(den:ℤ)^count-r56_normZ S.l start count num den:ℤ):ℚ)/((S.s:ℚ)*(den:ℚ)^count))=
      4*(S.l.getD 0 0:ℚ)*(((S.l.getD 2 0*(den:ℤ)^count-r56_normZ S.l start count num den:ℤ)):ℚ)/
        ((S.s:ℚ)^2*(den:ℚ)^count) := by
    field_simp
  rw [e1,e2]
  exact div_lt_div_of_pos_right hq (by positivity)

/-- A polynomial of degree below `11` is its quadratic part plus its power tail. -/
private theorem r56_quadratic_split {p : ℚ[X]} (h : p.natDegree≤10) :
    p=C (p.coeff 0)+C (p.coeff 1)*X+C (p.coeff 2)*X^2+PowerTailBounds.tail p 3 8 := by
  conv_lhs => rw [as_sum_range_C_mul_X_pow' p (Nat.lt_succ_of_le h)]
  rw [show Nat.succ 10=3+8 from rfl,Finset.sum_range_add,PowerTailBounds.tail,
    Fin.sum_univ_eq_sum_range (fun j => C (p.coeff (j+3))*X^(j+3)) 8]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.reduceAdd,pow_zero,pow_one,
    mul_one,zero_add]

/-- A polynomial of degree at most `n` is its constant term plus its power tail. -/
private theorem r56_constant_split {p : ℚ[X]} {n : ℕ} (hp : p.natDegree≤n) :
    p=C (p.coeff 0)+PowerTailBounds.tail p 1 n := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (n:=n+1) (Nat.lt_succ_of_le hp)]
  rw [Finset.sum_range_succ',PowerTailBounds.tail,
    ← Fin.sum_univ_eq_sum_range (fun i => C (p.coeff (i+1))*X^(i+1)) n,pow_zero,mul_one,add_comm]


open WholeIntervalPolynomial.Certificate (Scaled)

private def r56S7 : Scaled :=
  ((Scaled.var.sub ((Scaled.const (1/6)).mul (Scaled.var.pow 3))).add
    ((Scaled.const (1/120)).mul (Scaled.var.pow 5))).sub
    ((Scaled.const (1/5040)).mul (Scaled.var.pow 7))
private theorem r56S7_rep : r56S7.Rep TailPolynomial.S7 :=
  ((Scaled.rep_var.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 5))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 7))
private def r56C6 : Scaled :=
  (((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (1/24)).mul (Scaled.var.pow 4))).sub
    ((Scaled.const (1/720)).mul (Scaled.var.pow 6))
private theorem r56C6_rep : r56C6.Rep TailPolynomial.C6 :=
  ((Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 6))

namespace PrefixPolynomial

def c : ℚ[X] := C (3/5)+C (2/5)*X
def P1 : ℚ[X] := C (1149087/1000000)-C (308159/1000000)*X-C (293179/1000000)*X^2
def P2 : ℚ[X] := C (1149087/1000000)+C (210926/1000000)*X+C (41598/1000000)*X^2
def X1 : ℚ[X] := C ((49/50)^2)+c^2-C (2*(49/50))*c*TailPolynomial.S7
def X2 : ℚ[X] := C ((49/50)^2)+c^2
def L : ℚ[X] := C (314159/100000+3*(49/50)-16761/4520)-X+C 2*c+
  C (49/50)*TailPolynomial.C6
def H : ℚ[X] := C 2*P1*P2*L-C (1979/1000)*(P2*(X1+P1^2)+P1*(X2+P2^2))
def centered : ℚ[X] := DirectedPowerBounds.shift (7/20) H


private def r56c : Scaled := (Scaled.const (3/5)).add ((Scaled.const (2/5)).mul Scaled.var)
private theorem r56c_rep : r56c.Rep c :=
  (Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)
private def r56P1 : Scaled :=
  ((Scaled.const (1149087/1000000)).sub ((Scaled.const (308159/1000000)).mul Scaled.var)).sub
    ((Scaled.const (293179/1000000)).mul (Scaled.var.pow 2))
private theorem r56P1_rep : r56P1.Rep P1 :=
  ((Scaled.rep_const _).sub ((Scaled.rep_const _).mul Scaled.rep_var)).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))
private def r56P2 : Scaled :=
  ((Scaled.const (1149087/1000000)).add ((Scaled.const (210926/1000000)).mul Scaled.var)).add
    ((Scaled.const (41598/1000000)).mul (Scaled.var.pow 2))
private theorem r56P2_rep : r56P2.Rep P2 :=
  ((Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))
private def r56X1 : Scaled :=
  ((Scaled.const ((49/50)^2)).add (r56c.pow 2)).sub
    (((Scaled.const (2*(49/50))).mul r56c).mul r56S7)
private theorem r56X1_rep : r56X1.Rep X1 :=
  ((Scaled.rep_const _).add (r56c_rep.pow 2)).sub
    (((Scaled.rep_const _).mul r56c_rep).mul r56S7_rep)
private def r56X2 : Scaled := (Scaled.const ((49/50)^2)).add (r56c.pow 2)
private theorem r56X2_rep : r56X2.Rep X2 := (Scaled.rep_const _).add (r56c_rep.pow 2)
private def r56L : Scaled :=
  (((Scaled.const (314159/100000+3*(49/50)-16761/4520)).sub Scaled.var).add
    ((Scaled.const 2).mul r56c)).add ((Scaled.const (49/50)).mul r56C6)
private theorem r56L_rep : r56L.Rep L :=
  (((Scaled.rep_const _).sub Scaled.rep_var).add
    ((Scaled.rep_const _).mul r56c_rep)).add ((Scaled.rep_const _).mul r56C6_rep)
private def r56H : Scaled :=
  ((((Scaled.const 2).mul r56P1).mul r56P2).mul r56L).sub
    ((Scaled.const (1979/1000)).mul
      ((r56P2.mul (r56X1.add (r56P1.pow 2))).add (r56P1.mul (r56X2.add (r56P2.pow 2)))))
private theorem r56H_rep : r56H.Rep H :=
  ((((Scaled.rep_const _).mul r56P1_rep).mul r56P2_rep).mul r56L_rep).sub
    ((Scaled.rep_const _).mul
      ((r56P2_rep.mul (r56X1_rep.add (r56P1_rep.pow 2))).add
        (r56P1_rep.mul (r56X2_rep.add (r56P2_rep.pow 2)))))
private def r56cen : Scaled := r56H.center 1 20 7 20
private theorem r56cen_rep : r56cen.Rep centered :=
  r56_shift_rep r56H_rep 1 20 7 20 (by norm_num) (by norm_num) (by norm_num)

@[simp] theorem c_eval (p : ℝ) : aeval p c=weight p := by simp [c,weight,slope]

theorem centered_identity : centered=C (centered.coeff 0)+C (centered.coeff 1)*X+
    C (centered.coeff 2)*X^2+tail centered 3 8 :=
  r56_quadratic_split ((r56cen_rep.natDegree_le (by decide +kernel)).trans (by decide +kernel))

theorem centered_reserves : 0<centered.coeff 2-norm centered 3 8 (7/20) ∧
    (centered.coeff 1)^2<4*(centered.coeff 0)*(centered.coeff 2-norm centered 3 8 (7/20)) := by
  have hr : (7/20:ℚ)=((7:ℕ):ℚ)/((20:ℕ):ℚ) := by norm_num
  rw [hr]
  exact ⟨r56_reserve_pos r56cen_rep (by decide +kernel) 2 3 8 7 20 (by norm_num)
      (by decide +kernel),
    r56_discriminant r56cen_rep (by decide +kernel) 3 8 7 20 (by norm_num) (by decide +kernel)⟩

theorem positive {p : ℝ} (hp : p∈Icc 0 frameCap) : 0<aeval p H := by
  have hdom : |p-7/20|≤((7/20:ℚ):ℝ) := by
    push_cast
    exact TailPolynomial.centered_domain hp
  have hl := PowerTailBounds.quadratic_lower centered_identity
    (by norm_num : (0:ℚ)≤7/20) hdom
  have ha : 0<(centered.coeff 2:ℝ)-(norm centered 3 8 (7/20):ℝ) := by
    exact_mod_cast centered_reserves.1
  have hd : (centered.coeff 1:ℝ)^2<4*
      ((centered.coeff 2:ℝ)-(norm centered 3 8 (7/20):ℝ))*(centered.coeff 0:ℝ) := by
    have hh := centered_reserves.2
    exact_mod_cast (by linarith [hh] : (centered.coeff 1)^2<4*
      (centered.coeff 2-norm centered 3 8 (7/20))*(centered.coeff 0))
  have hpos := TailPolynomial.strict_quadratic (x := p-7/20) ha hd
  have he : aeval (p-7/20) centered=aeval p H := by
    simp [centered,DirectedPowerBounds.shift_eval]
  rw [he] at hl
  linarith

theorem envelopes_positive {p : ℝ} (hp : p∈Icc 0 frameCap) :
    (3/4:ℝ)<aeval p P1 ∧ 1<aeval p P2 := by
  have h2 := pow_le_pow_left₀ hp.1 hp.2 2
  dsimp [frameCap] at hp h2
  norm_num [P1,P2]
  constructor <;> nlinarith [hp.1,hp.2,sq_nonneg p]

end PrefixPolynomial

namespace BasePolynomial

def P : ℚ[X] := C (3083/2500)-C (73/500)*X^2+C (4/125)*X^4
def coefficient : ℚ[X] :=
  C (314159/100000+(5/2)*(49/50)+6/5-11369/5000-16761/4520+(269343/250000)/2)-X
def U : ℚ[X] := 1-C (1/2)*X^2+C (1/24)*X^4
def L : ℚ[X] := coefficient*TailPolynomial.C6+
  C (269343/250000)*(1+C (13/12)*TailPolynomial.S7)
def energy : ℚ[X] := C ((269343/250000)^2)+C (9/25)*U^2
def H : ℚ[X] := C 2*P*L-C (1979/1000)*(energy+P^2)
def centered : ℚ[X] := DirectedPowerBounds.shift (9/20) H

private def r56P : Scaled :=
  ((Scaled.const (3083/2500)).sub ((Scaled.const (73/500)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (4/125)).mul (Scaled.var.pow 4))
private theorem r56P_rep : r56P.Rep P :=
  ((Scaled.rep_const _).sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4))
private def r56coefficient : Scaled :=
  (Scaled.const (314159/100000+(5/2)*(49/50)+6/5-11369/5000-16761/4520+(269343/250000)/2)).sub
    Scaled.var
private theorem r56coefficient_rep : r56coefficient.Rep coefficient :=
  (Scaled.rep_const _).sub Scaled.rep_var
private def r56U : Scaled :=
  ((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (1/24)).mul (Scaled.var.pow 4))
private theorem r56U_rep : r56U.Rep U :=
  (Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4))
private def r56L : Scaled :=
  (r56coefficient.mul r56C6).add
    ((Scaled.const (269343/250000)).mul ((Scaled.ofNat 1).add ((Scaled.const (13/12)).mul r56S7)))
private theorem r56L_rep : r56L.Rep L :=
  (r56coefficient_rep.mul r56C6_rep).add
    ((Scaled.rep_const _).mul (Scaled.rep_one.add ((Scaled.rep_const _).mul r56S7_rep)))
private def r56energy : Scaled :=
  (Scaled.const ((269343/250000)^2)).add ((Scaled.const (9/25)).mul (r56U.pow 2))
private theorem r56energy_rep : r56energy.Rep energy :=
  (Scaled.rep_const _).add ((Scaled.rep_const _).mul (r56U_rep.pow 2))
private def r56H : Scaled :=
  (((Scaled.const 2).mul r56P).mul r56L).sub
    ((Scaled.const (1979/1000)).mul (r56energy.add (r56P.pow 2)))
private theorem r56H_rep : r56H.Rep H :=
  (((Scaled.rep_const _).mul r56P_rep).mul r56L_rep).sub
    ((Scaled.rep_const _).mul (r56energy_rep.add (r56P_rep.pow 2)))
private def r56cen : Scaled := r56H.center 1 20 9 20
private theorem r56cen_rep : r56cen.Rep centered :=
  r56_shift_rep r56H_rep 1 20 9 20 (by norm_num) (by norm_num) (by norm_num)

theorem centered_identity : centered=C (centered.coeff 0)+tail centered 1 11 :=
  r56_constant_split ((r56cen_rep.natDegree_le (by decide +kernel)).trans (by decide +kernel))

theorem centered_reserve : 0<centered.coeff 0-norm centered 1 11 (1/4) := by
  have hr : (1/4:ℚ)=((1:ℕ):ℚ)/((4:ℕ):ℚ) := by norm_num
  rw [hr]
  exact r56_reserve_pos r56cen_rep (by decide +kernel) 0 1 11 1 4 (by norm_num) (by decide +kernel)

theorem positive {t : ℝ} (ht : t∈Icc (1/5:ℝ) frameCap) : 0<aeval t H := by
  have hdom : |t-(9/20:ℝ)|≤((1/4:ℚ):ℝ) := by
    rw [abs_le]
    simp only [frameCap] at ht
    push_cast
    constructor <;> linarith [ht.1,ht.2]
  have hl := DirectedPowerBounds.constant_lower centered_identity hdom
  have hp : 0<(centered.coeff 0:ℝ)-(norm centered 1 11 (1/4):ℝ) := by
    exact_mod_cast centered_reserve
  have he : aeval (t-9/20) centered=aeval t H := by
    simp [centered,DirectedPowerBounds.shift_eval]
  rw [he] at hl
  linarith

theorem envelope_positive {t : ℝ} (ht : t∈Icc 0 frameCap) : 1<aeval t P := by
  have h2 := pow_le_pow_left₀ ht.1 ht.2 2
  dsimp [frameCap] at ht h2
  norm_num [P]
  nlinarith [pow_nonneg (sq_nonneg t) 2]

theorem coefficient_positive {t : ℝ} (ht : t∈Icc 0 frameCap) :
    0<aeval t coefficient := by
  norm_num [coefficient]
  dsimp [frameCap] at ht
  linarith [ht.2]

end BasePolynomial

end SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3
