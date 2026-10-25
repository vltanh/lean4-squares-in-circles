module

public import SquaresInCircles.Eight.TableFree.WholeIntervalPolynomial
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates
public import SquaresInCircles.Eight.TableFree.ScalarRadicalTransfer

/-!
# Continuous boundary certificates for the positive-TD2 long-span exclusion

Uncompiled source draft of equations (28)--(37) in
HAND_G5_GLOBAL_PRIMARY_ENTRY_NEGATIVE_GA_TD2_SPAN_BOUND.md.
The three intervals are the intrinsic edges of the feasible (t,v) polygon;
they do not subdivide an angle search. Polynomial identities and coefficient
reserves are specified for kernel reduction and have not been executed.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.PositiveTDSpanPolynomials
open Polynomial WholeIntervalPolynomial WholeIntervalPolynomial.Certificate

inductive Edge where | zero | short | spread

def lo : Edge → ℚ | .zero => 11/50 | .short => 13/100 | .spread => 61/100
def hi : Edge → ℚ | .zero => 7/10 | .short => 61/100 | .spread => 7/10
def degree : Edge → ℕ | .zero => 10 | .short => 10 | .spread => 11
def reserve : Edge → ℚ | .zero => 11/500 | .short => 4/125 | .spread => 33/500
def center : Edge → ℚ | .zero => 23/50 | .short => 37/100 | .spread => 131/200

def Rbar : ℚ := 494697/250000
def cbar : ℚ := 179843/200000
def kbar : ℚ := 114322/125000
def lambda : ℚ[X] := C (59/100)+C (47/100)*X
def t : Edge → ℚ[X] | .zero => 0 | .short => C (9/100) | .spread => C (7/10)-X
def w : Edge → ℚ[X] | .zero => X-C (11/50) | .short => X-C (13/100) | .spread => C (12/25)
def S5 (x : ℚ[X]) : ℚ[X] := x-C (1/6)*x^3+C (1/120)*x^5
def S7 (x : ℚ[X]) : ℚ[X] := S5 x-C (1/5040)*x^7
def C6 (x : ℚ[X]) : ℚ[X] := 1-C (1/2)*x^2+C (1/24)*x^4-C (1/720)*x^6
def delta (i : Edge) : ℚ[X] := X-C (center i)
def mass0 (i : Edge) : ℚ[X] :=
  match i with
  | .zero => C (1284507/1000000)+C (73747/250000)*delta i+C (26057/500000)*(delta i)^2
  | .short => C (1258389/1000000)+C (8916/31250)*delta i+C (55427/1000000)*(delta i)^2
  | .spread => C (53757/40000)+C (156999/500000)*delta i+C (45503/1000000)*(delta i)^2
def mass1 (i : Edge) : ℚ[X] :=
  match i with
  | .zero => C (966507/1000000)-C (571273/1000000)*delta i-C (61027/200000)*(delta i)^2
  | .short => C (203083/200000)-C (51519/100000)*delta i-C (158721/500000)*(delta i)^2
  | .spread => C (843959/1000000)-C (170729/250000)*delta i-C (263049/1000000)*(delta i)^2
def demand (i : Edge) : ℚ[X] :=
  C (2-cbar)+2*lambda+C (3/2-cbar)*C6 (t i)+C (13/12)*S7 (t i)+C6 X-
    C kbar*S5 (w i)+C (1/2)*C6 (w i)
def radicand0 : ℚ[X] := 1+lambda^2
def radicand1 : ℚ[X] := 1+lambda^2-2*lambda*S7 X
def certificate (i : Edge) : ℚ[X] :=
  2*mass0 i*mass1 i*demand i-C Rbar*
    (mass1 i*(radicand0+(mass0 i)^2)+mass0 i*(radicand1+(mass1 i)^2))

/-- Build a `Scaled` representation of a polynomial written with `+`, `-`, `*`,
powers, `C`, `X` and numerals, following its syntax. -/
local syntax "repT" : tactic
local macro_rules | `(tactic| repT) => `(tactic| first
  | (with_reducible apply Scaled.Rep.add; repT; repT)
  | (with_reducible apply Scaled.Rep.sub; repT; repT)
  | (with_reducible apply Scaled.Rep.mul; repT; repT)
  | (with_reducible apply Scaled.Rep.pow; repT)
  | (with_reducible apply Scaled.Rep.neg; repT)
  | with_reducible exact Scaled.rep_var
  | with_reducible exact Scaled.rep_zero
  | with_reducible exact Scaled.rep_one
  | with_reducible exact Scaled.rep_ofNat _
  | with_reducible exact Scaled.rep_natCast _
  | with_reducible exact Scaled.rep_const _)

private theorem lt_lowerOn_of {c : Scaled} {a b ρ : ℚ} {p : ℚ[X]} {D : ℕ}
    (hc : c.Rep (centered a b p)) (hs : c.s≠0) (hl : c.l.length≤D+1)
    (h : ρ<(lowerZ D (fun j => (chebList c.l).getD j 0):ℚ)/(c.s*2^c.l.length/2)) :
    ρ<lowerOn D a b p := by
  rw [lowerOn_eq_of_rep hc hs hl]
  exact h

/-- The centering data of each edge: `(lo+hi)/2 = s/den` and `(hi-lo)/2 = t/den`. -/
private def cden : Edge → ℕ | .zero => 50 | .short => 100 | .spread => 200
private def cs : Edge → ℤ | .zero => 23 | .short => 37 | .spread => 131
private def ct : Edge → ℤ | .zero => 12 | .short => 24 | .spread => 9

private theorem rep_centered {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (i : Edge) :
    (c.center 1 (cden i) (cs i) (ct i)).Rep (centered (lo i) (hi i) p) := by
  cases i <;> exact hc.centered _ _ _ _ (by norm_num [cden]) (by norm_num [lo,hi,cs,cden])
    (by norm_num [lo,hi,ct,cden])

/-- Unfold the polynomials of this file. -/
local macro "unfoldAll" : tactic => `(tactic| simp only [certificate,mass0,mass1,demand,
  radicand0,radicand1,lambda,t,w,S5,S7,C6,delta])

theorem expansion_identity (i : Edge) :
    centered (lo i) (hi i) (certificate i)=
      expansion (degree i) (centered (lo i) (hi i) (certificate i)) := by
  cases i <;> exact (rep_centered (by unfoldAll; repT) _).eq_expansion
    (by decide +kernel) (by decide +kernel)

theorem coefficient_reserve (i : Edge) :
    reserve i<lowerOn (degree i) (lo i) (hi i) (certificate i) := by
  cases i <;> exact lt_lowerOn_of (rep_centered (by unfoldAll; repT) _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem mass_identities (i : Edge) :
    centered (lo i) (hi i) (mass0 i)=expansion 2 (centered (lo i) (hi i) (mass0 i)) ∧
    centered (lo i) (hi i) (mass1 i)=expansion 2 (centered (lo i) (hi i) (mass1 i)) := by
  cases i <;> exact ⟨(rep_centered (by unfoldAll; repT) _).eq_expansion
    (by decide +kernel) (by decide +kernel),(rep_centered (by unfoldAll; repT) _).eq_expansion
    (by decide +kernel) (by decide +kernel)⟩

theorem mass_reserves (i : Edge) :
    (4/5:ℚ)<lowerOn 2 (lo i) (hi i) (mass0 i) ∧
    (4/5:ℚ)<lowerOn 2 (lo i) (hi i) (mass1 i) := by
  cases i <;> exact ⟨lt_lowerOn_of (rep_centered (by unfoldAll; repT) _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel),
    lt_lowerOn_of (rep_centered (by unfoldAll; repT) _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem certificate_positive (i : Edge) {v : ℝ} (hv : v∈Set.Icc (lo i:ℝ) (hi i:ℝ)) :
    (reserve i:ℝ)<aeval v (certificate i) :=
  positive_on_interval (by cases i <;> norm_num [lo,hi])
    (expansion_identity i) (coefficient_reserve i) hv

theorem masses_positive (i : Edge) {v : ℝ} (hv : v∈Set.Icc (lo i:ℝ) (hi i:ℝ)) :
    0<aeval v (mass0 i) ∧ 0<aeval v (mass1 i) := by
  have h0 := positive_on_interval (by cases i <;> norm_num [lo,hi])
    (mass_identities i).1 (mass_reserves i).1 hv
  have h1 := positive_on_interval (by cases i <;> norm_num [lo,hi])
    (mass_identities i).2 (mass_reserves i).2 hv
  constructor <;> norm_num at * <;> linarith

theorem radical_transfer (i : Edge) {v D R p0 p1 : ℝ}
    (hv : v∈Set.Icc (lo i:ℝ) (hi i:ℝ))
    (hD : aeval v (demand i)≤D) (hR : 0≤R) (hRu : R≤(Rbar:ℝ))
    (hp0 : 0≤p0) (hp1 : 0≤p1)
    (hp0u : p0≤aeval v radicand0) (hp1u : p1≤aeval v radicand1) :
    0<D-R*(Real.sqrt p0+Real.sqrt p1) := by
  obtain ⟨hm0,hm1⟩ := masses_positive i hv
  have hs0 := ScalarRadicalTransfer.sqrt_le_mass_majorant hp0 hm0
  have hs1 := ScalarRadicalTransfer.sqrt_le_mass_majorant hp1 hm1
  have hquot0 := div_le_div_of_nonneg_right
    (add_le_add hp0u (le_refl ((aeval v (mass0 i))^2))) (by positivity : 0≤2*aeval v (mass0 i))
  have hquot1 := div_le_div_of_nonneg_right
    (add_le_add hp1u (le_refl ((aeval v (mass1 i))^2))) (by positivity : 0≤2*aeval v (mass1 i))
  have hsum := add_le_add (hs0.trans hquot0) (hs1.trans hquot1)
  have hmul := mul_le_mul hRu hsum (by positivity) (hR.trans hRu)
  have hpoly := certificate_positive i hv
  have hreserve : (0:ℝ)<(reserve i:ℝ) := by cases i <;> norm_num [reserve]
  have hpolypos : 0<aeval v (certificate i) := hreserve.trans hpoly
  have hid : aeval v (certificate i)/(2*aeval v (mass0 i)*aeval v (mass1 i))=
      aeval v (demand i)-(Rbar:ℝ)*
        ((aeval v radicand0+(aeval v (mass0 i))^2)/(2*aeval v (mass0 i))+
         (aeval v radicand1+(aeval v (mass1 i))^2)/(2*aeval v (mass1 i))) := by
    simp only [certificate,map_sub,map_add,map_mul,map_pow,map_ofNat,aeval_C,eq_ratCast]
    field_simp [hm0.ne',hm1.ne']
  have hpos := div_pos hpolypos (by positivity : 0<2*aeval v (mass0 i)*aeval v (mass1 i))
  rw [hid] at hpos
  linarith

@[simp] theorem lambda_eval (v : ℝ) : aeval v lambda=59/100+(47/100)*v := by simp [lambda]
@[simp] theorem S5_eval (p : ℚ[X]) (v : ℝ) :
    aeval v (S5 p)=aeval v p-(aeval v p)^3/6+(aeval v p)^5/120 := by simp [S5]; ring
@[simp] theorem S7_eval (p : ℚ[X]) (v : ℝ) :
    aeval v (S7 p)=aeval v p-(aeval v p)^3/6+(aeval v p)^5/120-(aeval v p)^7/5040 := by simp [S7]; ring
@[simp] theorem C6_eval (p : ℚ[X]) (v : ℝ) :
    aeval v (C6 p)=1-(aeval v p)^2/2+(aeval v p)^4/24-(aeval v p)^6/720 := by simp [C6]; ring

end SquaresInCircles.Eight.TableFree.PositiveTDSpanPolynomials
