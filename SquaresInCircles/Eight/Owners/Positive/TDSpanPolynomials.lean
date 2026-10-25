module

public import SquaresInCircles.Eight.Owners.ScalarRadicalTransfer

/-!
# Eight squares: continuous boundary certificates for the positive-TD2 long-span exclusion

The three intervals are the intrinsic edges of the feasible (t,v) polygon;
they do not subdivide an angle search. Polynomial identities and coefficient
reserves are specified for kernel reduction and have not been executed.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.PositiveTDSpanPolynomials
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

/-- On each edge `certificate i - reserve i` has positive Bernstein coefficients of its degree:
it is a positive combination of the products `(v - lo)^k (hi - v)^(n-k)`, which `linarith`
finds. -/
local macro "edge_positive" a:term:max b:term:max : tactic => `(tactic| (
  intro v hv
  have h0 : 0≤v-$a := sub_nonneg.2 hv.1
  have h1 : 0≤$b-v := sub_nonneg.2 hv.2
  have hb (k l : ℕ) : 0≤(v-$a)^k*($b-v)^l := mul_nonneg (pow_nonneg h0 k) (pow_nonneg h1 l)
  simp only [certificate,mass0,mass1,demand,radicand0,radicand1,lambda,t,w,S5,S7,C6,delta,center,
    Rbar,cbar,kbar,map_add,map_sub,map_mul,map_pow,map_one,map_zero,map_ofNat,aeval_C,aeval_X,
    eq_ratCast]
  push_cast
  linarith [hb 11 0,hb 10 1,hb 9 2,hb 8 3,hb 7 4,hb 6 5,hb 5 6,hb 4 7,hb 3 8,hb 2 9,hb 1 10,
    hb 0 11,hb 10 0,hb 9 1,hb 8 2,hb 7 3,hb 6 4,hb 5 5,hb 4 6,hb 3 7,hb 2 8,hb 1 9,hb 0 10]))

private theorem certificate_positive_zero :
    ∀ {v : ℝ},v∈Set.Icc (11/50:ℝ) (7/10) → (11/500:ℝ)<aeval v (certificate .zero) := by
  edge_positive (11/50) (7/10)
private theorem certificate_positive_short :
    ∀ {v : ℝ},v∈Set.Icc (13/100:ℝ) (61/100) → (4/125:ℝ)<aeval v (certificate .short) := by
  edge_positive (13/100) (61/100)
private theorem certificate_positive_spread :
    ∀ {v : ℝ},v∈Set.Icc (61/100:ℝ) (7/10) → (33/500:ℝ)<aeval v (certificate .spread) := by
  edge_positive (61/100) (7/10)

theorem certificate_positive (i : Edge) {v : ℝ} (hv : v∈Set.Icc (lo i:ℝ) (hi i:ℝ)) :
    (reserve i:ℝ)<aeval v (certificate i) := by
  cases i <;> norm_num [lo,hi,reserve] at hv ⊢
  · exact certificate_positive_zero hv
  · exact certificate_positive_short hv
  · exact certificate_positive_spread hv

theorem masses_positive (i : Edge) {v : ℝ} (hv : v∈Set.Icc (lo i:ℝ) (hi i:ℝ)) :
    0<aeval v (mass0 i) ∧ 0<aeval v (mass1 i) := by
  have h1 : 0≤v-lo i := sub_nonneg.2 hv.1
  have h2 : 0≤(hi i:ℝ)-v := sub_nonneg.2 hv.2
  have h12 := mul_nonneg h1 h2
  have h11 := mul_nonneg h1 h1
  cases i <;>
    simp only [lo,hi,mass0,mass1,delta,center,map_add,map_sub,map_mul,map_pow,aeval_C,aeval_X,
      eq_ratCast] at h1 h2 h12 h11 ⊢ <;>
    push_cast at h1 h2 h12 h11 ⊢ <;>
    constructor <;> linarith

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

end SquaresInCircles.Eight.PositiveTDSpanPolynomials
