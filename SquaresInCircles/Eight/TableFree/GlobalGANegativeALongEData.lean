module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsEndpoints

/-!
# The four intrinsic domains for a negative A primary and a longer E total

Uncompiled transcription of Sections 5--6 of
`HAND_G3_NEGATIVE_A_PRIMARY_WITH_LONGER_E_TOTAL_EXCLUSION.md`.
The equal and cut endpoints retain their native triangle or trapezoid.
The polynomials are literal formulas, including the cubic auxiliary
masses; no value of a radical is asserted by the mass constants.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE
open TensorWholeIntervalPolynomial TwoVariablePolynomial

inductive Region | TE | TC | RE | RC deriving DecidableEq

namespace Explicit

def Domain : Region → ℝ → ℝ → Prop
  | .TE,x,y => 0≤x ∧ 0≤y ∧ x+y≤8/15
  | .TC,x,y => 0≤x ∧ 0≤y ∧ x+y≤23/150
  | .RE,x,y => x∈Icc 0 (1/6) ∧ y∈Icc 0 (19/50-x)
  | .RC,x,y => x∈Icc 0 (1/6) ∧ y∈Icc 0 (23/150+x)

def baseRegion : Region → NonnegativeTotals.Region
  | .TE | .TC => .triangle
  | .RE | .RC => .rectangle

def baseY : Region → ℝ → ℝ → ℝ
  | .TE,_,y => y
  | .TC,_,y => 19/50+y
  | .RE,_,y => y
  | .RC,x,y => 19/50+y-x

def z (r : Region) (x y : ℝ) : ℝ :=
  NonnegativeTotals.Explicit.theta (baseRegion r) x (baseY r x y)
def e (r : Region) (x y : ℝ) : ℝ :=
  NonnegativeTotals.Explicit.e (baseRegion r) x (baseY r x y)
def s : Region → ℝ → ℝ → ℝ
  | .TE,_,y => y
  | .TC,_,_ => 19/50
  | .RE,x,y => x+y
  | .RC,_,_ => 19/50
def delta (r : Region) (x y : ℝ) : ℝ := z r x y+e r x y-s r x y
def k (r : Region) (x y : ℝ) : ℝ :=
  NonnegativeTotals.Explicit.k (baseRegion r) x (baseY r x y)
def l (r : Region) (x y : ℝ) : ℝ :=
  NonnegativeTotals.Explicit.l (baseRegion r) x (baseY r x y)
def c (r : Region) (x y : ℝ) : ℝ :=
  NonnegativeTotals.Explicit.c (baseRegion r) x (baseY r x y)

theorem base_domain {r : Region} {x y : ℝ} (hd : Domain r x y) :
    NonnegativeTotals.Explicit.Domain (baseRegion r) x (baseY r x y) := by
  cases r <;>
    simp only [Domain,baseRegion,baseY,NonnegativeTotals.Explicit.Domain] at *
  · exact hd
  · exact ⟨hd.1,by linarith [hd.2.1],by linarith [hd.2.2]⟩
  · exact ⟨hd.1,⟨hd.2.1,by linarith [hd.1.1,hd.2.2]⟩⟩
  · exact ⟨hd.1,⟨by linarith [hd.1.2,hd.2.1],by linarith [hd.2.2]⟩⟩

theorem domains {r : Region} {x y : ℝ} (hd : Domain r x y) :
    z r x y∈Icc 0 TableFree.frameCap ∧
    e r x y∈Icc 0 TableFree.frameCap ∧
    s r x y∈Icc 0 (8/15) ∧ s r x y≤e r x y ∧
    delta r x y∈Icc 0 TableFree.frameCap := by
  have hb := NonnegativeTotals.Explicit.domains (base_domain hd)
  refine ⟨hb.1,hb.2.1,?_⟩
  cases r with
  | TE =>
    rcases hd with ⟨hx,hy,hxy⟩
    simp only [z,e,s,delta,baseRegion,baseY,NonnegativeTotals.Explicit.theta,
      NonnegativeTotals.Explicit.e,TableFree.frameCap,mem_Icc]
    exact ⟨⟨hy,by linarith⟩,le_rfl,⟨by linarith,by linarith⟩⟩
  | TC =>
    rcases hd with ⟨hx,hy,hxy⟩
    simp only [z,e,s,delta,baseRegion,baseY,NonnegativeTotals.Explicit.theta,
      NonnegativeTotals.Explicit.e,TableFree.frameCap,mem_Icc]
    exact ⟨⟨by norm_num,by norm_num⟩,by linarith,⟨by linarith,by linarith⟩⟩
  | RE =>
    rcases hd with ⟨⟨hx0,hx1⟩,⟨hy0,hy1⟩⟩
    simp only [z,e,s,delta,baseRegion,baseY,NonnegativeTotals.Explicit.theta,
      NonnegativeTotals.Explicit.e,TableFree.frameCap,mem_Icc]
    exact ⟨⟨by linarith,by linarith⟩,le_rfl,⟨by linarith,by linarith⟩⟩
  | RC =>
    rcases hd with ⟨⟨hx0,hx1⟩,⟨hy0,hy1⟩⟩
    simp only [z,e,s,delta,baseRegion,baseY,NonnegativeTotals.Explicit.theta,
      NonnegativeTotals.Explicit.e,TableFree.frameCap,mem_Icc]
    exact ⟨⟨by norm_num,by norm_num⟩,by linarith,⟨by linarith,by linarith⟩⟩

/-- Each actual upper endpoint has one of the four native coordinates. -/
theorem coordinates {z e : ℝ} (hz : 0≤z) (he : 0≤e)
    (ht : z+e∈Icc (1/6) TableFree.frameCap) :
    ∃ r x y,Domain r x y ∧ Explicit.z r x y=z ∧
      Explicit.e r x y=e ∧ s r x y=min e (19/50) := by
  by_cases hzL : 1/6≤z
  · by_cases heM : e≤19/50
    · refine ⟨.TE,z-1/6,e,?_,?_,?_,?_⟩
      · exact ⟨by linarith,he,by dsimp [TableFree.frameCap] at ht; linarith [ht.2]⟩
      · simp [Explicit.z,baseRegion,baseY,NonnegativeTotals.Explicit.theta]
      · rfl
      · simp [s,min_eq_left heM]
    · refine ⟨.TC,z-1/6,e-19/50,?_,?_,?_,?_⟩
      · exact ⟨by linarith,by linarith,by dsimp [TableFree.frameCap] at ht; linarith [ht.2]⟩
      · simp [Explicit.z,baseRegion,baseY,NonnegativeTotals.Explicit.theta]
      · simp [Explicit.e,baseRegion,baseY,NonnegativeTotals.Explicit.e]
      · simp [s,min_eq_right (le_of_not_ge heM)]
  · by_cases heM : e≤19/50
    · refine ⟨.RE,1/6-z,z+e-1/6,?_,?_,?_,?_⟩
      · exact ⟨⟨by linarith,by linarith⟩,⟨by linarith [ht.1],by linarith⟩⟩
      · simp [Explicit.z,baseRegion,baseY,NonnegativeTotals.Explicit.theta]
      · dsimp [Explicit.e,baseRegion,baseY,NonnegativeTotals.Explicit.e]; ring
      · simp [s,min_eq_left heM]
    · refine ⟨.RC,1/6-z,e-19/50,?_,?_,?_,?_⟩
      · exact ⟨⟨by linarith,by linarith⟩,
          ⟨by linarith,by dsimp [TableFree.frameCap] at ht; linarith [ht.2]⟩⟩
      · simp [Explicit.z,baseRegion,baseY,NonnegativeTotals.Explicit.theta]
      · dsimp [Explicit.e,baseRegion,baseY,NonnegativeTotals.Explicit.e]; ring
      · simp [s,min_eq_right (le_of_not_ge heM)]

end Explicit

namespace Certificate

def baseY : Region → Bivar
  | .TE | .RE => C X
  | .TC => scalar (19/50)+C X
  | .RC => scalar (19/50)+C X-X
def pull (r : Region) (p : Bivar) : Bivar := substitute X (baseY r) p
def z (r : Region) : Bivar := pull r (NonnegativeTotals.Certificate.theta (Explicit.baseRegion r))
def e (r : Region) : Bivar := pull r (NonnegativeTotals.Certificate.e (Explicit.baseRegion r))
def s : Region → Bivar
  | .TE => C X
  | .TC | .RC => scalar (19/50)
  | .RE => X+C X
def delta (r : Region) : Bivar := z r+e r-s r
def k (r : Region) : Bivar := pull r (NonnegativeTotals.Certificate.k (Explicit.baseRegion r))
def l (r : Region) : Bivar := pull r (NonnegativeTotals.Certificate.l (Explicit.baseRegion r))
def c (r : Region) : Bivar := pull r (NonnegativeTotals.Certificate.c (Explicit.baseRegion r))

def gain (u : Bivar) : Bivar :=
  scalar (13/12)*lift u PositiveTD.Certificate.S11+
    (scalar (82/125)-scalar (63/100)*u)*(lift u PositiveTD.Certificate.C10-1)
def jE : Region → Bivar
  | .TE => NonnegativeTotals.Certificate.J (e .TE)-scalar (1/500)*(e .TE)^4
  | .TC => NonnegativeTotals.Certificate.J (e .TC)-scalar (1/500)*(e .TC)^4
  | .RE => NonnegativeTotals.Certificate.J (e .RE)
  | .RC => NonnegativeTotals.Certificate.J (e .RC)-scalar (29/1000)*(e .RC)^4
def M (r : Region) : Bivar :=
  c r*(lift (z r) PositiveTD.Certificate.C12+scalar (293/1000)*lift (z r) PositiveTD.Certificate.S9)
def qB : Region → Bivar
  | .TE => l .TE+scalar (3/20)*(scalar (8/15)-X)
  | .TC => l .TC+scalar (3/20)*(scalar (8/15)-X)
  | .RE => M .RE
  | .RC => M .RC
def ABase (r : Region) : Bivar :=
  scalar 2*k r+scalar 3*l r+scalar 3+
    c r*(1+scalar 2*lift (z r) PositiveTD.Certificate.C10+
      scalar ((3/2)*(293/1000)+1/2-NonnegativeTotals.Certificate.sigmabar)*
        lift (z r) PositiveTD.Certificate.S9)+jE r+l r*gain (s r)
def A (r : Region) (i : Fin 3) : Bivar :=
  ABase r+(![1,l r,qB r] i)*(lift (delta r) PositiveTD.Certificate.C10-1)
def baseNorm (r : Region) : Fin 4 → Bivar :=
  ![1+(k r)^2,(k r)^2+(l r)^2,(l r)^2+(M r)^2,1+(c r)^2]
def P (r : Region) (i : Fin 3) (j : Fin 4) : Bivar :=
  baseNorm r j-if j.val=i.val then
    scalar 2*(![k r,k r*l r,l r*M r,0] j)*lift (delta r) PositiveTD.Certificate.S11 else 0
def rho (r : Region) (i : Fin 3) (j : Fin 4) : ℚ :=
  match r with
  | .TE | .RE =>
    if j.val=i.val then
      if j=2 then 1325511353/1000000000 else 27678887/25000000
    else ![150407189/125000000,150407189/125000000,1451171531/1000000000,
      142578599/100000000] j
  | .TC | .RC =>
    if j.val=i.val then
      ![579701923/500000000,1232394077/1000000000,1450364739/1000000000,0] j
    else ![50621029/40000000,167732132/125000000,1587872067/1000000000,
      747493761/500000000] j
def mass (r : Region) (i : Fin 3) (j : Fin 4) : Bivar := cubicMass (rho r i j) (P r i j)
def numerator (r : Region) (i : Fin 3) : Bivar :=
  let w := mass r i
  scalar 2*A r i*w 0*w 1*w 2*w 3-scalar NonnegativeTotals.Certificate.Rbar*
    ((P r i 0+(w 0)^2)*w 1*w 2*w 3+(P r i 1+(w 1)^2)*w 0*w 2*w 3+
      (P r i 2+(w 2)^2)*w 0*w 1*w 3+(P r i 3+(w 3)^2)*w 0*w 1*w 2)
def degree : Region → ℕ | .TE | .TC => 39 | .RE | .RC => 35
def transform (r : Region) (p : Bivar) : Bivar :=
  match r with
  | .TE => triangle (8/15) p
  | .TC => triangle (23/150) p
  | .RE => substitute (scalar (1/6)*unitX)
      ((scalar (19/50)-scalar (1/6)*unitX)*unitY) p
  | .RC => trapezoid (23/150) (1/6) p
def lowerOn (r : Region) (D : ℕ) (p : Bivar) : ℚ := lower D (coefficient D (transform r p))
def upperOn (r : Region) (D : ℕ) (p : Bivar) : ℚ :=
  TwoVariablePolynomial.upper D (coefficient D (transform r p))

@[simp] theorem evaluate_baseY (r : Region) (x y : ℝ) :
    evaluate x y (baseY r)=Explicit.baseY r x y := by cases r <;> simp [baseY,Explicit.baseY]
@[simp] theorem evaluate_z (r : Region) (x y : ℝ) : evaluate x y (z r)=Explicit.z r x y := by
  simp [z,pull,Explicit.z]
@[simp] theorem evaluate_e (r : Region) (x y : ℝ) : evaluate x y (e r)=Explicit.e r x y := by
  simp [e,pull,Explicit.e]
@[simp] theorem evaluate_s (r : Region) (x y : ℝ) : evaluate x y (s r)=Explicit.s r x y := by
  cases r <;> simp [s,Explicit.s]
@[simp] theorem evaluate_delta (r : Region) (x y : ℝ) :
    evaluate x y (delta r)=Explicit.delta r x y := by simp [delta,Explicit.delta]
@[simp] theorem evaluate_k (r : Region) (x y : ℝ) : evaluate x y (k r)=Explicit.k r x y := by
  simp [k,pull,Explicit.k]
@[simp] theorem evaluate_l (r : Region) (x y : ℝ) : evaluate x y (l r)=Explicit.l r x y := by
  simp [l,pull,Explicit.l]
@[simp] theorem evaluate_c (r : Region) (x y : ℝ) : evaluate x y (c r)=Explicit.c r x y := by
  simp [c,pull,Explicit.c]

theorem domain_bounds {r : Region} {D : ℕ} {p : Bivar}
    (hid : transform r p=expansion D (transform r p))
    {x y : ℝ} (hd : Explicit.Domain r x y) :
    (lowerOn r D p:ℝ)≤evaluate x y p ∧ evaluate x y p≤(upperOn r D p:ℝ) := by
  cases r with
  | TE =>
    exact triangle_bounds (by norm_num) hid hd.1 hd.2.1
      (by rw [show ((8/15:ℚ):ℝ)=8/15 by norm_num]; exact hd.2.2)
  | TC =>
    exact triangle_bounds (by norm_num) hid hd.1 hd.2.1
      (by rw [show ((23/150:ℚ):ℝ)=23/150 by norm_num]; exact hd.2.2)
  | RC =>
    exact trapezoid_bounds (by norm_num) (by norm_num) hid
      (by rw [show ((1/6:ℚ):ℝ)=1/6 by norm_num]; exact hd.1)
      (by rw [show ((23/150:ℚ):ℝ)=23/150 by norm_num]; exact hd.2)
  | RE =>
    have hb : 0<(19/50:ℝ)-x := by linarith [hd.1.2]
    let u : ℝ := 6*x
    let v : ℝ := y/(19/50-x)
    have hu : u∈Icc 0 1 := ⟨by dsimp [u]; linarith [hd.1.1],by dsimp [u]; linarith [hd.1.2]⟩
    have hv : v∈Icc 0 1 := ⟨div_nonneg hd.2.1 hb.le,(div_le_one hb).2 hd.2.2⟩
    have hx : (1/6:ℝ)*u=x := by dsimp [u]; ring
    have hy : ((19/50:ℝ)-x)*v=y := mul_div_cancel₀ y hb.ne'
    have hh := square_bounds hid (centered_unit hu) (centered_unit hv)
    have e1 : ((1/6:ℚ):ℝ)=1/6 := by norm_num
    have e2 : ((19/50:ℚ):ℝ)=19/50 := by norm_num
    simp only [lowerOn,upperOn]
    simp only [transform,evaluate_substitute,map_mul,map_sub,evaluate_scalar,
      evaluate_unitX,evaluate_unitY,e1,e2,hx,hy] at hh ⊢
    exact hh

theorem positive_on_domain {r : Region} {D : ℕ} {p : Bivar} {reserve : ℚ}
    (hid : transform r p=expansion D (transform r p)) (hr : reserve<lowerOn r D p)
    {x y : ℝ} (hd : Explicit.Domain r x y) : (reserve:ℝ)<evaluate x y p := by
  have hc : (reserve:ℝ)<(lowerOn r D p:ℝ) := by exact_mod_cast hr
  exact hc.trans_le (domain_bounds hid hd).1

theorem upper_on_domain {r : Region} {D : ℕ} {p : Bivar} {reserve : ℚ}
    (hid : transform r p=expansion D (transform r p)) (hr : upperOn r D p<reserve)
    {x y : ℝ} (hd : Explicit.Domain r x y) : evaluate x y p<(reserve:ℝ) := by
  have hc : (upperOn r D p:ℝ)<(reserve:ℝ) := by exact_mod_cast hr
  exact (domain_bounds hid hd).2.trans_lt hc

end Certificate
end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE
