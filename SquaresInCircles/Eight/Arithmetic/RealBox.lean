module

public import SquaresInCircles.Eight.Arithmetic.Arctangent
public import SquaresInCircles.Eight.Arithmetic.Taylor
public import SquaresInCircles.Eight.CentralForbidden

/-!
# A closed-domain real-expression certificate compiler

This module supplies the continuous semantics for the remaining whole-pair
finite proof scripts. The input expressions are the actual circle branches,
labels, center-gap constraints and signed separating margins. A leaf must
prove either a violated necessary inequality or a strictly positive cost.
A split is the union of two CLOSED boxes, including their common face.

`certify` is ordinary Lean recursion over rational interval arithmetic.
Its `by decide` applications are uncompiled source: they have deliberately
not been evaluated here. In particular an external report or search result
is never an assumption of `certify_sound`. Failure to close any leaf makes
the finite proposition false and prevents the corresponding theorem from
elaborating in a later compilation.
-/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.Arithmetic.RealBox

abbrev Box (n : ℕ) := Fin n → QInterval

def Box.Mem {n : ℕ} (B : Box n) (env : Fin n → ℝ) : Prop :=
  ∀ i, (B i).Mem (env i)

def rootStep (q : ℚ) (I : QInterval) : QInterval :=
  let m := (I.lo+I.hi)/2
  if m^2 ≤ q then ⟨m,I.hi⟩ else ⟨I.lo,m⟩

def rootBracket (q : ℚ) : ℕ → QInterval
  | 0 => ⟨0,max 1 q⟩
  | n+1 => rootStep q (rootBracket q n)

/-- Each bisection also preserves nonnegative rational endpoints. -/
lemma rootBracket_spec {q : ℚ} (hq : 0≤q) (n : ℕ) :
    0≤(rootBracket q n).lo ∧ (rootBracket q n).Mem (Real.sqrt q) := by
  induction n with
  | zero =>
      have hq' : (0:ℝ)≤q := by exact_mod_cast hq
      have hh : (q:ℝ)≤(max 1 q:ℚ)^2 := by
        rcases le_total q 1 with h | h
        · simp [rootBracket,max_eq_left h]
          exact_mod_cast h
        · simp only [max_eq_right h]
          have h' : (1:ℝ)≤q := by exact_mod_cast h
          nlinarith
      refine ⟨by norm_num [rootBracket],Real.sqrt_nonneg _,?_⟩
      have hn : (0:ℝ)≤(max 1 q:ℚ) := by positivity
      nlinarith [Real.sq_sqrt hq',Real.sqrt_nonneg (q:ℝ)]
  | succ n ih =>
      have hI := ih.2
      have hhi : 0≤(rootBracket q n).hi := by
        exact_mod_cast (Real.sqrt_nonneg (q:ℝ)).trans hI.2
      constructor
      · simp only [rootBracket,rootStep]
        split_ifs <;> dsimp <;> linarith [ih.1,hhi]
      · have hq' : (0:ℝ)≤q := by exact_mod_cast hq
        have hx := Real.sq_sqrt hq'
        unfold rootBracket
        unfold rootStep
        split_ifs with hm
        · constructor
          · have hm' : (((rootBracket q n).lo+(rootBracket q n).hi)/2:ℚ)^2≤q := hm
            have hmc : (((rootBracket q n).lo+(rootBracket q n).hi)/2:ℚ)^2≤(q:ℝ) := by
              exact_mod_cast hm'
            have hlo : (0:ℝ)≤(rootBracket q n).lo := by exact_mod_cast ih.1
            have hu : (0:ℝ)≤(rootBracket q n).hi := by exact_mod_cast hhi
            push_cast at *
            nlinarith [Real.sqrt_nonneg (q:ℝ)]
          · exact hI.2
        · constructor
          · exact hI.1
          · have hm' : (q:ℝ)<(((rootBracket q n).lo+(rootBracket q n).hi)/2:ℚ)^2 := by
              exact_mod_cast lt_of_not_ge hm
            have hlo : (0:ℝ)≤(rootBracket q n).lo := by exact_mod_cast ih.1
            have hu : (0:ℝ)≤(rootBracket q n).hi := by exact_mod_cast hhi
            push_cast at *
            nlinarith [Real.sqrt_nonneg (q:ℝ)]

def sqrtRange (I : QInterval) : QInterval :=
  ⟨(rootBracket (max 0 I.lo) 96).lo,(rootBracket (max 0 I.hi) 96).hi⟩

lemma sqrtRange_sound {I : QInterval} {x : ℝ} (hx : I.Mem x) :
    (sqrtRange I).Mem (Real.sqrt x) := by
  have hl := (rootBracket_spec (le_max_left 0 I.lo) 96).2
  have hu := (rootBracket_spec (le_max_left 0 I.hi) 96).2
  have hslo : Real.sqrt (max 0 (I.lo:ℝ))≤Real.sqrt x := by
    by_cases hx0 : 0≤x
    · exact Real.sqrt_le_sqrt (max_le hx0 hx.1)
    · have hi0 : (I.lo:ℝ)≤0 := le_trans hx.1 (le_of_not_ge hx0)
      simp [max_eq_left hi0,Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hx0)]
  have hshi : Real.sqrt x≤Real.sqrt (max 0 (I.hi:ℝ)) :=
    Real.sqrt_le_sqrt (hx.2.trans (le_max_right _ _))
  exact ⟨(by simpa using hl.1).trans hslo,hshi.trans (by simpa using hu.2)⟩

def absRange (I : QInterval) : QInterval :=
  if 0≤I.lo then I else if I.hi≤0 then I.neg else ⟨0,max (-I.lo) I.hi⟩

lemma absRange_sound {I : QInterval} {x : ℝ} (hx : I.Mem x) :
    (absRange I).Mem |x| := by
  unfold absRange
  split_ifs with hl hu
  · have h : (0:ℝ)≤I.lo := by exact_mod_cast hl
    simpa [abs_of_nonneg (h.trans hx.1)] using hx
  · have h : (I.hi:ℝ)≤0 := by exact_mod_cast hu
    simpa [abs_of_nonpos (hx.2.trans h)] using QInterval.mem_neg hx
  · refine ⟨abs_nonneg _,abs_le.mpr ⟨?_,?_⟩⟩
    · have h : (-(I.lo:ℝ))≤max (-(I.lo:ℝ)) I.hi := le_max_left _ _
      push_cast
      linarith [hx.1]
    · push_cast
      exact hx.2.trans (le_max_right _ _)

/-- Dense power coefficients. Every coefficient is rational source data. -/
def polynomialRange (p : List ℚ) (I : QInterval) : QInterval :=
  p.foldr (fun c J => (QInterval.point c).add (I.mul J)) (QInterval.point 0)
noncomputable def polynomialValue (p : List ℚ) (x : ℝ) : ℝ :=
  p.foldr (fun c y => (c:ℝ)+x*y) 0

lemma polynomialRange_sound (p : List ℚ) {I : QInterval} {x : ℝ} (hx : I.Mem x) :
    (polynomialRange p I).Mem (polynomialValue p x) := by
  induction p with
  | nil => exact QInterval.mem_point 0
  | cons c p ih => exact QInterval.mem_add (QInterval.mem_point c) (QInterval.mem_mul hx ih)

def C16 (x : ℝ) := CentralForbidden.C14 x+x^16/20922789888000
lemma cos_le_C16 {x : ℝ} (hx : 0≤x) : Real.cos x≤C16 x := by
  have h := nonneg_of_deriv_nonneg (fun t => C16 t-Real.cos t)
    (by unfold C16 CentralForbidden.C14 CentralForbidden.C12 CentralForbidden.C10 CentralForbidden.C8 CentralForbidden.S15 CentralForbidden.S13 CentralForbidden.S11 CentralForbidden.S9; fun_prop)
    (by norm_num [C16,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9])
    (fun t ht => by
      have hp := CentralForbidden.S15_le_sin ht
      simp (disch := fun_prop) [C16,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9] at hp ⊢
      linarith) hx
  linarith
def S17 (x : ℝ) := CentralForbidden.S15 x+x^17/355687428096000
lemma sin_le_S17 {x : ℝ} (hx : 0≤x) : Real.sin x≤S17 x := by
  have h := nonneg_of_deriv_nonneg (fun t => S17 t-Real.sin t)
    (by unfold C16 S17 CentralForbidden.C14 CentralForbidden.C12 CentralForbidden.C10 CentralForbidden.C8 CentralForbidden.S15 CentralForbidden.S13 CentralForbidden.S11 CentralForbidden.S9; fun_prop)
    (by norm_num [C16,S17,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9])
    (fun t ht => by
      have hp := cos_le_C16 ht
      simp (disch := fun_prop) [C16,S17,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9] at hp ⊢
      linarith) hx
  linarith
def C18 (x : ℝ) := C16 x-x^18/6402373705728000
lemma C18_le_cos {x : ℝ} (hx : 0≤x) : C18 x≤Real.cos x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.cos t-C18 t)
    (by unfold C16 S17 C18 CentralForbidden.C14 CentralForbidden.C12 CentralForbidden.C10 CentralForbidden.C8 CentralForbidden.S15 CentralForbidden.S13 CentralForbidden.S11 CentralForbidden.S9; fun_prop)
    (by norm_num [C16,S17,C18,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9])
    (fun t ht => by
      have hp := sin_le_S17 ht
      simp (disch := fun_prop) [C16,S17,C18,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9] at hp ⊢
      linarith) hx
  linarith
def S19 (x : ℝ) := S17 x-x^19/121645100408832000
lemma S19_le_sin {x : ℝ} (hx : 0≤x) : S19 x≤Real.sin x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.sin t-S19 t)
    (by unfold C16 S17 C18 S19 CentralForbidden.C14 CentralForbidden.C12 CentralForbidden.C10 CentralForbidden.C8 CentralForbidden.S15 CentralForbidden.S13 CentralForbidden.S11 CentralForbidden.S9; fun_prop)
    (by norm_num [C16,S17,C18,S19,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9])
    (fun t ht => by
      have hp := C18_le_cos ht
      simp (disch := fun_prop) [C16,S17,C18,S19,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9] at hp ⊢
      linarith) hx
  linarith
def C20 (x : ℝ) := C18 x+x^20/2432902008176640000
lemma cos_le_C20 {x : ℝ} (hx : 0≤x) : Real.cos x≤C20 x := by
  have h := nonneg_of_deriv_nonneg (fun t => C20 t-Real.cos t)
    (by unfold C16 S17 C18 S19 C20 CentralForbidden.C14 CentralForbidden.C12 CentralForbidden.C10 CentralForbidden.C8 CentralForbidden.S15 CentralForbidden.S13 CentralForbidden.S11 CentralForbidden.S9; fun_prop)
    (by norm_num [C16,S17,C18,S19,C20,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9])
    (fun t ht => by
      have hp := S19_le_sin ht
      simp (disch := fun_prop) [C16,S17,C18,S19,C20,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9] at hp ⊢
      linarith) hx
  linarith
def S21 (x : ℝ) := S19 x+x^21/51090942171709440000
lemma sin_le_S21 {x : ℝ} (hx : 0≤x) : Real.sin x≤S21 x := by
  have h := nonneg_of_deriv_nonneg (fun t => S21 t-Real.sin t)
    (by unfold C16 S17 C18 S19 C20 S21 CentralForbidden.C14 CentralForbidden.C12 CentralForbidden.C10 CentralForbidden.C8 CentralForbidden.S15 CentralForbidden.S13 CentralForbidden.S11 CentralForbidden.S9; fun_prop)
    (by norm_num [C16,S17,C18,S19,C20,S21,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9])
    (fun t ht => by
      have hp := cos_le_C20 ht
      simp (disch := fun_prop) [C16,S17,C18,S19,C20,S21,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9] at hp ⊢
      linarith) hx
  linarith
def C22 (x : ℝ) := C20 x-x^22/1124000727777607680000
lemma C22_le_cos {x : ℝ} (hx : 0≤x) : C22 x≤Real.cos x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.cos t-C22 t)
    (by unfold C16 S17 C18 S19 C20 S21 C22 CentralForbidden.C14 CentralForbidden.C12 CentralForbidden.C10 CentralForbidden.C8 CentralForbidden.S15 CentralForbidden.S13 CentralForbidden.S11 CentralForbidden.S9; fun_prop)
    (by norm_num [C16,S17,C18,S19,C20,S21,C22,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9])
    (fun t ht => by
      have hp := sin_le_S21 ht
      simp (disch := fun_prop) [C16,S17,C18,S19,C20,S21,C22,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9] at hp ⊢
      linarith) hx
  linarith
def S23 (x : ℝ) := S21 x-x^23/25852016738884976640000
lemma S23_le_sin {x : ℝ} (hx : 0≤x) : S23 x≤Real.sin x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.sin t-S23 t)
    (by unfold C16 S17 C18 S19 C20 S21 C22 S23 CentralForbidden.C14 CentralForbidden.C12 CentralForbidden.C10 CentralForbidden.C8 CentralForbidden.S15 CentralForbidden.S13 CentralForbidden.S11 CentralForbidden.S9; fun_prop)
    (by norm_num [C16,S17,C18,S19,C20,S21,C22,S23,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9])
    (fun t ht => by
      have hp := C22_le_cos ht
      simp (disch := fun_prop) [C16,S17,C18,S19,C20,S21,C22,S23,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9] at hp ⊢
      linarith) hx
  linarith
def C24 (x : ℝ) := C22 x+x^24/620448401733239439360000
lemma cos_le_C24 {x : ℝ} (hx : 0≤x) : Real.cos x≤C24 x := by
  have h := nonneg_of_deriv_nonneg (fun t => C24 t-Real.cos t)
    (by unfold C16 S17 C18 S19 C20 S21 C22 S23 C24 CentralForbidden.C14 CentralForbidden.C12 CentralForbidden.C10 CentralForbidden.C8 CentralForbidden.S15 CentralForbidden.S13 CentralForbidden.S11 CentralForbidden.S9; fun_prop)
    (by norm_num [C16,S17,C18,S19,C20,S21,C22,S23,C24,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9])
    (fun t ht => by
      have hp := S23_le_sin ht
      simp (disch := fun_prop) [C16,S17,C18,S19,C20,S21,C22,S23,C24,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9] at hp ⊢
      linarith) hx
  linarith
def S25 (x : ℝ) := S23 x+x^25/15511210043330985984000000
lemma sin_le_S25 {x : ℝ} (hx : 0≤x) : Real.sin x≤S25 x := by
  have h := nonneg_of_deriv_nonneg (fun t => S25 t-Real.sin t)
    (by unfold C16 S17 C18 S19 C20 S21 C22 S23 C24 S25 CentralForbidden.C14 CentralForbidden.C12 CentralForbidden.C10 CentralForbidden.C8 CentralForbidden.S15 CentralForbidden.S13 CentralForbidden.S11 CentralForbidden.S9; fun_prop)
    (by norm_num [C16,S17,C18,S19,C20,S21,C22,S23,C24,S25,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9])
    (fun t ht => by
      have hp := cos_le_C24 ht
      simp (disch := fun_prop) [C16,S17,C18,S19,C20,S21,C22,S23,C24,S25,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9] at hp ⊢
      linarith) hx
  linarith
def C26 (x : ℝ) := C24 x-x^26/403291461126605635584000000
lemma C26_le_cos {x : ℝ} (hx : 0≤x) : C26 x≤Real.cos x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.cos t-C26 t)
    (by unfold C16 S17 C18 S19 C20 S21 C22 S23 C24 S25 C26 CentralForbidden.C14 CentralForbidden.C12 CentralForbidden.C10 CentralForbidden.C8 CentralForbidden.S15 CentralForbidden.S13 CentralForbidden.S11 CentralForbidden.S9; fun_prop)
    (by norm_num [C16,S17,C18,S19,C20,S21,C22,S23,C24,S25,C26,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9])
    (fun t ht => by
      have hp := sin_le_S25 ht
      simp (disch := fun_prop) [C16,S17,C18,S19,C20,S21,C22,S23,C24,S25,C26,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9] at hp ⊢
      linarith) hx
  linarith
def S27 (x : ℝ) := S25 x-x^27/10888869450418352160768000000
lemma S27_le_sin {x : ℝ} (hx : 0≤x) : S27 x≤Real.sin x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.sin t-S27 t)
    (by unfold C16 S17 C18 S19 C20 S21 C22 S23 C24 S25 C26 S27 CentralForbidden.C14 CentralForbidden.C12 CentralForbidden.C10 CentralForbidden.C8 CentralForbidden.S15 CentralForbidden.S13 CentralForbidden.S11 CentralForbidden.S9; fun_prop)
    (by norm_num [C16,S17,C18,S19,C20,S21,C22,S23,C24,S25,C26,S27,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9])
    (fun t ht => by
      have hp := C26_le_cos ht
      simp (disch := fun_prop) [C16,S17,C18,S19,C20,S21,C22,S23,C24,S25,C26,S27,CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8,CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9] at hp ⊢
      linarith) hx
  linarith
def sineCoefficients : List ℚ := [0,1,0,(-1/6),0,(1/120),0,(-1/5040),0,(1/362880),0,(-1/39916800),0,(1/6227020800),0,(-1/1307674368000),0,(1/355687428096000),0,(-1/121645100408832000),0,(1/51090942171709440000),0,(-1/25852016738884976640000),0,(1/15511210043330985984000000)]
def cosineCoefficients : List ℚ := [1,0,(-1/2),0,(1/24),0,(-1/720),0,(1/40320),0,(-1/3628800),0,(1/479001600),0,(-1/87178291200),0,(1/20922789888000),0,(-1/6402373705728000),0,(1/2432902008176640000),0,(-1/1124000727777607680000),0,(1/620448401733239439360000)]
def atanLowerCoefficients : List ℚ := [0,1,0,(-1/3),0,(1/5),0,(-1/7),0,(1/9),0,(-1/11),0,(1/13),0,(-1/15),0,(1/17),0,(-1/19),0,(1/21),0,(-1/23),0,(1/25),0,(-1/27),0,(1/29),0,(-1/31),0,(1/33),0,(-1/35),0,(1/37),0,(-1/39),0,(1/41),0,(-1/43),0,(1/45),0,(-1/47),0,(1/49),0,(-1/51)]
def atanUpperCoefficients : List ℚ := [0,1,0,(-1/3),0,(1/5),0,(-1/7),0,(1/9),0,(-1/11),0,(1/13),0,(-1/15),0,(1/17),0,(-1/19),0,(1/21),0,(-1/23),0,(1/25),0,(-1/27),0,(1/29),0,(-1/31),0,(1/33),0,(-1/35),0,(1/37),0,(-1/39),0,(1/41),0,(-1/43),0,(1/45),0,(-1/47),0,(1/49)]

lemma sineValue (x : ℝ) : polynomialValue sineCoefficients x=S25 x := by
  norm_num [polynomialValue,sineCoefficients,S25,S23,S21,S19,S17,
    CentralForbidden.S15,CentralForbidden.S13,CentralForbidden.S11,CentralForbidden.S9]
  ring
lemma cosineValue (x : ℝ) : polynomialValue cosineCoefficients x=C24 x := by
  norm_num [polynomialValue,cosineCoefficients,C24,C22,C20,C18,C16,
    CentralForbidden.C14,CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8]
  ring
lemma atanLowerValue (x : ℝ) : polynomialValue atanLowerCoefficients x=atanLower x := by
  norm_num [polynomialValue,atanLowerCoefficients,atanLower]
  ring
lemma atanUpperValue (x : ℝ) : polynomialValue atanUpperCoefficients x=atanUpper x := by
  norm_num [polynomialValue,atanUpperCoefficients,atanUpper]
  ring

lemma sineRemainder (x : ℝ) :
    |Real.sin x-S25 x|≤|x|^27/10888869450418352160768000000 := by
  have he : S25 (-x)=-(S25 x) := by
    dsimp [S25,S23,S21,S19,S17,CentralForbidden.S15,CentralForbidden.S13,
      CentralForbidden.S11,CentralForbidden.S9]
    ring
  rcases le_total 0 x with hx | hx
  · have hu := sin_le_S25 hx
    have hl := S27_le_sin hx
    rw [abs_of_nonneg hx,abs_of_nonpos (by linarith)]
    dsimp [S27] at hl
    linarith
  · have hu := sin_le_S25 (neg_nonneg.mpr hx)
    have hl := S27_le_sin (neg_nonneg.mpr hx)
    simp only [Real.sin_neg,he,S27] at hu hl
    rw [abs_of_nonpos hx,abs_of_nonneg (by linarith)]
    linarith

lemma cosineRemainder (x : ℝ) :
    -(|x|^26/403291461126605635584000000)≤Real.cos x-C24 x ∧
    Real.cos x-C24 x≤0 := by
  have he : C24 |x|=C24 x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx]
      dsimp [C24,C22,C20,C18,C16,CentralForbidden.C14,
        CentralForbidden.C12,CentralForbidden.C10,CentralForbidden.C8]
      ring
  have hu := cos_le_C24 (abs_nonneg x)
  have hl := C26_le_cos (abs_nonneg x)
  rw [Real.cos_abs,he] at hu
  simp only [C26,Real.cos_abs,he] at hl
  exact ⟨by linarith,by linarith⟩

def magnitude (I : QInterval) : ℚ := max |I.lo| |I.hi|
lemma abs_le_magnitude {I : QInterval} {x : ℝ} (hx : I.Mem x) : |x|≤I.magnitude := by
  apply abs_le.mpr
  constructor
  · have h : -(max |(I.lo:ℝ)| |(I.hi:ℝ)|)≤I.lo :=
      (neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)
    simpa [magnitude] using h.trans hx.1
  · have h : (I.hi:ℝ)≤max |(I.lo:ℝ)| |(I.hi:ℝ)| :=
      (le_abs_self _).trans (le_max_right _ _)
    simpa [magnitude] using hx.2.trans h

def sinRange (I : QInterval) : QInterval :=
  let e := I.magnitude^27/10888869450418352160768000000
  (polynomialRange sineCoefficients I).add ⟨-e,e⟩
def cosRange (I : QInterval) : QInterval :=
  let e := I.magnitude^26/403291461126605635584000000
  (polynomialRange cosineCoefficients I).add ⟨-e,0⟩

lemma sinRange_sound {I : QInterval} {x : ℝ} (hx : I.Mem x) :
    (sinRange I).Mem (Real.sin x) := by
  have hp := polynomialRange_sound sineCoefficients hx
  rw [sineValue] at hp
  have he := (sineRemainder x).trans (div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg x) (abs_le_magnitude hx) 27) (by norm_num))
  have hh : (⟨-(I.magnitude^27/10888869450418352160768000000),
      I.magnitude^27/10888869450418352160768000000⟩:QInterval).Mem (Real.sin x-S25 x) := by
    simpa [QInterval.Mem] using abs_le.mp he
  simpa [sinRange] using QInterval.mem_add hp hh

lemma cosRange_sound {I : QInterval} {x : ℝ} (hx : I.Mem x) :
    (cosRange I).Mem (Real.cos x) := by
  have hp := polynomialRange_sound cosineCoefficients hx
  rw [cosineValue] at hp
  have he := cosineRemainder x
  have hpow := div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg x) (abs_le_magnitude hx) 26)
    (show (0:ℝ)≤403291461126605635584000000 by norm_num)
  have hh : (⟨-(I.magnitude^26/403291461126605635584000000),0⟩:QInterval).Mem
      (Real.cos x-C24 x) := by
    constructor <;> dsimp [QInterval.Mem] <;> push_cast
    · linarith [he.1]
    · exact he.2
  simpa [cosRange] using QInterval.mem_add hp hh

lemma arctan_half_positive {x : ℝ} (hx : 0≤x) :
    Real.arctan x=2*Real.arctan (atanHalf x) := by
  have hs : 0<Real.sqrt (1+x^2) := Real.sqrt_pos.mpr (by positivity)
  have he := Real.sq_sqrt (show (0:ℝ)≤1+x^2 by positivity)
  have hxs : x<Real.sqrt (1+x^2) := by nlinarith
  have hd : 0<1+Real.sqrt (1+x^2) := by positivity
  have hy0 := atanHalf_nonneg hx
  have hy1 : atanHalf x<1 := by unfold atanHalf; exact (div_lt_one hd).mpr (by linarith)
  have hyden : 0<1-(atanHalf x)^2 := by nlinarith
  have hid : 2*atanHalf x/(1-(atanHalf x)^2)=x := by
    unfold atanHalf
    field_simp [ne_of_gt hd,ne_of_gt hyden]
    nlinarith [congrArg (fun z : ℝ => x*z) he]
  rw [Real.two_mul_arctan (by linarith [hy0]) hy1,hid]

def atanPositive (q : ℚ) : QInterval :=
  let R := sqrtRange (QInterval.point (1+q^2))
  let J := (QInterval.point q).mul (((QInterval.point 1).add R).inv)
  ⟨2*(polynomialRange atanLowerCoefficients J).lo,
    2*(polynomialRange atanUpperCoefficients J).hi⟩

lemma atanPositive_sound {q : ℚ} (hq : 0≤q) : (atanPositive q).Mem (Real.arctan q) := by
  let R := sqrtRange (QInterval.point (1+q^2))
  have hR : R.Mem (Real.sqrt (1+(q:ℝ)^2)) := by
    simpa [R] using sqrtRange_sound (QInterval.mem_point (1+q^2))
  have hl : 0≤R.lo := by
    have hh := (rootBracket_spec (q:=max 0 (1+q^2)) (le_max_left _ _) 96).1
    dsimp [R,sqrtRange,QInterval.point]
    exact hh
  have hden : 0<((QInterval.point 1).add R).lo := by
    dsimp [QInterval.add,QInterval.point]
    linarith
  have hJ := QInterval.mem_mul (QInterval.mem_point q)
    (QInterval.mem_inv_pos hden (QInterval.mem_add (QInterval.mem_point 1) hR))
  have hhalf : ((QInterval.point q).mul (((QInterval.point 1).add R).inv)).Mem (atanHalf q) := by
    simpa [atanHalf,div_eq_mul_inv] using hJ
  have hL := polynomialRange_sound atanLowerCoefficients hhalf
  have hU := polynomialRange_sound atanUpperCoefficients hhalf
  rw [atanLowerValue] at hL
  rw [atanUpperValue] at hU
  have hq' : (0:ℝ)≤q := by exact_mod_cast hq
  have hlow := atanLower_le (atanHalf_nonneg hq')
  have hupp := arctan_le_atanUpper (atanHalf_nonneg hq')
  rw [arctan_half_positive hq']
  constructor <;> dsimp [atanPositive,QInterval.Mem] <;> push_cast <;> linarith [hL.1,hU.2]

def atanPoint (q : ℚ) : QInterval := if 0≤q then atanPositive q else (atanPositive (-q)).neg
lemma atanPoint_sound (q : ℚ) : (atanPoint q).Mem (Real.arctan q) := by
  unfold atanPoint
  split_ifs with hq
  · exact atanPositive_sound hq
  · have h := QInterval.mem_neg (atanPositive_sound (neg_nonneg.mpr (le_of_not_ge hq)))
    simpa using h

def atanRange (I : QInterval) : QInterval := ⟨(atanPoint I.lo).lo,(atanPoint I.hi).hi⟩
lemma atanRange_sound {I : QInterval} {x : ℝ} (hx : I.Mem x) :
    (atanRange I).Mem (Real.arctan x) :=
  ⟨(atanPoint_sound I.lo).1.trans (Real.arctan_mono hx.1),
    (Real.arctan_mono hx.2).trans (atanPoint_sound I.hi).2⟩

inductive Expr (n : ℕ)
  | const (q : ℚ) | var (i : Fin n) | pi
  | add (a b : Expr n) | neg (a : Expr n) | mul (a b : Expr n)
  | inv (a : Expr n) | sqrt (a : Expr n)
  | sin (a : Expr n) | cos (a : Expr n) | atan (a : Expr n)
  | abs (a : Expr n) | pow (a : Expr n) (k : ℕ)
  deriving DecidableEq, Repr

namespace Expr
instance {n} : Add (Expr n) := ⟨.add⟩
instance {n} : Neg (Expr n) := ⟨.neg⟩
instance {n} : Sub (Expr n) := ⟨fun a b => .add a (.neg b)⟩
instance {n} : Mul (Expr n) := ⟨.mul⟩
instance {n} : Div (Expr n) := ⟨fun a b => .mul a (.inv b)⟩
instance {n k} : OfNat (Expr n) k := ⟨.const k⟩
instance {n} : Pow (Expr n) ℕ := ⟨.pow⟩

noncomputable def eval {n} (env : Fin n→ℝ) : Expr n→ℝ
  | .const q => q | .var i => env i | .pi => Real.pi
  | .add a b => eval env a+eval env b
  | .neg a => -eval env a | .mul a b => eval env a*eval env b
  | .inv a => (eval env a)⁻¹ | .sqrt a => Real.sqrt (eval env a)
  | .sin a => Real.sin (eval env a) | .cos a => Real.cos (eval env a)
  | .atan a => Real.arctan (eval env a) | .abs a => |eval env a|
  | .pow a k => (eval env a)^k

def bounds {n} (B : Box n) : Expr n→Option QInterval
  | .const q => some (.point q) | .var i => some (B i)
  | .pi => some ⟨3141592653589793238/1000000000000000000,
      3141592653589793239/1000000000000000000⟩
  | .add a b => do return (← bounds B a).add (← bounds B b)
  | .neg a => do return (← bounds B a).neg
  | .mul a b => do return (← bounds B a).mul (← bounds B b)
  | .inv a => do
      let I ← bounds B a
      if 0<I.lo then some I.inv else none
  | .sqrt a => do return sqrtRange (← bounds B a)
  | .sin a => do return sinRange (← bounds B a)
  | .cos a => do return cosRange (← bounds B a)
  | .atan a => do return atanRange (← bounds B a)
  | .abs a => do return absRange (← bounds B a)
  | .pow a k => do return (← bounds B a).pow k

theorem bounds_sound {n} (e : Expr n) (B : Box n) (env : Fin n→ℝ)
    (henv : ∀ i,(B i).Mem (env i)) {I : QInterval}
    (hI : e.bounds B=some I) : I.Mem (e.eval env) := by
  induction e generalizing I with
  | const q => simpa [bounds] using hI ▸ QInterval.mem_point q
  | var i => simpa [bounds] using hI ▸ henv i
  | pi =>
      cases Option.some.inj hI
      exact ⟨pi_hand_enclosure.1.le,pi_hand_enclosure.2.le⟩
  | add a b ha hb =>
      cases hA : a.bounds B with
      | none => simp [bounds,hA] at hI
      | some A =>
          cases hB : b.bounds B with
          | none => simp [bounds,hA,hB] at hI
          | some J =>
              simp only [bounds,hA,hB,Option.bind_some,Option.some.injEq] at hI
              subst I
              exact QInterval.mem_add (ha hA) (hb hB)
  | mul a b ha hb =>
      cases hA : a.bounds B with
      | none => simp [bounds,hA] at hI
      | some A =>
          cases hB : b.bounds B with
          | none => simp [bounds,hA,hB] at hI
          | some J =>
              simp only [bounds,hA,hB,Option.bind_some,Option.some.injEq] at hI
              subst I
              exact QInterval.mem_mul (ha hA) (hb hB)
  | inv a ha =>
      cases hA : a.bounds B with
      | none => simp [bounds,hA] at hI
      | some A =>
          by_cases hpos : 0<A.lo
          · simp only [bounds,hA,Option.bind_some,hpos,if_true,Option.some.injEq] at hI
            subst I
            exact QInterval.mem_inv_pos hpos (ha hA)
          · simp [bounds,hA,hpos] at hI
  | neg a ha | sqrt a ha | sin a ha | cos a ha | atan a ha | abs a ha | pow a k ha =>
      cases hA : a.bounds B with
      | none => simp [bounds,hA] at hI
      | some A =>
          simp only [bounds,hA,Option.bind_some,Option.some.injEq] at hI
          subst I
          first
          | exact QInterval.mem_neg (ha hA)
          | exact sqrtRange_sound (ha hA)
          | exact sinRange_sound (ha hA)
          | exact cosRange_sound (ha hA)
          | exact atanRange_sound (ha hA)
          | exact absRange_sound (ha hA)
          | exact QInterval.mem_pow (ha hA) k
end Expr

structure Problem (n : ℕ) where
  hypotheses : List (Expr n)
  conclusion : Expr n
  deriving DecidableEq, Repr

def Problem.Holds {n : ℕ} (P : Problem n) (env : Fin n → ℝ) : Prop :=
  ∀ e ∈ P.hypotheses, 0 ≤ Expr.eval env e

def negative {n} (B : Box n) (e : Expr n) : Bool :=
  match e.bounds B with | some I => decide (I.hi<0) | none => false

def positive {n} (B : Box n) (e : Expr n) : Bool :=
  match e.bounds B with | some I => decide (0<I.lo) | none => false

def closes {n} (P : Problem n) (B : Box n) : Bool :=
  P.hypotheses.any (negative B) || positive B P.conclusion

def leftBox {n} (B : Box n) (j : Fin n) : Box n :=
  Function.update B j ⟨(B j).lo,((B j).lo+(B j).hi)/2⟩
def rightBox {n} (B : Box n) (j : Fin n) : Box n :=
  Function.update B j ⟨((B j).lo+(B j).hi)/2,(B j).hi⟩

def widest {n} (B : Box (n+1)) : Fin (n+1) :=
  (List.finRange (n+1)).foldl (fun i j =>
    if (B i).hi-(B i).lo<(B j).hi-(B j).lo then j else i) 0

/-- The two children cover the parent, with weak endpoints on both sides. -/
lemma split_covers {n} (B : Box n) (j : Fin n) (env : Fin n→ℝ)
    (hB : ∀i,(B i).Mem (env i)) :
    (∀i,(leftBox B j i).Mem (env i)) ∨ (∀i,(rightBox B j i).Mem (env i)) := by
  rcases le_total (env j) (((B j).lo+(B j).hi)/2:ℚ) with h | h
  · left
    intro i
    by_cases hi : i=j
    · subst i
      simpa [leftBox,QInterval.Mem] using And.intro (hB j).1 h
    · simpa [leftBox,Function.update_of_ne hi] using hB i
  · right
    intro i
    by_cases hi : i=j
    · subst i
      simpa [rightBox,QInterval.Mem] using And.intro h (hB j).2
    · simpa [rightBox,Function.update_of_ne hi] using hB i

def certify {n} : ℕ→Problem (n+1)→Box (n+1)→Bool
  | 0,P,B => closes P B
  | fuel+1,P,B =>
      if closes P B then true else
        certify fuel P (leftBox B (widest B)) && certify fuel P (rightBox B (widest B))

lemma closes_sound {n} {P : Problem n} {B : Box n}
    (h : closes P B=true) (env : Fin n→ℝ) (hB : ∀i,(B i).Mem (env i))
    (hP : ∀e∈P.hypotheses,0≤e.eval env) : 0<P.conclusion.eval env := by
  rcases Bool.or_eq_true.mp h with hneg | hpos
  · obtain ⟨e,he,hcheck⟩ := List.any_eq_true.mp hneg
    cases hI : e.bounds B with
    | none => simp [negative,hI] at hcheck
    | some I =>
        have hn : I.hi<0 := by simpa [negative,hI] using hcheck
        have hs := e.bounds_sound B env hB hI
        have hn' : (I.hi:ℝ)<0 := by exact_mod_cast hn
        exact (not_lt_of_ge (hP e he) (hs.2.trans_lt hn')).elim
  · cases hI : P.conclusion.bounds B with
    | none => simp [positive,hI] at hpos
    | some I =>
        have hp : 0<I.lo := by simpa [positive,hI] using hpos
        have hp' : (0:ℝ)<I.lo := by exact_mod_cast hp
        exact hp'.trans_le (P.conclusion.bounds_sound B env hB hI).1

theorem certify_sound {n fuel} {P : Problem (n+1)} {B : Box (n+1)}
    (h : certify fuel P B=true) (env : Fin (n+1)→ℝ)
    (hB : ∀i,(B i).Mem (env i))
    (hP : ∀e∈P.hypotheses,0≤e.eval env) : 0<P.conclusion.eval env := by
  induction fuel generalizing B with
  | zero => exact closes_sound h env hB hP
  | succ fuel ih =>
      by_cases hc : closes P B=true
      · exact closes_sound hc env hB hP
      · have hh : certify fuel P (leftBox B (widest B))=true ∧
            certify fuel P (rightBox B (widest B))=true := by
          simpa [certify,hc] using h
        rcases split_covers B (widest B) env hB with hl | hr
        · exact ih hh.1 hl
        · exact ih hh.2 hr

end SquaresInCircles.Eight.Arithmetic.RealBox
