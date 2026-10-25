module

public import SquaresInCircles.Eight.Arithmetic.Taylor
public import SquaresInCircles.Eight.Words.Second.WordData

/-!
# Eight squares: exact products at named analytic reference points

The bilinear enclosure follows twice from the elementary affine
endpoint inequality.  It is used only to combine exact rational
coefficient and Taylor brackets at the fixed analytic references.
-/

section
/-!
## Exact arithmetic transfer at a single physical circle reference

The inputs bracket one coordinate and its one circle radical.  The
outputs are explicit rational formulas for the value and first two
derivatives of the target label.  This arithmetic lemma is used only
after the actual fixed reference has been established by circle squaring
and Taylor inequalities; it makes no assertion about a mesh of points.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.FixedReference

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def valueLo (bl bh _ul uh : ℝ) : ℝ :=
  167/10000+(121161/50000)*bl-(2867/3125)*bh^2-(95769/100000)*(uh-1/2)*bh
def valueHi (bl bh ul _uh : ℝ) : ℝ :=
  167/10000+(121161/50000)*bh-(2867/3125)*bl^2-(95769/100000)*(ul-1/2)*bl
def firstLo (bl bh _ul uh : ℝ) : ℝ :=
  121161/50000-(5734/3125)*bh-(95769/100000)*(uh-1/2)+
    (95769/100000)*bl*((bl+1/2)/uh)
def firstHi (bl bh ul _uh : ℝ) : ℝ :=
  121161/50000-(5734/3125)*bl-(95769/100000)*(ul-1/2)+
    (95769/100000)*bh*((bh+1/2)/ul)
def secondLo (bl _bh _ul uh : ℝ) : ℝ :=
  -5734/3125+(95769/50000)*((bl+1/2)/uh)+(95769/100000)*bl*(Q0/uh^3)
def secondHi (_bl bh ul _uh : ℝ) : ℝ :=
  -5734/3125+(95769/50000)*((bh+1/2)/ul)+(95769/100000)*bh*(Q0/ul^3)

lemma ratios {b bl bh ul uh : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hbox : b∈Icc bl bh) (hU : U b∈Icc ul uh) (hbl : 0≤bl) (hul : 1/2<ul) :
    (bl+1/2)/uh≤ratio b ∧ ratio b≤(bh+1/2)/ul ∧
      Q0/uh^3≤ratioD b ∧ ratioD b≤Q0/ul^3 := by
  have hu := U_positive (outer_domain hb)
  have hul0 : 0<ul := by linarith
  have huh0 : 0<uh := hu.trans_le hU.2
  have hrl : 0≤(bl+1/2)/uh := by positivity
  have hrh : 0≤(bh+1/2)/ul := by
    have hbh : 0≤bh := hbl.trans (hbox.1.trans hbox.2)
    positivity
  have hUlo3 := pow_le_pow_left₀ hul0.le hU.1 3
  have hUhi3 := pow_le_pow_left₀ hu.le hU.2 3
  refine ⟨?_,?_,?_,?_⟩
  · change (bl+1/2)/uh≤W b/U b
    apply (le_div_iff₀ hu).2
    have hm := mul_le_mul_of_nonneg_left hU.2 hrl
    have he : ((bl+1/2)/uh)*uh=bl+1/2 := by field_simp [huh0.ne']
    rw [he] at hm
    dsimp [W]
    linarith [hbox.1]
  · change W b/U b≤(bh+1/2)/ul
    apply (div_le_iff₀ hu).2
    have hm := mul_le_mul_of_nonneg_left hU.1 hrh
    have he : ((bh+1/2)/ul)*ul=bh+1/2 := by field_simp [hul0.ne']
    rw [he] at hm
    dsimp [W]
    nlinarith [hbox.2]
  · change Q0/uh^3≤Q0/(U b)^3
    apply (le_div_iff₀ (pow_pos hu 3)).2
    have hm := mul_le_mul_of_nonneg_left hUhi3
      (show 0≤Q0/uh^3 by norm_num [Q0]; positivity)
    have he : (Q0/uh^3)*uh^3=Q0 := by field_simp [huh0.ne']
    simpa only [he] using hm
  · change Q0/(U b)^3≤Q0/ul^3
    apply (div_le_iff₀ (pow_pos hu 3)).2
    have hm := mul_le_mul_of_nonneg_left hUlo3
      (show 0≤Q0/ul^3 by norm_num [Q0]; positivity)
    have he : (Q0/ul^3)*ul^3=Q0 := by field_simp [hul0.ne']
    rw [he] at hm
    nlinarith

theorem target {b bl bh ul uh : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hbox : b∈Icc bl bh) (hU : U b∈Icc ul uh) (hbl : 0≤bl) (hul : 1/2<ul) :
    valueLo bl bh ul uh≤T b ∧ T b≤valueHi bl bh ul uh ∧
      firstLo bl bh ul uh≤TLabel.d1 b ∧ TLabel.d1 b≤firstHi bl bh ul uh ∧
      secondLo bl bh ul uh≤TLabel.d2 b ∧ TLabel.d2 b≤ secondHi bl bh ul uh := by
  have hr := ratios hb hbox hU hbl hul
  have hul0 : 0<ul := by linarith
  have huh0 : 0<uh := (U_positive (outer_domain hb)).trans_le hU.2
  have hbh : 0≤bh := hb.1.trans hbox.2
  have harc0 : 0≤U b-1/2 := by linarith [hU.1]
  have harcH : 0≤uh-1/2 := by linarith [hU.1,hU.2]
  have hradL : 0≤(bl+1/2)/uh := by positivity
  have hr0 : 0≤ratio b := by linarith [(outer_ratio_bounds hb).1]
  have hD0 : 0≤ratioD b := (outer_ratio_bounds hb).2.2.1.le
  have hq : 0≤Q0 := by norm_num [Q0]
  have hb2lo := pow_le_pow_left₀ hbl hbox.1 2
  have hb2hi := pow_le_pow_left₀ hb.1 hbox.2 2
  have hablo := mul_le_mul (show ul-1/2≤U b-1/2 by linarith [hU.1]) hbox.1 hbl harc0
  have habhi := mul_le_mul (show U b-1/2≤uh-1/2 by linarith [hU.2]) hbox.2 hb.1 harcH
  have hbrlo := mul_le_mul hbox.1 hr.1 hradL hb.1
  have hbrhi := mul_le_mul hbox.2 hr.2.1 hr0 hbh
  have hbDlo := mul_le_mul hbox.1 hr.2.2.1 (by positivity : 0≤Q0/uh^3) hb.1
  have hbDhi := mul_le_mul hbox.2 hr.2.2.2 hD0 hbh
  have hv : T b=167/10000+(121161/50000)*b-(2867/3125)*b^2-
      (95769/100000)*(U b-1/2)*b := by
    dsimp [T,RoleLabel.outer,RoleLabel.eval,TLabel,U]
    ring
  have hd : TLabel.d1 b=121161/50000-(5734/3125)*b-
      (95769/100000)*(U b-1/2)+(95769/100000)*b*ratio b := by
    dsimp [RoleLabel.d1,TLabel,U]
    ring
  have hdd : TLabel.d2 b= -5734/3125+(95769/50000)*ratio b+
      (95769/100000)*b*ratioD b := by
    dsimp [RoleLabel.d2,TLabel]
    ring
  rw [hv,hd,hdd]
  dsimp only [valueLo,valueHi,firstLo,firstHi,secondLo,secondHi]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · linarith only [hbox.1,hb2hi,habhi]
  · linarith only [hbox.2,hb2lo,hablo]
  · linarith only [hbox.2,hU.2,hbrlo]
  · linarith only [hbox.1,hU.1,hbrhi]
  · linarith only [hr.1,hbDlo]
  · linarith only [hr.2.1,hbDhi]

end SquaresInCircles.Eight.SecondWord.FixedReference
end
end
end

section
/-!
## Exact circle references for the original second-word labels

The only enclosures here are proved from the one physical circle equation.
Multiplying a label derivative by its positive circle radical makes the
reference comparison affine in that radical.  Thus a rational square
bracket supplies a reference without an interval evaluation procedure.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

lemma shifted_chart_reference {b l u : ℝ} (hb : b∈Icc 0 outerAxial)
    (hl : 0≤l) (hu : 0≤u)
    (hlo : l^2+(W b)^2<Q0) (hhi : Q0<u^2+(W b)^2) :
    l<U b ∧ U b<u := by
  have hc := UW_circle hb
  have hp := U_positive hb
  constructor <;> nlinarith

namespace Asymmetric

lemma rational_outer_mem {b : ℝ} (hb : b∈Icc 0 (899/1000)) :
    b∈Icc 0 outerDiagonal :=
  ⟨hb.1,by linarith [hb.2,fine_outer_endpoint_bounds.2]⟩

lemma shifted_reference {b l u : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hl : 0≤l) (hu : 0≤u)
    (hlo : l^2+(W b)^2<Q0) (hhi : Q0<u^2+(W b)^2) :
    l<U b ∧ U b<u := shifted_chart_reference (outer_domain hb) hl hu hlo hhi

end Asymmetric

lemma affine_min_le {c l u x : ℝ} (hx : x∈Icc l u) :
    min (c*l) (c*u)≤c*x := by
  by_cases hc : 0≤c
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hx.1 hc)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hx.2 (le_of_not_ge hc))

lemma affine_le_max {c l u x : ℝ} (hx : x∈Icc l u) :
    c*x≤ max (c*l) (c*u) := by
  by_cases hc : 0≤c
  · exact (mul_le_mul_of_nonneg_left hx.2 hc).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge hc)).trans (le_max_left _ _)

lemma RoleLabel.first_numerator (H : RoleLabel) {b : ℝ}
    (hb : b∈Icc 0 outerAxial) :
    H.d1 b*U b=(H.q+2*H.r*b-H.s/2)*U b+
      H.s*(Q0-(W b)^2)-(H.p+H.s*b)*W b := by
  have hp := U_positive hb
  have hc := UW_circle hb
  have hr : ratio b*U b=W b := by
    change (W b/U b)*U b=W b
    field_simp [hp.ne']
  dsimp [RoleLabel.d1,U,W] at hc hr ⊢
  linear_combination H.s*hc-(H.p+H.s*b)*hr

lemma RoleLabel.third_numerator (H : RoleLabel) {b : ℝ}
    (hb : b∈Icc 0 outerAxial) :
    H.d3 b*(U b)^5= -3*Q0*(H.s*Q0+(H.p-H.s/2)*W b) := by
  have hu := U_positive hb
  have hu0 : U b≠0 := hu.ne'
  have hc := UW_circle hb
  have hD : ratioD b=Q0/(U b)^3 := rfl
  have hDD : ratioDD b=3*Q0*(W b)/(U b)^5 := rfl
  have he : H.d3 b*(U b)^5=
      -3*Q0*(H.s*(U b)^2+(H.p+H.s*b)*W b) := by
    rw [RoleLabel.d3,hD,hDD]
    field_simp
    ring
  rw [he]
  simp only [W] at hc ⊢
  linear_combination -3*Q0*H.s*hc

/-- The hypotheses following the circle domain contain rational data only
when the reference and radical bracket are rational. -/
lemma RoleLabel.first_chart_reference (H : RoleLabel) {b l u dlo dhi : ℝ}
    (hb : b∈Icc 0 outerAxial)
    (hl : 0≤l) (hu : 0≤u)
    (hlo : l^2+(W b)^2<Q0) (hhi : Q0<u^2+(W b)^2)
    (hdlo : 0< min ((H.q+2*H.r*b-H.s/2-dlo)*l)
      ((H.q+2*H.r*b-H.s/2-dlo)*u)+
        H.s*(Q0-(W b)^2)-(H.p+H.s*b)*W b)
    (hdhi : max ((H.q+2*H.r*b-H.s/2-dhi)*l)
      ((H.q+2*H.r*b-H.s/2-dhi)*u)+
        H.s*(Q0-(W b)^2)-(H.p+H.s*b)*W b<0) :
    dlo<H.d1 b ∧ H.d1 b<dhi := by
  have hU := shifted_chart_reference hb hl hu hlo hhi
  have hp := U_positive hb
  have he := H.first_numerator hb
  have hlow := affine_min_le (c := H.q+2*H.r*b-H.s/2-dlo)
    ⟨hU.1.le,hU.2.le⟩
  have hhigh := affine_le_max (c := H.q+2*H.r*b-H.s/2-dhi)
    ⟨hU.1.le,hU.2.le⟩
  constructor <;> nlinarith

lemma primary_ratio_one {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    1≤ratio a := by
  have hp := U_positive (primary_domain ha)
  have hs := primary_state ha
  change 1≤W a/U a
  apply (one_le_div hp).2
  dsimp [U,W]
  linarith [hs.2.1]

lemma RoleLabel.affine_difference_hasDerivAt (H : RoleLabel) (c : ℝ)
    {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    HasDerivAt (fun t => c*t-H.outer t) (c-H.d1 b) b := by
  have h1 : HasDerivAt (fun t => c*t) (c*1) b := (hasDerivAt_id' b).const_mul c
  exact (h1.sub (H.outer_hasDerivAt hb)).congr_deriv (by ring)

lemma RoleLabel.tangent_upper (H : RoleLabel) {l u x t : ℝ}
    (hdom : Icc l u⊆Icc 0 outerAxial)
    (hx : x∈Icc l u) (ht : t∈Icc l u)
    (hsecond : ∀ y∈Icc l u, H.d2 y≤0) :
    H.outer x≤H.outer t+H.d1 t*(x-t) := by
  have hh := curvature_tangent (f := fun y => -H.outer y)
    (d := fun y => -H.d1 y) (dd := fun y => -H.d2 y) (κ := 0)
    hx ht
    (fun y hy => (H.outer_hasDerivAt (hdom hy)).neg)
    (fun y hy => (H.d1_hasDerivAt (hdom hy)).neg)
    (fun y hy => neg_nonneg.mpr (hsecond y hy))
  linarith

end SquaresInCircles.Eight.SecondWord
end
end
end

section
/-!
## Exact fixed-reference arithmetic for every literal outer label

An already established bracket for one
physical coordinate and its circle radical gives explicit bounds for
the value and two derivatives of any literal role label.  This is
ordinary finite arithmetic at a named reference, not a cover of the
coordinate domain or an external arithmetic certificate.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.GeneralReference
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def lo (c l u : ℝ) : ℝ := min (c*l) (c*u)
def hi (c l u : ℝ) : ℝ := max (c*l) (c*u)
def rlo (bl _bh _ul uh : ℝ) : ℝ := (bl+1/2)/uh
def rhi (_bl bh ul _uh : ℝ) : ℝ := (bh+1/2)/ul
def dlo (_bl _bh _ul uh : ℝ) : ℝ := Q0/uh^3
def dhi (_bl _bh ul _uh : ℝ) : ℝ := Q0/ul^3

def valueLo (H : RoleLabel) (bl bh ul uh : ℝ) : ℝ :=
  H.c+lo H.p (ul-1/2) (uh-1/2)+lo H.q bl bh+lo H.r (bl^2) (bh^2)+
    lo H.s ((ul-1/2)*bl) ((uh-1/2)*bh)
def valueHi (H : RoleLabel) (bl bh ul uh : ℝ) : ℝ :=
  H.c+hi H.p (ul-1/2) (uh-1/2)+hi H.q bl bh+hi H.r (bl^2) (bh^2)+
    hi H.s ((ul-1/2)*bl) ((uh-1/2)*bh)
def firstLo (H : RoleLabel) (bl bh ul uh : ℝ) : ℝ :=
  H.q+lo (2*H.r) bl bh+lo H.s (ul-1/2) (uh-1/2)+
    lo (-H.p) (rlo bl bh ul uh) (rhi bl bh ul uh)+
    lo (-H.s) (bl*rlo bl bh ul uh) (bh*rhi bl bh ul uh)
def firstHi (H : RoleLabel) (bl bh ul uh : ℝ) : ℝ :=
  H.q+hi (2*H.r) bl bh+hi H.s (ul-1/2) (uh-1/2)+
    hi (-H.p) (rlo bl bh ul uh) (rhi bl bh ul uh)+
    hi (-H.s) (bl*rlo bl bh ul uh) (bh*rhi bl bh ul uh)
def secondLo (H : RoleLabel) (bl bh ul uh : ℝ) : ℝ :=
  2*H.r+lo (-2*H.s) (rlo bl bh ul uh) (rhi bl bh ul uh)+
    lo (-H.p) (dlo bl bh ul uh) (dhi bl bh ul uh)+
    lo (-H.s) (bl*dlo bl bh ul uh) (bh*dhi bl bh ul uh)
def secondHi (H : RoleLabel) (bl bh ul uh : ℝ) : ℝ :=
  2*H.r+hi (-2*H.s) (rlo bl bh ul uh) (rhi bl bh ul uh)+
    hi (-H.p) (dlo bl bh ul uh) (dhi bl bh ul uh)+
    hi (-H.s) (bl*dlo bl bh ul uh) (bh*dhi bl bh ul uh)

lemma bounds {l u x : ℝ} (c : ℝ) (hx : x∈Icc l u) :
    lo c l u≤c*x ∧ c*x≤hi c l u :=
  ⟨affine_min_le hx,affine_le_max hx⟩

theorem label (H : RoleLabel) {b bl bh ul uh : ℝ}
    (hb : b∈Icc 0 outerDiagonal) (hbox : b∈Icc bl bh)
    (hU : U b∈Icc ul uh) (hbl : 0≤bl) (hul : 1/2<ul) :
    valueLo H bl bh ul uh≤H.outer b ∧ H.outer b≤valueHi H bl bh ul uh ∧
      firstLo H bl bh ul uh≤H.d1 b ∧ H.d1 b≤firstHi H bl bh ul uh ∧
      secondLo H bl bh ul uh≤H.d2 b ∧ H.d2 b≤ secondHi H bl bh ul uh := by
  have hr := FixedReference.ratios hb hbox hU hbl hul
  have hul0 : 0<ul := by linarith
  have huh0 : 0<uh := (U_positive (outer_domain hb)).trans_le hU.2
  have ha : arc b∈Icc (ul-1/2) (uh-1/2) := by
    dsimp [U] at hU
    constructor <;> linarith [hU.1,hU.2]
  have harc0 : 0≤arc b := by linarith [ha.1]
  have hbh : 0≤bh := hbl.trans (hbox.1.trans hbox.2)
  have hab : arc b*b∈Icc ((ul-1/2)*bl) ((uh-1/2)*bh) := by
    exact ⟨mul_le_mul ha.1 hbox.1 hbl harc0,
      mul_le_mul ha.2 hbox.2 hb.1 (by linarith [hU.1,hU.2])⟩
  have hb2 : b^2∈Icc (bl^2) (bh^2) :=
    ⟨pow_le_pow_left₀ hbl hbox.1 2,pow_le_pow_left₀ hb.1 hbox.2 2⟩
  have hri : ratio b∈Icc (rlo bl bh ul uh) (rhi bl bh ul uh) := ⟨hr.1,hr.2.1⟩
  have hdi : ratioD b∈Icc (dlo bl bh ul uh) (dhi bl bh ul uh) := ⟨hr.2.2.1,hr.2.2.2⟩
  have hr0 : 0≤ratio b := by linarith [(outer_ratio_bounds hb).1]
  have hd0 : 0≤ratioD b := (outer_ratio_bounds hb).2.2.1.le
  have hrl : 0≤rlo bl bh ul uh := by dsimp [rlo]; positivity
  have hrh : 0≤rhi bl bh ul uh := by dsimp [rhi]; positivity
  have hdl : 0≤dlo bl bh ul uh := by dsimp [dlo]; norm_num [Q0]; positivity
  have hdh : 0≤dhi bl bh ul uh := by dsimp [dhi]; norm_num [Q0]; positivity
  have hbr : b*ratio b∈Icc (bl*rlo bl bh ul uh) (bh*rhi bl bh ul uh) :=
    ⟨mul_le_mul hbox.1 hri.1 hrl hb.1,mul_le_mul hbox.2 hri.2 hr0 hbh⟩
  have hbd : b*ratioD b∈Icc (bl*dlo bl bh ul uh) (bh*dhi bl bh ul uh) :=
    ⟨mul_le_mul hbox.1 hdi.1 hdl hb.1,mul_le_mul hbox.2 hdi.2 hd0 hbh⟩
  have hvp := bounds H.p ha
  have hvq := bounds H.q hbox
  have hvr := bounds H.r hb2
  have hvs := bounds H.s hab
  have hdr := bounds (2*H.r) hbox
  have hds := bounds H.s ha
  have hdp := bounds (-H.p) hri
  have hdbr := bounds (-H.s) hbr
  have hddr := bounds (-2*H.s) hri
  have hddp := bounds (-H.p) hdi
  have hddbr := bounds (-H.s) hbd
  dsimp only [valueLo,valueHi,firstLo,firstHi,secondLo,secondHi,
    RoleLabel.outer,RoleLabel.eval,RoleLabel.d1,RoleLabel.d2]
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith

end SquaresInCircles.Eight.SecondWord.GeneralReference
end
end
end

section
/-!
## Exact references for the positive edge-three target label

These enclosures retain the signs of every coefficient of the literal
label `L`.  Their hypotheses are a coordinate bracket and a square-
proved bracket for its actual circle radical, with no verifier table.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.LReference

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio ratioD)

def valueLo (bl bh _ul uh : ℝ) : ℝ :=
  793/20000+(38551/10000)*bl-(37437/25000)*bh^2-
    (94721/50000)*(uh-1/2)*bh
def valueHi (bl bh ul _uh : ℝ) : ℝ :=
  793/20000+(38551/10000)*bh-(37437/25000)*bl^2-
    (94721/50000)*(ul-1/2)*bl
def firstLo (bl bh _ul uh : ℝ) : ℝ :=
  38551/10000-(37437/12500)*bh-(94721/50000)*(uh-1/2)+
    (94721/50000)*bl*((bl+1/2)/uh)
def firstHi (bl bh ul _uh : ℝ) : ℝ :=
  38551/10000-(37437/12500)*bl-(94721/50000)*(ul-1/2)+
    (94721/50000)*bh*((bh+1/2)/ul)
def secondLo (bl _bh _ul uh : ℝ) : ℝ :=
  -(37437/12500)+(94721/25000)*((bl+1/2)/uh)+
    (94721/50000)*bl*(Q0/uh^3)
def secondHi (_bl bh ul _uh : ℝ) : ℝ :=
  -(37437/12500)+(94721/25000)*((bh+1/2)/ul)+
    (94721/50000)*bh*(Q0/ul^3)

theorem target {b bl bh ul uh : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hbox : b∈Icc bl bh) (hU : U b∈Icc ul uh)
    (hbl : 0≤bl) (hul : 1/2<ul) :
    valueLo bl bh ul uh≤L b ∧ L b≤valueHi bl bh ul uh ∧
      firstLo bl bh ul uh≤LLabel.d1 b ∧ LLabel.d1 b≤firstHi bl bh ul uh ∧
      secondLo bl bh ul uh≤LLabel.d2 b ∧ LLabel.d2 b≤ secondHi bl bh ul uh := by
  have hr := FixedReference.ratios hb hbox hU hbl hul
  have hul0 : 0<ul := by linarith
  have huh0 : 0<uh := by linarith [hU.1,hU.2]
  have hrad : 0≤U b-1/2 := by linarith [hU.1]
  have hradhi : 0≤uh-1/2 := by linarith [hU.1,hU.2]
  have hprodlo := mul_le_mul
    (show ul-1/2≤U b-1/2 by linarith [hU.1]) hbox.1 hbl hrad
  have hprodhi := mul_le_mul
    (show U b-1/2≤uh-1/2 by linarith [hU.2]) hbox.2 hb.1 hradhi
  have hslo : bl^2≤b^2 := pow_le_pow_left₀ hbl hbox.1 2
  have hshi : b^2≤bh^2 := pow_le_pow_left₀ hb.1 hbox.2 2
  have hr0 : 0≤ratio b := (ShortOuterOne.SameContact.ratio_pos (outer_domain hb)).le
  have hrl0 : 0≤(bl+1/2)/uh := by positivity
  have hbrlo := mul_le_mul hbox.1 hr.1 hrl0 hb.1
  have hbrhi := mul_le_mul hbox.2 hr.2.1 hr0 (hb.1.trans hbox.2)
  have hD0 : 0≤ratioD b := (outer_ratio_bounds hb).2.2.1.le
  have hDl0 : 0≤Q0/uh^3 := by norm_num [Q0]; positivity
  have hbDlo := mul_le_mul hbox.1 hr.2.2.1 hDl0 hb.1
  have hbDhi := mul_le_mul hbox.2 hr.2.2.2 hD0 (hb.1.trans hbox.2)
  have hv : L b=793/20000+(38551/10000)*b-(37437/25000)*b^2-
      (94721/50000)*(U b-1/2)*b := by
    dsimp [L,RoleLabel.outer,RoleLabel.eval,LLabel,U]
    ring
  have hd : LLabel.d1 b=38551/10000-(37437/12500)*b-
      (94721/50000)*(U b-1/2)+(94721/50000)*b*ratio b := by
    dsimp [RoleLabel.d1,LLabel,U]
    ring
  have hdd : LLabel.d2 b= -(37437/12500)+(94721/25000)*ratio b+
      (94721/50000)*b*ratioD b := by
    dsimp [RoleLabel.d2,LLabel]
    ring
  rw [hv,hd,hdd]
  dsimp only [valueLo,valueHi,firstLo,firstHi,secondLo,secondHi]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · linarith only [hbox.1,hshi,hprodhi]
  · linarith only [hbox.2,hslo,hprodlo]
  · linarith only [hbox.2,hU.2,hbrlo]
  · linarith only [hbox.1,hU.1,hbrhi]
  · linarith only [hr.1,hbDlo]
  · linarith only [hr.2.1,hbDhi]

end SquaresInCircles.Eight.SecondWord.LReference
end
end
end

section
/-!
## Adjacent Taylor supports at the physical angle cap

The degree-eleven and degree-twelve bounds follow by integration from
the existing degree-ten support.  The single cap reference is then a
rational substitution in these whole-half-line inequalities.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.ReferenceTrig

open Arithmetic

def sin11 (x : ℝ) : ℝ := sin9 x-x^11/39916800
def cos12 (x : ℝ) : ℝ := cos10 x+x^12/479001600

lemma sin11_le_sin {x : ℝ} (hx : 0≤x) : sin11 x≤Real.sin x := by
  have hh := nonneg_of_deriv_nonneg (fun t => Real.sin t-sin11 t)
    (by dsimp [sin11,sin9,sin7]; fun_prop)
    (by norm_num [sin11,sin9,sin7])
    (fun t ht => by
      simp (disch := fun_prop) [sin11,sin9,sin7]
      have hc := cos10_le_cos ht
      dsimp [cos10,cos8] at hc
      linarith) hx
  linarith

lemma cos_le_cos12 {x : ℝ} (hx : 0≤x) : Real.cos x≤cos12 x := by
  have hh := nonneg_of_deriv_nonneg (fun t => cos12 t-Real.cos t)
    (by dsimp [cos12,cos10,cos8]; fun_prop)
    (by norm_num [cos12,cos10,cos8])
    (fun t ht => by
      simp (disch := fun_prop) [cos12,cos10,cos8]
      have hs := sin11_le_sin ht
      dsimp [sin11,sin9,sin7] at hs
      linarith) hx
  linarith

end SquaresInCircles.Eight.SecondWord.ReferenceTrig

namespace SquaresInCircles.Eight.ShortOuterOne.FiveSame

open Arithmetic SecondWord.ReferenceTrig

lemma cap_fine :
    (1610544218/2500000000:ℝ)<Real.sin (7/10) ∧
      Real.sin (7/10)<644217688/1000000000 ∧
      (956052734/1250000000:ℝ)<Real.cos (7/10) ∧
      Real.cos (7/10)<7648421873/10000000000 := by
  have hs := sin11_le_sin (show (0:ℝ)≤7/10 by norm_num)
  have hsu := sin_le_sin9 (show (0:ℝ)≤7/10 by norm_num)
  have hc := cos10_le_cos (show (0:ℝ)≤7/10 by norm_num)
  have hcu := cos_le_cos12 (show (0:ℝ)≤7/10 by norm_num)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hs hsu hc hcu
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

end SquaresInCircles.Eight.ShortOuterOne.FiveSame
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PointProducts

open Arithmetic ReferenceTrig

lemma product {x y xl xu yl yu : ℝ} (hx : x∈Icc xl xu) (hy : y∈Icc yl yu) :
    x*y∈Icc (min (min (xl*yl) (xl*yu)) (min (xu*yl) (xu*yu)))
      (max (max (xl*yl) (xl*yu)) (max (xu*yl) (xu*yu))) := by
  have hxlo : min (xl*y) (xu*y)≤x*y := by
    simpa only [mul_comm] using affine_min_le (c := y) hx
  have hxhi : x*y≤ max (xl*y) (xu*y) := by
    simpa only [mul_comm] using affine_le_max (c := y) hx
  exact ⟨(min_le_min (affine_min_le (c := xl) hy)
    (affine_min_le (c := xu) hy)).trans hxlo,
    hxhi.trans (max_le_max (affine_le_max (c := xl) hy)
      (affine_le_max (c := xu) hy))⟩

lemma trig {t : ℝ} (ht : 0≤t) :
    Real.sin t∈Icc (sin11 t) (sin9 t) ∧
      Real.cos t∈Icc (cos10 t) (cos12 t) :=
  ⟨⟨sin11_le_sin ht,sin_le_sin9 ht⟩,⟨cos10_le_cos ht,cos_le_cos12 ht⟩⟩

end SquaresInCircles.Eight.SecondWord.PointProducts
end
end
end
