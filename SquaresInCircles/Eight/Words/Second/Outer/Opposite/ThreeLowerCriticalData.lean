module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerEnvelopeBounds

/-!
# Eight squares: an explicit parameterization of the reverse critical curve

The free target coordinate `B` is the parameter. The source coordinate `source B` is recovered
by the original circle radical from the scalar critical equation. This gives ordinary
derivatives (`first`, `second`, `third`) without an implicit inverse.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerCritical
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open LowerInverse LowerEnvelope

def height (B : ℝ) : ℝ := (Q0+1-S B)/2
def width (B : ℝ) : ℝ := Real.sqrt (Q0-(height B)^2)
def source (B : ℝ) : ℝ := width B-1/2
def sourceD (B : ℝ) : ℝ := height B*D B/width B
def Domain (B : ℝ) : Prop := B∈Icc (3/100) (3/20) ∧ source B∈Icc 0 (3/5)
def cost (B : ℝ) : ℝ := LowerContact.cost true B (source B)
def first (B : ℝ) : ℝ :=
  factor (U (source B))+2*ratio (source B)*g₁ B-TLabel.d1 (source B)
def second (B : ℝ) : ℝ :=
  -ratio (source B)*factorD (U (source B))+4*(ratio (source B))^2*g₂ B+
    2*ratioD (source B)*g₁ B-TLabel.d2 (source B)
def third (B : ℝ) : ℝ :=
  LowerInverse.X (source B)-TLabel.d3 (source B)+8*(ratio (source B))^3*g₃ B+
    12*ratio (source B)*ratioD (source B)*g₂ B+2*ratioDD (source B)*g₁ B

lemma height_bounds {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    (41/25:ℝ)<height B ∧ height B<193/100 := by
  have hh := S_bounds hB
  dsimp [height]
  norm_num [Q0]
  constructor <;> linarith

lemma width_data {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    0<width B ∧ (width B)^2+(height B)^2=Q0 := by
  have hu := height_bounds hB
  have hrad : 0<Q0-(height B)^2 := by norm_num [Q0]; nlinarith [hu.1,hu.2]
  exact ⟨Real.sqrt_pos.2 hrad,by dsimp [width]; rw [Real.sq_sqrt hrad.le]; ring⟩

lemma source_U {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : U (source B)=height B := by
  have hw := width_data hB
  have hu : 0<height B := by linarith [(height_bounds hB).1]
  have he : Q0-(width B)^2=(height B)^2 := by linarith
  calc
    U (source B)=Real.sqrt (Q0-(width B)^2) := by dsimp [U,arc,source]; ring_nf
    _=height B := by rw [he,Real.sqrt_sq_eq_abs,abs_of_pos hu]

lemma source_W (B : ℝ) : W (source B)=width B := by dsimp [W,source]; ring

lemma source_q {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : q (U (source B))=S B := by
  rw [source_U hB]
  dsimp [q,NegativeTwo.Inverse.q,height]
  ring

lemma height_hasDerivAt {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    HasDerivAt height (-D B) B := by
  have h := ((S_hasDerivAt (mem_outer hB)).const_sub (Q0+1)).div_const 2
  have hf : height = fun x => (Q0+1-S x)/2 := rfl
  rw [hf]
  convert h using 1
  ring

lemma source_hasDerivAt {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    HasDerivAt source (sourceD B) B := by
  have hw := width_data hB
  have hrad : Q0-(height B)^2≠0 := by nlinarith [hw.1,hw.2]
  convert ((((height_hasDerivAt hB).pow 2).const_sub Q0).sqrt hrad).sub_const (1/2)
    using 1
  · rfl
  · dsimp [sourceD,width]
    field_simp [show Real.sqrt (Q0-(height B)^2)≠0 from hw.1.ne']

lemma sourceD_positive {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : 0<sourceD B := by
  have hu : 0<height B := by linarith [(height_bounds hB).1]
  have hd := D_positive (mem_short hB)
  have hw := (width_data hB).1
  dsimp [sourceD]
  positivity

lemma source_strictMono : StrictMonoOn source (Icc (3/100) (3/20)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
  · intro B hB
    exact (source_hasDerivAt hB).continuousAt.continuousWithinAt
  · intro B hB
    exact (source_hasDerivAt (interior_subset hB)).hasDerivWithinAt
  · intro B hB
    exact sourceD_positive (interior_subset hB)

lemma source_monotone : MonotoneOn source (Icc (3/100) (3/20)) := source_strictMono.monotoneOn

lemma domain_between {l u B : ℝ} (hl : Domain l) (hu : Domain u) (hB : B∈Icc l u) : Domain B := by
  have ht : B∈Icc (3/100) (3/20) := ⟨hl.1.1.trans hB.1,hB.2.trans hu.1.2⟩
  exact ⟨ht,⟨hl.2.1.trans (source_monotone hl.1 ht hB.1),
    (source_monotone ht hu.1 hB.2).trans hu.2.2⟩⟩

lemma source_domain {B : ℝ} (hB : Domain B) : source B∈Icc 0 outerDiagonal :=
  LowerGeometry.full_domain ⟨hB.2.1,by linarith [hB.2.2]⟩

lemma shift_mem {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : z B∈LowerInverse.shifts := by
  dsimp [z,LowerInverse.shifts,OppositeTwo.PrimaryInverse.shifts]
  constructor <;> linarith [hB.1,hB.2]

lemma source_ratio_identity {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    ratio (source B)*sourceD B=D B := by
  have hu : 0<height B := by linarith [(height_bounds hB).1]
  have hw := (width_data hB).1
  change W (source B)/U (source B)*(height B*D B/width B)=D B
  rw [source_U hB,source_W]
  field_simp [hu.ne',hw.ne']

lemma source_eq_of_S {B b : ℝ} (hB : B∈Icc (3/100) (3/20))
    (hb : b∈Icc 0 (3/5)) (he : S B=q (U b)) : source B=b := by
  have hu : height B=U b := by
    dsimp [height]
    rw [he]
    dsimp [q,NegativeTwo.Inverse.q]
    ring
  have hw := width_data hB
  have hc := UW_circle (outer_domain (LowerGeometry.full_domain ⟨hb.1,by linarith [hb.2]⟩))
  rw [hu] at hw
  have hv : 0<W b := by dsimp [W]; linarith [hb.1]
  have hew : width B=W b := by nlinarith [hw.1,hw.2]
  dsimp [source]
  rw [hew]
  dsimp [W]
  ring

lemma critical_speed {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    LowerInverse.speed (z B) (source B)=1/p B := by
  have hp := p_positive (mem_outer hB)
  change Real.sqrt (q (U (source B))-(z B)^2)=1/p B
  rw [source_q hB]
  have he : S B-(z B)^2=(1/p B)^2 := by dsimp [S]; ring
  rw [he,Real.sqrt_sq_eq_abs,abs_of_pos (by positivity : 0<1/p B)]

lemma stationary {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    LowerContact.freeFirst true B (source B)=0 := by
  change 1/LowerInverse.speed (z B) (source B)-p B=0
  rw [critical_speed hB,one_div_one_div,sub_self]

lemma actual_first {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    LowerContact.outerFirst true B (source B)=first B := by
  have hp := p_positive (mem_outer hB)
  have hs := S_positive (mem_outer hB)
  change factor (U (source B))-z B*ratio (source B)/
    (q (U (source B))*LowerInverse.speed (z B) (source B))-TLabel.d1 (source B)=first B
  rw [critical_speed hB,source_q hB]
  dsimp [first,g₁,h]
  field_simp [hp.ne',hs.ne']
  ring

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerCritical
