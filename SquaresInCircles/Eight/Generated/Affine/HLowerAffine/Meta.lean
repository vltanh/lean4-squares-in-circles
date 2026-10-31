module

public import SquaresInCircles.Eight.Arithmetic.AffineTableData
public meta import SquaresInCircles.Eight.Certificates.Data

/-! Exact rational metadata for `HLowerAffine`; its context and rows are checked separately. -/
@[expose] public section
namespace SquaresInCircles.Eight.Generated.Affine.HLowerAffine

noncomputable def table : Arithmetic.AffineTableMeta :=
  certificate_data% "../../../../../data/eight/affine/HLowerAffine.meta.json"

end SquaresInCircles.Eight.Generated.Affine.HLowerAffine
