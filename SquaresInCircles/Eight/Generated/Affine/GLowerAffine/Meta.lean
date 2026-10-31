module

public import SquaresInCircles.Eight.Arithmetic.AffineTableData
public meta import SquaresInCircles.Eight.Certificates.Data

/-! Exact rational metadata for `GLowerAffine`; its context and rows are checked separately. -/
@[expose] public section
namespace SquaresInCircles.Eight.Generated.Affine.GLowerAffine

noncomputable def table : Arithmetic.AffineTableMeta :=
  certificate_data% "../../../../../data/eight/affine/GLowerAffine.meta.json"

end SquaresInCircles.Eight.Generated.Affine.GLowerAffine
