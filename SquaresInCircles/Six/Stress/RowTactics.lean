import SquaresInCircles.Six.Stress.FixedData.Checks

/-!
# Fixed-row application tactics

These macros only apply proved row-exclusion theorems, simplify exact finite
data, and discharge explicit bit, axis and real-domain premises. They do not
run an external checker or introduce an assumption.
-/

open SquaresInCircles.Six.Stress

syntax "exclude_main " num " for " term : tactic
syntax "exclude_hard " num " for " term : tactic
syntax "exclude_app " num " for " term : tactic
syntax "exclude_tail " num " for " term : tactic
syntax "exclude_bridge " num " for " term : tactic

macro_rules
  | `(tactic| exclude_main $i:num for $P:term) => `(tactic|
      apply (FixedData.RowId.main $i).excludes $P
      · norm_num [FixedData.RowId.row,FixedData.defaultRows,FixedSpec.Realized]
        <;> aesop
      · rw [FixedRow.inDomain_iff]
        norm_num [FixedData.RowId.row,FixedData.defaultRows,PiBound.value]
        <;> (repeat' constructor)
        <;> linarith)
  | `(tactic| exclude_hard $i:num for $P:term) => `(tactic|
      apply (FixedData.RowId.hard $i).excludes $P
      · norm_num [FixedData.RowId.row,FixedData.hardRows,FixedSpec.Realized]
        <;> aesop
      · rw [FixedRow.inDomain_iff]
        norm_num [FixedData.RowId.row,FixedData.hardRows,PiBound.value]
        <;> (repeat' constructor)
        <;> linarith)
  | `(tactic| exclude_app $i:num for $P:term) => `(tactic|
      apply (FixedData.RowId.app $i).excludes $P
      · norm_num [FixedData.RowId.row,FixedData.appendixcRows,FixedSpec.Realized]
        <;> aesop
      · rw [FixedRow.inDomain_iff]
        norm_num [FixedData.RowId.row,FixedData.appendixcRows,PiBound.value]
        <;> (repeat' constructor)
        <;> linarith)
  | `(tactic| exclude_tail $i:num for $P:term) => `(tactic|
      apply (FixedData.RowId.tail $i).excludes $P
      · norm_num [FixedData.RowId.row,FixedData.tailsRows,FixedSpec.Realized]
        <;> aesop
      · rw [FixedRow.inDomain_iff]
        norm_num [FixedData.RowId.row,FixedData.tailsRows,PiBound.value]
        <;> (repeat' constructor)
        <;> linarith)
  | `(tactic| exclude_bridge $i:num for $P:term) => `(tactic|
      apply (FixedData.RowId.bridge $i).excludes $P
      · norm_num [FixedData.RowId.row,FixedData.bridgeRows,FixedSpec.Realized]
        <;> aesop
      · rw [FixedRow.inDomain_iff]
        norm_num [FixedData.RowId.row,FixedData.bridgeRows,PiBound.value]
        <;> (repeat' constructor)
        <;> linarith)
