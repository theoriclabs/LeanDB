import LeanDb.Model
import LeanDb.Native.Storage
import LeanDb.Native.Witness
import LeanDb.Native.Resources
import LeanDb.Native.Operations
import LeanDb.Native.Interpreter
import LeanDb.Native.Schema

/-! # LeanDb.Native: model programs on SQLite

`native_schema% S := T₁, T₂, …` derives, from the `LeanDb.Model` declarations of each entity
(fields, `constraint … : unique`, `constraint … : cascade`, `link`), the native entities and
schema `S`, and the evidence (`EntityStorage`, `UniqueStorage`, `LinkEvidence`,
`ColumnEvidence`) that `storageResources S` carries. A model program generalized with
`derive_requirements` runs on it with `runCommand`/`runQuery` (or the `commandInterpreter` /
`queryInterpreter` directly), and the same program runs in memory (`LeanDb.Model.Memory`). -/
