import LeanDb.Model.Metadata
import LeanDb.Model.Represent
import LeanDb.Model.Resources
import LeanDb.Model.Request
import LeanDb.Model.DB
import LeanDb.Model.Deriving
import LeanDb.Model.Entities
import LeanDb.Model.Requirements
import LeanDb.Model.Memory

/-! # LeanDb.Model: the portable data model

`import LeanDb.Model` and `open LeanDb.Model`. No SQLite, no native code: the import closure
is this library, `LeanOntology` and Lean, so it compiles with LeanJS too.

```
structure Game where
  board : Board
  deriving Entity

represent Board as List Move by (·.moves) checked Board.replay
constraint Player.uniqueEmail : unique email
constraint Move.removeWithGame : cascade game
internal Game.delete
link Seat.game Seat.player
deriving instance Changes (except := [owner]) for Game
```

* `LeanDb.Model.Metadata` — `Domain`, `Entity`, `FieldType`, `StorageCodec`, `HasRecord`,
  field paths and lawful lenses (`EditableField`), `Change`, `UniqueKey`, `LinkKey`,
  `Constraint`, `Time`; the scalars and `Ref` of `LeanOntology` are exported.
* `LeanDb.Model.Represent` — `represent T as R by enc checked dec`.
* `LeanDb.Model.Resources` — `StorageResources`, `Has…Resource`, `portableStorage`.
* `LeanDb.Model.Request` — the storage-request IR (`StorageRequest`, `Program`, `Access`,
  `Row`, `OpScope`), `Interpreter`, `Program.run`, `MonadStorage`, `Program.lift`.
* `LeanDb.Model.DB` — `DB`, `Query`, `HasRow`, `Row T`, the generic storage steps.
* `LeanDb.Model.Deriving` — `deriving Domain`, `deriving Entity`.
* `LeanDb.Model.Entities` — the generated `T.insert/find/findBy/select/update/delete/patch`,
  `constraint` (unique, cascade), `internal`, `link`, `Changes`, `entity_operations`.
* `LeanDb.Model.Requirements` — `derive_requirements`, and the generalization machinery an
  operation layer reuses.
* `LeanDb.Model.Memory` — the in-memory backend.

`LeanDb.Native` runs the same programs on SQLite. -/
