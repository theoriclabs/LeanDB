import LeanDb.Model.Resources

/-! # The storage-request IR

Every storage step a model program takes is one `StorageRequest`: `find`, `findBy`,
`select` and `linkField` read; `insert`, `update` (whole-record `T.update` and selective
`T.patch` both lower to it, with a `Change`) and `delete` write. A request is indexed by

* the resource family (`StorageResources`): the typed evidence it carries;
* the transaction `Scope`: an uninhabited, rank-2 index rows are tied to;
* its `Access`: reads are polymorphic in it, writes exist only at `.command`. A `.query`
  program cannot contain a write: that is a type error, not a runtime check;
* its answer type.

Declared unique conflicts are VALUES of the entity's own conflict type (`Except C _`); a
foreign-key, restrict or decode failure is the backend's fault, outside the model.

`Program` is the free monad over these requests. `DB` and `Query` (`LeanDb.Model.DB`) are
`Program` at the portable family. A backend runs a program with an `Interpreter`; the
in-memory backend (`LeanDb.Model.Memory`) and SQLite (`LeanDb.Native`) interpret the same
requests. A larger monad (an operation IR) embeds programs with `Program.run`, or with
`Program.lift` given a `MonadStorage` instance. -/

namespace LeanDb.Model
open Ontology

/-- What a program may do: `query` reads one snapshot, `command` reads and writes. -/
inductive Access where
  | query
  | command
  deriving Repr, BEq, DecidableEq

/-- Transaction index of model programs. Uninhabited and never inspected: a backend
replaces it by its own rank-2 `Scope`, so rows cannot depend on it. -/
inductive OpScope : Type

/-- A stored row: its identity and its value, read in transaction `Scope`. Interpreter-local
data: no `Wire` instance, no public constructor. -/
structure Row (Scope T : Type) where
  private mk ::
  id : Ref T
  value : T

instance {Scope T : Type} : CoeOut (Row Scope T) T := ⟨@Row.value Scope T⟩

/- Explicitly trusted assembly boundary: interpreters build rows only after a live lookup in
the current snapshot or transaction. -/
namespace Trusted
def row (id : Ref T) (value : T) : Row Scope T := ⟨id, value⟩
end Trusted

/-- One storage step. See the module documentation. -/
inductive StorageRequest (resources : StorageResources) (Scope : Type) : Access → Type → Type 1 where
  /-- The row with this identity, if it exists. -/
  | find {T : Type} [Entity T] (storage : resources.entity T) (id : Ref T) :
      StorageRequest resources Scope access (Option (Row Scope T))
  /-- The row whose declared unique key is `key`, if it exists. -/
  | findBy {T K : Type} [Entity T] (storage : resources.entity T) (unique : UniqueKey T K)
      (lookup : resources.unique storage unique) (key : K) :
      StorageRequest resources Scope access (Option (Row Scope T))
  /-- Every row, by identity. -/
  | select {T : Type} [Entity T] (storage : resources.entity T) :
      StorageRequest resources Scope access (List (Row Scope T))
  /-- A join projection: field `field` of every target `T` linked to `parent` through edge
  `E`, each target once, ordered by target identity. -/
  | linkField {E P T V : Type} [Entity E] [Entity T] (edges : resources.entity E) (key : LinkKey E P T)
      (link : resources.link edges key) (targets : resources.entity T) (field : FieldPath T V)
      (column : resources.column targets field) (parent : Ref P) :
      StorageRequest resources Scope access (List V)
  /-- Insert a row. A clash with one of `conflicts` is `.error` of its `publicFailure`, and
  writes nothing. -/
  | insert {T C : Type} [Entity T] (storage : resources.entity T) (value : T)
      (conflicts : List (Constraint C)) : StorageRequest resources Scope .command (Except C (Ref T))
  /-- Apply `patch` to the live row. Only constraints over fields whose value changes are
  checked (touched-field rule); a clash is `.error` and writes nothing. -/
  | update {T C : Type} [Entity T] (storage : resources.entity T) (row : Row Scope T) (patch : Change T)
      (conflicts : List (Constraint C)) : StorageRequest resources Scope .command (Except C Unit)
  /-- Delete the row. A row still referenced (and not cascaded) is the backend's fault. -/
  | delete {T : Type} [Entity T] (storage : resources.entity T) (row : Row Scope T) :
      StorageRequest resources Scope .command Unit

/-- Read requests run unchanged inside a writer. -/
def StorageRequest.toCommand {resources : StorageResources} {Scope A : Type} :
    StorageRequest resources Scope .query A → StorageRequest resources Scope .command A
  | @StorageRequest.find _ _ _ T inst storage id => @StorageRequest.find _ _ _ T inst storage id
  | @StorageRequest.findBy _ _ _ T K inst storage unique lookup key =>
      @StorageRequest.findBy _ _ _ T K inst storage unique lookup key
  | @StorageRequest.select _ _ _ T inst storage => @StorageRequest.select _ _ _ T inst storage
  | @StorageRequest.linkField _ _ _ E P T V instE instT edges key link targets field column parent =>
      @StorageRequest.linkField _ _ _ E P T V instE instT edges key link targets field column parent

/-- A model program: the free monad over `StorageRequest`. -/
inductive Program (resources : StorageResources) (access : Access) (Scope : Type) : Type → Type 1 where
  | pure {A : Type} (value : A) : Program resources access Scope A
  | bind {A B : Type} (value : Program resources access Scope A) (next : A → Program resources access Scope B) :
      Program resources access Scope B
  | request {A : Type} (value : StorageRequest resources Scope access A) : Program resources access Scope A

instance {resources : StorageResources} {access : Access} {Scope : Type} : Monad (Program resources access Scope) where
  pure := Program.pure
  bind := Program.bind

/-- A read program runs unchanged inside a writer. -/
def Program.toCommand {resources : StorageResources} {Scope : Type} :
    {A : Type} → Program resources .query Scope A → Program resources .command Scope A
  | _, .pure value => .pure value
  | _, .bind value next => .bind (Program.toCommand value) (fun result => Program.toCommand (next result))
  | _, .request req => .request req.toCommand

/-- A backend: how each storage request runs in monad `m`. LeanDB implements it in memory
(`LeanDb.Model.Memory.interpreter`) and on SQLite (`LeanDb.Native.commandInterpreter`,
`LeanDb.Native.queryInterpreter`). Framework failures belong to `m`. -/
structure Interpreter (m : Type → Type u) (resources : StorageResources) (access : Access) (Scope : Type) where
  request : {A : Type} → StorageRequest resources Scope access A → m A

/-- A command interpreter also answers read requests. -/
def Interpreter.toQuery {m : Type → Type u} {resources : StorageResources} {Scope : Type}
    (interpreter : Interpreter m resources .command Scope) : Interpreter m resources .query Scope :=
  ⟨fun req => interpreter.request req.toCommand⟩

/-- Run a program with an interpreter. The one semantics of a model program. -/
def Program.run {m : Type → Type u} [Monad m] {resources : StorageResources} {access : Access} {Scope : Type}
    (interpreter : Interpreter m resources access Scope) : {A : Type} → Program resources access Scope A → m A
  | _, .pure value => Pure.pure value
  | _, .bind value next => do Program.run interpreter (next (← Program.run interpreter value))
  | _, .request req => interpreter.request req

/-- A monad that can perform the storage requests of family `resources` at `access`: how an
operation IR embeds model programs (`instance : MonadStorage … (Op ε)` gives
`MonadLift DB (Op ε)`). -/
class MonadStorage (resources : StorageResources) (access : Access) (Scope : Type) (m : Type → Type u) where
  storage : {A : Type} → StorageRequest resources Scope access A → m A

/-- Embed a program into a `MonadStorage` monad, request by request. -/
def Program.lift {m : Type → Type u} [Monad m] {resources : StorageResources} {access : Access} {Scope : Type}
    [MonadStorage resources access Scope m] {A : Type} (program : Program resources access Scope A) : m A :=
  program.run ⟨MonadStorage.storage⟩

end LeanDb.Model
