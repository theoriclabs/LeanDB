import LeanDb.Native.Operations
import LeanDb.Native.Resources

/-! # The SQLite backend for model programs

Implements the model's `Interpreter` on LeanDB's typed IR: a command program runs in one
writer transaction (`Txn`), a query program in one read snapshot (`Read`). Each request is
lowered to its hook (`LeanDb.Native.Operations`) on the exact storage the request carries;
`Txn.denote`/`Read.denote` give the pure meaning of the same program.

The program must be at the native family: generalize a `DB`/`Query` definition with
`derive_requirements f` and run `f.withResources f.Requirements.infer args`. -/

namespace LeanDb.Native
open LeanDb
open LeanDb.Model (StorageRequest Program Interpreter)

/-- One storage request in a writer transaction. A `StorageFault` aborts through `fault`,
which rolls back the whole transaction. -/
def commandRequest {s : Type} [IsSchema s] {σ ε : Type} (fault : StorageFault → ε) :
    {A : Type} → StorageRequest (storageResources s) σ .command A → Txn σ s ε A
  | _, @StorageRequest.find _ _ _ _ inst storage reference =>
      letI := inst
      match storage.find reference with
      | .error why => Txn.throw (fault (.invalidReference why))
      | .ok read => Txn.ofRead read
  | _, @StorageRequest.findBy _ _ _ _ _ inst storage _ lookup key => do
      letI := inst
      match ← Txn.ofRead (storage.findBy lookup key) with
      | .ok row => pure row
      | .error why => Txn.throw (fault why)
  | _, @StorageRequest.select _ _ _ _ inst storage => do
      letI := inst
      match ← Txn.ofRead storage.select with
      | .ok rows => pure rows
      | .error why => Txn.throw (fault why)
  | _, @StorageRequest.linkField _ _ _ _ _ _ _ _ _ _ _ link targets _ column parent =>
      match link.project targets column parent with
      | .error why => Txn.throw (fault (.invalidReference why))
      | .ok read => Txn.ofRead read
  | _, @StorageRequest.insert _ _ _ _ inst storage value conflicts =>
      letI := inst
      storage.insert value conflicts fault
  | _, @StorageRequest.update _ _ _ _ inst storage row patch conflicts =>
      letI := inst
      storage.update row patch conflicts fault
  | _, @StorageRequest.delete _ _ _ inst storage row =>
      letI := inst
      storage.delete row fault

/-- One read request in a snapshot. -/
def queryRequest {s : Type} [IsSchema s] {Scope : Type} :
    {A : Type} → StorageRequest (storageResources s) Scope .query A → ExceptT StorageFault (Read s) A
  | _, @StorageRequest.find _ _ _ _ inst storage reference =>
      letI := inst
      match storage.find reference with
      | .error why => throw (.invalidReference why)
      | .ok read => liftM read
  | _, @StorageRequest.findBy _ _ _ _ _ inst storage _ lookup key =>
      letI := inst
      ExceptT.mk (storage.findBy lookup key)
  | _, @StorageRequest.select _ _ _ _ inst storage =>
      letI := inst
      ExceptT.mk storage.select
  | _, @StorageRequest.linkField _ _ _ _ _ _ _ _ _ _ _ link targets _ column parent =>
      match link.project targets column parent with
      | .error why => throw (.invalidReference why)
      | .ok read => liftM read

/-- The writer backend. -/
def commandInterpreter {s : Type} [IsSchema s] {σ ε : Type} (fault : StorageFault → ε) :
    Interpreter (Txn σ s ε) (storageResources s) .command σ :=
  ⟨commandRequest fault⟩

/-- The snapshot backend. -/
def queryInterpreter {s : Type} [IsSchema s] {Scope : Type} :
    Interpreter (ExceptT StorageFault (Read s)) (storageResources s) .query Scope :=
  ⟨queryRequest⟩

/-- A command program as one transaction. -/
def Program.toTxn {s : Type} [IsSchema s] {σ A : Type}
    (program : Program (storageResources s) .command σ A) : Txn σ s StorageFault A :=
  program.run (commandInterpreter id)

/-- A query program as one snapshot read. -/
def Program.toRead {s : Type} [IsSchema s] {Scope A : Type}
    (program : Program (storageResources s) .query Scope A) : Read s (Except StorageFault A) :=
  (program.run queryInterpreter).run

/-- Run a command program in one writer transaction. A `StorageFault` rolls it back. -/
def runCommand {s : Type} [IsSchema s] {A : Type}
    (program : {σ : Type} → Program (storageResources s) .command σ A) :
    Db (Except DbFault (Except StorageFault A)) :=
  Txn.run fun {σ} => Program.toTxn (program (σ := σ))

/-- Run a query program in one read snapshot. -/
def runQuery {s : Type} [IsSchema s] {A : Type}
    (program : Program (storageResources s) .query Unit A) : Db (Except DbFault (Except StorageFault A)) :=
  Read.run (Program.toRead program)

end LeanDb.Native
