# Terminology

Use these terms for LeanDB's public API and documentation.
For a worked example, see [Core concepts](core_concepts_and_terminology.md).

## Data

| Term | Meaning |
|---|---|
| Domain type | A Lean type for an application value, such as a title or order. |
| Entity | A type with an `Entity` instance. It defines a table's fields and row encoding. |
| Schema | The list of table and column specifications derived from a base's entities. |
| Codec | A `ColCodec` instance. It converts a Lean value to a SQL column and decodes it back. |
| Stored row | `Stored α`: an entity value plus its assigned `Id α`. |
| ID | `Id α`: a row identifier tied to one entity type. |
| Reference | `Ref α`: an alias for `Id α`, used for foreign keys. |
| Closed enum | A fixed set of named choices with a `ClosedEnum` instance. It is stored as checked text. |
| Nullable field | An `Option α` field. `none` is stored as SQL `NULL`. |
| Inline value | A record with an `Inline` instance. Its fields become prefixed columns in the parent table. |
| Child list | A `List` of inline records stored in a separate child table. Rows carry a parent reference and a position. |
| JSON column | A structured value stored in one text column through `ColCodec.json`. Its declared shape is schema metadata. |
| `DbJson.via` | A codec for a validated nested type: it stores the data representation and re-decides the proofs on read. The schema sees the data representation's shape. |
| Derived column | A field declared with `:= derived expression`. It is recomputed on write and checked on read. |

## Packages and execution

| Term | Meaning |
|---|---|
| Engine | The LeanDB library and runtime. |
| Base | A Lean package with domain types, tables, queries, and a `LeanDb.Base` value. |
| Instance | One SQLite file used by a base. Its path is chosen at runtime. |
| Server | A process exposing a base over JSON lines, HTTP, or MCP. |
| Host | A process that serves several base processes under one HTTP port. |
| Database action | A `DbM α` computation that returns an `α` or a `DbError`. |
| Registered query | A query added to `Base.queries` through `query%`. It is callable through the CLI and server interfaces. |
| Typed client | A client whose query arguments and result types come from the base's Lean definitions. |

## Query planning

| Term | Meaning |
|---|---|
| Predicate | A condition used to filter rows. `select` accepts a Lean function returning `Bool`. |
| Field symbol | A generated Lean value naming an entity field, such as `Note.Field.title`. |
| Plan | A `Pred ts` value describing a condition over the selected entity types `ts`. |
| Reification | Turning a Lean expression into a query plan during elaboration. |
| Pushdown | Executing supported parts of a query in SQL to reduce the rows fetched. |
| Residual | A condition that stays in Lean because the planner cannot translate it. |
| Reference semantics | The Lean implementation that fetches, filters, and sorts rows. It defines the intended query result. |
| Footprint | The tables and columns a query plan reads, plus whether it contains a residual. |
| Impact report | The part of `migrate status` that relates changed columns to query footprints and logged runs. |

## Schema history

| Term | Meaning |
|---|---|
| Fingerprint | A value computed from schema metadata. It detects disagreement between a base and an instance. |
| Schema version | An instance's migration position. It is not the LeanDB package version. |
| Snapshot | A saved schema description, with generated Lean row types for that version. |
| Unfrozen base | A base without a migration chain. Changes are planned from the instance's schema and the current code. |
| Frozen base | A base with a `Chain` of schema snapshots and migrations. |
| Migration | A change from one schema version to the next, including any required data conversion. |
| Typed transform | A function `Old → Except String New`, used with `Step.transformT` to convert stored rows. |
| Adoption | Opening an existing SQLite file as a base instance and recording its matching schema. |
| Migration rollback | Restoring the backup made before a migration. This also restores the data from that time. |

Source definitions: [Core](../LeanDb/Core.lean), [Entity](../LeanDb/Entity.lean),
[Base](../LeanDb/Base.lean), [Pred](../LeanDb/Pred.lean), and
[Migration](../LeanDb/Migration.lean).
