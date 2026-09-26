# Roadmap

LeanDB aims to preserve domain rules across the application and database.
This page separates the current implementation from future work.
The future items are directions, not release dates or API commitments.

## Available in 0.3.1

- Entity-derived schemas, typed IDs and references, and validating codecs.
- Closed enums, enum sets, JSON columns, inline records, and child lists.
- Typed `select`, `insert`, `update`, and `delete` operations over SQLite.
- SQL pushdown for supported predicates, joins, and related-row quantifiers.
- Query plans, logs, and schema-change impact reports.
- Schema diffs, frozen migration chains, and typed row transformations.
- Migration transactions, backups, history, and rollback.
- Standalone base generation and SQLite import reports.
- CLI, JSON-lines, HTTP, and MCP interfaces.
- Typed clients over stdio and the separate HTTP adapter.

See [Core concepts](core_concepts_and_terminology.md) for how these fit together.
The [changelog](../CHANGELOG.md) records released changes.

## Next areas to develop

### More expressive domain models

Support automatic storage for fields whose types depend on earlier values.
An example is a cup size whose allowed choices depend on the drink's temperature.
Automatic entity derivation currently rejects these dependent fields.

Broaden nested data support. Current inline records cannot contain another
inline record or a child list. Optional inline records and derived child
lists also need a defined storage model.

### Queries that do more work in SQL

Add SQL projections for individual fields. `select` currently fetches
complete entity rows; applications can map the results in Lean.
Extend pushdown to column arithmetic and aggregates.
Arithmetic and aggregate calculations currently run in Lean.

### Stronger preservation proofs

Connect the original Lean predicate, generated plan, SQL rendering, and
codec behavior with explicit correctness guarantees.

The existing `Pred.approx_sound` theorem relates a plan's Lean meaning to
its SQL-translatable approximation. It is not an end-to-end proof of the
query compiler or SQLite executor. The original predicate still runs on
decoded rows, and tests compare planned and unplanned execution.

### Configurable products

Turn the Eats configurable-offer experiment into reusable support.
Keep pricing rules, summary fields, and tabulated prices in sync when data
changes. The current experiment maintains some of these relationships by hand.
Its [design notes](../examples/eats/DESIGN.md) describe the gaps and tests.

### Safer imports and migration previews

Broaden SQLite import support. The importer currently reports unsupported
features such as views, triggers, and composite keys instead of translating them.
Source constraints and indexes listed in the import report may be lost when
LeanDB later rebuilds a table.

Use logged plans to test queries against a candidate schema before migration.
The current impact report identifies affected queries; it does not replay them.

## Later possibilities

- Other SQL backends and queries across database instances.
- Typed names for selected rows from a database vocabulary.
- Shared Lean domain types across frontend and backend applications.

Start with a small example and a clear expected result when proposing work.
Keep the current SQLite behavior covered by the [release checks](../RELEASING.md).
