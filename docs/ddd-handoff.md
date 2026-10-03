# Partiful native database handoff

Status: tested native foundations and optional original-type storage bridge;
DDD-LDB-01..04 remain partially complete. The full Partiful flows are not yet
lowered to SQLite. Root stays Lean 4.33.0; no dependency/toolchain downloads or
pin changes. All changes are uncommitted. Initial user edits in CHANGELOG.md,
docs/roadmap.md and docs/typed-interface.md remain verbatim.

Current dependent projection ABI COMPILES on installed Lean 4.33.0 with fresh
portable Resources/Flow/Declarations sources. The BYTE-FOR-BYTE authored
Partiful.Domain compiles, and partyPage.Requirements.infer + shared Flow.run pass
a populated native fixture. Query requirements also compile for an arbitrary
API-owned dependent auth slot, using API's resource-family composition pattern.
The earlier no-HasFieldProjection-candidates diagnostic is RESOLVED: the generated
provider carries its EditableField dictionary, which the result of the generic
HasProjectionResource instance retains. Do not copy an older provider signature.
No peer source is modified here. API owns the production native Flow algebra.

Exact compiled additions (`LeanDbDomain.Witness`, `.Resources`, `.Access`):

```lean
HasFieldProjection (S T : Type) (field : String) (V : outParam Type)
  [IsSchema S] (target : outParam (EntityStorage S T)) : Type 1
-- .editable : LeanApp.Domain.EditableField T field V
-- .column : @FieldStorage T V target.entity
-- .source_agrees : column.source = editable.lens.toFieldPath
ProjectionStorage (relation : MemberStorage S P T) (path : Ontology.FieldPath T V) : Type 1
-- .column : @FieldStorage T V relation.target.entity
-- .source_agrees : column.source = path
ProjectionStorage.project selection (parent : LeanApp.Domain.Ref P)
  : Except String (Read S (List V))
```

For native query assembly, use
`partyPage.Requirements.infer (resources := storageResources S)`.
`storageResources S` now defines `projection := fun relation path =>
ProjectionStorage relation path`. Its generic HasProjectionResource instance
requires `HasFieldProjection S T field V storage.target` for the ACTUAL carried member
storage. native_schema% generates this instance on the canonical original-type
EntityStorage from the existing HasFieldStorage, with a kernel-checked path
equality. The provider carries the generated EditableField dictionary and is
resolved before constructing HasProjectionResource; that portable result is
indexed by this exact dictionary. Both the actual native target and the portable
dictionary must unify, despite lookup treating them as outputs. Unrelated target
dictionaries do not gain evidence. `getter_agrees` additionally
proves the native getter equals the carried path getter; SQL still uses only the
column via existing MemberStorage.project. HasFieldStorage is unchanged.

DB's auth slot is `fun _ => ULift Empty`, with NO HasAuthResource instance: an
explicit unavailable capability, not an authentication implementation or witness.
API's existing `{ storageResources S with auth := fun storage => Auth.Storage S _
storage }` reuses entity/member/projection unchanged and supplies its own anchored
auth evidence. The generic projection-forwarding instance in NativeResources can
use DB HasProjectionResource directly. Member witness forwarding must apply the
explicit field argument:
`HasMemberStorage.storage (s := S) (Parent := P) (field := field) (Target := T)`;
bare `HasMemberStorage.storage` is a function. This exact composition is compiled
in Tests/PartifulProjection. Import LeanDbDomain.Schema (which reexports Resources)
and LeanDbDomain.Access, or import LeanDbDomain. No credential/session/KDF/HTTP
code belongs to DB.

The exact physical-to-semantic unique mapping is now generated/tested as
EntityStorage.sourceUnique, with genuine nativeKeyAgreement evidence; API create
and signup should consume that typed mapping rather than matching fields.

## Native member-set interface

`members% Party.guests : Person` generates `Party.Guests` and
`Party.guestsRelation : MemberRelation Party Person Party.Guests`:

- A real `party_guests` table with nominal parent/target references, parent
  ON DELETE CASCADE and target RESTRICT.
- `uq_party_guests_byPair(parent,target)` and `ix_party_guests_target(target)`.
- Kernel-proved `LawfulEntity` and actual `onlyPair`, `pairAll`, encoded-pair
  evidence. No new portable Ref/Members/Disclosure vocabulary.

`schema% S := Person, Party` includes the association. Member metadata persists
across imports. Schema inbound actions normalize actual stored
`Entity.fieldSpec.cascade`, including imported entities, rather than forgotten
command-local annotations. Missing relation targets reject assembly. Associations
participate in DbState, fingerprints and existing migration machinery, independently
of ordered child lists. Native-only Entity deriving retains T.Field.

Compiled native API:

```lean
Party.guestsRelation.bind (parent : Current σ Party)
  : MemberHandle σ Party Person Party.Guests
Txn.includeMember handle (target : Id Person)
  : Txn σ S Error (Except (ForeignKey Party.Guests) Unit)
MemberHandle.contains handle target : Txn σ S Error Bool
```

The private handle retains parent/type/scope. Include runs under the admitted
writer transaction; only the exact pair duplicate is a successful no-op. FK and
infrastructure errors remain. Current/Valid assembly is trusted native access;
the portable/API adapter must supply the authenticated person's identity.

`Read.memberContains` executes indexed EXISTS without hydration.
`Read.memberField relation parent field` selects only that target column through
the FK join, ordered by target ID. `memberContainsSql` / `memberFieldSql` expose
actual plans. Parent field patches preserve edges; parent deletion cascades only
its edges and retains people/other parties.

## Disclosure, preparation and constraints

`Read.discloseWith policy projection visible hidden` and
`MemberHandle.discloseField handle policy field visible hidden` authorize FIRST,
then project inside the same snapshot/transaction. Denial never executes the
projection. Callers supply the shared Disclosure constructors. Native raw reads,
contains and storage witnesses remain privileged assembly APIs; they are NOT a
protected public domain capability. No second policy IR/Flow/auth engine exists.

Prepared runners preserve old run callers and exact result shapes:

```lean
Read.runPrepared (prepare : Db Env) (build : Env → Read S A)
  : Db (Except DbFault A)
Txn.runPrepared (prepare : Db Env)
  (build : {σ : Type} → Env → Txn σ S Error A)
  : Db (Except DbFault (Except Error A))
```

Preparation runs inside readSnapshot / AFTER BEGIN IMMEDIATE succeeds, including
SQLite writer-lock admission. Clock/environment IO is trusted; KDF work stays
outside the writer. Live actor/resource/policy lookups belong in the same program.
`Entity.check T value : Except (InvalidFields T) (Checked T)` is the reusable checked
constructor: propagate validation/range failure instead of substituting trivial
for Checked.of evidence.

ConstraintMetadata, Unique.metadata, ForeignKey.metadata, MemberRelation.metadata
and InsertError.metadata expose stable identity/table/columns/source paths without
conflict holders, rows or credentials. Typed native payloads remain internal;
closed public failure mapping is portable/API-owned. canonicalizationPreflight
reports ALL invalid/colliding rows, never a survivor; Domain.emailPreflight uses
the single shared Email parser.

UpdateError.metadata?, SetError.metadata?, AppendError.metadata? and
DeleteError.metadata? retain actual typed constraint alternatives, including
selective touched keys and inbound restricting FKs. Gone/stale/invalid/notAppend
return none because they are separate failures, not discharged constraints.
ReferencedBy.metadata strips counts too. Actual duplicate-email patch and
restricted member-target deletion tests check these identities and full state.

HasUnique.identity has a compatible default for custom dictionaries; native
generation assigns each alternative its exact physical index name. Unique.metadata
uses that identity, retaining distinct names even for identical column sets.

## Optional original-type bridge and typed witnesses

Modules: `adapters/domain/LeanDbDomain/{Storage,Witness,Resources,Access,Schema}.lean`, aggregate
`LeanDbDomain.lean`; namespace LeanDb.Domain. Core retains no portable/browser
imports. `native_schema% S := Person, Party` consumes ORIGINAL portable records,
derives native Entity/field/FK/unique symbols, enum storage and member closure.
Portable `unique% Person.byEmail := email` becomes the native unique index without
repeating it. No app-owned PersonRow/PartyRow/conversion is needed. Direct unique
paths require a generated, kernel-checked `<unique>.nativeFieldAgreement` theorem
that the path getter equals the selected original field. A same-name/same-type
path with a swapped getter is rejected; unsupported paths reject explicitly.
Portable T.Field stays; native bridge symbols use T.DbField. Original Party has
FIVE stored fields, and
Members occupies no column and reconstructs only its empty declaration marker.

Storage codecs: Name/Title/Text/Email/Instant, with shared-parser decode AND checked
encode; genuine LawfulColCodec consumes parse_value/ofEpochSeconds_value. Text
scalar ordering has LawfulSqlOrd proofs. Instant is exact signed-64-bit INTEGER.
`refToId`/`idToRef` use Ref.parse, rejecting invalid/nonpositive/out-of-range,
noncanonical or non-default-scope identities. Checked ref writes reject another
scope. Password intentionally has no storage codec: native credentials stay API-owned.
Core adapter hooks are ReferenceValue and MemberDeclaration, not portable types.

Witness.lean exports (compiled, generated by native_schema%):

- `EntityStorage S T : Type 1`, with actual coherent Entity/Indexes/HasUnique/
  HasForeignKey/IsSchema.Has/HasPack/ReferencedBy dictionaries;
  `HasEntityStorage S T` selects it.
- `MemberStorage S Parent Target : Type 1`, retaining existential `Edge : Type`,
  coherent parent/target/edge dictionaries and the real MemberRelation;
  `HasMemberStorage S Parent "guests" Target` selects a declared field.

Exact constraint identity hook: `EntityStorage.sourceUnique : Unique T → String`
maps EACH typed native alternative to the shared Unique.identity, generated by
native_schema% (physical Unique.metadata.identity remains unchanged). New
`<unique>.nativeKeyAgreement` proves actual encoded-key equality to the portable
path/codec; nativeFieldAgreement separately proves getter equality. Mapping is
exhaustive over generated native alternatives, never a field-name search. Custom
native dictionaries retain a compatible native identity default. Duplicate semantic
declarations colliding on a native constructor reject instead of being ignored.

The storage fixture executes a generic witnessedContains through the shared
HasMemberResource without naming the Edge. Portable Request AND Projection carry
typed resources; the protected projection includes the column witness below. A runtime
TypeId cannot safely recover arbitrary dictionaries. There are no unsafe casts,
fake empty results or copied Flow.run semantics.

Compiled typed projection hook: `FieldStorage T Value` retains a
native field, actual `Entity.fieldTy field = Value`, original portable FieldPath,
and a kernel proof that its getter agrees. `HasFieldStorage S T "name" Name`
is generated by native_schema% for direct columns; `FieldStorage.project`
selects only that column and transports the result via the real equality proof.
No column witness is generated for Members. HasFieldProjection additionally
anchors the original EditableField dictionary to the exact target storage and
proves source path equality. ProjectionStorage carries the column/path evidence
through the shared portable ProjectionF.members constructor. An arbitrary
FieldPath identity/getter alone cannot recover the native Value dictionary or
prove that selecting a similarly named column implements that getter. Do not
work around this by hydrating whole target rows/emails before projecting names.

`LeanDbDomain.Resources` now instantiates the newly compiled shared family:
`storageResources S : LeanApp.Domain.ResourceFamily`, with EntityStorage,
MemberStorage and dependent ProjectionStorage witnesses. Generic HasEntityResource,
HasMemberResource and HasProjectionResource instances consume schema-generated
providers. MemberStorage includes actual
portable parent/target HasTypeId dictionaries for checked nominal ref conversion.
No alternate portable resource vocabulary or interpreter is defined. The auth slot
is unavailable until API supplies its typed native store.

Access.lean exports compiled, populated-runtime-tested assembly hooks:

```lean
EntityStorage.find storage reference
  : Except String (Read S (Option (LeanApp.Domain.Row Scope T)))
MemberStorage.contains storage parent person : Except String (Read S Bool)
MemberStorage.project storage coherentField parent : Except String (Read S (List Value))
ProjectionStorage.project selection parent : Except String (Read S (List Value))
MemberStorage.includeActor storage parent (actor : SignedIn Scope Target) missingParent
  : Except String (Txn Scope S Error (Except (ForeignKey storage.Edge) Unit))
```

The actual include type retains edge dictionaries explicitly. Reference checks
reject unsupported scopes; actual lookups/projection remain inside the runner.
includeActor obtains target ONLY from actor.id, re-reads the live parent in the
admitted writer, then binds the native transaction handle. It leaves typed FK
failures intact. Actor construction is the shared trusted API boundary, not a new
authentication engine. These are privileged native assembly hooks for the ONE
Flow algebra, not automatically published protected capabilities or a second IR.

## Proof and trust boundary

ExecutesAsMeaning now has read_agrees, txn_agrees and rollback propositions.
Read.observe / Txn.observe instrument the real executors with loaded
before/result/after states in one admitted snapshot/transaction. ObservedIO is a
successful transition of that actual IO action on opaque world tokens. Faults,
failed commit/rollback/lock admission are not successful observations. Equality
includes typed failure payloads and all tables/AUTOINCREMENT counters. No automatic
instance, new axiom or fabricated SQLite proof is supplied; SQLite/FFI remains
trusted. Txn.observed_postcondition needs explicit correspondence, initial WF and
an actual successful observation to carry a pure fact into runtime.

Audited kernel proofs (only propext/Classical.choice/Quot.sound):

- Txn.includeMember_idempotent: two includes equal one, exact result/state,
  including missing references and counter exhaustion.
- Txn.includeMember_existing and includeMember_wf, using actual lawful generated
  association codecs. Existing patch_get_other frames the entire member table.
- Read.memberField_provenance, discloseWith_hidden and discloseWith_denied_equal
  under the explicit equal-denial permission release.
- Txn.denote_go_error_restores / denote_error_restores / denote_abort_restores:
  structural rollback for EVERY constructor, including failures after writes.
  API should consume this DB-owned law once the current source is integrated.

No universal LawfulColCodec Ref or LawfulEntity Party is claimed: unrestricted
Ontology.EntityId still permits incompatible keys/scopes. Checked codecs are not
that universal theorem. General cascade/patch/program-WF proofs and lowered
host/date/source-order/API corollaries remain incomplete. The whole running stack
is not claimed formally verified.

## Actual validation

Use LEAN_NUM_THREADS=2; Lake 5 rejects -j. Direct Lean uses -j 2.

- `lake build leandb_tests leandb_ddd_tests`: PASS (160 jobs), extended axiom audit.
- `.lake/build/bin/leandb_tests`: PASS, all engine tests; 572 fixed-seed M15a
  cases and D1..D10 agreement, preserving typed writes/lists/migrations.
- `.lake/build/bin/leandb_ddd_tests`: PASS nonempty differential/runtime checks:
  exact answers/failure payloads and ALL tables/counters, WF before/after;
  reverse insertion/stable ordering, retries, same/distinct concurrent writers,
  typed missing parent/target, target restriction, parent patch/cascade and late
  abort; actual read/writer observations; full public/attendee/private matrix
  with no host exception, including stored private visibility with an actual
  host RSVP. A visibility writer commits between lookup/projection:
  the enclosing reader snapshot stays consistent and the next private snapshot
  hides names. Denial succeeds after physically dropping the relation, proving
  no protected query is prepared. EXPLAIN confirms the covering pair index.
  Duplicate-edge migration refuses atomically and retains every legacy row.
  A simulated dropped-include executor mutation is detected by final-state
  mismatch even when Unit answers agree.
- `python3 scripts/ddd_negative.py`: four intended compiler rejections (empty
  correspondence, wrong parent, private handle, scope escape), plus separately
  compiled imported association/schema closure/cascade differential execution.
- `python3 scripts/ddd_bridge.py <portable-repo>`: PASS against current portable
  sources: original records, nonempty names, generated typed witnesses, canonical
  unique collision, exactly one concurrent canonical profile, typed corruption
  attributed to original email, scalar/range/scope edges, preflight, missing
  byEmail exhaustiveness rejection after portable uniqueness evolution. Scalar
  and generated association/typed-field/key-agreement axiom audits pass. The fixture
  retains the real enum default and shared storageResources. WrongProjection
  rejects the actual Email-to-Name column equality; WrongUniqueGetter rejects
  a same-type path naming email but selecting backup. Both checks require their
  intended compiler diagnostics; a same-named True marker cannot bypass the
  getter proof check. The current full bridge command exits 0.
- `Tests/UniqueSources.lean` checks distinct physical AND semantic identities
  for two typed unique alternatives covering identical columns. It executes a
  nonempty canonical SQLite collision and compares the source result/state to
  denotation; all rows and the counter remain unchanged.
- `Tests/Access.lean` independently passes actual SQLite original-record lookup,
  missing lookup, scope refusal, authenticated include/retry, indexed contains,
  typed-column projection, live-parent refusal and all-table/counter preservation.
  Its include answer/final state and projection are also checked against denotation.
- `python3 scripts/ddd_bridge.py <portable-repo> --spec <spec-repo>` additionally
  compiles an unchanged copy of authored partiful/Domain.lean into DB-owned ignored
  output and executes Tests/PartifulProjection. Its test-only generic query algebra
  uses shared Flow.run: nonempty guest names ordered by target ID despite reversed
  includes, exact-set retry, public/attendees/private matrix (host has no attendee
  exception, private hides even an RSVP'd host), complete-state/counter/WF read
  checks, pure Read denotation, actual closed partyMissing, names-only execution
  despite invalid stored emails, and denial after the guest table is dropped.
  Deliberate corruption/drop phases are excluded from WF claims. Composition with
  an arbitrary API auth slot compiles without providing any auth witness.
- Tests/ProjectionEvolution adds an original nickname:Name column and a generated
  query; Requirements.infer and its populated native projection pass with no new
  manual column witness. MissingProjection rejects an unmapped lawful alias;
  WrongProjectionTarget rejects both a canonical column in an arbitrary target
  dictionary and synthesis of a resource for that dictionary; WrongProjectionGetter
  rejects a same-type/same-identity swapped getter. WrongProjectionLens has genuine
  lens laws but rejects replacement of the actual portable field dictionary.
  ProjectionStorage.getter_agrees is audited with only propext.
  The generated HasFieldProjection name witness is also audited: only
  propext/Classical.choice/Quot.sound. New rejection checks require exact error
  counts, so a broken lens-law fixture cannot masquerade as missing native evidence.

Focused follow-up receipt (final source, installed 4.33.0, bounded threads):

- `LEAN_NUM_THREADS=2 python3 scripts/ddd_bridge.py /Users/harshwork/code/LeanReact
  --spec /Users/harshwork/code/domain_driven_development`: exit 0, full optional
  source rebuild, five populated runtime fixtures, seven intended compiler
  rejections, scalar/association/field/key/getter audits. Log:
  `/tmp/leandb-projection-bridge-final.log`.
- The final minimal Schema/Access imports compile and run PartifulProjection:
  exit 0, `/tmp/leandb-projection-partiful-final.log`.
- `.lake/build/bin/leandb_tests`: exit 0, all engine tests including 572 M15a
  cases and D1..D10; `/tmp/leandb-projection-engine.log`.
- `.lake/build/bin/leandb_ddd_tests`: exit 0,
  `/tmp/leandb-projection-native-ddd.log`.
- `python3 scripts/ddd_negative.py`: exit 0, four native compiler rejections and
  imported relation/schema/cascade execution;
  `/tmp/leandb-projection-native-negative.log`.
- `git diff --check`: clean. The original baseline diff for each of CHANGELOG.md,
  docs/roadmap.md and docs/typed-interface.md was compared verbatim and is unchanged.

This follow-up changes only Witness/Resources/Schema/Access in the optional bridge,
the bridge runner, six focused fixtures and this handoff. Native SQL/index names,
EntityStorage.sourceUnique, existing getter/key laws and core execution/Ref contracts
are preserved. A fresh portable-source rebuild temporarily encountered a peer
Declarations edit error; the repaired current source rebuilt and all gates above
passed. It is not a remaining blocker.

Concurrency fixtures open/verify both connections BEFORE racing their admitted
transactions. Concurrent withDb schema/bootstrap setup produced an existing
SQLite busy error in an earlier fixture; startup concurrency is not claimed here.
No error retry/catch hides a failure in the tested business transactions.

Native Members/Rollback/Constraint source closure also compiled with installed
nightly-2026-09-26 into isolated output BEFORE the cross-module persistence fix.
This is limited source/law compatibility, not linked runtime/LeanJS qualification.
Common candidate remains 4.33.0; API owns unified linked audit and its own pins.
Validation paths are CLI inputs/ignored artifacts, never release dependencies.
No peer source/artifacts were modified and no second dependency checkout was made.

## Remaining work and exact next step

1. The generated dependent projection evidence and actual Partiful query resource
   requirements are now compiled and populated-runtime-tested. API should finish
   its native Algebra.project case by invoking the carried selection.project
   relation.parent and recursively mapping ProjectionF.map, then use the shared
   Flow.run policy-first branch. Continue its own auth/app/closed-command lowering.
   No per-Partiful native dispatch/service body or string casts are needed.
2. Lower the portable policy to exact SQL and enforce protected field/count/export
   capabilities. These native primitives/tests are foundations, not completion of
  DDD-LDB-03; native raw assembly reads stay privileged, not protected/public APIs.
3. Reconcile remaining FK/unique/changed-field failures and closed public errors;
   resolve the checked-reference carrier law; finish applicable WF/cascade/flow
   theorems; integrate original six business flows plus native auth.
4. API/coordinator already demonstrated the linked current-DB/current-Domain/API
   4.33 regression (580/0) and stable LeanJS corpus (13/0). Complete qualification
   of the actual witnessed Partiful/auth publication path and pinned optional
   package/fresh-clone assembly. Development validation is not a completed
   optional release package.

Changed files (excluding the three preserved original user edits):

- `LeanDb.lean`, `LeanDb/Core.lean`, `LeanDb/Entity.lean`, `LeanDb/Derive.lean`;
  `LeanDb/Typed/{Schema,Read,Txn,Members,Constraint,Rollback}.lean`.
- `TestsDdd.lean`, `lakefile.toml`, `scripts/CheckAxioms.lean`;
  `scripts/{ddd_compile_portable,ddd_bridge,ddd_negative}.py`.
- `adapters/domain/LeanDbDomain.lean`;
  `adapters/domain/LeanDbDomain/{Storage,Witness,Resources,Access,Schema}.lean`;
  `adapters/domain/Tests/{Storage,Access,UniqueSources,UniqueEvolution,WrongProjection,WrongUniqueGetter}.lean`;
  `adapters/domain/Tests/{PartifulProjection,ProjectionEvolution,MissingProjection,WrongProjectionTarget,WrongProjectionGetter,WrongProjectionLens}.lean`.
- `fixtures/ddd/{Generation,EmptyCorrespondence,WrongParent,ForgedHandle,EscapedHandle}.lean`;
  `fixtures/ddd/Imported/{Declaration,Schema}.lean`.
- `docs/ddd-handoff.md`, the only added prose document.

Initial dirty documentation remains untouched. Generated Python bytecode was
moved intact to ignored `.lake/ddd-python-cache`; no untracked/ignored files were
deleted. No commits/pushes or releases were made.
