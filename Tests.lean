import LeanDb
import Std.Http.Test.Helpers
import TestsLdb01
import TestsLdb15
import TestsLdb16
import TestsLdb17
import TestsLdb18
import TestsLdb19
import TestsLdb20
import TestsLdb21
import TestsLdb22
import TestsLdb23
import TestsLdb24
import TestsM14a
import TestsM14b
import TestsM14c
import TestsM15a
import CheckAxioms

/-! Engine tests: codecs, deriving, the dependent select against a real
SQLite file, CAS staleness, FK restriction. Fixture types live here — the
engine library itself imports no domain. -/

open LeanDb

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

/-! ## Fixtures -/

structure Author where
  name : String
  age : Nat
  deriving Repr, LeanDb.Entity

structure Book where
  title : String
  author : Ref Author
  rating : Option Float
  deriving Repr, LeanDb.Entity

structure Marker where
  deriving Repr, LeanDb.Entity

/-- A column name with an embedded quote — legal as a Lean field under
    guillemets, legal SQL inside a quoted identifier, and the one name
    where the DDL's quoting and the plan renderer's quoting could disagree. -/
structure Quoted where
  «a"b» : Int64
deriving Repr, LeanDb.Entity

def schema : List TableSpec := [Entity.spec Author, Entity.spec Book]

/-! ## Pure tests -/

private def roundtrip [ColCodec α] [BEq α] (a : α) : Bool :=
  match fromCol (toCol a) with
  | .ok b => a == b
  | .error _ => false

private def testCodecs : IO Unit := do
  check (roundtrip (42 : Int64)) "Int64 roundtrip"
  check (roundtrip (7 : Nat)) "Nat roundtrip"
  check (roundtrip true && roundtrip false) "Bool roundtrip"
  check (roundtrip "quote \" and unicode λ") "String roundtrip"
  check (roundtrip (some (3 : Nat)) && roundtrip (none : Option Nat)) "Option roundtrip"
  check ((fromCol (α := Nat) (.int (-1))).isOk == false) "negative Nat must fail decode"
  check ((fromCol (α := Bool) (.int 2)).isOk == false) "Bool 2 must fail decode"
  check ((fromCol (α := String) (.int 5)).isOk == false) "String from INTEGER must fail"
  check ((fromCol (α := UInt16) (.int 65535)).toOption == some 65535)
    "UInt16 maximum must decode"
  check ((fromCol (α := UInt16) (.int 65536)).isOk == false)
    "UInt16 size must not wrap to zero"
  check ((fromCol (α := UInt32) (.int 4294967295)).toOption == some 4294967295)
    "UInt32 maximum must decode"
  check ((fromCol (α := UInt32) (.int 4294967296)).isOk == false)
    "UInt32 size must not wrap to zero"
  -- JSON true/false is a Bool, not a silent 0/1 for every INTEGER (#37)
  let age := columnSpec "age" Nat
  check ((Col.fromJson age (Lean.Json.bool false)).isOk == false)
    "JSON false is refused on a Nat INTEGER column"
  check ((Col.fromJson age (Lean.Json.bool true)).isOk == false)
    "JSON true is refused on a Nat INTEGER column"
  let on := columnSpec "on" Bool
  check (on.boolCodec) "the Bool column is marked as a bool codec"
  check ((Col.fromJson on (Lean.Json.bool true)).toOption == some (.int 1))
    "JSON true is accepted on a Bool column"
  check ((Col.fromJson on (Lean.Json.bool false)).toOption == some (.int 0))
    "JSON false is accepted on a Bool column"

private def testDerivedSpec : IO Unit := do
  check (Entity.tableName Author == "author") "table name snake_case"
  let cols := Entity.columns Book
  check (cols.map (·.name) == #["title", "author", "rating"]) "Book column names"
  check ((cols.getD 1 default).fkTable == some "author") "Ref column carries FK target"
  check ((cols.getD 2 default).nullable == true) "Option column is nullable"
  check ((cols.getD 0 default).nullable == false) "plain column is NOT NULL"
  let a : Author := ⟨"Ada", 36⟩
  let rt : Except DbError Author := Entity.decode (Entity.encode a)
  check (rt.toOption.map (·.name) == some "Ada") "entity encode/decode roundtrip"
  check (((Entity.decode #[.int 1] : Except DbError Author)).isOk == false)
    "wrong column count must fail decode"
  let missingFk := validateSchema [Entity.spec Book]
  check (missingFk.isOk == false) "schema rejects a reference to an omitted table"
  let duplicate := validateSchema [Entity.spec Author, Entity.spec Author]
  check (duplicate.isOk == false) "schema rejects duplicate table names"
  let sameName : TableSpec :=
    ⟨"author", #[{ name := "other", sqlType := .text, nullable := false, fkTable := none }], #[], none⟩
  match collidingTable? [Entity.spec Author, sameName] with
  | some (a, b) =>
      check (a.toLower == "author" && b.toLower == "author")
        "unequal specs that share a name collide"
  | none => throw <| IO.userError "FAIL: colliding author specs must be reported"
  check ((collidingTable? [Entity.spec Author, Entity.spec Author]).isNone)
    "the same spec listed twice is not an unequal collision"
  let upper : TableSpec := { sameName with name := "Author" }
  check ((collidingTable? [Entity.spec Author, upper]).isSome)
    "case-folded table names collide"
  let reserved : TableSpec := ⟨"_leandb_user", #[], #[], none⟩
  check ((validateSchema [reserved]).isOk == false) "schema rejects the internal table prefix"
  -- LEP-0002 stage 1: field symbols
  check (Entity.fields (α := Author) == #[.name, .age]) "one symbol per field, in order"
  check ((Entity.fields (α := Book)).map Entity.fieldName == #["title", "author", "rating"])
    "fieldName follows declaration order"
  check ((Entity.fields (α := Book)).all fun f => Entity.fieldOfName? Book (Entity.fieldName f) == some f)
    "fieldName round-trips through fieldOfName?"
  check ((Entity.fieldOfName? Author "nope").isNone) "unknown column has no symbol"
  check ((Entity.fields (α := Marker)).isEmpty) "zero-field entity has no symbols"
  check (Entity.get (α := Author) Author.Field.age a == 36) "get reads a field through its symbol"
  -- `columns` is now computed from `fieldSpec`; the DDL it yields is what
  -- the stored `columns` array produced before (goldens captured then)
  check ((Entity.spec Author).ddl ==
      "CREATE TABLE IF NOT EXISTS \"author\" (id INTEGER PRIMARY KEY AUTOINCREMENT, \"name\" TEXT NOT NULL, \"age\" INTEGER NOT NULL)")
    s!"author DDL golden, got {(Entity.spec Author).ddl}"
  check ((Entity.spec Book).ddl ==
      "CREATE TABLE IF NOT EXISTS \"book\" (id INTEGER PRIMARY KEY AUTOINCREMENT, \"title\" TEXT NOT NULL, \"author\" INTEGER NOT NULL REFERENCES \"author\"(id) ON DELETE RESTRICT ON UPDATE RESTRICT, \"rating\" REAL)")
    s!"book DDL golden, got {(Entity.spec Book).ddl}"
  check ((Entity.spec Marker).ddl ==
      "CREATE TABLE IF NOT EXISTS \"marker\" (id INTEGER PRIMARY KEY AUTOINCREMENT)")
    s!"marker DDL golden, got {(Entity.spec Marker).ddl}"

-- `get` through the symbol is typed by the field's declared type
example : (Entity.get (α := Author) Author.Field.age ⟨"Ada", 36⟩ : Nat) = 36 := rfl

private def testSortBy : IO Unit := do
  let xs := #[(3, "c"), (1, "b"), (1, "a"), (2, "z")]
  let byFst : SortBy (Nat × String) := .key (·.1)
  let both : SortBy (Nat × String) := .andThen (.key (·.1)) (.desc (.key (·.2)))
  check ((xs.qsort (fun a b => (byFst.ord a b).isLT)).map (·.1) == #[1, 1, 2, 3]) "key sort"
  check ((xs.qsort (fun a b => (both.ord a b).isLT)) == #[(1, "b"), (1, "a"), (2, "z"), (3, "c")])
    "andThen + desc sort"

/-! ## Closed worlds -/

inductive Status where
  | backlog | inProgress | done
  deriving Repr, DecidableEq, Ord, LeanDb.ClosedEnum

structure Todo where
  title : String
  status : Status
  deriving Repr, LeanDb.Entity

private def Status.rank : Status → Nat
  | .backlog => 0 | .inProgress => 1 | .done => 2

private instance : LT Status := ⟨fun a b => a.rank < b.rank⟩
private instance (a b : Status) : Decidable (a < b) := by
  change Decidable (a.rank < b.rank)
  infer_instance

private instance (a b : Option Nat) : Decidable (a < b) := by
  change Decidable (Option.lt (fun x y : Nat => x < y) a b)
  cases a <;> cases b <;> simp [Option.lt] <;> infer_instance

structure MaybeRank where
  score : Option Nat
  deriving Repr, LeanDb.Entity

-- Closed types are not entities: there is nothing to insert into or
-- delete from — this must not typecheck.
#check_failure insert Status Status.backlog

/-- Regression: structure field defaults must compile in the derived
    instance and be honored when JSON omits the field. -/
structure Draft where
  title : String
  status : Status := .backlog
  score : Nat := 10
  note : Option Nat := some 5
  deriving Repr, LeanDb.Entity

private def testDefaults : IO Unit := do
  let cols := Entity.columns Draft
  check (cols.map (·.dflt) == #[none, some (.text "backlog"), some (.int 10), some (.int 5)])
    s!"defaults reified into the column specs, got {repr (cols.map (·.dflt))}"
  let ddl := (Entity.spec Draft).ddl
  check (((ddl.splitOn "DEFAULT 'backlog'").length == 2) && ((ddl.splitOn "DEFAULT 10").length == 2))
    s!"DDL carries DEFAULT clauses, got {ddl}"
  check (ddl ==
      "CREATE TABLE IF NOT EXISTS \"draft\" (id INTEGER PRIMARY KEY AUTOINCREMENT, \"title\" TEXT NOT NULL, \"status\" TEXT NOT NULL DEFAULT 'backlog' CHECK (\"status\" IN ('backlog', 'inProgress', 'done')), \"score\" INTEGER NOT NULL DEFAULT 10, \"note\" INTEGER DEFAULT 5)")
    s!"draft DDL golden (defaults reified through fieldSpec), got {ddl}"
  let d1 := (Lean.Json.parse "{\"title\":\"t\"}").toOption.bind
    fun j => (rowOfJson Draft j).toOption
  check (d1.map (fun d => d.status == .backlog && d.score == 10 && d.note == some 5) == some true)
    "omitted fields take defaults"
  let d2 := (Lean.Json.parse "{\"title\":\"t\",\"note\":null}").toOption.bind
    fun j => (rowOfJson Draft j).toOption
  check (d2.map (·.note == none) == some true) "explicit null beats a default"

/-- Parse a rendered REAL literal back through SQLite itself — the actual
    consumer of a DDL DEFAULT. (`String.toFloat?` does not exist on this
    toolchain, and SQLite's parser is the one that matters here.) -/
private def sqliteReal (lit : String) : IO (Option Float) := do
  let db ← SQLite.open ":memory:"
  let stmt ← db.prepare s!"SELECT ({lit})"
  if ← stmt.step then return some (← stmt.columnDouble 0) else return none

private def testRealLiterals : IO Unit := do
  -- Float.toString prints six decimals (printf %f): every value here was
  -- silently misrecorded in DDL defaults and frozen snapshots (issue #34)
  let vals : List Float := [0.1, 1/3, 1e-300, 5e-7, 1e300, -0.0, 123456.789012345, 0.000001]
  for v in vals do
    match renderRealExact v with
    | .error m => throw <| IO.userError s!"FAIL: {v} must render exactly, got error: {m}"
    | .ok lit =>
        match ← sqliteReal lit with
        | some back => check (back == v) s!"exact REAL literal {lit} must round-trip to {v}, got {back}"
        | none => throw <| IO.userError s!"FAIL: no row for literal {lit}"
  -- a tiny REAL default must survive the DDL, not collapse to 0.000000
  let tiny : TableSpec :=
    ⟨"tiny", #[{ name := "ratio", sqlType := .real, nullable := false, fkTable := none,
                 dflt := some (.real 1e-300) }], #[], none⟩
  let ddl := tiny.ddl
  let some lit := (renderRealExact 1e-300).toOption
    | throw <| IO.userError "FAIL: 1e-300 must render exactly"
  -- the default token in the DDL is the exact literal, not a six-decimal
  -- rounding of it (`DEFAULT 0.000000` is what Float.toString used to emit)
  let defaultTok := ((((ddl.splitOn "DEFAULT ").getD 1 "").splitOn ",").getD 0 "").splitOn ")" |>.getD 0 ""
  check (defaultTok == lit) s!"DDL default must be the exact literal, got {defaultTok}"
  -- the DDL is executable and the stored default is the exact value
  let db ← SQLite.open ":memory:"
  db.exec ddl
  db.exec "INSERT INTO tiny DEFAULT VALUES"
  let stmt ← db.prepare "SELECT ratio FROM tiny"
  if ← stmt.step then
    check ((← stmt.columnDouble 0) == 1e-300) "the stored REAL default is the exact value"
  else throw <| IO.userError "FAIL: default insert produced no row"
  -- a frozen snapshot carries the exact literal too (Render.colLit)
  let snap := Render.specsLit [tiny]
  check ((snap.splitOn s!"LeanDb.Col.real ({lit})").length == 2)
    s!"frozen snapshot must carry the exact literal, got {snap}"
  check (Render.colLit (.real 5e-7) != "LeanDb.Col.real (0.000000)")
    "a sub-microscopic REAL must not render as the six-decimal rounding 0.000000"
  -- non-finite REAL defaults are refused loudly, not rendered as inf/NaN
  let bad (v : Float) : TableSpec :=
    ⟨"bad", #[{ name := "ratio", sqlType := .real, nullable := false, fkTable := none,
                dflt := some (.real v) }], #[], none⟩
  match validateSchema [bad (1.0/0.0)] with
  | .error (.schemaInvalid msg) =>
      check ((msg.splitOn "bad.ratio").length == 2) s!"refusal must name table and column, got {msg}"
  | _ => throw <| IO.userError "FAIL: an infinite REAL default must be refused"
  match validateSchema [bad (0.0/0.0)] with
  | .error _ => pure ()
  | .ok _ => throw <| IO.userError "FAIL: a NaN REAL default must be refused"


private def testClosedEnum : IO Unit := do
  check (roundtrip Status.inProgress && roundtrip Status.done) "closed enum roundtrip"
  check ((fromCol (α := Status) (.text "cancelled")).isOk == false)
    "unknown variant must fail decode"
  check (ClosedEnum.variants Status == #["backlog", "inProgress", "done"]) "variant names"
  check (ClosedEnum.all (α := Status) == #[.backlog, .inProgress, .done]) "all enumerates the world"
  check ((ClosedEnum.all (α := Status)).all fun s => ClosedEnum.decodeName (ClosedEnum.encodeName s) == some s)
    "encode/decode total over the world"
  let cols := Entity.columns Todo
  check ((cols.getD 1 default).enum == some #["backlog", "inProgress", "done"])
    "status column carries its closed world"
  check (((Entity.spec Todo).ddl.splitOn "CHECK").length == 2) "DDL contains CHECK"
  check ((Entity.spec Todo).ddl ==
      "CREATE TABLE IF NOT EXISTS \"todo\" (id INTEGER PRIMARY KEY AUTOINCREMENT, \"title\" TEXT NOT NULL, \"status\" TEXT NOT NULL CHECK (\"status\" IN ('backlog', 'inProgress', 'done')))")
    s!"todo DDL golden, got {(Entity.spec Todo).ddl}"

/-! ## Plan reflection (M4: pushdown as fetch narrowing) -/

private def agePlan : PlanFor (ts := [Author]) (fun (a : Stored Author) => a.val.age ≥ 40) := by leandb_plan

private def capturedPlan (n : Nat) : PlanFor (ts := [Author]) (fun (a : Stored Author) => a.val.age ≥ n) := by
  leandb_plan

private def joinPlan : PlanFor (ts := [Book, Author]) (fun (r : Stored Book × Stored Author) =>
    r.1.val.author == r.2.ref && r.2.val.age ≥ 40 && r.1.val.rating == none) := by leandb_plan

private def somePlan : PlanFor (ts := [Book]) (fun (b : Stored Book) => b.val.rating == some 4.5) := by
  leandb_plan

private def enumPlan : PlanFor (ts := [Todo]) (fun (t : Stored Todo) => t.val.status == Status.done) := by
  leandb_plan

private structure Flag where
  on : Bool
  deriving LeanDb.Entity
private def boolPlan : PlanFor (ts := [Flag]) (fun (f : Stored Flag) => f.val.on) := by leandb_plan

private def opaquePred (a : Stored Author) : Bool := a.val.age % 2 == 0
private def residualPlan : PlanFor (ts := [Author]) opaquePred := by leandb_plan

@[db] private def Author.isAdult (a : Author) : Bool := a.age ≥ 40
private def dbFnPlan : PlanFor (ts := [Author]) (fun (a : Stored Author) => a.val.isAdult) := by leandb_plan

private def isNonePlan : PlanFor (ts := [Book]) (fun (b : Stored Book) => b.val.rating.isNone) := by leandb_plan
private def isSomePlan : PlanFor (ts := [Book]) (fun (b : Stored Book) => b.val.rating.isSome) := by leandb_plan

private def orPlan : PlanFor (ts := [Author]) (fun (a : Stored Author) =>
    a.val.age < 30 || a.val.age > 50) := by leandb_plan

private def notPlan : PlanFor (ts := [Author]) (fun (a : Stored Author) => !(a.val.age ≥ 40)) := by leandb_plan

-- `if` on a column comparison: the shape a midnight-wrapping opening-hours
-- predicate takes (`if closes < opens then … else …`)
private def itePlan : PlanFor (ts := [Author]) (fun (a : Stored Author) =>
    if a.val.age < 30 then a.val.name == "x" else a.val.age > 50) := by leandb_plan
private def iteResidualPlan : PlanFor (ts := [Author]) (fun (a : Stored Author) =>
    if opaquePred a then a.val.age < 30 else true) := by leandb_plan

private def nullableOrderPlan : PlanFor (ts := [MaybeRank]) (fun (r : Stored MaybeRank) =>
    decide (r.val.score < some 4)) := by
  leandb_plan

private def enumOrderPlan : PlanFor (ts := [Todo]) (fun (t : Stored Todo) =>
    decide (t.val.status < Status.done)) := by
  leandb_plan

private def orResidualPlan : PlanFor (ts := [Author]) (fun (a : Stored Author) =>
    a.val.age < 30 || opaquePred a) := by leandb_plan

private def matchPlan : PlanFor (ts := [Todo]) (fun (t : Stored Todo) =>
    match t.val.status with | .done => false | _ => true) := by leandb_plan

@[db] private def Status.weight : Status → Nat
  | .backlog => 0 | .inProgress => 1 | .done => 2
private def weightPlan : PlanFor (ts := [Todo]) (fun (t : Stored Todo) => t.val.status.weight ≥ 1) := by
  leandb_plan

private def weightCapturedPlan (n : Nat) : PlanFor (ts := [Todo]) (fun (t : Stored Todo) =>
    t.val.status.weight ≥ n) := by leandb_plan

/-! Validated newtypes: a column stored *through* a projection. The
    planner may only unwrap the projection when it is the codec's own
    encoding — `Milli` qualifies, `Span` (whose codec mixes both fields)
    does not, and must stay residual. -/

private structure Milli where
  v : Nat
  deriving Repr, DecidableEq

private instance : ColCodec Milli := ColCodec.via (·.v) (.ok ⟨·⟩)

private structure Span where
  lo : Nat
  hi : Nat
  deriving Repr, DecidableEq

private instance : ColCodec Span :=
  ColCodec.via (fun s => s.lo * 1000 + s.hi) (fun n => .ok ⟨n / 1000, n % 1000⟩)

private structure Priced where
  price : Milli
  span : Span
  deriving LeanDb.Entity

private def newtypeEqPlan : PlanFor (ts := [Priced]) (fun (r : Stored Priced) => r.val.price.v == 500) := by
  leandb_plan

private def newtypeLePlan : PlanFor (ts := [Priced]) (fun (r : Stored Priced) =>
    r.val.price.v ≤ 500) := by leandb_plan

private def newtypeCapturedPlan (n : Nat) : PlanFor (ts := [Priced]) (fun (r : Stored Priced) =>
    r.val.price.v ≤ n) := by leandb_plan

private def newtypeGePlan (n : Nat) : PlanFor (ts := [Priced]) (fun (r : Stored Priced) =>
    r.val.price.v ≥ n) := by leandb_plan

private def newtypeAndPlan (n : Nat) : PlanFor (ts := [Priced]) (fun (r : Stored Priced) =>
    r.val.price.v ≤ n && r.val.price.v ≥ 10) := by leandb_plan

/-- The guard doing its job: same syntactic shape, different codec. -/
private def foreignProjPlan : PlanFor (ts := [Priced]) (fun (r : Stored Priced) =>
    r.val.span.lo ≤ 5) := by leandb_plan

private def foreignProjEqPlan : PlanFor (ts := [Priced]) (fun (r : Stored Priced) =>
    r.val.span.hi == 5) := by leandb_plan

/-! Case splits on a *captured parameter* of closed-enum type: after the
    column split, a `@[db]` function that inspects its parameter before
    its column argument (or a derived form like `!(d.forbids.contains k)`)
    is stuck on the parameter; the tactic splits on its world too, with a
    value/value guard. -/

inductive Diet where
  | vegetarian | pescatarian | omnivore
  deriving Repr, DecidableEq, LeanDb.ClosedEnum

inductive Kind where
  | meat | fish | plant
  deriving Repr, DecidableEq, LeanDb.ClosedEnum

structure Ingredient where
  name : String
  kind : Kind
  deriving Repr, LeanDb.Entity

private def Diet.forbids : Diet → List Kind
  | .vegetarian => [.meat, .fish] | .pescatarian => [.meat] | .omnivore => []

/-- The derived form: list membership, no `match` on the column at all. -/
@[db] private def Diet.allows (d : Diet) (k : Kind) : Bool := !(d.forbids.contains k)

/-- Matches on the parameter first: `whnf` is stuck on `d` once the
    column has been substituted. -/
@[db] private def Diet.allowsParamFirst (d : Diet) (k : Kind) : Bool :=
  match d with
  | .omnivore => true
  | .pescatarian => k != .meat
  | .vegetarian => k == .plant

/-- Matches on the column first: the column split alone leaves
    `d OP constant`, the plain value/value path. -/
@[db] private def Diet.allowsColumnFirst (d : Diet) (k : Kind) : Bool :=
  match k with
  | .plant => true
  | .fish => d != .vegetarian
  | .meat => d == .omnivore

private def allowsPlan (d : Diet) : PlanFor (ts := [Ingredient]) (fun (i : Stored Ingredient) =>
    d.allows i.val.kind) := by leandb_plan

private def paramFirstPlan (d : Diet) : PlanFor (ts := [Ingredient]) (fun (i : Stored Ingredient) =>
    d.allowsParamFirst i.val.kind) := by leandb_plan

private def columnFirstPlan (d : Diet) : PlanFor (ts := [Ingredient]) (fun (i : Stored Ingredient) =>
    d.allowsColumnFirst i.val.kind) := by leandb_plan

/-- A captured `Nat` is not a closed world: after the column split the
    branch `kindBonus n .plant` is stuck on `n` and must stay residual. -/
private def kindBonus (n : Nat) (k : Kind) : Bool :=
  match k with | .plant => n > 3 | _ => false
private def natParamPlan (n : Nat) : PlanFor (ts := [Ingredient]) (fun (i : Stored Ingredient) =>
    kindBonus n i.val.kind) := by leandb_plan

/-- An enum parameter inside a genuinely opaque function: the split fires
    but no branch can be evaluated, so the conjunct stays residual. -/
@[irreducible] private def dietOpaque (d : Diet) (k : Kind) : Bool :=
  d == .omnivore || k == .plant
private def opaqueParamPlan (d : Diet) : PlanFor (ts := [Ingredient]) (fun (i : Stored Ingredient) =>
    dietOpaque d i.val.kind) := by leandb_plan

/-- A plan golden: the SQL of its pushable projection, the bind values in
    placeholder order, and the residual count. -/
private def checkPlan (p : PlanFor w) (sql : String) (binds : Array Col) (residual : Nat)
    (label : String) : IO Unit :=
  let got := (p.plan.approx.renderT, p.plan.residuals)
  unless got == ((sql, binds), residual) do
    throw <| IO.userError s!"FAIL: {label}: got {repr got}"

private def testPlans : IO Unit := do
  checkPlan agePlan "t0.\"age\" >= ?" #[.int 40] 0 "age plan fully pushed"
  checkPlan (capturedPlan 41) "t0.\"age\" >= ?" #[.int 41] 0 "captured variable as bound param"
  checkPlan joinPlan
    "((t0.\"author\" IS t1.\"id\" AND t1.\"age\" >= ?) AND t0.\"rating\" IS ?)" #[.int 40, .null] 0
    "equi-join pushes as eq2 + per-table conds"
  check joinPlan.plan.approx.hasJoin "join plan routes to joined executor"
  checkPlan somePlan "t0.\"rating\" IS ?" #[.real 4.5] 0 "some-literal via Option codec"
  checkPlan enumPlan "t0.\"status\" IS ?" #[.text "done"] 0 "closed enum pushes as its name"
  checkPlan boolPlan "t0.\"on\" IS ?" #[.int 1] 0 "bare Bool column"
  checkPlan residualPlan "1" #[] 1 "opaque predicate is fully residual"
  checkPlan dbFnPlan "t0.\"age\" >= ?" #[.int 40] 0 "@[db] def unfolds"
  checkPlan isNonePlan "t0.\"rating\" IS NULL" #[] 0 "isNone as IS NULL"
  checkPlan isSomePlan "t0.\"rating\" IS NOT NULL" #[] 0 "isSome as IS NOT NULL"
  checkPlan orPlan "(t0.\"age\" < ? OR t0.\"age\" > ?)" #[.int 30, .int 50] 0
    "disjunction pushes whole"
  checkPlan notPlan "t0.\"age\" < ?" #[.int 40] 0 "negation is exact"
  checkPlan itePlan
    "((t0.\"age\" < ? AND t0.\"name\" IS ?) OR (t0.\"age\" >= ? AND t0.\"age\" > ?))"
    #[.int 30, .text "x", .int 30, .int 50] 0
    "if-then-else on columns pushes as (c ∧ t) ∨ (¬c ∧ e)"
  checkPlan iteResidualPlan "1" #[] 1 "if with an opaque condition is fully residual"
  checkPlan nullableOrderPlan "1" #[] 1 "nullable ordering remains residual"
  checkPlan enumOrderPlan "(t0.\"status\" IS ? OR t0.\"status\" IS ?)"
    #[.text "backlog", .text "inProgress"] 0
    "closed-enum ordering case-splits instead of using SQL text order"
  checkPlan orResidualPlan "1" #[] 1 "or with unpushable side is fully residual"
  checkPlan matchPlan "(t0.\"status\" IS ? OR t0.\"status\" IS ?)"
    #[.text "backlog", .text "inProgress"] 0
    "match on closed enum case-splits to a disjunction"
  checkPlan weightPlan "(t0.\"status\" IS ? OR t0.\"status\" IS ?)"
    #[.text "inProgress", .text "done"] 0
    "enum-table function case-splits, false branches drop"
  -- the value/value guards a case split leaves behind compare two values
  -- that are both known when the plan is built (`Pred.vvOrd`), so `0 ≥ 1`
  -- folds to `ff` and drops its branch: only the surviving columns reach SQL
  checkPlan (weightCapturedPlan 1) "(t0.\"status\" IS ? OR t0.\"status\" IS ?)"
    #[.text "inProgress", .text "done"] 0
    "case split against a captured threshold folds the value tests"
  checkPlan newtypeEqPlan "t0.\"price\" IS ?" #[.int 500] 0
    "newtype projection that is the codec's encoding pushes (eq, literal)"
  checkPlan newtypeLePlan "t0.\"price\" <= ?" #[.int 500] 0
    "ordering through the encoding projection pushes (literal)"
  checkPlan (newtypeCapturedPlan 700) "t0.\"price\" <= ?" #[.int 700] 0
    "ordering through the encoding projection pushes (captured variable)"
  checkPlan (newtypeGePlan 700) "t0.\"price\" >= ?" #[.int 700] 0
    "reverse ordering through the encoding projection pushes"
  checkPlan (newtypeAndPlan 700) "(t0.\"price\" <= ? AND t0.\"price\" >= ?)" #[.int 700, .int 10] 0
    "both bounds through the projection push"
  checkPlan foreignProjPlan "1" #[] 1
    "projection that is not the codec's encoding stays residual (order)"
  checkPlan foreignProjEqPlan "1" #[] 1
    "projection that is not the codec's encoding stays residual (equality)"
  -- captured closed-enum parameter: the world of `d` is split too, guarded
  -- by `d IS 'c'` — known at plan build, so every guard but one folds away
  -- and both match orders leave the same column condition
  checkPlan (paramFirstPlan .vegetarian) "t0.\"kind\" IS ?" #[.text "plant"] 0
    "@[db] function matching on the parameter first splits on its world"
  checkPlan (columnFirstPlan .vegetarian) "t0.\"kind\" IS ?" #[.text "plant"] 0
    "@[db] function matching on the column first reaches the same plan"
  for d in ClosedEnum.all (α := Diet) do
    check ((allowsPlan d).plan.residuals == 0)
      s!"derived allows ({repr d}) pushes with residual 0"
    check ((paramFirstPlan d).plan.residuals == 0)
      s!"param-first allows ({repr d}) pushes with residual 0"
    check ((columnFirstPlan d).plan.residuals == 0)
      s!"column-first allows ({repr d}) pushes with residual 0"
  checkPlan (allowsPlan .vegetarian) "(t0.\"kind\" IS NOT ? AND t0.\"kind\" IS NOT ?)"
    #[.text "meat", .text "fish"] 0 "derived allows folds to the forbidden kinds"
  -- omnivore forbids nothing: the whole conjunct folds to `true` — no
  -- narrowing, no residual
  checkPlan (paramFirstPlan .omnivore) "1" #[] 0 "a diet that allows everything folds to tt"
  checkPlan (natParamPlan 5) "1" #[] 1 "captured Nat inside a non-@[db] function stays residual"
  checkPlan (opaqueParamPlan .omnivore) "1" #[] 1
    "enum parameter inside an opaque function stays residual"

/-! ## Typed predicate IR (LEP-0002)

Plans built by hand over the fixtures, then the tactic's own: the
ill-typed plans are unrepresentable, `denote` agrees with the lambda,
`approx`/`residuals` split the residual out, `render` is pinned, and
every plan `leandb_plan` emitted above is *coherent* — its denotation is
the lambda it was reified from, opaque leaves included. -/

-- the right type, from the symbol alone
#check (Pred.Col.here Author.Field.age : Pred.Col [Author] Nat _)
-- wrong type is unrepresentable
#check_failure (Pred.Col.here Author.Field.age : Pred.Col [Author] String _)
-- wrong table is unrepresentable
#check_failure (Pred.Col.here Book.Field.title : Pred.Col [Author] _ _)
-- no `SqlOrd (Option Float)`: ordering a nullable column is unrepresentable
#check_failure (Pred.ord (Pred.Col.here Book.Field.rating) .lt (some 3.0) : Pred [Book])
-- a value of the wrong type for its column is unrepresentable
#check_failure (Pred.eq (Pred.Col.here Todo.Field.status) .eq (3 : Nat) : Pred [Todo])
-- `via`: the projection that IS the codec's encoding, proof by `rfl`…
#check (Pred.Col.via (Pred.Col.here Priced.Field.price) (·.v) (fun _ => rfl) : Pred.Col [Priced] Nat _)
-- …and the one that is not (`Span`'s codec mixes both fields): `rfl` does not close
#check_failure (Pred.Col.via (Pred.Col.here Priced.Field.span) (·.lo) (fun _ => rfl) : Pred.Col [Priced] Nat _)
-- `some` lifts a column to its `Option`, for col-vs-col through `some`
#check (Pred.Col.via (Pred.Col.here Author.Field.age) some (fun _ => rfl) : Pred.Col [Author] (Option Nat) _)
-- the theorem, elaborated
example (snap : Pred.Snapshot) (p : Pred ts) (r : Rows ts) (h : p.denote snap r = true) :
    p.approx.denote snap r = true :=
  Pred.approx_sound snap p r h

private def ada : Stored Author := ⟨⟨1⟩, ⟨"Ada", 36⟩⟩
private def alan : Stored Author := ⟨⟨2⟩, ⟨"Alan", 41⟩⟩
private def computable : Stored Book := ⟨⟨7⟩, ⟨"On Computable Numbers", alan.ref, some 4.5⟩⟩
private def notes : Stored Book := ⟨⟨8⟩, ⟨"Notes on the Analytical Engine", ada.ref, none⟩⟩
private def unrated : Stored Book := ⟨⟨9⟩, ⟨"Unrated", alan.ref, none⟩⟩
private def cheap : Stored Priced := ⟨⟨1⟩, ⟨⟨400⟩, ⟨1, 2⟩⟩⟩
private def dear : Stored Priced := ⟨⟨2⟩, ⟨⟨900⟩, ⟨1, 2⟩⟩⟩

/-- `agePlan`, by hand. -/
private def ageP : Pred [Author] := .ord (.here Author.Field.age) .ge 40
/-- `joinPlan`, by hand: `r.1.val.author == r.2.ref && r.2.val.age ≥ 40 && r.1.val.rating == none`. -/
private def joinP : Pred [Book, Author] :=
  .and (.and (.eq2 (.here Book.Field.author) .eq (.there .id))
             (.ord (.there (.here Author.Field.age)) .ge 40))
       (.eq (.here Book.Field.rating) .eq none)
/-- `itePlan`, by hand: `if age < 30 then name == "x" else age > 50`. -/
private def iteP : Pred [Author] :=
  .or (.and (.ord (.here Author.Field.age) .lt 30) (.eq (.here Author.Field.name) .eq "x"))
      (.and (.ord (.here Author.Field.age) .ge 30) (.ord (.here Author.Field.age) .gt 50))
private def oddP : Pred [Author] := .opaque fun a => a.val.age % 2 == 0

private def testTypedPred : IO Unit := do
  -- denote agrees with the lambda
  let ageL := fun (a : Stored Author) => a.val.age ≥ 40
  for a in [ada, alan] do
    check (ageP.denote .empty a == ageL a) s!"ord denotes like the lambda on {a.val.name}"
  let joinL := fun (r : Stored Book × Stored Author) =>
    r.1.val.author == r.2.ref && r.2.val.age ≥ 40 && r.1.val.rating == none
  for b in [computable, notes, unrated] do
    for a in [ada, alan] do
      check (joinP.denote .empty (b, a) == joinL (b, a))
        s!"join denotes like the lambda on ({b.val.title}, {a.val.name})"
  check ((joinP.denote .empty (unrated, alan), joinP.denote .empty (computable, alan)) == (true, false))
    "join denotation is not vacuous"
  let nullP : Pred [Book] := .isNull (.here Book.Field.rating)
  check (nullP.denote .empty notes == true && nullP.denote .empty computable == false) "isNull denotes NULL"
  check (nullP.neg.denote .empty notes == false && nullP.neg.denote .empty computable == true) "neg of isNull"
  check (oddP.denote .empty ada == true && oddP.denote .empty alan == false) "opaque denotes its function"
  check (ageP.neg.denote .empty ada == true && ageP.neg.denote .empty alan == false) "neg of ord is exact"
  -- approx drops opaques; residuals counts them
  let mixed : Pred [Author] := .and ageP oddP
  check (mixed.residuals == 1 && mixed.hasOpaque) "one residual conjunct"
  check (mixed.approx.residuals == 0 && !mixed.approx.hasOpaque) "approx has no residual"
  check ((mixed.approx.renderT) == (ageP.renderT)) "approx of (pushed ∧ opaque) is the pushed side"
  check (((Pred.or ageP oddP).approx.renderT).1 == "1") "or with an opaque side widens to true"
  for a in [ada, alan] do
    check (!(mixed.denote .empty a) || mixed.approx.denote .empty a) s!"approx_sound, observed on {a.val.name}"
  -- render, pinned: these strings are what the untyped renderer produced
  check (ageP.renderT == ("t0.\"age\" >= ?", #[.int 40]))
    s!"age render, got {repr (ageP.renderT)}"
  check (joinP.renderT ==
      ("((t0.\"author\" IS t1.\"id\" AND t1.\"age\" >= ?) AND t0.\"rating\" IS ?)", #[.int 40, .null]))
    s!"join render, got {repr (joinP.renderT)}"
  check (iteP.renderT ==
      ("((t0.\"age\" < ? AND t0.\"name\" IS ?) OR (t0.\"age\" >= ? AND t0.\"age\" > ?))",
        #[.int 30, .text "x", .int 30, .int 50]))
    s!"ite render, got {repr (iteP.renderT)}"
  check (joinP.render (fun _ => "t0") ==
      ("((t0.\"author\" IS t0.\"id\" AND t0.\"age\" >= ?) AND t0.\"rating\" IS ?)", #[.int 40, .null]))
    s!"single-table render aliases every index to t0, got {repr (joinP.render (fun _ => "t0"))}"
  check ((ageP.renderT).1 == "t0.\"age\" >= ?" && (ageP.render (fun _ => "t0")).1 == "t0.\"age\" >= ?")
    "render text, pinned"
  check (mixed.describe == "pushed: t0.\"age\" >= ?, residual conjuncts: 1")
    s!"describe format, got {mixed.describe}"
  -- a column name with an embedded quote: the render must quote it the way
  -- the DDL does (`quoteIdent`), or the SQL it emits addresses nothing
  let qp : Pred [Quoted] := .eq (.here Quoted.Field.«a"b») .eq 5
  check (qp.renderT == ("t0.\"«a\"\"b»\" IS ?", #[.int 5]))
    s!"quoted-name render, got {repr (qp.renderT)}"
  check ((Entity.spec Quoted).ddl.contains "\"«a\"\"b»\" INTEGER NOT NULL")
    s!"DDL and render quote the name identically, got {(Entity.spec Quoted).ddl}"
  check (qp.render (fun _ => "t0") == qp.renderT) "quoted name under the single-table alias"
  -- plan surface
  check (joinP.hasJoin && !ageP.hasJoin) "hasJoin"
  check (joinP.tables == [0, 1] && ageP.tables == [0]) "tables"
  check (joinP.conjuncts.length == 3) "conjuncts"
  check ((joinP.forTable 1).render (fun _ => "t0") == ("t0.\"age\" >= ?", #[.int 40]))
    "forTable keeps only the conjuncts touching that table"
  check ((joinP.forTable 0).render (fun _ => "t0") == ("t0.\"rating\" IS ?", #[.null]))
    "forTable 0 keeps the rating test"
  -- value/value folds at plan build
  check ((Pred.vvOrd (ts := [Author]) (0 : Nat) .ge 1).renderT == ("0", #[]))
    "vvOrd folds 0 ≥ 1 to ff"
  check ((Pred.vvEq (ts := [Author]) Status.done .eq Status.done).renderT == ("1", #[]))
    "vvEq folds on the encoded name"
  check ((Pred.vvEq (ts := [Author]) (none : Option Nat) .eq none).renderT == ("1", #[]))
    "vvEq is null-safe (none IS none)"
  -- through a newtype projection: same column, compared on the representation
  let priceP : Pred [Priced] := .ord (.via (.here Priced.Field.price) (·.v) (fun _ => rfl)) .le 500
  check (priceP.renderT == ("t0.\"price\" <= ?", #[.int 500]))
    s!"via renders the underlying column, got {repr (priceP.renderT)}"
  check (priceP.denote .empty cheap == true && priceP.denote .empty dear == false) "via denotes through the projection"

private def quotedDbPath : System.FilePath := ".lake" / "leandb_test_quoted.sqlite"

/-- The quoted column, end to end: the DDL created the quoted identifier,
    the rendered WHERE addresses the same identifier, and SQLite agrees. -/
private def testQuotedEndToEnd : IO Unit := do
  if ← quotedDbPath.pathExists then IO.FS.removeFile quotedDbPath
  let r ← withDb quotedDbPath [Entity.spec Quoted] do
    discard <| insert Quoted ⟨5⟩
    discard <| insert Quoted ⟨7⟩
    let p : Pred [Quoted] := .eq (.here Quoted.Field.«a"b») .eq 5
    return (← selectP [Quoted] p).map (·.val.«a"b»)
  match r with
  | .ok xs => check (xs == #[5]) s!"quoted column filters, got {repr xs}"
  | .error e => throw <| IO.userError s!"FAIL: quoted column e2e: {e}"

/-! ### Coherence of the tactic's plans

`(reify where').denote .empty r = where' r`: the plan `leandb_plan` emitted is
the lambda, row for row — pushed leaves through their encodings, opaque
leaves through the conjunct they carry. Together with `approx_sound` this
is the whole safety argument: what ships to SQL accepts everything the
lambda accepts. -/

private def checkCoherent {ts : List Type} {w : Rows ts → Bool} (p : PlanFor w)
    (rows : Array (Rows ts)) (label : String) : IO Unit := do
  for r in rows do
    check (p.plan.denote .empty r == w r) s!"coherence: {label}"

private def authors : Array (Stored Author) :=
  #[ada, alan, ⟨⟨3⟩, ⟨"x", 40⟩⟩, ⟨⟨4⟩, ⟨"Grace", 29⟩⟩, ⟨⟨5⟩, ⟨"x", 51⟩⟩, ⟨⟨6⟩, ⟨"Ed", 30⟩⟩]
private def books : Array (Stored Book) := #[computable, notes, unrated]
private def bookAuthors : Array (Stored Book × Stored Author) :=
  books.flatMap fun b => authors.map fun a => (b, a)
private def todos : Array (Stored Todo) :=
  #[⟨⟨1⟩, ⟨"write plan", .done⟩⟩, ⟨⟨2⟩, ⟨"build engine", .inProgress⟩⟩, ⟨⟨3⟩, ⟨"ship", .backlog⟩⟩]
private def flags : Array (Stored Flag) := #[⟨⟨1⟩, ⟨true⟩⟩, ⟨⟨2⟩, ⟨false⟩⟩]
private def ranks : Array (Stored MaybeRank) :=
  #[⟨⟨1⟩, ⟨none⟩⟩, ⟨⟨2⟩, ⟨some 3⟩⟩, ⟨⟨3⟩, ⟨some 4⟩⟩, ⟨⟨4⟩, ⟨some 9⟩⟩]
private def priced : Array (Stored Priced) :=
  #[cheap, dear, ⟨⟨3⟩, ⟨⟨500⟩, ⟨5, 7⟩⟩⟩, ⟨⟨4⟩, ⟨⟨700⟩, ⟨0, 5⟩⟩⟩, ⟨⟨5⟩, ⟨⟨10⟩, ⟨9, 5⟩⟩⟩]
private def ingredients : Array (Stored Ingredient) :=
  #[⟨⟨1⟩, ⟨"pork", .meat⟩⟩, ⟨⟨2⟩, ⟨"salmon", .fish⟩⟩, ⟨⟨3⟩, ⟨"tofu", .plant⟩⟩]

/-! ### Child-table quantifiers (LEP-0004)

`exists`/`forall` over a related table: the relation is typed by both keys
being `Id α`, so a quantifier over the wrong foreign key is
unrepresentable; `denote` quantifies over a `Snapshot`; `neg` swaps them
exactly; `approx` recurses into the body and the executor's re-check
restores what it widened; the rendering is a correlated subquery. -/

-- parent reference and child key agree on the entity: representable
#check (Pred.forall (ts := [Author]) .id (.here Book.Field.author) .tt : Pred [Author])
-- fk not an `Id`
#check_failure (Pred.forall (ts := [Author]) .id (.here Book.Field.title) .tt : Pred [Author])
-- `Id` of the wrong entity: `Book.author : Id Author` is no key onto `Book`
#check_failure (Pred.forall (ts := [Book]) .id (.here Book.Field.author) .tt : Pred [Book])

/-- Authors all of whose books are rated. -/
private def allRatedP : Pred [Author] :=
  Pred.all (.here Book.Field.author) (.isNotNull (.here Book.Field.rating))
/-- Authors with an unrated book. -/
private def unratedP : Pred [Author] :=
  Pred.any (.here Book.Field.author) (.isNull (.here Book.Field.rating))
/-- Authors all of whose books have an even-length title: the body is an
    opaque leaf, so `approx` widens the quantifier to vacuous truth. -/
private def evenTitlesP : Pred [Author] :=
  Pred.all (.here Book.Field.author) (.opaque fun (b, _) => b.val.title.length % 2 == 0)
/-- Authors with a book titled after themselves — the body reaches the
    outer row. -/
private def selfTitledP : Pred [Author] :=
  Pred.any (.here Book.Field.author)
    (.eq2 (.here Book.Field.title) .eq (.there (.here Author.Field.name)))
/-- Nested: some book of the author whose (1:1) author row is 40 or older —
    a join expressed as a quantifier, at depth 1. -/
private def nestedP : Pred [Author] :=
  Pred.any (.here Book.Field.author)
    (Pred.exists (.here Book.Field.author) .id (.ord (.here Author.Field.age) .ge 40))
/-- Over two tables: the author (table 1) has a book with this book's
    (table 0) title — the quantifier relates both outer tables. -/
private def crossP : Pred [Book, Author] :=
  Pred.exists (.there .id) (.here Book.Field.author)
    (.eq2 (.here Book.Field.title) .eq (.there (.here Book.Field.title)))

private def bookSnap : Pred.Snapshot := Pred.Snapshot.empty.add Book books

/-- The two-fetch answer, by hand. -/
private def allRatedByHand : Array (Stored Author) :=
  authors.filter fun a => books.all fun b => b.val.author != a.ref || b.val.rating.isSome
private def unratedByHand : Array (Stored Author) :=
  authors.filter fun a => books.any fun b => b.val.author == a.ref && b.val.rating.isNone

private def ids (rows : Array (Stored Author)) : Array Int64 := rows.map (·.id.toInt64)

private def testQuantifiers : IO Unit := do
  -- denote over a fixture snapshot is the hand-written two-fetch answer
  check (ids (authors.filter (allRatedP.denote bookSnap)) == ids allRatedByHand
      && ids allRatedByHand == #[3, 4, 5, 6])
    s!"forall denotes the two-fetch answer, got {ids (authors.filter (allRatedP.denote bookSnap))}"
  check (ids (authors.filter (unratedP.denote bookSnap)) == ids unratedByHand
      && ids unratedByHand == #[1, 2])
    s!"exists denotes the two-fetch answer, got {ids (authors.filter (unratedP.denote bookSnap))}"
  -- under an empty snapshot forall is vacuous and exists is empty
  check (authors.all (allRatedP.denote .empty) && !(authors.any (unratedP.denote .empty)))
    "empty snapshot: forall vacuous, exists false"
  -- neg is exact and swaps the quantifiers
  for a in authors do
    check (allRatedP.neg.denote bookSnap a == !(allRatedP.denote bookSnap a))
      s!"neg of forall on {a.val.name}"
    check (allRatedP.neg.denote bookSnap a == unratedP.denote bookSnap a)
      s!"neg of forall is the exists on {a.val.name}"
  check ((Pred.Snapshot.empty.rows Book).isEmpty && (bookSnap.rows Author).isEmpty
      && (bookSnap.rows Book).size == 3)
    "snapshot rows by table"
  check ((bookSnap.rows Book).map (·.id.toInt64) == books.map (·.id.toInt64)
      && (bookSnap.rows Book).map (·.val.title) == books.map (·.val.title))
    "every added row comes back through the codec round trip"
  -- approx recurses into the body: the opaque leaf is counted and dropped,
  -- and what remains never excludes a row the plan accepts
  check (evenTitlesP.residuals == 1 && evenTitlesP.approx.residuals == 0) "residual inside a body"
  check (ids (authors.filter (evenTitlesP.denote bookSnap)) == #[1, 3, 4, 5, 6])
    "opaque body denotes its function"
  check (authors.all (evenTitlesP.approx.denote bookSnap)) "approx of an opaque body is vacuous"
  for a in authors do
    check (!(evenTitlesP.denote bookSnap a) || evenTitlesP.approx.denote bookSnap a)
      s!"approx_sound through a quantifier, observed on {a.val.name}"
  -- the plan surface
  check (allRatedP.tables == [0] && !allRatedP.hasJoin) "a quantifier on table 0 is not a join"
  check (crossP.tables == [1, 0] && crossP.hasJoin) "a quantifier reaching two outer tables is a join"
  check ((Pred.and allRatedP unratedP).children.map (fun c => @Entity.tableName c.1 c.2) == ["book"])
    "children deduplicate by table"
  check (nestedP.children.map (fun c => @Entity.tableName c.1 c.2) == ["book", "author"])
    "children collect nested quantifiers"
  -- render, pinned
  check (unratedP.renderT ==
      ("EXISTS (SELECT 1 FROM \"book\" AS s0 WHERE s0.\"author\" IS t0.\"id\" AND s0.\"rating\" IS NULL)", #[]))
    s!"exists render, got {repr unratedP.renderT}"
  check (allRatedP.renderT ==
      ("NOT EXISTS (SELECT 1 FROM \"book\" AS s0 WHERE s0.\"author\" IS t0.\"id\" AND s0.\"rating\" IS NULL)", #[]))
    s!"forall render negates the body, got {repr allRatedP.renderT}"
  check (selfTitledP.renderT ==
      ("EXISTS (SELECT 1 FROM \"book\" AS s0 WHERE s0.\"author\" IS t0.\"id\" AND s0.\"title\" IS t0.\"name\")", #[]))
    s!"body reaches the outer alias, got {repr selfTitledP.renderT}"
  check (nestedP.renderT ==
      ("EXISTS (SELECT 1 FROM \"book\" AS s0 WHERE s0.\"author\" IS t0.\"id\" AND EXISTS (SELECT 1 FROM \"author\" AS s1 WHERE s1.\"id\" IS s0.\"author\" AND s1.\"age\" >= ?))",
        #[.int 40]))
    s!"nested render, got {repr nestedP.renderT}"
  check (crossP.renderT ==
      ("EXISTS (SELECT 1 FROM \"book\" AS s0 WHERE s0.\"author\" IS t1.\"id\" AND s0.\"title\" IS t0.\"title\")", #[]))
    s!"two-table render, got {repr crossP.renderT}"
  check (evenTitlesP.approx.renderT ==
      ("NOT EXISTS (SELECT 1 FROM \"book\" AS s0 WHERE s0.\"author\" IS t0.\"id\" AND 0)", #[]))
    s!"approx of an opaque body renders vacuous, got {repr evenTitlesP.approx.renderT}"
  check (allRatedP.render (fun _ => "t0") == allRatedP.renderT)
    "single-table aliasing agrees on table 0"
  -- `pred%`: the tactic's reflection as a term
  let agePP : Pred [Author] := pred% [Author] fun a => a.val.age ≥ 40
  check (agePP.renderT == agePlan.plan.renderT && agePP.residuals == 0)
    "pred% reflects like leandb_plan"
  let n := 41
  let capPP : Pred [Author] := pred% [Author] fun a => a.val.age ≥ n
  check (capPP.renderT == (capturedPlan 41).plan.renderT) "pred% binds captured variables"
  let joinPP : Pred [Book, Author] := pred% [Book, Author] fun (b, a) =>
    b.val.author == a.ref && a.val.age ≥ 40 && b.val.rating == none
  check (joinPP.renderT == joinPlan.plan.renderT) "pred% over a tuple lambda"
  for r in bookAuthors do
    check (joinPP.denote .empty r == joinPlan.plan.denote .empty r) "pred% plan is coherent"
  let allRatedPP : Pred [Author] :=
    Pred.all (.here Book.Field.author) (pred% [Book, Author] fun (b, _) => b.val.rating.isSome)
  check (allRatedPP.renderT == allRatedP.renderT) "pred% as a quantifier body"
  let residualPP : Pred [Author] := pred% [Author] opaquePred
  check (residualPP.residuals == 1) "pred% falls back to an opaque leaf"

private def testCoherence : IO Unit := do
  checkCoherent agePlan authors "agePlan"
  checkCoherent (capturedPlan 41) authors "capturedPlan 41"
  checkCoherent joinPlan bookAuthors "joinPlan"
  checkCoherent somePlan books "somePlan"
  checkCoherent enumPlan todos "enumPlan"
  checkCoherent boolPlan flags "boolPlan"
  checkCoherent residualPlan authors "residualPlan (the opaque leaf is the conjunct)"
  checkCoherent dbFnPlan authors "dbFnPlan"
  checkCoherent isNonePlan books "isNonePlan"
  checkCoherent isSomePlan books "isSomePlan"
  checkCoherent orPlan authors "orPlan"
  checkCoherent notPlan authors "notPlan"
  checkCoherent itePlan authors "itePlan"
  checkCoherent iteResidualPlan authors "iteResidualPlan"
  checkCoherent nullableOrderPlan ranks "nullableOrderPlan"
  checkCoherent enumOrderPlan todos "enumOrderPlan"
  checkCoherent orResidualPlan authors "orResidualPlan (the opaque leaf is the whole disjunction)"
  checkCoherent matchPlan todos "matchPlan"
  checkCoherent weightPlan todos "weightPlan"
  checkCoherent (weightCapturedPlan 1) todos "weightCapturedPlan 1"
  checkCoherent (weightCapturedPlan 0) todos "weightCapturedPlan 0"
  checkCoherent (weightCapturedPlan 3) todos "weightCapturedPlan 3"
  checkCoherent newtypeEqPlan priced "newtypeEqPlan"
  checkCoherent newtypeLePlan priced "newtypeLePlan"
  checkCoherent (newtypeCapturedPlan 700) priced "newtypeCapturedPlan 700"
  checkCoherent (newtypeGePlan 700) priced "newtypeGePlan 700"
  checkCoherent (newtypeAndPlan 700) priced "newtypeAndPlan 700"
  checkCoherent foreignProjPlan priced "foreignProjPlan"
  checkCoherent foreignProjEqPlan priced "foreignProjEqPlan"
  for d in ClosedEnum.all (α := Diet) do
    checkCoherent (allowsPlan d) ingredients s!"allowsPlan {repr d}"
    checkCoherent (paramFirstPlan d) ingredients s!"paramFirstPlan {repr d}"
    checkCoherent (columnFirstPlan d) ingredients s!"columnFirstPlan {repr d}"
    checkCoherent (opaqueParamPlan d) ingredients s!"opaqueParamPlan {repr d}"
  checkCoherent (natParamPlan 5) ingredients "natParamPlan 5"
  checkCoherent (natParamPlan 2) ingredients "natParamPlan 2"

/-! ## JSON, derived from the schema (M5) -/

private def parseJ (str : String) : IO Lean.Json :=
  match Lean.Json.parse str with
  | .ok j => pure j
  | .error e => throw <| IO.userError s!"FAIL: json parse: {e}"

private def testJson : IO Unit := do
  let b : Stored Book := ⟨⟨7⟩, ⟨"T", ⟨3⟩, none⟩⟩
  check ((rowJson Book b).compress == "{\"author\":3,\"id\":7,\"rating\":null,\"title\":\"T\"}")
    s!"row JSON shape, got {(rowJson Book b).compress}"
  let j ← parseJ "{\"title\":\"T2\",\"author\":3}"
  let full := rowOfJson Book j
  check (full.toOption.map (fun bk => bk.title == "T2" && bk.rating == none) == some true)
    "rowOfJson decodes with missing nullable as none"
  let merged := rowMergeJson Book b.val j
  check (merged.toOption.map (fun bk => bk.title == "T2" && bk.author == b.val.author) == some true)
    "rowMergeJson overlays only present fields"
  check ((rowOfJson Book (← parseJ "{\"author\":3}")).isOk == false)
    "missing required field must fail"
  check ((rowOfJson Draft (← parseJ "null")).isOk == false)
    "insert input must be an object even when every field has a default"
  check ((rowOfJson Draft (← parseJ "{\"title\":\"t\",\"scroe\":9}")).isOk == false)
    "insert must reject unknown fields instead of silently taking a default"
  check ((rowMergeJson Book b.val (← parseJ "{\"titel\":\"typo\"}")).isOk == false)
    "update must reject unknown fields instead of silently doing nothing"
  let bogus := rowMergeJson Todo ⟨"x", .backlog⟩ (← parseJ "{\"status\":\"bogus\"}")
  match bogus with
  | .error (.decode "todo" "status" _) => pure ()
  | _ => throw <| IO.userError "FAIL: closed world must reject bogus via JSON"

/-! ## End-to-end against SQLite -/

private def dbPath : System.FilePath := ".lake" / "leandb_test.sqlite"

private def freshDb : IO Unit := do
  if ← dbPath.pathExists then IO.FS.removeFile dbPath

private def expectOk (r : Except DbError α) (context : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {context}: {e}"

private def expectErr (r : Except DbError α) (code : String) (context : String) : IO Unit :=
  match r with
  | .ok _ => throw <| IO.userError s!"FAIL: {context}: expected [{code}], got success"
  | .error e =>
      unless e.code == code do
        throw <| IO.userError s!"FAIL: {context}: expected [{code}], got {e}"

private def seed : DbM (Stored Author × Stored Author × Stored Book) := do
  let ada ← insert Author ⟨"Ada", 36⟩
  let alan ← insert Author ⟨"Alan", 41⟩
  let book ← insert Book ⟨"On Computable Numbers", alan.ref, some 4.5⟩
  discard <| insert Book ⟨"Notes on the Analytical Engine", ada.ref, none⟩
  return (ada, alan, book)

private def testEndToEnd : IO Unit := do
  freshDb
  let r ← withDb dbPath schema do
    let (ada, alan, _) ← seed
    -- get
    let got ← get ada.id
    check' (got.map (·.val.name) == some "Ada") "get returns the row"
    -- single-table select: dependent type is Stored Author
    let adults ← select [Author] (fun a => a.val.age ≥ 40) (.key (·.val.name))
    check' (adults.map (·.val.name) == #["Alan"]) "typed where' filters"
    -- join: Rows [Book, Author] = Stored Book × Stored Author
    let byAuthor ← select [Book, Author]
      (fun (b, a) => b.val.author == a.ref)
      (.key fun (b, _) => b.val.title)
    check' (byAuthor.map (fun (b, a) => ((b.val.title.take 5).toString, a.val.name))
      == #[("Notes", "Ada"), ("On Co", "Alan")]) "equi-join via Ref equality"
    -- differential: the planned path must equal the unplanned reference
    let key := fun (r : Stored Book × Stored Author) => (r.1.id.toInt64, r.2.id.toInt64)
    let pred := fun (r : Stored Book × Stored Author) =>
      r.1.val.author == r.2.ref && r.2.val.age ≥ 40 && r.1.val.rating != none
    let planned ← select [Book, Author] pred (.key fun (b, _) => b.val.title)
    let unplanned ← selectUnplanned [Book, Author] pred (.key fun (b, _) => b.val.title)
    check' (planned.map key == unplanned.map key && planned.size == 1)
      "differential: planned select equals the reference"
    -- CAS update
    let alan' ← update alan { alan.val with age := 42 }
    check' (alan'.val.age == 42) "update applies"
    return (ada, alan)
  let (ada, alan) ← expectOk r "seed + queries"
  -- stale CAS: 'alan' still holds age 41 but the row now says 42
  expectErr (← withDb dbPath schema do discard <| update alan { alan.val with name := "A." })
    "stale" "CAS with stale snapshot"
  -- FK RESTRICT: alan is referenced by a book
  expectErr (← withDb dbPath schema do delete alan.id) "restricted" "delete referenced author"
  -- dangling Ref: inserting/updating toward a nonexistent row is
  -- missing_ref, not "referenced by other rows"
  expectErr (← withDb dbPath schema do discard <| insert Book ⟨"Ghost", ⟨99999⟩, none⟩)
    "missing_ref" "insert with dangling Ref"
  expectErr (← withDb dbPath schema do
      let books ← select [Book] (fun _ => true)
      match books[0]? with
      | some b => discard <| update b { b.val with author := ⟨99999⟩ }
      | none => throw (.sqlite "no book to update"))
    "missing_ref" "update to dangling Ref"
  -- delete of unreferenced row after removing its book, then notFound on re-delete
  let r ← withDb dbPath schema do
    let books ← select [Book] (fun b => b.val.author == ada.ref)
    for b in books do delete b.id
    delete ada.id
  discard <| expectOk r "cascade-by-hand delete"
  expectErr (← withDb dbPath schema do delete ada.id) "not_found" "double delete"
  -- reopen: fingerprint accepted, data persisted
  let names ← withDb dbPath schema do
    return (← select [Author] (fun _ => true) (.key (·.val.name))).map (·.val.name)
  check ((← expectOk names "reopen") == #["Alan"]) "persistence across open"
  -- fingerprint mismatch: same file, different schema
  expectErr (← withDb dbPath [Entity.spec Author] (pure ())) "schema_mismatch"
    "drifted schema must refuse to open"
where
  check' (condition : Bool) (message : String) : DbM Unit :=
    unless condition do throw (.sqlite s!"FAIL: {message}")

private def taskDbPath : System.FilePath := ".lake" / "leandb_test_tasks.sqlite"

private def testClosedEndToEnd : IO Unit := do
  if ← taskDbPath.pathExists then IO.FS.removeFile taskDbPath
  let r ← withDb taskDbPath [Entity.spec Todo] do
    discard <| insert Todo ⟨"write plan", .done⟩
    discard <| insert Todo ⟨"build engine", .inProgress⟩
    discard <| insert Todo ⟨"ship", .backlog⟩
    select [Todo] (fun t => t.val.status == .inProgress)
  let active ← expectOk r "closed-enum filter"
  check (active.map (·.val.title) == #["build engine"]) "match on closed world filters"
  -- the file itself refuses vocabulary violations (CHECK), even via raw SQL
  let db ← SQLite.open taskDbPath
  let raw : IO Unit := db.exec "INSERT INTO todo (title, status) VALUES ('rogue', 'cancelled')"
  match ← raw.toBaseIO with
  | .ok _ => throw <| IO.userError "FAIL: CHECK should reject unknown variant"
  | .error e =>
      match e with
      | .otherError 19 details =>
          check ((details.toLower.splitOn "check constraint").length == 2)
            s!"raw insert rejected by CHECK, got: {details}"
      | e => throw <| IO.userError s!"FAIL: expected constraint error 19, got: {e}"

private def dietDbPath : System.FilePath := ".lake" / "leandb_test_diet.sqlite"

/-- Differential: the parameter-split plans must agree with the unplanned
    reference for every diet, and with the hand-written expectation. -/
private def testParamSplitEndToEnd : IO Unit := do
  if ← dietDbPath.pathExists then IO.FS.removeFile dietDbPath
  let r ← withDb dietDbPath [Entity.spec Ingredient] do
    discard <| insert Ingredient ⟨"pork", .meat⟩
    discard <| insert Ingredient ⟨"salmon", .fish⟩
    discard <| insert Ingredient ⟨"tofu", .plant⟩
    discard <| insert Ingredient ⟨"lentils", .plant⟩
    let byName : SortBy (Stored Ingredient) := .key (·.val.name)
    let names (rows : Array (Stored Ingredient)) := rows.map (·.val.name)
    for d in ClosedEnum.all (α := Diet) do
      let allowed := fun (i : Stored Ingredient) => d.allows i.val.kind
      let planned ← select [Ingredient] allowed byName
      let reference ← selectUnplanned [Ingredient] allowed byName
      unless names planned == names reference do
        throw (.sqlite s!"FAIL: derived allows ({repr d}): planned {names planned} vs reference {names reference}")
      let forbidden := fun (i : Stored Ingredient) => !(d.allows i.val.kind)
      let plannedF ← select [Ingredient] forbidden byName
      let referenceF ← selectUnplanned [Ingredient] forbidden byName
      unless names plannedF == names referenceF do
        throw (.sqlite s!"FAIL: negated allows ({repr d}): planned {names plannedF} vs reference {names referenceF}")
      let paramFirst := fun (i : Stored Ingredient) => d.allowsParamFirst i.val.kind
      let plannedP ← select [Ingredient] paramFirst byName
      let referenceP ← selectUnplanned [Ingredient] paramFirst byName
      unless names plannedP == names referenceP do
        throw (.sqlite s!"FAIL: param-first allows ({repr d}): planned {names plannedP} vs reference {names referenceP}")
    let vegetarian ← select [Ingredient] (fun i => Diet.vegetarian.allows i.val.kind) byName
    let pescatarian ← select [Ingredient] (fun i => Diet.pescatarian.allows i.val.kind) byName
    let omnivore ← select [Ingredient] (fun i => Diet.omnivore.allows i.val.kind) byName
    return (names vegetarian, names pescatarian, names omnivore)
  let (veg, pesc, omni) ← expectOk r "diet queries"
  check (veg == #["lentils", "tofu"]) s!"vegetarian sees plants only, got {veg}"
  check (pesc == #["lentils", "salmon", "tofu"]) s!"pescatarian adds fish, got {pesc}"
  check (omni == #["lentils", "pork", "salmon", "tofu"]) s!"omnivore sees everything, got {omni}"

private def quantDbPath : System.FilePath := ".lake" / "leandb_test_quant.sqlite"

/-- LEP-0004 end to end: `selectP` over a SQLite file — the per-table path
    (a quantifier on table 0 rides the aliased single-table fetch), the
    joined path, and the re-check restoring what `approx` widened — each
    against the two-fetch computation and against `selectUnplanned` over
    the same snapshot. -/
private def testQuantifiersEndToEnd : IO Unit := do
  if ← quantDbPath.pathExists then IO.FS.removeFile quantDbPath
  let r ← withDb quantDbPath schema do
    let ada ← insert Author ⟨"Ada", 36⟩
    let alan ← insert Author ⟨"Alan", 41⟩
    discard <| insert Author ⟨"Grace", 29⟩
    discard <| insert Book ⟨"On Computable Numbers", alan.ref, some 4.5⟩
    discard <| insert Book ⟨"Notes on the Analytical Engine", ada.ref, none⟩
    discard <| insert Book ⟨"Unrated", alan.ref, none⟩
    let byName : SortBy (Stored Author) := .key (·.val.name)
    let names (rows : Array (Stored Author)) := rows.map (·.val.name)
    -- the two-fetch computation
    let allAuthors ← fetchAll Author
    let allBooks ← fetchAll Book
    let twoFetch (ok : Stored Book → Bool) : Array String :=
      (allAuthors.filter fun a => allBooks.all fun b => b.val.author != a.ref || ok b).map (·.val.name)
    -- forall, pushed whole: NOT EXISTS on the single-table fetch
    let allRated ← selectP [Author] allRatedP byName
    unless names allRated == #["Grace"] && names allRated == twoFetch (·.val.rating.isSome) do
      throw (.sqlite s!"FAIL: selectP forall: {names allRated}")
    let unrated ← selectP [Author] unratedP byName
    unless names unrated == #["Ada", "Alan"] do
      throw (.sqlite s!"FAIL: selectP exists: {names unrated}")
    -- an opaque body: SQL returns everyone, the re-check restores the answer
    let even ← selectP [Author] evenTitlesP byName
    unless names even == #["Ada", "Grace"]
        && names even == twoFetch (·.val.title.length % 2 == 0) do
      throw (.sqlite s!"FAIL: selectP with an opaque body: {names even}")
    let snap ← evenTitlesP.snapshot
    let reference ← selectUnplanned [Author] (evenTitlesP.denote snap) byName
    unless names even == names reference do
      throw (.sqlite s!"FAIL: differential over the same snapshot: {names even} vs {names reference}")
    -- the joined path: books whose author has another unrated book
    let other : Pred [Book, Author] :=
      .and (.eq2 (.here Book.Field.author) .eq (.there .id))
        (Pred.exists (.there .id) (.here Book.Field.author)
          (.and (.isNull (.here Book.Field.rating)) (.eq2 .id .ne (.there .id))))
    let joined ← selectP [Book, Author] other (.key fun (b, _) => b.val.title)
    let joinedRef ← selectUnplanned [Book, Author] (other.denote (← other.snapshot))
      (.key fun (b, _) => b.val.title)
    let titles := joined.map fun (b, a) => (b.val.title, a.val.name)
    unless titles == #[("On Computable Numbers", "Alan")]
        && titles == joinedRef.map (fun (b, a) => (b.val.title, a.val.name)) do
      throw (.sqlite s!"FAIL: joined selectP with a quantifier: {titles}")
    -- the log shows the quantifier and the residual
    let entries ← readLog 10
    let details := entries.map fun e => (e.getObjValAs? String "detail").toOption.getD ""
    unless details.any (fun d => d.startsWith "author | pushed: NOT EXISTS (SELECT 1 FROM \"book\" AS s0"
        && (d.splitOn "residual conjuncts: 0").length == 2) do
      throw (.sqlite s!"FAIL: log lacks the NOT EXISTS plan: {details}")
    unless details.any (fun d => (d.splitOn "AND 0), residual conjuncts: 1").length == 2) do
      throw (.sqlite s!"FAIL: log lacks the widened plan with residual 1: {details}")
  discard <| expectOk r "quantifier queries"

/-! ## Migrations (additive auto-apply, loud destruction, world rebuilds) -/

private def migDbPath : System.FilePath := ".lake" / "leandb_test_mig.sqlite"

private def col (name : String) (ty : SqlType) (nullable : Bool := false)
    (enum : Option (Array String) := none) (dflt : Option Col := none) : ColumnSpec :=
  { name, sqlType := ty, nullable, fkTable := none, enum, dflt }

private def testMigrations : IO Unit := do
  if ← migDbPath.pathExists then IO.FS.removeFile migDbPath
  let v1 : TableSpec := ⟨"author", #[col "name" .text], #[], none⟩
  let v2 : TableSpec := ⟨"author", #[col "name" .text, col "nick" .text (nullable := true)], #[], none⟩
  let vBad : TableSpec := ⟨"author", #[col "name" .text, col "age" .integer], #[], none⟩
  -- create at v1 and put a row in
  discard <| expectOk (← withDb migDbPath [v1] (pure ())) "create at v1"
  let db ← SQLite.open migDbPath
  db.exec "INSERT INTO author (name) VALUES ('Ada')"
  -- additive migration applies
  let r ← migrate migDbPath [v2] (apply := true)
  let (_, report?) ← expectOk r "additive migrate"
  check ((report?.map (·.applied)).getD [] == ["add column \"author\".\"nick\""])
    "add-column step applied"
  discard <| expectOk (← withDb migDbPath [v2] (pure ())) "open at v2 after migrate"
  -- NOT NULL addition is refused with guidance
  expectErr (← migrate migDbPath [vBad] (apply := true)) "migrate" "NOT NULL column refused"
  -- ...but a NOT NULL column WITH a default backfills existing rows
  let vDef : TableSpec := ⟨"author",
    #[col "name" .text, col "nick" .text (nullable := true),
      col "score" .integer (dflt := some (.int 7))], #[], none⟩
  discard <| expectOk (← migrate migDbPath [vDef] (apply := true)) "defaulted NOT NULL add"
  let dbv ← SQLite.open migDbPath
  let stv ← dbv.prepare "SELECT score FROM author WHERE name = 'Ada'"
  discard <| stv.step
  check ((← stv.columnInt64 0) == 7) "existing row took the declared default"
  -- destructive requires the flag
  expectErr (← migrate migDbPath [v1] (apply := true)) "migrate" "destructive needs flag"
  discard <| expectOk (← migrate migDbPath [v1] (apply := true) (allowDestructive := true))
    "destructive with flag"
  -- closed-world rebuild: grow, then a shrink that data refuses
  if ← migDbPath.pathExists then IO.FS.removeFile migDbPath
  let small := ⟨"todo", #[col "title" .text, col "status" .text (enum := some #["a", "b"])], #[], none⟩
  let grown : TableSpec :=
    ⟨"todo", #[col "title" .text, col "status" .text (enum := some #["a", "b", "c"])], #[], none⟩
  let shrunk : TableSpec := ⟨"todo", #[col "title" .text, col "status" .text (enum := some #["a"])], #[], none⟩
  discard <| expectOk (← withDb migDbPath [small] (pure ())) "create small world"
  let db2 ← SQLite.open migDbPath
  db2.exec "INSERT INTO todo (title, status) VALUES ('x', 'b')"
  let (_, rep) ← expectOk (← migrate migDbPath [grown] (apply := true)) "grow world"
  check (((rep.map (·.applied)).getD []).any (·.startsWith "rebuild")) "grow is a rebuild"
  let db3 ← SQLite.open migDbPath
  db3.exec "INSERT INTO todo (title, status) VALUES ('y', 'c')"   -- new CHECK admits 'c'
  -- shrink to just 'a': rows say 'b'/'c' → CHECK fails during copy → rolled back
  expectErr (← migrate migDbPath [shrunk] (apply := true)) "migrate"
    "world shrink refused by nonconforming data"
  let db4 ← SQLite.open migDbPath
  let stmt ← db4.prepare "SELECT count(*) FROM todo"
  discard <| stmt.step
  check ((← stmt.columnInt64 0) == 2) "rollback kept the data"
  -- Corrupt metadata is not an empty schema: migration must stop instead
  -- of blessing the live database with a new fingerprint.
  db4.exec "UPDATE _leandb_meta SET value = 'not-json' WHERE key = 'schema_json'"
  expectErr (← migrate migDbPath [grown] (apply := false)) "migrate"
    "invalid stored schema metadata must be reported"


/-! ## Migration error paths restore the session PRAGMAs (#71)

A failed migration must leave the session connection as it found it. The
live #71 scenario: a custom step commits the transaction away, so the
migration's own COMMIT fails ("no transaction is active") and the catch's
ROLLBACK fails the same way — the failure used to escape with
`foreign_keys=OFF` and `legacy_alter_table=ON` still in force. -/

private def migLeakDbPath : System.FilePath := ".lake" / "leandb_test_mig_leak.sqlite"

private def testMigrationErrorPragmas : IO Unit := do
  if ← migLeakDbPath.pathExists then IO.FS.removeFile migLeakDbPath
  let v1 : TableSpec := ⟨"author", #[col "name" .text], #[], none⟩
  let v2 : TableSpec := ⟨"author", #[col "name" .text, col "nick" .text (nullable := true)], #[], none⟩
  discard <| expectOk (← withDb migLeakDbPath [v1] (pure ())) "create v1"
  let conn ← expectOk (← openDbRaw migLeakDbPath) "reopen v1"
  let m : Migration :=
    { fromFingerprint := fingerprint [v1]
      toFingerprint := fingerprint [v2]
      snapshot := [v2]
      steps := [.custom "commit early" (fun c => c.raw.exec "COMMIT")] }
  expectErr (← m.applyOn conn [v1] (toVersion := 1) (allowDestructive := false) (backup := none))
    "migrate" "a commit-early custom step must fail the migration"
  let fk ← conn.raw.prepare "PRAGMA foreign_keys"
  discard <| fk.step
  check ((← fk.columnInt64 0) == 1)
    s!"foreign_keys restored after a failed migration (got {← fk.columnInt64 0})"
  let lat ← conn.raw.prepare "PRAGMA legacy_alter_table"
  discard <| lat.step
  check ((← lat.columnInt64 0) == 0) "legacy_alter_table restored after a failed migration"
  -- the failed ROLLBACK poisoned the connection (#72): later verbs refuse
  match ← (insert Author ⟨"Ada", 36⟩).run conn with
  | .error e =>
      check ((e.message.splitOn "poisoned").length > 1)
        s!"the refusal names the poison: {e.message}"
  | .ok _ => throw <| IO.userError "FAIL: a poisoned connection must refuse insert"


private def quoteDbPath : System.FilePath := ".lake" / "leandb_test_quote.sqlite"

private def testSqlQuoting : IO Unit := do
  if ← quoteDbPath.pathExists then IO.FS.removeFile quoteDbPath
  let quoted : TableSpec := ⟨"odd\"table",
    #[col "odd\"column" .text (enum := some #["it's"])], #[], none⟩
  discard <| expectOk (← withDb quoteDbPath [quoted] (pure ()))
    "quoted SQL identifiers and enum values"
  let db ← SQLite.open quoteDbPath
  db.exec "INSERT INTO \"odd\"\"table\" (\"odd\"\"column\") VALUES ('it''s')"

private def emptyDbPath : System.FilePath := ".lake" / "leandb_test_empty.sqlite"

private def testEmptyEntity : IO Unit := do
  if ← emptyDbPath.pathExists then IO.FS.removeFile emptyDbPath
  let stored ← expectOk (← withDb emptyDbPath [Entity.spec Marker] do
    let row ← insert Marker {}
    update row {}) "zero-field insert and update"
  check (stored.id.toInt64 == 1) "zero-field entity gets a row identity"
  discard <| expectOk (← withDb emptyDbPath [Entity.spec Marker] do delete stored.id)
    "zero-field delete"

private def blobDbPath : System.FilePath := ".lake" / "leandb_test_blob.sqlite"

/-- A BLOB is a decode failure like any other bad value: typed, and naming
    the column it came from. -/
private def expectBlobDecode (r : Except DbError Unit) (context : String) : IO Unit := do
  expectErr r "decode" context
  match r with
  | .error e =>
      check (e.message == "author.name: BLOB columns are not supported")
        s!"{context}: decode error names the table and field, got {e}"
  | .ok _ => pure ()

/-- Only raw SQL can plant a BLOB in a typed column, so the fixture goes in
    behind the typed layer — then every read path must refuse it the same
    way. -/
private def testBlobColumn : IO Unit := do
  if ← blobDbPath.pathExists then IO.FS.removeFile blobDbPath
  discard <| expectOk (← withDb blobDbPath schema do
    let a ← insert Author ⟨"Ada", 36⟩
    discard <| insert Book ⟨"Notes", a.ref, none⟩) "seed before planting a BLOB"
  let db ← SQLite.open blobDbPath
  db.exec "UPDATE author SET name = x'414243'"
  expectBlobDecode (← withDb blobDbPath schema do
    discard <| get (α := Author) ⟨1⟩) "get over a BLOB column"
  expectBlobDecode (← withDb blobDbPath schema do
    discard <| select [Author] (fun _ => true)) "unfiltered select over a BLOB column"
  expectBlobDecode (← withDb blobDbPath schema do
    discard <| select [Author] (fun a => a.val.age ≥ 1)) "filtered select over a BLOB column"
  expectBlobDecode (← withDb blobDbPath schema do
    discard <| select [Book, Author] (fun (b, a) => b.val.author == a.ref))
    "joined select over a BLOB column"

private def uniqDbPath : System.FilePath := ".lake" / "leandb_test_unique.sqlite"

/-- The `duplicate` classification depends on SQLite's message text (see
    `constraintError`); pin it so a re-wording fails here, not in the field. -/
private def testUniqueConstraint : IO Unit := do
  if ← uniqDbPath.pathExists then IO.FS.removeFile uniqDbPath
  discard <| expectOk (← withDb uniqDbPath schema do
    discard <| insert Author ⟨"Ada", 36⟩) "seed before the unique index"
  let db ← SQLite.open uniqDbPath
  db.exec "CREATE UNIQUE INDEX u_author_name ON author(name)"
  expectErr (← withDb uniqDbPath schema do discard <| insert Author ⟨"Ada", 41⟩)
    "duplicate" "uniqueness violation is typed, not a raw sqlite error"

/-- A column literally named `foreign key` — legal as the escaped Lean
    field «foreign key», and the one name that puts the FK classifier's
    bare substring inside a UNIQUE-violation message. -/
structure FkName where
  «foreign key» : String
  deriving Repr, LeanDb.Entity

private def fkDbPath : System.FilePath := ".lake" / "leandb_test_fk_name.sqlite"

/-- `constraintError` must match SQLite's full FK phrase, not any
    occurrence of "foreign key": a UNIQUE violation on the column above
    reads "UNIQUE constraint failed: fk_name.foreign key" and must stay
    `.duplicate`, not become `.missingRef`. -/
private def testConstraintClassify : IO Unit := do
  if ← fkDbPath.pathExists then IO.FS.removeFile fkDbPath
  discard <| expectOk (← withDb fkDbPath [Entity.spec FkName] do
    discard <| insert FkName ⟨"same"⟩) "seed before the unique index"
  let db ← SQLite.open fkDbPath
  db.exec "CREATE UNIQUE INDEX u_fk_name_fk ON \"fk_name\" (\"foreign key\")"
  expectErr (← withDb fkDbPath [Entity.spec FkName] do discard <| insert FkName ⟨"same"⟩)
    "duplicate" "a UNIQUE violation on «foreign key» is .duplicate, not .missingRef"
private def nanDbPath : System.FilePath := ".lake" / "leandb_test_nan.sqlite"

/-- A NaN Float has no SQLite representation: bound, it becomes NULL, so a
    NOT NULL REAL column failed with a misleading constraint error and a
    nullable one silently reads back `none`. The bind boundary refuses it
    by name instead. -/
private def testNanReal : IO Unit := do
  if ← nanDbPath.pathExists then IO.FS.removeFile nanDbPath
  let nan : Float := 0.0 / 0.0
  let r ← withDb nanDbPath schema do
    discard <| insert Author ⟨"Ada", 36⟩
    discard <| insert Book ⟨"NaN", ⟨1⟩, some nan⟩
  expectErr r "sqlite" "NaN into a REAL column is refused at the bind boundary"
  match r with
  | .error e =>
      check ((e.message.splitOn "NaN").length > 1) s!"the refusal names NaN, got {e.message}"
  | .ok _ => pure ()
  let count ← withDb nanDbPath schema do
    return (← select [Book] (fun _ => true)).size
  check ((← expectOk count "rows after the refused NaN write") == 0)
    "nothing was stored for the refused write"

private def testInfReal : IO Unit := do
  if ← nanDbPath.pathExists then IO.FS.removeFile nanDbPath
  -- the bind boundary refuses infinities like NaN (issue: Infinity
  -- binds, stores, and then leaves every JSON surface as the string
  -- "Infinity")
  let r ← withDb nanDbPath schema do
    discard <| insert Author ⟨"Ada", 36⟩
    discard <| insert Book ⟨"Inf", ⟨1⟩, some (1.0 / 0.0)⟩
  expectErr r "sqlite" "Infinity into a REAL column is refused at the bind boundary"
  -- the JSON decode boundary refuses non-finite REALs too (a raw 1e999
  -- overflows to inf; Lean renders non-finite floats as strings, so the
  -- column would stop being a REAL the moment it is read back)
  let realSpec := (Entity.spec Book).columns.getD 2 default
  check (((Col.fromJson realSpec (Lean.Json.num 1e999)).toOption.map (·.describe)) == none)
    "a JSON 1e999 for a REAL column is refused"
  check (((Col.fromJson realSpec (Lean.Json.str "Infinity")).isOk == false)
    && ((Col.fromJson realSpec (Lean.Json.str "-Infinity")).isOk == false))
    "the Infinity strings are not REALs"
  check (((fromCol (α := Float) (.real (1.0 / 0.0))).isOk == false)
    && ((fromCol (α := Float) (.real (0.0 / 0.0))).isOk == false))
    "the Float codec refuses non-finite stored values"


/-! ## Importer: what it reports as not carried (§5.3 — partial support is
fine, *silent* partiality is not). `planOf` is pure, so this drives it
over a hand-built schema rather than a database file. -/

section Importer
open LeanDb.Import

/-- A table whose DDL *looks* like it has UNIQUE and CHECK but does not, and
    which `PRAGMA index_list` correctly reports as index-free. -/
private def phantomTable : RawTable :=
  { name := "phantom"
    createSql :=
      "CREATE TABLE phantom (\n" ++
      "  id INTEGER PRIMARY KEY,\n" ++
      "  check_digit TEXT NOT NULL,          -- looks like CHECK but is not\n" ++
      "  unique_ref TEXT,                    -- looks like UNIQUE but is not\n" ++
      "  label TEXT NOT NULL DEFAULT 'UNIQUE and CHECK live here',\n" ++
      "  \"CHECK\" TEXT,\n" ++
      "  [unique] TEXT\n" ++
      "  /* a comment that says UNIQUE and CHECK */\n" ++
      ")"
    columns := #[
      { name := "id", declType := "INTEGER", notnull := true, pkIndex := 1,
        defaultSql := none },
      { name := "check_digit", declType := "TEXT", notnull := true,
        pkIndex := 0, defaultSql := none },
      { name := "unique_ref", declType := "TEXT", notnull := false,
        pkIndex := 0, defaultSql := none }]
    fks := #[]
    indexes := #[] }


/-- Real constraints: an inline `UNIQUE`, a named `CONSTRAINT ... CHECK`,
    an unnamed inline `CHECK`, and a table-level `UNIQUE (sku, qty)`. -/
private def realTable : RawTable :=
  { name := "real_constraints"
    createSql :=
      "CREATE TABLE real_constraints (\n" ++
      "  id INTEGER PRIMARY KEY,\n" ++
      "  sku TEXT NOT NULL UNIQUE,\n" ++
      "  qty INT NOT NULL CHECK (qty > 0),\n" ++
      "  grade TEXT,\n" ++
      "  CONSTRAINT grade_range CHECK (grade IN ('a','b')),\n" ++
      "  CONSTRAINT sku_qty_uq UNIQUE (sku, qty)\n" ++
      ")"
    columns := #[
      { name := "id", declType := "INTEGER", notnull := true, pkIndex := 1,
        defaultSql := none },
      { name := "sku", declType := "TEXT", notnull := true, pkIndex := 0,
        defaultSql := none },
      { name := "qty", declType := "INT", notnull := true, pkIndex := 0,
        defaultSql := none },
      { name := "grade", declType := "TEXT", notnull := false, pkIndex := 0,
        defaultSql := none }]
    fks := #[]
    indexes := #[
      { name := "uq_grade", isUnique := true, origin := "c",
        isPartial := false, columns := #[some "grade"] },
      { name := "sqlite_autoindex_real_constraints_2", isUnique := true,
        origin := "u", isPartial := false,
        columns := #[some "sku", some "qty"] },
      { name := "sqlite_autoindex_real_constraints_1", isUnique := true,
        origin := "u", isPartial := false, columns := #[some "sku"] }] }

private def testImportNotCarried : IO Unit := do
  let raw : RawSchema :=
    { tables := #[phantomTable, realTable], views := #[], triggers := #[],
      indexes := #["uq_grade"] }
  let plan := planOf "adv" "Adv" raw
  let names := plan.notCarried.map fun e => (e.kind, e.name)
  -- No phantom: a `check_digit` column, a `'UNIQUE and CHECK'` default, a
  -- `"CHECK"` identifier and a comment must not invent constraints.
  check (!names.contains ("unique constraint", "phantom"))
    "phantom table must not report a UNIQUE constraint"
  check (!names.contains ("check", "phantom"))
    "phantom table must not report a CHECK constraint"
  check (plan.notCarried.all fun e => !e.name.startsWith "phantom(")
    "phantom table must not report any UNIQUE constraint by columns"
  -- Real constraints are still reported, now named by column list.
  check (names.contains ("unique constraint", "real_constraints(sku)"))
    "inline UNIQUE is reported by column"
  check (names.contains ("unique constraint", "real_constraints(sku, qty)"))
    "table-level UNIQUE is reported by column list"
  -- `origin = "c"` is a CREATE INDEX: reported once, as an index.
  check (!names.contains ("unique constraint", "real_constraints(grade)"))
    "a CREATE UNIQUE INDEX is not double-reported as a UNIQUE constraint"
  check (names.contains ("index", "uq_grade")) "the unique index is reported"
  check ((plan.notCarried.find? fun e => e.name == "uq_grade").any fun e =>
      (e.reason.splitOn "UNIQUE").length > 1)
    "a UNIQUE index says so in its reason"
  -- CHECKs: the named one by name, the unnamed one counted on the table.
  check (names.contains ("check", "real_constraints.grade_range"))
    "a CONSTRAINT-named CHECK is reported by name"
  check ((plan.notCarried.find? fun e =>
      e.kind == "check" && e.name == "real_constraints").any fun e =>
      (e.reason.splitOn "1 unnamed").length > 1)
    "the unnamed CHECK is reported with a count"

/-- A column named `rec` (or a Lean modifier keyword) cannot become a
    field symbol: the derive would fail with an unattributed kernel or
    parser error. The importer skips it by name, like a BLOB. -/
private def testImportUnusableNames : IO Unit := do
  let t : RawTable :=
    { name := "widget"
      createSql := "CREATE TABLE widget (id INTEGER PRIMARY KEY, rec TEXT NOT NULL, safe TEXT)"
      columns := #[
        { name := "id", declType := "INTEGER", notnull := true, pkIndex := 1, defaultSql := none },
        { name := "rec", declType := "TEXT", notnull := true, pkIndex := 0, defaultSql := none },
        { name := "safe", declType := "TEXT", notnull := false, pkIndex := 0, defaultSql := none }]
      fks := #[]
      indexes := #[] }
  let plan := planOf "wn" "Wn" { tables := #[t], views := #[], triggers := #[], indexes := #[] }
  check ((plan.tables.map (·.table)) == #["widget"]) "the table still imports"
  let skipped := (plan.tables.find? (·.table == "widget")).map fun tp =>
    (tp.skippedColumns.map (·.1)).toList
  check (skipped == some ["rec"]) s!"rec is skipped by name, got {repr skipped}"
  check ((plan.tables.find? (·.table == "widget")).any fun tp =>
      (tp.skippedColumns.find? (·.1 == "rec")).any fun (_, r) =>
        (r.splitOn "field symbol").length > 1)
    "the skip reason says why"


/-- Issue #65: a SQLite declared type is interpolated into the generated
    Lean — and SQLite lets a quoted identifier carry arbitrary text. The
    payload below once closed the `Scalars.lean` doc comment and compiled
    as top-level Lean (`def Docbase.pwn : Nat := 137`). Generated Lean
    must now render only the normalized affinity; the raw type survives
    as inert data in `import-report.json` and `IMPORT.md`. -/
private def testImportHostileDeclType : IO Unit := do
  let payload := "x]-/ def pwn : Nat := 137 /-"
  let t : RawTable :=
    { name := "doc"
      createSql :=
        "CREATE TABLE doc (id INTEGER PRIMARY KEY, body \"x]-/ def pwn : Nat := 137 /-\")"
      columns := #[
        { name := "id", declType := "INTEGER", notnull := true, pkIndex := 1,
          defaultSql := none },
        { name := "body", declType := payload, notnull := false, pkIndex := 0,
          defaultSql := none }]
      fks := #[]
      indexes := #[] }
  let plan := planOf "docbase" "Docbase"
    { tables := #[t], views := #[], triggers := #[], indexes := #[] }
  -- The column still imports: a text newtype with the (bogus) declared type.
  let body := (plan.tables.find? (·.table == "doc")).bind fun tp =>
    tp.fields.find? (·.column == "body")
  check (body.any fun f => match f.mapping with | .newtype _ => true | _ => false)
    "the hostile column still imports as a text newtype"
  -- Generated Lean: no attacker code, no unbalanced comment, and only the
  -- affinity label where the declared type used to sit.
  let files := renderFiles plan "." "doc.db" "doc.db" "test"
  let some scalars := (files.find? (·.1 == "Docbase/Scalars.lean")).map (·.2)
    | throw <| IO.userError "FAIL: Scalars.lean was generated"
  check ((scalars.splitOn "def pwn").length == 1) "no injected declaration in Scalars.lean"
  check ((scalars.splitOn "137").length == 1) "no attacker tokens in Scalars.lean"
  check ((scalars.splitOn "]-/").length == 1) "no comment-closer payload in Scalars.lean"
  check ((scalars.splitOn "/-").length == (scalars.splitOn "-/").length)
    "the generated block comments stay balanced"
  check ((scalars.splitOn "(NUMERIC affinity). Identity validator").length > 1)
    "the doc comment carries the affinity, not the raw type"
  -- The raw declared type is still reported, as inert data.
  let some md := (files.find? (·.1 == "IMPORT.md")).map (·.2)
    | throw <| IO.userError "FAIL: IMPORT.md was generated"
  check ((md.splitOn payload).length > 1) "the raw declared type stays in IMPORT.md"
  let some json := (files.find? (·.1 == "import-report.json")).map (·.2)
    | throw <| IO.userError "FAIL: import-report.json was generated"
  check ((json.splitOn payload).length > 1) "the raw declared type stays in import-report.json"
  -- Normal types still read naturally.
  let clean : RawTable :=
    { name := "plain"
      createSql := "CREATE TABLE plain (id INTEGER PRIMARY KEY, note VARCHAR(20))"
      columns := #[
        { name := "id", declType := "INTEGER", notnull := true, pkIndex := 1,
          defaultSql := none },
        { name := "note", declType := "VARCHAR(20)", notnull := false, pkIndex := 0,
          defaultSql := none }]
      fks := #[]
      indexes := #[] }
  let plan2 := planOf "docbase" "Docbase"
    { tables := #[clean], views := #[], triggers := #[], indexes := #[] }
  let files2 := renderFiles plan2 "." "doc.db" "doc.db" "test"
  let some scalars2 := (files2.find? (·.1 == "Docbase/Scalars.lean")).map (·.2)
    | throw <| IO.userError "FAIL: Scalars.lean was generated for the clean table"
  check ((scalars2.splitOn "(TEXT affinity). Identity validator").length > 1)
    "a VARCHAR column reads as TEXT affinity"
  check ((scalars2.splitOn "VARCHAR(20)").length == 1)
    "even a benign declared type stays out of generated Lean"
/-- Issue #66, revisited against Lean v4.33.0: a column name can still be
    carried as a guillemet-quoted binder when only the bare spelling is a
    token (`suffices`, `using`, `forall`), is refused only when even the
    quoted binder clashes in the kernel (`mk`, `noConfusion`, `ctorIdx`),
    and words that were once refused wholesale but compile bare on this
    toolchain (`type`) come through as plain binders. Each refusal or
    quoting decision was verified by scratch-compiling the candidate as a
    structure field under `deriving LeanDb.Entity`. -/
private def testImportHostileNames : IO Unit := do
  let col (n : String) : RawColumn :=
    { name := n, declType := "TEXT", notnull := false, pkIndex := 0, defaultSql := none }
  let t : RawTable :=
    { name := "hostile"
      createSql :=
        "CREATE TABLE hostile (id INTEGER PRIMARY KEY, suffices TEXT, using TEXT, \
type TEXT, mk TEXT, noConfusion TEXT, ctorIdx TEXT, toCtorIdx TEXT, ok TEXT)"
      columns := #[
        { name := "id", declType := "INTEGER", notnull := true, pkIndex := 1,
          defaultSql := none },
        col "suffices", col "using", col "type", col "mk", col "noConfusion",
        col "ctorIdx", col "toCtorIdx", col "ok"]
      fks := #[]
      indexes := #[] }
  let plan := planOf "hn" "Hn" { tables := #[t], views := #[], triggers := #[], indexes := #[] }
  let some tp := plan.tables.find? (·.table == "hostile")
    | throw <| IO.userError "FAIL: hostile table planned"
  check ((tp.skippedColumns.map (·.1)).toList ==
      ["mk", "noConfusion", "ctorIdx", "toCtorIdx"])
    s!"only the kernel-clashing names are skipped, got {repr tp.skippedColumns.toList}"
  check (tp.skippedColumns.all fun (_, r) => (r.splitOn "kernel").length > 1)
    "each skip reason names the kernel collision"
  check ((tp.fields.map (·.column)).toList == ["suffices", "using", "type", "ok"])
    "token and ordinary names are still carried"
  let files := renderFiles plan "." "h.db" "h.db" "test"
  let some entities := (files.find? (·.1 == "Hn/Entities.lean")).map (·.2)
    | throw <| IO.userError "FAIL: Entities.lean was generated"
  for n in ["mk", "noConfusion", "ctorIdx", "toCtorIdx"] do
    check ((entities.splitOn n).length == 1)
      s!"Entities.lean never mentions refused name {n}"
  check ((entities.splitOn "  «suffices» : ").length > 1)
    "the token name suffices is emitted guillemet-quoted"
  check ((entities.splitOn "  «using» : ").length > 1)
    "the token name using is emitted guillemet-quoted"
  check ((entities.splitOn "  type : Option HostileType").length > 1)
    "type is emitted as a plain binder (no over-refusal, no over-quoting)"
  check ((entities.splitOn "  ok : Option HostileOk").length > 1)
    "the ordinary column is emitted as a plain identifier"

/-- Issue #67: `WITHOUT ROWID` is a token decision over `bareWords`, not
    a raw DDL substring — a string default containing the phrase must not
    exclude a perfectly importable rowid table, while a real WITHOUT
    ROWID table is still refused. -/
private def testImportWithoutRowidPhrase : IO Unit := do
  let phrase : RawTable :=
    { name := "note"
      createSql :=
        "CREATE TABLE note (\n" ++
        "  id INTEGER PRIMARY KEY,\n" ++
        "  tag TEXT DEFAULT 'WITHOUT ROWID' -- WITHOUT ROWID\n" ++
        ")"
      columns := #[
        { name := "id", declType := "INTEGER", notnull := true, pkIndex := 1,
          defaultSql := none },
        { name := "tag", declType := "TEXT", notnull := false, pkIndex := 0,
          defaultSql := some "'WITHOUT ROWID'" }]
      fks := #[]
      indexes := #[] }
  let real : RawTable :=
    { name := "w"
      createSql := "CREATE TABLE w (a TEXT) WITHOUT ROWID"
      columns := #[{ name := "a", declType := "TEXT", notnull := false,
                     pkIndex := 0, defaultSql := none }]
      fks := #[]
      indexes := #[] }
  let plan := planOf "wr" "Wr"
    { tables := #[phrase, real], views := #[], triggers := #[], indexes := #[] }
  check ((plan.tables.map (·.table)) == #["note"])
    "a string default containing the phrase does not exclude the table"
  let skipped := plan.skippedTables.filter (·.1 == "w")
  check (skipped.size == 1) "a real WITHOUT ROWID table is still skipped"
  check (skipped.any fun (_, r) => (r.splitOn "WITHOUT ROWID").length > 1)
    "the skip reason still says WITHOUT ROWID"

/-- Issue #68: a column targeted by two single-column foreign keys
    cannot carry a typed reference — a `Ref` points at only one parent,
    and typing the first silently lost the second. It is imported as
    Int64 with the targets named in `notCarried`; a single-FK column
    still types as `Ref`. -/
private def fkRow (fromCol toTable : String) (gid : Nat) : RawFk :=
  { groupId := gid, fromCol, toTable, toCol := some "id",
    onUpdate := "RESTRICT", onDelete := "RESTRICT", matchClause := "NONE" }

private def dualFkParent : RawTable :=
  { name := "parent"
    createSql := "CREATE TABLE parent (id INTEGER PRIMARY KEY, name TEXT)"
    columns := #[
      { name := "id", declType := "INTEGER", notnull := true, pkIndex := 1,
        defaultSql := none },
      { name := "name", declType := "TEXT", notnull := false, pkIndex := 0,
        defaultSql := none }]
    fks := #[]
    indexes := #[] }

private def dualFkOther : RawTable :=
  { name := "other"
    createSql := "CREATE TABLE other (id INTEGER PRIMARY KEY, tag TEXT)"
    columns := #[
      { name := "id", declType := "INTEGER", notnull := true, pkIndex := 1,
        defaultSql := none },
      { name := "tag", declType := "TEXT", notnull := false, pkIndex := 0,
        defaultSql := none }]
    fks := #[]
    indexes := #[] }

/-- The issue's dual_fk fixture: `pid` carries two single-column FKs. -/
private def dualFkTable : RawTable :=
  { name := "dual_fk"
    createSql :=
      "CREATE TABLE dual_fk (id INTEGER PRIMARY KEY, pid INTEGER, \
FOREIGN KEY (pid) REFERENCES parent(id), FOREIGN KEY (pid) REFERENCES other(id))"
    columns := #[
      { name := "id", declType := "INTEGER", notnull := true, pkIndex := 1,
        defaultSql := none },
      { name := "pid", declType := "INTEGER", notnull := false, pkIndex := 0,
        defaultSql := none }]
    fks := #[fkRow "pid" "parent" 0, fkRow "pid" "other" 1]
    indexes := #[] }

/-- A column with exactly one single-column FK keeps its typed `Ref`. -/
private def singleFkTable : RawTable :=
  { name := "single"
    createSql :=
      "CREATE TABLE single (id INTEGER PRIMARY KEY, pid INTEGER, \
FOREIGN KEY (pid) REFERENCES parent(id))"
    columns := #[
      { name := "id", declType := "INTEGER", notnull := true, pkIndex := 1,
        defaultSql := none },
      { name := "pid", declType := "INTEGER", notnull := false, pkIndex := 0,
        defaultSql := none }]
    fks := #[fkRow "pid" "parent" 0]
    indexes := #[] }

private def testImportDualFk : IO Unit := do
  let plan := planOf "df" "Df"
    { tables := #[dualFkParent, dualFkOther, dualFkTable, singleFkTable],
      views := #[], triggers := #[], indexes := #[] }
  let pid := (plan.tables.find? (·.table == "dual_fk")).bind fun tp =>
    tp.fields.find? (·.column == "pid")
  check (pid.any fun f => f.mapping == Mapping.int64)
    "the dual-FK column is imported as Int64, not Ref"
  check (pid.any fun f => f.notes.any fun n =>
      (n.splitOn "parent").length > 1 && (n.splitOn "other").length > 1)
    "the field note names both FK targets"
  let nc := plan.notCarried.filter fun e =>
    e.kind == "foreign-key" && e.name == "dual_fk.pid"
  check (nc.size == 1) "the untyped FKs are reported by name in notCarried"
  check (nc.any fun e =>
      (e.reason.splitOn "parent").length > 1 && (e.reason.splitOn "other").length > 1)
    "the notCarried reason names both targets"
  let spid := (plan.tables.find? (·.table == "single")).bind fun tp =>
    tp.fields.find? (·.column == "pid")
  check (spid.any fun f => f.mapping == Mapping.ref "parent" "Parent")
    "a single single-column FK still types the column as Ref"

 end Importer

/-! ## LEP-0003 B: JSON columns with a declared shape, derived columns -/

namespace Lep3

inductive Kind where
  | a | b
  deriving Repr, DecidableEq, LeanDb.ClosedEnum, Lean.ToJson, Lean.FromJson

/-- Recursive, named payloads. -/
inductive Tree where
  | leaf
  | node (l : Tree) (v : Nat) (r : Tree)
  deriving Repr, DecidableEq, LeanDb.DbJson

/-- A positional payload (anonymous binders → array encoding). -/
inductive Seg where
  | dot
  | seg : Nat → Nat → Seg
  deriving Repr, DecidableEq, LeanDb.DbJson

structure Point where
  x : Nat
  y : Nat := 0
  kind : Kind := .a
  tag : Option String := none
  path : List Tree := []
  deriving Repr, DecidableEq, LeanDb.DbJson

/-- `Point` plus a defaulted field: additive. -/

structure Widened where
  x : Nat
  y : Nat := 0
  kind : Kind := .a
  tag : Option String := none
  path : List Tree := []
  stride : Nat := 1
  deriving Repr, DecidableEq, LeanDb.DbJson

/-- `Point` minus `y`: not additive. -/
structure Narrowed where
  x : Nat
  kind : Kind := .a
  tag : Option String := none
  path : List Tree := []
  deriving Repr, DecidableEq, LeanDb.DbJson

/-- A nested default that depends on an earlier field. -/
structure Dep where
  a : Nat
  b : Nat := a + 1
  deriving Repr, DecidableEq, LeanDb.DbJson

instance : ColCodec Point :=
  ColCodec.json Point fun p => if p.x > 1000 then .error "x too large" else .ok p

structure Gadget where
  name : String
  shape : Point
  extra : Option Point
  deriving Repr, LeanDb.Entity

/-- `total` is derived: recomputed on write, checked on read. -/
structure LineItem where
  qty : Nat
  price : Nat
  total : Nat := derived (qty * price)
  deriving Repr, LeanDb.Entity

private def pj (s : String) : IO Lean.Json :=
  match Lean.Json.parse s with
  | .ok j => pure j
  | .error e => throw <| IO.userError s!"FAIL: bad test JSON: {e}"

private def treeShape := "Tree(leaf|node{l:Tree,v:Nat,r:Tree})"
private def pointShape := s!"Point\{x:Nat,y:Nat=,kind:<a|b>=,tag:String?=,path:[{treeShape}]=}"

private def testDbJson : IO Unit := do
  -- Lean's encoding, byte for byte: objects with sorted keys, tagged constructors
  let p : Point := { x := 1, path := [.node .leaf 2 .leaf] }
  check ((Lean.toJson p).compress ==
      "{\"kind\":\"a\",\"path\":[{\"node\":{\"l\":\"leaf\",\"r\":\"leaf\",\"v\":2}}],\"tag\":null,\"x\":1,\"y\":0}")
    s!"DbJson encodes like Lean's derive, got {(Lean.toJson p).compress}"
  check ((Lean.toJson (Seg.seg 1 2)).compress == "{\"seg\":[1,2]}") "positional payload is an array"
  check ((Lean.toJson Seg.dot).compress == "\"dot\"") "payload-free constructor is a string"
  -- round trips, recursion included
  let t : Tree := .node (.node .leaf 1 .leaf) 2 (.node .leaf 3 (.node .leaf 4 .leaf))
  check ((Lean.fromJson? (Lean.toJson t) : Except String Tree).toOption == some t) "recursive round trip"
  check ((Lean.fromJson? (Lean.toJson (Seg.seg 7 8)) : Except String Seg).toOption == some (.seg 7 8)) "positional round trip"
  check ((Lean.fromJson? (Lean.toJson p) : Except String Point).toOption == some p) "structure round trip"
  -- the point of B1: an omitted field with a default takes the default
  check ((Lean.fromJson? (← pj "{\"x\":3}") : Except String Point).toOption ==
      some { x := 3, y := 0, kind := .a, tag := none, path := [] })
    "omitted defaulted fields take their defaults"
  check ((Lean.fromJson? (← pj "{\"x\":3,\"y\":9,\"kind\":\"b\",\"tag\":\"t\"}") : Except String Point).toOption ==
      some { x := 3, y := 9, kind := .b, tag := some "t", path := [] })
    "supplied fields override defaults"
  check ((Lean.fromJson? (← pj "{\"a\":3}") : Except String Dep).toOption == some { a := 3, b := 4 })
    "a nested default may depend on an earlier field"
  -- a missing field WITHOUT a default is still an error, named like Lean names it
  match (Lean.fromJson? (← pj "{\"y\":1}") : Except String Point) with
  | .error m => check ((m.splitOn "Lep3.Point.x").length > 1) s!"missing required field named, got {m}"
  | .ok _ => throw <| IO.userError "FAIL: missing required field accepted"
  match (Lean.fromJson? (← pj "{\"nope\":1}") : Except String Tree) with
  | .error _ => pure ()
  | .ok _ => throw <| IO.userError "FAIL: unknown constructor accepted"
  -- shapes: canonical, deterministic, closed enums by variant list
  check (JsonShape.shape Tree == treeShape) s!"Tree shape, got {JsonShape.shape Tree}"
  check (JsonShape.shape Seg == "Seg(dot|seg[Nat,Nat])") s!"Seg shape, got {JsonShape.shape Seg}"
  check (JsonShape.shape Point == pointShape) s!"Point shape, got {JsonShape.shape Point}"
  check (JsonShape.shape Dep == "Dep{a:Nat,b:Nat=}") s!"Dep shape, got {JsonShape.shape Dep}"
  check (JsonShape.shape (List (Option (Nat × String))) == "[(Nat,String)?]") "container shapes"
  -- the codec: TEXT, compressed JSON, validated
  check ((fromCol (toCol p) : Except String Point).toOption == some p) "ColCodec.json round trip"
  check ((toCol p) matches Col.text _) "ColCodec.json stores TEXT"
  check ((fromCol (toCol ({ x := 2000 } : Point)) : Except String Point) matches .error _)
    "ColCodec.json decodes through the validator"

private def testShapedColumns : IO Unit := do
  let cols := Entity.columns Gadget
  check (cols.map (·.shape) == #[none, some pointShape, some pointShape])
    s!"JSON columns carry their shape (Option lifts it), scalars none; got {repr (cols.map (·.shape))}"
  check (cols.map (·.sqlType) == #[.text, .text, .text]) "JSON columns are TEXT"
  check ((cols.getD 2 default).nullable) "Option JSON column is nullable"
  -- DDL does not mention the shape; the fingerprint does
  let ddl := (Entity.spec Gadget).ddl
  check (ddl == "CREATE TABLE IF NOT EXISTS \"gadget\" (id INTEGER PRIMARY KEY AUTOINCREMENT, \"name\" TEXT NOT NULL, \"shape\" TEXT NOT NULL, \"extra\" TEXT)")
    s!"shape is not DDL, got {ddl}"
  let shapeless : TableSpec := ⟨"gadget", cols.map fun c => { c with shape := none }, #[], none⟩
  check (fingerprint [shapeless] == toString (hash shapeless.ddl))
    "a shape-less schema fingerprints exactly its DDL, as before B2"
  check (fingerprint [Entity.spec Author] == toString (hash (Entity.spec Author).ddl))
    "pre-existing schemas are unchanged by B2"
  check (fingerprint [Entity.spec Gadget] != fingerprint [shapeless])
    "the shape is part of the fingerprint"
  -- schema_json carries the shape and round-trips it byte for byte
  for c in cols do
    check ((ColumnSpec.fromJson? c.toJson).toOption == some c) s!"ColumnSpec JSON round trip for {c.name}"
  check ((specsFromJson? (specsToJson [Entity.spec Gadget])).toOption == some [Entity.spec Gadget])
    "schema JSON round trip with shapes"
  check (((Entity.spec Gadget).toJson.compress.splitOn "\"shape\":\"Point{").length == 3)
    "schema JSON shows the shape on both JSON columns"

private def reshaped (shape : String) : TableSpec :=
  ⟨"gadget", (Entity.columns Gadget).map fun c =>
    if c.name == "shape" then { c with shape := some shape } else c, #[], none⟩

private def shapeDbPath : System.FilePath := ".lake" / "leandb_test_shape.sqlite"

private def testShapeMigration : IO Unit := do
  let old := Entity.spec Gadget
  -- additive with defaults: a restamp step, no SQL
  match planMigration [old] [reshaped (JsonShape.shape Widened)] with
  | .ok plan =>
      check (plan.steps.map (·.describe) == ["restamp shape of \"gadget\".\"shape\""])
        s!"field added with a default → restamp, got {plan.steps.map (·.describe)}"
      check (plan.steps.all fun s => s.sql.isEmpty && !s.destructive) "restamp has no SQL and is not destructive"
  | .error e => throw <| IO.userError s!"FAIL: additive shape change refused: {e}"
  -- constructor added, variant added: still additive
  match planMigration [old] [reshaped (pointShape.replace "node{l:Tree,v:Nat,r:Tree})" "node{l:Tree,v:Nat,r:Tree}|twig)")] with
  | .ok plan => check (plan.steps.length == 1) "constructor added → restamp"
  | .error e => throw <| IO.userError s!"FAIL: added constructor refused: {e}"
  match planMigration [old] [reshaped (pointShape.replace "<a|b>" "<a|b|c>")] with
  | .ok plan => check (plan.steps.length == 1) "variant added → restamp"
  | .error e => throw <| IO.userError s!"FAIL: added variant refused: {e}"
  -- a field removed: refused, naming table, column and field
  match planMigration [old] [reshaped (JsonShape.shape Narrowed)] with
  | .ok _ => throw <| IO.userError "FAIL: field removal was not refused"
  | .error e =>
      check ((e.splitOn "field `y` removed from `Point`").length == 2 &&
             (e.splitOn "\"gadget\"").length == 2 && (e.splitOn "\"shape\"").length == 2 &&
             (e.splitOn "typed value transformation").length == 2)
        s!"refusal names the field, got {e}"
  -- a field added WITHOUT a default: refused
  match planMigration [old] [reshaped (pointShape.replace "x:Nat," "x:Nat,z:Nat,")] with
  | .ok _ => throw <| IO.userError "FAIL: undefaulted field addition was not refused"
  | .error e =>
      check ((e.splitOn "field `z` added to `Point` without a default").length == 2)
        s!"refusal names the undefaulted field, got {e}"
  -- a constructor renamed inside a nested type: refused
  match planMigration [old] [reshaped (pointShape.replace "node{" "branch{")] with
  | .ok _ => throw <| IO.userError "FAIL: constructor rename was not refused"
  | .error e =>
      check ((e.splitOn "constructor `node` renamed/removed from `Tree`").length == 2)
        s!"refusal names the constructor, got {e}"
  -- a nested closed world shrunk: refused
  match planMigration [old] [reshaped (pointShape.replace "<a|b>" "<a>")] with
  | .ok _ => throw <| IO.userError "FAIL: shrunk nested enum was not refused"
  | .error e => check ((e.splitOn "variant `b` removed").length == 2) s!"refusal names the variant, got {e}"
  -- a field retyped: refused
  match planMigration [old] [reshaped (pointShape.replace "x:Nat" "x:String")] with
  | .ok _ => throw <| IO.userError "FAIL: retyped field was not refused"
  | .error e =>
      check ((e.splitOn "type changed from `Nat` to `String`").length == 2)
        s!"refusal names the type change, got {e}"
  -- shape declared where the stored schema had none: nothing to compare, restamp
  let unshaped : TableSpec := ⟨"gadget", (Entity.columns Gadget).map fun c => { c with shape := none }, #[], none⟩
  match planMigration [unshaped] [old] with
  | .ok plan =>
      check (plan.steps.length == 2 && plan.steps.all (· matches .restampShape ..))
        "a newly declared shape restamps"
  | .error e => throw <| IO.userError s!"FAIL: newly declared shape refused: {e}"
  -- end to end: the restamp is journaled and moves the fingerprint; the old
  -- code then sees a mismatch at open, the refusal leaves the file untouched
  if ← shapeDbPath.pathExists then IO.FS.removeFile shapeDbPath
  discard <| expectOk (← withDb shapeDbPath [old] do
    discard <| insert Gadget ⟨"g", { x := 1 }, none⟩) "create at the Point shape"
  let widened := reshaped (JsonShape.shape Widened)
  let (_, report?) ← expectOk (← migrate shapeDbPath [widened] (apply := true)) "restamp migrate"
  check ((report?.map (·.applied)).getD [] == ["restamp shape of \"gadget\".\"shape\""])
    "restamp step applied and reported"
  check ((report?.map (·.fingerprint)) == some (fingerprint [widened])) "fingerprint moved to the new shape"
  expectErr (← withDb shapeDbPath [old] (pure ())) "schema_mismatch" "old shape refused at open (exit 4)"
  discard <| expectOk (← withDb shapeDbPath [widened] (pure ())) "new shape opens"
  let db ← SQLite.open shapeDbPath
  let stmt ← db.prepare "SELECT steps FROM _leandb_migrations ORDER BY rowid DESC LIMIT 1"
  discard <| stmt.step
  check (((← stmt.columnText 0).splitOn "restamp shape").length == 2) "restamp is journaled"
  expectErr (← migrate shapeDbPath [reshaped (JsonShape.shape Narrowed)] (apply := true)) "migrate"
    "field removal refused on a live instance"
  discard <| expectOk (← withDb shapeDbPath [widened] (pure ())) "refusal left the instance at the widened shape"

private def itemDbPath : System.FilePath := ".lake" / "leandb_test_derived.sqlite"

private def testDerivedColumns : IO Unit := do
  check ((Entity.fields (α := LineItem)).map Entity.isDerived == #[false, false, true])
    "the derived field is marked"
  check ((Entity.columns LineItem).map (·.dflt) == #[none, none, none])
    "a derived column has no reified DEFAULT"
  -- encode recomputes; the supplied value is ignored
  check (Entity.encode ({ qty := 2, price := 5, total := 999 } : LineItem) == #[.int 2, .int 5, .int 10])
    "encode recomputes the derived column"
  -- decode checks
  check ((Entity.decode #[.int 2, .int 5, .int 10] : Except DbError LineItem).isOk) "agreeing row decodes"
  match (Entity.decode #[.int 2, .int 5, .int 11] : Except DbError LineItem) with
  | .error (.decode "line_item" "total" m) => check (m == "derived column disagrees with its source") s!"decode message, got {m}"
  | .error e => throw <| IO.userError s!"FAIL: wrong error for a disagreeing derived column: {e}"
  | .ok _ => throw <| IO.userError "FAIL: disagreeing derived column decoded"
  -- JSON may omit it, a supplied value is ignored, a merge recomputes
  let r1 ← expectOk (rowOfJson LineItem (← pj "{\"qty\":3,\"price\":4}")) "rowOfJson without the derived field"
  check (r1.total == 12) "rowOfJson computes the derived field"
  let r2 ← expectOk (rowOfJson LineItem (← pj "{\"qty\":3,\"price\":4,\"total\":7}")) "rowOfJson with a lying derived field"
  check (r2.total == 12) "rowOfJson ignores a supplied derived value"
  let r3 ← expectOk (rowMergeJson LineItem r1 (← pj "{\"qty\":10}")) "rowMergeJson of a source"
  check (r3.total == 40) "rowMergeJson recomputes rather than keeps the stale value"
  -- end to end: a write through LeanDB cannot desynchronize; a raw write is caught on read
  if ← itemDbPath.pathExists then IO.FS.removeFile itemDbPath
  -- (`insert`/`update` hand back the value they were given; what the row
  -- holds is what a read returns)
  let stored ← expectOk (← withDb itemDbPath [Entity.spec LineItem] do
    let s ← insert LineItem { qty := 2, price := 5, total := 0 }
    discard <| update s { s.val with qty := 3 }
    fetchAll LineItem) "insert + update"
  check (stored.map (·.val.total) == #[15]) s!"stored derived value follows its sources, got {stored.map (·.val.total)}"
  let db ← SQLite.open itemDbPath
  db.exec "UPDATE line_item SET total = 99"
  match ← withDb itemDbPath [Entity.spec LineItem] (fetchAll LineItem) with
  | .error (.decode "line_item" "total" _) => pure ()
  | .error e => throw <| IO.userError s!"FAIL: raw-SQL desync: wrong error {e}"
  | .ok _ => throw <| IO.userError "FAIL: raw-SQL desync of a derived column was read back"

def run : IO Unit := do
  testDbJson
  testShapedColumns
  testShapeMigration
  testDerivedColumns

end Lep3

/-! ## LEP-0003 A: `EnumSet` — a set over a closed world as an INTEGER bitmask -/

namespace EnumSetA

inductive Tri where
  | x | y | z
  deriving Repr, DecidableEq, LeanDb.ClosedEnum

structure Tagged where
  name : String
  kind : Tri
  tags : EnumSet Tri
  deriving Repr, LeanDb.Entity

/-- A world of 63 names — one more than an `EnumSet` column admits. The
    instance is deliberately incoherent (one constructor, 63 names): only
    its `variants` count matters to the refusal. -/
inductive Big where
  | only
  deriving Repr, DecidableEq

instance : ClosedEnum Big where
  variants := (Array.range 63).map fun k => s!"v{k}"
  all := #[.only]
  encodeName _ := "v0"
  decodeName _ := some .only

private def bitPlan : PlanFor (ts := [Tagged]) (fun (t : Stored Tagged) => t.val.tags.contains .y) := by
  leandb_plan
private def notBitPlan : PlanFor (ts := [Tagged]) (fun (t : Stored Tagged) => !(t.val.tags.contains .y)) := by
  leandb_plan
private def paramBitPlan (a : Tri) : PlanFor (ts := [Tagged]) (fun (t : Stored Tagged) => t.val.tags.contains a) := by
  leandb_plan
private def memPlan : PlanFor (ts := [Tagged]) (fun (t : Stored Tagged) => Tri.z ∈ t.val.tags) := by
  leandb_plan
/-- The member is a closed-enum *column*: the case split on `kind` leaves a
    bit test per constructor. -/
private def colBitPlan : PlanFor (ts := [Tagged]) (fun (t : Stored Tagged) => t.val.tags.contains t.val.kind) := by
  leandb_plan
private def mixedPlan : PlanFor (ts := [Tagged]) (fun (t : Stored Tagged) =>
    t.val.tags.contains .x && t.val.name != "skip") := by leandb_plan

private def pj (s : String) : IO Lean.Json :=
  match Lean.Json.parse s with
  | .ok j => pure j
  | .error e => throw <| IO.userError s!"FAIL: bad test JSON: {e}"

private def tagsSpec : ColumnSpec := (Entity.columns Tagged).getD 2 default

private def testCodec : IO Unit := do
  let s : EnumSet Tri := .ofList [.z, .x]
  check (s.contains .x && !s.contains .y && s.contains .z) "contains"
  check (s.toList == [.x, .z] && s.names == ["x", "z"] && s.size == 2) "toList in declaration order"
  check ((s.insert .y).bits == 7 && s.erase .x == EnumSet.ofList [.z] && s.erase .y == s) "insert/erase"
  check (EnumSet.mask Tri == 7 && (EnumSet.full : EnumSet Tri).toList == [.x, .y, .z]) "mask and full"
  check (EnumSet.bitOf Tri.y == 2 && EnumSet.index Tri.z == 2) "the bit is the declaration index"
  check (decide (Tri.x ∈ s) && !decide (Tri.y ∈ s)) "Membership"
  check (enumSetMask 0 == 0 && enumSetMask 62 == 4611686018427387903) "enumSetMask"
  check (roundtrip s && roundtrip (EnumSet.empty : EnumSet Tri) && roundtrip (EnumSet.full : EnumSet Tri))
    "codec round trips: a set, the empty set, the full set"
  check (toCol s == .int 5 && toCol (EnumSet.empty : EnumSet Tri) == .int 0) "stored as the bitmask"
  match (fromCol (.int 8) : Except String (EnumSet Tri)) with
  | .error m => check (m == "bit 3 is not in the closed world (3 variants)") s!"stray bit message, got {m}"
  | .ok _ => throw <| IO.userError "FAIL: a stray bit decoded"
  check ((fromCol (.int (-1)) : Except String (EnumSet Tri)).isOk == false) "a negative mask is refused"
  check ((fromCol (.text "x") : Except String (EnumSet Tri)).isOk == false) "TEXT is refused"
  -- a world of more than 62 variants: refused by the codec and by validateSchema
  match (fromCol (.int 0) : Except String (EnumSet Big)) with
  | .error m => check (m == "closed world has 63 variants; EnumSet supports at most 62") s!"63-variant message, got {m}"
  | .ok _ => throw <| IO.userError "FAIL: a 63-variant world decoded"
  expectErr (validateSchema [⟨"big", #[columnSpec "s" (EnumSet Big)], #[], none⟩]) "schema"
    "a 63-variant EnumSet column is refused by validateSchema"
  check ((validateSchema [Entity.spec Tagged]).isOk) "a 3-variant world is fine"
  -- the column spec and its DDL
  check (tagsSpec.enumSet == some #["x", "y", "z"] && tagsSpec.enum == none && tagsSpec.sqlType == .integer
    && tagsSpec.shape == none) s!"tags spec carries enumSet and nothing else, got {repr tagsSpec}"
  check ((Entity.spec Tagged).ddl ==
      "CREATE TABLE IF NOT EXISTS \"tagged\" (id INTEGER PRIMARY KEY AUTOINCREMENT, \"name\" TEXT NOT NULL, \"kind\" TEXT NOT NULL CHECK (\"kind\" IN ('x', 'y', 'z')), \"tags\" INTEGER NOT NULL CHECK ((\"tags\" & ~7) = 0))")
    s!"tagged DDL golden, got {(Entity.spec Tagged).ddl}"
  -- the fingerprint hashes the names: a rename leaves the DDL alone but not the fingerprint
  let renamed : TableSpec := ⟨"tagged", (Entity.columns Tagged).map fun c =>
    if c.name == "tags" then { c with enumSet := some #["x", "y", "w"] } else c, #[], none⟩
  check (renamed.ddl == (Entity.spec Tagged).ddl) "a renamed variant has the same DDL"
  check (fingerprint [renamed] != fingerprint [Entity.spec Tagged]) "…and a different fingerprint"
  -- an Option (EnumSet _) column is nullable and keeps the world
  let optSpec := columnSpec "o" (Option (EnumSet Tri))
  check (optSpec.nullable && optSpec.enumSet == some #["x", "y", "z"]) "Option lifts enumSet"

private def testJson : IO Unit := do
  let row : Stored Tagged := ⟨⟨1⟩, ⟨"a", .x, .ofList [.x, .z]⟩⟩
  check ((rowJson Tagged row).compress == "{\"id\":1,\"kind\":\"x\",\"name\":\"a\",\"tags\":[\"x\",\"z\"]}")
    s!"row JSON renders the set as names, got {(rowJson Tagged row).compress}"
  let r1 ← expectOk (rowOfJson Tagged (← pj "{\"name\":\"a\",\"kind\":\"y\",\"tags\":[\"z\",\"x\"]}")) "array of names"
  check (r1.tags == EnumSet.ofList [.x, .z]) "names decode to bits"
  let r2 ← expectOk (rowOfJson Tagged (← pj "{\"name\":\"a\",\"kind\":\"y\",\"tags\":5}")) "bare bitmask"
  check (r2.tags.bits == 5) "the bare bitmask is accepted on input"
  let r3 ← expectOk (rowOfJson Tagged (← pj "{\"name\":\"a\",\"kind\":\"y\",\"tags\":[]}")) "empty array"
  check (r3.tags == .empty) "the empty array is the empty set"
  match rowOfJson Tagged (← pj "{\"name\":\"a\",\"kind\":\"y\",\"tags\":[\"x\",\"w\"]}") with
  | .error (.decode "tagged" "tags" m) =>
      check (m == "tags: \"w\" is not in the closed world #[x, y, z]") s!"unknown name is refused by name, got {m}"
  | .error e => throw <| IO.userError s!"FAIL: unknown name: wrong error {e}"
  | .ok _ => throw <| IO.userError "FAIL: an unknown variant name was accepted"
  match rowOfJson Tagged (← pj "{\"name\":\"a\",\"kind\":\"y\",\"tags\":8}") with
  | .error (.decode "tagged" "tags" _) => pure ()
  | .error e => throw <| IO.userError s!"FAIL: stray bit via JSON: wrong error {e}"
  | .ok _ => throw <| IO.userError "FAIL: a stray bit was accepted through JSON"
  check ((rowOfJson Tagged (← pj "{\"name\":\"a\",\"kind\":\"y\",\"tags\":true}")).isOk == false)
    "a boolean is not a set"
  let r4 ← expectOk (rowMergeJson Tagged r1 (← pj "{\"tags\":[\"y\"]}")) "merge"
  check (r4.tags == EnumSet.ofList [.y] && r4.name == "a") "rowMergeJson replaces the set"
  -- schema JSON carries enumSet and round-trips it
  let spec := Entity.spec Tagged
  check (((tagsSpec.toJson.getObjVal? "enumSet").toOption.bind (·.getArr?.toOption)).map
      (·.filterMap (·.getStr?.toOption)) == some #["x", "y", "z"])
    "schema JSON carries enumSet"
  match specsFromJson? (specsToJson [spec]) with
  | .ok [s'] => check (s' == spec) "schema JSON round-trips the enumSet column"
  | .ok _ => throw <| IO.userError "FAIL: schema JSON round trip lost a table"
  | .error e => throw <| IO.userError s!"FAIL: schema JSON round trip: {e}"

private def testPred : IO Unit := do
  let p : Pred [Tagged] := .bit (.here Tagged.Field.tags) Tri.y true
  check (p.renderT == ("((t0.\"tags\" & ?) != 0)", #[.int 2])) s!"bit render, got {repr p.renderT}"
  check (p.neg.renderT == ("((t0.\"tags\" & ?) = 0)", #[.int 2])) s!"negated bit render, got {repr p.neg.renderT}"
  check (p.neg.neg.renderT == p.renderT) "neg is an involution on bit"
  let row : Stored Tagged := ⟨⟨1⟩, ⟨"a", .x, .ofList [.y]⟩⟩
  let other : Stored Tagged := ⟨⟨2⟩, ⟨"b", .x, .ofList [.x]⟩⟩
  check (p.denote .empty row && !(p.denote .empty other)) "bit denotes contains"
  check (!(p.neg.denote .empty row) && p.neg.denote .empty other) "negated bit denotes the complement"
  check (p.residuals == 0 && p.tables == [0] && !p.hasJoin && p.approx.renderT == p.renderT && p.size == 1)
    "bit is a pushed leaf"
  check (p.describe == "pushed: ((t0.\"tags\" & ?) != 0), residual conjuncts: 0") s!"describe, got {p.describe}"
  -- the tactic
  checkPlan bitPlan "((t0.\"tags\" & ?) != 0)" #[.int 2] 0 "contains pushes as a bit test"
  checkPlan notBitPlan "((t0.\"tags\" & ?) = 0)" #[.int 2] 0 "negated contains flips the test"
  checkPlan (paramBitPlan .z) "((t0.\"tags\" & ?) != 0)" #[.int 4] 0 "a captured parameter is the bit"
  checkPlan memPlan "((t0.\"tags\" & ?) != 0)" #[.int 4] 0 "∈ goes through the Membership instance"
  checkPlan mixedPlan "(((t0.\"tags\" & ?) != 0) AND t0.\"name\" IS NOT ?)" #[.int 1, .text "skip"] 0
    "bit test inside a conjunction"
  checkPlan colBitPlan
    "(((t0.\"kind\" IS ? AND ((t0.\"tags\" & ?) != 0)) OR (t0.\"kind\" IS ? AND ((t0.\"tags\" & ?) != 0))) OR (t0.\"kind\" IS ? AND ((t0.\"tags\" & ?) != 0)))"
    #[.text "x", .int 1, .text "y", .int 2, .text "z", .int 4] 0
    "a closed-enum column as the member splits on its world"

private def dbPath : System.FilePath := ".lake" / "leandb_test_enumset.sqlite"

private def testEndToEnd : IO Unit := do
  if ← dbPath.pathExists then IO.FS.removeFile dbPath
  let r ← withDb dbPath [Entity.spec Tagged] do
    discard <| insert Tagged ⟨"a", .x, .ofList [.x]⟩
    discard <| insert Tagged ⟨"b", .y, .ofList [.x, .y]⟩
    discard <| insert Tagged ⟨"c", .z, .ofList [.y, .z]⟩
    discard <| insert Tagged ⟨"d", .z, .empty⟩
    discard <| insert Tagged ⟨"e", .x, .full⟩
    let byName : SortBy (Stored Tagged) := .key (·.val.name)
    let names (rows : Array (Stored Tagged)) := rows.map (·.val.name)
    let differential (label : String) (f : Stored Tagged → Bool) : DbM Unit := do
      let planned ← select [Tagged] f byName
      let reference ← selectUnplanned [Tagged] f byName
      unless names planned == names reference do
        throw (.sqlite s!"FAIL: {label}: planned {names planned} vs reference {names reference}")
    for a in ClosedEnum.all (α := Tri) do
      differential s!"contains {repr a}" fun t => t.val.tags.contains a
      differential s!"not contains {repr a}" fun t => !(t.val.tags.contains a)
      differential s!"{repr a} ∈" fun t => a ∈ t.val.tags
    differential "contains own kind" fun t => t.val.tags.contains t.val.kind
    differential "contains x and not y" fun t => t.val.tags.contains .x && !(t.val.tags.contains .y)
    let ys ← select [Tagged] (fun t => t.val.tags.contains .y) byName
    let own ← select [Tagged] (fun t => t.val.tags.contains t.val.kind) byName
    let mem ← select [Tagged] (fun t => Tri.z ∈ t.val.tags) byName
    let none' ← select [Tagged] (fun t => !(t.val.tags.contains .x) && !(t.val.tags.contains .z)) byName
    let log ← readLog 1
    return (names ys, names own, names mem, names none', log)
  let (ys, own, mem, none', log) ← expectOk r "enum-set queries"
  check (ys == #["b", "c", "e"]) s!"contains y, got {ys}"
  check (own == #["a", "b", "c", "e"]) s!"contains own kind, got {own}"
  check (mem == #["c", "e"]) s!"z ∈, got {mem}"
  check (none' == #["d"]) s!"neither x nor z, got {none'}"
  check ((log.getD 0 Lean.Json.null |>.getObjValAs? String "detail").toOption ==
      some "tagged | pushed: (((t0.\"tags\" & ?) = 0) AND ((t0.\"tags\" & ?) = 0)), residual conjuncts: 0")
    s!"logged plan, got {log}"
  -- the file refuses a stray bit (CHECK), even via raw SQL
  let db ← SQLite.open dbPath
  let raw : IO Unit := db.exec "INSERT INTO tagged (name, kind, tags) VALUES ('rogue', 'x', 8)"
  match ← raw.toBaseIO with
  | .ok _ => throw <| IO.userError "FAIL: CHECK should reject a bit outside the world"
  | .error e =>
      match e with
      | .otherError 19 details =>
          check ((details.toLower.splitOn "check constraint").length == 2)
            s!"raw insert rejected by CHECK, got: {details}"
      | e => throw <| IO.userError s!"FAIL: expected constraint error 19, got: {e}"
  -- planted behind the CHECK: the drift scan catches it at open, by column
  db.exec "PRAGMA ignore_check_constraints = ON"
  db.exec "UPDATE tagged SET tags = 9 WHERE name = 'd'"
  db.exec "PRAGMA ignore_check_constraints = OFF"
  match ← withDb dbPath [Entity.spec Tagged] (pure ()) with
  | .error (.enumDrift "tagged" "tags" v) => check (v == "9") s!"drift names the offending mask, got {v}"
  | .error e => throw <| IO.userError s!"FAIL: drift scan: wrong error {e}"
  | .ok _ => throw <| IO.userError "FAIL: a stray bit passed the drift scan"
  db.exec "UPDATE tagged SET tags = 0 WHERE name = 'd'"
  let rows ← expectOk (← withDb dbPath [Entity.spec Tagged] (fetchAll Tagged)) "scan passes once the bit is gone"
  check (((rows.find? (·.val.name == "e")).map fun r => (rowJson Tagged r).compress) ==
      some "{\"id\":5,\"kind\":\"x\",\"name\":\"e\",\"tags\":[\"x\",\"y\",\"z\"]}")
    "a fetched row renders its set as names"

private def migPath : System.FilePath := ".lake" / "leandb_test_enumset_mig.sqlite"

/-- `tagged(name, tags)` with `tags` an `EnumSet` over `vs`. -/
private def world (vs : Array String) : TableSpec :=
  ⟨"tagged", #[col "name" .text,
    { name := "tags", sqlType := .integer, nullable := false, fkTable := none, enumSet := some vs }], #[], none⟩

private def testMigration : IO Unit := do
  if ← migPath.pathExists then IO.FS.removeFile migPath
  let two := world #["x", "y"]
  let three := world #["x", "y", "z"]
  check (three.ddl.endsWith "\"tags\" INTEGER NOT NULL CHECK ((\"tags\" & ~7) = 0))") s!"three DDL, got {three.ddl}"
  discard <| expectOk (← withDb migPath [two] (pure ())) "create at two variants"
  let db ← SQLite.open migPath
  db.exec "INSERT INTO tagged (name, tags) VALUES ('a', 3)"
  -- grow: the CHECK changes, so it is a rebuild; old rows keep their bits
  let (_, rep) ← expectOk (← migrate migPath [three] (apply := true)) "grow the world"
  check (((rep.map (·.applied)).getD []).any (·.startsWith "rebuild")) "grow is a rebuild"
  discard <| expectOk (← withDb migPath [three] (pure ())) "opens at three variants"
  let db2 ← SQLite.open migPath
  let st ← db2.prepare "SELECT tags FROM tagged WHERE name = 'a'"
  discard <| st.step
  check ((← st.columnInt64 0) == 3) "old rows keep their bits"
  db2.exec "INSERT INTO tagged (name, tags) VALUES ('b', 4)"   -- the new CHECK admits bit 2
  -- shrink with a row using the removed variant: the rebuild's CHECK fails → rollback
  expectErr (← migrate migPath [two] (apply := true)) "migrate" "shrink refused by a live bit"
  let cnt ← db2.prepare "SELECT count(*) FROM tagged"
  discard <| cnt.step
  check ((← cnt.columnInt64 0) == 2) "rollback kept the data"
  discard <| expectOk (← withDb migPath [three] (pure ())) "still at three after the rollback"
  -- shrink with conforming data succeeds
  db2.exec "DELETE FROM tagged WHERE name = 'b'"
  discard <| expectOk (← migrate migPath [two] (apply := true)) "shrink with conforming data"
  discard <| expectOk (← withDb migPath [two] (pure ())) "opens at two variants"
  expectErr (← withDb migPath [three] (pure ())) "schema_mismatch" "the grown code is refused at open"
  -- a reorder or rename would re-label stored bits: refused by name
  match ← migrate migPath [world #["y", "x"]] (apply := true) with
  | .error (.migrate m) =>
      check ((m.splitOn "\"tags\" changed its variant order").length == 2) s!"reorder refusal, got {m}"
  | .error e => throw <| IO.userError s!"FAIL: reorder: wrong error {e}"
  | .ok _ => throw <| IO.userError "FAIL: a variant reorder was migrated"
  expectErr (← migrate migPath [world #["x", "w"]] (apply := true)) "migrate" "rename refused"
  expectErr (← migrate migPath [world #["x", "z", "y"]] (apply := true)) "migrate" "insertion in the middle refused"
  discard <| expectOk (← withDb migPath [two] (pure ())) "refusals left the instance at two variants"
  -- the plan diff itself, pure
  match planMigration [two] [three] with
  | .ok plan =>
      let first := (plan.steps.head?.map (·.describe)).getD ""
      check (plan.steps.length == 1 && first.startsWith "rebuild") s!"planMigration: grow is one rebuild step, got {first}"
  | .error e => throw <| IO.userError s!"FAIL: planMigration grow: {e}"
  check ((planMigration [two] [two]).toOption.map (·.steps.isEmpty) == some true) "planMigration: same world, no steps"

def run : IO Unit := do
  testCodec
  testJson
  testPred
  testEndToEnd
  testMigration

end EnumSetA

/-! ## Optional filters: case splits on a captured `Option α` parameter

"Filter by X if given": `(k? : Option Kind)` used as `k?.isNone || some
col == k?` or as `match k? with | none => true | some t => col == t`. The
world of `k?` is `none :: (ClosedEnum.all Kind).map some`; the split's
guards are value/value tests on `Option Kind`, so `k? = none` folds the
conjunct to `tt` and `k? = some c` to the column test. -/

private def optionalKindPlan (k? : Option Kind) : PlanFor (ts := [Ingredient])
    (fun (i : Stored Ingredient) => k?.isNone || some i.val.kind == k?) := by leandb_plan

private def optionalKindMatchPlan (k? : Option Kind) : PlanFor (ts := [Ingredient])
    (fun (i : Stored Ingredient) => match k? with | none => true | some t => i.val.kind == t) := by
  leandb_plan

/-- The negation of an optional filter is exact: `none` gives `ff`,
    `some c` gives `IS NOT`. -/
private def optionalKindNegPlan (k? : Option Kind) : PlanFor (ts := [Ingredient])
    (fun (i : Stored Ingredient) => !(k?.isNone || some i.val.kind == k?)) := by leandb_plan

/-- `some col == some c` with the column *under* the `some`: the column
    sits inside the match arm, so the split on `k?` fires first and the
    branch is recognized by unwrapping both `some`s. -/
private def someSomePlan (k? : Option Kind) : PlanFor (ts := [Ingredient])
    (fun (i : Stored Ingredient) =>
      match k? with | none => true | some t => some i.val.kind == some t) := by leandb_plan

/-- A captured `Option Nat` is not a closed world: the conjunct stays
    residual. -/
private def optionalNatPlan (n? : Option Nat) : PlanFor (ts := [Ingredient])
    (fun (i : Stored Ingredient) => n?.isNone || some i.val.name.length == n?) := by leandb_plan

private def kindWorld : Array (Option Kind) := #[none] ++ (ClosedEnum.all (α := Kind)).map some

private def testOptionalParamPlans : IO Unit := do
  checkPlan (optionalKindPlan none) "1" #[] 0
    "optional filter (isNone spelling), none: the conjunct folds to tt"
  checkPlan (optionalKindPlan (some .meat)) "t0.\"kind\" IS ?" #[.text "meat"] 0
    "optional filter (isNone spelling), some: the column test alone"
  checkPlan (optionalKindMatchPlan none) "1" #[] 0
    "optional filter (match spelling), none: the conjunct folds to tt"
  checkPlan (optionalKindMatchPlan (some .meat)) "t0.\"kind\" IS ?" #[.text "meat"] 0
    "optional filter (match spelling), some: the column test alone"
  checkPlan (optionalKindNegPlan none) "0" #[] 0 "negated optional filter, none: ff"
  checkPlan (optionalKindNegPlan (some .meat)) "t0.\"kind\" IS NOT ?" #[.text "meat"] 0
    "negated optional filter, some: IS NOT"
  checkPlan (someSomePlan none) "1" #[] 0 "some col == some c under the split, none"
  checkPlan (someSomePlan (some .fish)) "t0.\"kind\" IS ?" #[.text "fish"] 0
    "some col == some c under the split unwraps to the column test"
  checkPlan (optionalNatPlan none) "1" #[] 1 "captured Option Nat stays residual (none)"
  checkPlan (optionalNatPlan (some 4)) "1" #[] 1 "captured Option Nat stays residual (some)"
  for k? in kindWorld do
    check ((optionalKindPlan k?).plan.residuals == 0)
      s!"optional filter (isNone spelling) {repr k?} pushes with residual 0"
    check ((optionalKindMatchPlan k?).plan.residuals == 0)
      s!"optional filter (match spelling) {repr k?} pushes with residual 0"
    check ((optionalKindNegPlan k?).plan.residuals == 0)
      s!"negated optional filter {repr k?} pushes with residual 0"
    checkCoherent (optionalKindPlan k?) ingredients s!"optionalKindPlan {repr k?}"
    checkCoherent (optionalKindMatchPlan k?) ingredients s!"optionalKindMatchPlan {repr k?}"
    checkCoherent (optionalKindNegPlan k?) ingredients s!"optionalKindNegPlan {repr k?}"
    checkCoherent (someSomePlan k?) ingredients s!"someSomePlan {repr k?}"
  checkCoherent (optionalNatPlan none) ingredients "optionalNatPlan none"
  checkCoherent (optionalNatPlan (some 4)) ingredients "optionalNatPlan (some 4)"

private def optionalDbPath : System.FilePath := ".lake" / "leandb_test_optional.sqlite"

/-- Differential: for `none` and each `some`, both spellings and the
    negation agree with `selectUnplanned`, and with the expected rows. -/
private def testOptionalParamEndToEnd : IO Unit := do
  if ← optionalDbPath.pathExists then IO.FS.removeFile optionalDbPath
  let r ← withDb optionalDbPath [Entity.spec Ingredient] do
    discard <| insert Ingredient ⟨"pork", .meat⟩
    discard <| insert Ingredient ⟨"salmon", .fish⟩
    discard <| insert Ingredient ⟨"tofu", .plant⟩
    discard <| insert Ingredient ⟨"lentils", .plant⟩
    let byName : SortBy (Stored Ingredient) := .key (·.val.name)
    let names (rows : Array (Stored Ingredient)) := rows.map (·.val.name)
    let differential (label : String) (w : Stored Ingredient → Bool) : DbM (Array String) := do
      let planned ← select [Ingredient] w byName
      let reference ← selectUnplanned [Ingredient] w byName
      unless names planned == names reference do
        throw (.sqlite s!"FAIL: {label}: planned {names planned} vs reference {names reference}")
      return names planned
    let mut out : Array (Array String) := #[]
    for k? in kindWorld do
      let a ← differential s!"optional (isNone) {repr k?}" fun i => k?.isNone || some i.val.kind == k?
      let b ← differential s!"optional (match) {repr k?}" fun i =>
        match k? with | none => true | some t => i.val.kind == t
      let c ← differential s!"negated optional {repr k?}" fun i => !(k?.isNone || some i.val.kind == k?)
      unless a == b do throw (.sqlite s!"FAIL: spellings disagree for {repr k?}: {a} vs {b}")
      out := out.push a
      out := out.push c
    return out
  let rows ← expectOk r "optional filter queries"
  check (rows == #[#["lentils", "pork", "salmon", "tofu"], #[],
                   #["pork"], #["lentils", "salmon", "tofu"],
                   #["salmon"], #["lentils", "pork", "tofu"],
                   #["lentils", "tofu"], #["pork", "salmon"]])
    s!"optional filter rows: {rows}"

/-! ## LEP-0003 C: inline flatten — an `Inline` structure stored as sibling columns -/

namespace InlineC

/-- Two fields: a `via` newtype (the root `Milli`, whose codec is its
    projection) and a scalar with a default. -/
structure Dims where
  w : Milli
  h : Nat := 1
  deriving Repr, DecidableEq, LeanDb.Inline

/-- `size` has no parent-level default (its `h` still has the sub-field's);
    `pad` has one for the whole value, split into per-column defaults. -/
structure Box where
  label : String
  size : Dims
  pad : Dims := ⟨⟨7⟩, 2⟩
  deriving Repr, LeanDb.Entity

-- The refusals, at derive time and by name.
/--
error: deriving LeanDb.Entity: field 'd' of InlineC.OptBox is `Option Dims` where Dims is an Inline structure; an optional inline value is not supported (all sub-columns NULL is ambiguous once a sub-field is itself nullable) — store it as a JSON column (ColCodec.json) if it must be optional
-/
#guard_msgs in
structure OptBox where
  d : Option Dims
  deriving LeanDb.Entity

/--
error: deriving LeanDb.Inline: field 'd' of InlineC.Nested has type Dims, which is itself an Inline structure; nesting inline structures is not supported yet (one level only)
-/
#guard_msgs in
structure Nested where
  d : Dims
  deriving LeanDb.Inline

/--
error: deriving LeanDb.Inline: field 'd' of InlineC.OptInner is `Option Dims` where Dims is an Inline structure; an optional inline value is not supported (all sub-columns NULL is ambiguous once a sub-field is itself nullable) — store it as a JSON column (ColCodec.json) if it must be optional
-/
#guard_msgs in
structure OptInner where
  d : Option Dims
  deriving LeanDb.Inline

/--
error: deriving LeanDb.Entity: field 'd' of InlineC.DerivedInline is marked `derived` but has an Inline type; a derived column must be a scalar
-/
#guard_msgs in
structure DerivedInline where
  n : Nat
  d : Dims := derived ⟨⟨n⟩, n⟩
  deriving LeanDb.Entity

-- the flattened symbol is a column reference like any other, typed by
-- the sub-field
#check (Pred.Col.here Box.Field.size_w : Pred.Col [Box] Milli _)
#check (Pred.ord (.here Box.Field.size_h) .le 5 : Pred [Box])
-- …and there is no symbol for the inline field as a whole
#check_failure Box.Field.size

private def pj (s : String) : IO Lean.Json :=
  match Lean.Json.parse s with
  | .ok j => pure j
  | .error e => throw <| IO.userError s!"FAIL: bad test JSON: {e}"

private def box (label : String) (w h : Nat) : Box := { label, size := ⟨⟨w⟩, h⟩ }

private def testDerived : IO Unit := do
  -- the inline instance: the Entity surface minus the table
  check ((Inline.fields (α := Dims)).map Inline.fieldName == #["w", "h"]) "inline symbols in order"
  check ((Inline.columns Dims).map (·.dflt) == #[none, some (.int 1)]) "inline sub-field default is its column's"
  check ((Inline.columns Dims).all (·.group.isNone)) "an inline structure's own columns carry no group"
  check (Inline.encode (⟨⟨5⟩, 9⟩ : Dims) == #[.int 5, .int 9]) "inline encode"
  check ((Inline.decode #[.int 5, .int 9] : Except String Dims).toOption == some ⟨⟨5⟩, 9⟩) "inline decode"
  let strErr (r : Except String Dims) : Option String := match r with | .error m => some m | .ok _ => none
  check (strErr (Inline.decode #[.text "x", .int 9]) == some "w: expected INTEGER, found TEXT \"x\"")
    "inline decode names the sub-field"
  check (strErr (Inline.decode #[.int 5]) == some "*: expected 2 columns, found 1")
    "inline decode names the arity"
  -- the parent: one symbol and one column per sub-field, in order
  check (Entity.fields (α := Box) == #[.label, .size_w, .size_h, .pad_w, .pad_h]) "flattened symbols"
  check ((Entity.columns Box).map (·.name) == #["label", "size_w", "size_h", "pad_w", "pad_h"]) "flattened columns"
  check ((Entity.columns Box).map (·.group) == #[none, some "size", some "size", some "pad", some "pad"])
    "flattened columns carry their group"
  check ((Entity.columns Box).map (·.dflt) == #[none, none, some (.int 1), some (.int 7), some (.int 2)])
    "sub-field default kept; parent-level default split per column"
  check ((Entity.fields (α := Box)).all fun f => !Entity.isDerived f) "flattened columns are not derived"
  check (Entity.fieldOfName? Box "size_w" == some .size_w) "fieldOfName? finds a flattened column"
  check ((Entity.fieldOfName? Box "size").isNone) "the inline field itself is not a column"
  check (Entity.get (α := Box) Box.Field.size_h (box "b" 5 9) == 9) "get composes through the inline value"
  check ((Entity.spec Box).ddl ==
      "CREATE TABLE IF NOT EXISTS \"box\" (id INTEGER PRIMARY KEY AUTOINCREMENT, \"label\" TEXT NOT NULL, \"size_w\" INTEGER NOT NULL, \"size_h\" INTEGER NOT NULL DEFAULT 1, \"pad_w\" INTEGER NOT NULL DEFAULT 7, \"pad_h\" INTEGER NOT NULL DEFAULT 2)")
    s!"box DDL golden, got {(Entity.spec Box).ddl}"
  -- encode splices, decode slices; errors name the flattened column
  check (Entity.encode (box "b" 5 9) == #[.text "b", .int 5, .int 9, .int 7, .int 2]) "encode splices the inline values"
  match (Entity.decode #[.text "b", .int 5, .int 9, .int 7, .int 2] : Except DbError Box) with
  | .ok b => check (b.label == "b" && b.size == ⟨⟨5⟩, 9⟩ && b.pad == ⟨⟨7⟩, 2⟩) "decode round trip"
  | .error e => throw <| IO.userError s!"FAIL: decode: {e}"
  match (Entity.decode #[.text "b", .text "bad", .int 9, .int 7, .int 2] : Except DbError Box) with
  | .error (.decode "box" "size_w" m) => check (m == "expected INTEGER, found TEXT \"bad\"") s!"wrapped message, got {m}"
  | .error e => throw <| IO.userError s!"FAIL: wrong error for a bad sub-column: {e}"
  | .ok _ => throw <| IO.userError "FAIL: a bad sub-column decoded"
  match (Entity.decode #[.text "b", .int 5, .int 9, .int 7] : Except DbError Box) with
  | .error (.decode "box" "*" _) => pure ()
  | r => throw <| IO.userError s!"FAIL: wrong result for a short row: {repr (r.toOption.map (·.label))}"
  -- the group is not DDL and not fingerprint material
  let ungrouped : TableSpec := ⟨"box", (Entity.columns Box).map fun c => { c with group := none }, #[], none⟩
  check (fingerprint [Entity.spec Box] == fingerprint [ungrouped]) "group is not part of the fingerprint"
  check (fingerprint [Entity.spec Box] == toString (hash (Entity.spec Box).ddl)) "an inline schema fingerprints its DDL"
  -- entities without inline fields: nothing moved (value pinned before this change)
  check ((Entity.columns Author).all (·.group.isNone) && (Entity.columns Book).all (·.group.isNone))
    "plain entities have no groups"
  check (fingerprint schema == "13729757873300583215")
    s!"author+book fingerprint unchanged by stage C, got {fingerprint schema}"

private def testJson : IO Unit := do
  let b : Stored Box := ⟨⟨1⟩, box "b" 5 9⟩
  check ((rowJson Box b).compress == "{\"id\":1,\"label\":\"b\",\"pad\":{\"h\":2,\"w\":7},\"size\":{\"h\":9,\"w\":5}}")
    s!"row JSON nests the groups, got {(rowJson Box b).compress}"
  -- in: nested, flat, mixed across groups; an omitted sub-field takes its default
  let nested ← expectOk (rowOfJson Box (← pj "{\"label\":\"x\",\"size\":{\"w\":5,\"h\":9}}")) "nested in"
  check (nested.size == ⟨⟨5⟩, 9⟩ && nested.pad == ⟨⟨7⟩, 2⟩) "nested spelling decodes; omitted group takes the split default"
  let flat ← expectOk (rowOfJson Box (← pj "{\"label\":\"x\",\"size_w\":5,\"size_h\":9,\"pad_h\":4}")) "flat in"
  check (flat.size == ⟨⟨5⟩, 9⟩ && flat.pad == ⟨⟨7⟩, 4⟩) "flat spelling decodes"
  let partial_ ← expectOk (rowOfJson Box (← pj "{\"label\":\"x\",\"size\":{\"w\":5}}")) "partial group in"
  check (partial_.size == ⟨⟨5⟩, 1⟩) "an omitted sub-field inside the group takes the sub-field default"
  -- refusals, by name
  match rowOfJson Box (← pj "{\"label\":\"x\",\"size_w\":5,\"size\":{\"w\":6}}") with
  | .error (.decode "box" "size_w" m) => check ((m.splitOn "given twice").length == 2) s!"both-spellings message, got {m}"
  | r => throw <| IO.userError s!"FAIL: a column given in both spellings was not refused: {repr (r.toOption.map (·.label))}"
  match rowOfJson Box (← pj "{\"label\":\"x\",\"size\":{\"w\":6,\"depth\":1}}") with
  | .error (.decode "box" "size_depth" _) => pure ()
  | r => throw <| IO.userError s!"FAIL: an unknown sub-field was not refused: {repr (r.toOption.map (·.label))}"
  match rowOfJson Box (← pj "{\"label\":\"x\",\"size\":5}") with
  | .error (.decode "box" "size" _) => pure ()
  | r => throw <| IO.userError s!"FAIL: a non-object group was not refused: {repr (r.toOption.map (·.label))}"
  match rowOfJson Box (← pj "{\"label\":\"x\"}") with
  | .error (.decode "box" "size_w" "missing required field") => pure ()
  | r => throw <| IO.userError s!"FAIL: a missing required sub-column was not refused: {repr (r.toOption.map (·.label))}"
  match rowOfJson Box (← pj "{\"label\":\"x\",\"size\":{\"w\":\"five\"}}") with
  | .error (.decode "box" "size_w" _) => pure ()
  | r => throw <| IO.userError s!"FAIL: a mistyped nested value was not refused: {repr (r.toOption.map (·.label))}"
  -- merge: a nested object overlays only the sub-fields it names
  let merged ← expectOk (rowMergeJson Box b.val (← pj "{\"size\":{\"h\":3}}")) "nested merge"
  check (merged.size == ⟨⟨5⟩, 3⟩ && merged.label == "b") "nested merge overlays one sub-field"
  let mergedFlat ← expectOk (rowMergeJson Box b.val (← pj "{\"pad_w\":1}")) "flat merge"
  check (mergedFlat.pad == ⟨⟨1⟩, 2⟩) "flat merge overlays one column"
  check ((rowMergeJson Box b.val (← pj "{\"size_h\":3,\"size\":{\"h\":4}}")).isOk == false)
    "merge refuses both spellings of one column"
  -- schema JSON carries the group and round-trips it
  for c in Entity.columns Box do
    check ((ColumnSpec.fromJson? c.toJson).toOption == some c) s!"ColumnSpec JSON round trip for {c.name}"
  check ((specsFromJson? (specsToJson [Entity.spec Box])).toOption == some [Entity.spec Box])
    "schema JSON round trip with groups"
  check (((Entity.spec Box).toJson.compress.splitOn "\"group\":\"size\"").length == 3)
    "schema JSON shows the group on both of its columns"
  check (((Entity.spec Author).toJson.compress.splitOn "group").length == 1)
    "schema JSON of a plain entity mentions no group"

/-! The tactic: a projection of an inline field is the flattened column,
    a `via` sub-field unwraps on top, negation stays exact. -/

private def sizeHPlan : PlanFor (ts := [Box]) (fun (b : Stored Box) => b.val.size.h ≤ 5) := by leandb_plan
private def sizeWPlan : PlanFor (ts := [Box]) (fun (b : Stored Box) => b.val.size.w.v ≤ 5) := by leandb_plan
private def sizeWCapturedPlan (n : Nat) : PlanFor (ts := [Box]) (fun (b : Stored Box) =>
    b.val.size.w.v ≥ n) := by leandb_plan
private def negPlan : PlanFor (ts := [Box]) (fun (b : Stored Box) => !(b.val.pad.h == 2)) := by leandb_plan
private def bothPlan (n : Nat) : PlanFor (ts := [Box]) (fun (b : Stored Box) =>
    b.val.size.h ≤ n && b.val.size.w.v ≥ 3) := by leandb_plan
private def eqWholePlan (d : Dims) : PlanFor (ts := [Box]) (fun (b : Stored Box) =>
    b.val.size == d) := by leandb_plan
private def sizeWLitPlan : PlanFor (ts := [Box]) (fun (b : Stored Box) => b.val.size.w == ⟨5⟩) := by leandb_plan

private def testPlans : IO Unit := do
  checkPlan sizeHPlan "t0.\"size_h\" <= ?" #[.int 5] 0 "projection of an inline field pushes as the flattened column"
  checkPlan sizeWPlan "t0.\"size_w\" <= ?" #[.int 5] 0 "a via newtype sub-field unwraps on top of the flattening"
  checkPlan (sizeWCapturedPlan 3) "t0.\"size_w\" >= ?" #[.int 3] 0 "captured bound through the flattened newtype"
  checkPlan negPlan "t0.\"pad_h\" IS NOT ?" #[.int 2] 0 "negation over a flattened column is exact"
  checkPlan (bothPlan 5) "(t0.\"size_h\" <= ? AND t0.\"size_w\" >= ?)" #[.int 5, .int 3] 0 "both sub-fields push"
  checkPlan (eqWholePlan ⟨⟨1⟩, 1⟩) "1" #[] 1 "equality against the whole inline value is residual (no column for it)"
  checkPlan sizeWLitPlan "t0.\"size_w\" IS ?" #[.int 5] 0 "equality on a newtype sub-field pushes through its codec"
  -- coherence: the plan means what the lambda means
  let boxes : Array (Stored Box) := #[⟨⟨1⟩, box "a" 5 9⟩, ⟨⟨2⟩, box "b" 2 3⟩, ⟨⟨3⟩, { box "c" 3 5 with pad := ⟨⟨1⟩, 5⟩ }⟩]
  checkCoherent sizeHPlan boxes "sizeHPlan"
  checkCoherent sizeWPlan boxes "sizeWPlan"
  checkCoherent negPlan boxes "negPlan"
  checkCoherent (bothPlan 5) boxes "bothPlan 5"

private def dbPath : System.FilePath := ".lake" / "leandb_test_inline.sqlite"

private def testEndToEnd : IO Unit := do
  if ← dbPath.pathExists then IO.FS.removeFile dbPath
  let r ← withDb dbPath [Entity.spec Box] do
    let a ← insert Box (box "a" 5 9)
    discard <| insert Box (box "b" 2 3)
    discard <| insert Box { box "c" 3 5 with pad := ⟨⟨1⟩, 5⟩ }
    let byLabel : SortBy (Stored Box) := .key (·.val.label)
    let planned ← select [Box] (fun b => b.val.size.h ≤ 5 && b.val.size.w.v ≥ 3) byLabel
    let reference ← selectUnplanned [Box] (fun b => b.val.size.h ≤ 5 && b.val.size.w.v ≥ 3) byLabel
    unless planned.map (·.val.label) == reference.map (·.val.label) do
      throw (.sqlite s!"FAIL: planned {planned.map (·.val.label)} ≠ unplanned {reference.map (·.val.label)}")
    unless planned.map (·.val.label) == #["c"] do
      throw (.sqlite s!"FAIL: expected [c], got {planned.map (·.val.label)}")
    let log ← readLog 2
    let details := log.map fun e => (e.getObjValAs? String "detail").toOption.getD "?"
    unless details.contains "box | pushed: (t0.\"size_h\" <= ? AND t0.\"size_w\" >= ?), residual conjuncts: 0" do
      throw (.sqlite s!"FAIL: log lacks the pushed plan: {details}")
    -- update through the JSON boundary with the nested spelling
    let a' ← DbM.ofExcept (rowMergeJson Box a.val (Lean.Json.mkObj [("size", Lean.Json.mkObj [("h", 1)])]))
    discard <| update a a'
    fetchAll Box
  let rows ← expectOk r "inline end to end"
  check (rows.map (·.val.size.h) == #[1, 3, 5] && rows.map (·.val.pad.h) == #[2, 2, 5]) "rows read back through the slices"
  -- the file holds plain columns: a raw write to one sub-column is one column
  let db ← SQLite.open dbPath
  db.exec "UPDATE box SET size_w = 'oops' WHERE label = 'b'"
  match ← withDb dbPath [Entity.spec Box] (fetchAll Box) with
  | .error (.decode "box" "size_w" _) => pure ()
  | .error e => throw <| IO.userError s!"FAIL: raw-SQL corruption of a sub-column: wrong error {e}"
  | .ok _ => throw <| IO.userError "FAIL: a corrupted sub-column was read back"

private def migPath : System.FilePath := ".lake" / "leandb_test_inline_mig.sqlite"

/-- `Box` before `pad` existed. -/
private def boxV1 : TableSpec :=
  ⟨"box", (Entity.columns Box).filter fun c => c.group != some "pad", #[], none⟩

private def testMigration : IO Unit := do
  -- adding an inline field is one addColumn per sub-column
  match planMigration [boxV1] [Entity.spec Box] with
  | .ok plan =>
      check (plan.steps.map (·.describe) == ["add column \"box\".\"pad_w\"", "add column \"box\".\"pad_h\""])
        s!"adding an inline field plans N addColumn steps, got {plan.steps.map (·.describe)}"
  | .error e => throw <| IO.userError s!"FAIL: planMigration: {e}"
  if ← migPath.pathExists then IO.FS.removeFile migPath
  discard <| expectOk (← withDb migPath [boxV1] (pure ())) "create at v1"
  let db ← SQLite.open migPath
  db.exec "INSERT INTO box (label, size_w, size_h) VALUES ('old', 4, 4)"
  let (_, report?) ← expectOk (← migrate migPath [Entity.spec Box] (apply := true)) "additive migrate"
  check ((report?.map (·.applied)).getD [] == ["add column \"box\".\"pad_w\"", "add column \"box\".\"pad_h\""])
    "both sub-columns added"
  let rows ← expectOk (← withDb migPath [Entity.spec Box] (fetchAll Box)) "open after migrate"
  check (rows.map (·.val.pad) == #[⟨⟨7⟩, 2⟩]) "existing rows took the split parent default"

def run : IO Unit := do
  testDerived
  testJson
  testPlans
  testEndToEnd
  testMigration

end InlineC

/-! ## LEP-0003 D: child tables — a `List` of `Inline` records as a table of its own -/

namespace ChildD

/-- The record: a name, a quantity with a default, and a `Ref` into another
    table (a foreign key inside a child row). -/
structure Item where
  name : String
  qty : Nat := 1
  supplier : Option (Ref Author) := none
  deriving Repr, LeanDb.Inline

/-- The parent: one child list, and a derived column computed from it —
    which `decode` cannot check without the list, so the link's `attach`
    does. -/
structure Order where
  customer : String
  items : List Item
  total : Nat := derived (items.foldl (fun acc i => acc + i.qty) 0)
  deriving Repr, LeanDb.Entity

/-- Another table pointing at `Order` with an ordinary (RESTRICT) reference. -/
structure Shipment where
  order : Ref Order
  carrier : String
  deriving Repr, LeanDb.Entity

-- The refusals, at derive time and by name.
/--
error: deriving LeanDb.Entity: field 'tags' of ChildD.BadList is `List Nat` but Nat is not an Inline record; a child table needs `deriving LeanDb.Inline` on the element type (or give `List Nat` a ColCodec of its own to store it as one column)
-/
#guard_msgs in
structure BadList where
  tags : List Nat
  deriving LeanDb.Entity

/--
error: deriving LeanDb.Inline: field 'items' of ChildD.NestedList is `List Item` where Item is an Inline record; an Inline record cannot itself contain a child list (nested child tables are not supported)
-/
#guard_msgs in
structure NestedList where
  items : List Item
  deriving LeanDb.Inline

/--
error: deriving LeanDb.Entity: field 'items' of ChildD.OptList is `Option (List Item)` where Item is an Inline record; an optional child list is not supported (an absent list and an empty one would be the same rows) — use `List Item` and let empty mean none
-/
#guard_msgs in
structure OptList where
  items : Option (List Item)
  deriving LeanDb.Entity

/--
error: deriving LeanDb.Entity: field 'items' of ChildD.DerivedList is a child list marked `derived`; derived child lists (a tabulated relation, LEP-0005) are not supported yet
-/
#guard_msgs in
structure DerivedList where
  n : Nat
  items : List Item := derived (List.replicate n ⟨"x", 1, none⟩)
  deriving LeanDb.Entity

structure KeyedRec where
  parent : Nat
  deriving Repr, LeanDb.Inline

/--
error: deriving LeanDb.Entity: field 'ks' of ChildD.KeyedParent: the record ChildD.KeyedRec has a field 'parent', which is the name of the child table's key column; rename it
-/
#guard_msgs in
structure KeyedParent where
  ks : List KeyedRec
  deriving LeanDb.Entity

-- The generated child is an ordinary entity: its key is a typed `Id Order`,
-- so it is a valid LEP-0004 relation, and its record columns are its symbols.
#check (Pred.forall (ts := [Order]) .id (.here Order.Items.Field.parent) .tt : Pred [Order])
#check (Pred.Col.here Order.Items.Field.qty : Pred.Col [Order.Items] Nat _)
#check (Order.Items.record : Order.Items → Item)
#check (Order.Items.ofRecord : Ref Order → Nat → Item → Order.Items)
-- …and the parent has no symbol for the list: it is not a column
#check_failure Order.Field.items

private def pj (s : String) : IO Lean.Json :=
  match Lean.Json.parse s with
  | .ok j => pure j
  | .error e => throw <| IO.userError s!"FAIL: bad test JSON: {e}"

private def item (name : String) (qty : Nat) : Item := { name, qty }
private def order (customer : String) (items : List Item) : Order := { customer, items }

instance : Inhabited (Stored Order) := ⟨⟨⟨0⟩, order "" []⟩⟩
instance : Inhabited (Stored Shipment) := ⟨⟨⟨0⟩, ⟨⟨0⟩, ""⟩⟩⟩

private def sameItem (a b : Item) : Bool :=
  a.name == b.name && a.qty == b.qty && a.supplier == b.supplier
private def sameItems (a b : List Item) : Bool :=
  a.length == b.length && (a.zip b).all fun (x, y) => sameItem x y

private def link : ChildLink Order := (Entity.children (α := Order)).headD
  { field := "?", table := "?", spec := ⟨"?", #[], #[], none⟩, rows := fun _ => #[]
    attach := fun _ a => .ok a, attachRecomputing := fun _ a => .ok a }

private def testDerived : IO Unit := do
  -- the parent: scalar columns only, the list is not one
  check (Entity.fields (α := Order) == #[.customer, .total]) "the parent's symbols are its columns"
  check ((Entity.columns Order).map (·.name) == #["customer", "total"]) "no column for the list"
  check ((Entity.children (α := Order)).map (·.field) == ["items"]
      && (Entity.children (α := Order)).map (·.table) == ["order_items"])
    "one child link, named after the field and the parent table"
  check ((Entity.specs Order).map (·.name) == ["order", "order_items"]) "specs: parent first, then children"
  check ((Entity.specs Order).head? == some (Entity.spec Order)) "spec stays the parent's alone"
  check ((Entity.specs Author).map (·.name) == ["author"]) "an entity without children has one spec"
  -- the child: parent (cascading FK), position, then the record's columns verbatim
  check (Entity.tableName Order.Items == "order_items") "child table name"
  check ((Entity.columns Order.Items).map (·.name) == #["parent", "position", "name", "qty", "supplier"])
    "child columns in order"
  let parentCol := (Entity.columns Order.Items).getD 0 default
  check (parentCol.fkTable == some "order" && parentCol.cascade && parentCol.sqlType == .integer && !parentCol.nullable)
    s!"parent is a cascading FK onto the parent table, got {repr parentCol}"
  let supplierCol := (Entity.columns Order.Items).getD 4 default
  check (supplierCol.fkTable == some "author" && !supplierCol.cascade && supplierCol.nullable)
    "a Ref inside the record is an ordinary RESTRICT FK"
  check (((Entity.columns Order.Items).getD 3 default).dflt == some (.int 1)) "the record's default is the column's"
  check (link.recordColumns.map (·.name) == #["name", "qty", "supplier"]) "recordColumns skips the keys"
  check ((Entity.spec Order.Items).ddl ==
      "CREATE TABLE IF NOT EXISTS \"order_items\" (id INTEGER PRIMARY KEY AUTOINCREMENT, \"parent\" INTEGER NOT NULL REFERENCES \"order\"(id) ON DELETE CASCADE ON UPDATE RESTRICT, \"position\" INTEGER NOT NULL, \"name\" TEXT NOT NULL, \"qty\" INTEGER NOT NULL DEFAULT 1, \"supplier\" INTEGER DEFAULT NULL REFERENCES \"author\"(id) ON DELETE RESTRICT ON UPDATE RESTRICT)")
    s!"child DDL golden, got {(Entity.spec Order.Items).ddl}"
  check ((Entity.spec Order).ddl ==
      "CREATE TABLE IF NOT EXISTS \"order\" (id INTEGER PRIMARY KEY AUTOINCREMENT, \"customer\" TEXT NOT NULL, \"total\" INTEGER NOT NULL)")
    s!"parent DDL golden, got {(Entity.spec Order).ddl}"
  check (((Entity.spec Shipment).ddl.splitOn "ON DELETE RESTRICT").length == 2) "an ordinary Ref still restricts"
  -- record ↔ child row
  let c := Order.Items.ofRecord ⟨7⟩ 2 (item "a" 3)
  check (c.parent == ⟨7⟩ && c.position == 2 && c.name == "a" && c.qty == 3 && sameItem c.record (item "a" 3))
    "ofRecord/record round trip"
  check (Entity.encode c == #[.int 7, .int 2, .text "a", .int 3, .null]) "child encode: keys then record"
  -- encode/decode of the parent: the list is not encoded; decode leaves it empty
  let o := order "c" [item "a" 2, item "b" 3]
  check (Entity.encode o == #[.text "c", .int 5]) "parent encode recomputes the derived column from the list"
  match (Entity.decode #[.text "c", .int 5] : Except DbError Order) with
  | .ok o' => check (o'.customer == "c" && o'.items.isEmpty && o'.total == 5) "decode leaves the list empty, keeps the stored derived value"
  | .error e => throw <| IO.userError s!"FAIL: decode: {e}"
  -- the link: rows off a value, attach back (with the derived check)
  check (link.rows o == #[#[.text "a", .int 2, .null], #[.text "b", .int 3, .null]]) "link.rows is the records' encode"
  let bare : Order := { customer := "c", items := [], total := 5 }
  match link.attach #[(0, #[.text "a", .int 2, .null]), (1, #[.text "b", .int 3, .null])] bare with
  | .ok o' => check (sameItems o'.items o.items && o'.total == 5) "attach sets the list and the derived check passes"
  | .error e => throw <| IO.userError s!"FAIL: attach: {e}"
  match link.attach #[(0, #[.text "a", .int 2, .null])] bare with
  | .error (.decode "order" "total" m) => check (m == "derived column disagrees with its source") s!"attach check message, got {m}"
  | r => throw <| IO.userError s!"FAIL: attach did not check the derived column: {repr (r.toOption.map (·.total))}"
  match link.attachRecomputing #[(0, #[.text "a", .int 2, .null])] bare with
  | .ok o' => check (o'.total == 2 && o'.items.length == 1) "attachRecomputing recomputes the derived column"
  | .error e => throw <| IO.userError s!"FAIL: attachRecomputing: {e}"
  match link.attach #[(0, #[.text "a", .text "two", .null])] bare with
  | .error (.decode "order_items" "qty" _) => pure ()
  | r => throw <| IO.userError s!"FAIL: a bad child column was not refused by name: {repr (r.toOption.map (·.total))}"
  match link.attach #[(0, #[.text "a"])] bare with
  | .error (.decode "order_items" "*" _) => pure ()
  | r => throw <| IO.userError s!"FAIL: a short child row was not refused: {repr (r.toOption.map (·.total))}"
  -- cascade is DDL, so it is fingerprint material; the default (no cascade) changes nothing
  let restricted : TableSpec := ⟨"order_items", (Entity.columns Order.Items).map fun c => { c with cascade := false }, #[], none⟩
  check (fingerprint (Entity.specs Order) != fingerprint [Entity.spec Order, restricted]) "cascade is part of the fingerprint"
  check (fingerprint schema == "13729757873300583215")
    s!"author+book fingerprint unchanged by stage D, got {fingerprint schema}"
  -- schema JSON carries the cascade and round-trips it
  for c in Entity.columns Order.Items do
    check ((ColumnSpec.fromJson? c.toJson).toOption == some c) s!"ColumnSpec JSON round trip for {c.name}"
  check (((Entity.spec Order.Items).toJson.compress.splitOn "\"cascade\":true").length == 2)
    "schema JSON shows the cascade on the parent column only"
  check (((Entity.spec Book).toJson.compress.splitOn "cascade").length == 1) "an ordinary FK mentions no cascade"

private def testJson : IO Unit := do
  let o : Stored Order := ⟨⟨1⟩, order "c" [item "a" 2, item "b" 3]⟩
  check ((rowJson Order o).compress ==
      "{\"customer\":\"c\",\"id\":1,\"items\":[{\"name\":\"a\",\"qty\":2,\"supplier\":null},{\"name\":\"b\",\"qty\":3,\"supplier\":null}],\"total\":5}")
    s!"row JSON nests the child list, got {(rowJson Order o).compress}"
  -- in: the list, positions by order; an omitted record field takes its default
  let nested ← expectOk (rowOfJson Order (← pj "{\"customer\":\"x\",\"items\":[{\"name\":\"p\"},{\"name\":\"q\",\"qty\":5}]}")) "nested in"
  check (sameItems nested.items [item "p" 1, item "q" 5] && nested.total == 6)
    "child list decodes in order; the derived column is recomputed from it"
  let none' ← expectOk (rowOfJson Order (← pj "{\"customer\":\"x\"}")) "omitted list"
  check (none'.items.isEmpty && none'.total == 0) "an omitted child list is empty"
  -- refusals, by name
  match rowOfJson Order (← pj "{\"customer\":\"x\",\"items\":[{\"name\":\"p\",\"bogus\":1}]}") with
  | .error (.decode "order_items" "bogus" _) => pure ()
  | r => throw <| IO.userError s!"FAIL: an unknown record field was not refused: {repr (r.toOption.map (·.total))}"
  match rowOfJson Order (← pj "{\"customer\":\"x\",\"items\":{\"name\":\"p\"}}") with
  | .error (.decode "order" "items" _) => pure ()
  | r => throw <| IO.userError s!"FAIL: a non-array list was not refused: {repr (r.toOption.map (·.total))}"
  match rowOfJson Order (← pj "{\"customer\":\"x\",\"items\":[3]}") with
  | .error (.decode "order_items" "*" _) => pure ()
  | r => throw <| IO.userError s!"FAIL: a non-object record was not refused: {repr (r.toOption.map (·.total))}"
  match rowOfJson Order (← pj "{\"customer\":\"x\",\"items\":[{\"qty\":2}]}") with
  | .error (.decode "order_items" "name" "missing required field") => pure ()
  | r => throw <| IO.userError s!"FAIL: a missing record field was not refused: {repr (r.toOption.map (·.total))}"
  match rowOfJson Order (← pj "{\"customer\":\"x\",\"items\":[{\"name\":\"p\",\"qty\":\"two\"}]}") with
  | .error (.decode "order_items" "qty" _) => pure ()
  | r => throw <| IO.userError s!"FAIL: a mistyped record field was not refused: {repr (r.toOption.map (·.total))}"
  -- merge: a list given replaces the whole list; omitted, the old one is kept
  let replaced ← expectOk (rowMergeJson Order o.val (← pj "{\"items\":[{\"name\":\"z\",\"qty\":9}]}")) "merge with a list"
  check (sameItems replaced.items [item "z" 9] && replaced.total == 9 && replaced.customer == "c")
    "merge replaces the list and recomputes the derived column"
  let kept ← expectOk (rowMergeJson Order o.val (← pj "{\"customer\":\"d\"}")) "merge without the list"
  check (sameItems kept.items o.val.items && kept.customer == "d" && kept.total == 5) "merge without the list keeps it"

/-! The tactic: `.any`/`.all` over the child-list field is LEP-0004's
    quantifier over the generated child; a body it cannot translate makes
    the whole quantifier opaque; anything but a quantifier over the list
    stays residual. -/

private def anyPlan : PlanFor (ts := [Order]) (fun (o : Stored Order) => o.val.items.any (·.qty ≥ 3)) := by leandb_plan
private def allPlan (n : Nat) : PlanFor (ts := [Order]) (fun (o : Stored Order) =>
    o.val.items.all (fun i => i.qty ≥ n)) := by leandb_plan
private def dotAllPlan : PlanFor (ts := [Order]) (fun (o : Stored Order) =>
    List.all o.val.items (fun i => i.qty ≥ 3)) := by leandb_plan
private def outerPlan : PlanFor (ts := [Order]) (fun (o : Stored Order) =>
    o.val.items.any (fun i => i.name == o.val.customer)) := by leandb_plan
private def opaqueBodyPlan : PlanFor (ts := [Order]) (fun (o : Stored Order) =>
    o.val.items.any (fun i => i.name.length == 3)) := by leandb_plan
private def lengthPlan : PlanFor (ts := [Order]) (fun (o : Stored Order) => o.val.items.length == 2) := by leandb_plan
private def negAllPlan : PlanFor (ts := [Order]) (fun (o : Stored Order) =>
    o.val.customer == "c" && !(o.val.items.all (·.qty ≥ 3))) := by leandb_plan
private def joinedPlan : PlanFor (ts := [Shipment, Order]) (fun (r : Stored Shipment × Stored Order) =>
    r.1.val.order == r.2.ref && r.2.val.items.any (fun i => i.qty ≥ 3)) := by leandb_plan
private def supplierPlan (a : Ref Author) : PlanFor (ts := [Order]) (fun (o : Stored Order) =>
    o.val.items.any (fun i => i.supplier == some a)) := by leandb_plan

/-- The same question as `allPlan 3`, written as data (LEP-0004). -/
private def allP (n : Nat) : Pred [Order] :=
  Pred.all (.here Order.Items.Field.parent) (pred% [Order.Items, Order] fun (i, _) => i.val.qty ≥ n)

private def orders : Array (Stored Order) := #[
  ⟨⟨1⟩, order "c" [item "ab" 2, item "abc" 4]⟩,
  ⟨⟨2⟩, order "d" []⟩,
  ⟨⟨3⟩, order "xyz" [item "xyz" 3]⟩]

/-- The child table as the snapshot sees it: every list, flattened. -/
private def childRows : Array (Stored Order.Items) := Id.run do
  let mut out := #[]
  for o in orders do
    for (i, k) in o.val.items.zipIdx do
      out := out.push (⟨⟨out.size.toInt64 + 1⟩, Order.Items.ofRecord o.ref k i⟩ : Stored Order.Items)
  return out

private def snap : Pred.Snapshot := Pred.Snapshot.empty.add Order.Items childRows

/-- `checkCoherent` under the snapshot of the child table: the lambda reads
    the attached list, the plan the snapshot — the same rows. -/
private def checkCoherentSnap {ts : List Type} {w : Rows ts → Bool} (p : PlanFor w)
    (rows : Array (Rows ts)) (label : String) : IO Unit := do
  for r in rows do
    check (p.plan.denote snap r == w r) s!"coherence: {label}"

private def testPlans : IO Unit := do
  checkPlan anyPlan "EXISTS (SELECT 1 FROM \"order_items\" AS s0 WHERE s0.\"parent\" IS t0.\"id\" AND s0.\"qty\" >= ?)" #[.int 3] 0
    ".any over the child list is EXISTS"
  checkPlan (allPlan 3) "NOT EXISTS (SELECT 1 FROM \"order_items\" AS s0 WHERE s0.\"parent\" IS t0.\"id\" AND s0.\"qty\" < ?)" #[.int 3] 0
    ".all over the child list is NOT EXISTS of the negated body"
  checkPlan dotAllPlan "NOT EXISTS (SELECT 1 FROM \"order_items\" AS s0 WHERE s0.\"parent\" IS t0.\"id\" AND s0.\"qty\" < ?)" #[.int 3] 0
    "List.all spelling is the same plan"
  checkPlan outerPlan "EXISTS (SELECT 1 FROM \"order_items\" AS s0 WHERE s0.\"parent\" IS t0.\"id\" AND s0.\"name\" IS t0.\"customer\")" #[] 0
    "the body reaches the outer row"
  checkPlan opaqueBodyPlan "1" #[] 1 "a body the tactic cannot translate makes the whole quantifier opaque"
  checkPlan lengthPlan "1" #[] 1 "an aggregate over the list stays residual"
  checkPlan negAllPlan "(t0.\"customer\" IS ? AND EXISTS (SELECT 1 FROM \"order_items\" AS s0 WHERE s0.\"parent\" IS t0.\"id\" AND s0.\"qty\" < ?))" #[.text "c", .int 3] 0
    "negation of a quantifier is exact"
  checkPlan joinedPlan "(t0.\"order\" IS t1.\"id\" AND EXISTS (SELECT 1 FROM \"order_items\" AS s0 WHERE s0.\"parent\" IS t1.\"id\" AND s0.\"qty\" >= ?))" #[.int 3] 0
    "a quantifier on the second table of a join lifts its parent reference"
  checkPlan (supplierPlan ⟨5⟩) "EXISTS (SELECT 1 FROM \"order_items\" AS s0 WHERE s0.\"parent\" IS t0.\"id\" AND s0.\"supplier\" IS ?)" #[.int 5] 0
    "a Ref column of the record pushes through `some`"
  -- lambda and data spellings are one plan
  check ((allPlan 3).plan.renderT == (allP 3).renderT && (allPlan 3).plan.residuals == (allP 3).residuals)
    s!"lambda .all and Pred.all render identically: {(allPlan 3).plan.renderT.1} vs {(allP 3).renderT.1}"
  -- the plan surface
  check (anyPlan.plan.tables == [0] && !anyPlan.plan.hasJoin) "a quantifier on table 0 is not a join"
  check ((anyPlan.plan.children.map fun c => @Entity.tableName c.1 c.2) == ["order_items"]) "children names the generated child"
  -- coherence under the child snapshot
  checkCoherentSnap anyPlan orders "anyPlan"
  checkCoherentSnap (allPlan 3) orders "allPlan 3"
  checkCoherentSnap (allPlan 5) orders "allPlan 5"
  checkCoherentSnap outerPlan orders "outerPlan"
  checkCoherentSnap opaqueBodyPlan orders "opaqueBodyPlan"
  checkCoherentSnap lengthPlan orders "lengthPlan"
  checkCoherentSnap negAllPlan orders "negAllPlan"
  check ((orders.filter ((allP 3).denote snap)).map (·.id.toInt64) == #[2, 3]) "Pred.all denotes over the child snapshot"

private def dbPath : System.FilePath := ".lake" / "leandb_test_child.sqlite"

private def childSchema : List TableSpec :=
  [Entity.spec Author] ++ Entity.specs Order ++ [Entity.spec Shipment]

/-- Raw count of child rows for one parent. -/
private def childCount (db : SQLite) (parent : Int64) : IO Int64 := do
  let stmt ← db.prepare "SELECT count(*) FROM order_items WHERE parent = ?"
  stmt.bindInt64 1 parent
  discard <| stmt.step
  stmt.columnInt64 0

private def customers (rows : Array (Stored Order)) : Array String := rows.map (·.val.customer)

private def testEndToEnd : IO Unit := do
  if ← dbPath.pathExists then IO.FS.removeFile dbPath
  let r ← withDb dbPath childSchema do
    let ada ← insert Author ⟨"Ada", 36⟩
    let o1 ← insert Order (order "c" [item "ab" 2, { item "abc" 4 with supplier := some ada.ref }])
    let o2 ← insert Order (order "d" [])
    let o3 ← insert Order (order "xyz" [item "xyz" 3])
    -- every read path attaches, in position order
    let some g ← get o1.id | throw (.sqlite "FAIL: get")
    unless sameItems g.val.items o1.val.items && g.val.total == 6 do
      throw (.sqlite s!"FAIL: get attaches: {repr g.val}")
    let all ← fetchAll Order
    unless all.size == 3 && sameItems all[0]!.val.items o1.val.items && all[1]!.val.items.isEmpty
        && sameItems all[2]!.val.items o3.val.items do
      throw (.sqlite s!"FAIL: fetchAll attaches: {repr all}")
    let filtered ← select [Order] (fun o => o.val.customer == "c")
    unless filtered.size == 1 && sameItems filtered[0]!.val.items o1.val.items do
      throw (.sqlite s!"FAIL: fetchFiltered attaches: {repr filtered}")
    let sh ← insert Shipment ⟨o1.ref, "post"⟩
    let joined ← select [Shipment, Order] (fun (s, o) => s.val.order == o.ref)
    unless joined.size == 1 && sameItems joined[0]!.2.val.items o1.val.items && joined[0]!.1.id == sh.id do
      throw (.sqlite s!"FAIL: selectJoined attaches: {joined.size}")
    -- the quantifier, three ways: lambda, data, reference — one answer
    let byId : SortBy (Stored Order) := .key (·.id)
    let viaLambda ← select [Order] (fun o => o.val.items.all (·.qty ≥ 3)) byId
    let viaData ← selectP [Order] (allP 3) byId
    let reference ← selectUnplanned [Order] (fun o => o.val.items.all (·.qty ≥ 3)) byId
    unless customers viaLambda == #["d", "xyz"] && customers viaData == customers viaLambda
        && customers reference == customers viaLambda do
      throw (.sqlite s!"FAIL: .all three ways: {customers viaLambda} / {customers viaData} / {customers reference}")
    let entries ← readLog 3
    let details := entries.map fun e => (e.getObjValAs? String "detail").toOption.getD ""
    let expected := "order | pushed: NOT EXISTS (SELECT 1 FROM \"order_items\" AS s0 WHERE s0.\"parent\" IS t0.\"id\" AND s0.\"qty\" < ?), residual conjuncts: 0"
    unless (details.filter (· == expected)).size == 2 do
      throw (.sqlite s!"FAIL: lambda and data log the same NOT EXISTS plan: {details}")
    let anyRows ← select [Order] (fun o => o.val.items.any (·.qty ≥ 3)) byId
    unless customers anyRows == #["c", "xyz"] do throw (.sqlite s!"FAIL: .any: {customers anyRows}")
    -- an opaque body: SQL returns everyone, the lambda decides
    let opaqueRows ← select [Order] (fun o => o.val.items.any (fun i => i.name.length == 3)) byId
    let opaqueRef ← selectUnplanned [Order] (fun o => o.val.items.any (fun i => i.name.length == 3)) byId
    unless customers opaqueRows == #["c", "xyz"] && customers opaqueRows == customers opaqueRef do
      throw (.sqlite s!"FAIL: opaque body: {customers opaqueRows} vs {customers opaqueRef}")
    let last ← readLog 2
    unless (last.map fun e => (e.getObjValAs? String "detail").toOption.getD "").contains
        "order | pushed: 1, residual conjuncts: 1" do
      throw (.sqlite s!"FAIL: opaque quantifier logged as residual 1: {last}")
    -- update replaces the list wholesale and recomputes the derived column
    let o1' ← update o1 { o1.val with items := [item "z" 9] }
    let some g' ← get o1.id | throw (.sqlite "FAIL: get after update")
    unless sameItems g'.val.items [item "z" 9] && g'.val.total == 9 do
      throw (.sqlite s!"FAIL: update replaced the list: {repr g'.val}")
    -- CAS staleness on the parent still fires, and leaves the children alone
    match ← (update o1 (order "stale" []) >>= fun _ => pure "updated") <|> pure "stale" with
    | "stale" => pure ()
    | r => throw (.sqlite s!"FAIL: stale update: {r}")
    let some g'' ← get o1.id | throw (.sqlite "FAIL: get after stale update")
    unless sameItems g''.val.items [item "z" 9] do throw (.sqlite "FAIL: a stale update touched the children")
    -- a failing child write rolls the parent back: dangling supplier
    match ← (insert Order (order "bad" [{ item "a" 1 with supplier := some ⟨999⟩ }]) >>= fun _ => pure "inserted")
        <|> pure "refused" with
    | "refused" => pure ()
    | r => throw (.sqlite s!"FAIL: dangling ref inside a child row: {r}")
    unless (← fetchAll Order).size == 3 do throw (.sqlite "FAIL: the parent row survived a failed child write")
    -- RESTRICT from another table still refuses; then the cascade takes the children
    match ← (delete o1.id >>= fun _ => pure "deleted") <|> pure "restricted" with
    | "restricted" => pure ()
    | r => throw (.sqlite s!"FAIL: a referenced parent was deleted: {r}")
    delete sh.id
    delete o1.id
    delete o2.id
    let _ := o1'
    fetchAll Order
  let rows ← expectOk r "child tables end to end"
  check (customers rows == #["xyz"]) s!"the surviving order, got {customers rows}"
  -- the file: the deleted parent's children are gone, the survivor's are there
  let db ← SQLite.open dbPath
  check ((← childCount db 1) == 0 && (← childCount db 3) == 1) "cascade removed the deleted parent's rows only"
  -- the typed errors, by code
  expectErr (← withDb dbPath childSchema (insert Order (order "bad" [{ item "a" 1 with supplier := some ⟨999⟩ }])))
    "missing_ref" "dangling Ref inside a child row"
  expectErr (← withDb dbPath childSchema (update ⟨⟨3⟩, order "stale" []⟩ (order "x" []))) "stale" "stale parent CAS"
  -- a raw-SQL write to the derived column is caught by attach, by name
  db.exec "UPDATE \"order\" SET total = 99 WHERE id = 3"
  match ← withDb dbPath childSchema (fetchAll Order) with
  | .error (.decode "order" "total" m) => check (m == "derived column disagrees with its source") s!"desync message, got {m}"
  | .error e => throw <| IO.userError s!"FAIL: raw-SQL desync of a child-derived column: wrong error {e}"
  | .ok _ => throw <| IO.userError "FAIL: a desynchronized child-derived column was read back"
  db.exec "UPDATE \"order\" SET total = 3 WHERE id = 3"
  -- the CLI: the child table is a table like any other; the parent shows the list
  let cli ← expectOk (← withDb dbPath childSchema do
      let child := CliTable.of Order.Items
      let byName ← child.rowsWhere [("name", "xyz")] 100
      let parent := CliTable.of Order
      let inserted ← parent.insertJson (← DbM.ofExcept (match Lean.Json.parse "{\"customer\":\"j\",\"items\":[{\"name\":\"p\",\"qty\":2},{\"name\":\"q\"}]}" with
        | .ok j => .ok j | .error e => .error (.sqlite e)))
      return (byName.compress, inserted.compress)) "cli"
  check ((cli.1.splitOn "\"count\":1").length == 2 && (cli.1.splitOn "\"parent\":3").length == 2)
    s!"rows on the child table with --eq, got {cli.1}"
  check ((cli.2.splitOn "\"items\":[{\"name\":\"p\",\"qty\":2,\"supplier\":null},{\"name\":\"q\",\"qty\":1,\"supplier\":null}]").length == 2
      && (cli.2.splitOn "\"total\":3").length == 2)
    s!"CLI insert with a nested list, got {cli.2}"

private def chunkDbPath : System.FilePath := ".lake" / "leandb_test_child_chunk.sqlite"

/-- More parents than one `IN (…)` chunk names: every list still comes back. -/
private def testChunking : IO Unit := do
  if ← chunkDbPath.pathExists then IO.FS.removeFile chunkDbPath
  let r ← withDb chunkDbPath childSchema do
    for i in [0:505] do
      discard <| insert Order (order s!"c{i}" (if i % 7 == 0 then [] else [item s!"i{i}" (i % 5 + 1), item "x" 1]))
    let all ← fetchAll Order
    unless all.size == 505 do throw (.sqlite s!"FAIL: {all.size} orders")
    for o in all do
      let i := o.id.toInt64.toNatClampNeg - 1
      let expected := if i % 7 == 0 then [] else [item s!"i{i}" (i % 5 + 1), item "x" 1]
      unless sameItems o.val.items expected do throw (.sqlite s!"FAIL: order {i} came back as {repr o.val}")
    let some big := all.find? (·.val.customer == "c503") | throw (.sqlite "FAIL: c503")
    let filtered ← select [Order] (fun o => o.val.items.any (·.qty ≥ 5))
    let reference ← selectUnplanned [Order] (fun o => o.val.items.any (·.qty ≥ 5))
    return (big.val.items.length, filtered.size, reference.size)
  let (n, m, m') ← expectOk r "chunked attach"
  check (n == 2 && m == m' && m > 0) s!"c503 has its list ({n}); the quantifier agrees with the reference ({m} vs {m'})"

private def migPath : System.FilePath := ".lake" / "leandb_test_child_mig.sqlite"

private def testMigration : IO Unit := do
  -- adding a child list is a new table; removing it drops one (destructive)
  match planMigration [Entity.spec Order] (Entity.specs Order) with
  | .ok plan =>
      check (plan.steps.map (·.describe) == ["create table \"order_items\""] && !plan.isDestructive)
        s!"adding a child list plans createTable, got {plan.steps.map (·.describe)}"
  | .error e => throw <| IO.userError s!"FAIL: planMigration add: {e}"
  match planMigration (Entity.specs Order) [Entity.spec Order] with
  | .ok plan =>
      check (plan.steps.map (·.describe) == ["DROP table \"order_items\""] && plan.destructiveAgainst (Entity.specs Order))
        s!"removing a child list plans a destructive dropTable, got {plan.steps.map (·.describe)}"
  | .error e => throw <| IO.userError s!"FAIL: planMigration remove: {e}"
  -- cascade is a DDL change: switching it is a rebuild of the child table
  let restricted : TableSpec := ⟨"order_items", (Entity.columns Order.Items).map fun c => { c with cascade := false }, #[], none⟩
  match planMigration [Entity.spec Order, restricted] (Entity.specs Order) with
  | .ok plan => check ((plan.steps.map (·.describe)).any (·.startsWith "rebuild table \"order_items\"")) "cascade change rebuilds the child"
  | .error e => throw <| IO.userError s!"FAIL: planMigration cascade: {e}"
  -- the cascade FK survives a rebuild of the parent
  if ← migPath.pathExists then IO.FS.removeFile migPath
  discard <| expectOk (← withDb migPath childSchema do
      discard <| insert Order (order "c" [item "a" 1, item "b" 2])
      discard <| insert Order (order "d" [item "e" 3])) "seed at v1"
  let v2 : List TableSpec := childSchema.map fun t =>
    if t.name == "order" then ⟨"order", t.columns.map fun c => if c.name == "customer" then { c with nullable := true } else c, #[], none⟩ else t
  let (_, report?) ← expectOk (← migrate migPath v2 (apply := true)) "rebuild the parent"
  check (((report?.map (·.applied)).getD []).any (·.startsWith "rebuild table \"order\"")) "the parent was rebuilt"
  let db ← SQLite.open migPath
  check ((← childCount db 1) == 2 && (← childCount db 2) == 1) "child rows survived the parent rebuild"
  db.exec "PRAGMA foreign_keys = ON"
  db.exec "DELETE FROM \"order\" WHERE id = 1"
  check ((← childCount db 1) == 0 && (← childCount db 2) == 1) "the cascade still fires after the rebuild"

def run : IO Unit := do
  testDerived
  testJson
  testPlans
  testEndToEnd
  testChunking
  testMigration

end ChildD

/-! ## Base descriptor: derived schema order and instance resolution -/

/-- Two entities whose derived table names collide: `UserProfile` and
    `userProfile` both become `user_profile` (`tableNameOf`). -/
structure UserProfile where
  n : String
  deriving Repr, LeanDb.Entity
structure userProfile where
  n : Nat
  deriving Repr, LeanDb.Entity

private def testBaseSpecs : IO Unit := do
  -- an already-ordered list comes back unchanged, so fingerprints do not move
  check (orderSpecs schema == schema) "orderSpecs keeps a dependency-ordered list"
  -- a referrer listed before its target is moved after it; the rest stays stable
  let reversed := [Entity.spec Book, Entity.spec Author]
  check ((orderSpecs reversed).map (·.name) == ["author", "book"]) "orderSpecs orders FK target first"
  -- duplicates (a child table listed via its parent and on its own) collapse
  let dup := [Entity.spec Author, Entity.spec Book, Entity.spec Author]
  check ((orderSpecs dup).map (·.name) == ["author", "book"]) "orderSpecs dedups by name"
  -- Base.specs is the flattened, ordered table list
  let b : Base := { name := "t", tables := [CliTable.of Book, CliTable.of Author] }
  check (b.specs.map (·.name) == ["author", "book"]) "Base.specs derives the schema"
  check (fingerprint b.specs == fingerprint schema) "Base.specs fingerprint equals the hand-written schema"
  check (b.defaultInstance == ("data" / "t.sqlite")) "default instance path"
  -- `--db` only before the verb is consumed; after the verb it is argv
  match ← Instance.resolve b ["--db", "/tmp/x.sqlite", "rows", "book"] with
  | .ok (inst, args) =>
      check (inst.path == "/tmp/x.sqlite" && args == ["rows", "book"]) "--db before the verb resolves and strips"
      check (inst.backups == ("/tmp" / "backups")) "backups dir next to the instance"
  | .error m => throw <| IO.userError s!"FAIL: --db: {m}"
  match ← Instance.resolve b ["rows", "--db", "/tmp/x.sqlite", "book"] with
  | .ok (inst, args) =>
      check (args == ["rows", "--db", "/tmp/x.sqlite", "book"])
        "--db after the verb is not stripped"
      check (inst.path == b.defaultInstance) "a mid-argv --db does not choose the instance"
  | .error m => throw <| IO.userError s!"FAIL: mid-argv --db: {m}"
  match ← Instance.resolve b ["--db", "/tmp/x.sqlite", "--", "rows", "--db", "literal"] with
  | .ok (inst, args) =>
      check (inst.path == "/tmp/x.sqlite" && args == ["rows", "--db", "literal"])
        "-- ends options; a later --db is a positional argument"
  | .error m => throw <| IO.userError s!"FAIL: --db with --: {m}"
  match ← Instance.resolve b ["--db"] with
  | .ok _ => throw <| IO.userError "FAIL: --db without a path must be refused"
  | .error _ => pure ()
  -- a usage error must not create the instance file (#29)
  let usagePath : System.FilePath := ".lake" / "leandb_test_usage_nocreate.sqlite"
  if ← usagePath.pathExists then IO.FS.removeFile usagePath
  let code ← Cli.run b ["--db", usagePath.toString, "query", "missing"]
  check (code == 3) "unknown query is a usage error"
  check (!(← usagePath.pathExists)) "a usage error must not create the instance file"
  -- UserProfile and userProfile both derive table `user_profile` (#38)
  let collide : Base := { name := "c", tables := [CliTable.of UserProfile, CliTable.of userProfile] }
  match collide.check with
  | .error e =>
      check (e.code == "schema") "colliding table names are a schema error"
      check ((e.message.splitOn "user_profile").length > 1)
        s!"the collision names the table, got {e.message}"
  | .ok () => throw <| IO.userError "FAIL: UserProfile vs userProfile must be refused"

/-! ## Sessions: a drifted instance is served, gated, and admitted after migrate -/

private def sessDbPath : System.FilePath := ".lake" / "leandb_test_session.sqlite"

private def testSession : IO Unit := do
  if ← sessDbPath.pathExists then IO.FS.removeFile sessDbPath
  let backups : System.FilePath := ".lake" / "backups"
  if ← backups.pathExists then IO.FS.removeDirAll backups
  -- an instance shaped by an older code: `author` had an extra nullable column
  let older : TableSpec := ⟨"author", #[col "name" .text, col "age" .integer,
    col "nick" .text (nullable := true)], #[], none⟩
  discard <| expectOk (← withDb sessDbPath [older] (pure ())) "create older"
  (← SQLite.open sessDbPath).exec "INSERT INTO author (name, age, nick) VALUES ('Ada', 36, 'A')"
  let b : Base := { name := "s", tables := [CliTable.of Author] }
  let inst := Instance.ofPath sessDbPath
  let sess ← expectOk (← Cli.Session.open b inst) "open a drifted instance"
  let code := fun (j : Lean.Json) => (j.getObjValAs? String "code").toOption.getD ""
  -- verbs are held back with the typed reason; version and migrate answer
  let r ← b.handle inst sess ["rows", "author"]
  check (code r == "schema_mismatch" && Cli.exitCodeOf r == 4) "drifted: rows is gated"
  let v ← b.handle inst sess ["version"]
  check ((v.getObjValAs? Bool "in_sync").toOption == some false) "drifted: version says out of sync"
  let st ← b.handle inst sess ["migrate", "status"]
  check ((st.getObjValAs? Bool "destructive").toOption == some true) "drifted: plan is destructive"
  let refused ← b.handle inst sess ["migrate", "apply"]
  check (code refused == "migrate" && Cli.exitCodeOf refused == 2) "destructive apply refused"
  check (code (← b.handle inst sess ["rows", "author"]) == "schema_mismatch") "still gated after refusal"
  let applied ← b.handle inst sess ["migrate", "apply", "--allow-destructive"]
  check ((applied.getObjValAs? Bool "ok").toOption == some true)
    s!"apply with the flag: {applied}"
  let rows ← b.handle inst sess ["rows", "author"]
  check ((rows.getObjValAs? Nat "count").toOption == some 1) "admitted after apply, data kept"
  let v ← b.handle inst sess ["version"]
  check ((v.getObjValAs? Bool "in_sync").toOption == some true
    && (v.getObjValAs? Nat "schema_version").toOption == some 2) "in sync at version 2"
  check (Cli.exitCodeOf (← b.handle inst sess ["frobnicate"]) == 3) "usage exit code"
  -- the apply took a full backup first; the journal names it
  let backup := (applied.getObjValAs? String "backup").toOption.getD ""
  check (backup.startsWith (System.FilePath.mk ".lake" / "backups" / "s-v1-").toString) s!"backup named by base/version: {backup}"
  check (← (System.FilePath.mk backup).pathExists) "backup file exists"
  check ((applied.getObjValAs? Nat "from_version").toOption == some 1
    && (applied.getObjValAs? Nat "to_version").toOption == some 2) "report carries the versions"
  let hist ← b.handle inst sess ["migrate", "history"]
  check ((hist.getObjValAs? Nat "count").toOption == some 1) "one journal row"
  -- rollback restores the pre-migration file: old shape, old version, gated again
  let rb ← b.handle inst sess ["migrate", "rollback"]
  check ((rb.getObjValAs? Bool "ok").toOption == some true
    && (rb.getObjValAs? Nat "schema_version").toOption == some 1
    && (rb.getObjValAs? Bool "in_sync").toOption == some false) s!"rollback restores v1: {rb}"
  check (code (← b.handle inst sess ["rows", "author"]) == "schema_mismatch") "gated again after rollback"
  let hist ← b.handle inst sess ["migrate", "history"]
  check ((hist.getObjValAs? Nat "count").toOption == some 1) "restored file journals the rollback"
  -- the `nick` column is back, with its data
  let dbr ← SQLite.open sessDbPath
  let st ← dbr.prepare "SELECT nick FROM author WHERE name = 'Ada'"
  discard <| st.step
  check ((← st.columnText 0) == "A") "rolled-back data intact"
  -- nothing else to roll back now; apply again without a backup
  check (code (← b.handle inst sess ["migrate", "rollback"]) == "migrate") "rollback refused without a backup"
  let again ← b.handle inst sess ["migrate", "apply", "--allow-destructive", "--no-backup"]
  check ((again.getObjValAs? Bool "ok").toOption == some true
    && (again.getObjValAs? String "backup").toOption.isNone) "--no-backup applies without one"
  check ((← b.handle inst sess ["rows", "author"] |>.map code) == "") "admitted after re-apply"
  -- explicit backup and restore
  let bk ← b.handle inst sess ["backup"]
  let bkPath := (bk.getObjValAs? String "backup").toOption.getD ""
  check (← (System.FilePath.mk bkPath).pathExists) "backup verb writes a file"
  check (code (← b.handle inst sess ["restore", ".lake/does-not-exist.sqlite"]) == "migrate") "restore refuses a missing file"
  let rs ← b.handle inst sess ["restore", bkPath]
  check ((rs.getObjValAs? Bool "in_sync").toOption == some true) "restore of a current backup stays in sync"
  check ((← b.handle inst sess ["rows", "author"] |>.map code) == "") "verbs admitted after restore"
  -- two backups in the same wall-second: the second gets a `-2` suffix
  -- (#74) instead of failing the verb
  let bk1 ← b.handle inst sess ["backup"]
  let bk2 ← b.handle inst sess ["backup"]
  let p1 := (bk1.getObjValAs? String "backup").toOption.getD ""
  let p2 := (bk2.getObjValAs? String "backup").toOption.getD ""
  check (p1 != p2) s!"two same-second backups get distinct paths: {p1} vs {p2}"
  check (p2.startsWith (System.FilePath.mk ".lake" / "backups" / "s-v2-").toString)
    s!"the second backup stays named by base/version: {p2}"
  check (← (System.FilePath.mk p2).pathExists) "the suffixed backup file exists"

/-- #78: two connections racing `ensureColumns` over the same file — the
    loser's `duplicate column name` must not fail its open. -/
private def ensureRaceDbPath : System.FilePath := ".lake" / "leandb_test_ensure_race.sqlite"

private def testEnsureColumnsRace : IO Unit := do
  if ← ensureRaceDbPath.pathExists then IO.FS.removeFile ensureRaceDbPath
  let db ← SQLite.open ensureRaceDbPath
  db.exec "CREATE TABLE _leandb_migrations (idx INTEGER PRIMARY KEY)"
  let cols := [("from_version", "INTEGER"), ("to_version", "INTEGER")]
  -- the plain idempotence: a second connection's rescan sees the columns
  -- and skips every ALTER
  ensureColumns db "_leandb_migrations" cols
  let bConn ← SQLite.open ensureRaceDbPath
  ensureColumns bConn "_leandb_migrations" cols
  -- the loser's interleave (#78), deterministically: `ensureColumns`
  -- pre-scans `table_info` once and then ALTERs each requested column in
  -- turn, so a duplicated request entry replays exactly what two
  -- concurrent first upgrades do to the loser — its second ALTER runs on
  -- a stale pre-scan that no longer knows `note` exists, fails with
  -- `duplicate column name`, and the catch's re-check must treat
  -- present = success instead of refusing a fine database. (`extra`
  -- proves the ALTER after the tolerated duplicate still really runs.)
  db.exec "CREATE TABLE _leandb_probe (id INTEGER PRIMARY KEY)"
  ensureColumns db "_leandb_probe" [("note", "TEXT"), ("note", "TEXT"), ("extra", "INTEGER")]
  let stmt ← db.prepare
    "SELECT count(*) FROM pragma_table_info('_leandb_probe') WHERE name = 'note'"
  discard <| stmt.step
  check ((← stmt.columnInt64 0) == 1) "the column exists exactly once after the duplicate"

/-- #74: with the suggested backup path and its `-2` suffix both already
    taken, the next attempt is `<base>-3` — the suffix base is computed
    once from the suggested name, not recomputed from the last attempt
    (which would compound to `…-2-3`). -/
private def backupStemDbPath : System.FilePath := ".lake" / "leandb_test_backup_stem.sqlite"

private def testBackupSuffixChain : IO Unit := do
  let dir : System.FilePath := ".lake" / "leandb_test_backup_stem"
  IO.FS.createDirAll dir
  let base := dir / "b-v1-0.sqlite"
  IO.FS.writeFile base "taken"
  IO.FS.writeFile (dir / "b-v1-0-2.sqlite") "taken"
  if ← backupStemDbPath.pathExists then IO.FS.removeFile backupStemDbPath
  -- an earlier run may have left a -3 behind: the chain must land on it
  if ← (dir / "b-v1-0-3.sqlite").pathExists then IO.FS.removeFile (dir / "b-v1-0-3.sqlite")
  let conn ← expectOk (← openDbRaw backupStemDbPath) "open the stem probe"
  let dest ← backupToUniquified conn base
  check (dest.toString.endsWith "b-v1-0-3.sqlite")
    s!"the third collision is -3, not a compounded suffix: {dest}"
  check (← dest.pathExists) "the -3 backup file was written"

/-! ## Restore safety: a bad source is refused before the instance is touched

Issue #25: `restore` used to overwrite the instance before validating the
source, destroying user data on failure and leaving the session silently
serving an empty in-memory database. -/

structure Probe where
  label : String
  deriving Repr, LeanDb.Entity

private def restoreDbPath : System.FilePath := ".lake" / "leandb_test_restore.sqlite"

private def testRestoreSafety : IO Unit := do
  if ← restoreDbPath.pathExists then IO.FS.removeFile restoreDbPath
  let garbage : System.FilePath := ".lake" / "leandb_test_restore_garbage.txt"
  IO.FS.writeFile garbage "dear instance, I am not a database"
  let dir : System.FilePath := ".lake" / "leandb_test_restore_dir"
  unless ← dir.pathExists do IO.FS.createDir dir
  -- the magic check, pure: text, a truncated header, the real magic
  check (!Restore.headerOk "definitely not sqlite".toUTF8) "magic check rejects text"
  check (!Restore.headerOk "SQLite format 3".toUTF8) "magic check rejects a truncated header"
  check (Restore.headerOk Restore.magic) "magic check accepts the magic"
  discard <| expectOk (← withDb restoreDbPath [Entity.spec Probe] (pure ()))
    "create the restore probe"
  let head ← IO.FS.readBinFile restoreDbPath
  check (Restore.headerOk (head.extract 0 16)) "a real instance carries the magic header"
  let b : Base := { name := "r", tables := [CliTable.of Probe] }
  let inst := Instance.ofPath restoreDbPath
  let sess ← expectOk (← Cli.Session.open b inst) "open the probe"
  discard <| b.handle inst sess ["insert", "probe", "{\"label\":\"keep\"}"]
  let before ← IO.FS.readBinFile restoreDbPath
  -- a garbage source: refused with a typed error, the live session and
  -- the instance file untouched
  let refused ← b.handle inst sess ["restore", garbage.toString]
  check ((refused.getObjValAs? Bool "ok").toOption == some false) s!"garbage restore refused: {refused}"
  check ((refused.getObjValAs? String "code").toOption == some "migrate")
    s!"garbage restore is a typed migrate error: {refused}"
  let rows ← b.handle inst sess ["rows", "probe"]
  check ((rows.getObjValAs? Nat "count").toOption == some 1) s!"session still serves the live data: {rows}"
  check ((← IO.FS.readBinFile restoreDbPath) == before) "garbage restore left the instance file untouched"
  -- a directory as source: refused the same way
  let refusedDir ← b.handle inst sess ["restore", dir.toString]
  check ((refusedDir.getObjValAs? Bool "ok").toOption == some false)
    s!"directory restore refused: {refusedDir}"
  let rowsDir ← b.handle inst sess ["rows", "probe"]
  check ((rowsDir.getObjValAs? Nat "count").toOption == some 1)
    "session still serves the live data after a directory source"
  check ((← IO.FS.readBinFile restoreDbPath) == before) "directory restore left the instance file untouched"
  -- the happy path is unchanged: backup, insert more, restore back
  let bk ← b.handle inst sess ["backup"]
  let bkPath := (bk.getObjValAs? String "backup").toOption.getD ""
  discard <| b.handle inst sess ["insert", "probe", "{\"label\":\"extra\"}"]
  let rs ← b.handle inst sess ["restore", bkPath]
  check ((rs.getObjValAs? Bool "ok").toOption == some true) s!"restore of a valid backup succeeds: {rs}"
  let rows ← b.handle inst sess ["rows", "probe"]
  check ((rows.getObjValAs? Nat "count").toOption == some 1) "the restored instance holds the backup's rows"

private def resilienceDbPath : System.FilePath := ".lake" / "leandb_test_restore_resilience.sqlite"

/-- #59/#77: restore failure paths leave the session consistent. The
    transient case (first reopen fails, retry succeeds) cannot be forced
    deterministically, so the gate recompute is proven on the reachable
    paths: an early failure touches neither gate nor dead flag, and a
    successful swap always re-derives the gate from the connection that
    was actually installed. The deterministic stand-in for a reopen that
    fails twice is a valid SQLite source whose `_leandb_log` is a VIEW:
    validation (magic + quick_check) passes, the swap happens, and both
    `openDbRaw` attempts then fail on the `CREATE TABLE IF NOT EXISTS`. -/
private def testRestoreResilience : IO Unit := do
  if ← resilienceDbPath.pathExists then IO.FS.removeFile resilienceDbPath
  let poison : System.FilePath := ".lake" / "leandb_test_restore_poison.sqlite"
  if ← poison.pathExists then IO.FS.removeFile poison
  let garbage : System.FilePath := ".lake" / "leandb_test_restore_res_garbage.txt"
  IO.FS.writeFile garbage "dear instance, I am not a database"
  let other : System.FilePath := ".lake" / "leandb_test_restore_other.sqlite"
  if ← other.pathExists then IO.FS.removeFile other
  let b : Base := { name := "rr", tables := [CliTable.of Probe] }
  let inst := Instance.ofPath resilienceDbPath
  discard <| expectOk (← withDb resilienceDbPath [Entity.spec Probe] (pure ())) "create the live instance"
  let sess ← expectOk (← Cli.Session.open b inst) "open the live instance"
  discard <| b.handle inst sess ["insert", "probe", "{\"label\":\"live\"}"]
  let bk ← b.handle inst sess ["backup"]
  let bkPath := (bk.getObjValAs? String "backup").toOption.getD ""
  let code := fun (j : Lean.Json) => (j.getObjValAs? String "code").toOption.getD ""
  -- an early failure (no swap) poisons nothing: the gate and the dead
  -- flag stay as they were, and the session still serves its data
  let refused ← b.handle inst sess ["restore", garbage.toString]
  check (code refused == "migrate") s!"garbage source refused: {refused}"
  check ((← sess.gate.get).isNone && (← sess.dead.get).isNone) "an early failure poisons nothing"
  let rows ← b.handle inst sess ["rows", "probe"]
  check ((rows.getObjValAs? Nat "count").toOption == some 1) "session still serves the live data"
  -- a successful swap re-derives the gate from the installed connection:
  -- a foreign-schema file restores, but the session is gated for drift
  discard <| expectOk (← withDb other [Entity.spec Author] (pure ())) "create a foreign-schema source"
  let drifted ← b.handle inst sess ["restore", other.toString]
  check ((drifted.getObjValAs? Bool "ok").toOption == some true) s!"restore of the foreign file succeeds: {drifted}"
  check ((drifted.getObjValAs? Bool "in_sync").toOption == some false) "the recomputed gate says out of sync"
  let rows ← b.handle inst sess ["rows", "probe"]
  check (code rows == "schema_mismatch") "the session is gated by the recomputed gate"
  let back ← b.handle inst sess ["restore", bkPath]
  check ((back.getObjValAs? Bool "ok").toOption == some true
    && (back.getObjValAs? Bool "in_sync").toOption == some true) s!"restore back: {back}"
  -- the reopen that fails twice: the poison source swaps in, then both
  -- `openDbRaw` attempts fail — the gate is set, and the dead flag marks
  -- the session as serving the old unlinked inode
  let pdb ← SQLite.open poison
  pdb.exec "CREATE TABLE filler (x INTEGER)"
  pdb.exec "CREATE VIEW _leandb_log AS SELECT 1"
  let dead ← b.handle inst sess ["restore", poison.toString]
  check ((dead.getObjValAs? Bool "ok").toOption == some false
    && code dead == "sqlite") s!"post-swap reopen failure reported: {dead}"
  check ((← sess.dead.get).isSome) "both reopens failing sets the dead flag"
  check (code (← b.handle inst sess ["version"]) == "sqlite") "version refuses on a dead session (#77)"
  check (code (← b.handle inst sess ["backup"]) == "sqlite") "backup refuses on a dead session"
  check (code (← b.handle inst sess ["migrate", "status"]) == "sqlite") "migrate refuses on a dead session"
  let gated ← b.handle inst sess ["rows", "probe"]
  check (code gated == "sqlite") "gated verbs answer the gate error"

private def boundaryDbPath : System.FilePath := ".lake" / "leandb_test_boundary.sqlite"

/-- #73: a raw IO exception inside a verb comes back as `ok:false` JSON —
    one bad query must not kill the serve/MCP loops or drop the HTTP
    response. Dropping the journal table under the session's feet (via a
    second connection) makes `migrate history`'s raw `conn.raw.prepare`
    throw "no such table". -/
private def testHandleBoundary : IO Unit := do
  if ← boundaryDbPath.pathExists then IO.FS.removeFile boundaryDbPath
  let b : Base := { name := "xb", tables := [CliTable.of Probe] }
  discard <| expectOk (← withDb boundaryDbPath [Entity.spec Probe] (pure ())) "create the boundary instance"
  let inst := Instance.ofPath boundaryDbPath
  let sess ← expectOk (← Cli.Session.open b inst) "open"
  let v ← b.handle inst sess ["version"]
  check ((v.getObjValAs? Bool "ok").toOption == some true) "normal verbs answer"
  (← SQLite.open boundaryDbPath).exec "DROP TABLE _leandb_migrations"
  -- must not throw: the boundary catch turns the raw error into JSON
  let r ← b.handle inst sess ["migrate", "history"]
  check ((r.getObjValAs? Bool "ok").toOption == some false
    && (r.getObjValAs? String "code").toOption == some "sqlite")
    s!"an escaped IO error comes back as ok:false JSON: {r}"
  let v2 ← b.handle inst sess ["version"]
  check ((v2.getObjValAs? Bool "ok").toOption == some true) "the session keeps serving after the caught failure"

/-! ## Chains: a typed transform carries rows the mechanical diff refuses -/

/-- `author` as stored at V0 (what `migrate freeze` would generate). -/
structure V0Author where
  name : String
  age : Int64
  deriving Repr, LeanDb.Entity


/-- #76: `restore` refuses with a typed `busy` error while another
    process holds the instance's write transaction, and the refusal
    destroys nothing; once the writer is gone the same restore succeeds. -/
private def testRestoreWriterGuard : IO Unit := do
  if ← restoreDbPath.pathExists then IO.FS.removeFile restoreDbPath
  discard <| expectOk (← withDb restoreDbPath [Entity.spec Probe] (pure ()))
    "create the guard probe"
  let b : Base := { name := "r", tables := [CliTable.of Probe] }
  let inst := Instance.ofPath restoreDbPath
  let sess ← expectOk (← Cli.Session.open b inst) "open the guard probe"
  discard <| b.handle inst sess ["insert", "probe", "{\"label\":\"keep\"}"]
  -- a valid source, so the refusal can only come from the writer guard
  let bk ← b.handle inst sess ["backup"]
  let bkPath := (bk.getObjValAs? String "backup").toOption.getD ""
  -- a second connection takes the write transaction and holds it
  let other ← SQLite.open restoreDbPath
  other.exec "BEGIN IMMEDIATE"
  other.exec "INSERT INTO probe (label) VALUES ('writer')"
  let refused ← b.handle inst sess ["restore", bkPath]
  check ((refused.getObjValAs? Bool "ok").toOption == some false)
    s!"restore refused under a foreign writer: {refused}"
  check ((refused.getObjValAs? String "code").toOption == some "busy")
    s!"the refusal is a typed busy error: {refused}"
  let msg := (refused.getObjValAs? String "message").toOption.getD ""
  check ((msg.splitOn "writer").length > 1) s!"the refusal names the writer: {refused}"
  -- the refused swap destroyed nothing: the writer's transaction is
  -- still intact and commits, and the session then serves its row
  other.exec "COMMIT"
  let rows ← b.handle inst sess ["rows", "probe"]
  check ((rows.getObjValAs? Nat "count").toOption == some 2)
    s!"the foreign writer's row survived the refused swap: {rows}"
  -- and once no writer is active, the same restore succeeds
  let rs ← b.handle inst sess ["restore", bkPath]
  check ((rs.getObjValAs? Bool "ok").toOption == some true)
    s!"restore succeeds once the writer is gone: {rs}"
  let restored ← b.handle inst sess ["rows", "probe"]
  check ((restored.getObjValAs? Nat "count").toOption == some 1)
    s!"the restored instance holds the backup's rows: {restored}"

/-- V1: `age` becomes a closed `Cohort`, NOT NULL without a default — the
    diff refuses it; the transform decides. -/
inductive Cohort where
  | young | senior
  deriving Repr, DecidableEq, Ord, LeanDb.ClosedEnum

structure AuthorV1 where
  name : String
  cohort : Cohort
  deriving Repr, LeanDb.Entity

private def chainDbPath : System.FilePath := ".lake" / "leandb_test_chain.sqlite"

private def testChain : IO Unit := do
  if ← chainDbPath.pathExists then IO.FS.removeFile chainDbPath
  let v0 : List TableSpec := [Entity.spec Author]
  -- the V1 snapshot keeps the table name `author` with the new columns
  let v1 : List TableSpec := [{ Entity.spec AuthorV1 with name := "author" }]
  let toV1 : V0Author → Except String AuthorV1 := fun old =>
    if old.age < 0 then .error s!"negative age {old.age}"
    else .ok { name := old.name, cohort := if old.age ≥ 50 then .senior else .young }
  let migration : Migration := {
    fromFingerprint := fingerprint v0
    toFingerprint := fingerprint v1
    snapshot := v1
    steps := [Step.transformT V0Author AuthorV1 toV1 (table := "author")] }
  let chain : Chain := { origin := v0, migrations := [migration] }
  -- the chain checks against the head schema, and refuses a stale one
  if let .error m := chain.check v1 then throw <| IO.userError s!"FAIL: chain head is v1: {m}"
  match chain.check v0 with
  | .ok () => throw <| IO.userError "FAIL: chain.check must refuse a stale head"
  | .error m => check (m.startsWith "the code's schema") s!"stale head named: {m}"
  -- refusals name the table; covering it lets the plan through
  check ((Freeze.refusals v0 v1).map (·.1) == ["author"]) "refusal names author"
  check ((planMigration v0 v1).toOption.isNone) "uncovered plan refuses"
  check ((planMigration v0 v1 ["author"]).toOption.isSome) "covered plan rebuilds"
  -- an instance at V0 with rows
  discard <| expectOk (← withDb chainDbPath v0 do
    discard <| insert Author ⟨"Ada", 36⟩
    discard <| insert Author ⟨"Grace", 85⟩) "seed at v0"
  let conn ← expectOk (← openDbRaw chainDbPath) "open raw"
  check ((chain.versionOf? (fingerprint v0)) == some 0) "instance fingerprint is V0"
  -- apply: the transform rewrites both rows, keeping ids
  let r ← expectOk (← migration.applyOn conn v0 1 (allowDestructive := true) none) "apply V0→V1"
  check (r.applied.any (·.startsWith "transform rows of \"author\"") && r.applied.any (fun a => (a.splitOn ": 2 rows").length == 2))
    s!"transform applied to 2 rows: {r.applied}"
  check (r.fromVersion == some 0 && r.toVersion == some 1) "versions journaled"
  let (fp, ver) ← instanceInfoOn conn
  check (fp == some (fingerprint v1) && ver == some 1) "instance now at V1"
  let db ← SQLite.open chainDbPath
  let st ← db.prepare "SELECT id, name, cohort FROM author ORDER BY id"
  let mut rows : Array (Int64 × String × String) := #[]
  repeat
    if ← st.step then rows := rows.push (← st.columnInt64 0, ← st.columnText 1, ← st.columnText 2)
    else break
  check (rows == #[(1, "Ada", "young"), (2, "Grace", "senior")]) s!"rows transformed with ids kept: {rows}"
  -- a rejecting transform aborts the whole migration: nothing changes
  if ← chainDbPath.pathExists then IO.FS.removeFile chainDbPath
  discard <| expectOk (← withDb chainDbPath v0 do
    discard <| insert Author ⟨"Ada", 36⟩
    discard <| insert Author ⟨"Bad", 0⟩) "seed again"
  (← SQLite.open chainDbPath).exec "UPDATE author SET age = -1 WHERE name = 'Bad'"
  let conn ← expectOk (← openDbRaw chainDbPath) "open raw again"
  match ← migration.applyOn conn v0 1 (allowDestructive := true) none with
  | .ok _ => throw <| IO.userError "FAIL: a rejecting transform must abort"
  | .error e =>
      check ((e.message.splitOn "row 2 of \"author\": negative age -1").length == 2) s!"names the row: {e.message}"
  let (fp, _) ← instanceInfoOn conn
  check (fp == some (fingerprint v0)) "still at V0 after the abort"
  check ((← rowCountOf chainDbPath) == 2) "rows untouched after the abort"
where
  rowCountOf (p : System.FilePath) : IO Nat := do
    let st ← (← SQLite.open p).prepare "SELECT COUNT(*) FROM author"
    if ← st.step then return (← st.columnInt64 0).toNatClampNeg else return 0


private def adoptDbPath : System.FilePath := ".lake" / "leandb_test_adopt.sqlite"

private def colRating : ColumnSpec := (Entity.spec Book).columns.getD 2 default

private def testStrictSchemaJson : IO Unit := do
  -- a valid spec still round-trips byte for byte
  let c := Entity.spec Book
  for col in c.columns do
    check ((ColumnSpec.fromJson? col.toJson).toOption == some col) s!"ColumnSpec round trip: {col.name}"
  -- a present-but-malformed optional is an ERROR, not an absence: the
  -- lossy decode would make migrate diff a schema that was never stored
  let bad : List (String × Lean.Json) := [
    ("references", Lean.Json.num 3),
    ("enum", Lean.Json.arr #[Lean.Json.str "a", Lean.Json.num 1]),
    ("enumSet", Lean.Json.arr #[Lean.Json.bool true]),
    ("default", Lean.Json.str "junk"),
    ("shape", Lean.Json.num 7),
    ("group", Lean.Json.arr #[]),
    ("cascade", Lean.Json.str "yes")]
  for (key, v) in bad do
    let j := (colRating.toJson).mergeObj (Lean.Json.mkObj [(key, v)])
    check ((ColumnSpec.fromJson? j).isOk == false) s!"malformed \"{key}\" is refused, not dropped"
  -- an ABSENT optional is still fine, and the untouched spec round-trips
  check ((ColumnSpec.fromJson? colRating.toJson).toOption == some colRating)
    "the untouched spec decodes"

/-- An adopted file keeps whatever declared types it was created with:
    BIGINT, VARCHAR — affinity synonyms of INTEGER and TEXT. The snapshot
    records the canonical spelling, so `matchesSnapshot` must normalize by
    SQLite's affinity rules; a raw string comparison matches no version,
    the file is stamped at the head, and the migrations in between
    silently never run. -/
private def foreignDbPath : System.FilePath := ".lake" / "leandb_test_foreign.sqlite"

/-- A file no LeanDB engine ever created — user tables, no schema meta —
    must be refused at open, not silently stamped as this base's
    instance: the stamped metadata would lie, later verbs would fail with
    raw SQL errors instead of a typed mismatch, and `migrate` would plan
    from a phantom baseline. -/
private def testForeignFileRefused : IO Unit := do
  if ← foreignDbPath.pathExists then IO.FS.removeFile foreignDbPath
  let db ← SQLite.open foreignDbPath
  db.exec "CREATE TABLE user (weird_col BLOB NOT NULL)"
  db.exec "INSERT INTO user VALUES (x'00')"
  let r ← openDb foreignDbPath schema
  expectErr r "migrate" "a foreign file with tables is refused, not adopted silently"
  match r with
  | .error e =>
      check ((e.message.splitOn "import-sqlite").length > 1) s!"the refusal points at import-sqlite, got {e.message}"
  | .ok _ => pure ()
  let stamped ← (← SQLite.open foreignDbPath).prepare "SELECT COUNT(*) FROM _leandb_meta"
  discard <| stamped.step
  check ((← stamped.columnInt64 0) == 0) "no meta was stamped onto the foreign file"
  -- a fresh file still opens and stamps normally
  if ← foreignDbPath.pathExists then IO.FS.removeFile foreignDbPath
  discard <| expectOk (← withDb foreignDbPath schema do discard <| insert Author ⟨"Ada", 36⟩)
    "a fresh file opens and stamps"

private def testAdoptAffinity : IO Unit := do
  if ← adoptDbPath.pathExists then IO.FS.removeFile adoptDbPath
  let colX : ColumnSpec := { name := "x", sqlType := .integer, nullable := false, fkTable := none }
  let colT : ColumnSpec := { name := "t", sqlType := .text, nullable := false, fkTable := none }
  let v0 : List TableSpec := [⟨"t", #[colX, colT], #[], none⟩]
  -- V1: one more column, nullable — a mechanical, non-destructive step
  let colZ : ColumnSpec := { name := "z", sqlType := .text, nullable := true, fkTable := none }
  let v1 : List TableSpec := [⟨"t", #[colX, colT, colZ], #[], none⟩]
  let mig : Migration :=
    { fromFingerprint := (fingerprint v0), toFingerprint := (fingerprint v1), snapshot := v1 }
  let chain : Chain := { origin := v0, migrations := [mig] }
  -- the imported file, with affinity-synonym declared types
  let db ← SQLite.open adoptDbPath
  db.exec "CREATE TABLE t (id INTEGER PRIMARY KEY AUTOINCREMENT, x BIGINT NOT NULL, t VARCHAR(20) NOT NULL)"
  db.exec "INSERT INTO t (x, t) VALUES (1, 'a')"
  let conn ← expectOk (← openDbRaw adoptDbPath) "open the adopted file raw"
  let adopted ← chain.adopt conn
  check (adopted == some 0) s!"the BIGINT/VARCHAR file is adopted at V0, got {repr adopted}"
  -- the pending V0→V1 step is now visible and applies mechanically
  let r ← expectOk (← migrateOn conn v1 { apply := true }) "apply the pending step"
  check (r.2.map (·.fingerprint) == some (fingerprint v1)) "instance moved to V1"
  let st ← (← SQLite.open adoptDbPath).prepare "SELECT z FROM t WHERE id = 1"
  discard <| st.step
  check ((← st.columnType 0) == .null) "the added column is NULL for the old row"
/-! ## Footprints: what a query reads, statically; the log as data; impact -/

/-- A query over both fixtures: a join, a null test, and a residual. -/
def unratedByAuthor (a : Ref Author) : DbM (Array (Stored Book × Stored Author)) :=
  select [Book, Author]
    (fun (b, au) => b.val.author == au.ref && au.ref == a && b.val.rating.isNone
      && b.val.title.length > 3)
    (.key fun (b, _) => b.val.title)

private def fpDbPath : System.FilePath := ".lake" / "leandb_test_footprint.sqlite"

private def testFootprints : IO Unit := do
  let q : QueryEntry := query% unratedByAuthor
  -- static: recorded by the tactic under the def, read by query%
  check (q.params == [("a", "Ref Author")]) s!"params: {q.params}"
  let f := q.footprint
  check (f.columns.contains ("Book", "author") && f.columns.contains ("Book", "rating")
    && f.columns.contains ("Author", "id")) s!"static footprint columns: {f.columns}"
  check (f.residual) "the title-length conjunct is residual"
  -- resolved against the base: type names become table names
  let b : Base := { name := "fp", tables := [CliTable.of Author, CliTable.of Book], queries := [q] }
  let r := b.resolveFootprint f
  check (r.columns.contains ("book", "rating") && r.tables.contains "author") s!"resolved: {r.columns}"
  -- run it under its name: the log stores the plan as data, attributed
  if ← fpDbPath.pathExists then IO.FS.removeFile fpDbPath
  let inst := Instance.ofPath fpDbPath
  let sess ← expectOk (← Cli.Session.open b inst) "open"
  let ada ← b.handle inst sess ["insert", "author", "{\"name\":\"Ada\",\"age\":36}"]
  let adaId := ((ada.getObjVal? "row" >>= (·.getObjValAs? Nat "id")).toOption.getD 0)
  discard <| b.handle inst sess ["insert", "book", s!"\{\"title\":\"Notes\",\"author\":{adaId}}"]
  let res ← b.handle inst sess ["query", "unratedByAuthor", toString adaId]
  check ((res.getObjValAs? Bool "ok").toOption == some true) s!"query ran: {res}"
  let log ← b.handle inst sess ["log", "1"]
  let entry := ((log.getObjValAs? (Array Lean.Json) "entries").toOption.getD #[])[0]!
  check ((entry.getObjValAs? String "query").toOption == some "unratedByAuthor") s!"log names the query: {entry}"
  let plan := (entry.getObjVal? "plan").toOption.getD Lean.Json.null
  check ((plan.getObjVal? "footprint" >>= (·.getObjValAs? (Array String) "columns")).toOption.getD #[] |>.contains "book.rating")
    s!"log footprint has book.rating: {plan}"
  check ((plan.getObjVal? "plan" >>= (·.getObjValAs? String "kind")).toOption == some "and") s!"plan stored as data: {plan}"
  -- the insert was not attributed to a query
  let log ← b.handle inst sess ["log", "3"]
  let entries := (log.getObjValAs? (Array Lean.Json) "entries").toOption.getD #[]
  check (entries.any fun e => (e.getObjValAs? String "verb").toOption == some "insert"
    && (e.getObjVal? "query").toOption == some Lean.Json.null) "inserts carry no query name"
  -- changed columns: drop book.rating (a base without it)
  let v2Book : TableSpec := { Entity.spec Book with columns := (Entity.spec Book).columns.filter (·.name != "rating") }
  let changed := Cli.changedColumns b.specs [Entity.spec Author, v2Book]
  check (changed == [("book", "rating")]) s!"changed columns: {changed}"
  check ((Cli.changedColumns b.specs [Entity.spec Author]) == [("book", "*")]) "dropped table touches everything"
  -- impact: a base whose Book lost its rating column sees the query and its logged run
  let b2 : Base := { name := "fp", tables := [CliTable.of Author, CliTable.of Marker], queries := [q] }
  let sess2 ← expectOk (← Cli.Session.open b2 inst) "open under the changed base"
  let st ← b2.handle inst sess2 ["migrate", "status"]
  let impact := (st.getObjValAs? (Array Lean.Json) "impact").toOption.getD #[]
  check (impact.any fun i => (i.getObjValAs? String "query").toOption == some "unratedByAuthor"
      && (i.getObjValAs? Nat "logged_runs").toOption == some 1) s!"impact names the query and its run: {st}"
  check (((st.getObjValAs? (Array String) "changed").toOption.getD #[]).contains "book.*") s!"changed lists book.*: {st}"
  -- The historical window is explicit, and static impact survives a disabled scan.
  for _ in [0:2] do
    discard <| b.handle inst sess ["query", "unratedByAuthor", toString adaId]
  let limited := { b2 with log := { impactLimit := 1 } }
  let limitedSess ← expectOk (← Cli.Session.open limited inst) "open with an impact budget"
  let limitedStatus ← limited.handle inst limitedSess ["migrate", "status"]
  let window := (limitedStatus.getObjVal? "impact_log").toOption.getD .null
  check ((window.getObjValAs? Nat "limit").toOption == some 1 &&
    (window.getObjValAs? Nat "scanned").toOption == some 1 &&
    (window.getObjValAs? Bool "truncated").toOption == some true) s!"bounded impact window: {limitedStatus}"
  let limitedImpact := (limitedStatus.getObjValAs? (Array Lean.Json) "impact").toOption.getD #[]
  check (limitedImpact.any fun i => (i.getObjValAs? Nat "logged_runs").toOption == some 1)
    "impact counts only the recent window"
  let staticOnly := { b2 with log := { impactLimit := 0 } }
  let staticSess ← expectOk (← Cli.Session.open staticOnly inst) "open with historical scans disabled"
  let staticStatus ← staticOnly.handle inst staticSess ["migrate", "status"]
  let staticImpact := (staticStatus.getObjValAs? (Array Lean.Json) "impact").toOption.getD #[]
  check (staticImpact.any fun i => (i.getObjValAs? String "query").toOption == some "unratedByAuthor" &&
    (i.getObjValAs? Nat "logged_runs").toOption == some 0) "static impact does not depend on history"
  let unchanged ← b.handle inst sess ["migrate", "status"]
  check ((unchanged.getObjVal? "impact_log").toOption.isNone &&
    ((unchanged.getObjValAs? (Array String) "notes").toOption.getD #[]).contains "schema already up to date")
    "an unchanged schema returns before computing impact"
  let migration : Migration := {
    fromFingerprint := fingerprint b.specs
    toFingerprint := fingerprint b2.specs
    snapshot := b2.specs }
  let chained := { limited with chain := some { origin := b.specs, migrations := [migration] } }
  let chainSess ← expectOk (← Cli.Session.open chained inst) "open versioned impact fixture"
  let chainStatus ← chained.handle inst chainSess ["migrate", "status"]
  let chainWindow := (chainStatus.getObjVal? "impact_log").toOption.getD .null
  check ((chainWindow.getObjValAs? Nat "scanned").toOption == some 1 &&
    (chainWindow.getObjValAs? Bool "truncated").toOption == some true) s!"chain impact is bounded too: {chainStatus}"

private def testLogPolicy : IO Unit := do
  let .ok defaults := LogConfig.ofSettings {} none none | throw <| IO.userError "default log config failed"
  check (defaults.maxEntries.isNone && defaults.impactLimit == 1000) "preserve history by default"
  let .ok overrides := LogConfig.ofSettings { maxEntries := some 9 } (some "unlimited") (some "0") |
    throw <| IO.userError "log overrides failed"
  check (overrides.maxEntries.isNone && overrides.impactLimit == 0) "explicit unlimited and zero scan"
  for s in ["", "-1", "oops", "9223372036854775807", "18446744073709551616"] do
    check ((LogConfig.ofSettings {} (some s) none).toOption.isNone) s!"bad retention {s}"
    check ((LogConfig.ofSettings {} none (some s)).toOption.isNone) s!"bad impact limit {s}"
  let path : System.FilePath := ".lake/leandb_test_log_policy.sqlite"
  if ← path.pathExists then IO.FS.removeFile path
  let conn ← expectOk (← openDb path schema) "open log-policy fixture"
  for id in [2, 5, 9, 17, 30] do
    conn.raw.exec s!"INSERT INTO _leandb_log(id,verb,detail,ok,rows) VALUES ({id},'insert','fixture',1,0)"
  let reopened ← expectOk (← openDbRaw path) "reopen with default retention"
  check ((← expectOk (← (readLog 10).run reopened) "default history").size == 5) "default open never prunes"
  let conn ← expectOk (← openDb path schema { maxEntries := some 3 }) "open with retention"
  let kept ← expectOk (← (readLog 10).run conn) "retained history"
  check (kept.map (fun j => (j.getObjValAs? Nat "id").toOption.getD 0) == #[30, 17, 9])
    "retention keeps the newest entries despite id gaps"
  for i in [0:7] do
    discard <| expectOk (← (insert Author ⟨s!"author-{i}", i⟩).run conn) "logged write"
    let entries ← expectOk (← (readLog 10).run conn) "batched retention"
    check (entries.size <= 5) "a long-lived connection stays within its retention batch"
  let entries ← expectOk (← (readLog 10).run conn) "history after seven writes"
  check (entries.size == 4) "retention runs repeatedly without reopening"
  let removed ← expectOk (← (pruneLog 1).run conn) "manual prune"
  check (removed == 3) "manual prune returns the deleted count"
  check ((← expectOk (← (fetchAll Author).run conn) "application rows").size == 7)
    "pruning never deletes application data"
  let b : Base := { name := "log_policy", tables := [CliTable.of Author, CliTable.of Book] }
  let inst := Instance.ofPath path
  let sess ← expectOk (← Cli.Session.open b inst) "CLI log session"
  let cleared ← b.handle inst sess ["log", "prune", "0"]
  check ((cleared.getObjValAs? Nat "deleted").toOption == some 1) "CLI can clear history explicitly"
  let bad ← b.handle inst sess ["log", "prune", "-1"]
  check ((bad.getObjValAs? String "code").toOption == some "usage") "invalid prune is a usage error"
  discard <| expectOk (← (insert Author ⟨"before-disable", 1⟩).run conn) "write before disabling logs"
  let disabled ← expectOk (← openDb path schema { maxEntries := some 0 }) "disable logging"
  discard <| expectOk (← (insert Author ⟨"no-log", 1⟩).run disabled) "writes still work without logs"
  check ((← expectOk (← (readLog 10).run disabled) "disabled history").isEmpty) "zero clears and disables logs"
  -- Only select plans enter the scan; the one-row lookahead is not parsed.
  let plan := "{\"footprint\":{\"columns\":[\"author.age\"]}}"
  for q in ["old", "new"] do
    let st ← disabled.raw.prepare "INSERT INTO _leandb_log(verb,detail,ok,rows,query,plan) VALUES ('select','fixture',1,0,?,?)"
    st.bindText 1 q
    st.bindText 2 plan
    st.exec
  disabled.raw.exec "INSERT INTO _leandb_log(verb,detail,ok,rows,plan) VALUES ('insert','ignored',1,0,'not-json')"
  let scan ← scanLogFootprints disabled 1
  check (scan.entries == #[(some "new", [("author", "age")])] && scan.truncated)
    "scan counts select plans only, newest first, with truncation"
  let exact ← scanLogFootprints disabled 2
  check (exact.entries.size == 2 && !exact.truncated) "exact window is not truncated"
  let zero ← scanLogFootprints disabled 0
  check (zero.entries.isEmpty && zero.truncated) "zero scan parses no plans"
  -- Restoring reopens the file with the base's policy, not the raw defaults.
  let backup : System.FilePath := ".lake/leandb_test_log_policy_backup.sqlite"
  if ← backup.pathExists then IO.FS.removeFile backup
  backupTo disabled backup
  let retainedBase := { b with log := { maxEntries := some 1, impactLimit := 2 } }
  let retainedSess ← expectOk (← Cli.Session.open retainedBase inst) "configured restore session"
  let restored ← retainedBase.handle inst retainedSess ["restore", backup.toString]
  check ((restored.getObjValAs? Bool "ok").toOption == some true) s!"restore: {restored}"
  let restoredConn ← retainedSess.conn.get
  check (restoredConn.logConfig.maxEntries == some 1 && restoredConn.logConfig.impactLimit == 2)
    "restore preserves configured limits"
  check ((← expectOk (← (readLog 10).run restoredConn) "restored log").size == 1)
    "restore reapplies retention to restored history"

private def testHttpBodyLimits : IO Unit := do
  check ((Http.bodyLimitOf none).toOption == some (2 * 1024 * 1024)) "HTTP default body limit"
  check ((Http.bodyLimitOf (some "4096")).toOption == some 4096) "HTTP body limit override"
  for s in ["", "0", "-1", "1.5", "oops"] do
    check ((Http.bodyLimitOf (some s)).toOption.isNone) s!"invalid HTTP limit {s}"
  let calls ← IO.mkRef (0 : Nat)
  let resolve : Http.Resolver := fun segs => return .ok (segs, "test", fun _ => do
    calls.modify (· + 1)
    return Lean.Json.mkObj [("ok", .bool true)])
  let handler := Http.handleRequestWithLimit 8 (.bearer "test-token") resolve
  let config := Http.serverConfig 8
  let reqPrefix := "POST /rpc HTTP/1.1\r\nHost: localhost\r\nContent-Type: application/json\r\nConnection: close\r\n"
  let auth := "Authorization: Bearer test-token\r\n"
  let run := fun (name raw status : String) (cfg : Std.Http.Config) => do
    Std.Http.Internal.Test.checkClose name raw handler
      (fun bytes => Std.Http.Internal.Test.assertStatus bytes s!"HTTP/1.1 {status}") cfg
  -- A valid JSON body exactly at the boundary still dispatches.
  run "body at limit" (reqPrefix ++ auth ++ "Content-Length: 8\r\n\r\n[\"help\"]") "200" config
  check ((← calls.get) == 1) "accepted body dispatched once"
  -- Reject from the headers, without waiting for or allocating the body.
  run "oversized content length" (reqPrefix ++ auth ++ "Content-Length: 9\r\n\r\n") "413" config
  -- Each chunk fits, but the sum does not.
  run "cumulative chunk limit" (reqPrefix ++ auth ++ "Transfer-Encoding: chunked\r\n\r\n5\r\n[\"hel\r\n4\r\np\"] \r\n0\r\n\r\n") "413" config
  run "valid prefix of rejected body" (reqPrefix ++ auth ++ "Transfer-Encoding: chunked\r\n\r\n8\r\n[\"help\"]\r\n1\r\n \r\n0\r\n\r\n") "413" config
  run "oversized chunk header" (reqPrefix ++ auth ++ "Transfer-Encoding: chunked\r\n\r\n800001\r\n") "413" config
  -- Direct handler users can supply a looser parser configuration. The
  -- handler still refuses before parsing or dispatching the oversized body.
  run "handler body budget" (reqPrefix ++ auth ++ "Content-Length: 9\r\n\r\n[\"help\"] ") "413" (Http.serverConfig 32)
  run "auth before JSON parsing" (reqPrefix ++ "Content-Length: 8\r\n\r\nnot-json") "401" config
  check ((← calls.get) == 1) "rejected requests never dispatched"
  -- Host / Origin / Content-Type (#40)
  check (Http.isLoopbackHost "127.0.0.1" && Http.isLoopbackHost "localhost")
    "loopback names"
  check (!Http.isLoopbackHost "0.0.0.0" && !Http.isLoopbackHost "evil.example")
    "non-loopback names"
  check (Http.hostAllowed "127.0.0.1" "localhost:7411") "Host localhost is loopback"
  check (!Http.hostAllowed "127.0.0.1" "evil.example") "a foreign Host is refused"
  check (Http.originAllowed "127.0.0.1" none) "missing Origin is allowed"
  check (Http.originAllowed "127.0.0.1" (some "http://127.0.0.1:9")) "loopback Origin"
  check (!Http.originAllowed "127.0.0.1" (some "http://evil.example")) "foreign Origin"
  check (Http.isJsonContentType "application/json") "plain JSON type"
  check (Http.isJsonContentType "application/json; charset=utf-8") "JSON with charset"
  check (!Http.isJsonContentType "text/plain") "text/plain is not JSON"
  let openHandler := Http.handleRequestWithLimit 64 .open resolve
  let openCfg := Http.serverConfig 64
  let runOpen := fun (name raw status : String) => do
    Std.Http.Internal.Test.checkClose name raw openHandler
      (fun bytes => Std.Http.Internal.Test.assertStatus bytes s!"HTTP/1.1 {status}") openCfg
  runOpen "foreign host" "POST /rpc HTTP/1.1\r\nHost: evil.example\r\nContent-Type: application/json\r\nContent-Length: 8\r\nConnection: close\r\n\r\n[\"help\"]" "403"
  runOpen "foreign origin" "POST /rpc HTTP/1.1\r\nHost: localhost\r\nOrigin: http://evil.example\r\nContent-Type: application/json\r\nContent-Length: 8\r\nConnection: close\r\n\r\n[\"help\"]" "403"
  runOpen "missing content-type" "POST /rpc HTTP/1.1\r\nHost: localhost\r\nContent-Length: 8\r\nConnection: close\r\n\r\n[\"help\"]" "415"
  check ((← calls.get) == 1) "Host/Origin/Content-Type refusals never dispatch"

private def testCliLimits : IO Unit := do
  check ((Cli.limitOf "50").toOption == some 50) "ordinary limit parses"
  check ((Cli.limitOf "9223372036854775807").toOption == some 9223372036854775807)
    "the largest Int64 limit is accepted as-is"
  for s in ["9223372036854775808", "18446744073709551615"] do
    check ((Cli.limitOf s).toOption.isNone) s!"a limit beyond Int64 range is refused: {s}"
  check ((Cli.limitOf "oops").toOption.isNone) "a non-numeric limit is refused"

private def testPortOf : IO Unit := do
  check ((Cli.portOf "7411").toOption == some 7411) "ordinary port parses"
  check ((Cli.portOf "1").toOption == some 1) "lowest port parses"
  check ((Cli.portOf "65535").toOption == some 65535) "highest port parses"
  for s in ["0", "65536", "70000", "-1", "oops", ""] do
    check ((Cli.portOf s).toOption.isNone) s!"port outside 1..65535 is refused: {s}"

private def rowsDbPath : System.FilePath := ".lake" / "leandb_test_rows_limit.sqlite"

private def testRowsLimitPushdown : IO Unit := do
  -- the cap must reach SQL, not trim after a full-table fetch
  if ← rowsDbPath.pathExists then IO.FS.removeFile rowsDbPath
  discard <| expectOk (← withDb rowsDbPath schema do
    for i in [0:10] do
      discard <| insert Author ⟨s!"a{i}", i⟩) "seed ten authors"
  -- the CLI `rows` path (`rowsWhere`): the cap ships as a bound LIMIT ?
  -- over the trivial plan, so exactly three rows are fetched, not ten
  let j ← expectOk (← withDb rowsDbPath schema do
    (CliTable.of Author).rowsWhere [] 3) "rows with limit 3"
  check ((j.getObjValAs? Nat "count").toOption == some 3) s!"three rows: {j}"
  -- direct: fetchFiltered with a cap bounds the fetch itself
  let capped ← withDb rowsDbPath schema do fetchFiltered (α := Author) (ts := [Author]) .tt (some 3)
  check ((← expectOk capped "capped fetch").size == 3) "the cap bounds the fetch"

private def testModuleNameOk : IO Unit := do
  for s in ["Tickets", "tickets", "A.B.C", "_Private", "M1.Migrations", "a_b'c"] do
    check (Freeze.moduleNameOk s) s!"a plain dotted identifier is accepted: {s}"
  for s in ["/tmp/pwn", "../pwn", "a/b", "..", "a..b", "a./x", "1foo",
            "a b", "a-/x", "a\nb", "", ".", "a.", ".a", "a b.Migrations"] do
    check (!Freeze.moduleNameOk s) s!"a non-identifier module is refused: {s}"

/-- An inline field with a space in the name: legal for the derive, which
    builds syntax; the freeze text renderer would emit the binder
    with two tokens. -/
structure Sp where
  «a b» : Int64
  deriving Repr, LeanDb.Entity
private def testFreezeNames : IO Unit := do
  -- plain identifiers and keywords (for columns) are accepted
  for s in ["user", "user_profile", "M1", "a_b'c"] do
    check (Freeze.freezeNameOk s false) s!"a plain identifier is accepted: {s}"
  for s in ["end", "structure", "rec"] do
    check (Freeze.freezeNameOk s true) s!"a keyword column is accepted: {s}"
  -- the shapes the freeze renderer cannot emit, from issue #35
  for s in ["1foo", "a b", "a b_w", "a-/x", "a\nb", "", "a.b", "«quoted»"] do
    check (!Freeze.freezeNameOk s false) s!"a non-identifier table name is refused: {s}"
  for s in ["1foo", "a b_w", "a\nb"] do
    check (!Freeze.freezeNameOk s true) s!"a non-identifier, non-keyword column is refused: {s}"
  -- end to end: a schema with a space-named column is refused by freeze
  let r := Freeze.checkNames [Entity.spec Sp]
  check (r.isOk == false) "a schema with a composite guillemet column is refused"
  match r with
  | .error m => check ((m.splitOn "a b").length > 1) s!"the refusal names the column, got {m}"
  | .ok _ => pure ()
  testEnsureColumnsRace
  testBackupSuffixChain

private def lineStream (s : String) : IO (IO.Ref IO.FS.Stream.Buffer) := do
  IO.mkRef { data := s.toUTF8, pos := 0 }

private def testStdioLineCap : IO Unit := do
  -- ordinary lines, then EOF
  let buf ← lineStream "ping\npong\n"
  let r ← Cli.LineReader.new (IO.FS.Stream.ofBuffer buf)
  check ((← r.next) matches .line "ping") "first line"
  check ((← r.next) matches .line "pong") "second line (pushback survives the chunk boundary)"
  check ((← r.next) matches .eof) "eof after the last newline"
  -- EOF right after bytes: the unterminated line is still delivered
  let buf ← lineStream "tail"
  let r ← Cli.LineReader.new (IO.FS.Stream.ofBuffer buf)
  check ((← r.next) matches .line "tail") "unterminated final line"
  -- over the budget: drained, not buffered; the next line still reads
  let buf ← lineStream "abcdef\nok\n"
  let r ← Cli.LineReader.new (IO.FS.Stream.ofBuffer buf) 3
  check ((← r.next) matches .tooLong) "a line beyond the budget is refused"
  check ((← r.next) matches .line "ok") "the next line still reads"
  -- exactly at the budget is accepted
  let buf ← lineStream "abcd\n"
  let r ← Cli.LineReader.new (IO.FS.Stream.ofBuffer buf) 4
  check ((← r.next) matches .line "abcd") "a line at the budget reads"

private def walDbPath : System.FilePath := ".lake" / "leandb_test_wal.sqlite"

private def testWalOpen : IO Unit := do
  if ← walDbPath.pathExists then IO.FS.removeFile walDbPath
  let conn ← expectOk (← openDb walDbPath schema) "open sets WAL"
  let stmt ← conn.raw.prepare "PRAGMA journal_mode"
  discard <| stmt.step
  check (((← stmt.columnText 0).toLower) == "wal") "open enables WAL"
  let timeout ← conn.raw.prepare "PRAGMA busy_timeout"
  discard <| timeout.step
  check ((← timeout.columnInt64 0) == 5000) "open sets busy_timeout"

private def testStdioInvalidUtf8 : IO Unit := do
  -- #57: a request line whose bytes are not valid UTF-8 used to decode to
  -- "" and be skipped silently — the peer waited forever for a response.
  -- It now surfaces as its own `StdLine` case; only genuinely empty lines
  -- stay silent.
  let bad : ByteArray := (ByteArray.empty.push 0xFF).push 0xFE
  let buf ← IO.mkRef { data := bad ++ "\n\n[\"version\"]\n".toUTF8, pos := 0 }
  let r ← Cli.LineReader.new (IO.FS.Stream.ofBuffer buf)
  check ((← r.next) matches .undecodable) "an invalid-UTF-8 line is undecodable, not empty"
  check ((← r.next) matches .line "") "a genuinely empty line still reads as empty"
  check ((← r.next) matches .line "[\"version\"]") "good lines around it still read"
  check ((← r.next) matches .eof) "eof after the last line"
  -- invalid bytes after a valid prefix poison the whole line
  let buf ← IO.mkRef { data := "[\"ver".toUTF8 ++ bad ++ "\n".toUTF8, pos := 0 }
  let r ← Cli.LineReader.new (IO.FS.Stream.ofBuffer buf)
  check ((← r.next) matches .undecodable) "a valid prefix does not rescue bad bytes"

-- #96: `Handle.read n` on a pipe is `fread` and blocks until *n* bytes or
-- EOF, so a peer whose line is shorter than the read chunk wedged `serve`.
-- Byte-wise reads fix it; model the pipe deterministically by clamping
-- every read to one byte and asserting lines still assemble.
private def testStdioShortReads : IO Unit := do
  let buf ← lineStream "[\"version\"]\n[\"ping\"]\ntail"
  let slow := IO.FS.Stream.ofBuffer buf
  let s := { slow with read := fun _ => slow.read 1 }
  let r ← Cli.LineReader.new s
  check ((← r.next) matches .line "[\"version\"]") "a line assembles across one-byte reads"
  check ((← r.next) matches .line "[\"ping\"]") "pushback still works with one-byte reads"
  check ((← r.next) matches .line "tail") "an unterminated line still assembles"
  check ((← r.next) matches .eof) "eof still surfaces"
/-- The host spec parser (issue #62, comma-in-path): a raw comma splits
    the launch line, `\,` is a literal comma, in name, exe, and args. -/
private def testHostSpecParsing : IO Unit := do
  let ok (s : String) : IO (String × String × List String) :=
    match Host.parseSpec s with
    | .ok r => pure r
    | .error m => throw <| IO.userError s!"FAIL: {String.quote s} should parse: {m}"
  let bad (s : String) : IO Unit :=
    match Host.parseSpec s with
    | .ok _ => throw <| IO.userError s!"FAIL: {String.quote s} should not parse"
    | .error _ => pure ()
  let (n, e, as) ← ok "a=exe"
  check (n == "a" && e == "exe" && as == []) "a plain name=exe spec parses"
  let (n, e, as) ← ok "a=exe,--db,path"
  check (n == "a" && e == "exe" && as == ["--db", "path"]) "exe and args split on raw commas"
  let (n, e, as) ← ok "probe=/opt/my\\,tools/leandb"
  check (n == "probe" && e == "/opt/my,tools/leandb" && as == [])
    "an escaped comma inside the exe path is a literal comma"
  let (_, _, as) ← ok "a=exe,--db,my\\,db.sqlite"
  check (as == ["--db", "my,db.sqlite"]) "an escaped comma inside an arg is a literal comma"
  let (n, _, _) ← ok "my\\,name=exe"
  check (n == "my,name") "an escaped comma inside the name is a literal comma"
  let (n, e, as) ← ok "a=exe=x,--db,y=2"
  check (n == "a" && e == "exe=x" && as == ["--db", "y=2"]) "later =s stay inside the launch line"
  bad "=exe"
  bad "a="
  bad "justname"

/-- The host's `--port` resolves through `Cli.portOf` (issue #56: the
    wrap bug bound port mod 2^16 while the banner echoed the raw Nat). -/
private def testHostPortWiring : IO Unit := do
  match Host.parseArgs ["--port", "70000", "a=exe"] with
  | .ok (p, h, _, specs) =>
      check (p == some "70000") "the --port flag survives as its string"
      check (h == "127.0.0.1" && specs == ["a=exe"]) "the rest of the argv still parses"
      check ((Cli.portOf (p.getD "")).toOption.isNone) "a port beyond 65535 is refused, not wrapped"
  | .error m => check false s!"host argv should parse: {m}"
  match Host.parseArgs ["--port", "0", "a=exe"] with
  | .ok (p, _, _, _) =>
      check ((Cli.portOf (p.getD "")).toOption.isNone) "port 0 is refused"
  | .error m => check false s!"host argv should parse: {m}"
  match Host.parseArgs ["--port", "7654", "a=exe"] with
  | .ok (p, _, _, _) =>
      check ((Cli.portOf (p.getD "")).toOption == some 7654) "an in-range port resolves as-is"
  | .error m => check false s!"host argv should parse: {m}"

/-- The response-line guard (issue #62, uncapped read + desync): only a
    JSON object line is a response; eof, an undecodable line, an over-cap
    line, or a stray non-object line is a transport error, and the
    tooLong refusal names the cap. -/
private def testProcessLineGuard : IO Unit := do
  check ((Client.processLine (.line "{\"ok\":true}")).toOption.isSome) "a JSON object line is a response"
  check ((Client.processLine (.line "hello from the base")).toOption.isNone)
    "a stray non-JSON line is a transport error, not a response"
  check ((Client.processLine (.line "[1,2,3]")).toOption.isNone)
    "a stray JSON non-object line is a transport error"
  check ((Client.processLine .eof).toOption.isNone) "eof is a transport error"
  check ((Client.processLine .undecodable).toOption.isNone)
    "an invalid-UTF-8 line is a transport error (#57)"
  match Client.processLine .tooLong with
  | .error m =>
      check ((m.splitOn "cap").length > 1) s!"the tooLong refusal names the cap: {m}"
  | .ok _ => check false "an over-cap line must be refused"

/-- The capped child-stdout reader: `Handle.read n` is `fread` and would
    wedge on a live pipe with a partial line, so the reader reads
    byte-wise; the cap bounds what an uncapped `getLine` would buffer. -/
private def testNextLineCap : IO Unit := do
  let p : System.FilePath := ".lake" / "leandb_test_line.txt"
  IO.FS.writeFile p "ping\npong\ntail"
  try
    let h ← IO.FS.Handle.mk p .read
    check ((← Client.nextLine h) matches .line "ping") "first line"
    check ((← Client.nextLine h) matches .line "pong") "next line still reads"
    check ((← Client.nextLine h) matches .line "tail") "unterminated final line"
    check ((← Client.nextLine h) matches .eof) "eof after the last line"
  finally IO.FS.removeFile p
  IO.FS.writeFile p "abcdef\nok\n"
  try
    let h ← IO.FS.Handle.mk p .read
    check ((← Client.nextLine h 3) matches .tooLong) "a line beyond the budget is refused"
  finally IO.FS.removeFile p
  IO.FS.writeFile p "abcd\n"
  try
    let h ← IO.FS.Handle.mk p .read
    check ((← Client.nextLine h 4) matches .line "abcd") "a line at the budget reads"
  finally IO.FS.removeFile p
  -- invalid bytes are `undecodable`, not a silently emptied line (#57)
  let bad : ByteArray := (ByteArray.empty.push 0xFF).push 0xFE
  IO.FS.writeFile p ""
  let w ← IO.FS.Handle.mk p .write
  w.write ("pre".toUTF8 ++ bad ++ "\ntail\n".toUTF8)
  try
    let h ← IO.FS.Handle.mk p .read
    check ((← Client.nextLine h) matches .undecodable) "a line of invalid bytes is undecodable"
    check ((← Client.nextLine h) matches .line "tail") "good lines after it still read"
    check ((← Client.nextLine h) matches .eof) "eof after the last line"
  finally IO.FS.removeFile p
  IO.FS.writeFile p ""
  let w ← IO.FS.Handle.mk p .write
  w.write ("tail".toUTF8 ++ bad ++ "\n".toUTF8)
  try
    let h ← IO.FS.Handle.mk p .read
    check ((← Client.nextLine h) matches .undecodable) "bad bytes after a valid prefix poison the line"
  finally IO.FS.removeFile p

/-! ## Scaffold: reserved modules and TOML emission (issues #69, #70) -/

private def testScaffoldReservedModule : IO Unit := do
  check (Scaffold.moduleOf "main" == "Main") "main mangles to Main"
  -- `leandb new main` used to mangle to module `Main`, collapsing the
  -- lib-root aggregate and the CLI entrypoint onto one `Main.lean` and
  -- emitting a self-importing package (#69).
  for s in ["main", "option", "json", "int", "lean_db", "stored", "sql_type"] do
    check (!Scaffold.validName s) s!"a name mangling to a reserved module is refused: {s}"
  for s in ["price_watch", "note_store", "a1", "x"] do
    check (Scaffold.validName s) s!"an ordinary snake_case name stays valid: {s}"

private def testTomlString : IO Unit := do
  check (Scaffold.tomlString "plain" == "\"plain\"") "a plain string is just quoted"
  check (Scaffold.tomlString "" == "\"\"") "the empty string is still quoted"
  check (Scaffold.tomlString "a\"b" == "\"a\\\"b\"") "a double quote is escaped"
  check (Scaffold.tomlString "a\\b" == "\"a\\\\b\"") "a backslash is escaped"
  check (Scaffold.tomlString "a\tb\nc\rd" == "\"a\\tb\\nc\\rd\"") "the short escapes"
  check (Scaffold.tomlString "a\x01b" == "\"a\\u0001b\"") "control characters use \\uXXXX"
  check (Scaffold.tomlString "a\x0bb" == "\"a\\u000bb\"") "vertical tab has no short escape"
  check (Scaffold.tomlString "\x7f" == "\"\\u007f\"") "DEL is escaped, never raw"
  let nasty := "http://x\x01y\"z\\q\n\t\x0b\x7fé"
  let rendered := Scaffold.tomlString nasty
  check (!(rendered.toList.any fun c => c.toNat < 0x20 || c.toNat == 0x7f))
    "no raw control bytes survive"
  check ((rendered.splitOn "\\x").length == 1) "no Lean-style \\x escapes survive"
  check ((rendered.splitOn "\\u").length == 4) "every escaped control char is \\uXXXX"
  check (Import.tomlString nasty == rendered) "the importer's escaper agrees with the scaffold's"

/-- MCP over the handler: notifications never answered, bad arguments
    refused (issues #63, #64). -/

private def mcpDbPath : System.FilePath := ".lake" / "leandb_test_mcp.sqlite"

private def testMcpRpc : IO Unit := do
  if ← mcpDbPath.pathExists then IO.FS.removeFile mcpDbPath
  discard <| expectOk (← withDb mcpDbPath [Entity.spec Probe] (pure ())) "create the mcp probe"
  let b : Base := { name := "m", tables := [CliTable.of Probe] }
  let inst := Instance.ofPath mcpDbPath
  let sess ← expectOk (← Cli.Session.open b inst) "open the mcp session"
  let parse (s : String) : Lean.Json :=
    match Lean.Json.parse s with
    | .ok j => j
    | .error e => panic! s!"bad test JSON: {e}"
  let answer (line : String) : IO (Option String) := do
    match ← Mcp.respond b inst sess (parse line) with
    | none => pure none
    | some r => pure r.compress
  let codeOf (r : Option String) : Option Int :=
    match r with
    | none => none
    | some t =>
      match (parse t).getObjVal? "error" with
      | .ok e => (e.getObjValAs? Int "code").toOption
      | .error _ => none
  let countOf (r : Option String) : Option Nat :=
    match r with
    | none => none
    | some t =>
      match (parse t).getObjVal? "result" with
      | .ok res => match res.getObjVal? "structuredContent" with
        | .ok sc => (sc.getObjValAs? Nat "count").toOption
        | .error _ => none
      | .error _ => none
  -- a request still gets its reply, echoing the id
  let hi ← answer "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{}}"
  check (((parse (hi.getD "")).getObjValAs? Int "id").toOption == some 1) "a request's reply echoes its id"
  -- #64: a notification with a known method gets no reply
  let r ← answer "{\"jsonrpc\":\"2.0\",\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"2025-06-18\"}}"
  check (r == none) "a known-method notification gets no reply"
  let r ← answer "{\"jsonrpc\":\"2.0\",\"method\":\"tools/list\"}"
  check (r == none) "tools/list as a notification gets no reply"
  let r ← answer "{\"jsonrpc\":\"2.0\",\"method\":\"frobnicate\"}"
  check (r == none) "an unknown-method notification still gets no reply"
  -- #64: tools/call as a notification gets no reply and is never executed
  let r ← answer "{\"jsonrpc\":\"2.0\",\"method\":\"tools/call\",\"params\":{\"name\":\"insert_probe\",\"arguments\":{\"row\":{\"label\":\"ghost\"}}}}"
  check (r == none) "tools/call as a notification gets no reply"
  let rows ← b.handle inst sess ["rows", "probe"]
  check ((rows.getObjValAs? Nat "count").toOption == some 0) "the notification never executed the tool"
  -- #64: id:null is an invalid request (-32600), not a notification, and
  -- the tool it names is not executed
  let r ← answer "{\"jsonrpc\":\"2.0\",\"id\":null,\"method\":\"tools/call\",\"params\":{\"name\":\"insert_probe\",\"arguments\":{\"row\":{\"label\":\"ghost\"}}}}"
  check (codeOf r == some (-32600)) s!"an id:null request is invalid, got {r}"
  let rows ← b.handle inst sess ["rows", "probe"]
  check ((rows.getObjValAs? Nat "count").toOption == some 0) "the id:null request never executed the tool"
  -- #63: a malformed eq is refused with -32602, unfiltered rows never returned
  let r ← answer "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"tools/call\",\"params\":{\"name\":\"rows_probe\",\"arguments\":{\"eq\":\"label=ghost\"}}}"
  check (codeOf r == some (-32602)) s!"a string eq is refused with -32602, got {r}"
  check ((r.getD "").contains "eq") "the refusal names the argument"
  check (((parse (r.getD "")).getObjVal? "result").toOption.isNone) "no result accompanies the refusal"
  -- #63: an array eq with a non-string member is refused too
  let r ← answer "{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"tools/call\",\"params\":{\"name\":\"rows_probe\",\"arguments\":{\"eq\":[5]}}}"
  check (codeOf r == some (-32602)) s!"a non-string eq member is refused with -32602, got {r}"
  -- #63: a non-scalar limit is refused
  let r ← answer "{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"tools/call\",\"params\":{\"name\":\"rows_probe\",\"arguments\":{\"limit\":{\"n\":5}}}}"
  check (codeOf r == some (-32602)) s!"an object limit is refused with -32602, got {r}"
  -- the well-formed path is unchanged: absent eq is no filter, a real eq filters
  discard <| b.handle inst sess ["insert", "probe", "{\"label\":\"keep\"}"]
  let rowsNone ← answer "{\"jsonrpc\":\"2.0\",\"id\":10,\"method\":\"tools/call\",\"params\":{\"name\":\"rows_probe\",\"arguments\":{}}}"
  check (countOf rowsNone == some 1) "an absent eq still means no filter"
  let rowsFiltered ← answer "{\"jsonrpc\":\"2.0\",\"id\":11,\"method\":\"tools/call\",\"params\":{\"name\":\"rows_probe\",\"arguments\":{\"eq\":[\"label=ghost\"]}}}"
  check (countOf rowsFiltered == some 0) "an array eq filters as before"
  let rowsKeep ← answer "{\"jsonrpc\":\"2.0\",\"id\":12,\"method\":\"tools/call\",\"params\":{\"name\":\"rows_probe\",\"arguments\":{\"eq\":[\"label=keep\"]}}}"
  check (countOf rowsKeep == some 1) "the eq filter matches the inserted row"
  -- argvOf: the same contract, on the argv level
  let noEq := Mcp.argvOf b "rows_probe" (parse "{\"limit\":5}")
  check (noEq.toOption == some ["rows", "probe", "--limit", "5"]) "absent eq is no filter"
  match Mcp.argvOf b "rows_probe" (parse "{\"eq\":\"label=keep\"}") with
  | .error m => check (m.contains "eq") s!"the argvOf refusal names eq, got {m}"
  | .ok _ => pure ()
  match Mcp.argvOf b "rows_probe" (parse "{\"eq\":[\"label=keep\"]}") with
  | .error _ => pure ()
  | .ok argv => check (argv == ["rows", "probe", "--eq", "label=keep"]) "a real eq becomes --eq pairs"
  -- a non-object message is an invalid request, not a notification
  let r ← answer "3"
  check (codeOf r == some (-32600)) s!"a non-object message is invalid, got {r}"

def main : IO UInt32 := do
  testCliLimits
  testStrictSchemaJson
  testRowsLimitPushdown
  testFreezeNames
  testPortOf
  testModuleNameOk
  testStdioLineCap
  testStdioInvalidUtf8
  testStdioShortReads
  testScaffoldReservedModule
  testTomlString
  testHttpBodyLimits
  testWalOpen
  testLogPolicy
  testCodecs
  testBaseSpecs
  testNextLineCap
  testSession
  testMcpRpc
  testRestoreSafety
  testRestoreResilience
  testHandleBoundary
  testRestoreWriterGuard
  testChain
  testFootprints
  testDerivedSpec
  testSortBy
  testPlans
  testTypedPred
  testQuantifiers
  testHostSpecParsing
  testHostPortWiring
  testProcessLineGuard
  testCoherence
  testClosedEnum
  testDefaults
  testRealLiterals
  testJson
  testEndToEnd
  testNanReal
  testInfReal
  testParamSplitEndToEnd
  testQuantifiersEndToEnd
  testMigrations
  testMigrationErrorPragmas
  testSqlQuoting
  testEmptyEntity
  testBlobColumn
  testUniqueConstraint
  testConstraintClassify
  testImportNotCarried
  testQuotedEndToEnd
  testAdoptAffinity
  testForeignFileRefused
  testImportUnusableNames
  testImportHostileDeclType
  testImportHostileNames
  testImportWithoutRowidPhrase
  testImportDualFk
  Lep3.run
  EnumSetA.run
  testOptionalParamPlans
  testOptionalParamEndToEnd
  InlineC.run
  ChildD.run
  TestsLdb01.run
  TestsLdb15.run
  TestsLdb16.run
  TestsLdb17.run
  TestsLdb18.run
  TestsLdb19.run
  TestsLdb20.run
  TestsLdb21.run
  TestsLdb22.run
  TestsLdb23.run
  TestsLdb24.run
  TestsM14a.run
  TestsM14b.run
  TestsM14c.run
  TestsM15a.run
  IO.println "all engine tests passed"
  return 0
