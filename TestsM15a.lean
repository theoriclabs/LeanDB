import LeanDb

/-! M15a: meaning vs SQLite. One regression case per D1–D10.

Each case compares `run` and `denote` on the answer (including a typed
failure with payload), and on the final tables via `load`/`get`. A
`DbFault` is recorded on the execution side (meaning never produces one).
-/

namespace TestsM15a

open LeanDb
open LeanDb.Harness

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

private def check' (condition : Bool) (message : String) : DbM Unit :=
  unless condition do throw (.sqlite s!"FAIL: {message}")

private def expectOk (r : Except DbError α) (context : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {context}: {e}"

inductive Status where
  | backlog | inProgress | done
  deriving Repr, DecidableEq, Ord, BEq, LeanDb.ClosedEnum

structure Org where
  name : String
  deriving Repr, BEq, LeanDb.Entity

structure Team where
  name : String
  org : Ref Org
  deriving Repr, BEq

cascade% Team.org
deriving instance LeanDb.Entity for Team

structure Member where
  name : String
  team : Ref Team
  deriving Repr, BEq

cascade% Member.team
deriving instance LeanDb.Entity for Member

structure Doc where
  title : String
  owner : Option (Ref Member)
  deriving Repr, BEq, LeanDb.Entity

structure Job where
  title : String
  status : Status
  deriving Repr, BEq, LeanDb.Entity

structure Item where
  label : String
  deriving Repr, BEq, LeanDb.Inline

structure Bag where
  name : String
  items : List Item
  deriving Repr, BEq, LeanDb.Entity

unique% Bag.byName := name

structure Counter where
  n : Nat
  deriving Repr, BEq, LeanDb.Entity

structure Badge where
  label : String
  deriving Repr, BEq, LeanDb.Inline

structure Crew where
  name : String
  team : Ref Team
  badges : List Badge
  deriving Repr, BEq, LeanDb.Entity

/-- Invariant that mixes two columns, for D10. -/
structure Pair where
  a : String
  b : String
  deriving Repr, BEq

@[leandb_invariant]
def Pair.invariant (p : Pair) : Bool := p.a == p.b

deriving instance LeanDb.Entity for Pair

schema% S := Org, Team, Member, Doc, Job, Bag, Counter, Crew, Pair

private def specs : List TableSpec := IsSchema.specs S

private def dbPath : System.FilePath := ".lake" / "leandb_test_m15a.sqlite"

private def fresh (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then IO.FS.removeFile p
  for suffix in ["-wal", "-shm"] do
    let side : System.FilePath := p.toString ++ suffix
    if ← side.pathExists then IO.FS.removeFile side

private def ck {α} [Entity α] (v : α)
    (h : Invariant α v := by
      unfold Invariant
      simp only [sqlRangeOk]
      first | trivial | (refine ⟨trivial, ?_⟩; decide) | decide) :
    Checked α :=
  Checked.of v h

private def stateEqS (a b : DbState S) : Bool :=
  getEq (α := Org) a b && getEq (α := Team) a b && getEq (α := Member) a b &&
    getEq (α := Doc) a b && getEq (α := Job) a b && getEq (α := Bag) a b &&
    getEq (α := Counter) a b && getEq (α := Crew) a b && getEq (α := Pair) a b

/-- One comparison: `run` vs `denote`. `agree` is true only when both
    produced a typed result (no `DbFault`) with equal payload and equal
    tables. -/
private def cmpTxn {ε α} (p : {σ : Type} → Txn σ S ε α)
    (eq : Except ε α → Except ε α → Bool) (msg : String) :
    DbM Bool := do
  let st0 ← DbState.load (s := S)
  requireWF st0 s!"{msg} (load)"
  let (want, stD) := Txn.denote (σ := Unit) (s := S) (p (σ := Unit)) st0
  match ← Txn.run (s := S) p with
  | .error f =>
      let st1 ← DbState.load (s := S)
      requireWF st1 s!"{msg} (load after fault)"
      IO.println s!"  {msg}: DISAGREE run=DbFault {f} stateEq={stateEqS st1 stD}"
      return false
  | .ok got =>
      let st1 ← DbState.load (s := S)
      requireWF st1 s!"{msg} (load after)"
      let ans := eq got want
      let stOk := stateEqS st1 stD
      let wfD := DbState.checkWF stD
      unless wfD do
        IO.println s!"  {msg}: denote checkWF=false"
      if ans && stOk then
        IO.println s!"  {msg}: AGREE"
        return true
      else
        IO.println s!"  {msg}: DISAGREE ans={ans} state={stOk}"
        return false

private def cmpRead {α} (r : Read S α) (eq : α → α → Bool) (msg : String) :
    DbM Bool := do
  let st0 ← DbState.load (s := S)
  requireWF st0 s!"{msg} (load)"
  let want := Read.denote (s := S) r st0
  match ← Read.run (s := S) r with
  | .error f =>
      IO.println s!"  {msg}: DISAGREE run=DbFault {f}"
      return false
  | .ok got =>
      let st1 ← DbState.load (s := S)
      requireWF st1 s!"{msg} (after)"
      if eq got want then
        IO.println s!"  {msg}: AGREE"
        return true
      else
        IO.println s!"  {msg}: DISAGREE run≠denote"
        return false

private def eqEmpty {α} (eq : α → α → Bool) :
    Except Empty α → Except Empty α → Bool
  | .ok a, .ok b => eq a b
  | .error e, _ => nomatch e
  | _, .error e => nomatch e

private def eqOptNat : Except Empty (Option Int64) → Except Empty (Option Int64) → Bool :=
  eqEmpty fun a b => a == b

private def eqStr : Except Empty String → Except Empty String → Bool :=
  eqEmpty fun a b => a == b

private def eqInsDoc :
    Except Empty (Except (InsertError Doc) Int64) →
    Except Empty (Except (InsertError Doc) Int64) → Bool :=
  eqEmpty fun
    | .ok a, .ok b => a == b
    | .error (.missingRef _), .error (.missingRef _) => true
    | .error (.duplicate ..), .error (.duplicate ..) => true
    | _, _ => false

private def eqAppLabels :
    Except Empty (Except (AppendError Bag) (List String)) →
    Except Empty (Except (AppendError Bag) (List String)) → Bool :=
  eqEmpty fun
    | .ok a, .ok b => a == b
    | .error .gone, .error .gone => true
    | .error (.stale a), .error (.stale b) => a.id == b.id && a.val == b.val
    | .error (.notAppend _), .error (.notAppend _) => true
    | .error (.duplicate ..), .error (.duplicate ..) => true
    | .error (.missingRef _), .error (.missingRef _) => true
    | _, _ => false

/-! ## D1: filters on child-list contents -/

private def bagsWithX : Query S [Bag] (Stored Bag) :=
  (Query.from Bag).where' (fun b => b.val.items.any (fun i => i.label == "x"))

private def bagsAllX : Query S [Bag] (Stored Bag) :=
  (Query.from Bag).where' (fun b => b.val.items.all (fun i => i.label == "x"))

private def namesOf (xs : List (Valid Bag)) : List String := xs.map (·.val.name)

private def testD1 : IO Bool := do
  fresh dbPath
  expectOk (← withDb dbPath specs do
    let _ ← LeanDb.insert Bag ⟨"hasX", [⟨"x"⟩]⟩
    let _ ← LeanDb.insert Bag ⟨"noX", [⟨"y"⟩]⟩
    check' bagsWithX.exact "D1 any should be exact"
    check' bagsAllX.exact "D1 all should be exact"
    let a ← cmpRead (Read.all bagsWithX)
      (fun x y => namesOf x == namesOf y) "D1 any"
    let c ← cmpRead (Read.count bagsWithX) (· == ·) "D1 count"
    let al ← cmpRead (Read.all bagsAllX)
      (fun x y => namesOf x == namesOf y) "D1 forall"
    return a && c && al
  ) "D1"

/-! ## D2: cascades more than one level -/

private def testD2 : IO Bool := do
  fresh dbPath
  expectOk (← withDb dbPath specs do
    let o ← LeanDb.insert Org ⟨"o"⟩
    let t ← LeanDb.insert Team ⟨"t", o.id⟩
    let _ ← LeanDb.insert Member ⟨"m", t.id⟩
    cmpTxn (fun {_} => do
        let r ← Txn.delete (α := Org) o.id
        return r.toOption.map (·.id.toInt64))
      eqOptNat "D2 cascade Org→Team→Member"
  ) "D2"

/-! ## D3: Option (Ref) invisible to the typed layer -/

private def testD3 : IO Bool := do
  fresh dbPath
  let a ← expectOk (← withDb dbPath specs do
    cmpTxn (fun {_} => do
        let r ← Txn.insert (α := Doc) (ck ⟨"d", some ⟨99⟩⟩)
        return r.map (fun c => c.id.toInt64))
      eqInsDoc "D3 insert dangling Option Ref"
  ) "D3 insert"
  fresh dbPath
  let b ← expectOk (← withDb dbPath specs do
    let o ← LeanDb.insert Org ⟨"o2"⟩
    let t ← LeanDb.insert Team ⟨"t2", o.id⟩
    let m ← LeanDb.insert Member ⟨"m2", t.id⟩
    let _ ← LeanDb.insert Doc ⟨"d2", some m.id⟩
    cmpTxn (fun {_} => do
        let r ← Txn.delete (α := Member) m.id
        return (match r with
          | .ok _ => "ok"
          | .error .gone => "gone"
          | .error (.restricted _ _) => "restricted"))
      eqStr "D3 delete Member referenced by Option Ref"
  ) "D3 delete"
  return a && b

/-! ## D4: append staleness and parent constraints -/

private def testD4 : IO Bool := do
  fresh dbPath
  let a ← expectOk (← withDb dbPath specs do
    let b ← LeanDb.insert Bag ⟨"ap", [⟨"a"⟩]⟩
    let _ ← LeanDb.update b ⟨"ap", [⟨"b"⟩]⟩
    let bv ← match Valid.ofStored? b with
      | some v => pure v
      | none => throw (.sqlite "D4 bag not Valid")
    -- `b` still has items=[a] in the handle; stored list is [b] (same length).
    cmpTxn (fun {_} => do
        let r ← Txn.append (α := Bag) bv (ck ⟨"ap", [⟨"a"⟩, ⟨"c"⟩]⟩)
        return r.map (fun s => s.val.items.map Item.label))
      eqAppLabels "D4 append same-length changed list"
  ) "D4 lists"
  fresh dbPath
  let b ← expectOk (← withDb dbPath specs do
    let _ ← LeanDb.insert Bag ⟨"taken", []⟩
    let mine ← LeanDb.insert Bag ⟨"mine", []⟩
    let mv ← match Valid.ofStored? mine with
      | some v => pure v
      | none => throw (.sqlite "D4 mine not Valid")
    cmpTxn (fun {_} => do
        let r ← Txn.append (α := Bag) mv (ck ⟨"taken", [⟨"z"⟩]⟩)
        return (match r with | .ok _ => "ok" | .error _ => "appendError"))
      eqStr "D4 append onto taken unique key"
  ) "D4 unique"
  return a && b

/-! ## D5: ClosedEnum orderBy -/

private def jobsByStatus : Query S [Job] (Stored Job) :=
  (Query.from Job).orderBy (.asc (Job.Field.status : Entity.Field Job))

private theorem jobsByStatus_exact : jobsByStatus.exact = true := by
  unfold jobsByStatus Query.orderBy Query.exact Query.from
  rfl

private def testD5 : IO Bool := do
  fresh dbPath
  expectOk (← withDb dbPath specs do
    let _ ← LeanDb.insert Job ⟨"a", .done⟩
    let _ ← LeanDb.insert Job ⟨"b", .backlog⟩
    let _ ← LeanDb.insert Job ⟨"c", .inProgress⟩
    let a ← cmpRead (Read.all jobsByStatus)
      (fun x y => (x.map (·.val.title)) == (y.map (·.val.title))) "D5 all"
    let f ← cmpRead (Read.first jobsByStatus jobsByStatus_exact)
      (fun x y => (x.map (·.val.title)) == (y.map (·.val.title))) "D5 first"
    return a && f
  ) "D5"

/-! ## D6: forged Current is unrepresentable; schema membership is compile-time -/

/--
error: Invalid `⟨...⟩` notation: Constructor for `LeanDb.Current` is marked as private
-/
#guard_msgs in
example {σ} (s : Stored Org) : Current σ Org :=
  ⟨s, by decide⟩

private def testD6 : IO Bool := pure true

/-! ## D7: Nat above Int64.max is not `Checked` -/

/--
error: Tactic `decide` proved that the proposition
  Invariant Counter { n := 2 ^ 63 }
is false
-/
#guard_msgs in
example : Checked Counter := Checked.of ⟨2^63⟩ (by decide)

private def testD7 : IO Bool := do
  match Entity.check Counter ⟨2^63⟩ with
  | .ok _ =>
      IO.println "  D7: DISAGREE Entity.check accepted Nat 2^63"
      return false
  | .error names =>
      IO.println s!"  D7 Entity.check 2^63: AGREE refused {names.names}"
  match Entity.check Counter ⟨1⟩ with
  | .error _ =>
      IO.println "  D7: DISAGREE Entity.check refused Nat 1"
      return false
  | .ok _ => pure ()
  fresh dbPath
  expectOk (← withDb dbPath specs do
    let c ← LeanDb.insert Counter ⟨1⟩
    cmpTxn (fun {_} => do
        match ← Txn.get Counter c.id with
        | none => return "none"
        | some row =>
            let r ← Txn.set (α := Counter) row (ck ⟨2⟩)
            return (match r with | .ok s => s!"ok {s.val.n}" | .error _ => "setError"))
      eqStr "D7 set Nat 2 (in range)"
  ) "D7 set"

/-! ## D8: first after limit 0 -/

private def testD8 : IO Bool := do
  fresh dbPath
  expectOk (← withDb dbPath specs do
    let _ ← LeanDb.insert Job ⟨"a", .done⟩
    let q0 := (Query.from Job).withWindow { limit := some 0 }
    let z ← cmpRead (Read.first q0)
      (fun x y => (x.map (·.val.title)) == (y.map (·.val.title))) "D8 first limit 0"
    let qHuge := (Query.from Job).withWindow
      { offset := Int64.maxValue.toNatClampNeg }
    let h ← cmpRead (Read.all qHuge)
      (fun x y => (x.map (·.val.title)) == (y.map (·.val.title))) "D8 offset Int64.max"
    let qLim := (Query.from Job).withWindow
      { limit := some Int64.maxValue.toNatClampNeg }
    let l ← cmpRead (Read.all qLim)
      (fun x y => (x.map (·.val.title)) == (y.map (·.val.title))) "D8 limit Int64.max"
    return z && h && l
  ) "D8"

/-! ## D9: quantifier then join -/

private def crewsX : Query S [Crew] (Stored Crew) :=
  (Query.from Crew).where' (fun c => c.val.badges.any (fun b => b.label == "x"))

private def crewsXJoin : Query S [Crew, Team] (Stored Crew × Stored Team) :=
  crewsX.join Crew.ForeignKey.team

/-- Join after a child-list filter: `true` only when run equals denote
    *and* the matching crew is present (both sides used to drop it). -/
private def testD9 : IO Bool := do
  fresh dbPath
  expectOk (← withDb dbPath specs do
    let o ← LeanDb.insert Org ⟨"o"⟩
    let t ← LeanDb.insert Team ⟨"t", o.id⟩
    let _ ← LeanDb.insert Crew ⟨"cx", t.id, [⟨"x"⟩]⟩
    check' crewsX.exact "D9 crewsX should be exact (quantifier is a plan leaf)"
    let a ← cmpRead (Read.all crewsX)
      (fun x y => (x.map (·.val.name)) == (y.map (·.val.name))) "D9 crewsX"
    let st ← DbState.load (s := S)
    let wantJoin := (Read.denote (s := S) (Read.all crewsXJoin) st).map (·.1.val.name)
    let gotJoin ← match ← Read.run (s := S) (Read.all crewsXJoin) with
      | .error f =>
          IO.println s!"  D9 join: DISAGREE run=DbFault {f}"
          pure ([] : List String)
      | .ok got => pure (got.map (·.1.val.name))
    let jAgree := gotJoin == wantJoin
    let jKept := wantJoin == ["cx"] && gotJoin == ["cx"]
    IO.println s!"  D9 join: agree={jAgree} kept={jKept} exact={crewsXJoin.exact} denote={wantJoin} run={gotJoin}"
    -- D9 itself is the join keeping the quantifier; crewsX is D1.
    return jKept && jAgree && a
  ) "D9"

/-! ## D10: patch that breaks a mixed invariant -/

private def testD10 : IO Bool := do
  fresh dbPath
  expectOk (← withDb dbPath specs do
    let p ← LeanDb.insert Pair ⟨"xx", "xx"⟩
    cmpTxn (fun {_} => do
        match ← Txn.get Pair p.id with
        | none => return "none"
        | some row =>
            -- `new` is Checked (a=b=yy) but merge of `a` only yields a=yy, b=xx.
            let r ← Txn.patch (α := Pair) row (Fields.singleton Pair.Field.a) (ck ⟨"yy", "yy"⟩)
            return (match r with | .ok s => s!"ok {s.val.a}/{s.val.b}" | .error .gone => "gone" | .error _ => "err"))
      eqStr "D10 patch mixed invariant"
  ) "D10"

/-- A program over `S` cannot mention an entity that is not a table of `S`. -/
structure Ghost where
  name : String
  deriving Repr, BEq, LeanDb.Entity

/--
error: failed to synthesize instance of type class
  IsSchema.Has S Ghost

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Read S (Option (Valid Ghost)) := Read.get Ghost ⟨1⟩

structure ChildWithRef where
  who : Ref Member
  deriving Repr, BEq, LeanDb.Inline

structure ParentWithChildRef where
  name : String
  kids : List ChildWithRef
  deriving Repr, BEq, LeanDb.Entity

/--
error: schema: TestsM15a.ParentWithChildRef field 'kids' is a child list of TestsM15a.ChildWithRef, which has a Ref field 'who'; foreign keys inside child-list records are not typed (SQLite would enforce them, the meaning would not). Put the reference on a schema table.
-/
#guard_msgs in
schema% BadChildRef := ParentWithChildRef

private def staleIdOnly (a b : UpdateError Bag) : Bool :=
  match a, b with
  | .stale x, .stale y => x.id == y.id
  | .gone, .gone => true
  | _, _ => false

private def testStaleBEq : IO Unit := do
  let a : Stored Bag := ⟨⟨1⟩, ⟨"a", [⟨"x"⟩]⟩⟩
  let b : Stored Bag := ⟨⟨1⟩, ⟨"a", [⟨"y"⟩]⟩⟩
  let e1 : UpdateError Bag := .stale a
  let e2 : UpdateError Bag := .stale b
  IO.println s!"  stale BEq-by-id (same id, different val) = {staleIdOnly e1 e2}"

def run : IO Unit := do
  let d1 ← testD1
  let d2 ← testD2
  let d3 ← testD3
  let d4 ← testD4
  let d5 ← testD5
  let d6 ← testD6
  let d7 ← testD7
  let d8 ← testD8
  let d9 ← testD9
  let d10 ← testD10
  testStaleBEq
  -- Pinned against `79cfbcc` (M15-pre2). `true` = run equals denote
  -- on answer, failure payload, and tables. Flipped to `true` as each
  -- finding is fixed.
  check d1 "D1 child-list any/all: run equals denote"
  check d2 "D2 two-level cascade already agrees (M15-pre2 deleteAt)"
  check d3 "D3 Option Ref: missingRef / restricted in both"
  check d4 "D4 append: list CAS and parent unique/FK"
  check d5 "D5 ClosedEnum orderBy: Lean sort in both"
  check d6 "D6 Current constructor is private; Has is required"
  check d7 "D7 Nat above Int64.max is not Checked"
  check d8 "D8 first after limit 0; huge window applied in Lean"
  check d9 "D9 join keeps the left-side quantifier"
  check (!d10) "D10 still reproduces (mixed-invariant patch is DbFault vs .gone)"
  IO.println s!"M15a reproduce: D1={d1} D2={d2} D3={d3} D4={d4} D5={d5} D6={d6} D7={d7} D8={d8} D9={d9} D10={d10}"

end TestsM15a
