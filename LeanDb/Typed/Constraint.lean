import LeanDb.Typed.Write

namespace LeanDb

inductive ConstraintKind where
  | unique | foreignKey | memberPair
  deriving Repr, BEq

/-- Stable physical identity plus source-level diagnostics. Metadata contains
    no conflict holder, row, credential, or publication permission. -/
structure ConstraintMetadata where
  identity : String
  table : String
  sourcePaths : List String
  columns : Array String
  kind : ConstraintKind
  target : Option String := none
  cascade : Bool := false
  deriving Repr, BEq

def Unique.metadata {α} [Entity α] [HasUnique α] [Indexes α] (ix : Unique α) :
    ConstraintMetadata :=
  let cols := Unique.columns ix
  { identity := Unique.identity ix
    table := Entity.tableName α
    sourcePaths := cols.toList.map (fun col => Entity.typeName (α := α) ++ "." ++ col)
    columns := cols
    kind := .unique }

def ForeignKey.metadata {α} [Entity α] [HasForeignKey α] (fk : ForeignKey α) :
    ConstraintMetadata :=
  let field := ForeignKey.field fk
  let col := Entity.fieldName field
  { identity := Entity.tableName α ++ ".foreignKey." ++ col
    table := Entity.tableName α
    sourcePaths := [Entity.typeName (α := α) ++ "." ++ col]
    columns := #[col]
    kind := .foreignKey
    target := (Entity.fieldSpec field).fkTable
    cascade := ForeignKey.cascade fk }

def MemberRelation.metadata {p t e} [Entity p] [Entity t] [Entity e]
    [HasUnique e] [HasForeignKey e] [Indexes e] (relation : MemberRelation p t e) :
    ConstraintMetadata :=
  { Unique.metadata relation.pairIndex with sourcePaths := [relation.sourceField], kind := .memberPair }

/-- Redacted structural failure source. The conflict holder in InsertError
    remains available to privileged native code but never enters this value. -/
def InsertError.metadata {α} [Entity α] [HasUnique α] [HasForeignKey α] [Indexes α] :
    InsertError α → ConstraintMetadata
  | .duplicate index _ => Unique.metadata index
  | .missingRef fk => ForeignKey.metadata fk

/-- Inbound FK identity for a restricted delete. Counts and referenced rows
    stay in the privileged typed error, never in this structural projection. -/
def ReferencedBy.metadata {s α} [IsSchema s] [Entity α] [HasReferencedBy s α]
    (key : ReferencedBy s α) : ConstraintMetadata :=
  let source := ReferencedBy.sourceEntity key
  let table := @Entity.tableName (ReferencedBy.Source key) source
  let column := ReferencedBy.columnName key
  { identity := table ++ ".foreignKey." ++ column
    table := table
    sourcePaths := [@Entity.typeName (ReferencedBy.Source key) source ++ "." ++ column]
    columns := #[column]
    kind := .foreignKey
    target := some (Entity.tableName α)
    cascade := ReferencedBy.cascade key }

/-- Only actual constraint alternatives acquire metadata. Gone/stale values
    are separate failures; returning none does not discharge those failures. -/
def UpdateError.metadata? {α} [Entity α] [HasUnique α] [HasForeignKey α] [Indexes α] :
    UpdateError α → Option ConstraintMetadata
  | .duplicate index _ => some (Unique.metadata index)
  | .missingRef fk => some (ForeignKey.metadata fk)
  | .stale _ | .gone => none

/-- Retains the actual touched unique/FK alternative of a selective patch;
    invalid/gone remain separate and must still be handled by the caller. -/
def SetError.metadata? {α} [Entity α] [HasUnique α] [HasForeignKey α] [Indexes α]
    {fs : Fields α} :
    SetError α fs → Option ConstraintMetadata
  | .duplicate index _ => some (Unique.metadata index.ix)
  | .missingRef fk => some (ForeignKey.metadata fk.fk)
  | .gone | .invalid _ => none

def AppendError.metadata? {α} [Entity α] [HasListField α] [HasUnique α]
    [HasForeignKey α] [Indexes α] : AppendError α → Option ConstraintMetadata
  | .duplicate index _ => some (Unique.metadata index)
  | .missingRef fk => some (ForeignKey.metadata fk)
  | .stale _ | .gone | .notAppend _ => none

def DeleteError.metadata? {s α} [IsSchema s] [Entity α] [HasReferencedBy s α] :
    DeleteError s α → Option ConstraintMetadata
  | .restricted key _ => some (ReferencedBy.metadata key.val)
  | .gone => none

structure CanonicalConflict (key : Type) where
  canonical : key
  rows : List Int64
  deriving Repr, BEq

structure CanonicalPreflight (key : Type) where
  invalid : List (Int64 × String)
  conflicts : List (CanonicalConflict key)
  deriving Repr, BEq

/-- Read-only migration preflight using the caller's ONE scalar parser. Report
    every invalid row and all rows in each collapsed canonical key, never pick
    a survivor or rewrite/deduplicate data. -/
def canonicalizationPreflight {key} [BEq key]
    (parse : String → Except String key) (rows : List (Int64 × String)) : CanonicalPreflight key :=
  let (invalid, groups) := rows.foldl (init := ([], [])) fun (invalid, groups) (id, raw) =>
    match parse raw with
    | .error why => (invalid ++ [(id, why)], groups)
    | .ok canonical =>
        if groups.any (fun group => group.canonical == canonical) then
          (invalid, groups.map fun group =>
            if group.canonical == canonical then { group with rows := group.rows ++ [id] } else group)
        else (invalid, groups ++ [{ canonical, rows := [id] }])
  { invalid, conflicts := groups.filter (fun group => group.rows.length > 1) }

end LeanDb
