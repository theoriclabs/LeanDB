import TestsModel.Represent
import TestsModel.Post
import TestsModel.Commands
import TestsModel.LoansRun
import TestsModel.PostRun
import TestsModel.RepresentRun
import TestsModel.RepresentNative
import TestsModel.JsonColumns
import TestsModel.LibraryRuntime
import TestsModel.GateEvolution
import TestsModel.UniqueSources

/-! `leandb_model_tests`: `LeanDb.Model` programs on both backends, and the model on SQLite
(`LeanDb.Native`). The model modules check their declarations at compile time
(`#guard_msgs`, `#guard`); this runs the scenarios. -/

def main : IO Unit := do
  -- The same programs in memory and on SQLite.
  LoansRun.run
  PostRun.run
  RepresentRun.run
  -- Model entities on SQLite: migrations, structured columns, represented fields.
  LibraryRuntimeFixture.run
  JsonColumnFixture.run
  RepresentNative.run
  GateEvolutionFixture.run
  UniqueSourcesFixture.run
  IO.println "LeanDb.Model tests passed"
