import LeanDb.Client

/-! A precompiled client consumer, like the standalone HTTP adapter. Its import
closure does not include LeanOntology, so loading the engine must not implicitly
load the portable model's shared library. Lake builds this fixture with
`precompileModules = true` to exercise shared-library loading during elaboration. -/
