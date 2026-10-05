import LeanDb.Typed.Txn

namespace LeanDb

/-- Structural rollback law for every transaction constructor. In particular,
    a failing continuation of bind/orElse restores the ORIGINAL state, not the
    state after the first write. This is not an execution hypothesis. -/
theorem Txn.denote_go_error_restores {σ s ε α} [IsSchema s]
    (program : Txn σ s ε α) (original current : DbState s) (error : ε) (final : DbState s)
    (failed : Txn.denote.go original program current = (.error error, final)) :
    final = original := by
  induction program generalizing current error final with
  | pure value => simp [Txn.denote.go] at failed
  | bind first next firstIH nextIH =>
      simp only [Txn.denote.go] at failed
      cases hfirst : Txn.denote.go original first current with
      | mk answer state =>
          cases answer with
          | error failure =>
              simp only [hfirst] at failed
              cases failed
              exact firstIH current error final hfirst
          | ok value =>
              simp only [hfirst] at failed
              exact nextIH value state error final failed
  | liftRead read => simp [Txn.denote.go] at failed
  | get type id => simp [Txn.denote.go] at failed
  | lookup type index key => simp [Txn.denote.go] at failed
  | throw failure =>
      simp only [Txn.denote.go, Prod.mk.injEq, Except.error.injEq] at failed
      exact failed.2.symm
  | orAbort first map firstIH =>
      simp only [Txn.denote.go] at failed
      cases hfirst : Txn.denote.go original first current with
      | mk answer state =>
          cases answer with
          | error failure =>
              simp only [hfirst] at failed
              cases failed
              exact firstIH current error final hfirst
          | ok result =>
              cases result with
              | error failure =>
                  simp only [hfirst, Prod.mk.injEq, Except.error.injEq] at failed
                  exact failed.2.symm
              | ok value => simp [hfirst] at failed
  | orElse first recover firstIH recoverIH =>
      simp only [Txn.denote.go] at failed
      cases hfirst : Txn.denote.go original first current with
      | mk answer state =>
          cases answer with
          | error failure =>
              simp only [hfirst] at failed
              cases failed
              exact firstIH current error final hfirst
          | ok result =>
              cases result with
              | error failure =>
                  simp only [hfirst] at failed
                  exact recoverIH failure state error final failed
              | ok value => simp [hfirst] at failed
  | insert type checked =>
      simp only [Txn.denote.go] at failed
      split at failed <;> try simp_all
      split at failed <;> try simp_all
  | update type old new =>
      simp only [Txn.denote.go] at failed
      split at failed <;> try simp_all
      split at failed <;> try simp_all
      split at failed <;> try simp_all
      split at failed <;> try simp_all
  | set type row checked =>
      simp only [Txn.denote.go] at failed
      split at failed <;> try simp_all
      split at failed <;> try simp_all
      split at failed <;> try simp_all
  | patch type row fields checked =>
      simp only [Txn.denote.go] at failed
      split at failed <;> try simp_all
      split at failed <;> try simp_all
      split at failed <;> try simp_all
      split at failed <;> try simp_all
  | append type old new =>
      simp only [Txn.denote.go] at failed
      split at failed <;> try simp_all
      split at failed <;> try simp_all
      split at failed <;> try simp_all
      split at failed <;> try simp_all
      split at failed <;> try simp_all
  | delete type id =>
      simp only [Txn.denote.go] at failed
      split at failed <;> try simp_all
      split at failed <;> try simp_all

theorem Txn.denote_error_restores {σ s ε α} [IsSchema s]
    (program : Txn σ s ε α) (original : DbState s) (error : ε) (final : DbState s)
    (failed : Txn.denote program original = (.error error, final)) : final = original :=
  Txn.denote_go_error_restores program original original error final failed

/-- Result-projection form, convenient for API carry-over proofs. -/
theorem Txn.denote_abort_restores {σ s ε α} [IsSchema s]
    (program : Txn σ s ε α) (original : DbState s) (error : ε)
    (failed : (Txn.denote program original).1 = .error error) :
    (Txn.denote program original).2 = original :=
  Txn.denote_error_restores program original error (Txn.denote program original).2
    (Prod.ext failed rfl)

end LeanDb
