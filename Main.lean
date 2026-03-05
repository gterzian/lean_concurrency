import Std
import LeanConcurrency
import LeanConcurrency.ConcurrencyImplementation

open LeanConcurrency.ConcurrencyImplementation

/--
Parse the first command line argument as a natural number and return it.
Defaults to `3` when the argument is missing or not a valid number.
-/
def getNumThreads : List String → Nat
  | arg :: _ =>
      match arg.toNat? with
      | some n => n
      | none   => 3
  | []       => 3

open IO

-- Lean's runtime currently does **not** expose command line
-- arguments to the `IO` monad (there's no `IO.getArgs`).  attempting to
-- `#check` `System.args` or `IO.args` fails, so we fall back to an
-- environment‑variable based convention instead.
--
-- Users can run the program with e.g.:
--
--   NUM_THREADS=5 lake run
--
-- and the code below will read that value and default to 3 if it's
-- missing or malformed.


def main : IO Unit := do
  let maybeEnv ← IO.getEnv "NUM_THREADS"
  let n :=
    match maybeEnv with
    | some s => match s.toNat? with
                  | some k => k
                  | none   => 3
      | none   => 3
    println s!"spawning {n} threads (default 3)";
    if h : 1 < n then
      runIO n h
    else
      IO.println "nthreads must be > 1"
