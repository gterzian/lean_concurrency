import LeanConcurrency.ConcurrencySpec
import Std

namespace LeanConcurrency.ConcurrencyImplementation

open Concurrency
open State

-- simple concurrent example using a mutex to protect a shared abstract state.
def runIO (nthreads : Nat := 3) (hN2 : 1 < nthreads := by omega) : IO Unit := do
  let N := nthreads
  let inst : NeZero N := ⟨Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one hN2)⟩
  let state : IO.Ref (@State N inst) ← IO.mkRef (@State.init N inst)
  let mutex : Std.Mutex Unit ← Std.Mutex.new ()

  let showBool : Bool -> String := fun
    | true => "1"
    | false => "0"

  let tasks : List (Task (IO Unit)) :=
    (List.range N).map fun i =>
      Task.spawn fun _ => do
        if h : i < N then
          let p : Process N := ⟨i, h⟩
          mutex.atomically do
            state.modify (State.setNum p)
            let s ← state.get
            let prevVal := s.y p
            let prevBool := match prevVal with
              | some true => true
              | _ => false
            IO.println s!"thread {i}: previous = {showBool prevBool}"

  tasks.forM fun t => t.get
  IO.println "done."

/-- refinement theorem: every reachable state satisfies the
inductive invariant. -/
theorem runIO_implements_invariants (nthreads : Nat) [NeZero nthreads]
  (hN2 : 1 < nthreads)
    {st : State nthreads} :
    State.reachable st → State.InductiveInvariant st := by
  intro hreach
  induction hreach with
  | init =>
      intro p hy
      simp [State.init] at hy
  | step s t _ hstep ih =>
    exact Concurrency.step_preserves_ind_inv hstep ih hN2

end LeanConcurrency.ConcurrencyImplementation
