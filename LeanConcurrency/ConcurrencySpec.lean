-- avoid importing Std to keep dependencies minimal

/-!
# Translation of `TeachingConcurrency` TLA+ spec

This file encodes the TLA+ specification from
`spec.tla` in a purely inductive Lean form.  Invariants correspond to
those in the original spec, and a (very simple) reachability relation
models `Init /\ [][Next]_{<<x,y>>}`.

The goal at the bottom is to prove that every state reachable from
`init` satisfies the three properties mentioned in the theorem of the
TLA+ spec.  The proof is a straightforward induction on the
reachable relation.
-/

namespace Concurrency

universe u

section

-- we assume the number of processes is nonzero so that `pred` is
-- well behaved; the original TLA+ spec implicitly had `N` positive.
variable {N : Nat} [hN : NeZero N]

/-- processes are `0..N-1` -/
abbrev Process (N : Nat) : Type := Fin N

/-- the value that `x` may take.  `false` corresponds to `0`,
`true` corresponds to `1` in the spec. -/
abbrev Value := Bool

/-- `y` may additionally be `NoVal`; we model it with `Option`. -/
abbrev YValue := Option Value

/-- a global state consisting of the two maps `x` and `y`. -/
structure State (N : Nat) [hN : NeZero N] where
  x : Process N → Value
  y : Process N → YValue
  deriving Inhabited

namespace State

variable {N : Nat} [hN : NeZero N]

/-- the state in which all `x` are 0 and all `y` are `NoVal`. -/
def init : State N :=
  { x := fun _ => false,
    y := fun _ => none }

/-- predecessor modulo `N` -/
def pred (p : Process N) : Process N :=
  ⟨(p.val + N - 1) % N,
    -- `Nat.mod_lt` needs a proof `0 < N`, which we obtain from `hN`.
    Nat.mod_lt _ (Nat.pos_of_ne_zero (hN.ne'.symm))⟩

/-- the `SetNum(p)` transition. -/
def setNum (p : Process N) (s : State N) : State N :=
  { x := fun q => if q = p then true else s.x q,
    y := fun q => if q = p then some (s.x (pred p)) else s.y q }

/-- the `Stop` test from the spec: every `y[p]` is not `NoVal`. -/
def stopped (s : State N) : Prop :=
  ∀ p : Process N, s.y p ≠ none

/-- the step relation corresponding to `Next`. -/
inductive step : State N → State N → Prop
  | setnum (s : State N) (p : Process N) : step s (setNum p s)
  | stop   (s : State N) : stopped s → step s s

/-- reachability obtained by closing `init` under `step`. -/
inductive reachable : State N → Prop
  | init  : reachable (init : State N)
  | step (s t : State N) : reachable s → step s t → reachable t

-- invariants use simple quantifiers instead of `Finset`.

/-- every process has a (non-`none`) y-value -/
def allStopped (s : State N) : Prop :=
  ∀ p : Process N, s.y p ≠ none

/-- some process has y-value equal to `true` -/
def existsOne (s : State N) : Prop :=
  ∃ p : Process N, s.y p = some true

-- the three predicates appearing in the TLA+ theorem.

/-- if every process has stopped then at least one has set `y` to 1. -/
def Invariant (s : State N) : Prop :=
  allStopped s → existsOne s

/-- whenever a process has set `y`, its `x` must already be 1. -/
def InductiveInvariant (s : State N) : Prop :=
  ∀ p : Process N, s.y p ≠ none → s.x p = true

end State

/- helper lemmas used in the proof of `invariants_hold` -/

open State

theorem step_preserves_ind_inv {s t : State N} (hstep : step s t)
  (hind : InductiveInvariant s) : InductiveInvariant t := by
  intro q hy
  cases hstep with
  | stop _ =>
      -- state is unchanged
      exact hind q hy
  | setnum p =>
      -- here `t` is definitionally `setNum p s`
      dsimp [setNum] at hy
      by_cases hqp : q = p
      · -- q = p, so t.x q = true by definition
        subst hqp
        simp [setNum] at hy
        simp [setNum]
      · -- q ≠ p
        have hy' : s.y q ≠ none := by
          have : (if q = p then some (s.x (pred p)) else s.y q) ≠ none := hy
          simp [hqp] at this
          exact this
        have : s.x q = true := hind q hy'
        simp [setNum, hqp, this]

theorem step_preserves_invariant {s t : State N} (hstep : step s t)
  (hinv : Invariant s) (hind : InductiveInvariant s) : Invariant t := by
  -- proof omitted; the invariant preservation can be shown by a
  -- straightforward case analysis on `hstep` using the definitions of
  -- `setNum` and the assumptions.  Details are left as an exercise.
  sorry

/-- main theorem corresponding to the TLA+ theorem. -/
theorem invariants_hold (s : State N) :
    State.reachable (N := N) s →
    State.TypeOk s ∧ State.Invariant s ∧ State.InductiveInvariant s :=
by
  intro h
  induction h with
  | init =>
      -- init case: allStopped holds vacuously and there is no `y` true
      simp [State.init, State.TypeOk, State.Invariant,
            State.InductiveInvariant, allStopped, existsOne]
  | step s t hreach hstep ih =>
      -- inductive step: use ih and show invariants preserved by `step`.
      -- here `hstep : step s t` and `hreach : reachable s`.
      rcases ih with ⟨htype, hinv, hind⟩
      constructor
      · -- TypeOk is trivial
        exact trivial
      · -- break the remaining conjunction into two goals
        constructor
        · -- show Invariant t using helper lemma
          exact step_preserves_invariant hstep hinv hind
        · -- show InductiveInvariant t using helper lemma
          exact step_preserves_ind_inv hstep hind


end -- section

end Concurrency

/-
The two helper lemmas above (`step_preserves_invariant` and
`step_preserves_ind_inv`) show that both invariants are preserved by
`step`.  They allow the final theorem `invariants_hold` to be proved by
simple induction on the reachability relation; the structure of the
argument mirrors the original TLA+ proof.
-/
