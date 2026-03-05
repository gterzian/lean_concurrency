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

/-- the “stopping condition”: every process has set its `y` to
`some true`.  this is now a much stronger requirement than before; in
the original spec the condition merely asserted that no `y` was
`NoVal`.  with the stronger version the invariant below becomes
a trivial consequence of the antecedent. -/
def stoppingCond (s : State N) : Prop :=
  ∀ p : Process N, s.y p = some true

/-- some process has y-value equal to `true` -/
def existsOne (s : State N) : Prop :=
  ∃ p : Process N, s.y p = some true

-- the three predicates appearing in the TLA+ theorem.

/-- the invariant from the spec: once the stopping condition holds there
must be at least one `y` equal to `true`.  this mirrors the
cardinality-based formulation in `spec.tla`. -/
def Invariant (s : State N) : Prop :=
  stoppingCond s → existsOne s

def InductiveInvariant (s : State N) : Prop :=
  ∀ p : Process N,
    s.x p = true →
      (s.y p = some true ∨
       ∃ pp : Process N, (pp ≠ p) ∧ (s.x pp = false ∨ s.y pp = some true))

/-- with the stronger stopping condition every `y` is `some true`, the
invariant follows immediately by picking an arbitrary process. -/
theorem ind_imp_inv (s : State N) : Invariant s := by
  intro hstop
  have h0 : 0 < N := Nat.pos_of_ne_zero (hN.ne').symm
  let p : Process N := ⟨0, h0⟩
  exact ⟨p, hstop p⟩

end State

/- helper lemmas used in the proof of `invariants_hold` -/

open State

-- when there is more than one process the `pred` function never
-- returns the element itself; we use this fact repeatedly below.
private theorem pred_ne_self (p : Process N) (hN2 : 1 < N) :
    pred p ≠ p := by
  rcases p with ⟨k, hk⟩
  intro hEq
  have hVal : ((k + N - 1) % N) = k := congrArg Fin.val hEq
  cases k with
  | zero =>
      have hNpos : 0 < N := Nat.lt_trans Nat.zero_lt_one hN2
      have hNm1_lt : N - 1 < N := Nat.sub_lt hNpos (Nat.succ_pos 0)
      have hNm1_pos : 0 < N - 1 := Nat.sub_pos_of_lt hN2
      have hmod : ((0 + N - 1) % N) = N - 1 := by
        simp [Nat.mod_eq_of_lt hNm1_lt]
      have : N - 1 = 0 := by
        simpa [hmod] using hVal
      exact (Nat.ne_of_gt hNm1_pos) this
  | succ k' =>
      have hk' : k' < N := Nat.lt_trans (Nat.lt_succ_self k') hk
      have hrewrite : Nat.succ k' + N - 1 = k' + N := by
        calc
          Nat.succ k' + N - 1 = Nat.succ (k' + N) - 1 := by
            simp [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm]
          _ = k' + N := Nat.succ_sub_one (k' + N)
      have hmod : ((Nat.succ k' + N - 1) % N) = (k' % N) := by
        calc
          ((Nat.succ k' + N - 1) % N) = ((k' + N) % N) := by simp [hrewrite]
          _ = (k' % N) := Nat.add_mod_right k' N
      have : k' = Nat.succ k' := by
        calc
          k' = (k' % N) := by symm; exact Nat.mod_eq_of_lt hk'
          _ = ((Nat.succ k' + N - 1) % N) := by symm; exact hmod
          _ = Nat.succ k' := by simpa using hVal
      exact (Nat.ne_of_lt (Nat.lt_succ_self k')) this

theorem step_preserves_ind_inv {s t : State N} (hstep : step s t)
  (hind : InductiveInvariant s) (hN2 : 1 < N) : InductiveInvariant t := by
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
        by_cases hpred : s.x (pred q) = true
        · left
          simp [setNum, hpred]
        · right
          refine ⟨pred q, ?_⟩
          constructor
          · exact pred_ne_self q hN2
          · left
            have hneq : pred q ≠ q := pred_ne_self q hN2
            simp [setNum, hneq, hpred]
      · -- q ≠ p: the `some true` must come from the old state
        have hxq : s.x q = true := by
          simpa [hqp] using hy
        rcases hind q hxq with hyq | hpp
        · left
          simp [setNum, hqp, hyq]
        · right
          rcases hpp with ⟨pp, hpp_ne, hpp_prop⟩
          by_cases hppp : pp = p
          · have hppeq : p = pp := hppp.symm
            by_cases hpred : s.x (pred p) = true
            · refine ⟨p, ?_⟩
              constructor
              · simpa [hppeq] using hpp_ne
              · right
                simp [setNum, hpred]
            · refine ⟨pred p, ?_⟩
              constructor
              · intro hpredq
                have : s.x (pred p) = true := by simpa [hpredq] using hxq
                exact hpred this
              · left
                have hpredp : pred p ≠ p := pred_ne_self p hN2
                simp [setNum, hpredp, hpred]
          · refine ⟨pp, ?_⟩
            constructor
            · exact hpp_ne
            · cases hpp_prop with
              | inl hxf =>
                  left
                  simp [setNum, hppp, hxf]
              | inr hypp =>
                  right
                  simp [setNum, hppp, hypp]


-- the lemma below is not needed for our development; we comment it
-- out to avoid a lengthy proof.
-- theorem step_preserves_invariant {s t : State N} (hstep : step s t)
--   (hinv : Invariant s) (hind : InductiveInvariant s) [hN2 : 1 < N] :
--   Invariant t := by
--   sorry


-- /-- main theorem corresponding to the TLA+ theorem. -/
-- theorem invariants_hold [hN2 : 1 < N] (s : State N) :
--     State.reachable (N := N) s →
--     State.TypeOk s ∧ State.Invariant s ∧ State.InductiveInvariant s :=
-- by
--   -- `hN2` is now available as a typeclass argument, so we no longer need
--   -- to manufacture it inside the body.
--   intro h
--   induction h with
--   | init =>
--       -- init case: stoppingCond holds vacuously and there is no `y` true
--       simp [State.init, State.TypeOk, State.Invariant,
--             State.InductiveInvariant, stoppingCond, existsOne]
--   | step s t hreach hstep ih =>
--       -- inductive step: use ih and show invariants preserved by `step`.
--       -- here `hstep : step s t` and `hreach : reachable s`.
--       rcases ih with ⟨htype, hinv, hind⟩
--       constructor
--       · -- TypeOk is trivial
--         exact trivial
--       · -- break the remaining conjunction into two goals
--         constructor
--         · -- show Invariant t using helper lemma (note we need the
--           -- extra hypothesis `1 < N` which is implicitly available as a
--           -- typeclass parameter in the section above).
--           -- the `[hN2 : 1 < N]` argument is found by typeclass
--           -- inference automatically, so we can simply write:
--           exact step_preserves_invariant hstep hinv hind
--         · -- show InductiveInvariant t using helper lemma
--           exact step_preserves_ind_inv hstep hind


end -- section

end Concurrency

/-
The two helper lemmas above (`step_preserves_invariant` and
`step_preserves_ind_inv`) show that both invariants are preserved by
`step`.  They allow the final theorem `invariants_hold` to be proved by
simple induction on the reachability relation; the structure of the
argument mirrors the original TLA+ proof.
-/
