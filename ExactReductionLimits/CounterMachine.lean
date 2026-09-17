import Mathlib

noncomputable section

/-!
# Deterministic two-counter machines and the free-site zero test

This file formalizes the discrete computation encoded in Section 5.  The graph
syntax of roots and token chains is represented by its exact invariant: a free
root iff the encoded counter is zero, and mutually exclusive local variants for
zero, one-token, and multi-token cases.
-/

namespace ExactReductionLimits
namespace CounterMachine

inductive CounterSel where
  | first
  | second
  deriving DecidableEq, Repr

inductive Instr (PC : Type*) where
  | inc (which : CounterSel) (next : PC)
  | jzdec (which : CounterSel) (ifZero ifPositive : PC)
  | halt
  deriving Repr

structure Config (PC : Type*) where
  pc : PC
  c1 : ℕ
  c2 : ℕ
  deriving DecidableEq, Repr

structure Machine (PC : Type*) where
  instr : PC → Instr PC

/-- Read one counter. -/
def readCounter {PC : Type*} (which : CounterSel) (c : Config PC) : ℕ :=
  match which with
  | .first => c.c1
  | .second => c.c2

/-- Update one counter, preserving the other. -/
def writeCounter {PC : Type*}
    (which : CounterSel) (n : ℕ) (c : Config PC) : Config PC :=
  match which with
  | .first => { c with c1 := n }
  | .second => { c with c2 := n }

/-- One deterministic INC/JZDEC machine step; halt has no successor. -/
def step {PC : Type*} [DecidableEq PC]
    (M : Machine PC) (c : Config PC) : Option (Config PC) :=
  match M.instr c.pc with
  | .halt => none
  | .inc which next =>
      some { (writeCounter which (readCounter which c + 1) c) with pc := next }
  | .jzdec which q0 q1 =>
      if readCounter which c = 0 then
        some { c with pc := q0 }
      else
        some { (writeCounter which (readCounter which c - 1) c) with pc := q1 }

/-- Rooted-chain representation of a counter at the invariant level. -/
structure EncodedCounter where
  tokens : ℕ
  deriving DecidableEq, Repr

/-- In ordinary Kappa the root site is free exactly in the zero case. -/
def rootFree (c : EncodedCounter) : Prop := c.tokens = 0

@[simp] theorem rootFree_iff_zero (c : EncodedCounter) :
    rootFree c ↔ c.tokens = 0 := Iff.rfl

/-- The local rule variant enabled at the root. -/
inductive LocalVariant where
  | incZero
  | incPositive
  | branchZero
  | decOne
  | decMany
  | halted
  deriving DecidableEq, Repr

/-- The free/bound root and one/many-token tests select exactly one finite local
variant. -/
def enabledVariant {PC : Type*} (i : Instr PC) (n : ℕ) : LocalVariant :=
  match i with
  | .halt => .halted
  | .inc _ _ => if n = 0 then .incZero else .incPositive
  | .jzdec _ _ _ =>
      if n = 0 then .branchZero else if n = 1 then .decOne else .decMany

/-- The finite-rule encoding has exactly one enabled instruction variant for
every non-halted machine configuration. -/
def enabledVariants {PC : Type*} (i : Instr PC) (n : ℕ) : List LocalVariant :=
  [enabledVariant i n]

@[simp] theorem exactly_one_enabled_variant
    {PC : Type*} (i : Instr PC) (n : ℕ) :
    (enabledVariants i n).length = 1 := by
  rfl

/-- The zero and nonzero root conditions are mutually exclusive and exhaustive. -/
theorem zero_test_exact (n : ℕ) : (n = 0) ↔ ¬ 0 < n := by
  omega

/-- Within the positive branch, one-token and multi-token cases are mutually
exclusive and exhaustive. -/
theorem positive_is_one_or_many {n : ℕ} (hn : 0 < n) :
    n = 1 ∨ 1 < n := by
  omega

/-- Numeric effect of the Kappa-style root insertion/removal rules. -/
def localCounterStep {PC : Type*} (i : Instr PC) (n : ℕ) : ℕ :=
  match i with
  | .halt => n
  | .inc _ _ => n + 1
  | .jzdec _ _ _ => if n = 0 then 0 else n - 1

/-- INC is exactly local insertion of one token. -/
@[simp] theorem localCounterStep_inc
    {PC : Type*} (which : CounterSel) (q : PC) (n : ℕ) :
    localCounterStep (Instr.inc which q) n = n + 1 := by
  rfl

/-- JZDEC is exact zero-test/decrement. -/
theorem localCounterStep_jzdec
    {PC : Type*} (which : CounterSel) (q0 q1 : PC) (n : ℕ) :
    localCounterStep (Instr.jzdec which q0 q1) n =
      if n = 0 then 0 else n - 1 := by
  rfl

end CounterMachine
end ExactReductionLimits
