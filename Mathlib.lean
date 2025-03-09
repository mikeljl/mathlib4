import Std
import Batteries
import Mathlib.Algebra.AddConstMap.Basic
import docs
import Mathlib.Init
import Mathlib.Tactic
import Archive





-- open Nat (add_assoc add_comm)

-- theorem hello_world (a b c : Nat)
--   : a + b + c = a + c + b := by
--   -- Step 1: Rewrite using associativity of addition
--   rw [add_assoc]
--   -- Now we have (a + b) + c = a + c + b
--   -- Step 2: Rewrite using commutativity of addition
--   rw [add_comm b c]
--   -- Now we have (a + c) + b = a + c + b
--   -- Step 3: Rewrite using associativity of addition again
--   rw [←add_assoc]
--   -- Now we have a + (c + b) = a + c + b
