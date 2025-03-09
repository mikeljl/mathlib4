import Std
import Batteries
import Mathlib.Algebra.AddConstMap.Basic
import Mathlib.Algebra.AddConstMap.Equiv
import Mathlib.Algebra.AddTorsor.Basic
import Mathlib.Algebra.AddTorsor.Defs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Field
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Quasispectrum
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Algebra.Spectrum
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Algebra.Subalgebra.Directed
import Mathlib.Algebra.Algebra.Subalgebra.IsSimpleOrder
import Mathlib.Algebra.Algebra.Subalgebra.MulOpposite
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.Algebra.Subalgebra.Order
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Pointwise
import Mathlib.Algebra.Algebra.Subalgebra.Prod
import Mathlib.Algebra.Algebra.Subalgebra.Rank
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.Algebra.Algebra.Subalgebra.Unitization
import Mathlib.Util.MemoFix
import Mathlib.Util.Notation3
import Mathlib.Util.PPOptions
import Mathlib.Util.ParseCommand
import Mathlib.Util.Qq
import Mathlib.Util.SleepHeartbeats
import Mathlib.Util.Superscript
import Mathlib.Util.SynthesizeUsing
import Mathlib.Util.Tactic
import Mathlib.Util.TermReduce
import Mathlib.Util.TransImports
import Mathlib.Util.WhatsNew
import Mathlib.Util.WithWeakNamespace
import docs
import Mathlib.Init
import Mathlib.Tactic
import Archive





open Nat (add_assoc add_comm)

theorem hello_world (a b c : Nat)
  : a + b + c = a + c + b := by
  -- Step 1: Rewrite using associativity of addition
  rw [add_assoc]
  -- Now we have (a + b) + c = a + c + b
  -- Step 2: Rewrite using commutativity of addition
  rw [add_comm b c]
  -- Now we have (a + c) + b = a + c + b
  -- Step 3: Rewrite using associativity of addition again
  rw [←add_assoc]
  -- Now we have a + (c + b) = a + c + b
