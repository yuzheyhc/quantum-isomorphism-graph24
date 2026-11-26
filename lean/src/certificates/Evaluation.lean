import Lean

open Lean Elab Tactic

/-- Set this option to true to replay every witness with kernel reduction. -/
register_option qgi.kernelWitnesses : Bool := {
  defValue := false
  descr := "Use kernel reduction to check the individual colored counting witnesses"
}

/-- Both modes check the same closed Boolean equality. The normal build uses
Lean's native evaluator. Each witness retains its own declaration and inputs. -/
elab "verify_count" : tactic => do
  if qgi.kernelWitnesses.get (← getOptions) then
    evalTactic (← `(tactic| decide))
  else
    evalTactic (← `(tactic| native_decide))
