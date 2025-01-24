import Checker

open Lean

-- def modules : Array Import := #[
--   `Smt.Reconstruct.Builtin.Lemmas,
--   `Smt.Reconstruct.Builtin.Rewrites,
--   `Smt.Reconstruct.Int.Lemmas,
--   `Smt.Reconstruct.Int.Polynorm,
--   `Smt.Reconstruct.Int.Rewrites,
--   `Smt.Reconstruct.Prop.Core,
--   `Smt.Reconstruct.Prop.Lemmas,
--   `Smt.Reconstruct.Prop.Rewrites,
--   `Smt.Reconstruct.Quant.Lemmas,
--   `Smt.Reconstruct.Rat.Core,
--   `Smt.Reconstruct.Rat.Lemmas,
--   `Smt.Reconstruct.Rat.Polynorm,
--   `Smt.Reconstruct.Rat.Rewrites,
--   -- `Smt.Reconstruct.Real.Polynorm,
--   -- `Smt.Reconstruct.Real.Lemmas,
--   -- `Smt.Reconstruct.Real.Rewrites,
--   `Smt.Reconstruct.UF.Rewrites
-- ]

def module : Array Import := #[
  `Definitions
]

namespace Checker

open cvc5 in
def solve' (query : String) : IO (Except Error Proof) := do
  Solver.run (← TermManager.new) do
    Solver.setOption "dag-thresh" "0"
    Solver.setOption "enum-inst" "true"
    Solver.setOption "cegqi-midpoint" "true"
    Solver.setOption "produce-proofs" "true"
    Solver.setOption "proof-elim-subtypes" "true"
    Solver.setOption "proof-granularity" "dsl-rewrite"
    Solver.parse query
    let r ← Solver.checkSat
    if r.isUnsat then
      let ps ← Solver.getProof
      if h : 0 < ps.size then
        return ps[0]
    throw (Error.error s!"Expected unsat, got {r}")

def checkAndPrintLogs (pf : cvc5.Proof) : MetaM Unit := do
  activateScoped `Classical
  checkProof pf
  printTraces
  Language.reportMessages (← Core.getMessageLog) (← getOptions)

unsafe def solveAndCheck' (query : String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r ← solve' query
  let t1 ← IO.monoMsNow
  IO.printlnAndFlush s!"[time] solve: {t1 - t0}"
  match r with
  | .error e =>
    IO.eprintln (repr e)
  | .ok pf =>
    let t0 ← IO.monoMsNow
    initSearchPath (← findSysroot)
    withImportModules module Options.empty 0 fun env => do
      let t1 ← IO.monoMsNow
      IO.printlnAndFlush s!"[time] load: {t1 - t0}"
      let coreContext := { fileName := "cpc-checker", fileMap := default }
      let coreState := { env }
      _ ← Meta.MetaM.toIO (checkAndPrintLogs pf) coreContext coreState

end Checker

unsafe def main (args : List String) : IO Unit := do
  let query ← IO.FS.readFile args[0]!
  Checker.solveAndCheck' query
