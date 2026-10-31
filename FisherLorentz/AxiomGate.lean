/-
# The axiom gate as a build step

`#assert_standard_axioms_in FisherLorentz` makes the build itself fail if any theorem
of the library depends on an axiom other than the three standard axioms of Lean's logic,
`propext`, `Classical.choice` and `Quot.sound`. `sorry` (which introduces `sorryAx`) and
`native_decide` (which introduces `Lean.ofReduceBool`) are therefore rejected, whether or
not they appear in the source text. Every theorem whose name lies under the given
namespace is checked, in every imported module of the library and in the current file,
so a result that nobody remembered to list is still covered.
-/
import Lean

namespace FisherLorentz.AxiomGate

open Lean Elab Command

/-- The three standard axioms. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Theorem names under `pre`: from imported modules of the library, then the current file. -/
def theoremsUnder (env : Environment) (pre : Name) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for i in [0:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]!
    if pre.isPrefixOf mod then
      for ci in env.header.moduleData[i]!.constants do
        if ci.isTheorem && pre.isPrefixOf ci.name then out := out.push ci.name
  for (n, ci) in env.constants.map₂.toList do
    if ci.isTheorem && pre.isPrefixOf n then out := out.push n
  return out

/-- Fail the build if any theorem under the namespace uses a non-standard axiom. -/
elab "#assert_standard_axioms_in " ns:ident : command => do
  let pre := ns.getId
  let names := theoremsUnder (← getEnv) pre
  if names.isEmpty then throwError "axiom gate: no theorems found under {pre}"
  let mut bad : Array MessageData := #[]
  for n in names do
    let axs ← collectAxioms n
    let nonstd := axs.filter (fun a => !standardAxioms.contains a)
    unless nonstd.isEmpty do bad := bad.push m!"{n}: {nonstd.toList}"
  unless bad.isEmpty do
    throwError m!"axiom gate FAILED for {bad.size} theorem(s):\n{MessageData.joinSep bad.toList "\n"}"
  logInfo m!"axiom gate passed: {names.size} theorems under {pre} use only propext, Classical.choice, Quot.sound"

end FisherLorentz.AxiomGate
