import JPEG2000
import Lean

/-!
# Public entry point totality audit (Plan.md §3 and §4, S2)

Walk the kernel declarations reachable from the decoder and display functions, including
their types. Project functions must expose a safe implementation. Lean generates a
native constructor-index primitive for inductive types with multiple constructors.
-/

open Lean Elab Command

namespace ClosureAudit

private partial def reachable (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reachable env rest seen
    else
      let deps := match env.find? n with
        | none => #[]
        | some info => info.type.getUsedConstants ++
            (info.value?.map Expr.getUsedConstants).getD #[]
      reachable env (deps.toList ++ rest) (seen.insert n)

private def projectDecl (env : Environment) (n : Name) : Bool :=
  let module := (env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?
  (`JPEG2000).isPrefixOf (privateToUserName n) ||
    module.any fun m => [`JPEG2000, `Spec, `Encode].any (·.isPrefixOf m)

private def compilerCtorIdx (env : Environment) (n impl : Name) : Bool :=
  (isCtorIdxCore? env n).isSome && impl == n.str "_impl"

elab "#check_closure " id:ident : command => do
  let root ← resolveGlobalConstNoOverload id
  let env ← getEnv
  let all := reachable env [root] {}
  let mut count := 0
  for n in all.toList do
    let some info := env.find? n | throwError "unknown declaration {n} reachable from {root}"
    if info.isUnsafe then throwError "{root} depends on unsafe declaration {n}"
    if info matches .axiomInfo _ then
      unless [``propext, ``Classical.choice, ``Quot.sound].contains n do
        throwError "{root} depends on unapproved axiom {n}"
    if projectDecl env n then
      count := count + 1
      if info matches .opaqueInfo _ then
        throwError "{root} depends on opaque project declaration {n}"
      if isExtern env n then throwError "{root} depends on external project declaration {n}"
      if let some impl := Compiler.implementedByAttr.getParam? env n then
        unless compilerCtorIdx env n impl do
          throwError "{root} reaches implementation override {n} -> {impl}"
  logInfo m!"{root}: checked {all.size} reachable declarations ({count} project declarations)"

#check_closure JPEG2000.decodeCodestream
#check_closure JPEG2000.decode
#check_closure JPEG2000.Image.interleaved8
#check_closure JPEG2000.Image.interleaved16

end ClosureAudit
