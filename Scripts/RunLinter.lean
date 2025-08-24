import Lean.Util.SearchPath
import Batteries.Tactic.Lint
import Batteries.Data.Array.Basic
import Lake.CLI.Main

namespace Scripts

open Lean Core Elab Command Batteries.Tactic.Lint
open System (FilePath)

abbrev NoLints := Array (Name × Name)

def readJsonFile (α) [FromJson α] (path : System.FilePath) : IO α := do
  let _ : MonadExceptOf String IO := ⟨throw ∘ IO.userError, fun x _ => x⟩
  liftExcept <| fromJson? <|← liftExcept <| Json.parse <|← IO.FS.readFile path

def writeJsonFile [ToJson α] (path : System.FilePath) (a : α) : IO Unit :=
  IO.FS.writeFile path <| toJson a |>.pretty.push '\n'

open Lake

def resolveDefaultRootModules : IO (Array Name) := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let some workspace ← loadWorkspace config |>.toBaseIO
    | throw <| IO.userError "failed to load Lake workspace"
  let defaultTargetModules := workspace.root.defaultTargets.flatMap fun target =>
    if let some lib := workspace.root.findLeanLib? target then
      lib.roots
    else if let some exe := workspace.root.findLeanExe? target then
      #[exe.config.root]
    else
      #[]
  return defaultTargetModules

def parseLinterArgs (args: List String) : Except String (Bool × Option Name) :=
  let (update, moreArgs) :=
    match args with
    | "--update" :: args => (true, args)
    | _ => (false, args)
  match moreArgs with
    | [] => Except.ok (update, none)
    | [mod] => match mod.toName with
      | .anonymous => Except.error "cannot convert module to Name"
      | name => Except.ok (update, some name)
    | _ => Except.error "cannot parse arguments"

def determineModulesToLint (specifiedModule : Option Name) : IO (Array Name) := do
  match specifiedModule with
  | some module =>
    println!"Running linter on specified module: {module}"
    return #[module]
  | none =>
    println!"Automatically detecting modules to lint"
    let defaultModules ← resolveDefaultRootModules
    println!"Default modules: {defaultModules}"
    return defaultModules

unsafe def runLinterOnModule (update : Bool) (module : Name): IO Unit := do
  initSearchPath (← findSysroot)
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    let child ← IO.Process.spawn {
      cmd := (← IO.getEnv "LAKE").getD "lake"
      args := #["build", s!"+{module}"]
      stdin := .null
    }
    _ ← child.wait
  let lintModule := `Batteries.Tactic.Lint
  let lintFile ← findOLean lintModule
  unless (← lintFile.pathExists) do
    let child ← IO.Process.spawn {
      cmd := (← IO.getEnv "LAKE").getD "lake"
      args := #["build", s!"+{lintModule}"]
      stdin := .null
    }
    _ ← child.wait
  let nolintsFile : FilePath := "scripts/nolints.json"
  let nolints ← if ← nolintsFile.pathExists then
    readJsonFile NoLints nolintsFile
  else
    pure #[]
  unsafe Lean.enableInitializersExecution
  let env ← importModules #[module, lintModule] {} (trustLevel := 1024) (loadExts := true)
  let ctx := { fileName := "", fileMap := default }
  let state := { env }
  Prod.fst <$> (CoreM.toIO · ctx state) do
    let decls ← getDeclsInPackage module.getRoot
    let linters ← getChecks (slow := true) (runAlways := none) (runOnly := none)
    let results ← lintCore decls linters
    if update then
      writeJsonFile (α := NoLints) nolintsFile <|
        .qsort (lt := fun (a, b) (c, d) => a.lt c || (a == c && b.lt d)) <|
        .flatten <| results.map fun (linter, decls) =>
        decls.fold (fun res decl _ => res.push (linter.name, decl)) #[]
    let results := results.map fun (linter, decls) =>
      .mk linter <| nolints.foldl (init := decls) fun decls (linter', decl') =>
        if linter.name == linter' then decls.erase decl' else decls
    let failed := results.any (!·.2.isEmpty)
    if failed then
      let fmtResults ←
        formatLinterResults results decls (groupByFilename := true) (useErrorFormat := true)
          s!"in {module}" (runSlowLinters := true) .medium linters.size
      IO.print (← fmtResults.toString)
      IO.Process.exit 1
    else
      IO.println s!"-- Linting passed for {module}."

unsafe def main (args : List String) : IO Unit := do
  let linterArgs := parseLinterArgs args
  let (update, specifiedModule) ← match linterArgs with
    | Except.ok args => pure args
    | Except.error msg => do
      IO.eprintln s!"Error parsing args: {msg}"
      IO.eprintln "Usage: runLinter [--update] [My.Project.Root]"
      IO.Process.exit 1

  let modulesToLint ← determineModulesToLint specifiedModule

  modulesToLint.forM <| runLinterOnModule update

end Scripts

unsafe def main (args : List String) : IO Unit := Scripts.main args
