/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.Workspace

/-! # Cleaning Lake Outputs

This module contains the API definitions of implementing `lake clean`.
-/

open System

namespace Lake

/--
Remove the package's Lake outputs
(i.e., delete its build directory and compiled configuration).
-/
def Package.clean (self : Package) : LogIO Bool := do
  -- Remove cached configuration
  let some configName := FilePath.mk <$> self.configFile.fileName
    | logWarning s!"{self.name}: invalid configuration file name"
      return false
  let lockFile := self.lakeDir / configName.withExtension "olean.lock"
  let hLock ← IO.FS.Handle.mk lockFile .write
  if (← hLock.tryLock) then
    -- Remove build directory
    if (← self.buildDir.pathExists) then
      IO.FS.removeDirAll self.buildDir
    -- Remove cached configuration
    let olean := self.lakeDir / configName.withExtension "olean"
    let traceFile := self.lakeDir / configName.withExtension "olean.trace"
    if (← olean.pathExists) then
      IO.FS.removeFile olean
    if (← traceFile.pathExists) then
      IO.FS.removeFile traceFile
    hLock.unlock
    return true
  else
    logWarning s!"{self.name}: \
      could not acquire an exclusive configuration lock; \
      another process may be reconfiguring the package"
    return false

/--
Remove the workspace's Lake outputs
(i.e., delete each package's build directory and compiled configuration).
-/
def Workspace.clean (self : Workspace) : LogIO Bool := do
  self.packages.foldlM (init := true) fun ok pkg => return ok && (← pkg.clean)
