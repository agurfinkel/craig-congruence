import Lake
open Lake DSL

package craigAudit

-- Match the proof library's Lean release; keep documentation dependencies
-- out of the root package.
require verso from git "https://github.com/leanprover/verso" @
  "304b8561790c50222551c937ce02928df0d5b445"
require «craig-congruence» from "../.."

@[default_target]
lean_lib Audit

lean_exe audit where
  root := `Main
  supportInterpreter := true
