import VersoManual
import Audit

open Verso Doc Genre Manual

def main := manualMain (%doc Audit) (config := {
  emitTeX := false
  emitHtmlSingle := .immediately
  emitHtmlMulti := .no
})
