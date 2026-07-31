-- SPDX-License-Identifier: MIT

import ClausalProofInterpolation

/-!
Executable entry point for the CraigCongruence development. Importing the
top-level interpolation library also checks its complete dependency closure.
-/

def main : IO Unit :=
  IO.println "CraigCongruence: verified EUF interpolation"
