import VersoManual
import Audit.Model
import Audit.Exchange
import Audit.Resolution
import Audit.Interface
import Audit.Examples
import Audit.Scope
import Audit.Reference

open Verso.Genre Manual

#doc (Manual) "Craig interpolation for EUF" =>
%%%
shortTitle := "EUF interpolation"
%%%

An equality proof can explain why two inputs contradict each other while
revealing symbols private to either input. Craig interpolation asks for a
different explanation: a formula in their shared vocabulary that follows
from the first input and contradicts the second. Removing private symbols
must preserve the dependencies that made the equality proof work.

This development makes those dependencies explicit. An equality passed
between the two sides carries its justification. The extractor turns the
first side's justifications into conditional equalities, then carries their
meaning through a clausal refutation. A second extraction route reads shared
clauses directly from a proof that already obeys a suitable dependency cut.
Both routes prove the Craig conditions for supplied proof evidence.

The manual explains why the proof objects have this shape and where their
soundness arguments meet. Read the model, equality exchange, and resolution
chapters in order. The shared-interface chapter presents the alternative
route. The examples expose choices that are easy to miss in the abstract
definitions. Scope and references identify the hypotheses and declarations
to inspect when auditing the code.

{include 1 Audit.Model}

{include 1 Audit.Exchange}

{include 1 Audit.Resolution}

{include 1 Audit.Interface}

{include 1 Audit.Examples}

{include 1 Audit.Scope}

{include 1 Audit.Reference}
