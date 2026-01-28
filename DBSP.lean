-- This module serves as the root of the `DBSP` library.
-- Import modules here that should be built as part of the library.

-- The definition of DBSP (well-formed) circuits and their denotational semantics.
import DBSP.Circuits.Circuits

-- The termination specification and detection algorithm
import DBSP.Termination.Spec
import DBSP.Termination.FPDetector

-- Equivalence and refinement between DBSP circuits
import DBSP.Practical.Sequiv
import DBSP.Practical.Refine

-- The correctness and efficiency (in terms of iteration bounds) of DBSP optimization transformations
import DBSP.Practical.PushLifting
import DBSP.Practical.Incrementalize

-- The Hoare logics
import DBSP.Logic.Hoare
import DBSP.Logic.HoareT
