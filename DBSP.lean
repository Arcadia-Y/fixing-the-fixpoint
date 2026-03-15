-- This module serves as the root of the `DBSP` library.
-- Import modules here that should be built as part of the library.

-- The definition of DBSP (well-formed) circuits and their denotational semantics.
import DBSP.Circuits.Circuits

-- The convergence specification and detection algorithm
import DBSP.Convergence.Spec
import DBSP.Convergence.FPDetector

-- Convergence-complete circuits and fixpoint-complete circuits, our core concept for arguing about the practicality of the new convergence specification.
import DBSP.Practical.ConvComplete
-- Semantic equivalence and convergence equivalence between DBSP circuits
import DBSP.Practical.Sequiv
import DBSP.Practical.ConvEq
-- The correctness and efficiency (in terms of iteration bounds) of DBSP optimization transformations
import DBSP.Practical.PushLifting
import DBSP.Practical.IncOpt
-- Regular Circuits and their inner iteration bounds
import DBSP.Practical.Expressiveness
import DBSP.Practical.RegularCkt

-- The Hoare logics
import DBSP.Logic.Hoare
import DBSP.Logic.HoareT

-- The cost model and logic for resource analysis
import DBSP.ResourceAnalysis.CktCost
import DBSP.ResourceAnalysis.HoareR

-- The ZsetCkt case study
import DBSP.ZsetCkt.ZsetCkt
import DBSP.ZsetCkt.JoinExample
import DBSP.ZsetCkt.GraphExample
import DBSP.ZsetCkt.GraphExampleIncOpt
import DBSP.ZsetCkt.FirstZeroCounterexample
