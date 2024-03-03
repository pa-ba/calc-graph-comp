{-# OPTIONS --sized-types #-}

module Everything where

-- partiality monad
import Partial

-- generic definition of tree-based and graph-based code
import Code

-- compiler calculations from paper
import Cond
import Repeat
import WhileState

-- addtional calculations
import While
import Exception
import Termination.Exception -- termination proof

-- some examples (for the while language)
import Examples

-- calculation of execG from exec
import ExecG


-- De Bruijn version of graph-based code
import DeBruijn.Code
import DeBruijn.Repeat
import DeBruijn.While
import DeBruijn.WhileState