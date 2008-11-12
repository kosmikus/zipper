{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeFamilies     #-}

module ASTExamples where

import Data.Maybe (fromJust)
import Control.Arrow ((>>>))
import Control.Monad ((>=>))

import AST

import Generics.MultiRec.Zipper

-- | Example expression

example = Let ("x" := Mul (Const 6) (Const 9))
              (Add (EVar "x") (EVar "y"))

-- | Test for the generic zipper

testZipper :: Maybe Expr
testZipper =
    enter Expr   >>>
    down         >=>
    down         >=>
    right        >=>
    update solve >>>
    leave        >>>
    return        $  example
  where
    solve :: AST ix -> ix -> ix
    solve Expr _ = Const 42
    solve _    x = x



