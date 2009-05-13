{-# LANGUAGE FlexibleContexts #-}

module Main where

-- This is currently more a navigator than an editor, because
-- there is no way to update the value yet.
-- Also, the implementation uses ugly non-portable ANSI escape codes
-- at the moment.

import AST
import ASTUse

import Generics.MultiRec.Base
import Generics.MultiRec.Zipper
import Generics.MultiRec.Show as GS

import System.IO
import Control.Monad

main :: IO ()
main = startEditor

-- | Call this to start the navigation demo.
startEditor :: IO ()
startEditor = 
  do
    intro
    hSetBuffering stdin NoBuffering
    loop $ enter Expr example

example = Let (Seq (Seq ("x" := Mul (Const 6) (Const 9)) ("y" := Const (-12))) None)
              (Add (EVar "x") (EVar "y"))

-- | Show the current location, with the focus being highlighted in red.
showZipper :: Loc AST I0 Expr -> String
showZipper l = (spaces $ map ($ 0) $ unK0 (foldZipper focus (\ p x -> K0 (hShowsPrecAlg p x)) l)) ""
  where focus :: AST ix -> ix -> K0 ([Int -> ShowS]) ix
        focus ix x = K0 [\ n -> ("\ESC[01;31m" ++) . GS.showsPrec ix n x . ("\ESC[00m" ++)]

typeOfFocus :: Loc AST I0 Expr -> String
typeOfFocus = on focus
  where focus :: AST ix -> I0 ix -> String
        focus Expr _ = "expression"
        focus Decl _ = "declaration"
        focus Var  _ = "variable"

-- | Main loop. Prints current location, asks for a command and executes
-- a navigation operation depending on that command.
loop :: Loc AST I0 Expr -> IO ()
loop l =
  do
    putStr $ (showZipper l) ++ " {" ++ typeOfFocus l ++ "}"
    cmd <- getChar
    putStr "\r\ESC[2K"
    when (cmd == 'q') $ putStrLn ""
    when (cmd /= 'q') $ do
      let op = case cmd of
                'j'  -> down
                'l'  -> right
                'h'  -> left
                'k'  -> up
                ' '  -> dfnext
                'n'  -> dfnext
                'b'  -> dfprev
                _    -> return
      case op l of
        Nothing -> loop l
        Just l' -> loop l'

-- | Introductory help message.
intro :: IO ()
intro =
  putStrLn "h: left, j: down, k: up, l: right, q: quit, n,[space]: df lr traversal, b: df rl traversal"
