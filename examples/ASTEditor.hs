{-# LANGUAGE FlexibleContexts #-}

module ASTEditor where

-- This is currently more a navigator than an editor, because
-- there is no way to update the value yet.

import AST

import Generics.MultiRec.Base
import Generics.MultiRec.Zipper
import Generics.MultiRec.Show as GS

import Control.Monad

-- | Call this to start the navigation demo.
startEditor :: IO ()
startEditor = 
  do
    intro
    loop $ enter Expr example

example = Let (Seq ("x" := Mul (Const 6) (Const 9)) ("y" := Const (-12)))
              (Add (EVar "x") (EVar "y"))

-- | Show the current location, with the focus being highlighted in red.
-- Uses ugly non-portable escape codes at the moment.
showZipper :: Loc AST I0 Expr -> String
showZipper l = (spaces $ map ($ 0) $ unK0 (foldZipper focus hShowsPrecAlg l)) ""
  where focus :: (Ix AST ix) => AST ix -> ix -> K0 ([Int -> ShowS]) ix
        focus ix x = K0 [const $ ("\ESC[01;31m{" ++) . GS.showsPrec ix 0 x . ("}\ESC[00m" ++)]

-- | Main loop. Prints current location, asks for a command and executes
-- a navigation operation depending on that command.
loop :: Loc AST I0 Expr -> IO ()
loop l =
  do
    putStr (showZipper l)
    cmd <- getChar
    putStr "\r\ESC[2K"
    when (cmd == 'q') $ putStrLn ""
    when (cmd /= 'q') $ do
      let op = case cmd of
                'j' -> down
                'l' -> right
                'h' -> left
                'k' -> up
                _   -> return
      case op l of
        Nothing -> loop l
        Just l' -> loop l'

-- | Introductory help message.
intro :: IO ()
intro =
  putStrLn "h: left, j: down, k: up, l: right, q: quit"
