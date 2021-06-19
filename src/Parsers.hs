{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PatternSynonyms #-}
module Parsers where

import Prelude hiding (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred, repeat)
import Parsley
import Parsley.Combinator (noneOf)
import Parsley.Fold (skipMany)
import Parsley.Register (Reg, get, put, newRegister, newRegister_, gets_, modify, local, modify_, bind)
import Parsley.Defunctionalized (Defunc(..), pattern UNIT)
import Control.Monad (liftM)
import Data.Char (isAlpha, isAlphaNum, isSpace, isUpper, isDigit, digitToInt, chr, ord)
import Data.Set (fromList, member)
import Data.Maybe (catMaybes)
import Text.Read (readMaybe)
import Language.Haskell.TH.Syntax (Lift)

import qualified Prelude

data Expr = Var String | Num Int | Add Expr Expr deriving Show
data Asgn = Asgn String Expr deriving Show

data BrainFuckOp = RightPointer | LeftPointer | Increment | Decrement | Output | Input | Loop [BrainFuckOp] deriving (Show, Eq)
deriving instance Lift BrainFuckOp

cinput :: Parser String
cinput = m --try (string "aaa") <|> string "db" --(string "aab" <|> string "aac") --(char 'a' <|> char 'b') *> string "ab"
  where
    --m = match "ab" (lookAhead item) op empty
    --op 'a' = item $> code "aaaaa"
    --op 'b' = item $> code "bbbbb"
    m = bf <* item
    bf = match ">" item op empty
    op '>' = string ">"

regTest :: Parser Int
regTest = newRegister_ [|7|] (\r -> modify_ r [|succ @Int|] *> (let g = get r in g *> g))

defuncTest :: Parser (Maybe Int)
defuncTest = [|Just|] <$> ([|(+)|] <$> (item $> [|1|]) <*> (item $> [|8|]))

manyTest :: Parser [Char]
manyTest = many (try (string "ab") $> [|'c'|])

nfb :: Parser ()
nfb = notFollowedBy (char 'a') <|> void (string "ab")

skipManyInspect :: Parser ()
skipManyInspect = skipMany (char 'a')

boom :: Parser ()
boom = let foo = newRegister_ UNIT (\r0 ->
            let goo = newRegister_ UNIT (\r1 ->
                  let hoo = get r0 <~> get r1 *> hoo in hoo
                 ) *> goo
            in goo) *> pure UNIT
       in foo *> foo

brainfuck :: Parser [BrainFuckOp]
brainfuck = whitespace *> bf
  where
    whitespace = skipMany (noneOf "<>+-[],.$")
    lexeme p = p <* whitespace
    bf = many (lexeme (match "><+-.,[" (lookAhead item) op empty))
    op '>' = item $> [|RightPointer|]
    op '<' = item $> [|LeftPointer|]
    op '+' = item $> [|Increment|]
    op '-' = item $> [|Decrement|]
    op '.' = item $> [|Output|]
    op ',' = item $> [|Input|]
    op '[' = between (lexeme item) (char ']') ([|Loop|] <$> bf)

data Tape = Tape [Int] Int [Int]

emptyTape :: Tape
emptyTape = Tape (Prelude.repeat 0) 0 (Prelude.repeat 0)

right :: Tape -> Tape
right (Tape ls x (r:rs)) = Tape (x:ls) r rs
left :: Tape -> Tape
left (Tape (l:ls) x rs) = Tape ls l (x:rs)
readTape :: Tape -> Int
readTape (Tape _ x _) = x
writeTape :: Int -> Tape -> Tape
writeTape x (Tape ls _ rs) = Tape ls x rs
isLoop :: BrainFuckOp -> Bool
isLoop (Loop p) = True
isLoop p        = False
getLoop :: BrainFuckOp -> [BrainFuckOp]
getLoop (Loop p) = p
inc :: Int -> Int
inc = (+ 1)
dec :: Int -> Int
dec = subtract 1
toInt :: Char -> Int
toInt = toEnum . ord
toChar :: Int -> Char
toChar = chr . fromEnum

evalBf :: Parser [BrainFuckOp] -> Parser [Char]
evalBf loader =
  -- first step is to place the program into a register and read the delimiter, then set up the state
  newRegister loader $ \instrs ->
    delim *> newRegister_ (makeQ emptyTape [||emptyTape||]) (\tape ->
      newRegister_ EMPTY $ \out ->
           eval instrs tape out
        *> gets_ out [|reverse|])
  where
    delim :: Parser Char
    delim = char '$'

    eval :: Reg r1 [BrainFuckOp] -> Reg r2 Tape -> Reg r3 [Char] -> Parser ()
    eval instrs tape out =
      let go = predicate [|null|] (get instrs) unit $
            bind (gets_ instrs [|head|]) $ \op ->
              let evalLoop =
                    predicate (EQ_H [|0|]) read
                      unit
                      (local instrs ([|getLoop|] <$> op) go *> evalLoop)
              in modify_ instrs [|tail|]
              *> predicate [|isLoop|] op
                   evalLoop
                   (match [RightPointer, LeftPointer, Increment, Decrement, Output, Input] op evalOp' empty)
              *> go
      in go
      where
        evalOp' :: BrainFuckOp -> Parser ()
        evalOp' RightPointer = move [|right|]
        evalOp' LeftPointer  = move [|left|]
        evalOp' Increment    = update [|inc|]
        evalOp' Decrement    = update [|dec|]
        evalOp' Output       = print ([|toChar|] <$> read)
        evalOp' Input        = write ([|toInt|] <$> item)

        -- Operations
        move :: Defunc (Tape -> Tape) -> Parser ()
        move = modify_ tape
        print :: Parser Char -> Parser ()
        print x = modify out (CONS <$> x)
        read :: Parser Int
        read = gets_ tape [|readTape|]
        write :: Parser Int -> Parser ()
        write px = modify tape ([|writeTape|] <$> px)
        update :: Defunc (Int -> Int) -> Parser ()
        update f = write (f <$> read)
