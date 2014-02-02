module Main

import Data.Buffer

em : Buffer 0
em = allocate 4

one : Bits32
one = 1

two : Bits8
two = 2

firstHalf : Buffer 4
firstHalf = appendBits32LE em one

full : Buffer 8
full = appendBits8 ( appendBits8 ( appendBits8 ( appendBits8 firstHalf two ) two ) two ) two

firstByte : Bits8
firstByte = peekBits8 full 0

firstHalfView : Buffer 4
firstHalfView = peekBuffer full 0

firstHalfCopy : Buffer 4
firstHalfCopy = copy firstHalfView

oneFromFirstHalf : Bits32
oneFromFirstHalf = peekBits32LE firstHalf 0

oneFromFirstHalfCopy : Bits32
oneFromFirstHalfCopy = peekBits32LE firstHalfCopy 0

viewsAndCopiesPreserveEquality : Bool
viewsAndCopiesPreserveEquality = ( oneFromFirstHalf == one ) && ( oneFromFirstHalfCopy == one )

secondHalfWord : Bits32
secondHalfWord = peekBits32LE full 4

main : IO ()
main = do
  putStrLn $ show firstByte
  putStrLn $ show viewsAndCopiesPreserveEquality
  putStrLn $ show secondHalfWord
