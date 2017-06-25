module Bowling

import Data.Vect


--------------------------------------------------------------------------------
-- The Frames
--------------------------------------------------------------------------------

PinCount : Nat
PinCount = 10

ValidFrame : (x, y: Nat) -> Type
ValidFrame x y = (x + y `LTE` PinCount, x `LT` PinCount, y `LT` PinCount)

data Frame : Type where
  TwoRolls : (x, y : Nat) -> { auto prf : ValidFrame x y } -> Frame
  Strike : Frame

roll : (x, y: Nat) -> { auto prf : ValidFrame x y } -> Frame
roll {prf} x y = TwoRolls x y {prf}

strike : Frame
strike = Strike

isSpare : Frame -> Bool
isSpare (TwoRolls x y) = x + y == PinCount
isSpare _ = False

knockedPins : Frame -> List Nat
knockedPins (TwoRolls x y) = [x, y]
knockedPins Strike = [PinCount]


--------------------------------------------------------------------------------
-- The Game Types
--------------------------------------------------------------------------------

FrameCount : Nat
FrameCount = 10

bonusRolls : Frame -> Nat
bonusRolls Strike = 2
bonusRolls rolls = if isSpare rolls then 1 else 0

BonusRollType : Frame -> Type
BonusRollType f = Vect (bonusRolls f) (Fin (S PinCount))

ValidBonuses : Vect n (Fin (S PinCount)) -> Type
ValidBonuses {n = Z}      bonuses = LTE 0 0
ValidBonuses {n = (S _)}  bonuses =
  Either
    (finToNat (head bonuses) = PinCount)
    (sum (map finToNat bonuses) `LTE` PinCount)

data BowlingGame : Type where
  MkBowlingGame : (frames: Vect FrameCount Frame)
                  -> (bonuses : BonusRollType (last frames))
                  -> { auto prf: ValidBonuses bonuses }
                  -> BowlingGame


--------------------------------------------------------------------------------
-- Computing the score
--------------------------------------------------------------------------------

gameRolls : BowlingGame -> List Nat
gameRolls (MkBowlingGame frames bonuses) =
  concatMap knockedPins frames ++ toList (map finToNat bonuses)

score' : Nat -> Vect n Frame -> List Nat -> Nat
score' current [] _ = current
score' current (f :: fs) rolls =
  let frameRollNb = length (knockedPins f)
      scoreRollNb = frameRollNb + bonusRolls f
      frameScore = sum (take scoreRollNb rolls)
  in score' (current + frameScore) fs (drop frameRollNb rolls)

score : BowlingGame -> Nat
score game@(MkBowlingGame frames bonus) = score' 0 frames (gameRolls game)


--------------------------------------------------------------------------------
-- Unit Tests
--------------------------------------------------------------------------------

assertEq : Eq a => (given : a) -> (expected : a) -> IO ()
assertEq g e = if g == e
    then putStrLn "Test Passed"
    else putStrLn "Test Failed"

should_be_300_for_perfect_game : IO ()
should_be_300_for_perfect_game =
  assertEq 300 $ score $ MkBowlingGame (replicate 10 strike) [10, 10]

should_be_164_for_spare_6_4_only_game : IO ()
should_be_164_for_spare_6_4_only_game =
  assertEq 164 $ score $ MkBowlingGame (replicate 10 (roll 6 4)) [10]

should_be_150_for_5_pins_only_game : IO ()
should_be_150_for_5_pins_only_game =
  assertEq 150 $ score $ MkBowlingGame (replicate 10 (roll 5 5)) [5]

should_be_90_for_best_game_without_bonus : IO ()
should_be_90_for_best_game_without_bonus =
  assertEq 90 $ score $ MkBowlingGame (replicate 10 (roll 6 3)) []

should_be_104_for_wikipedia_example : IO ()
should_be_104_for_wikipedia_example =
  assertEq 104 $ score $ MkBowlingGame ([strike, strike, strike, roll 8 2, roll 8 0] ++ replicate 5 (roll 0 0)) []

run_tests : IO ()
run_tests = do
  should_be_300_for_perfect_game
  should_be_164_for_spare_6_4_only_game
  should_be_150_for_5_pins_only_game
  should_be_90_for_best_game_without_bonus
  should_be_104_for_wikipedia_example

--
