import Control.Monad (liftM)
import System.Random

data Move = Rock | Paper | Scissors deriving (Show, Eq, Enum)

instance Ord Move where
  x <= y = x == y || (x,y) `elem` [(Rock,Paper),(Paper,Scissors),(Scissors,Rock)]

humanSelect :: IO Move
humanSelect = liftM (toEnum . read) getLine

computerSelect :: IO Move
computerSelect = liftM toEnum (randomRIO (0,2))

resultString :: Ordering -> String
resultString y = case y of
  LT -> "Player Wins"
  EQ -> "Draw!"
  GT -> "Computer Wins"

main :: IO ()
main = do
  putStrLn "Choose a move (0 for Rock, 1 for Paper, 2 for Scissors) :"
  humanMove <- humanSelect
  computerMove <- computerSelect
  putStrLn $ show humanMove ++ " (you) vs " ++ show computerMove ++ " (computer)"
  putStrLn $ resultString $ humanMove `compare` computerMove
  main
