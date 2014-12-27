data Move = Rock | Paper | Scissors
            deriving (Show, Eq, Enum)

instance Ord Move where
  x <= y = x == y ||
           (x,y) `elem` [(Rock,Paper),
                         (Paper,Scissors),
                         (Scissors,Rock)]


