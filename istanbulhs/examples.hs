fib = 1 : 1 : zipWith (+) fib (tail fib)

quicksort []     = []
quicksort (p:xs) =
  filter (< p) xs ++ [p] ++ filter (>= p) xs

birEkle :: Int -> Int
birEkle x = x + 1

topla :: Int -> Int -> Int
topla a b = a + b

fib' :: Int -> Int
fib' 0 = 1
fib' 1 = 1
fib' x = fib' (x-1) + fib' (x-2)

ilk :: [a] -> a
ilk (x:xs) = x

-- Tip siniflari

tekrarli :: Eq a => [a] -> Bool
tekrarli (x:y:xs) = x == y

data Cevap = Evet | Hayir | Bilinmiyor
             deriving (Show, Eq)

-- case ifadeleri
ters x = case x of
  Evet  -> Hayir
  Hayir -> Evet
  _     -> x


toList :: String -> [Int]
toList input = read ("[" ++ input ++ "]")

main = do
  putStrLn "Bir sayı listesi girin"
  input <- getLine
  print $ sum (toList input)


getInt :: IO Int
getInt = fmap read getLine


kaldirac :: (a -> b) -> IO a -> IO b
kaldirac f x = do
    ic <- x
    return (f ic)
