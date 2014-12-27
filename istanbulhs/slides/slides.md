% Giriş Seviyesinde Haskell
% Cumhur Korkut
% 27 Aralık 2014, İstanbul Hackerspace


# Haskell'ın kerametleri

* Derlenen bir dil
* Fonksiyonel
* Polimorfik statik tipleme
* Güçlü tipleme
* Tip çıkarımı (type inference)
* Tembel değerleme (lazy evaluation)
* Yan etki olmaması

# Biraz gösteriş yapalım

```haskell
-- Haskell'in ifade gücünün
-- ne kadar yüksek olduğunu
-- gösteren iki örnek.

fib = 1 : 1 : zipWith (+) fib (tail fib)

quicksort []     = []
quicksort (p:xs) = less ++ [p] ++ greater
  where less = filter (< p) xs
        greater = filter (>= p) xs
```

# Haskell kurulumu

[http://www.haskell.org/platform/](http://www.haskell.org/platform/)

# Fonksiyon Mantığı

```haskell
birEkle :: Int -> Int
birEkle x = x + 1

topla :: Int -> Int -> Int
topla a b = a + b

fib' :: Int -> Int
fib' 0 = 1
fib' 1 = 1
fib' x = fib (x-1) + fib (x-2)
```

# Tip Tablosu

| Yazılı Tip..........   | Anlamı                                                                  |
| ------------ | ----------------------------------------------------------------------- |
| Int          | Int tipi                                                                |
| Int -> Int   | Int'ten Int'e olan fonksiyon |
| Float -> Int | Float'tan Int'e olan fonksiyon |
| a -> Int     | herhangi bir tipten Int'e olan fonksiyon |
| a -> a       | herhangi bir a tipinden aynı a tipine olan fonksiyon |
| a -> a -> a  | herhangi bir a tipinden a'dan a'ya olan fonksiyona olan fonksiyon |
| a -> (a -> a)  | üsttekiyle aynı |

# Polimorfik fonksiyonlar

```haskell
ilk :: [a] -> a
ilk (x:xs) = x

-- Tip siniflari

tekrarli :: Eq a => [a] -> Bool
tekrarli (x:y:xs) = x == y

-- Show, Eq, Ord
-- kullanabileceginiz bazi tip siniflaridir.

-- Java'daki interface'ler
-- gibi dusunebilirsiniz.
```
# Function composition

```haskell
f :: Int -> Int
f x = x + 1 -- kisa yoldan: (+1)

g :: Int -> Int
g x = x * 2 -- kisa yoldan (*2)

check :: Int -> Bool
check x = x > 10 -- kisa yoldan: (>10)

h :: Int -> Int
h = f . g -- yani: h x = f (g x)

checkG :: Int -> Bool
checkG = check . g --yani checkH x = check (g x)
                   --yani checkH x = check $ g x
```


# `data` ile veri tipi tanımlama ve pattern matching

```haskell
data Cevap = Evet | Hayir | Bilinmiyor
             deriving (Show)

ters x = case x of
  Evet  -> Hayir
  Hayir -> Evet
  _     -> x

instance Eq Cevap where
  Evet       == Evet       = True
  Hayir      == Hayir      = True
  Bilinmiyor == Bilinmiyor = True
  _          == _          = False
```

# Kaçınılmaz soru: Monad nedir?

Ünlü deyişle, "a monad is a burrito", yani monad bir dürüme benzer.

Monad'leri şimdilik başka bir değeri sarmalayan bir yapı olarak düşünebilirsiniz.

Şimdilik sadece IO (Input/Output) işlemlerini yapmamıza izin verecek kadarını öğrenmemiz yeterli.

# IO Monad

```haskell
toList :: String -> [Int]
toList input = read ("[" ++ input ++ "]")

main = do
  putStrLn "Bir sayı listesi girin"
  input <- getLine
  print $ sum (toList input)
--yani: print (sum (toList input))

-- Tipleri hatırlayalım:
-- putStrLn :: IO ()
-- getLine :: IO String
-- input :: String
-- print :: Show a => a -> IO ()
-- sum :: Num a => [a] -> a
```

# Lifting nedir?

Dürümün içini degistiren fonksiyonu dürüme "lift" ediyoruz, dürümü
değiştiren fonksiyona çeviriyoruz.

```haskell
kaldirac :: (a -> b) -> IO a -> IO b
kaldirac f x = do
    ic <- x
    return (f ic)
```

Haskell'da bu işlemi tüm monad'ler için yapan `liftM` fonksiyonu mevcut.

(`Control.Monad`'i import etmeniz gerekiyor)

# Lifting örneği

```haskell
-- Tipleri hatırlayalım:
-- liftM :: Monad m => (a1 -> r) -> m a1 -> m r
-- read :: Read a -> String -> a
-- getLine :: IO String
getInt :: IO Int
getInt = liftM read getLine

-- burada:
--liftM :: (String -> Int) -> IO String -> IO Int
--read :: String -> Int
```

# Örnek bir uygulama yazalım

```haskell
data Move = Rock | Paper | Scissors
            deriving (Show, Eq, Enum)

-- neden Enum dediğimi açıklayacağım

instance Ord Move where
  x <= y = x == y ||
           (x,y) `elem` [(Rock,Paper),
                         (Paper,Scissors),
                         (Scissors,Rock)]
```

# Sonuç: Bu kadar "zahmete" değer mi?

* Type safety
* Hataların açık şekilde kontrolü

Eğer kullanım kolaylığı en büyük hedef olsaydı, hepimiz golf arabaları kullanıyor olurduk.  -Larry Wall
