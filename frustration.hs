{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

-- Computes the probability of winning frustration solitaire.
-- For info on frustration solitaire (and other rank-derangement problems),
-- see http://www.math.dartmouth.edu/~doyle/docs/rank/rank.pdf

-- In frustration solitaire, with a 4-suit deck and 13 cards per suit,
-- the probability of winning is:
--
--      1309302175551177162931045000259922525308763433362019257020678406144
-- p = --------------------------------------------------------------------
--     80658175170943878571660636856403766975289505440883277824000000000000
--
-- gcd = 283982221662775934976
--
--       4610507544750288132457667562311567997623087869
-- p = ------------------------------------------------
--     284025438982318025793544200005777916187500000000
--
--   ~ 1.62327274671946%

-- TODO: Command-line arguments
--     Support something like the following:
--         usage: frustration [-c cards_per_suit] [-s suits]
--         Default values of 4 for cards_per_suit, and 13 for suits
-- TODO: Deck size
--     Support much larger decks, such as 100 cards per suit.
-- TODO: HUnit
--     Convert runTests to use HUnit.
-- TODO: Polynomial
--     Use a standard polynomial class.

-- For frustration solitaire computations
import Data.Function (on)
import Data.List (dropWhileEnd)

-- For parsing arguments
import Control.Monad          (when)
import System.Console.GetOpt  (ArgDescr(NoArg), ArgDescr(OptArg), ArgDescr(ReqArg))
import System.Console.GetOpt  (ArgOrder(Permute))
import System.Console.GetOpt  (OptDescr(Option))
import System.Console.GetOpt  (getOpt, usageInfo)
import System.Environment     (getArgs, getProgName)
import System.Exit            (ExitCode(ExitFailure), ExitCode(ExitSuccess), exitWith)
import System.IO              (hPutStrLn, putStrLn, stderr)


type Dimension = Integer
type NumRooks  = Integer
type Poly      = [Integer]  -- Exponent coefficients, from x^0 upwards

factorial :: Integer -> Integer
factorial n = product [1..n]

-- ========================================
-- Polynomial functions

(<+>),(<***>) :: Poly -> Poly -> Poly

(<+>)   fs     []     = fs
(<+>)   []     gs     = gs
(<+>)   (f:fs) (g:gs) =
    dropWhileEnd (== 0) $ f+g : fs<+>gs

(<***>) (f:fs) (g:gs) =
    dropWhileEnd (== 0) $ [f*g] <+> (0:map (f*) gs) <+> (0:map (*g) fs) <+> (0:0:fs <***> gs)
(<***>) _      _      = []

degree :: Poly -> Int
degree p = length p

eval :: Poly -> Integer -> Integer
eval p x = foldr (\a b -> a + b * x) 0 p

pow :: Poly -> Integer -> Poly
pow p n | n < 0  = error "Negative exponent"
        | n == 0 = [1]
        | n == 1 = p
        | otherwise = p <***> (pow p (n-1))

polyStr :: Poly -> String
polyStr [] = "0"
polyStr cs = concatMap
             (\c -> " + " ++ (show (fst c)) ++ "x^" ++ (show (snd c)))
             (reverse (zip  cs  [0..length(cs)-1] ))

-- ========================================
-- Rook polynomial functions

getArrangementCount :: NumRooks -> Dimension -> Dimension -> Integer
getArrangementCount 0 m n = 1 :: Integer
getArrangementCount 1 m n = (m * n) :: Integer
getArrangementCount r m n =
    sum $ map (\k -> n * getArrangementCount (r-1) (m-k) (n-1)) [1 .. (m-r+1)]

getSquareRookPolynomial :: Integer -> Poly
getSquareRookPolynomial dim =
    map (\k -> getArrangementCount k dim dim) [0 .. dim]

-- ========================================

fdiv = (/) `on` fromIntegral

getFrustrationWinRawOdds :: Integer -> Integer -> (Integer, Integer)
getFrustrationWinRawOdds suit_count cards_per_suit = do
  let deck_size  = suit_count * cards_per_suit
  let suitPoly   = getSquareRookPolynomial suit_count
  let fullPoly   = pow suitPoly cards_per_suit

  let fac_term k = factorial $ deck_size - toInteger(k)
  let deck_inds  = [0 .. deck_size]
  let raw_numer  = sum [((-1)^k) * (fullPoly !! (fromIntegral k)) * (fac_term k) | k <- deck_inds]
  let raw_denom  = factorial deck_size
  (raw_numer, raw_denom)


printFrustrationSolitaireWinInfo :: Int -> Int -> IO()
printFrustrationSolitaireWinInfo suit_count cards_per_suit = do
  putStrLn $ "Frustration Solitaire win probability (see \"Frustration Solitaire\", by Doyle, Grinstead, and Snell)"
  -- Get probability of winning: Ways to win / Total number of permutations
  let (numer, denom) = getFrustrationWinRawOdds (toInteger suit_count) (toInteger cards_per_suit)
  putStrLn $ "  Odds numerator   (raw)     = " ++ (show numer)
  putStrLn $ "  Odds denominator (raw)     = " ++ (show denom)
  putStrLn $ "  Probability of winning (%) = " ++ show (fromIntegral(numer) `fdiv` denom)
  putStrLn ""

  -- Get probability of winning in reduced form
  let (numer2, denom2) = (numer `div` d, denom `div` d) where d = gcd numer denom

  putStrLn $ "  Odds numerator   (reduced) = " ++ (show numer2)
  putStrLn $ "  Odds denominator (reduced) = " ++ (show denom2)
  putStrLn $ "  Probability of winning (%) = " ++ show (fromIntegral(numer2) `fdiv` denom2)


runTests :: IO()
runTests = do
  -- Test basic rook polynomial computation
  let getRookPoly = getSquareRookPolynomial
  let testBase = and [ (getRookPoly 1) == [1, 1]
                     , (getRookPoly 2) == [1, 4, 2]
                     , (getRookPoly 3) == [1, 9, 18, 6]
                     , (getRookPoly 4) == [1, 16, 72, 96, 24]
                     ]

  -- Test rook polynomial multiplication
  let testPower = (getRookPoly 2) <***> (getRookPoly 2) == [1, 8, 20, 16, 4]

  -- Test with various suit counts, and cards per suit
  let test_1_2 = (getFrustrationWinRawOdds 1 2) == (1, 2)
  let test_1_3 = (getFrustrationWinRawOdds 1 3) == (2, 6)
  let test_2_2 = (getFrustrationWinRawOdds 2 2) == (4, 24)

  -- Verify that the prob of winning approaches exp(-4) as cards_per_suit --> Infinity
  let limit = exp(-4)
  let (numer_limit, denom_limit) = getFrustrationWinRawOdds 4 40
  let diff_ratio_limit = abs((numer_limit `fdiv` denom_limit) - limit) / limit
  let testLimit = diff_ratio_limit < 0.04

  putStrLn $ "Tests:"
  putStrLn $ "  Rook polynomial base test passed?  : " ++ show testBase
  putStrLn $ "  Rook polynomial power test passed? : " ++ show testPower
  putStrLn $ "  Frustration test (1, 2) passed?    : " ++ show test_1_2
  putStrLn $ "  Frustration test (1, 3) passed?    : " ++ show test_1_3
  putStrLn $ "  Frustration test (2, 2) passed?    : " ++ show test_2_2
  putStrLn $ "  Rook polynomial limit test passed? : " ++ show testLimit
  putStrLn ""

-- ========================================
-- Parsing command-line arguments

data Options = Options
    { optSuits :: Int
    , optCardsPerSuit :: Int
    , optDoShowHelp :: Bool
    } deriving Show

defaultOptions :: Options
defaultOptions = Options
    { optSuits = 4
    , optCardsPerSuit = 13
    , optDoShowHelp = False
    }

options :: [ OptDescr (Options -> Options) ]
options =
    [ Option "s" []
          (ReqArg (\arg opts -> opts { optSuits = read arg })
          "SUITS")
          "Specify the number of suits in the deck."
    , Option "c" []
          (ReqArg (\arg opts -> opts { optCardsPerSuit = read arg })
          "CARDS_PER_SUIT")
          "Specify the number of cards per suit."
    , Option "h" ["help"]
          (NoArg (\opts -> opts { optDoShowHelp = True }))
          "Print this help message."
    ]

parseArgs:: String -> [String] -> Options
parseArgs progName args = opts
  where
    (opts, errors) = case getOpt Permute options args of
      (opt, _, []) -> (foldl (flip id) defaultOptions opt, [])
      (_, _, errs) -> error (concat errs ++ usageInfo usageSummary options)
    usageSummary = "Usage: " ++ progName ++ " <OPTIONS>"

-- ========================================

main :: IO()
main = do
    -- Catch command-line argument errors before running tests
    args <- getArgs
    progName <- getProgName
    let !opts = parseArgs progName args

    -- Run tests
    runTests

    let Options { optSuits = suits
                , optCardsPerSuit = cardsPerSuit
                , optDoShowHelp = doShowHelp } = opts
    printFrustrationSolitaireWinInfo suits cardsPerSuit
