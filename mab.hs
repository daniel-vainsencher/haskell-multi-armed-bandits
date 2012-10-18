
module MultiArmedBandit where
import Data.List
import Control.Monad.IO.Class

--------- This section is a utility for maintaining empirical mean and variance estimates without keeping all scores.
-- |Sufficient information to calculate online mean and variance, see
-- |Donald E. Knuth (1998). The Art of Computer Programming, volume 2: Seminumerical Algorithms, 3rd edn., p. 232. Boston: Addison-Wesley.
data Stats = OnlineMeanAndVariance {
     mvN :: Integer,   -- number of samples so far
     mvX,              -- current mean
     mvM2 :: Float     -- extra information for variance
} deriving Show

-- |Stats for the empty sequence.
emptyStats = OnlineMeanAndVariance {mvN = 0, mvX = 0, mvM2 = 0}

-- |Add a number to the sequence over which we maintain statistics.
withEntry :: Stats -> Float -> Stats
withEntry (OnlineMeanAndVariance {mvN = n, mvX = x, mvM2 = m2}) xNew =
       OnlineMeanAndVariance {mvN = n + 1,
                              mvX = newMean,
                              mvM2 = m2 + delta * (xNew - newMean) }
          where
                delta = xNew - x
                newMean = x + delta / fromInteger (n + 1)
-- |Number of entries in sequence
entries OnlineMeanAndVariance {mvN = n} = n
-- |Mean of entries
mean OnlineMeanAndVariance {mvX = r} = r
-- |Variance of entries
variance OnlineMeanAndVariance {mvN = n, mvX = r, mvM2 = m2} = m2 / fromInteger n
------- Utility section ends here

-- | Each bandit is characterized by its statistical properties of its scores (number, mean and variance), and by some opaque identity a seen only by the environment.
data UCBBandits a = Bandits [(Stats, a)] deriving Show

-- | Each bandit in a tree also has a list of reachable nodes. Note that here the Stats of a node include also visits to its children. Intended invariant: a BanditNode has at least one visit in its stats.
data BanditTree a = BanditNode Stats a [BanditTree a] deriving Show


-- | selfVisitStats, #totalArms, #totalVisits, errorProbability -> upper confidence bound. See:
-- | Audibert, Munos and Szepesvari (2006). Use of variance estimation in the multi-armed bandit problem.
ucbBeta :: Stats -> Integer -> Integer -> Float -> Float
ucbBeta stats _ _ _ | entries stats == 0 = 1/0
ucbBeta stats arms round beta = empMean + confidenceSlow + confidenceFast
         where empMean = mean stats
               confidenceSlow = sqrt (2 * (variance stats) * logPart / visit)
	       confidenceFast = 16 * logPart / 3 / visit
               visit = fromInteger $ entries stats
               logPart = log $ 1 / betaS
               betaS = beta / 4.0 / fromInteger arms / visit / (visit + fromInteger 1)

-- |Choose an arm that maximizes ucbBeta (appropriate to play according to the UCB algorithm)
chosenAndRest (Bandits bandits) =
          let arms = toInteger $ length bandits
              (allStats, allIDs) = unzip bandits
              totalVisits = sum $ map entries allStats
              currUCB s = ucbBeta s arms totalVisits 0.1
              maxUCB = maximum $ map currUCB allStats
              (best, rest) = partition (\(s,i) -> (currUCB s == maxUCB)) bandits
              chosenArm = head best
          in (chosenArm , (tail best) ++ rest)

-- |Play the UCB algorithm with a given history and problem, returning the updated history.
play :: UCBBandits a -> BanditProblem a b -> IO (UCBBandits a)
play bandits' problem =
     let
          BanditProblem {bpPayoff = payoff} = problem
          ((chosenStats, chosenIdentity), otherArms) = chosenAndRest bandits'
     in do
          newScore <- payoff chosenIdentity
          let updatedArm = (chosenStats `withEntry` newScore, chosenIdentity)
          return (Bandits (updatedArm : otherArms))

{-playFromTree :: BanditTree a -> BanditProblem a b -> IO (BanditTree a)
playFromTree (BanditNode stats id sons) (BanditProblem payoff list) = 
	     let -}

-- | bpPayoff represents the feedback giving environment, bpNodeList represents the problem structure: it returns a list of possible actions identities. In a tree structured problem it might be given a current action identity.

data BanditProblem a b = BanditProblem {bpPayoff :: a -> IO Float, bpNodeList :: b -> [a]}

-- | A trivial bandit problem: the payoff equals the identity, identities are some consecutive integers.
biggerIsBetter = BanditProblem (\i -> do return i) (\n -> [1..n])

-- | f (f (f ... (f a) running f n times. Like unfold, without creating the list.
iterationResult :: (Num a, Ord a) => a -> t -> (t -> t) -> t
iterationResult n a f | n <= 0 = a
                      | otherwise = iterationResult (n - 1) (f a) f

main = let bibProblem = biggerIsBetter
	   BanditProblem {bpNodeList = actionSpecifier} = biggerIsBetter
	   start = do return (Bandits $ map (\ n -> (emptyStats, n)) $ actionSpecifier 3)
           round bs = do v <- bs
                         v `play` bibProblem
       in iterationResult 1000 start round
