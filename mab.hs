
module MultiArmedBandit where
import Data.List
import Control.Monad.IO.Class

--------- This section is a utility for maintaining empirical mean and variance estimates without keeping all scores.
-- |Sufficient information to calculate online mean and variance, see
-- |Donald E. Knuth (1998). The Art of Computer Programming, volume 2: Seminumerical Algorithms, 3rd edn., p. 232. Boston: Addison-Wesley.
data Stats = OnlineMeanAndVariance {
     mvN :: Integer,   -- number of samples so far
     mvX,          -- current mean
     mvM2 :: Float -- extra information for variance
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
------- Utility ends here

-- | Each bandit is characterized by its statistical properties of its scores (number, mean and variance), and by some opaque identity a seen only by the environment.
data UCBBandits a = Bandits [(Stats, a)] deriving Show

-- | selfVisitStats, #totalArms, #totalVisits, errorProbability -> upper confidence bound
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
play :: UCBBandits a -> BanditProblem a -> IO (UCBBandits a)
play bandits' problem =
     let
          BanditProblem {bpPayoff = payoff} = problem
          ((chosenStats, chosenIdentity), otherArms) = chosenAndRest bandits'
     in do
          newScore <- payoff chosenIdentity
          let updatedArm = (chosenStats `withEntry` newScore, chosenIdentity)
          return (Bandits (updatedArm : otherArms))

data BanditProblem a = BanditProblem {bpPayoff :: a -> IO Float}

biggerIsBetter i = do return i

--- instance Show (UCBBandit Float)

main = let threeBandits = Bandits $ map (\ n -> (emptyStats, n)) [1..3]
           bibProblem = (BanditProblem {bpPayoff = biggerIsBetter})
       in do
                resultingBandits <- play threeBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                resultingBandits <- play resultingBandits bibProblem
                return resultingBandits
