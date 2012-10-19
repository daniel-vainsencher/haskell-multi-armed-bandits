
module MultiArmedBandit where
import Data.List
import Control.Monad.IO.Class
import System.Random
import Text.Printf
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

-- | Each bandit in a tree also keeps a list of nodes for visited reachable ids, and a list of ids to be visited. Note that here the Stats of a node include also visits to its children. 
data BanditTree a = BanditNode {bnStats :: Stats, bnId :: a, bnSons :: [BanditTree a], bnUnvisitedSons :: [IO a]}


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

maximalAndRestBy :: (Ord b) => (a -> b) -> [a] -> (a, [a])
maximalAndRestBy f [] = error "empty list has no maximal element"
maximalAndRestBy f (x:[]) = (x, [])
maximalAndRestBy f (x:x':xs) =
    let rest = x':xs
        (largestInSuffix, restFromSuffix) = maximalAndRestBy f rest
    in case (f x) > (f largestInSuffix) of
         True -> (x,rest)
         False -> (largestInSuffix, x:restFromSuffix)


-- |Choose an arm that maximizes ucbBeta (appropriate to play according to the UCB algorithm)
chosenAndRest bandits toStats =
          let arms = toInteger $ length bandits
              totalVisits = sum $ map (entries . toStats) bandits
              currUCB b = ucbBeta (toStats b) arms totalVisits 0.1
              maxUCB = maximum $ map currUCB bandits
          in maximalAndRestBy currUCB bandits

-- |Play the UCB algorithm with a given history and problem, returning the updated history.
play :: UCBBandits a -> BanditProblem a b -> IO (UCBBandits a)
play (Bandits bandits) problem =
     let
          BanditProblem {bpPayoff = payoff} = problem
          ((chosenStats, chosenIdentity), otherArms) = chosenAndRest bandits (\(s,i) -> s)
     in do
          newScore <- payoff chosenIdentity
          let updatedArm = (chosenStats `withEntry` newScore, chosenIdentity)
          return (Bandits (updatedArm : otherArms))

initTree :: a -> BanditProblem a a -> BanditTree a
initTree rootId (BanditProblem _ nodeList) = BanditNode emptyStats rootId [] (nodeList rootId)

playFromTree :: BanditTree a -> BanditProblem a a -> IO (a, Float, BanditTree a)
-- If we have unvisited nodes, and the visited nodes have had sufficient attention, get a new node.
playFromTree (BanditNode stats id sons (xunvisited:xs)) (BanditProblem payoff list)
   | fromInteger (toInteger (length sons)) <= (sqrt $ fromInteger (entries stats)) =
     do newAction <- xunvisited
        newScore <- payoff newAction
        let newStats = emptyStats `withEntry` newScore
        let newUnvisited = list newAction
        let newNode = BanditNode newStats newAction [] newUnvisited
        let updatedStats = (stats `withEntry` newScore)
        return (newAction, newScore, (BanditNode updatedStats id (newNode:sons) xs))
-- If there are no unvisited nodes, and there is at least one visited son: visit a visited son.
-- If attention to visited hasn't been sufficient, and there is at least one visited son: visit a visited son.
playFromTree (BanditNode stats id sons@(s:ss) unvisited) problem =
   let (chosenSon, otherSons) = chosenAndRest sons (\(BanditNode s _ _ _) -> s)
     in do
          (action, newScore, updatedSon) <- playFromTree chosenSon problem
          let updatedStats = stats `withEntry` newScore
          return (action, newScore, BanditNode updatedStats id (updatedSon : otherSons) unvisited)
-- If we arrive here, there are no visited sons, and in particular, no attention deficit, therefore there are no unvisited sons left. So we can only play the current son. When feedback is deterministic, this is wasteful.
playFromTree (BanditNode stats id [] []) (BanditProblem payoff _) =
     do newScore <- payoff id
        let updatedStats = (stats `withEntry` newScore)
        return (id, newScore, BanditNode updatedStats id [] [])

playFromTree _ _ = error "Logic error in playFromTree: should not arrive here."

-- | bpPayoff represents the feedback giving environment, bpNodeList represents the problem structure: it returns a list of possible actions identities. In a tree structured problem it might be given a current action identity, then we'd have a=b.
data BanditProblem a b = BanditProblem {bpPayoff :: a -> IO Float, bpNodeList :: b -> [IO a]}

-- | A trivial bandit problem: the payoff equals the identity, identities are some consecutive integers.
biggerIsBetter n = BanditProblem (\i -> do return i)
                                 (\m -> case m of
                                     0 -> [do return m | m <- [1..n]]
                                     _ -> [])

-- | A simple non concave problem testing UCT
twinPeaks = BanditProblem (\x -> do return (- (min (abs (x+1)) (abs (x-1))))) (\x -> randomList x)
randomList x = randomRIO (x-0.1,x+0.1) : randomList x

-- | f (f (f ... (f a) running f n times. Like unfold, without creating the list.
iterationResult :: (Num a, Ord a) => a -> t -> (t -> t) -> t
iterationResult n a f | n <= 0 = a
                      | otherwise = iterationResult (n - 1) (f a) f


--main = let problem = biggerIsBetter 3
main = let problem = twinPeaks
           start = do return (initTree 0 problem)
           round bs = do v <- bs
                         (a, s, nbs) <- v `playFromTree` problem
                         printf "Did: %s got: %f\n" (show a) s
	                 return nbs
       in iterationResult 100000 start round

{-main = do let bibProblem = biggerIsBetter 3
              BanditProblem {bpNodeList = actionSpecifier} = bibProblem
          actions <- sequence (actionSpecifier 0)
          let start = do return (Bandits $ map (\ n -> (emptyStats, n)) $ actions)
              round bs = do v <- bs
                            v `play` bibProblem
          iterationResult 1000 start round -}
