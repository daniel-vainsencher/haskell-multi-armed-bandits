
module Main where
import Data.List
import Control.Monad.IO.Class
import System.Random
import Text.Printf
import Text.PrettyPrint.HughesPJ

--------- This section is a utility for maintaining empirical mean and variance estimates without keeping all scores.
-- |Sufficient information to calculate online mean and variance, see
-- |Donald E. Knuth (1998). The Art of Computer Programming, volume 2: Seminumerical Algorithms, 3rd edn., p. 232. Boston: Addison-Wesley.
data Stats = OnlineMeanAndVariance {
     mvN :: !Integer,   -- number of samples so far
     mvX,              -- current mean
     mvM2 :: !Float     -- extra information for variance
}

instance Show Stats where
  show st = printf "#=%d mean=%f var=%f" (entries st) (mean st) (variance st)

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



-----------------------  Generic code ---------------------------
-- | Each bandit in a tree also keeps a list of nodes for visited reachable ids, and a list of ids to be visited. Note that here the Stats of a node include also visits to its children. 
data BanditTree m a 
  = BanditNode { bnStats :: Stats             -- Score at his node
               , bnId :: a                    -- Game state at this node
               , bnSons :: [BanditTree m a]
               , bnUnvisitedSons :: [m a] }

instance Show a => Show (BanditTree m a) where
  show bt = show $ prettyBanditTree bt

prettyBanditTree (BanditNode bnStats bnId bnSons bnUS)
  = own $$ (nest 2 $ vcat sons)
    where
       own = text $ show (bnStats , bnId)
       sons = map prettyBanditTree bnSons


-- | bpPayoff represents the feedback giving environment, bpNodeList
-- represents the problem structure: it returns a list of possible
-- actions identities. In a tree structured problem it might be given
-- a current action identity, then we'd have a=b.
data BanditProblem m a = BanditProblem { bpPayoff   :: a -> m Float
                                       , bpNodeList :: a -> [m a]}

bestNode :: BanditTree m a -> BanditTree m a
bestNode t@(BanditNode {bnSons = []}) = t
bestNode t@(BanditNode {bnSons = sons}) = best
             where (best, rest) = maximalAndRestBy (mean . bnStats) $ map bestNode sons


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
play :: Monad m => UCBBandits a -> BanditProblem m a -> m (UCBBandits a)
play (Bandits bandits) problem =
     let
          BanditProblem {bpPayoff = payoff} = problem
          ((chosenStats, chosenIdentity), otherArms) = chosenAndRest bandits (\(s,i) -> s)
     in do
          newScore <- payoff chosenIdentity
          let updatedArm = (chosenStats `withEntry` newScore, chosenIdentity)
          return (Bandits (updatedArm : otherArms))

initTree :: a -> BanditProblem m a -> BanditTree m a
initTree rootId (BanditProblem _ nodeList) 
  = BanditNode { bnStats = emptyStats, bnId = rootId, bnSons = [], bnUnvisitedSons = nodeList rootId }

playFromTree :: Monad m => BanditProblem m a -> BanditTree m a 
                        -> m (a, Float, BanditTree m a)
-- A single iteration of main loop: 
-- Returns (state after chosen move, its payoff, updated tree)

-- First possibility: if we have unvisited nodes, and
-- the visited nodes have had sufficient attention, get a new node.
playFromTree (BanditProblem payoff list) (BanditNode stats id sons (xunvisited : xs))
   | fromInteger (toInteger (length sons)) <= max 1 (0.02 * (sqrt $ fromInteger (entries stats)))
   = do newState <- xunvisited
        newScore <- payoff newState
        let newStats = emptyStats `withEntry` newScore
        let newUnvisited = list newState
        let newNode = BanditNode newStats newState [] newUnvisited
        let updatedStats = (stats `withEntry` newScore)
        return (newState, newScore, (BanditNode updatedStats id (newNode:sons) xs))

-- Second possiblity: go down an already-visited son
-- If there are no unvisited nodes, and there is at
-- least one visited son: visit a visited son.  If attention to
-- visited hasn't been sufficient, and there is at least one visited
-- son: visit a visited son.
playFromTree problem (BanditNode stats id sons unvisited)
  | not (null sons)   -- We need at least one son
  = let (chosenSon, otherSons) = chosenAndRest sons bnStats   -- Pick son with highest upper bound
    in do (action, newScore, updatedSon) <- playFromTree problem chosenSon
          let updatedStats = stats `withEntry` newScore
          return (action, newScore, BanditNode updatedStats id (updatedSon : otherSons) unvisited)

-- Third possibility: if we arrive here, there are no visited sons, and in particular, no
-- attention deficit, therefore there are no unvisited sons left. So
-- we can only play the current node. When feedback is deterministic,
-- this is wasteful.
playFromTree (BanditProblem payoff _) (BanditNode stats id [] []) =
     do newScore <- payoff id
        let updatedStats = (stats `withEntry` newScore)
        return (id, newScore, BanditNode updatedStats id [] [])

playFromTree _ _ = error "Logic error in playFromTree: should not arrive here."

---------------------- Problem 1: bigger is better --------------------
-- | A trivial bandit problem: the payoff equals the identity, identities are some consecutive integers.
biggerIsBetter :: Int -> BanditProblem IO Float
biggerIsBetter n = BanditProblem { bpPayoff = \i -> return i
                                 , bpNodeList = \m -> case m of
                                                        0 -> [return (fromInteger $ toInteger m) | m <- [1..n]]
                                     			_ -> [] }

---------------------- Problem 2: twinPeaks --------------------
-- | A simple non concave problem testing UCT
-- An infinitely-branching tree of possiblities
twinPeaks :: BanditProblem IO Float
twinPeaks = BanditProblem { bpPayoff = \x -> return (- (min (abs (x+1)) (abs (x-1)))) 
                          , bpNodeList = \x -> randomList x }
randomList x = randomRIO (x-0.1,x+0.1) : randomList x

-- | f (f (f ... (f a) running f n times. Like unfold, without creating the list.
iterationResult :: (Num a, Ord a) => a -> (t -> t) -> t -> t
iterationResult n f a | n <= 0 = a
                      | otherwise = iterationResult (n - 1) f (f a)

problem = twinPeaks
printingRound bs
              = do v <- bs
                   (a, s, nbs) <- playFromTree problem v
                   printf "Got: %f\n" s
                   return nbs

silentRound bs
             = do v <- bs
                  (a, s, nbs) <- playFromTree problem v
                  return nbs

statCarryingRound pair -- IO (banditTree, stats)
                  = do (v, oldSt) <- pair
                       (a, s, nbs) <- playFromTree problem v
                       return (nbs, oldSt `withEntry` s)

start :: IO (BanditTree IO Float)
start = return (initTree 0 problem)

simulationStep
  :: (Eq t, Num t) =>
     (t, BanditTree IO Float, Stats)
     -> IO (Maybe (Stats, (t, BanditTree IO Float, Stats)))
simulationStep (i, _, _) | i == 0 = return Nothing
simulationStep triplet = 
	let (i, bt, stat) = triplet 
        in do (a, s, nbs) <- playFromTree problem bt
	      return (Just (stat, (i-1, nbs, stat `withEntry` s)))

unfoldrMine      :: (tb -> IO (Maybe (ta, tb))) -> tb -> IO [ta]
unfoldrMine f b  = do
  x <- f b 
  case x of
   Just (a,new_b) -> do rest <- unfoldrMine f new_b
			return (a : rest)
   Nothing        -> return []

main = do startbt <- start
	  allStats <- unfoldrMine simulationStep (1000, startbt, emptyStats)
	  return (last allStats)
