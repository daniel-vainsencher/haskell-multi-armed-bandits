
module Main where
import MultiArmedBanditTree

main = do bestLocation <- findBest 10000 100 twinPeaks
          putStrLn $ show $ bestLocation
