import Data.List.Split (splitOn)

-- module Main (main) where


-- An einstein puzzle can be graphed into F^d ; it then looks like a fully bijective 1-dimensional variety, i.e. a set of F^d that has the property that specifying any 1 of d coordinates results in exactly 1 point on the variety. 
-- For instance, in the original puzzle, there's exactly one Englishman -- he lives in the red house and smokes cigars and owns a horse, etc.
-- We can generalize this to a fully injective 1-dimensional variety, i.e. it's not necessarily onto, or in the original puzzle, there's not necessarily a New Zealander or a Peugeot driver, but if there were, there wouldn't be any others, etc.
-- Of course this generalizes to  k-dim varieties inside F^d, for instance, a fully bijective F^2 in F^3 specifies a typical magic square etc.

featuresPoolFileName :: FilePath
featuresPoolFileName = "features.txt"

type FeatureValueSet = [ String ]
type FeatureValuePool = [ FeatureValueSet ]

type Point = [ Int ]
type Variety = [ Point ]


-- Read and parse the feature value pool from the file
readFeatureValuePool :: FilePath -> IO FeatureValuePool
readFeatureValuePool filePath = do
  content <- readFile filePath
  let rawFeatureValueSets = splitOn "--" content
  return $ map (filter (not . null) . lines) rawFeatureValueSets

main :: IO ()
main = do
  putStrLn "hello world"
