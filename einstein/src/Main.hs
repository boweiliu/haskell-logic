import Data.List.Split (splitOn)

-- module Main (main) where


-- An einstein puzzle can be graphed into F^d ; it then looks like a fully bijective 1-dimensional variety, i.e. a set of F^d that has the property that specifying any 1 of d coordinates results in exactly 1 point on the variety. 
-- For instance, in the original puzzle, there's exactly one Englishman -- he lives in the red house and smokes cigars and owns a horse, etc.
-- We can generalize this to a fully injective 1-dimensional variety, i.e. it's not necessarily onto, or in the original puzzle, there's not necessarily a New Zealander or a Peugeot driver, but if there were, there wouldn't be any others, etc.
-- Of course this generalizes to  k-dim varieties inside F^d, for instance, a fully bijective F^2 in F^3 specifies a typical magic square etc.

featuresPoolFileName :: FilePath
featuresPoolFileName = "features.txt"

data Feature = Feature
  { description :: String,
    values :: [ String ]
  } deriving (Show)

type FeaturePool = [ Feature ]

type Point = [ Int ]
type Variety = [ Point ]

parseFeatureSection :: String -> Feature
parseFeatureSection section =
  case lines section of
    [] -> error ("could not parse section" ++ section)
    (d:v) -> Feature d (filter (not . null) v)

-- Read and parse the feature value pool from the file
readFeaturePool :: FilePath -> IO FeaturePool
readFeaturePool filePath = do
  content <- readFile filePath
  let sections = splitOn "--" content
  return $ map parseFeatureSection (filter (not . null) sections)

main :: IO ()
main = do
  -- Read the feature pool from the file
  featurePool <- readFeaturePool "features.txt"
  
  -- Display the feature pool
  putStrLn $ "Feature Pool:\n" ++ showFeaturePool featurePool

-- Convert a feature pool to a string for display purposes
showFeaturePool :: [Feature] -> String
showFeaturePool features =
  concatMap show features
