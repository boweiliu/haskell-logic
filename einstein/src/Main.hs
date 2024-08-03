import Data.List.Split (splitOn)
import Data.Maybe (fromMaybe)

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

parseFeatureSection :: String -> Feature
parseFeatureSection section =
  case filter (not . null ) (lines section) of
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
  featurePool <- readFeaturePool featuresPoolFileName
  
  -- Display the feature pool
  putStrLn $ "Feature Pool:\n" ++ showFeaturePool featurePool

  putStrLn $ "Test 1 results:\n" ++ show (example1 ())

-- Convert a feature pool to a string for display purposes
showFeaturePool :: [Feature] -> String
showFeaturePool features =
  concatMap showFeature features
  where showFeature f = (show f ++ "\n")


-- Now start defining space over which to do the computation.
newtype Idx = Idx Int deriving (Show, Eq) -- indexes into a vector, specifying which coord
newtype Val = Val Int deriving (Show, Eq) -- the value a coordinate can hold
toInt :: Idx -> Int
toInt (Idx i) = i

type Point = [ Val ] -- len == $d$
type CubeDims = [ Int ] -- len == $d$
type Curve = [ Point ] -- Any number of points

-- start by defining parameters:
-- d = 2 (dimensions)
-- n_0 = 3, n_1 = 3 (number of possible values each coordinate can take)

data UniverseParams = UniverseParams 
 -- maxIdx,      maxVals
  { univDims :: Int,
-- isInjective :: Bool,
    coordDims :: CubeDims
  } deriving ( Show, Eq )

-- Then add constraints:
-- "injective" == no dupes
-- p = p_0 (number of entities)
-- "p >= p_0" for any value of p_0
-- "p <= p_0" for any value of p_0
-- any constraints of this form: i, j, v_i, v_j are parameters
-- "someone who is/likes x_i == v_i exists"
-- "if someone who is/likes x_i == v_i exists, then they are/like x_j == v_j"
-- "if someone who is/likes x_i == v_i exists, then they aren't/don't like x_j == v_j"

data Comparator = Equ | Leq | Geq deriving (Show, Eq, Enum, Bounded)
data CountConstraint = CountConstraint { comparator :: Comparator, comparatorVal :: Int } deriving ( Show, Eq )
data ExistsConstraint = ExistsConstraint { existsDim :: Idx, existsVal :: Val } deriving ( Show, Eq )
data AffirmConstraint = AffirmConstraint
  { conditionDim :: Idx, conditionVal :: Val
  , clauseDim :: Idx, clauseVal :: Val } deriving ( Show, Eq )
newtype NegativeConstraint  = NegativeConstraint AffirmConstraint
  deriving (Show, Eq)
-- data CountConstraint = CountConstraint 

data FactConstraint
  = Exists ExistsConstraint
  | Affirm AffirmConstraint
  | Negative NegativeConstraint
  | Count CountConstraint
  deriving (Show, Eq)

checkPointConstraint :: Point -> FactConstraint -> Maybe Bool
checkPointConstraint point constraint = case constraint of
  Exists (ExistsConstraint dim val) ->
    if (point !! toInt dim == val) then Just True else Nothing
  Affirm (AffirmConstraint ifDim ifVal thenDim thenVal) ->
    if ( point !! toInt ifDim == ifVal) then 
      Just (point !! toInt thenDim == thenVal)
    else Nothing
  Negative (NegativeConstraint c) -> fmap not (checkPointConstraint point (Affirm c))
  Count _ -> Nothing

checkCurveConstraint :: Curve -> FactConstraint -> Bool  
checkCurveConstraint curve constraint = case constraint of 
  Exists _ -> (foldr (||) False . map (fromMaybe False))  pointChecks
  Affirm _ -> (foldr (&&) True . map (fromMaybe True))  pointChecks
  Negative _ -> (foldr (&&) True . map (fromMaybe True))  pointChecks
  Count (CountConstraint c cval) -> case c of
    Equ -> len == cval
    Leq -> len <= cval
    Geq -> len >= cval
    where len = length curve
  where pointChecks = map ( `checkPointConstraint` constraint ) curve

testData1 :: FactConstraint
testData1 = Exists (ExistsConstraint (Idx 0) (Val 10))
testCurve2 :: Curve
testCurve2 = map (map Val) [ [10, 3, 3], [1, 1, 1] ]
testData3 :: FactConstraint
testData3 = Affirm (AffirmConstraint (Idx 0) (Val 100) (Idx 1) (Val 4))
testData4 :: FactConstraint
testData4 = Negative (NegativeConstraint (AffirmConstraint (Idx 0) (Val 10) (Idx 1) (Val 3)))

example1 :: () -> String
example1 _ = show (checkCurveConstraint testCurve2 testData4)
-- example1 _ = show (checkPointConstraint (testCurve2 !! 0) testData3)


