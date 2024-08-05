{-# LANGUAGE TemplateHaskell #-}
import Data.List.Split (splitOn)
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import Data.List (intercalate)
import Control.Monad (liftM2)
import Data.Function.Memoize (deriveMemoizable, memoize)

type CubeDims = [ Int ] -- len == $d$
data UniverseParams = UniverseParams 
 -- maxIdx,      maxVals
  { numUnivDims :: Int,
-- isInjective :: Bool,
    coordDims :: CubeDims
  } deriving ( Show, Eq, Ord )

$(deriveMemoizable ''UniverseParams)

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

  putStrLn $ "Test 1 results:\n" ++ (example1 ())
  putStrLn $ "Test 2 results:\n" ++ (example2 ())
  putStrLn $ "Test 3 results:\n" ++ (example3 ())

-- Convert a feature pool to a string for display purposes
showFeaturePool :: [Feature] -> String
showFeaturePool features =
  concatMap showFeature features
  where showFeature f = (show f ++ "\n")


-- Now start defining space over which to do the computation.
newtype Idx = Idx Int deriving (Show, Eq) -- indexes into a vector, specifying which coord
newtype Val = Val Int deriving (Eq, Ord) -- the value a coordinate can hold
instance Show Val where
  show (Val x) = (show x)

toInt :: Idx -> Int
toInt (Idx i) = i

type Point = [ Val ] -- len == $d$
showPoint :: Point -> String
showPoint = foldr (++) "" . map show
parsePoint :: String -> Point
parsePoint = map (Val . read . return)
  

type Curve = [ Point ] -- Any number of points
showCurve :: Curve -> String
showCurve = intercalate "," . map showPoint

-- start by defining parameters:
-- d = 2 (dimensions)
-- n_0 = 3, n_1 = 3 (number of possible values each coordinate can take)



-- Then add constraints:
-- "injective" == no dupes
-- p = p_0 (number of entities)
-- "p >= p_0" for any value of p_0
-- "p <= p_0" for any value of p_0
-- any constraints of this form: i, j, v_i, v_j are parameters
-- "someone who is/likes x_i == v_i exists"
-- "if someone who is/likes x_i == v_i exists, then they are/like x_j == v_j"
-- "someone who is/likes x_i == v_i exists, and they are/like x_j == v_j"
-- "if someone who is/likes x_i == v_i exists, then they aren't/don't like x_j == v_j"

data Comparator = Equ | Leq | Geq deriving (Show, Eq, Enum, Bounded)
data CountConstraint = CountConstraint { comparator :: Comparator, comparatorVal :: Int } deriving ( Show, Eq )
data ExistsConstraint = ExistsConstraint { existsDim :: Idx, existsVal :: Val } deriving ( Show, Eq )
data AffirmConstraint = AffirmConstraint
  { conditionDim :: Idx, conditionVal :: Val
  , clauseDim :: Idx, clauseVal :: Val } deriving ( Show, Eq )
newtype ExactConstraint  = ExactConstraint AffirmConstraint
  deriving (Show, Eq)
newtype NegativeConstraint  = NegativeConstraint AffirmConstraint
  deriving (Show, Eq)
-- data CountConstraint = CountConstraint 

data FactConstraint
  = Exists ExistsConstraint
  | Affirm AffirmConstraint
  | Exact ExactConstraint
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
  Exact (ExactConstraint ce) -> checkPointConstraint point (Affirm ce)
  Negative (NegativeConstraint cn) -> fmap not (checkPointConstraint point (Affirm cn))
  Count _ -> Nothing

checkCurveConstraint :: Curve -> FactConstraint -> Bool  
checkCurveConstraint curve constraint = case constraint of 
  Exists _ -> (foldr (||) False . map (fromMaybe False))  pointChecks
  Affirm _ -> (foldr (&&) True . map (fromMaybe True))  pointChecks
  Exact _ -> (foldr (||) False . map (fromMaybe False))  pointChecks
  Negative _ -> (foldr (&&) True . map (fromMaybe True))  pointChecks
  Count (CountConstraint c cval) -> case c of
    Equ -> len == cval
    Leq -> len <= cval
    Geq -> len >= cval
    where len = length curve
  where pointChecks = map ( `checkPointConstraint` constraint ) curve

-- checkPartialCurveConstraint :: Curve -> FactConstraint -> Maybe Bool
-- checkPartialCurveConstraint curve constraint = case constraint of 
--   Exists _ -> (foldr (||) False . map (fromMaybe False))  pointChecks
--   Affirm _ -> (foldr (&&) True . map (fromMaybe True))  pointChecks
--   Exact _ -> (foldr (||) False . map (fromMaybe False))  pointChecks
--   Negative _ -> (foldr (&&) True . map (fromMaybe True))  pointChecks
--   Count (CountConstraint c cval) -> case c of
--     Equ -> len == cval
--     Leq -> len <= cval
--     Geq -> len >= cval
--     where len = length curve
--   where pointChecks = map ( `checkPointConstraint` constraint ) curve

checkCurveConstraints :: Curve -> [ FactConstraint ] -> Bool  
checkCurveConstraints cu constraints = all (checkCurveConstraint cu) constraints

-- hum dum. testing
testData1 :: FactConstraint
testData1 = Exists (ExistsConstraint (Idx 0) (Val 10))
testCurve2 :: Curve
testCurve2 = map (map Val) [ [10, 3, 3], [1, 1, 1] ]
testData3 :: FactConstraint
testData3 = Affirm (AffirmConstraint (Idx 0) (Val 100) (Idx 1) (Val 4))
testData4 :: FactConstraint
testData4 = Negative (NegativeConstraint (AffirmConstraint (Idx 0) (Val 10) (Idx 1) (Val 3)))

example1 :: () -> String
-- example1 _ = show (checkCurveConstraint testCurve2 testData4)
-- example1 _ = show (checkPointConstraint (testCurve2 !! 0) testData3)
example1 _ = show ((generateUnivPoints (UniverseParams 3 [3,4,5])))


-- i want to generate all valid curves in a UniverseParams
-- first, generate all points
-- then any set of any number of points  is a curve
-- then filter by satisfying d-dim injectivity (no repeated coordinate values)
-- data UniverseParams = UniverseParams 

generateUnivPoints_ :: UniverseParams -> Curve
generateUnivPoints_ (UniverseParams d ns) = case d of
  0 -> [ [] ]
  _ -> let  tailDimPoints = generateUnivPoints_ (UniverseParams (d-1) (tail ns))
            idxs = map Val [0 .. (head ns - 1)]
    in
    liftM2 (:) idxs tailDimPoints


generateUnivPoints :: UniverseParams -> Curve
generateUnivPoints = memoize generateUnivPoints_


-- generateAllCurves :: UniverseParams -> [ Curve ]
-- do i even need to write this


-- first, actually, just manually concoct a set of constraints, and see if it is solvable
data Puzzle = Puzzle {
  puzzleData :: [ FactConstraint ],
  puzzleParams :: UniverseParams
} deriving (Show, Eq)

  
-- how to list all curves that solve a puzzle?
-- DFS-y. WLOG your curves are lexicographical, so start with a partial curve and a list of partialCurves you've already looked at (since points are unordered in a curve). 
generateAllSolutions :: Puzzle -> [ Curve ]
generateAllSolutions p = generateAllSolutions_ p []

-- recursively hold: the current partial curve, all prior completed solutions
-- recurse by: adding a single point, finding all completed solutions, add them to the list
generateAllSolutions_ :: Puzzle -> Curve -> [ Curve ]
generateAllSolutions_ puz currCurve = let
  nextPoints :: [ Point ]
  nextPoints = generateCandidatePoints puz currCurve
  possibleNextCurves :: [ Curve ]
  possibleNextCurves = map ( flip (:) currCurve ) nextPoints
  isValid = checkCurveConstraints currCurve (puzzleData puz)
  in
  (if isValid then ([ currCurve ]) else ([]))
    ++ concat (map (generateAllSolutions_ puz) possibleNextCurves)


testPuzzle2 :: Puzzle
testPuzzle2 = (Puzzle [
    (Count (CountConstraint Geq 1))
    -- , (Affirm (AffirmConstraint (Idx 0) (Val 0) (Idx 1) (Val 1)))
    -- , Negative (NegativeConstraint (AffirmConstraint (Idx 0) (Val 0) (Idx 1) (Val 1)))
    -- , Exact (ExactConstraint (AffirmConstraint (Idx 0) (Val 0) (Idx 1) (Val 1)))
    -- ,Exists (ExistsConstraint (Idx 0) (Val 0))
  ]
  (UniverseParams 5 [4,4,4,4,4]))

showSolutions :: [Curve] -> String
showSolutions cvs = 
  if (length cvs >= 100) then
      l
    else l ++ "\n" ++ (intercalate "\n" . map showCurve) cvs ++ "\n" ++ l
  where l = show (length cvs) ++ " solutions."

example3 :: () -> String
example3 _ = showSolutions (generateAllSolutions testPuzzle2)


-- algorithm: given a puzzle and some points so far, figure out the set of other points that can be added
generateCandidatePoints :: Puzzle -> Curve -> [ Point ]
generateCandidatePoints puzz@(Puzzle constraints univParams) cuv = if (isFull puzz cuv) then [] else filter 
  ( \p -> True
    -- assumes curves are ordered reverse lexicographically, which is the natural way
    && fromMaybe True (liftM2 (>=) (Just p) maxPoint)
    && not (p `falsifiesConstraints` constraints) 
  )
  (generateUnivPointsAvoiding univParams cuv)
  where maxPoint = if (length cuv == 0) then Nothing else Just (head cuv)

smallSetFromList :: Ord a => [a] -> Set.Set a
smallSetFromList = Set.fromList

removeSmallSetMembers :: Ord a => [a] -> Set.Set a -> [a]
removeSmallSetMembers ls ss = filter (`Set.notMember` ss) ls

generateUnivPointsAvoiding :: UniverseParams -> Curve -> [ Point ]
generateUnivPointsAvoiding univp@(UniverseParams d ns) cuv = case (numUnivDims univp) of
  0 -> [ [ ] ]
  _ -> let tailPoints = (
            let smallerCuv = map tail cuv
            in
            generateUnivPointsAvoiding (UniverseParams (d-1) (tail ns)) smallerCuv
            )
           idx0ValsToAvoid = smallSetFromList (map head cuv)
           idx0Vals = (map Val [0 .. (head ns - 1)]) `removeSmallSetMembers` idx0ValsToAvoid
    in
    liftM2 (:) idx0Vals tailPoints

-- Check if we are not allowed to add any more points due to the count constraint!
isFull :: Puzzle -> Curve -> Bool
isFull (Puzzle constraints univParams) cu = case constraints of 
  [] -> False
  x:xs -> case x of
    Count (CountConstraint cmptr n) -> case cmptr of
      Geq -> False
      _ -> if (length cu == n) then True else False
    _ -> isFull (Puzzle xs univParams) cu

-- checks whether a point falsifies the constraints
falsifiesConstraints :: Point -> [ FactConstraint ] -> Bool
falsifiesConstraints p = any (== Just False) . map (checkPointConstraint p)
-- falsifiesConstraints p cs = any (falsifiesConstraint p) cs 
--   where falsifiesConstraint p_ c_ = (checkPointConstraint p_ c_) == Just False

-- returns true if the point has a shared coordinate with any in the partial existing curve, false otherwise
collidesWith :: Point -> Curve -> Bool
collidesWith p = any ( sharesCoordWith2 p )

sharesCoordWith2 :: Point -> Point -> Bool
sharesCoordWith2 p1 p2 = case p1 of
  [] -> False
  _ -> if ((head p1) == (head p2)) then True else sharesCoordWith2 (tail p1) (tail p2)
-- sharesCoordWith2 p1 p2 = let diffs = zip p1 p2
--  in (any id . map (\(x,y) -> x == y)) diffs

testPuzzle1 :: Puzzle
testPuzzle1 = (Puzzle [
    (Count (CountConstraint Equ 2)),
    (Affirm (AffirmConstraint (Idx 0) (Val 0) (Idx 1) (Val 1)))
  ]
  (UniverseParams 2 [2,2]))

example2 :: () -> String
example2 _ = showCurve (generateCandidatePoints testPuzzle1 [])
 ++ "\n" ++ showCurve (generateCandidatePoints testPuzzle1 [ parsePoint "00" ])
 ++ "\n" ++ showCurve (generateCandidatePoints testPuzzle1 [ parsePoint "10" ])


