module Golf where


skips :: [a] -> [[a]]
skips l = map (`skip` l) [1..length l]
  where skip n l = map snd $ filter  ((== 0) . (`mod` n) . fst) $ zip [1..length l] l
