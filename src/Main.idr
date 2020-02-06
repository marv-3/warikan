module Main

import warikan
import Data.Vect


main : IO ()
main = do
    let ss = sankashas $ 参加する "Nishi" ちょっと払える $ 企画する "kanji" "tada no noikai" "today"
    putStrLn $ (++) "幹事が" $ the String $ cast $ 割り勘 10000 ss

--  こっちにするとコンパイルエラー
-- putStrLn $ the String $ cast $ 割り勘 10000 [] 
